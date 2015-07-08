/*
 * Copyright (c) 2015 Ondrej Kuzelka
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ida.utils;

//import Jama.Matrix;
import ida.utils.tuples.Pair;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

/**
 * A class with some useful statistical methods.
 * Everything iterable this class is implemented naively, it needs to be re-implemented before any serious use (oh, well...).
 * 
 * @author Ondra
 */
public class Statistics {
    /**
     * computes a mean vector of a dataset (the dataset is an n times m matrix where rows correspond to observations and columns to variables)
     * @param data a two-dimensional array (where rows correspond to observations and columns to variables)
     * @return mean vector as a one-dimensional array
     */
    public static double[] mean(double[][] data){
        double[] mean = new double[data[0].length];
        for (int i = 0; i < data.length; i++){
            for (int j = 0; j < mean.length; j++){
                mean[j] += data[i][j];
            }
        }
        for (int i = 0; i < mean.length; i++){
            mean[i] /= data.length;
        }
        return mean;
    }

    /**
     * computes a weighted mean vector of a dataset (the dataset is an n times m matrix where rows correspond to observations and columns to variables)
     * @param data a two-dimensional array (where rows correspond to observations and columns to variables)
     * @param weights a vector of weights of the individual observations
     * @return mean vector as a one-dimensional array
     */
    public static double[] mean(double[][] data, double[] weights){
        double weightSum = VectorUtils.sum(weights);
        double[] mean = new double[data[0].length];
        for (int i = 0; i < data.length; i++){
            for (int j = 0; j < mean.length; j++){
                mean[j] += weights[i]*data[i][j];
            }
        }
        for (int i = 0; i < mean.length; i++){
            mean[i] /= weightSum;
        }
        return mean;
    }

    /**
     * computes a weighted covariance matrix of a dataset (the dataset is an n times m matrix where rows correspond to observations and columns to variables)
     * @param data a two-dimensional array (where rows correspond to observations and columns to variables)
     * @param weights a vector of weights of the individual observations
     * @return covariance matrix as a two-dimensional array
     */
    public static double[][] covariance(double[][] data, double[] weights){
        double weightSum = VectorUtils.sum(weights);
        double[] mean = mean(data, weights);
        double[][] cov = new double[data[0].length][data[0].length];
        for (int i = 0; i < data.length; i++){
            for (int j = 0; j < data[0].length; j++){
                for (int k = 0; k < data[0].length; k++){
                    cov[j][k] += weights[i]*(data[i][j]-mean[j])*(data[i][k]-mean[k]);
                }
            }
        }
        MatrixUtils.multiply(cov, 1.0/weightSum);
        return cov;
    }

    /**
     * computes a covariance matrix of a dataset (the dataset is an n times m matrix where rows correspond to observations and columns to variables)
     * @param data a two-dimensional array (where rows correspond to observations and columns to variables)
     * @return covariance matrix as a two-dimensional array
     */
    public static double[][] covariance(double[][] data){
        double[] mean = mean(data);
        double[][] cov = new double[data[0].length][data[0].length];
        for (int i = 0; i < data.length; i++){
            for (int j = 0; j < data[0].length; j++){
                for (int k = 0; k < data[0].length; k++){
                    cov[j][k] += (data[i][j]-mean[j])*(data[i][k]-mean[k]);
                }
            }
        }
        if (data.length > 1){
            MatrixUtils.multiply(cov, 1.0/(data.length-1));
        } else {
            MatrixUtils.multiply(cov, 1.0/data.length);
        }
        return cov;
    }

    /**
     * computes diagonal covariance-matrix elements
     * @param data a two-dimensional array (where rows correspond to observations and columns to variables)
     * @return a one-dimensional array where the i-th element corresponds to variance of the i-th variable
     */
    public static double[] variance(double[][] data){
       double[] mean = mean(data);
       double[] var = new double[data[0].length];
       for (double[] sample : data){
           for (int j = 0; j < sample.length; j++){
               var[j] += (sample[j]-mean[j])*(sample[j]-mean[j]);
           }
       }
       for (int i = 0; i < var.length; i++){
           var[i] /= (data.length-1);
       }
       return var;
    }

    /**
     * Computes Spearman's correlation coefficient of two vectors of numbers
     * @param dataX vector of numbers
     * @param dataY vector of numbers
     * @return Spearman's correlation coefficient between dataX and dataY
     */
    public static double spearmanCorrelation(double[] dataX, double[] dataY){
        List<Pair<Double, Integer>> pairsX = new ArrayList<Pair<Double, Integer>>();
        List<Pair<Double, Integer>> pairsY = new ArrayList<Pair<Double, Integer>>();

        for(int i=0; i<dataX.length; i++){
            pairsX.add(new Pair<Double, Integer>(dataX[i], i));
            pairsY.add(new Pair<Double, Integer>(dataY[i], i));
        }

        Collections.sort(pairsX, new Comparator<Pair<Double, Integer>>() {

            public int compare(Pair<Double, Integer> o1, Pair<Double, Integer> o2) {
                return (int)Math.signum(o1.r - o2.r);
            }
        });
        Collections.sort(pairsY, new Comparator<Pair<Double, Integer>>(){

            public int compare(Pair<Double, Integer> o1, Pair<Double, Integer> o2) {
                return (int)Math.signum(o1.r - o2.r);
            }
        });

        for (int i=0; i<pairsX.size();i++){
            int count = 0;
            
            for (int j=i+1; j< pairsX.size() && pairsX.get(i).r.equals(pairsX.get(j).r); j++){
                count = j - i;
            }
            double average = i+(double)count/2;

            for (int j=0; j<=count; j++){
                pairsX.get(i+j).r = average;
            }
            i += count;
        }

        for (int i=0; i<pairsY.size();i++){
            int count = 0;

            for (int j=i+1; j< pairsY.size() && pairsY.get(i).r.equals(pairsY.get(j).r); j++){
                count = j - i;
            }
            double average = i+(double)count/2;

            for (int j=0; j<=count; j++){
                pairsY.get(i+j).r = average;
            }
            i += count;
        }

        Collections.sort(pairsX, new Comparator<Pair<Double, Integer>>() {

            public int compare(Pair<Double, Integer> o1, Pair<Double, Integer> o2) {
                return (int)Math.signum(o1.s - o2.s);
            }
        });
        Collections.sort(pairsY, new Comparator<Pair<Double, Integer>>(){

            public int compare(Pair<Double, Integer> o1, Pair<Double, Integer> o2) {
                return (int)Math.signum(o1.s - o2.s);
            }
        });

        double avgRank = (pairsX.size()-1)/2.0;
        double sumNumerator = 0.0;
        double sumVarX = 0.0, sumVarY = 0.0;

        for (int i=0; i<pairsX.size(); i++){
            sumNumerator += (pairsX.get(i).r - avgRank)*(pairsY.get(i).r - avgRank);
            sumVarX += (pairsX.get(i).r - avgRank)*(pairsX.get(i).r - avgRank);
            sumVarY += (pairsY.get(i).r - avgRank)*(pairsY.get(i).r - avgRank);
        }

        return sumNumerator/Math.sqrt(sumVarX*sumVarY);
    }

    /**
     * Computes Spearman's correlation coefficients between the last column of the matrix data
     * (which should be the dependent variable) and all the other columns.
     * @param data the dataset
     * @return Spearman's correlation coefficients between the columns 0,...,length-2 and the column length-1
     */
    public static double[] spearmanCorrelation(double[][] data){
        double[] dataY = new double[data.length];
        double[] dataX = new double[data.length];

        for(int i=0; i<data.length; i++){
            dataY[i] = data[i][data[0].length-1];
        }

        double[] correlationCoeficients = new double[data[0].length];

        for(int i=0; i<data[0].length-1; i++){
            for(int j=0; j<data.length; j++){
                dataX[j] = data[j][i];
            }
            correlationCoeficients[i] = spearmanCorrelation(dataX, dataY);
        }
        correlationCoeficients[data[0].length-1] = 1;

        return correlationCoeficients;
    }
    /**
     * standardizes a data matrix (i.e. it subtracts means from individual variables and divides them by standard deviations)
     * @param data a two-dimensional array (where rows correspond to observations and columns to variables)
     * @return a standardized data-matrix
     */
    public static double[][] standardizeDataMatrix(double[][] data){
        double[][] standardizedData = new double[data.length][data[0].length];
        double[] mean = mean(data);
        double[] dev = variance(data);
        for (int i = 0; i < dev.length; i++){
            dev[i] = Math.sqrt(dev[i]);
        }
        for (int i = 0; i < data.length; i++){
            for (int j = 0; j < data[0].length; j++){
                if (dev[j] != 0){
                    standardizedData[i][j] = (data[i][j]-mean[j])/dev[j];
                } else {
                    standardizedData[i][j] = (data[i][j]-mean[j]);
                }
            }
        }
        return standardizedData;
    }

    /**
     * Performs log-transformation on the given dataset.
     * @param data the dataset
     * @return the transformed dataset
     */
    public static double[][] logDataMatrix(double[][] data){
        double[][] standardizedData = new double[data.length][data[0].length];
        for (int i = 0; i < data.length; i++){
            for (int j = 0; j < data[0].length; j++){
                standardizedData[i][j] = Math.log(1+data[i][j]);
            }
        }
        return standardizedData;
    }
    
   /**
     * Performs sigmoid-transformation on the given dataset.
     * @param data the dataset
     * @return the transformed dataset
     */
    public static double[][] sigmoidDataMatrix(double[][] data){
        double[][] standardizedData = new double[data.length][data[0].length];
        for (int i = 0; i < data.length; i++){
            for (int j = 0; j < data[0].length; j++){
                standardizedData[i][j] = 1.0/(1+Math.exp(-data[i][j]));
            }
        }
        return standardizedData;
    }
    
//    /**
//     * computes the Kullback-Leibler divergence of two multivariate normal distributions with given parameters
//     * @param mean1 mean of the first multivariate normal distribution
//     * @param cov1 covariance matrix of the first multivariate normal distribution
//     * @param mean2 mean of the second multivariate normal distribution
//     * @param cov2 covariance of the second multivariate normal distribution
//     * @return
//     */
//    public static double klDivergence(double[] mean1, double[][] cov1, double[] mean2, double[][] cov2){
//        double[][] meanArray1 = new double[mean1.length][1];
//        double[][] meanArray2 = new double[mean2.length][1];
//        for (int i = 0; i < mean1.length; i++){
//            meanArray1[i][0] = mean1[i];
//            meanArray2[i][0] = mean2[i];
//        }
//        Matrix meanDifference = new Matrix(meanArray2).minus(new Matrix(meanArray1));
//        return 0.5*(Math.log(new Matrix(cov2).det()/new Matrix(cov1).det()) + 
//                new Matrix(cov2).inverse().times(new Matrix(cov1)).trace() +
//                meanDifference.transpose().times(new Matrix(cov2).inverse()).times(meanDifference).trace()-mean1.length);
//    }
}
