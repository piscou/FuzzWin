#include "algorithm_gui.h"

/**** CLASSE ALGORITHME ****/

FuzzwinAlgorithm_GUI::FuzzwinAlgorithm_GUI(OSTYPE osType, ArgumentsForAlgorithm *pArgs) 
    : FuzzwinAlgorithm(osType) 
{
    // données de l'algorithme
    _resultsDir     = pArgs->_resultsDir;
    _targetPath     = pArgs->_targetPath;
    _firstInputPath = pArgs->_firstInputPath;

    // données pour les modules externes
    _z3Path         = pArgs->_z3Path;
    _cmdLinePin     = pArgs->_cmdLinePin;
    
    // options de l'algorithme
    _keepFiles        = pArgs->_keepFiles;
    _computeScore     = pArgs->_computeScore;
    _verbose          = pArgs->_verbose;
    _timeStamp        = pArgs->_timeStamp;
    _hashFiles        = pArgs->_hashFiles;
    _traceOnly        = pArgs->_traceOnly;
    _maxExecutionTime = pArgs->_maxExecutionTime;
}

/**  implémentation des méthodes virtuelles pures **/

void FuzzwinAlgorithm_GUI::log(const std::string &msg) const
{
    emit sendToGui(QString::fromLocal8Bit(msg.c_str()));
}

void FuzzwinAlgorithm_GUI::logVerbose(const std::string &msg) const
{
    if (_verbose) emit sendToGui(QString::fromLocal8Bit(msg.c_str()));
}

void FuzzwinAlgorithm_GUI::logVerboseEndOfLine() const
{
    if (_verbose) emit sendToGui(LINEFEED);
}

void FuzzwinAlgorithm_GUI::logEndOfLine() const
{
    emit sendToGui(LINEFEED);
}

void FuzzwinAlgorithm_GUI::logTimeStamp() const
{
    if (_timeStamp) emit sendToGui(TIMESTAMP);
}

void FuzzwinAlgorithm_GUI::logVerboseTimeStamp() const
{
    if (_verbose && _timeStamp) emit sendToGui(TIMESTAMP);
}

void FuzzwinAlgorithm_GUI::algorithmFinished()  { emit sendAlgorithmFinished(); }
void FuzzwinAlgorithm_GUI::notifyAlgoIsPaused() { emit pauseIsEffective(); }
void FuzzwinAlgorithm_GUI::faultFound()         { emit setFaultsFound(++_nbFautes); }
void FuzzwinAlgorithm_GUI::algorithmTraceOnlyFinished() { emit sendTraceOnlyFinished(); }

void FuzzwinAlgorithm_GUI::wrapStartFromGui() { this->run();   }
void FuzzwinAlgorithm_GUI::wrapStopFromGui()  { this->stop();  }
void FuzzwinAlgorithm_GUI::wrapPauseFromGui() { this->pause(); }
