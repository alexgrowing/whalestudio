import Development.EtaleCohomology.KummerTheory.AdicLimPfCok

namespace LateralTheory.KummerTheory

theorem AdicLim_of_fin (hF : AdicFin) : AdicLim := AdicLim_of AdicKer_holds hF AdicCok_holds

end LateralTheory.KummerTheory
