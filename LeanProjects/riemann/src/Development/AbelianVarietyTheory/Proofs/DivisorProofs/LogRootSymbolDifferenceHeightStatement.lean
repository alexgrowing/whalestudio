import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogRootSymbolDifferenceHeight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QDivBdQ
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_root_symbol_difference_height : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (B : ℝ) (x : DV.Rt D.what₂.Tau N) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (Φ.C k).Y), |lgOf (Φ.C k) (rootSym S.Dw (fun _ => false) none (DV.tauEmb D x.1) x.2) v e y - lgOf (Φ.C k) (rootSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D x.1) x.2) v e y| ≤ htLog κ B v := by
  first | exact @GlobalTheory.CovHt.Link.abs_lgOf_rootSym_false_sub_ind_le | exact GlobalTheory.CovHt.Link.abs_lgOf_rootSym_false_sub_ind_le | (intros; apply GlobalTheory.CovHt.Link.abs_lgOf_rootSym_false_sub_ind_le <;> assumption)
