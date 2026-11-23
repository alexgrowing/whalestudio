import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt.Link

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {Φ : s.Flag}
  {hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)} {h0 : RefMets Φ}

def bdQ (P : PolDat s Φ hm h0) (k : s.Comp) : Adl (cxSt D.what₂.LL) (Φ.C k).Y :=
  comb (fun o : Option (DV.Rt D.what₂.Tau N) => o.elim (P.ab k) fun x =>
      adlOf (Φ.C k) (fun _ => h0 k) (rootSym S.Dw (fun _ => false) none (DV.tauEmb D x.1) x.2))
    (fun o => o.elim (-1) fun x => -P.dirQ x.1 x.2) fun _ _ => 0

theorem qDiv_bdQ (P : PolDat s Φ hm h0) (k : s.Comp) : qDiv (bdQ P k) = 1 ⊗ₜ P.bd k := by
  have e (x : DV.Rt D.what₂.Tau N) : qDiv (adlOf (Φ.C k) (fun _ => h0 k)
      (rootSym S.Dw (fun _ => false) none (DV.tauEmb D x.1) x.2)) = 1 ⊗ₜ divOf (Φ.C k) (rootExp S x) := by
    simp [qDiv, adlOf, expo_rootSym]
  rw [bdQ, qDiv_comb, Fintype.sum_option]
  simp only [Option.elim]
  rw [PolDat.qDiv_ab]
  simp only [e, qL, PolDat.dirQ, TensorProduct.smul_tmul', smul_eq_mul, mul_one, neg_smul, one_smul, neg_sub, neg_neg,
    TensorProduct.neg_tmul, Finset.sum_neg_distrib, sub_neg_eq_add]
  abel

end GlobalTheory.CovHt.Link
