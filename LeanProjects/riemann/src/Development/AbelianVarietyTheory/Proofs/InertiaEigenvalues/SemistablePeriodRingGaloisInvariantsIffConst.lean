import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem stInv_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l)
    (x : Bst P), (∀ g : ↥(GK K), actSt P (g : GQ l) x = x) ↔
      ∃ c : ↥(K0 K), x = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
  intro l _ P AI T K x
  constructor
  · intro h
    obtain ⟨hdom, h2, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
    haveI := hdom
    obtain ⟨c, hcK, hc⟩ := h2 K 1 x one_ne_zero fun g => by rw [map_one, h g, one_mul]
    have hmem : (c : Om l) ∈ K0 K := IntermediateField.mem_inf.2 ⟨hcK, c.2⟩
    refine ⟨⟨c, hmem⟩, ?_⟩
    rw [hc, mul_one, Polynomial.algebraMap_apply]
    rfl
  · rintro ⟨c, rfl⟩ g
    have hc : (c : Om l) ∈ (K.1 : IntermediateField ℚ_[l] (Om l)) := (IntermediateField.mem_inf.1 c.2).1
    have hg : (g : GQ l) (c : Om l) = (c : Om l) := (mem_fixingSubgroup_iff _).1 g.2 _ hc
    have hK0 : algebraMap ↥(K0 K) P.R.B c =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, (IntermediateField.mem_inf.1 c.2).2⟩ := rfl
    rw [actSt]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, stHom_apply, Polynomial.map_C, Polynomial.C_comp]
    congr 1
    rw [hK0]
    exact P.actQ_Kur _ _ _ hg

end GlobalTheory.PMon
