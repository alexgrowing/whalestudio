import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfIffUnitaryDecoration
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwUnit

section Diag

variable {E : Type} [Field E]

open Classical in

def dEnt (n : ℕ) (π : E) (i : Fin n) : E := if i.1 + 1 = n then (if π = 0 then 1 else π) else 1

theorem dEnt_ne (n : ℕ) (π : E) (i : Fin n) : dEnt n π i ≠ 0 := by
  unfold dEnt
  split_ifs with h1 h2 <;> simp_all

def dAut (n : ℕ) (π : E) : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero E E (dEnt n π i) (dEnt_ne n π i)

theorem dAut_apply (n : ℕ) (π : E) (x : Fin n → E) (i : Fin n) : dAut n π x i = dEnt n π i * x i := rfl

end Diag

theorem exists_tw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (π : 𝓞 E), (∀ P ∈ Q, π ∉ P.asIdeal) → ∃ t : GL (Fin n) (AfE F E), t ∈ K1 hc n ST SG ∧ (∀ (P : Q) (i j : Fin n), adAt F P.1 (t.1 i j) = algebraMap E _ (if i = j then (if i.1 + 1 = n then (π : E) else 1) else 0)) ∧ ∀ w : HeightOneSpectrum (𝓞 E), w ∉ Q → conjPrime₂ w ∉ Q → ∀ i j : Fin n, adAt F w (t.1 i j) = if i = j then 1 else 0 := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ π hπ
  classical
  have hQc : ∀ P ∈ Q, conjPrime₂ P ∉ Q := fun P hP => (hQ P hP).2.2.2.2
  have hπ0 : ∀ P ∈ Q, (π : E) ≠ 0 := fun P hP h => hπ P hP (by
    have : π = 0 := RingOfIntegers.coe_eq_zero_iff.1 h
    rw [this]; exact P.asIdeal.zero_mem)
  have hval : ∀ P ∈ Q, ∀ i : Fin n, P.valuation E (dEnt n (π : E) i) = 1 := by
    intro P hP i
    unfold dEnt
    rw [if_neg (hπ0 P hP)]
    split_ifs
    · exact le_antisymm (HeightOneSpectrum.valuation_le_one _ π)
        (not_lt.1 fun h => hπ P hP ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h))
    · exact map_one _
  have hfr : ∀ P ∈ Q, CharValCompare.IsFr P (Formalism.UG.CS.globLat (1 : GL (Fin n) (AfE F E)) (stdLat E n))
      (dAut n (π : E)) := by
    intro P hP x
    rw [globLat_one_std]
    show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
    rw [mem_localization_standardLattice, mem_localization_standardLattice]
    simp only [dAut_apply, CharValCompare.intAt_iff, map_mul, hval P hP, one_mul]
  obtain ⟨g, hg, c1, c2, c3⟩ := PtExist.exists_modify (hc := hc) hQc (one_mem (UAd hc n)) (fun _ => dAut n (π : E)) hfr

  have hST : ∀ P ∈ ST, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).1 hP, fun h => (hQ _ h).2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  have hSG : ∀ P ∈ SG, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).2.1 hP, fun h => (hQ _ h).2.2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  have hb := isPtOf_base (F := F) hc (n := n) (ST := ST) (SG := SG) (Q := (∅ : Finset (HeightOneSpectrum (𝓞 E))))
  have hpt : IsPtOf hc g (DecoF.base E n ST SG (∅ : Finset (HeightOneSpectrum (𝓞 E)))) := by
    refine ⟨hg, ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · have h := c1
      rw [globLat_one_std] at h
      exact h
    · rw [c3 P.1 (hST P.1 P.2).1 (hST P.1 P.2).2 x i]
      exact hb.f P x hx i hi
    · rw [c3 w.1 (hSG w.1 w.2).1 (hSG w.1 w.2).2 x i]
      exact hb.be w x hx i
  have hd := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g (DecoF.base E n ST SG ∅) rfl).1 hpt
  have hK := mem_principal_of_same_decoration hc n ST SG (one_mem _) hg (by rw [decoRaw_one, ← hd.2]; rfl)
  rw [inv_one, one_mul] at hK
  refine ⟨g, hK, fun P i j => ?_, fun w hw hw' i j => ?_⟩
  · rw [c2 P.1 P.2 i j]
    congr 1
    show dAut n (π : E) (Pi.single j 1) i = _
    rw [dAut_apply]
    unfold dEnt
    rw [if_neg (hπ0 P.1 P.2)]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have e1 : ∀ i j, adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        if i = j then 1 else 0 := by
      intro i j
      have h := c3 w hw hw' (Pi.single j 1) i
      have hv : (fun k => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j (1 : E) : Fin n → E) k)) =
          Pi.single j 1 := by
        ext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
      have h' : adAt F w ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) =
          adAt F w ((((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) := by
        rw [← hv]; exact h
      rw [inv_one, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_single_one] at h'
      have h'' : adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
          adAt F w ((Pi.single j 1 : Fin n → AfE F E) i) := h'
      rw [h'', Pi.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hMi : (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F w) = 1 := by
      ext a b
      rw [Matrix.map_apply, e1, Matrix.one_apply]
    have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)) * ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hM : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
      have h := congrArg (fun M => M.map (adAt F w)) hgg
      simp only [Matrix.map_mul, hMi, mul_one] at h
      rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
    have h := congrFun (congrFun hM i) j
    rw [Matrix.map_apply, Matrix.one_apply] at h
    exact h

end GlobalTheory.Mem.Col2.TwUnit
