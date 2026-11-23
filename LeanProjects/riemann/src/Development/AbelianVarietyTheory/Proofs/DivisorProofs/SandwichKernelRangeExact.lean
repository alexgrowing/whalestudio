import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerMapSubsetImMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem ker_bC_eq_range_alC_and_ker_alC_eq_range_bC : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (h : ℕ) (D : Datum ε h Γ), LinearMap.ker (bC C D) = LinearMap.range (alC C D) ∧ LinearMap.ker (alC C D) = LinearMap.range (bC C D) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Γ _ _ h D
  obtain ⟨hdom, -, hker, hsurj, hnu, hxi, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  have hFG : D.F * D.G = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) :=
    (GlobalTheory.DetInv.datum_scalar_intertwine p C v O hv ε hε Γ h D).2.1
  have hGF : D.G * D.F = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := D.G_mul_F
  set f : Ainf p O →+* C := (algebraMap O C).comp (WittVector.fontaineTheta O p) with hf
  have hinj := hv.hom_inj
  have hfnu : f (nu ε) ≠ 0 := by
    intro h0
    apply hnu
    apply hinj
    simpa [hf] using h0
  have hxiker : WittVector.fontaineTheta O p (xi ε) = 0 := by
    have : xi ε ∈ RingHom.ker (WittVector.fontaineTheta O p) := by
      rw [hker]; exact Ideal.subset_span rfl
    exact this
  have hfmu : f (mu ε) = 0 := by
    rw [← xi_mul_nu, map_mul]
    simp [hf, hxiker]
  have hnzd : xi ε ∈ nonZeroDivisors (Ainf p O) := mem_nonZeroDivisors_of_ne_zero hxi
  have hfrac : ∀ c : C, ∃ s t : Ainf p O, f s ≠ 0 ∧ c * f s = f t := by
    intro c
    by_cases hc : v c ≤ 1
    · obtain ⟨a, ha⟩ := hv.exists_of_le_one hc
      obtain ⟨t, rfl⟩ := hsurj a
      refine ⟨1, t, by simp, ?_⟩
      simp [hf, ha]
    · have hc0 : c ≠ 0 := by
        intro h0; apply hc; simp [h0]
      have hle : v c⁻¹ ≤ 1 := by
        rw [map_inv₀]
        push_neg at hc
        exact inv_le_one_of_one_le₀ hc.le
      obtain ⟨a, ha⟩ := hv.exists_of_le_one hle
      obtain ⟨s, rfl⟩ := hsurj a
      refine ⟨s, 1, ?_, ?_⟩
      · simp [hf, ha, hc0]
      · simp [hf, ha, hc0]
  have hdiv : ∃ s : Ainf p O, f s ≠ 0 ∧ ∀ r : Ainf p O, f r = 0 → xi ε ∣ s * r := by
    refine ⟨1, by simp, fun r hr => ?_⟩
    have h1 : WittVector.fontaineTheta O p r = 0 := by
      apply hinj; simpa [hf] using hr
    have h2 : r ∈ RingHom.ker (WittVector.fontaineTheta O p) := h1
    rw [hker, Ideal.mem_span_singleton] at h2
    simpa using h2
  have hmuxi : mu ε = xi ε * nu ε := (xi_mul_nu ε).symm

  have hcomp : ∀ X Y : Matrix (Fin h) (Fin h) (Ainf p O), X * Y = mu ε • 1 →
      ∀ z : Fin h → C, X.map f *ᵥ (Y.map f *ᵥ z) = 0 := by
    intro X Y hXY z
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hXY]
    have : (mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))).map f = 0 := by
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.one_apply, hfmu]
    rw [this, Matrix.zero_mulVec]
  have hb : ∀ z, bC C D z = D.G.map f *ᵥ z := fun z => by
    simp [bC, redC, Matrix.toLin'_apply, hf]
  have ha : ∀ z, alC C D z = D.F.map f *ᵥ z := fun z => by
    simp [alC, redC, Matrix.toLin'_apply, hf]
  constructor
  · apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, hb] at hx
      obtain ⟨y, hy⟩ := GlobalTheory.DetInv.ker_map_subset_im_map (Ainf p O) C f (xi ε) (nu ε) h D.G D.F
        hnzd hfnu hfrac hdiv (by rw [hFG, hmuxi]) x hx
      exact ⟨y, by rw [ha, hy]⟩
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, hb, ha]
      exact hcomp D.G D.F hGF y
  · apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, ha] at hx
      obtain ⟨y, hy⟩ := GlobalTheory.DetInv.ker_map_subset_im_map (Ainf p O) C f (xi ε) (nu ε) h D.F D.G
        hnzd hfnu hfrac hdiv (by rw [hGF, hmuxi]) x hx
      exact ⟨y, by rw [hb, hy]⟩
    · rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, hb, ha]
      exact hcomp D.F D.G hFG y

end GlobalTheory.DetInv
