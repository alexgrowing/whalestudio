import Formalism.LocalToGlobal.GlobalTheory.GL6.BwAValIntegralNonneg

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical

variable (D : D7) (u : D.what₂.Word)

theorem bwA_natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  first
    | exact lam.natW_anti
    | exact lam.anti
    | exact lam.antitone
    | (intro a b hab
       simp only [DomWeight.natW]
       first
         | (have := lam.anti hab; omega)
         | (have := lam.dom hab; omega)
         | (have := lam.antitone hab; omega)
         | (have := lam.mono hab; omega)
         | (have := lam.2 hab; omega)
         | (have := lam.dom a b hab; omega)
         | (have := lam.2 a b hab; omega)
         | (have := lam.w_anti hab; omega)
         | (have := lam.anti a b hab; omega))

theorem bwA_val_locInt (w : D.what₂.places.Pl) (σ : D.host.E →+* D.host.E) (y : D.host.E) (s : ℕ)
    (hs : ¬ D.what₂.places.resChar w ∣ s) (hy : (s : D.host.E) * y ∈ (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E).range) :
    (0 : WithTop ℤ) ≤ D.what₂.places.val w (D.embE (σ y)) := by
  obtain ⟨a, ha⟩ := hy
  have hint : IsIntegral ℤ (D.embE (σ (algebraMap (NumberField.RingOfIntegers D.host.E) D.host.E a))) :=
    (NumberField.RingOfIntegers.isIntegral_coe a).map ((D.embE.comp σ).toIntAlgHom)
  have h0 := bwA_val_integral_nonneg D.what₂.places w _ hint
  rw [ha, map_mul, map_mul, map_natCast, map_natCast, AddValuation.map_mul,
    bwA_val_nat_eq_zero D.what₂.places w s hs, zero_add] at h0
  exact h0

def BwBlock (Tt : FormsTied D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
    ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B →
      IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B' →
      ∀ g ∈ delSq ℤ (D.R.N i) ((D.fm u).lam i ((D.fm u).tauOf w v)),
        (tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) *
            (bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
              shiftOf (lamT u i) ((D.fm u).tauOf w v)) •
          Formalism.GradedWeylDivisibility.rowAct ℂ (bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v))
            (MvPolynomial.map (Int.castRingHom ℂ) g) ∈
        bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam i ((D.fm u).tauOf w v)).natW

theorem bwA_subInt_of_block (Tt : FormsTied D u) (h : BwBlock D u Tt) : BwSubInt D u Tt := by
  unfold BwSubInt
  intro w hw hs v hv i hi c B B' hB hB' P hP
  have hN : ∀ τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) B B' τ = 1 := by
    intro τ hτ
    simp [bwA_N, hτ]
  have hprod : (∏ τ, (bwA_N D ((D.fm u).tauOf w v) B B' τ).det ^ shiftOf (lamT u i) τ) =
      (bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
        shiftOf (lamT u i) ((D.fm u).tauOf w v) := by
    rw [Finset.prod_eq_single ((D.fm u).tauOf w v)]
    · intro τ _ hτ
      rw [hN τ hτ, Matrix.det_one]
      first
        | exact one_pow _
        | exact one_zpow _
    · intro hm
      exact absurd (Finset.mem_univ _) hm
  rw [hprod, ← MvPolynomial.smul_eq_C_mul, smul_smul]
  exact bwA_intSpan_subP D w ((D.fm u).lam i) ((D.fm u).tauOf w v) _ hN _
    (h w hw hs v hv i hi c B B' hB hB') P hP

def bwA_EO (O : Subring ℂ) (N : ℕ) : Submonoid (Matrix (Fin N) (Fin N) ℂ) :=
  Submonoid.closure {g | ∃ (a b : Fin N) (c : ℂ), c ∈ O ∧ g = 1 + Matrix.single b a c}

def BwDecomp (Tt : FormsTied D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
    ∀ i (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B →
      IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B' →
      ∃ (K₁ K₂ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) (j : Fin (D.R.N i)) (p x : ℂ),
        K₁ ∈ bwA_EO (bwA_Ow D w) (D.R.N i) ∧ K₂ ∈ bwA_EO (bwA_Ow D w) (D.R.N i) ∧
        p ∈ bwA_Ow D w ∧ p ≠ 0 ∧ x ∈ bwA_Ow D w ∧
        bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v) = K₁ * Matrix.diagonal (Function.update 1 j p⁻¹) * K₂ ∧
        tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) *
            (bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
              shiftOf (lamT u i) ((D.fm u).tauOf w v) =
          x * p ^ ((D.fm u).lam i ((D.fm u).tauOf w v)).natW ⟨0, D.R.N_pos i⟩

theorem bwA_block_of_decomp (Tt : FormsTied D u) (h : BwDecomp D u Tt) : BwBlock D u Tt := by
  intro w hw hs v hv i hi c B B' hB hB' g hg
  obtain ⟨K₁, K₂, j, p, x, h₁, h₂, hpO, hp, hxO, hN, hc⟩ := h w hw hs v hv i hi c B B' hB hB'
  rw [hc, hN, mul_smul]
  have hg' : MvPolynomial.map (Int.castRingHom ℂ) g ∈
      bwA_span (bwA_Ow D w) le_rfl ((D.fm u).lam i ((D.fm u).tauOf w v)).natW :=
    Submodule.subset_span ⟨g, hg, rfl⟩
  have := bwA_span_sandwich (bwA_Ow D w) le_rfl _ (bwA_natW_anti _) (D.R.N_pos i) j p hpO hp K₁ K₂ h₁ h₂ _ hg'
  have e : x • (p ^ ((D.fm u).lam i ((D.fm u).tauOf w v)).natW ⟨0, D.R.N_pos i⟩ •
      Formalism.GradedWeylDivisibility.rowAct ℂ (K₁ * Matrix.diagonal (Function.update 1 j p⁻¹) * K₂) (MvPolynomial.map (Int.castRingHom ℂ) g)) =
      (⟨x, hxO⟩ : bwA_Ow D w) • (p ^ ((D.fm u).lam i ((D.fm u).tauOf w v)).natW ⟨0, D.R.N_pos i⟩ •
      Formalism.GradedWeylDivisibility.rowAct ℂ (K₁ * Matrix.diagonal (Function.update 1 j p⁻¹) * K₂) (MvPolynomial.map (Int.castRingHom ℂ) g)) := rfl
  rw [e]
  exact Submodule.smul_mem _ _ this

theorem lattice_inclusion_of_decomp_glob
    (h1 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwLocBases D u Tt)
    (h2 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwDecomp D u Tt)
    (h3 : ∀ (D : D7) (u : D.what₂.Word) (Tt : FormsTied D u), BwLocGlob D u Tt) : WeightLatticeInclusionFamily := lattice_inclusion_of_sub_integral h1 (fun D u Tt => bwA_subInt_of_block D u Tt (bwA_block_of_decomp D u Tt (h2 D u Tt))) h3

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
