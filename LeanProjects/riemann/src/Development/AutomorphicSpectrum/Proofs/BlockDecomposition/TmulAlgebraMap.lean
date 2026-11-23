import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open PositivityTheory.SiegelWeilFormula.Densx PositivityTheory.Rg.Base1
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RankOneLoc

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

variable (F) in

def cd (δ : E) {R : Type} [CommRing R] [Algebra F R] (a c : R) : R ⊗[F] E :=
  a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ

theorem tmul_algebraMap {R : Type} [CommRing R] [Algebra F R] (r : R) (t : F) :
    r ⊗ₜ[F] (algebraMap F E t) = (r * algebraMap F R t) ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_comm]

theorem exists_basis [CharZero F] (σ : E →ₐ[F] E) (hfr : Module.finrank F E = 2) {δ : E} (h0 : δ ≠ 0)
    (hσ : σ δ = -δ) : ∃ b2 : Module.Basis (Fin 2) F E, b2 0 = 1 ∧ b2 1 = δ := by
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    simp only [map_add, map_smul, map_one, hσ, map_zero, smul_neg] at h1
    have h2 : (2 * s) • (1 : E) = 0 := by
      have : (2 * s) • (1 : E) = (s • (1 : E) + t • δ) + (s • (1 : E) + -(t • δ)) := by
        rw [mul_smul, two_smul]; abel_nf
      rw [this, hst, h1, add_zero]
    have h3 : s = 0 := by
      have := (smul_eq_zero.1 h2).resolve_right one_ne_zero
      simpa using this
    refine ⟨h3, ?_⟩
    rw [h3, zero_smul, zero_add] at hst
    exact (smul_eq_zero.1 hst).resolve_right h0
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr]), ?_, ?_⟩ <;> simp

variable {R : Type} [CommRing R] [Algebra F R] {b2 : Module.Basis (Fin 2) F E} {δ : E}

theorem cd_surj (h0 : b2 0 = 1) (h1 : b2 1 = δ) (y : R ⊗[F] E) : ∃ a c : R, y = cd F δ a c := by
  refine ⟨(Algebra.TensorProduct.basis R b2).repr y 0, (Algebra.TensorProduct.basis R b2).repr y 1, ?_⟩
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b2).sum_repr y]
  rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, h0, h1, cd,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp

theorem repr_cd (h0 : b2 0 = 1) (h1 : b2 1 = δ) (a c : R) :
    (Algebra.TensorProduct.basis R b2).repr (cd F δ a c) 0 = a ∧
      (Algebra.TensorProduct.basis R b2).repr (cd F δ a c) 1 = c := by
  have e0 : b2.repr 1 = Finsupp.single 0 1 := by rw [← h0]; exact b2.repr_self 0
  have e1 : b2.repr δ = Finsupp.single 1 1 := by rw [← h1]; exact b2.repr_self 1
  simp [cd, Algebra.TensorProduct.basis_repr_tmul, e0, e1]

theorem cd_inj (h0 : b2 0 = 1) (h1 : b2 1 = δ) {a c a' c' : R} (h : cd F δ a c = cd F δ a' c') :
    a = a' ∧ c = c' := by
  have := repr_cd (R := R) h0 h1 a c
  have h' := repr_cd (R := R) h0 h1 a' c'
  rw [h] at this
  exact ⟨this.1.symm.trans h'.1, this.2.symm.trans h'.2⟩

theorem cd_mul {D : F} (hD : δ * δ = algebraMap F E D) (a c a' c' : R) :
    cd F δ a c * cd F δ a' c' =
      cd F δ (a * a' + algebraMap F R D * (c * c')) (a * c' + c * a') := by
  simp only [cd, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hD,
    tmul_algebraMap, TensorProduct.add_tmul]
  rw [show c * c' * algebraMap F R D = algebraMap F R D * (c * c') by ring]
  abel

theorem sigR_cd (σ : E →ₐ[F] E) (hσ : σ δ = -δ) (a c : R) :
    sigR R σ (cd F δ a c) = cd F δ a (-c) := by
  simp [sigR, cd, hσ, TensorProduct.tmul_neg, TensorProduct.neg_tmul]

theorem one_eq_cd : (1 : R ⊗[F] E) = cd F δ (1 : R) 0 := by
  simp [cd, Algebra.TensorProduct.one_def]

theorem tmul_one_eq_cd (n : R) : n ⊗ₜ[F] (1 : E) = cd F δ n 0 := by
  simp [cd]

theorem norm_cd (σ : E →ₐ[F] E) (hσ : σ δ = -δ) {D : F} (hD : δ * δ = algebraMap F E D) (a c : R) :
    sigR R σ (cd F δ a c) * cd F δ a c = (a * a - algebraMap F R D * (c * c)) ⊗ₜ[F] (1 : E) := by
  rw [sigR_cd σ hσ, cd_mul hD, tmul_one_eq_cd]
  congr 1 <;> ring

end Alg

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.CompanionTheory.SW.GoodInt GlobalTheory.CompanionTheory.SW.GoodMass in

theorem model (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ (δ : E) (D j₀ : F) (b2 : Module.Basis (Fin 2) F E), b2 0 = 1 ∧ b2 1 = δ ∧ σ δ = -δ ∧
      δ * δ = algebraMap F E D ∧ J 0 0 = algebraMap F E j₀ ∧
      ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (2 : Fv F v) = 1 ∧
        Valued.v (algebraMap F (Fv F v) D) = 1 ∧ Valued.v (algebraMap F (Fv F v) j₀) = 1 ∧
        ∀ y : Fv F v ⊗[F] E, (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) ↔
          ∃ a c : Fv F v, a ∈ v.adicCompletionIntegers F ∧ c ∈ v.adicCompletionIntegers F ∧ y = cd F δ a c := by
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    apply w.embedding.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  obtain ⟨e, he⟩ := exists_moved hcm
  have hδ0 : e - σ e ≠ 0 := sub_ne_zero.2 he.symm
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = e - σ e := ⟨_, rfl⟩
  rw [← hδ] at hδ0
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσσ]; ring
  obtain ⟨D, hD⟩ := fixed_mem hcm (δ * δ) (by rw [map_mul, hσδ]; ring)
  obtain ⟨j₀, hj⟩ := fixed_mem hcm (J 0 0) (hJ.1 0 0)
  obtain ⟨b2, h0, h1⟩ := exists_basis σ hcm.2.2.1 hδ0 hσδ
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, map_zero] at hD
    exact hδ0 (mul_self_eq_zero.1 hD.symm)
  have hj0 : j₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hj
    exact hJ.2 (by rw [Matrix.det_fin_one, ← hj])
  refine ⟨δ, D, j₀, b2, h0, h1, hσδ, hD.symm, hj.symm, ?_⟩
  obtain ⟨hint, hun⟩ := rational_integral_units F E σ hcm d b
  have hco : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ (k : Fin d) (l : Fin 2),
      algebraMap F (Fv F v) (b2.repr (b k) l) ∈ v.adicCompletionIntegers F := by
    refine eventually_all.2 fun k => eventually_all.2 fun l => ?_
    filter_upwards [eventually_le_one (b2.repr (b k) l)] with v hv
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
    exact hv
  filter_upwards [hun 2 two_ne_zero, hun D hD0, hun j₀ hj0, hint 1, hint δ, hco] with v v2 vD vj i1 iδ ico
  refine ⟨by rwa [map_ofNat] at v2, vD, vj, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · have hcoord : ∀ l, (Algebra.TensorProduct.basis (Fv F v) b2).repr y l =
        ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k * algebraMap F (Fv F v) (b2.repr (b k) l) := by
      intro l
      conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr y]
      rw [map_sum, Finsupp.finset_sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, Algebra.TensorProduct.basis_apply]
      congr 1
      exact repr_inclR b2 (Fv F v) (b k) l
    obtain ⟨a, c, rfl⟩ := cd_surj (R := Fv F v) h0 h1 y
    refine ⟨a, c, ?_, ?_, rfl⟩
    · have := hcoord 0
      rw [(repr_cd h0 h1 a c).1] at this
      rw [this]
      exact sum_mem fun k _ => mul_mem (hy k) (ico k 0)
    · have := hcoord 1
      rw [(repr_cd h0 h1 a c).2] at this
      rw [this]
      exact sum_mem fun k _ => mul_mem (hy k) (ico k 1)
  · rintro ⟨a, c, ha, hc, rfl⟩ k
    have e : cd F δ a c = a • inclR (Fv F v) (1 : E) + c • inclR (Fv F v) δ := by
      simp [cd, inclR, TensorProduct.smul_tmul']
    rw [e, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem ha (i1 k)) (mul_mem hc (iδ k))

end Model

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [Field R] [Algebra F R]
  {b2 : Module.Basis (Fin 2) F E} {δ : E}

theorem isField_iff (σ : E →ₐ[F] E) (h0 : b2 0 = 1) (h1 : b2 1 = δ) {D : F}
    (hD : δ * δ = algebraMap F E D) :
    IsField (R ⊗[F] E) ↔ ¬ IsSquare (algebraMap F R D) := by
  have hne : ∀ a c : R, cd F δ a c = 0 → a = 0 ∧ c = 0 := by
    intro a c h
    have e : (0 : R ⊗[F] E) = cd F δ (0 : R) 0 := by simp [cd]
    rw [e] at h
    exact cd_inj h0 h1 h
  constructor
  · rintro hF ⟨t, ht⟩
    have hz : cd F δ t 1 * cd F δ t (-1) = 0 := by
      rw [cd_mul hD, ht]
      simp [cd]
    have h10 : cd F δ t (1 : R) ≠ 0 := fun h => one_ne_zero (hne _ _ h).2
    obtain ⟨w, hw⟩ := hF.mul_inv_cancel h10
    have h2 : cd F δ t (-1 : R) = 0 := by
      calc cd F δ t (-1 : R) = (cd F δ t 1 * w) * cd F δ t (-1) := by rw [hw, one_mul]
        _ = w * (cd F δ t 1 * cd F δ t (-1)) := by ring
        _ = 0 := by rw [hz, mul_zero]
    exact one_ne_zero (neg_eq_zero.1 (hne _ _ h2).2)
  · intro hs
    refine ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
    · intro h
      rw [one_eq_cd (δ := δ)] at h
      exact one_ne_zero (hne _ _ h.symm).1
    · intro y hy
      obtain ⟨a, c, rfl⟩ := cd_surj h0 h1 y
      have hn : a * a - algebraMap F R D * (c * c) ≠ 0 := by
        intro h
        by_cases hc : c = 0
        · rw [hc] at h
          simp at h
          exact hy (by simp [cd, h, hc])
        · exact hs ⟨a / c, by field_simp; linear_combination -h⟩
      obtain ⟨n, hn'⟩ : ∃ n, n = a * a - algebraMap F R D * (c * c) := ⟨_, rfl⟩
      rw [← hn'] at hn
      refine ⟨cd F δ (a / n) (-c / n), ?_⟩
      rw [cd_mul hD, one_eq_cd (δ := δ)]
      congr 1
      · rw [show a * (a / n) + algebraMap F R D * (c * (-c / n)) = (a * a - algebraMap F R D * (c * c)) / n by ring,
          ← hn', div_self hn]
      · ring

end Field

section Val

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem val_norm (h2 : Valued.v (2 : Fv F v) = 1) {D : Fv F v} (hD : Valued.v D = 1) (hs : ¬ IsSquare D)
    (a c : Fv F v) : Valued.v (a * a - D * (c * c)) = max (Valued.v a) (Valued.v c) ^ 2 := by
  rcases lt_trichotomy (Valued.v a) (Valued.v c) with h | h | h
  · have h' : Valued.v (a * a) < Valued.v (D * (c * c)) := by
      rw [map_mul, map_mul, map_mul, hD, one_mul]
      exact mul_lt_mul'' h h zero_le' zero_le'
    rw [Valuation.map_sub_eq_of_lt_right _ h', max_eq_right h.le, map_mul, map_mul, hD, one_mul, sq]
  · by_cases hc : c = 0
    · have ha : a = 0 := by
        rw [hc, map_zero] at h
        exact (Valuation.zero_iff _).1 h
      simp [ha, hc]
    · have hc1 : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
      have hz : Valued.v (a / c) = 1 := by
        rw [map_div₀, h, div_self hc1]
      have hz0 : a / c ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hz
        exact zero_ne_one hz
      have ha0 : a ≠ 0 := fun h0 => hz0 (by simp [h0])
      have e : a * a - D * (c * c) = (c * c) * ((a / c) * (a / c) - D) := by field_simp
      have hle : Valued.v ((a / c) * (a / c) - D) ≤ 1 := by
        refine (Valuation.map_sub _ _ _).trans (max_le ?_ hD.le)
        rw [map_mul, hz, one_mul]
      have heq : Valued.v ((a / c) * (a / c) - D) = 1 := by
        refine le_antisymm hle (not_lt.1 fun hlt => hs ?_)
        have h4 : Valued.v (4 : Fv F v) = 1 := by
          rw [show (4 : Fv F v) = 2 * 2 by norm_num, map_mul, h2, one_mul]
        have hD0 : D ≠ 0 := by
          intro h0
          rw [h0, map_zero] at hD
          exact zero_ne_one hD
        have hq := GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v (D / ((a / c) * (a / c))) (by
          rw [h4, show D / ((a / c) * (a / c)) - 1 = -(((a / c) * (a / c) - D) / ((a / c) * (a / c))) by
            field_simp; ring, Valuation.map_neg, map_div₀, map_mul, hz, one_mul, div_one]
          exact hlt)
        have he : D = (a / c) * (a / c) * (D / ((a / c) * (a / c))) := by field_simp
        rw [he]
        exact (IsSquare.mul_self _).mul hq
      rw [e, map_mul, map_mul, heq, mul_one, ← h, max_self, h, sq]
  · have h' : Valued.v (D * (c * c)) < Valued.v (a * a) := by
      rw [map_mul, map_mul, map_mul, hD, one_mul]
      exact mul_lt_mul'' h h zero_le' zero_le'
    rw [Valuation.map_sub_eq_of_lt_left _ h', max_eq_left h.le, map_mul, sq]

theorem rv_of_val (e : ℝ) (s : Fv F v) (k : ℕ) (hs : Valued.v s = WithZero.exp (-(k : ℤ))) :
    rv v e s = ∑ i ∈ Finset.range (k + 1), e ^ i := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, map_zero] at hs
    exact WithZero.exp_ne_zero hs.symm
  have key : ∀ i : ℕ, (Valued.v s ≤ ((Multiplicative.ofAdd (-(i : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) ↔ i ≤ k := by
    intro i
    rw [hs]
    change WithZero.exp (-(k : ℤ)) ≤ WithZero.exp (-(i : ℤ)) ↔ _
    rw [WithZero.exp_le_exp]
    omega
  unfold rv
  rw [tsum_eq_sum (s := Finset.range (k + 1))]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos ⟨hs0, (key i).2 (by simpa [Nat.lt_succ_iff] using hi)⟩]
  · intro i hi
    rw [if_neg]
    rintro ⟨-, h⟩
    exact hi (by simpa [Nat.lt_succ_iff] using (key i).1 h)

theorem rv_of_not_int (e : ℝ) (s : Fv F v) (hs : s ∉ v.adicCompletionIntegers F) : rv v e s = 0 := by
  have hs' : ¬ Valued.v s ≤ 1 := fun h => hs (by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact h)
  unfold rv
  rw [tsum_eq_sum (s := ∅)]
  · simp
  · intro i _
    rw [if_neg]
    rintro ⟨-, h⟩
    refine hs' (h.trans ?_)
    change WithZero.exp (-(i : ℤ)) ≤ WithZero.exp 0
    rw [WithZero.exp_le_exp]
    omega

end Val

end GlobalTheory.CompanionTheory.RankOneLoc
