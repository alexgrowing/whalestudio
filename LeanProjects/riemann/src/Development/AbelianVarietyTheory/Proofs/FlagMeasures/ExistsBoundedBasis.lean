import Mathlib
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMassUpperBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPositiveAdd

open NumberField Module Submodule
open ReciprocityTheory.ChartRestriction.G.FD (herm cc fdeg rdE)
open Formalism.MainNotions.StandardLattice (stdForm stdLat)
open Formalism.HermitianLatticesTheory (gmap isom genus)

namespace GlobalTheory.SmallRankMass

theorem transference_dual {M : ℕ} (hM : 1 ≤ M)
    (D : Basis (Fin M) ℝ (EuclideanSpace ℝ (Fin M))) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range D), x ≠ 0 → lam ≤ ‖x‖)
    (z : Fin M → EuclideanSpace ℝ (Fin M)) (hz : LinearIndependent ℝ z)
    (hzD : ∀ i j, ∃ m : ℤ, inner ℝ (z i) (D j) = m) :
    ∃ y : Fin M → EuclideanSpace ℝ (Fin M), LinearIndependent ℝ y ∧
      (∀ i j, ∃ m : ℤ, inner ℝ (y i) (D j) = m) ∧ ∀ i, ‖y i‖ ≤ 5 / 4 * (M / lam) := by
  have hT := transference_successive_minima M (span ℤ (Set.range D)) inferInstance (ZSpan.span_top D) 1 le_rfl hM
  rw [show M + 1 - 1 = M by omega] at hT
  have h1 : lam ≤ PI.succMin (span ℤ (Set.range D)) 1 := by
    apply le_csInf
    · refine ⟨‖D ⟨0, hM⟩‖, norm_nonneg _, fun _ => D ⟨0, hM⟩, fun _ => subset_span ⟨_, rfl⟩, ?_, fun _ => le_rfl⟩
      rw [linearIndependent_unique_iff]
      exact D.ne_zero _
    · rintro t ⟨-, v, hvM, hvli, hvt⟩
      exact (hmin _ (hvM 0) (hvli.ne_zero 0)).trans (hvt 0)
  have h0 : 0 ≤ PI.succMin (PI.dualZ (span ℤ (Set.range D))) M := Real.sInf_nonneg (fun t ht => ht.1)
  have M0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlt : PI.succMin (PI.dualZ (span ℤ (Set.range D))) M < 5 / 4 * (M / lam) := by
    have : PI.succMin (PI.dualZ (span ℤ (Set.range D))) M ≤ M / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith
    have : 0 < (M : ℝ) / lam := by positivity
    linarith
  have hzm : ∀ i, z i ∈ PI.dualZ (span ℤ (Set.range D)) := by
    intro i x hx
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    choose m hm using hzD i
    refine ⟨∑ j, c j * m j, ?_⟩
    simp [inner_sum, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hm]
  obtain ⟨t, ⟨-, v, hvM, hvli, hvt⟩, htlt⟩ := exists_lt_of_csInf_lt
    (s := {t : ℝ | 0 ≤ t ∧ ∃ v : Fin M → EuclideanSpace ℝ (Fin M),
      (∀ j, v j ∈ PI.dualZ (span ℤ (Set.range D))) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t})
    ⟨∑ j, ‖z j‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), z, hzm, hz, fun j =>
      Finset.single_le_sum (f := fun j => ‖z j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)⟩ hlt
  exact ⟨v, hvli, fun i j => hvM i _ (subset_span ⟨j, rfl⟩), fun i => (hvt i).trans htlt.le⟩

theorem transference_rat {V : Type} [AddCommGroup V] [Module ℚ V] {M : ℕ} (hM : 1 ≤ M) (b : Basis (Fin M) ℚ V)
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) (hp : ∀ x, 0 ≤ B x x) (hn : B.Nondegenerate)
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ u, u ≠ 0 → (∀ j, ∃ k : ℤ, B u (b j) = k) → lam ^ 2 ≤ (B u u : ℝ)) :
    ∃ v : Fin M → V, (∀ i, v i ∈ span ℤ (Set.range b)) ∧ LinearIndependent ℚ v ∧
      ∀ i, (B (v i) (v i) : ℝ) ≤ (5 / 4 * ((M : ℝ) / lam)) ^ 2 := by
  have := b.finiteDimensional_of_finite
  obtain ⟨φ, hφ⟩ := ShortVectors.exists_euclidean (M := M)
    (by simpa using finrank_eq_card_basis b) B hs hp
  let d := B.dualBasis hn b
  have hd : ∀ i j, inner ℝ (φ (b i)) (φ (d j)) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hφ, LinearMap.BilinForm.apply_dualBasis_right hn hs]
    split_ifs <;> simp
  have hli : LinearIndependent ℝ (fun j => φ (d j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (inner ℝ (φ (b i))) hg
    simpa [inner_sum, real_inner_smul_right, hd] using this
  have hli' : LinearIndependent ℝ (fun j => φ (b j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (fun x => inner ℝ x (φ (d i))) hg
    simpa [sum_inner, real_inner_smul_left, hd] using this
  let D : Basis (Fin M) ℝ (EuclideanSpace ℝ (Fin M)) :=
    basisOfLinearIndependentOfCardEqFinrank' _ hli (by simp)
  have hD : ∀ j, D j = φ (d j) :=
    fun j => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j
  have hnorm : ∀ x, ‖φ x‖ ^ 2 = (B x x : ℝ) := fun x => by
    rw [← hφ, real_inner_self_eq_norm_sq]
  obtain ⟨y, hyli, hyint, hy⟩ := transference_dual hM D lam hlam (by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : (∑ i, c i • D i) = φ (∑ i, c i • d i) := by simp [hD]
    rw [hw] at hx0 ⊢
    have h := hmin (∑ i, c i • d i) (fun h => hx0 (by rw [h, map_zero])) (fun j => ⟨c j, by
      simp [d, LinearMap.BilinForm.apply_dualBasis_left]⟩)
    rw [← hnorm] at h
    exact (pow_le_pow_iff_left₀ hlam.le (norm_nonneg _) two_ne_zero).1 h) _ hli'
    (fun i j => ⟨if i = j then 1 else 0, by rw [hD, hd]; split_ifs <;> simp⟩)
  choose m hm using hyint
  let v : Fin M → V := fun i => ∑ j, m i j • b j
  have hv : ∀ i, φ (v i) = y i := by
    intro i
    refine InnerProductSpace.ext_inner_right_basis D fun j => ?_
    rw [hm, hD]
    simp [v, sum_inner, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hd]
  refine ⟨v, fun i => sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j, rfl⟩), ?_, fun i => ?_⟩
  · refine LinearIndependent.of_comp φ ?_
    have : φ ∘ v = y := funext hv
    rw [this]
    exact hyli.restrict_scalars' ℚ
  · rw [← hnorm, hv]
    exact pow_le_pow_left₀ (norm_nonneg _) (hy i) 2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rdE_pos : 0 < rdE E := Real.rpow_pos_of_pos
    (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero E)) _

open ShortVectors in

theorem exists_bounded_basis {n : ℕ} (hn : 1 ≤ n) (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) :
    ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ Λ) ∧ LinearIndependent E v ∧
      ∀ (σ : E →+* ℂ) (i k : Fin n), ‖σ (herm 1 (v i) (v k))‖ ≤ 2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2 := by
  obtain ⟨b, hb⟩ := exists_basis Λ hfg (DualFamily.span_eq_top Λ hfg hdual)
  have hf0 : 0 < fdeg E := ClassCount.fdeg_pos
  have hf : (0 : ℝ) < fdeg E := by exact_mod_cast hf0
  have hr : 0 < rdE E := rdE_pos
  have hl : 0 < 2 * (fdeg E : ℝ) / rdE E ^ 2 := by positivity
  obtain ⟨v, hv, hli, hle⟩ := transference_rat (Nat.mul_pos (by omega) hn) b (traceHerm n) (traceHerm_isSymm n)
    traceHerm_nonneg (traceHerm_nondegenerate n) _ (Real.sqrt_pos.mpr hl) (by
      intro u hu hk
      rw [Real.sq_sqrt hl.le, traceHerm_self]
      refine trace_dual_min Λ hint hdual u hu fun y hy => ?_
      obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 ((hb y).2 hy)
      choose k hk using hk
      refine ⟨∑ j, c j * k j, ?_⟩
      rw [← traceHerm_apply, map_sum]
      simp only [map_zsmul, hk]
      simp)
  have hle' : ∀ i (τ : E →+* ℂ), ∑ k, ‖τ (v i k)‖ ^ 2 ≤ 2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2 := by
    intro i τ
    have h := (two_mul_le_traceHerm (v i) τ).trans (hle i)
    have h4 : (5 / 4 * (((2 * fdeg E * n : ℕ) : ℝ) / √(2 * (fdeg E : ℝ) / rdE E ^ 2))) ^ 2
        = 25 / 16 * (2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2) := by
      rw [mul_pow, div_pow, div_pow, Real.sq_sqrt hl.le]
      push_cast
      field_simp
      norm_num
    have : 0 ≤ 2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2 := by positivity
    linarith
  obtain ⟨s, hs1, hs2, -⟩ := euclidean_basis_exists E (Fin n → E) _ v hli (by simp [ShortVectors.finrank_eq])
  have hsr : s.card = n := by simpa using hs1
  let e : Fin n ≃ s := (s.equivFinOfCardEq hsr).symm
  exact ⟨fun i => v (e i), fun i => (hb _).1 (hv _), hs2.comp e e.injective, fun σ i k =>
    SelfDualClasses.norm_herm_le σ _ _ _ (hle' _ σ) (hle' _ σ)⟩

open StdMassBound RootClassCount in

theorem mass_le [StarRing E] (hs : ∀ x : E, star x = IsCMField.complexConj E x) {n : ℕ} (hn : 1 ≤ n) {B : ℝ}
    (hB : B = 2 * (fdeg E : ℝ) * n ^ 2 * rdE E ^ 2) :
    Formalism.HermitianLatticesTheory.mass (stdForm E n) (stdLat E n) ≤ (1 + 2 * B) ^ (2 * fdeg E * n ^ 2) * (n * B) ^ (2 * fdeg E * n ^ 2) := by
  have B0 : 0 ≤ B := by rw [hB]; positivity
  obtain ⟨R, -, H, hR⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
    {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)} B0 fun L hL =>
      ⟨by simp, fun x hx => (hL.2 x).1 hx,
        hB ▸ exists_bounded_basis hn L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
  refine le_trans ?_ hR
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs with hex
  swap
  · positivity
  obtain ⟨h1, h2⟩ := hex.choose_spec
  generalize hex.choose = s at h1 h2
  have key : ∀ M ∈ s, ∃ L₀ ∈ R, ∃ g ∈ isom (stdForm E n), gmap g L₀ = M := by
    intro M hM
    obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H M ⟨(h1 M hM).1.fg, fun y => by
      simp only [isIntegral_herm_iff]
      simpa only [hs] using selfDual_of_mem_genus (h1 M hM) y⟩
    have hγ' : (γ : Matrix (Fin n) (Fin n) E) * (γ : Matrix (Fin n) (Fin n) E).conjTranspose = 1 := by
      rw [← mul_conjTranspose_eq_one _ hγ]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply, hs]
    refine ⟨L₀, hL₀, matEquiv _ hγ', matEquiv_mem _ hγ', ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := (matEquiv _ hγ').surjective x
    constructor
    · rintro ⟨z, hz, e⟩
      rw [← e]
      exact (hm z).1 hz
    · intro hx
      exact ⟨x, (hm x).2 hx, rfl⟩
  choose! f hf g hg hfg using key
  have hcard : s.card ≤ R.card := by
    refine Finset.card_le_card_of_injOn f (fun M hM => hf M hM) fun M hM N hN e => ?_
    have hM' : M ∈ s := hM
    have hN' : N ∈ s := hN
    refine (h2 M (h1 M hM')).unique ⟨hM', 1, one_mem _, Formalism.HermitianLatticesTheory.genusBasic_gmap_one _⟩
      ⟨hN', g M * (g N)⁻¹, mul_mem (hg M hM') (inv_mem (hg N hN')), ?_⟩
    have e1 : gmap (g N)⁻¹ N = f N := by
      have := Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (g N) (f N)
      rwa [hfg N hN'] at this
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, e1, ← e, hfg M hM']
  calc ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm E n) M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum fun M _ => Nat.cast_inv_le_one _
    _ = s.card := by simp
    _ ≤ R.card := by exact_mod_cast hcard

omit [IsCMField E] in

theorem mass_small [StarRing E] (hK : Formalism.HermitianLatticesTheory.IsCMUnram E) (hv : 1 ≤ Formalism.HermitianLatticesTheory.vInv E) {n : ℕ} (h1 : 1 ≤ n)
    (h2 : n ≤ 2) :
    Formalism.HermitianLatticesTheory.mass (Formalism.HermitianLatticesTheory.massTelescope_form E n) (Formalism.HermitianLatticesTheory.massTelescope_lat E n) ≤
      (20 * (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ 2) ^ (16 * Formalism.HermitianLatticesTheory.fDeg E) := by
  have htc := hK.1
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  haveI : IsCMField E := by
    refine LeastExponentCompare.isCMField_of_conj E star hK.2.1 ?_
    by_contra hne
    push Not at hne
    refine IsTotallyComplex.complexEmbedding_not_isReal σ (ComplexEmbedding.isReal_iff.2 ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, ← hK.2.1, hne]
  have hs : ∀ x : E, star x = IsCMField.complexConj E x := fun x => σ.injective (by
    rw [hK.2.1, IsCMField.complexEmbedding_complexConj])
  have hf : fdeg E = Formalism.HermitianLatticesTheory.fDeg E := ClassCount.card_infinitePlace.symm
  have hr : rdE E = 2 * Formalism.HermitianLatticesTheory.vInv E := by
    rw [RootClassCount.rdE_eq, Formalism.HermitianLatticesTheory.vInv, ShortVectors.finrank_eq, hf]
    push_cast
    ring
  have hm := mass_le hs h1 rfl
  have e1 : stdForm E n = Formalism.HermitianLatticesTheory.massTelescope_form E n := LinearMap.ext fun x => LinearMap.ext fun y => rfl
  have e2 : stdLat E n = Formalism.HermitianLatticesTheory.massTelescope_lat E n := by
    unfold stdLat Formalism.HermitianLatticesTheory.massTelescope_lat
    congr 2
    funext i
    simp
  rw [e1, e2, hr, hf] at hm
  refine hm.trans ?_
  have f1 : (1 : ℝ) ≤ Formalism.HermitianLatticesTheory.fDeg E := by exact_mod_cast (Fintype.card_pos : 0 < Formalism.HermitianLatticesTheory.fDeg E)
  generalize Formalism.HermitianLatticesTheory.fDeg E = f at *
  generalize Formalism.HermitianLatticesTheory.vInv E = v at *
  have hw : 4 ≤ (2 * v) ^ 2 := by nlinarith
  generalize (2 * v) ^ 2 = w at *
  have hx : 4 ≤ f * w := by nlinarith
  rw [← mul_pow]
  have n2 : (n : ℝ) ≤ 2 := by exact_mod_cast h2
  have n0 : (0 : ℝ) ≤ n := by positivity
  have nn : (n : ℝ) ^ 2 ≤ 4 := by nlinarith
  have b : 2 * (f : ℝ) * n ^ 2 * w ≤ 8 * (f * w) := by nlinarith
  have b0 : 0 ≤ 2 * (f : ℝ) * n ^ 2 * w := by have : 0 ≤ w := by linarith
                                              positivity
  calc _ ≤ ((20 * (f : ℝ) * w) * (20 * f * w)) ^ (2 * f * n ^ 2) := by
        refine pow_le_pow_left₀ (by positivity) (mul_le_mul (by linarith) (by nlinarith) (by positivity)
          (by linarith)) _
    _ ≤ ((20 * (f : ℝ) * w) * (20 * f * w)) ^ (8 * f) := by
        refine pow_le_pow_right₀ (by nlinarith) ?_
        have : n ^ 2 ≤ 4 := by nlinarith
        nlinarith
    _ = _ := by rw [← sq, ← pow_mul]; congr 1; ring

end GlobalTheory.SmallRankMass
