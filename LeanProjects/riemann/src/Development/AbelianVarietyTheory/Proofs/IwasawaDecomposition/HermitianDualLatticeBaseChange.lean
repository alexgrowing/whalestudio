import Mathlib
import Formalism.QuotientMetricDivisors.Statement
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.DualBC

variable {K : Type} [Field K] [NumberField K] [StarRing K]

omit [NumberField K] in

theorem mem_dual_iff {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (A : Submodule (𝓞 K) (Fin d → K)) (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]

omit [NumberField K] in

theorem hform_eq {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (x y : Fin d → K) :
    Formalism.DivisionValues.hform H x y = ∑ j, star (x j) * (H.mulVec y) j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring

omit [NumberField K] in

theorem star_int (c : 𝓞 K) : algebraMap (𝓞 K) K (Formalism.DivisionValues.cO K c) = star (algebraMap (𝓞 K) K c) := rfl

omit [StarRing K] in

theorem exists_extend {d : ℕ} (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A)
    (f : A →ₗ[𝓞 K] 𝓞 K) :
    ∃ F : (Fin d → K) →ₗ[K] K, ∀ x : A, F x = algebraMap (𝓞 K) K (f x) := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨s, hs, b, hb, hsA⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 K) A hA.span_eq_top
  obtain ⟨c, hc0, hc⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom (R := 𝓞 K) b A hA.fg
  have hbA : ∀ i, b i ∈ A := fun i => by rw [hb i]; exact hsA i.2
  let F : (Fin d → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩))
  let F' : A →ₗ[𝓞 K] K := (F.restrictScalars (𝓞 K)).comp A.subtype
  let g' : A →ₗ[𝓞 K] K := (Algebra.linearMap (𝓞 K) K).comp f
  let P : Submodule (𝓞 K) (Fin d → K) := (LinearMap.eqLocus F' g').map A.subtype
  have hspan : Submodule.span (𝓞 K) (Set.range b) ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨b i, hbA i⟩, ?_, rfl⟩
    show F (b i) = algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩)
    exact b.constr_basis K _ i
  refine ⟨F, fun x => ?_⟩
  obtain ⟨z, hz, hzx⟩ := hspan (hc x x.2)
  have hz' : z = c • x := Subtype.ext (by simpa using hzx)
  have hzF : F' z = g' z := hz
  rw [hz', map_smul, map_smul] at hzF
  simp only [F', g', LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
    Algebra.linearMap_apply, Algebra.smul_def] at hzF
  exact mul_left_cancel₀ (by simpa using hc0) hzF

theorem exists_family {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (hH : IsUnit H.det)
    (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A) :
    ∃ (n : ℕ) (a b : Fin n → Fin d → K), (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) ∧
      ∀ y, y = ∑ i, Formalism.DivisionValues.hform H (a i) y • b i := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨n, g, f, hgf⟩ := Formalism.HermitianLatticesTheory.finitely_generated_projective_coords (K := K) A hA.fg hinj
  choose F hF using fun i => exists_extend A hA (f i)
  let w : Fin n → Fin d → K := fun i => H⁻¹.mulVec (fun j => star (F i (Pi.single j 1)))
  have hFcoord : ∀ i (y : Fin d → K), F i y = ∑ j, y j * F i (Pi.single j 1) := by
    intro i y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (y j) : Fin d → K) = y j • Pi.single j 1 by
      ext k; by_cases hk : k = j <;> simp [hk], map_smul, smul_eq_mul]
  have hw : ∀ i (y : Fin d → K), Formalism.DivisionValues.hform H y (w i) = star (F i y) := by
    intro i y
    rw [hform_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec, hFcoord,
      star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
  have hexp : ∀ y : Fin d → K, y = ∑ i, F i y • (g i : Fin d → K) := by
    have hT : (∑ i, (F i).smulRight (g i : Fin d → K)) = LinearMap.id := by
      refine LinearMap.ext_on hA.span_eq_top fun x hx => ?_
      have h1 := congrArg (fun v : A => (v : Fin d → K)) (hgf ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      conv_rhs => rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hF i ⟨x, hx⟩, algebraMap_smul]
    intro y
    have := LinearMap.congr_fun hT y
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply] at this
    exact this.symm
  have hnd : ∀ z : Fin d → K, (∀ u, Formalism.DivisionValues.hform H u z = 0) → z = 0 := by
    intro z hz
    have hHz : H.mulVec z = 0 := by
      ext i
      have := hz (Pi.single i 1)
      rw [hform_eq, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (by simp)] at this
      simpa using this
    rw [← Matrix.one_mulVec z, ← Matrix.nonsing_inv_mul _ hH, ← Matrix.mulVec_mulVec, hHz,
      Matrix.mulVec_zero]
  refine ⟨n, fun i => (g i : Fin d → K), w, fun i => (g i).2, fun i => ?_, fun y => ?_⟩
  · rw [mem_dual_iff]
    intro y hy
    refine ⟨Formalism.DivisionValues.cO K (f i ⟨y, hy⟩), ?_⟩
    rw [star_int, hw, hF i ⟨y, hy⟩]
  · refine (sub_eq_zero.1 (hnd _ fun u => ?_)).symm
    rw [map_sub, sub_eq_zero, map_sum]
    conv_rhs => rw [hexp u]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, hw, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, mul_comm]

theorem dual_baseChange : ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] (φ : K →+* K') (d d' : ℕ)
  (G : Matrix (Fin d') (Fin d) K'), Function.Bijective G.mulVec → ∀ (H : Matrix (Fin d) (Fin d) K) (H' : Matrix (Fin d') (Fin d') K'),
  (∀ x y : Fin d → K, Formalism.DivisionValues.hform H' (Matrix.mulVec G fun k => φ (x k)) (Matrix.mulVec G fun k => φ (y k)) = φ (Formalism.DivisionValues.hform H x y)) →
  IsUnit H.det → ∀ A : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K A →
    Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H')
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K)))) =
    Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) ''
      ((Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K))) := by
  intro K K' _ _ _ _ _ _ φ d d' G hG H H' hHH' hH A hA
  classical
  set ι : (Fin d → K) → (Fin d' → K') := fun x => Matrix.mulVec G fun k => φ (x k) with hι
  have ι_add : ∀ x y, ι (x + y) = ι x + ι y := by
    intro x y
    simp only [hι, Pi.add_apply, map_add]
    rw [← Matrix.mulVec_add]
    rfl
  have ι_smul : ∀ (c : K) x, ι (c • x) = φ c • ι x := by
    intro c x
    simp only [hι, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← Matrix.mulVec_smul]
    rfl
  have ι_sum : ∀ {m : ℕ} (v : Fin m → Fin d → K), ι (∑ i, v i) = ∑ i, ι (v i) := by
    intro m v
    simp only [hι, Finset.sum_apply, map_sum]
    rw [← Matrix.mulVec_sum]
    congr 1
    ext k
    simp [Finset.sum_apply]
  have ι_single : ∀ k : Fin d, ι (Pi.single k 1) = G.mulVec (Pi.single k 1) := by
    intro k
    simp only [hι]
    congr 1
    ext j
    by_cases hj : j = k <;> simp [hj]
  have hspanι : Submodule.span K' (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨v, rfl⟩ := hG.2 z
    rw [← Finset.univ_sum_single v, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [show (Pi.single k (v k) : Fin d → K') = v k • Pi.single k 1 by
      ext j; by_cases hj : j = k <;> simp [hj], Matrix.mulVec_smul, ← ι_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hιH : ∀ x y, Formalism.DivisionValues.hform H' (ι x) (ι y) = φ (Formalism.DivisionValues.hform H x y) := hHH'
  apply le_antisymm
  · intro x hx
    obtain ⟨n, a, b, ha, hb, hab⟩ := exists_family H hH A hA
    have hT : (∑ i, (Formalism.DivisionValues.hform H' (ι (a i))).smulRight (ι (b i))) = LinearMap.id := by
      refine LinearMap.ext_on hspanι ?_
      rintro _ ⟨y, rfl⟩
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        hιH]
      conv_rhs => rw [hab y]
      rw [ι_sum]
      simp only [ι_smul]
    have hx' : x = ∑ i, Formalism.DivisionValues.hform H' (ι (a i)) x • ι (b i) := by
      have := LinearMap.congr_fun hT x
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply] at this
      exact this.symm
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := (mem_dual_iff H' _ x).1 hx (ι (a i))
      (Submodule.subset_span ⟨a i, ha i, rfl⟩)
    rw [← hc, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hb i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_dual_iff]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨c, hc⟩ := (mem_dual_iff H A z).1 hz y hy
      refine ⟨RingOfIntegers.mapRingHom φ c, ?_⟩
      rw [hιH, ← hc]
      rfl
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁⟩ := h₁
      obtain ⟨c₂, hc₂⟩ := h₂
      exact ⟨c₁ + c₂, by rw [map_add, map_add, LinearMap.add_apply, hc₁, hc₂]⟩
    | smul r y _ h =>
      obtain ⟨c, hc⟩ := h
      refine ⟨Formalism.DivisionValues.cO K' r * c, ?_⟩
      rw [← algebraMap_smul K' r y, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, hc,
        star_int, starRingEnd_apply]

end GlobalTheory.Mem.DualBC

end
