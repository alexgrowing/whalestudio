import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DenseHeight

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.IndexLog

variable {L : Type} [Field L] [NumberField L]

theorem card_quot_mul_absNorm {M : Type} [AddCommGroup M] [Module (𝓞 L) M] (ψ : M →ₗ[𝓞 L] 𝓞 L) (s : M) :
    Nat.card (M ⧸ Submodule.comap ψ (Ideal.span {ψ s} : Ideal (𝓞 L))) * Ideal.absNorm (LinearMap.range ψ) =
      Ideal.absNorm (Ideal.span {ψ s} : Ideal (𝓞 L)) := by
  set T : Ideal (𝓞 L) := Ideal.span {ψ s} with hT
  have hST : T ≤ LinearMap.range ψ :=
    (Ideal.span_singleton_le_iff_mem _).mpr ⟨s, rfl⟩
  have h := Submodule.card_quotient_mul_card_quotient (LinearMap.range ψ) T hST
  have hk : LinearMap.ker (T.mkQ ∘ₗ ψ) = Submodule.comap ψ T := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hr : LinearMap.range (T.mkQ ∘ₗ ψ) = (LinearMap.range ψ).map T.mkQ := LinearMap.range_comp _ _
  have hc : Nat.card (M ⧸ Submodule.comap ψ T) = Nat.card ((LinearMap.range ψ).map T.mkQ) := by
    rw [← hk, ← hr]
    exact Nat.card_congr (T.mkQ ∘ₗ ψ).quotKerEquivRange.toEquiv
  rw [hc]
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact h

theorem place_le_iSup {M : Type} [AddCommGroup M] [Module (𝓞 L) M] (φ : M →ₗ[𝓞 L] L) {n : ℕ} (g : Fin n → M)
    (hg : Submodule.span (𝓞 L) (Set.range g) = ⊤) (v : FinitePlace L) (x : M) :
    v (φ x) ≤ ⨆ i, v (φ (g i)) := by
  have hx : x ∈ Submodule.span (𝓞 L) (Set.range g) := hg ▸ Submodule.mem_top
  have h0 : 0 ≤ ⨆ i, v (φ (g i)) := Real.iSup_nonneg fun i ↦ apply_nonneg v _
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact le_ciSup (f := fun i ↦ v (φ (g i))) (Set.finite_range _).bddAbove i
  | zero => simpa using h0
  | add a b _ _ ha hb =>
    rw [map_add]
    exact (FinitePlace.add_le v _ _).trans (max_le ha hb)
  | smul r a _ ha =>
    rw [map_smul, Algebra.smul_def, map_mul]
    have hr : v (algebraMap (𝓞 L) L r) ≤ 1 :=
      finitePlace_le_one_of_isIntegral v (r.isIntegral_coe)
    calc v (algebraMap (𝓞 L) L r) * v (φ a) ≤ 1 * v (φ a) :=
          mul_le_mul_of_nonneg_right hr (apply_nonneg v _)
      _ ≤ _ := by simpa using ha

theorem support_log_finite {α : Type*} {f : α → ℝ} (hf : (Function.mulSupport f).Finite) :
    (Function.support fun a ↦ Real.log (f a)).Finite :=
  hf.subset fun a ha h1 ↦ ha (by simp only [h1, Real.log_one])

theorem log_card_eq {M : Type} [AddCommGroup M] [Module (𝓞 L) M] (φ : M →ₗ[𝓞 L] L) {n : ℕ} (g : Fin n → M)
    (hg : Submodule.span (𝓞 L) (Set.range g) = ⊤) (s : M) (hs : φ s ≠ 0) :
    Real.log (Nat.card (M ⧸ (Submodule.span (𝓞 L) {φ s}).comap φ)) =
      ∑ᶠ v : FinitePlace L, (Real.log (⨆ i, v (φ (g i))) - Real.log (v (φ s))) := by
  classical
  set y : Fin n → L := fun i ↦ φ (g i) with hydef
  have hy0 : y ≠ 0 := by
    intro h
    apply hs
    have hs' : s ∈ Submodule.span (𝓞 L) (Set.range g) := hg ▸ Submodule.mem_top
    have hle : Submodule.span (𝓞 L) (Set.range g) ≤ LinearMap.ker φ :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact congrFun h i)
    exact hle hs'
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L)) y
  choose z hz using hint
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : (b : L) ≠ 0 := by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hzy : ∀ i, ((z i : 𝓞 L) : L) = (b : L) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h

  have hint' : ∀ x, ∃ r : 𝓞 L, (r : L) = (b : L) * φ x := by
    intro x
    have hx : x ∈ Submodule.span (𝓞 L) (Set.range g) := hg ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact ⟨z i, hzy i⟩
    | zero => exact ⟨0, by simp⟩
    | add p q _ _ hp hq =>
      obtain ⟨r₁, h₁⟩ := hp
      obtain ⟨r₂, h₂⟩ := hq
      exact ⟨r₁ + r₂, by rw [map_add, mul_add, ← h₁, ← h₂]; rfl⟩
    | smul c p _ hp =>
      obtain ⟨r, h⟩ := hp
      refine ⟨c * r, ?_⟩
      rw [map_smul, Algebra.smul_def]
      change (c : L) * (r : L) = (b : L) * ((c : L) * φ p)
      rw [h]; ring
  choose ψ₀ hψ₀ using hint'
  let ψ : M →ₗ[𝓞 L] 𝓞 L :=
    { toFun := ψ₀
      map_add' := fun p q ↦ RingOfIntegers.ext (by
        change (ψ₀ (p + q) : L) = (ψ₀ p : L) + (ψ₀ q : L)
        rw [hψ₀, hψ₀, hψ₀, map_add, mul_add])
      map_smul' := fun c p ↦ RingOfIntegers.ext (by
        change (ψ₀ (c • p) : L) = (c : L) * (ψ₀ p : L)
        rw [hψ₀, hψ₀, map_smul, Algebra.smul_def]
        change (b : L) * ((c : L) * φ p) = _
        ring) }
  have hψ : ∀ x, ((ψ x : 𝓞 L) : L) = (b : L) * φ x := hψ₀
  have hψs0 : ψ s ≠ 0 := fun h ↦ by
    have := hψ s
    rw [h] at this
    exact mul_ne_zero hbL hs (by simpa using this.symm)
  have hcomap : Submodule.comap ψ (Ideal.span {ψ s} : Ideal (𝓞 L)) = (Submodule.span (𝓞 L) {φ s}).comap φ := by
    ext x
    simp only [Submodule.mem_comap, Ideal.mem_span_singleton', Submodule.mem_span_singleton]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_⟩
      have h := congrArg (fun t : 𝓞 L ↦ (t : L)) hr
      change (r : L) * (ψ s : L) = (ψ x : L) at h
      rw [hψ, hψ] at h
      rw [Algebra.smul_def]
      change (r : L) * φ s = φ x
      apply mul_left_cancel₀ hbL
      linear_combination h
    · rintro ⟨r, hr⟩
      refine ⟨r, RingOfIntegers.ext ?_⟩
      change (r : L) * (ψ s : L) = (ψ x : L)
      rw [hψ, hψ, ← hr, Algebra.smul_def]
      change (r : L) * ((b : L) * φ s) = (b : L) * ((r : L) * φ s)
      ring
  have hcard := card_quot_mul_absNorm ψ s
  rw [hcomap] at hcard
  have hJ : LinearMap.range ψ = Ideal.span (Set.range fun i ↦ ψ (g i)) := by
    rw [LinearMap.range_eq_map, ← hg, Submodule.map_span, ← Set.range_comp]
    rfl
  have hx0 : (fun i ↦ ψ (g i)) ≠ 0 := by
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy0
    intro h
    have h2 := hψ (g i0)
    rw [congrFun h i0] at h2
    exact mul_ne_zero hbL hi0 (by simpa [hydef] using h2.symm)
  have hJprod := absNorm_mul_finprod_finitePlace_eq_one hx0
  rw [← hJ] at hJprod
  have hsup : ∀ v : FinitePlace L, ⨆ i, v ((ψ (g i) : 𝓞 L) : L) = v (b : L) * ⨆ i, v (y i) := by
    intro v
    simp_rw [hψ, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg v _) _).symm
  simp_rw [hsup] at hJprod
  have hsprod := FinitePlace.prod_eq_inv_abs_norm_int hψs0
  simp_rw [hψ, map_mul] at hsprod
  have hNs : ((Ideal.absNorm (Ideal.span {ψ s} : Ideal (𝓞 L)) : ℕ) : ℝ) =
      |((Algebra.norm ℤ (ψ s) : ℤ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    push_cast
    rfl
  have hnorm0 : |((Algebra.norm ℤ (ψ s) : ℤ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]; exact hψs0

  have hvb : ∀ v : FinitePlace L, 0 < v (b : L) := fun v ↦ FinitePlace.pos_iff.mpr hbL
  have hvs : ∀ v : FinitePlace L, 0 < v (φ s) := fun v ↦ FinitePlace.pos_iff.mpr hs
  have hvt : ∀ v : FinitePlace L, 0 < ⨆ i, v (y i) := iSup_place_pos hy0
  have fb : (Function.mulSupport fun v : FinitePlace L ↦ v (b : L)).Finite :=
    FinitePlace.hasFiniteMulSupport hbL
  have fs : (Function.mulSupport fun v : FinitePlace L ↦ v (φ s)).Finite :=
    FinitePlace.hasFiniteMulSupport hs
  have ft : (Function.mulSupport fun v : FinitePlace L ↦ ⨆ i, v (y i)).Finite :=
    hasFiniteMulSupport_iSup_place hy0
  have fbt : (Function.mulSupport fun v : FinitePlace L ↦ v (b : L) * ⨆ i, v (y i)).Finite :=
    (fb.union ft).subset (Function.mulSupport_mul _ _)
  have fbs : (Function.mulSupport fun v : FinitePlace L ↦ v (b : L) * v (φ s)).Finite :=
    (fb.union fs).subset (Function.mulSupport_mul _ _)
  have e1 : ∑ᶠ v : FinitePlace L, (Real.log (⨆ i, v (y i)) - Real.log (v (φ s))) =
      ∑ᶠ v : FinitePlace L, Real.log (v (b : L) * ⨆ i, v (y i)) -
        ∑ᶠ v : FinitePlace L, Real.log (v (b : L) * v (φ s)) := by
    rw [← finsum_sub_distrib (support_log_finite fbt) (support_log_finite fbs)]
    refine finsum_congr fun v ↦ ?_
    rw [Real.log_mul (hvb v).ne' (hvt v).ne', Real.log_mul (hvb v).ne' (hvs v).ne']
    ring
  rw [e1, finsum_log_eq_log_finprod (fun v ↦ mul_pos (hvb v) (hvt v)) fbt,
    finsum_log_eq_log_finprod (fun v ↦ mul_pos (hvb v) (hvs v)) fbs, hsprod]
  set P := ∏ᶠ v : FinitePlace L, v (b : L) * ⨆ i, v (y i) with hP
  set NJ : ℝ := ((Ideal.absNorm (LinearMap.range ψ) : ℕ) : ℝ) with hNJ
  have hNJ0 : NJ ≠ 0 := fun h ↦ by rw [h, zero_mul] at hJprod; exact zero_ne_one hJprod
  have hP0 : P ≠ 0 := fun h ↦ by rw [h, mul_zero] at hJprod; exact zero_ne_one hJprod
  have hc : ((Nat.card (M ⧸ (Submodule.span (𝓞 L) {φ s}).comap φ) : ℕ) : ℝ) * NJ =
      |((Algebra.norm ℤ (ψ s) : ℤ) : ℝ)| := by
    rw [← hNs, ← hcard]; push_cast; rfl
  have hC : ((Nat.card (M ⧸ (Submodule.span (𝓞 L) {φ s}).comap φ) : ℕ) : ℝ) =
      P * |((Algebra.norm ℤ (ψ s) : ℤ) : ℝ)| := by
    linear_combination P * hc - ((Nat.card (M ⧸ (Submodule.span (𝓞 L) {φ s}).comap φ) : ℕ) : ℝ) * hJprod
  rw [hC, Real.log_mul hP0 hnorm0, Real.log_inv]
  ring

theorem abs_finsum_le {α : Type*} {f h : α → ℝ} (hh : (Function.support h).Finite) (hfh : ∀ a, |f a| ≤ h a) :
    |∑ᶠ a, f a| ≤ ∑ᶠ a, h a := by
  have hsub : Function.support f ⊆ hh.toFinset := by
    intro a ha
    have hne : h a ≠ 0 := fun h0 ↦ ha (abs_nonpos_iff.mp (h0 ▸ hfh a))
    exact Finset.mem_coe.mpr (hh.mem_toFinset.mpr hne)
  rw [finsum_eq_sum_of_support_subset f hsub,
    finsum_eq_sum_of_support_subset (s := hh.toFinset) h (by simp)]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ ↦ hfh a)

end GlobalTheory.CompanionTheory.Ar.RootHt.IndexLog

theorem GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le :
    ∀ (L : Type) [Field L] [NumberField L] (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc]
    (F₀ F₁ : Submodule (𝓞 L) Bc) (φ : F₁ →ₗ[𝓞 L] L) (s : F₁) (m : ℕ) (ρ : FinitePlace L → ℝ),
    F₁.FG → (∀ x, φ x = 0 ↔ (x : Bc) ∈ F₀) → φ s ≠ 0 → 0 < m → (∀ v, 0 < ρ v) → (Function.mulSupport ρ).Finite →
    (∀ v : FinitePlace L, (∀ x, v (φ x) ≤ (v (m : L))⁻¹ * ρ v) ∧ ∃ x, v (m : L) * ρ v ≤ v (φ x)) →
    |Real.log (Nat.card (F₁ ⧸ (F₀ ⊔ Submodule.span (𝓞 L) {(s : Bc)}).comap F₁.subtype)) -
      ∑ᶠ v : FinitePlace L, (Real.log (ρ v) - Real.log (v (φ s)))| ≤ Module.finrank ℚ L * Real.log m := by
  intro L _ _ Bc _ _ F₀ F₁ φ s m ρ hfg hker hs hm hρ hρf hloc
  classical
  haveI : Module.Finite (𝓞 L) F₁ := Module.Finite.iff_fg.mpr hfg
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := 𝓞 L) (M := F₁)
  have hC : (F₀ ⊔ Submodule.span (𝓞 L) {(s : Bc)}).comap F₁.subtype =
      (Submodule.span (𝓞 L) {φ s}).comap φ := by
    ext x
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_sup,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨f, hf, _, ⟨r, rfl⟩, hx⟩
      refine ⟨r, ?_⟩
      have hmem : ((x - r • s : F₁) : Bc) ∈ F₀ := by
        have : ((x - r • s : F₁) : Bc) = f := by
          rw [Submodule.coe_sub, Submodule.coe_smul, ← hx]; abel
        rw [this]; exact hf
      have := (hker _).mpr hmem
      rw [map_sub, map_smul, sub_eq_zero] at this
      exact this.symm
    · rintro ⟨r, hr⟩
      have h0 : φ (x - r • s) = 0 := by rw [map_sub, map_smul, hr, sub_self]
      refine ⟨_, (hker _).mp h0, _, ⟨r, rfl⟩, ?_⟩
      rw [Submodule.coe_sub, Submodule.coe_smul]; abel
  rw [hC, IndexLog.log_card_eq φ g hg s hs]
  have hmL : (m : L) ≠ 0 := by exact_mod_cast hm.ne'
  have hvm : ∀ v : FinitePlace L, 0 < v (m : L) := fun v ↦ FinitePlace.pos_iff.mpr hmL
  have hvs : ∀ v : FinitePlace L, 0 < v (φ s) := fun v ↦ FinitePlace.pos_iff.mpr hs
  have hne : Nonempty (Fin n) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    apply hs
    have hs' : s ∈ Submodule.span (𝓞 L) (Set.range g) := hg ▸ Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hs'
    rw [hs', map_zero]
  have hlow : ∀ v : FinitePlace L, v (m : L) * ρ v ≤ ⨆ i, v (φ (g i)) := fun v ↦ by
    obtain ⟨x, hx⟩ := (hloc v).2
    exact hx.trans (IndexLog.place_le_iSup φ g hg v x)
  have hup : ∀ v : FinitePlace L, (⨆ i, v (φ (g i))) ≤ (v (m : L))⁻¹ * ρ v := fun v ↦
    ciSup_le fun i ↦ (hloc v).1 (g i)
  have hvt : ∀ v : FinitePlace L, 0 < ⨆ i, v (φ (g i)) := fun v ↦
    (mul_pos (hvm v) (hρ v)).trans_le (hlow v)
  have fs := IndexLog.support_log_finite (FinitePlace.hasFiniteMulSupport hs)
  have fm := IndexLog.support_log_finite (FinitePlace.hasFiniteMulSupport hmL)
  have fρ := IndexLog.support_log_finite hρf
  have hy0 : (fun i ↦ φ (g i)) ≠ 0 := fun h ↦ by
    have hs' : s ∈ Submodule.span (𝓞 L) (Set.range g) := hg ▸ Submodule.mem_top
    have hle : Submodule.span (𝓞 L) (Set.range g) ≤ LinearMap.ker φ :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact congrFun h i)
    exact hs (hle hs')
  have ft := IndexLog.support_log_finite (hasFiniteMulSupport_iSup_place hy0)
  have e : ∑ᶠ v : FinitePlace L, (Real.log (⨆ i, v (φ (g i))) - Real.log (v (φ s))) -
        ∑ᶠ v : FinitePlace L, (Real.log (ρ v) - Real.log (v (φ s))) =
      ∑ᶠ v : FinitePlace L, (Real.log (⨆ i, v (φ (g i))) - Real.log (ρ v)) := by
    rw [finsum_sub_distrib ft fs, finsum_sub_distrib fρ fs, finsum_sub_distrib ft fρ]
    ring
  rw [e]
  have hb : ∀ v : FinitePlace L, |Real.log (⨆ i, v (φ (g i))) - Real.log (ρ v)| ≤ -Real.log (v (m : L)) := by
    intro v
    have h1 := Real.log_le_log (mul_pos (hvm v) (hρ v)) (hlow v)
    have h2 := Real.log_le_log (hvt v) (hup v)
    rw [Real.log_mul (hvm v).ne' (hρ v).ne'] at h1
    rw [Real.log_mul (inv_ne_zero (hvm v).ne') (hρ v).ne', Real.log_inv] at h2
    rw [abs_le]
    constructor <;> linarith
  have hfin : (Function.support fun v : FinitePlace L ↦ -Real.log (v (m : L))).Finite := by
    simpa [Function.support_neg] using fm
  refine (IndexLog.abs_finsum_le hfin hb).trans (le_of_eq ?_)
  rw [finsum_neg_distrib, finsum_log_finitePlace_natCast hm, neg_neg]
