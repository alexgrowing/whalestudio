import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothInExponentialCoordsIffFirstSecondKind
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasSmoothLogNearOneOfIsUnitaryLieExpData

noncomputable section

open Matrix GlobalTheory.HolDict GlobalTheory.SmoothForms NormedSpace
open scoped ContDiff Topology

namespace GlobalTheory.HolDict.Chart

section Abstract

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] (σ : 𝔸 →ₗ[ℝ] 𝔸)

def skew : Submodule ℝ 𝔸 := LinearMap.ker (σ + LinearMap.id)

omit [FiniteDimensional ℝ 𝔸] in
theorem mem_skew {X : 𝔸} : X ∈ skew σ ↔ σ X = -X := by
  simp [skew, add_eq_zero_iff_eq_neg]

theorem mul_adj {a : 𝔸} (h : σ a * a = 1) : a * σ a = 1 := by
  haveI : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
  exact mul_eq_one_comm.1 h

def unit (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (invol : ∀ a, σ (σ a) = a) : Subgroup 𝔸ˣ where
  carrier := {u | σ u * u = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rw [anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]
  one_mem' := by simp [one]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    have : ((a⁻¹ : 𝔸ˣ) : 𝔸) = σ a := (Units.eq_inv_of_mul_eq_one_right ha).symm
    rw [this, invol, mul_adj σ ha]

open Classical in

def sec (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (invol : ∀ a, σ (σ a) = a) (a : 𝔸) :
    unit σ anti one invol :=
  if h : σ a * a = 1 then ⟨⟨a, σ a, mul_adj σ h, h⟩, h⟩ else 1

variable {σ} (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (invol : ∀ a, σ (σ a) = a)

theorem sec_val {a : 𝔸} (h : σ a * a = 1) : ((sec σ anti one invol a : 𝔸ˣ) : 𝔸) = a := by
  rw [sec, dif_pos h]

theorem lieData : IsLieData σ (skew σ).subtype (sec σ anti one invol) where
  anti := anti
  one := one
  invol := invol
  inj := Subtype.val_injective
  skew X := ⟨fun h => ⟨⟨X, (mem_skew σ).2 h⟩, rfl⟩, by rintro ⟨Y, rfl⟩; exact (mem_skew σ).1 Y.2⟩
  mul a b ha hb := by
    have hab : σ (a * b) * (a * b) = 1 := by rw [anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul, sec_val _ _ _ ha, sec_val _ _ _ hb, sec_val _ _ _ hab]

include anti one invol in
theorem exists_ext (T : Set (skew σ)) (hT : Submodule.span ℝ T = ⊤) (f : 𝔸 → ℂ)
    (hf : ∀ (k : ℕ) (Y : Fin k → skew σ), (∀ i, Y i ∈ T) → ∀ u, σ u * u = 1 →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => f (u * (List.ofFn fun i => exp (t i • (Y i : 𝔸))).prod))
    {u : 𝔸} (hu : σ u * u = 1) :
    ∃ F : 𝔸 → ℂ, ContDiffAt ℝ ∞ F u ∧ ∀ᶠ a in 𝓝 u, σ a * a = 1 → f a = F a := by
  have H := lieData anti one invol
  have hl := hasLog_of_isLieData _ _ _ _ _ _ H
  let ρ : unit σ anti one invol →* 𝔸 := (Units.coeHom 𝔸).comp (unit σ anti one invol).subtype
  have hρ : ∀ X : skew σ, ρ (expMap (skew σ).subtype (sec σ anti one invol) X) = exp (X : 𝔸) := fun X =>
    sec_val anti one invol (SecondKind.exp_unitary H X)
  have hs := (SecondKind.sm_iff H hl T hT fun g => f (ρ g)).2 fun k Y hY g => by
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, hρ]
    exact hf k Y hY _ g.2
  have h0 := hs (sec σ anti one invol u)
  simp only [map_mul, hρ] at h0
  rw [show ρ (sec σ anti one invol u) = u from sec_val anti one invol hu] at h0
  obtain ⟨Λ, l1, l2, -⟩ := hl
  have hc : ContDiff ℝ ∞ fun a : 𝔸 => σ u * a := contDiff_const.mul contDiff_id
  refine ⟨fun a => f (u * exp (Λ (σ u * a) : 𝔸)), ?_, ?_⟩
  · exact h0.contDiffAt.comp u (ContDiffAt.comp (g := Λ) u (by rwa [hu]) hc.contDiffAt)
  · have ht := hc.continuous.tendsto u
    rw [hu] at ht
    filter_upwards [ht.eventually l2] with a h ha
    have := h (by rw [anti, invol, mul_assoc, ← mul_assoc u, mul_adj σ hu, one_mul, ha])
    rw [Submodule.subtype_apply] at this
    rw [this, ← mul_assoc, mul_adj σ hu, one_mul]

include anti one invol in
theorem chain (T : Set (skew σ)) (hT : Submodule.span ℝ T = ⊤) (f : 𝔸 → ℂ)
    (hf : ∀ (k : ℕ) (Y : Fin k → skew σ), (∀ i, Y i ∈ T) → ∀ u, σ u * u = 1 →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => f (u * (List.ofFn fun i => exp (t i • (Y i : 𝔸))).prod))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : E → 𝔸} {x : E} (hγ : ContDiffAt ℝ ∞ γ x)
    (hu : ∀ᶠ y in 𝓝 x, σ (γ y) * γ y = 1) :
    ContDiffAt ℝ ∞ (fun y => f (γ y)) x ∧ ∃ D : 𝔸 →L[ℝ] ℂ,
      (∀ X, σ X = -X → deriv (fun t : ℝ => f (γ x * exp (t • X))) 0 = D X) ∧
      ∀ v, σ (σ (γ x) * fderiv ℝ γ x v) = -(σ (γ x) * fderiv ℝ γ x v) ∧
        fderiv ℝ (fun y => f (γ y)) x v = D (σ (γ x) * fderiv ℝ γ x v) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have h0 := hu.self_of_nhds
  obtain ⟨F, F1, F2⟩ := exists_ext anti one invol T hT f hf h0
  have e : (fun y => f (γ y)) =ᶠ[𝓝 x] fun y => F (γ y) := by
    filter_upwards [hu, hγ.continuousAt.tendsto.eventually F2] with y a b using b a
  have dF := (F1.differentiableAt (by simp)).hasFDerivAt
  have dγ := (hγ.differentiableAt (by simp)).hasFDerivAt
  refine ⟨(F1.comp x hγ).congr_of_eventuallyEq e, fderiv ℝ F (γ x) ∘L ContinuousLinearMap.mul ℝ 𝔸 (γ x),
    fun X hX => ?_, fun v => ⟨?_, ?_⟩⟩
  · have d1 : HasDerivAt (fun t : ℝ => γ x * exp (t • X)) (γ x * X) 0 := by
      simpa using (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).const_mul (γ x)
    have ht := d1.continuousAt.tendsto
    have e0 : γ x * exp ((0 : ℝ) • X) = γ x := by simp
    simp only [e0] at ht
    have e1 : (fun t : ℝ => f (γ x * exp (t • X))) =ᶠ[𝓝 0] fun t => F (γ x * exp (t • X)) := by
      filter_upwards [ht.eventually F2] with t h
      refine h ?_
      have := SecondKind.exp_unitary (lieData anti one invol) (t • (⟨X, (mem_skew σ).2 hX⟩ : skew σ))
      rw [anti, mul_assoc, ← mul_assoc (σ (γ x)), h0, one_mul]
      exact this
    rw [e1.deriv_eq]
    exact (HasFDerivAt.comp_hasDerivAt (l := F) (0 : ℝ) (by rw [e0]; exact dF) d1).deriv
  · let S : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap σ
    have d1 := (S.hasFDerivAt.comp x dγ).mul' dγ
    have d2 : HasFDerivAt (fun _ : E => (1 : 𝔸)) (0 : E →L[ℝ] 𝔸) x := hasFDerivAt_const _ _
    have := congrArg (fun A => A v) (d1.unique (d2.congr_of_eventuallyEq hu))
    rw [anti, invol, eq_neg_iff_add_eq_zero, add_comm]
    simpa [S] using this
  · rw [e.fderiv_eq]
    have := (dF.comp x dγ).fderiv
    rw [Function.comp_def] at this
    rw [this]
    simp [← mul_assoc, mul_adj σ h0]

end Abstract

section Concrete

def Alg (n : ℕ) (ι : Type) : Type := ι → Mt n

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

section Inst

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

instance : NormedRing (Alg n ι) := inferInstanceAs (NormedRing (ι → Mt n))

instance : NormedAlgebra ℝ (Alg n ι) := inferInstanceAs (NormedAlgebra ℝ (ι → Mt n))

instance : FiniteDimensional ℝ (Alg n ι) := inferInstanceAs (FiniteDimensional ℝ (ι → Mt n))

omit [DecidableEq ι] in
theorem exp_alg (X : Alg n ι) (τ : ι) : (exp X : Alg n ι) τ = exp (X τ : Mt n) :=
  @Pi.coe_exp ι (fun _ => Mt n) _ _ _ (fun _ => FiniteDimensional.complete ℝ _) X τ

end Inst

def sgl (τ : ι) (X : Mt n) : Alg n ι := (Pi.single τ X : ι → Mt n)

theorem exp_sgl (τ : ι) (X : Mt n) (t : ℝ) :
    (exp (t • sgl τ X) : Alg n ι) = (Pi.mulSingle τ (exp (t • X)) : ι → Mt n) := by
  funext ρ
  rw [exp_alg]
  change exp (t • (Pi.single τ X : ι → Mt n) ρ) = _
  by_cases h : ρ = τ
  · subst h; simp
  · simp [h]

theorem sum_sgl (X : Alg n ι) : ∑ τ, sgl τ (X τ) = X := Finset.univ_sum_single (X : ι → Mt n)

def adj (Hm : ι → Mt n) : Alg n ι →ₗ[ℝ] Alg n ι where
  toFun X := fun τ => (Hm τ)⁻¹ * (X τ)ᴴ * Hm τ
  map_add' X Y := funext fun τ => by
    change _ * (X τ + Y τ)ᴴ * _ = _ * (X τ)ᴴ * _ + _ * (Y τ)ᴴ * _
    rw [conjTranspose_add, mul_add, add_mul]
  map_smul' c X := funext fun τ => by
    change _ * (c • X τ)ᴴ * _ = c • (_ * (X τ)ᴴ * _)
    rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]

def coord (n : ℕ) (ι : Type) [Fintype ι] : (ι → Fin n → Fin n → ℂ) →L[ℝ] Alg n ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x τ => Matrix.of (x τ), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

variable {Hm : ι → Mt n} (hH : ∀ τ, (Hm τ).IsHermitian ∧ (Hm τ).det ≠ 0)
include hH

omit [DecidableEq ι] in
theorem unit_iff (u : Alg n ι) : adj Hm u * u = 1 ↔ u ∈ UG Hm := by
  refine funext_iff.trans (forall_congr' fun τ => ?_)
  change (Hm τ)⁻¹ * (u τ)ᴴ * Hm τ * u τ = 1 ↔ (u τ)ᴴ * Hm τ * u τ = Hm τ
  have h := (hH τ).2.isUnit
  constructor
  · intro h1
    have := congrArg (Hm τ * ·) h1
    simpa only [← mul_assoc, mul_nonsing_inv _ h, one_mul, mul_one] using this
  · intro h1
    rw [mul_assoc, mul_assoc, ← mul_assoc (u τ)ᴴ, h1, nonsing_inv_mul _ h]

omit [DecidableEq ι] in
theorem skew_iff (X : Alg n ι) : adj Hm X = -X ↔ ∀ τ, X τ ∈ lieH (Hm τ) := by
  refine funext_iff.trans (forall_congr' fun τ => ?_)
  change (Hm τ)⁻¹ * (X τ)ᴴ * Hm τ = -X τ ↔ (X τ)ᴴ * Hm τ + Hm τ * X τ = 0
  have h := (hH τ).2.isUnit
  constructor
  · intro h1
    rw [← mul_nonsing_inv_cancel_left _ ((X τ)ᴴ * Hm τ) h, ← mul_assoc (Hm τ)⁻¹, h1, mul_neg, neg_add_cancel]
  · intro h1
    rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ h]

theorem sgl_skew {τ : ι} {X : Mt n} (hX : X ∈ lieH (Hm τ)) : adj Hm (sgl τ X) = -sgl τ X := by
  refine (skew_iff hH _).2 fun ρ => ?_
  by_cases h : ρ = τ
  · subst h; simpa [sgl] using hX
  · simp [sgl, h, lieH]

omit [DecidableEq ι] in
theorem adj_anti (a b : Alg n ι) : adj Hm (a * b) = adj Hm b * adj Hm a := funext fun τ => by
  change _ * (a τ * b τ)ᴴ * _ = (_ * (b τ)ᴴ * _) * (_ * (a τ)ᴴ * _)
  rw [conjTranspose_mul]
  simp only [mul_assoc]
  rw [mul_nonsing_inv_cancel_left _ _ (hH τ).2.isUnit]

omit [DecidableEq ι] in
theorem adj_one : adj Hm 1 = 1 := funext fun τ => by
  change (Hm τ)⁻¹ * (1 : Mt n)ᴴ * Hm τ = 1
  rw [conjTranspose_one, mul_one, nonsing_inv_mul _ (hH τ).2.isUnit]

omit [DecidableEq ι] in
theorem adj_invol (a : Alg n ι) : adj Hm (adj Hm a) = a := funext fun τ => by
  change _ * (_ * (a τ)ᴴ * _)ᴴ * _ = a τ
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, (hH τ).1]
  simp only [mul_assoc]
  rw [nonsing_inv_mul_cancel_left _ _ (hH τ).2.isUnit, nonsing_inv_mul _ (hH τ).2.isUnit, mul_one]

theorem span_sgl : Submodule.span ℝ {Y : skew (adj Hm) | ∃ τ, ∃ X ∈ lieH (Hm τ), (Y : Alg n ι) = sgl τ X} = ⊤ := by
  rw [eq_top_iff]
  intro Y _
  have hY := (skew_iff hH _).1 ((mem_skew _).1 Y.2)
  have : Y = ∑ τ, (⟨sgl τ (Y.1 τ), (mem_skew _).2 (sgl_skew hH (hY τ))⟩ : skew (adj Hm)) := by
    refine Subtype.ext ?_
    rw [Submodule.coe_sum]
    exact (sum_sgl _).symm
  rw [this]
  exact Submodule.sum_mem _ fun τ _ => Submodule.subset_span ⟨τ, _, hY τ, rfl⟩

theorem chain_at {f : (ι → Mt n) → ℂ} (hf : SmFn Hm f) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : E → ι → Fin n → Fin n → ℂ} {x : E} (hγ : ContDiffAt ℝ ∞ γ x)
    (hu : ∀ᶠ y in 𝓝 x, (fun τ => Matrix.of (γ y τ)) ∈ UG Hm) :
    ContDiffAt ℝ ∞ (fun y => f fun τ => Matrix.of (γ y τ)) x ∧ ∀ v : E,
      fderiv ℝ (fun y => f fun τ => Matrix.of (γ y τ)) x v =
        ∑ τ, der τ ((Matrix.of (γ x τ))⁻¹ * Matrix.of (fderiv ℝ γ x v τ)) f (fun τ => Matrix.of (γ x τ)) := by
  have hu' : ∀ᶠ y in 𝓝 x, adj Hm (coord n ι (γ y)) * coord n ι (γ y) = 1 := hu.mono fun y h => (unit_iff hH _).2 h
  obtain ⟨c1, D, c2, c3⟩ := chain (adj_anti hH) (adj_one hH) (adj_invol hH) _ (span_sgl hH) (f : Alg n ι → ℂ)
    (fun k Y hY u hu => by
      choose τs Xs h1 h2 using hY
      simp only [h2, exp_sgl]
      exact hf k τs Xs h1 u ((unit_iff hH _).1 hu))
    (γ := fun y => coord n ι (γ y)) ((coord n ι).contDiff.contDiffAt.comp x hγ) hu'
  refine ⟨c1, fun v => ?_⟩
  obtain ⟨c4, c5⟩ := c3 v
  have e : fderiv ℝ (fun y => coord n ι (γ y)) x v = coord n ι (fderiv ℝ γ x v) := by
    have := ((coord n ι).hasFDerivAt.comp x (hγ.differentiableAt (by simp)).hasFDerivAt).fderiv
    rw [Function.comp_def] at this
    rw [this]; rfl
  rw [e] at c4 c5
  refine c5.trans ?_
  rw [← sum_sgl (adj Hm _ * _), map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← c2 _ (sgl_skew hH ((skew_iff hH _).1 c4 τ))]
  simp only [exp_sgl]
  have hi : (Matrix.of (γ x τ))⁻¹ = adj Hm (coord n ι (γ x)) τ :=
    Matrix.inv_eq_left_inv (congrFun hu'.self_of_nhds τ)
  rw [hi]
  rfl

end Concrete

theorem main : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n),
    (∀ τ, (Hm τ).IsHermitian ∧ (Hm τ).det ≠ 0) → ∀ f, SmFn Hm f →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U : Set E)
      (γ : E → ι → Fin n → Fin n → ℂ), IsOpen U → ContDiffOn ℝ ∞ γ U →
      (∀ x ∈ U, (fun τ => Matrix.of (γ x τ)) ∈ UG Hm) →
      ContDiffOn ℝ ∞ (fun x => f fun τ => Matrix.of (γ x τ)) U ∧ ∀ x ∈ U, ∀ v : E,
        fderiv ℝ (fun y => f fun τ => Matrix.of (γ y τ)) x v =
          ∑ τ, der τ ((Matrix.of (γ x τ))⁻¹ * Matrix.of (fderiv ℝ γ x v τ)) f (fun τ => Matrix.of (γ x τ)) := by
  intro n ι _ _ Hm hH f hf E _ _ _ U γ hU hγ hu
  have key := fun x (hx : x ∈ U) => chain_at hH hf (hγ.contDiffAt (hU.mem_nhds hx))
    (Filter.eventually_of_mem (hU.mem_nhds hx) hu)
  exact ⟨fun x hx => (key x hx).1.contDiffWithinAt, fun x hx => (key x hx).2⟩

end GlobalTheory.HolDict.Chart
