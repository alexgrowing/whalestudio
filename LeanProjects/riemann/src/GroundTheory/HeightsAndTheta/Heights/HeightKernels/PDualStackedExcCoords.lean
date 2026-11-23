import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcResidueExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix StackedExceptionalFirstGeometric

noncomputable section

namespace StackedExceptionalCoordinates

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def ann (L : Submodule (𝓞 K) (Fin i → K)) (y : Fin i → K) : Ideal (𝓞 K) :=
  L.comap (LinearMap.toSpanSingleton (𝓞 K) (Fin i → K) y)

theorem mem_ann {L : Submodule (𝓞 K) (Fin i → K)} {y : Fin i → K} {μ : 𝓞 K} :
    μ ∈ ann L y ↔ μ • y ∈ L := Iff.rfl

variable {F F' : HermLattice K i}

theorem smul_mem_of_mem_ann (hle : F'.lattice ≤ F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {y : Fin i → K} (hyF : y ∈ F.lattice) (hy : y ∉ F'.lattice) {μ : 𝓞 K} (hμ : μ ∈ ann F'.lattice y)
    {x : Fin i → K} (hx : x ∈ F.lattice) : μ • x ∈ F'.lattice := by
  obtain ⟨z, hz, ν, rfl⟩ := exists_decomp hle hcov hyF hy hx
  rw [smul_add, smul_comm μ ν]
  exact add_mem (F'.lattice.smul_mem μ hz) (F'.lattice.smul_mem ν (mem_ann.mp hμ))

theorem ann_isMaximal (hle : F'.lattice ≤ F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {y : Fin i → K} (hyF : y ∈ F.lattice) (hy : y ∉ F'.lattice) : (ann F'.lattice y).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => hy (by simpa using mem_ann.mp h), fun J x hJ hx hxJ => ?_⟩
  obtain ⟨z, hz, ν, hzν⟩ := exists_decomp hle hcov (F.lattice.smul_mem x hyF) (mem_ann.not.mp hx) hyF
  have h1 : 1 - ν * x ∈ ann F'.lattice y := by
    rw [mem_ann, sub_smul, one_smul, mul_smul, sub_eq_of_eq_add hzν]
    exact hz
  have h2 := J.add_mem (hJ h1) (J.mul_mem_left ν hxJ)
  rwa [sub_add_cancel] at h2

theorem smul_mem_dual_of_mem_ann (hle : F'.lattice ≤ F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {y : Fin i → K} (hyF : y ∈ F.lattice) (hy : y ∉ F'.lattice) {c : 𝓞 K} (hc : c ∈ ann F'.lattice y)
    {φ : Fin i → K} (hφ : φ ∈ dualLattice F') : algebraMap (𝓞 K) K c • φ ∈ dualLattice F := by
  intro x hx
  rw [smul_dotProduct, ← dotProduct_smul, algebraMap_smul]
  exact hφ _ (smul_mem_of_mem_ann hle hcov hyF hy hc hx)

theorem exists_mul_not_mem {𝔪 : Ideal (𝓞 K)} (hmax : 𝔪.IsMaximal) {u : K}
    (hint : ∀ m ∈ 𝔪, algebraMap (𝓞 K) K m * u ∈ (algebraMap (𝓞 K) K).range)
    (hu : u ∉ (algebraMap (𝓞 K) K).range) :
    ∃ m ∈ 𝔪, ∃ β : 𝓞 K, algebraMap (𝓞 K) K m * u = algebraMap (𝓞 K) K β ∧ β ∉ 𝔪 := by
  have hbot : 𝔪 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmax (RingOfIntegers.not_isField K)
  by_contra hcon
  push Not at hcon
  let M : Submodule (𝓞 K) K := Submodule.map (Algebra.linearMap (𝓞 K) K) 𝔪
  have hint' : IsIntegral (𝓞 K) u := by
    refine isIntegral_of_smul_mem_submodule M ?_ ?_ u ?_
    · rw [Submodule.ne_bot_iff]
      obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
      simpa using hm0
    · exact Submodule.FG.map _ (IsNoetherian.noetherian _)
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨β, hβ⟩ := hint m hm
      refine ⟨β, hcon m hm β hβ.symm, ?_⟩
      rw [Algebra.linearMap_apply, hβ, smul_eq_mul, mul_comm]
      rfl
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint'
  exact hu ⟨w, hw⟩

theorem mul_not_mem {𝔪 : Ideal (𝓞 K)} (hmax : 𝔪.IsMaximal) {π : 𝓞 K} (hπ : π ∈ 𝔪) (hπ2 : π ∉ 𝔪 ^ 2) {u : K}
    (hint : ∀ m ∈ 𝔪, algebraMap (𝓞 K) K m * u ∈ (algebraMap (𝓞 K) K).range)
    (hu : u ∉ (algebraMap (𝓞 K) K).range) :
    ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K π * u → c ∉ 𝔪 := by
  intro c hc hc𝔪
  obtain ⟨m, hm, β, hβ, hβ𝔪⟩ := exists_mul_not_mem hmax hint hu
  obtain ⟨B, hB⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ)
  obtain ⟨β', hβ'B, hβ'𝔪⟩ : ∃ β' ∈ B, β' ∉ 𝔪 := by
    by_contra! h
    apply hπ2
    have h1 : Ideal.span {π} ≤ 𝔪 ^ 2 := by
      rw [hB, sq]
      exact Ideal.mul_mono_right h
    exact h1 (Ideal.mem_span_singleton_self π)
  have hmβ : m * β' ∈ Ideal.span {π} := by
    rw [hB]
    exact Ideal.mul_mem_mul hm hβ'B
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmβ
  have h1 : β' * β = r * c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    have h2 := congrArg (algebraMap (𝓞 K) K) hr
    simp only [map_mul] at h2 ⊢
    linear_combination (-algebraMap (𝓞 K) K β') * hβ - algebraMap (𝓞 K) K r * hc - u * h2
  have h2 : β' * β ∈ 𝔪 := h1 ▸ 𝔪.mul_mem_left r hc𝔪
  rcases hmax.isPrime.mem_or_mem h2 with h | h
  exacts [hβ'𝔪 h, hβ𝔪 h]

def intAt (F : HermLattice K i) (w : Fin i → K) (hw : w ∈ F.lattice) (φ : dualLattice F) : 𝓞 K :=
  ⟨(φ : Fin i → K) ⬝ᵥ w, DualLatticeIndexAlt.mem_integralClosure_of_mem_range (φ.2 w hw)⟩

theorem coe_intAt (F : HermLattice K i) (w : Fin i → K) (hw : w ∈ F.lattice) (φ : dualLattice F) :
    algebraMap (𝓞 K) K (intAt F w hw φ) = (φ : Fin i → K) ⬝ᵥ w := rfl

theorem intAt_zero (F : HermLattice K i) (w : Fin i → K) (hw : w ∈ F.lattice) : intAt F w hw 0 = 0 :=
  RingOfIntegers.coe_injective (zero_dotProduct w)

theorem intAt_add (F : HermLattice K i) (w : Fin i → K) (hw : w ∈ F.lattice) (φ ψ : dualLattice F) :
    intAt F w hw (φ + ψ) = intAt F w hw φ + intAt F w hw ψ :=
  RingOfIntegers.coe_injective (add_dotProduct (φ : Fin i → K) ψ w)

def redAt (F : HermLattice K i) {k : Type} [CommRing k] (ρ : 𝓞 K →+* k) (w : Fin i → K) (hw : w ∈ F.lattice) :
    dualLattice F →+ k where
  toFun φ := ρ (intAt F w hw φ)
  map_zero' := by rw [intAt_zero, map_zero]
  map_add' φ ψ := by rw [intAt_add, map_add]

theorem redAt_apply (F : HermLattice K i) {k : Type} [CommRing k] (ρ : 𝓞 K →+* k) (w : Fin i → K)
    (hw : w ∈ F.lattice) (φ : dualLattice F) : redAt F ρ w hw φ = ρ (intAt F w hw φ) := rfl

theorem exists_basis_ne {D T k : Type} [AddCommGroup D] [AddCommGroup k] (b : Module.Basis T ℤ D) (L : D →+ k)
    {φ : D} (hφ : L φ ≠ 0) : ∃ t, L (b t) ≠ 0 := by
  by_contra! h
  apply hφ
  have h1 : L.toIntLinearMap = 0 := b.ext fun t => h t
  exact LinearMap.congr_fun h1 φ

theorem forall_mem_of (hle : F'.lattice ≤ F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {y : Fin i → K} (hyF : y ∈ F.lattice) (hy : y ∉ F'.lattice) {m : ℕ} {g : Fin m → Fin i → K}
    (hg : Submodule.span (𝓞 K) (Set.range g) = F'.lattice) (𝔪 : Ideal (𝓞 K)) {φ : Fin i → K}
    (hφ : φ ∈ dualLattice F) (h0 : ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ y → c ∈ 𝔪)
    (hj : ∀ j, ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ g j → c ∈ 𝔪) :
    ∀ x ∈ F.lattice, ∃ c ∈ 𝔪, algebraMap (𝓞 K) K c = φ ⬝ᵥ x := by
  have hF' : ∀ z ∈ F'.lattice, ∃ c ∈ 𝔪, algebraMap (𝓞 K) K c = φ ⬝ᵥ z := by
    intro z hz
    rw [← hg] at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have hgj : g j ∈ F'.lattice := by
        rw [← hg]
        exact Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨c, hc⟩ := hφ (g j) (hle hgj)
      exact ⟨c, hj j c hc, hc⟩
    | zero => exact ⟨0, zero_mem _, by rw [map_zero, dotProduct_zero]⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc, e⟩ := hx
      obtain ⟨d, hd, f⟩ := hz
      exact ⟨c + d, add_mem hc hd, by rw [map_add, e, f, dotProduct_add]⟩
    | smul μ x _ hx =>
      obtain ⟨c, hc, e⟩ := hx
      exact ⟨μ * c, 𝔪.mul_mem_left μ hc, by
        rw [map_mul, e, ← algebraMap_smul K μ x, dotProduct_smul, smul_eq_mul]⟩
  intro x hx
  obtain ⟨z, hz, ν, rfl⟩ := exists_decomp hle hcov hyF hy hx
  obtain ⟨c, hc, e⟩ := hF' z hz
  obtain ⟨d, hd⟩ := hφ y hyF
  exact ⟨c + ν * d, add_mem hc (𝔪.mul_mem_left ν (h0 d hd)), by
    rw [map_add, map_mul, e, hd, dotProduct_add, ← algebraMap_smul K ν y, dotProduct_smul, smul_eq_mul]⟩

theorem mem_span_of_forall {𝔪 B : Ideal (𝓞 K)} {π : 𝓞 K} (hπ0 : π ≠ 0) (hB : Ideal.span {π} = 𝔪 * B)
    {φ : Fin i → K} (hφ : ∀ x ∈ F.lattice, ∃ c ∈ 𝔪, algebraMap (𝓞 K) K c = φ ⬝ᵥ x) :
    φ ∈ Submodule.span ℤ {ψ | ∃ c : 𝓞 K, Ideal.Quotient.mk 𝔪 c = 0 ∧ ∃ χ ∈ dualLattice F,
      ψ = algebraMap (𝓞 K) K c • χ} := by
  have hπK : algebraMap (𝓞 K) K π ≠ 0 := by simpa using hπ0
  have key : ∀ z ∈ 𝔪 * B, (algebraMap (𝓞 K) K z / algebraMap (𝓞 K) K π) • φ ∈
      Submodule.span ℤ {ψ | ∃ c : 𝓞 K, Ideal.Quotient.mk 𝔪 c = 0 ∧ ∃ χ ∈ dualLattice F,
        ψ = algebraMap (𝓞 K) K c • χ} := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro a ha b hb
      have hχ : (algebraMap (𝓞 K) K b / algebraMap (𝓞 K) K π) • φ ∈ dualLattice F := by
        intro x hx
        obtain ⟨c, hc𝔪, hc⟩ := hφ x hx
        have hcb : c * b ∈ Ideal.span {π} := by
          rw [hB]
          exact Ideal.mul_mem_mul hc𝔪 hb
        obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hcb
        refine ⟨r, ?_⟩
        have h2 := congrArg (algebraMap (𝓞 K) K) hr
        simp only [map_mul] at h2
        rw [smul_dotProduct, ← hc, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hπK]
        linear_combination h2
      refine Submodule.subset_span ⟨a, Ideal.Quotient.eq_zero_iff_mem.mpr ha, _, hχ, ?_⟩
      rw [smul_smul, map_mul, mul_div_assoc]
    · intro x y hx hy
      rw [map_add, add_div, add_smul]
      exact add_mem hx hy
  have hπB : π ∈ 𝔪 * B := by
    rw [← hB]
    exact Ideal.mem_span_singleton_self π
  have h1 := key π hπB
  rwa [div_self hπK, one_smul] at h1

end StackedExceptionalCoordinates

open StackedExceptionalCoordinates in

theorem DualStackedExcCoords.proof : DualStackedExcCoords.Statement := by
  intro K _ _ i F F' T _ _ b b' a _ hlt hcov _
  have hle := hlt.le
  obtain ⟨y₀, hyF, hy⟩ := SetLike.exists_of_lt hlt
  have hmax : (ann F'.lattice y₀).IsMaximal := ann_isMaximal hle hcov hyF hy
  set 𝔪 := ann F'.lattice y₀ with h𝔪
  have hbot : 𝔪 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmax (RingOfIntegers.not_isField K)
  obtain ⟨π, hπ, hπ2⟩ : ∃ π ∈ 𝔪, π ∉ 𝔪 ^ 2 := by
    simpa using Ideal.exists_mem_pow_notMem_pow_succ 𝔪 hbot hmax.ne_top 1
  have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ zero_mem _)
  obtain ⟨B, hB⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ)
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp F'.fg
  have hgF' : ∀ j, g j ∈ F'.lattice := fun j => by
    rw [← hg]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hgF : ∀ j, g j ∈ F.lattice := fun j => hle (hgF' j)
  obtain ⟨φc, hc, hc'⟩ := StackedExceptionalResidueExists.exists_mem_not_mem hlt
  have hu : φc ⬝ᵥ y₀ ∉ (algebraMap (𝓞 K) K).range := fun h => hc' (mem_dual_of hle hcov hyF hy hc h)
  have hint : ∀ μ ∈ 𝔪, algebraMap (𝓞 K) K μ * (φc ⬝ᵥ y₀) ∈ (algebraMap (𝓞 K) K).range := by
    intro μ hμ
    have h1 := hc _ (mem_ann.mp hμ)
    rwa [← algebraMap_smul K μ y₀, dotProduct_smul, smul_eq_mul] at h1
  have hkey := mul_not_mem hmax hπ hπ2 hint hu
  have hπy : algebraMap (𝓞 K) K π • y₀ ∈ F'.lattice := by
    rw [algebraMap_smul]
    exact mem_ann.mp hπ
  let _ : Field (𝓞 K ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hρ : ∀ c : 𝓞 K, Ideal.Quotient.mk 𝔪 c = 0 ↔ c ∈ 𝔪 := fun c => Ideal.Quotient.eq_zero_iff_mem
  have h10 : ∀ c : 𝓞 K, Ideal.Quotient.mk 𝔪 c = 0 → ∀ φ ∈ dualLattice F',
      algebraMap (𝓞 K) K c • φ ∈ dualLattice F :=
    fun c hc0 φ hφ => smul_mem_dual_of_mem_ann hle hcov hyF hy ((hρ c).mp hc0) hφ
  refine ⟨𝓞 K ⧸ 𝔪, inferInstance, Ideal.Quotient.mk 𝔪, π, y₀, m, g,
    fun t => redAt F' (Ideal.Quotient.mk 𝔪) _ hπy (b' t),
    fun t => (Fin.cons (redAt F (Ideal.Quotient.mk 𝔪) y₀ hyF (b t))
      (fun j => redAt F (Ideal.Quotient.mk 𝔪) (g j) (hgF j) (b t)) : Fin (m + 1) → 𝓞 K ⧸ 𝔪),
    Ideal.Quotient.mk_surjective, (hρ π).mpr hπ, hyF, hgF',
    fun t => ⟨_, coe_intAt F' _ hπy (b' t), rfl⟩, fun t => ⟨_, coe_intAt F y₀ hyF (b t), by simp [redAt_apply]⟩,
    fun t j => ⟨_, coe_intAt F (g j) (hgF j) (b t), by simp [redAt_apply]⟩, ?_, ?_, h10, ?_, ?_⟩
  ·
    refine exists_basis_ne b' _ (φ := ⟨φc, hc⟩) ?_
    rw [redAt_apply, Ne, hρ]
    refine hkey _ ?_
    rw [coe_intAt, dotProduct_smul, smul_eq_mul]
  ·
    obtain ⟨t, ht⟩ := exists_basis_ne b (redAt F (Ideal.Quotient.mk 𝔪) y₀ hyF)
      (φ := ⟨algebraMap (𝓞 K) K π • φc, h10 π ((hρ π).mpr hπ) φc hc⟩) (by
        rw [redAt_apply, Ne, hρ]
        refine hkey _ ?_
        rw [coe_intAt, smul_dotProduct, smul_eq_mul])
    exact ⟨t, by simpa using ht⟩
  ·
    intro φ hφ c hcdef hc0
    obtain ⟨l, hl⟩ := exists_sub_mem_dual hlt hcov hc hc' hφ
    obtain ⟨s, hs⟩ := hl y₀ hyF
    obtain ⟨c₀, hc₀⟩ := hc _ hπy
    have hc₀𝔪 : c₀ ∉ 𝔪 := hkey c₀ (by rw [hc₀, dotProduct_smul, smul_eq_mul])
    have hsum : c = π * s + l * c₀ := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_add, map_mul, map_mul, hs, hc₀, hcdef]
      simp only [dotProduct_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]
      ring
    have hl𝔪 : l ∈ 𝔪 := by
      have h1 : l * c₀ ∈ 𝔪 := by
        have h2 : l * c₀ = c - π * s := by rw [hsum]; ring
        rw [h2]
        exact sub_mem ((hρ c).mp hc0) (𝔪.mul_mem_right s hπ)
      exact (hmax.isPrime.mem_or_mem h1).resolve_right hc₀𝔪
    have h1 := add_mem hl (h10 l ((hρ l).mpr hl𝔪) φc hc)
    rwa [sub_add_cancel] at h1
  ·
    intro φ hφ h0 hj
    exact mem_span_of_forall hπ0 hB (forall_mem_of hle hcov hyF hy hg 𝔪 hφ
      (fun c hc1 => (hρ c).mp (h0 c hc1)) (fun j c hc1 => (hρ c).mp (hj j c hc1)))

end

end GroundTheory.Heights₂.Heights
