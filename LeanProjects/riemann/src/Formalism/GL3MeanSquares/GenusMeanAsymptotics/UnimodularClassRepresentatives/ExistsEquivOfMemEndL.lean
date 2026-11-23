import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem ι_pow_smul (π : 𝓞 F) (r : ℕ) (w : V) :
    ι (π ^ r) • w = algebraMap F K (π : F) ^ r • w := by
  rw [← algebraMap_smul K (ι (π ^ r)) w]
  congr 1
  rw [map_pow, map_pow]
  rfl

theorem exists_pow_smul_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {π : 𝓞 F} (hπ : π ∈ 𝔭) (w : V) :
    ∃ n : ℕ, algebraMap F K (π : F) ^ n • w ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnw⟩ := Formalism.HermitianLatticesTheory.traceReal_mult A₀ hA₀ w
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u, hu, ?_⟩⟩
  have : ι u • (algebraMap F K (π : F) ^ r • w) = ι v • (n • w) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n w, smul_smul, ← map_mul, mul_comm v, ← hv, map_mul,
      mul_smul, ι_pow_smul]
  rw [this]
  exact A₀.smul_mem _ hnw

theorem exists_smul_le {A₀ B₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ r : ℕ, extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀ := by
  have := h𝔭.isPrime
  obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hA₀ hB₀
  have hc : ((n : ℤ) : 𝓞 F) ≠ 0 := by exact_mod_cast hn
  obtain ⟨r, u, hu, hdvd⟩ := exists_mul_dvd h𝔭 hc
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  obtain ⟨v, hv⟩ := hdvd (π ^ r) (Ideal.pow_mem_pow hπ r)
  refine ⟨r, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hx
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 A₀ y).1 hy
  refine (LocalSpans.mem_locF 𝔭 _ _).2 ⟨u * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hu ht, ?_⟩
  have : ι (u * t) • (algebraMap F K (π : F) ^ r • y) = ι v • (n • (ι t • y)) := by
    rw [← LocF.algebraMap_intCast_smul (K := K) (F := F) n, ← ι_pow_smul, smul_smul, smul_smul, smul_smul,
      ← map_mul, ← map_mul, ← map_mul]
    congr 2
    linear_combination t * hv
  rw [this]
  exact B₀.smul_mem _ (hnx _ hty)

theorem eq_zero_of_forall_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {v : V} (hv : ∀ j : ℕ, v ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) :
    v = 0 := by
  have := h𝔭.isPrime
  have h0 : v ∈ locF 𝔭 A₀ := by simpa [pow_zero_smul] using hv 0
  obtain ⟨t, ht, htv⟩ := (LocalSpans.mem_locF 𝔭 A₀ v).1 h0
  have h1 : ∀ j : ℕ, ι t • v ∈ extP K 𝔭 ^ j • A₀ := fun j =>
    localizedQuotients.mem_smul_of_mem_smul_locF h𝔭 A₀ j htv (Submodule.smul_mem _ _ (hv j))
  have : Module.Finite (𝓞 K) ↥A₀ := Module.Finite.iff_fg.2 hA₀.fg
  have h2 : (⟨ι t • v, htv⟩ : ↥A₀) ∈ (⨅ i : ℕ, extP K 𝔭 ^ i • ⊤ : Submodule (𝓞 K) ↥A₀) := by
    rw [Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_smul_top_iff]
    exact h1 j
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (extP K 𝔭) _).1 h2
  have hr' : (r : 𝓞 K) • (ι t • v) = ι t • v := congrArg Subtype.val hr
  have hr1 : (r : 𝓞 K) ≠ 1 := by
    intro e
    have h3 : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 := by rw [pow_one, ← e]; exact r.2
    have h4 : (1 : 𝓞 F) ∈ 𝔭 ^ 1 := (idealPowerSpanBounds.mem_pow_iff (K := K) 𝔭 1 1).1 (by simpa using h3)
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h4))
  have h5 : (algebraMap (𝓞 K) K ((r : 𝓞 K) - 1) * algebraMap F K (t : F)) • v = 0 := by
    rw [mul_smul, ← MeanB.algebraMap_comp, algebraMap_smul, algebraMap_smul, sub_smul, hr', one_smul,
      sub_self]
  rcases smul_eq_zero.1 h5 with h6 | h6
  · rcases mul_eq_zero.1 h6 with h7 | h7
    · exact absurd (sub_eq_zero.1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 h7)) hr1
    · exact absurd h7 (notMem_ne_zero ht)
  · exact h6

theorem unif_pow_mem_pK_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ : π ∈ 𝔭) (k : ℕ) :
    algebraMap F K (π : F) ^ k ∈ pK K 𝔭 0 := by
  refine ⟨1, Submonoid.one_mem _, ?_⟩
  rw [one_smul]
  refine ⟨ι (π ^ k), by simp, ?_⟩
  show algebraMap (𝓞 K) K (ι (π ^ k)) = _
  rw [map_pow, map_pow]
  rfl

theorem mem_of_add_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) (j : ℕ) {w : V}
    (hw : w + D w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀) : w ∈ extP K 𝔭 ^ j • locF 𝔭 A₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have hπ0 := unif_ne_zero (K := K) hπ'
  set p : K := algebraMap F K (π : F) with hp
  have key : ∀ w : V, w + D w ∈ locF 𝔭 A₀ → w ∈ locF 𝔭 A₀ := by
    intro w hw
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hA₀ h𝔭 hπ w
    induction n with
    | zero => simpa using hn
    | succ n ih =>
      apply ih
      have h1 : D (p ^ (n + 1) • w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        rw [pow_one]; exact hD _ hn
      have h2 : p ^ (n + 1) • (w + D w) ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ :=
        (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨p ^ n • (w + D w),
          smul_mem_locF h𝔭 A₀ (unif_pow_mem_pK_zero hπ n) hw, by rw [smul_smul, pow_one, pow_succ']⟩
      have h3 : p ^ (n + 1) • w ∈ extP K 𝔭 ^ 1 • locF 𝔭 A₀ := by
        have := sub_mem h2 h1
        rwa [map_smul, smul_add, add_sub_cancel_right] at this
      obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h3
      have : p ^ n • w = y := by
        apply smul_right_injective V hπ0
        show p • p ^ n • w = p • y
        rw [smul_smul, ← pow_succ', e, pow_one]
      rwa [this]
  obtain ⟨y, hy, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 hw
  refine (mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨(p ^ j)⁻¹ • w, key _ ?_, ?_⟩
  · rw [map_smul, ← smul_add, e, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hπ0), one_smul]
    exact hy
  · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero j hπ0), one_smul]

theorem exists_equiv_of_mem_endL {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {D : V →ₗ[K] V}
    (hD : D ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀)) :
    ∃ X : V ≃ₗ[K] V, (∀ x, X x = x + D x) ∧ X ∈ glSub (locF 𝔭 A₀) := by
  have hinj : Function.Injective (LinearMap.id + D : V →ₗ[K] V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hw' : w + D w = 0 := hw
    exact eq_zero_of_forall_mem hA₀ h𝔭 fun j =>
      mem_of_add_mem hA₀ h𝔭 hD j (by rw [hw']; exact zero_mem _)
  refine ⟨LinearEquiv.ofInjectiveEndo _ hinj, fun x => ?_, ?_⟩
  · rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
  · have hX : ∀ x, LinearEquiv.ofInjectiveEndo _ hinj x = x + D x := fun x => by
      rw [LinearEquiv.coe_ofInjectiveEndo]; rfl
    rw [mem_glSub]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show LinearEquiv.ofInjectiveEndo _ hinj x ∈ _
      rw [hX]
      exact add_mem hx (Submodule.smul_le_right (hD x hx))
    · intro y hy
      refine ⟨(LinearEquiv.ofInjectiveEndo _ hinj).symm y, ?_, LinearEquiv.apply_symm_apply _ y⟩
      have h1 := hX ((LinearEquiv.ofInjectiveEndo _ hinj).symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      have := mem_of_add_mem hA₀ h𝔭 hD 0 (w := (LinearEquiv.ofInjectiveEndo _ hinj).symm y)
        (by rw [← h1, pow_zero_smul]; exact hy)
      rwa [pow_zero_smul] at this

theorem mem_glSub_of_sub_mem {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {X : V ≃ₗ[K] V}
    (hX : ∀ x ∈ locF 𝔭 A₀, X x - x ∈ extP K 𝔭 • locF 𝔭 A₀) : X ∈ glSub (locF 𝔭 A₀) := by
  obtain ⟨Y, hY, hY'⟩ := exists_equiv_of_mem_endL hA₀ h𝔭
    (D := (X : V →ₗ[K] V) - LinearMap.id) (fun x hx => hX x hx)
  have : X = Y := by
    ext x
    rw [hY]
    simp
  rwa [this]

end Formalism.HermitianLattices.Ext.L3.D2
