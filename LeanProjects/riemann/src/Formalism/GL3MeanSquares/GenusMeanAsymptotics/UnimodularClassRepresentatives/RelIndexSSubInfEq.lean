import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SurjectiveOfNondegenerate

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private theorem exists_int_add_star_eq_one_of_isCMUnram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ θ : 𝓞 K, algebraMap (𝓞 K) K θ + star (algebraMap (𝓞 K) K θ) = 1 := by
  classical
  have hstarF : ∀ f : F, star (algebraMap F K f) = algebraMap F K f := fun f => (hF _).mpr ⟨f, rfl⟩
  have hint : ∀ c : 𝓞 F, IsIntegral ℤ (algebraMap F K (algebraMap (𝓞 F) F c)) := fun c =>
    (isIntegral_algebraMap_iff (algebraMap F K).injective).mpr
      (NumberField.RingOfIntegers.isIntegral_coe c)
  have hcompat : ∀ x : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) =
      algebraMap F K (algebraMap (𝓞 F) F x) := fun x => rfl
  let tr : 𝓞 K → K := fun θ => algebraMap (𝓞 K) K θ + star (algebraMap (𝓞 K) K θ)
  show ∃ θ : 𝓞 K, tr θ = 1
  by_contra hne
  push_neg at hne
  let I : Ideal (𝓞 F) :=
    { carrier := {a | ∃ θ : 𝓞 K, tr θ = algebraMap F K (algebraMap (𝓞 F) F a)}
      add_mem' := by
        rintro a b ⟨θ, hθ⟩ ⟨θ', hθ'⟩
        refine ⟨θ + θ', ?_⟩
        simp only [tr, map_add, star_add] at hθ hθ' ⊢
        linear_combination hθ + hθ'
      zero_mem' := ⟨0, by simp [tr]⟩
      smul_mem' := by
        rintro c a ⟨θ, hθ⟩
        refine ⟨algebraMap (𝓞 F) (𝓞 K) c * θ, ?_⟩
        simp only [tr, smul_eq_mul, map_mul, star_mul', hcompat, hstarF] at hθ ⊢
        linear_combination (algebraMap F K (algebraMap (𝓞 F) F c)) * hθ }
  have hI : (1 : 𝓞 F) ∉ I := by
    rintro ⟨θ, hθ⟩
    exact hne θ (by simpa using hθ)
  obtain ⟨𝔮, h𝔮, hI𝔮⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).mpr hI)
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔮 := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have h1 : algebraMap F K (algebraMap (𝓞 F) F x) = algebraMap F K (algebraMap (𝓞 F) F 0) := by
      rw [← hcompat, hx, map_zero, map_zero, map_zero]
    have h2 := IsFractionRing.injective (𝓞 F) F ((algebraMap F K).injective h1)
    rw [h2]
    exact 𝔮.zero_mem
  obtain ⟨P, hP, hP𝔮⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) 𝔮 hker
  obtain ⟨a, t, ht, hat⟩ := hK.2.2 P hP
  have hta : star (algebraMap (𝓞 K) K t) = algebraMap (𝓞 K) K a := by rw [ht, star_star]
  have hdfix : star ((algebraMap (𝓞 K) K a - algebraMap (𝓞 K) K t) ^ 2) =
      (algebraMap (𝓞 K) K a - algebraMap (𝓞 K) K t) ^ 2 := by
    rw [star_pow, star_sub, ← ht, hta]
    ring
  obtain ⟨f, hf⟩ := (hF _).mp hdfix
  have hfi : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (A := F) (B := K) (algebraMap F K).injective, hf]
    have := NumberField.RingOfIntegers.isIntegral_coe ((a - t) ^ 2)
    simpa using this
  let fO : 𝓞 F := ⟨f, hfi⟩
  have hfI : fO ∈ I := by
    refine ⟨a * (a - t), ?_⟩
    show algebraMap (𝓞 K) K (a * (a - t)) + star (algebraMap (𝓞 K) K (a * (a - t))) =
      algebraMap F K f
    rw [hf]
    simp only [map_mul, map_sub, star_mul', star_sub, ← ht, hta]
    ring
  have hmem : algebraMap (𝓞 F) (𝓞 K) fO ∈ P := by
    rw [← Ideal.mem_comap, hP𝔮]
    exact hI𝔮 hfI
  have heq : algebraMap (𝓞 F) (𝓞 K) fO = (a - t) ^ 2 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [hcompat]
    show algebraMap F K f = _
    rw [hf]
    simp
  rw [heq] at hmem
  exact hat (hP.isPrime.mem_of_pow_mem 2 hmem)

theorem exists_theta (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    ∃ θ : K, θ ∈ pK K 𝔭 0 ∧ θ + star θ = 1 := by
  obtain ⟨θ, hθ⟩ := exists_int_add_star_eq_one_of_isCMUnram hK hF
  exact ⟨algebraMap (𝓞 K) K θ, algebraMap_mem_pK 𝔭 θ, hθ⟩

theorem mul_inv_mem_iff {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {n : ℕ}
    {U W : V ≃ₗ[K] V} (hUA : U ∈ glSub A) (hUB : U ∈ glSub B) (hWA : W ∈ glSub A) (hWB : W ∈ glSub B) :
    U * W⁻¹ ∈ sSub h B 𝔭 n ⊓ glSub A ↔ IA.phi h U - IA.phi h W ∈ hermL B 𝔭 n := by
  have eW : ∀ z : V, W (W⁻¹ z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  have eW' : ∀ z : V, W⁻¹ (W z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  constructor
  · intro hX
    have hX' := (Subgroup.mem_inf.mp hX).1.2
    refine ⟨fun x y => ?_, fun x hx y hy => ?_⟩
    · simp only [AddSubgroupClass.coe_sub, LinearMap.sub_apply, star_sub, IA.star_phi hs]
    · have := hX' (W x) (apply_mem hWB hx) (W y) (apply_mem hWB hy)
      simp only [LinearEquiv.mul_apply, eW'] at this
      simpa only [LinearMap.sub_apply, IA.phi_apply, sub_sub_sub_cancel_right] using this
  · intro hZ
    refine Subgroup.mem_inf.mpr ⟨⟨mul_mem hUB (inv_mem hWB), fun x hx y hy => ?_⟩,
      mul_mem hUA (inv_mem hWA)⟩
    have := hZ.2 (W⁻¹ x) (apply_mem (inv_mem hWB) hx) (W⁻¹ y) (apply_mem (inv_mem hWB) hy)
    simp only [LinearMap.sub_apply, IA.phi_apply, sub_sub_sub_cancel_right, eW] at this
    simpa only [LinearEquiv.mul_apply] using this

theorem exists_newton (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {r r' e : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (he : ∀ (k : ℕ) (x : V), (∀ y ∈ locF 𝔭 A₀, h y x ∈ pK K 𝔭 (k + e)) → x ∈ extP K 𝔭 ^ k • locF 𝔭 A₀)
    {k c : ℕ} (hk : c + 2 * e + 2 * r' + r + r' + 1 ≤ k) {Z : V →ₗ⋆[K] V →ₗ[K] K}
    (hZ : Z ∈ hermL (locF 𝔭 A₀) 𝔭 k) :
    ∃ X ∈ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀), IA.phi h X - Z ∈ hermL (locF 𝔭 B₀) 𝔭 (k + c) := by
  have hsym : ∀ a b : V, star (h a b) = h b a := by
    intro a b
    exact hs.eq a b
  obtain ⟨θ₀, hθ1⟩ := exists_int_add_star_eq_one_of_isCMUnram hK hF
  set θ : K := algebraMap (𝓞 K) K θ₀ with hθdef
  obtain ⟨Y0, hY0⟩ := IA.exists_adj hs (nondegenerate hd) Z
  set Y : V →ₗ[K] V := θ • Y0 with hYdef
  have hhY : ∀ x y, h x (Y y) = θ * Z x y := by
    intro x y
    rw [hYdef, LinearMap.smul_apply, map_smul, hY0, smul_eq_mul]
  have hYh : ∀ x y, h (Y x) y = star θ * Z x y := by
    intro x y
    rw [← hsym y (Y x), hhY, star_mul', hZ.1 y x]

  have hYA : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ (k - e) • locF 𝔭 A₀ := by
    intro x hx
    refine he (k - e) (Y x) fun y hy => ?_
    rw [hhY, show k - e + e = k by omega, hθdef, ← Algebra.smul_def]
    exact (pK K 𝔭 k).smul_mem θ₀ (hZ.2 y hy x hx)
  have hDA : Y ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := fun x hx =>
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) (hYA x hx)
  obtain ⟨X, hXeq, hXA⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hDA
  have hYB := IA.end_scale h𝔭 hr hr' Y (n := 1) (m := k - e) (by omega) hYA
  have hDB : Y ∈ endL (locF 𝔭 B₀) (extP K 𝔭 • locF 𝔭 B₀) := fun x hx => by
    simpa only [pow_one] using hYB x hx
  obtain ⟨X', hX'eq, hX'B⟩ := exists_equiv_of_mem_endL hB₀ h𝔭 hDB
  have hXX : X = X' := LinearEquiv.ext fun x => by rw [hXeq, hX'eq]
  have hphi : ∀ x y, IA.phi h X x y - Z x y = h (Y x) (Y y) := by
    intro x y
    rw [IA.phi_apply, hXeq, hXeq]
    simp only [map_add, LinearMap.add_apply]
    rw [hhY, hYh]
    linear_combination (Z x y) * hθ1
  have hYY : ∀ x ∈ locF 𝔭 A₀, ∀ y ∈ locF 𝔭 A₀, h (Y x) (Y y) ∈ pK K 𝔭 ((k - e) + (k - e)) :=
    fun x hx y hy => form_mem_pK hF hA₀i h𝔭 (hYA x hx) (hYA y hy)
  refine ⟨X, Subgroup.mem_inf.mpr ⟨mem_sSub.mpr ⟨hXA, fun x hx y hy => ?_⟩, hXX ▸ hX'B⟩, ?_, ?_⟩
  · have e1 : h (X x) (X y) - h x y = Z x y + h (Y x) (Y y) := by
      rw [← IA.phi_apply]
      linear_combination hphi x y
    rw [e1]
    exact add_mem (hZ.2 x hx y hy) (pK_anti 𝔭 (by omega) (hYY x hx y hy))
  · intro x y
    simp only [LinearMap.sub_apply, star_sub, IA.star_phi hs, hZ.1]
  · refine IA.sesq_scale hF h𝔭 hr' (IA.phi h X - Z) (n := k + c) (m := (k - e) + (k - e))
      (by omega) ?_
    intro x hx y hy
    rw [LinearMap.sub_apply, LinearMap.sub_apply, hphi]
    exact hYY x hx y hy

theorem relIndex_sSub_inf_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ∧
      sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k ∧
      (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) =
        (hermL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (hermL (locF 𝔭 A₀) 𝔭 k) := by
  obtain ⟨r, hr⟩ := exists_smul_le hA₀ hB₀ h𝔭
  obtain ⟨r', hr'⟩ := exists_smul_le hB₀ hA₀ h𝔭
  obtain ⟨e, he⟩ := exists_dual_bound hK hF hs hd hA₀ h𝔭
  refine ⟨2 * r, fun c hc => ⟨c + 2 * e + 2 * r' + r + r' + 1, fun k hk => ?_⟩⟩

  have hGA : ∀ {X : V ≃ₗ[K] V}, X ∈ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) →
      X ∈ glSub (locF 𝔭 A₀) ∧ X ∈ glSub (locF 𝔭 B₀) := fun hX =>
    ⟨(mem_sSub.mp (Subgroup.mem_inf.mp hX).1).1, (Subgroup.mem_inf.mp hX).2⟩
  have hphiA : ∀ {X : V ≃ₗ[K] V}, X ∈ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) →
      IA.phi h X ∈ hermL (locF 𝔭 A₀) 𝔭 k := by
    intro X hX
    refine ⟨fun x y => IA.star_phi hs X x y, fun x hx y hy => ?_⟩
    rw [IA.phi_apply]
    exact (mem_sSub.mp (Subgroup.mem_inf.mp hX).1).2 x hx y hy
  have hsesq : sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k := fun s hs' =>
    IA.sesq_scale hF h𝔭 hr s (n := k) (m := k + c) (by omega) hs'
  have hHG : sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤
      sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) := by
    intro X hX
    obtain ⟨hXB, hXA⟩ := Subgroup.mem_inf.mp hX
    obtain ⟨hXBgl, hXBv⟩ := mem_sSub.mp hXB
    refine Subgroup.mem_inf.mpr ⟨mem_sSub.mpr ⟨hXA, fun x hx y hy => ?_⟩, hXBgl⟩
    have := IA.sesq_scale hF h𝔭 hr (IA.phi h X) (n := k) (m := k + c) (by omega)
      (fun x hx y hy => by rw [IA.phi_apply]; exact hXBv x hx y hy) x hx y hy
    rwa [IA.phi_apply] at this
  refine ⟨hHG, hsesq, ?_⟩
  set G := sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) with hGdef
  set H := sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) with hHdef
  set HA := hermL (locF 𝔭 A₀) 𝔭 k with hHAdef
  set HB := hermL (locF 𝔭 B₀) 𝔭 (k + c) with hHBdef

  have key : ∀ X Y : G, (QuotientGroup.mk X : G ⧸ H.subgroupOf G) = QuotientGroup.mk Y ↔
      IA.phi h (X : V ≃ₗ[K] V)⁻¹ - IA.phi h (Y : V ≃ₗ[K] V)⁻¹ ∈ HB := by
    intro X Y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hX := hGA (inv_mem X.2)
    have hY := hGA (inv_mem Y.2)
    have := mul_inv_mem_iff hs (𝔭 := 𝔭) (n := k + c) hX.1 hX.2 hY.1 hY.2
    rw [inv_inv] at this
    rw [← this]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    try exact Iff.rfl
  have hmk : ∀ X : G, IA.phi h (X : V ≃ₗ[K] V)⁻¹ ∈ HA := fun X => hphiA (inv_mem X.2)
  have keyA : ∀ a b : HA, (QuotientAddGroup.mk a : HA ⧸ HB.addSubgroupOf HA) = QuotientAddGroup.mk b ↔
      (a : V →ₗ⋆[K] V →ₗ[K] K) - b ∈ HB := by
    intro a b
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add,
      AddSubgroup.coe_neg]
    constructor
    · intro hab
      have := HB.neg_mem hab
      rwa [neg_add_eq_sub, neg_sub] at this
    · intro hab
      have := HB.neg_mem hab
      rwa [neg_sub, sub_eq_neg_add] at this
  let f : G ⧸ H.subgroupOf G → HA ⧸ HB.addSubgroupOf HA :=
    Quotient.lift (fun X : G => (QuotientAddGroup.mk ⟨_, hmk X⟩ : HA ⧸ HB.addSubgroupOf HA))
      (fun X Y hXY => (keyA _ _).mpr ((key X Y).mp (Quotient.sound hXY)))
  have hinj : Function.Injective f := by
    intro q₁ q₂
    induction q₁ using QuotientGroup.induction_on with
    | H X =>
    induction q₂ using QuotientGroup.induction_on with
    | H Y =>
    intro hXY
    exact (key X Y).mpr ((keyA _ _).mp hXY)
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H Z =>
    obtain ⟨X, hXG, hXZ⟩ := exists_newton hK hF hs hd hA₀ hA₀i hB₀ h𝔭 hr hr' he (c := c) (k := k)
      (by omega) Z.2
    refine ⟨QuotientGroup.mk ⟨X⁻¹, inv_mem hXG⟩, ?_⟩
    show (QuotientAddGroup.mk ⟨_, hmk ⟨X⁻¹, inv_mem hXG⟩⟩ : HA ⧸ HB.addSubgroupOf HA) =
      QuotientAddGroup.mk Z
    rw [keyA]
    simpa only [inv_inv] using hXZ
  show Nat.card (G ⧸ H.subgroupOf G) = Nat.card (HA ⧸ HB.addSubgroupOf HA)
  exact Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

end Formalism.HermitianLattices.Ext.L3.D2
