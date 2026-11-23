import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJZetaDefs
import GroundTheory.AutomorphicForms.HaarCosets
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa MeasureTheory

section Extension

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {U : Type*} [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ G U}

theorem exists_extend_dual (hρ : IsSmooth ρ) (hτ : IsSmooth τ)
    (ι : Representation.IntertwiningMap ρ τ) (hι : Function.Injective ι) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {ℓ : Module.Dual ℂ V}
    (hℓ : ∀ k ∈ K, ∀ v, ℓ (ρ k v) = ℓ v) :
    ∃ lam : Module.Dual ℂ U, (∀ k ∈ K, ∀ x, lam (τ k x) = lam x) ∧ ∀ v, lam (ι v) = ℓ v := by
  classical
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (fixedMap ρ ι K)
    (LinearMap.ker_eq_bot.2 (fixedMap_injective ρ hι))
  refine ⟨ℓ ∘ₗ (fixedVectors ρ K).subtype ∘ₗ r ∘ₗ fixedProj τ hτ hKc hKo, fun k hk x => ?_,
    fun v => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [fixedProj_apply_act hτ hKc hKo hk]
  · simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [fixedProj_map hKc hKo hρ hτ ι v]
    have h1 : r (fixedMap ρ ι K (fixedProj ρ hρ hKc hKo v)) = fixedProj ρ hρ hKc hKo v := by
      rw [← LinearMap.comp_apply, hr, LinearMap.id_apply]
    rw [h1]

    have hker : ∀ y ∈ coinvariantsKer ρ K, ℓ y = 0 := by
      intro y hy
      refine Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by rw [map_add, ha, hb, add_zero])
        (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hy
      rintro _ ⟨k, rfl⟩
      simp [hℓ k.1.1 k.1.2 k.2]
    have := hker _ (sub_fixedProj_mem hρ hKc hKo v)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

end Extension

section Decomposition

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

variable (F n) in

theorem exists_reps_congruenceSubgroup (m : ℕ) :
    ∃ R : Finset (GL (Fin n) F), (∀ x ∈ R, x ∈ integralGL F n) ∧
      ∀ k ∈ integralGL F n, ∃ x ∈ R, x⁻¹ * k ∈ congruenceSubgroup F n m := by
  classical
  set K₀ := integralGL F n
  set K := congruenceSubgroup F n m
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  refine ⟨Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : GL (Fin n) F),
    ?_, fun k hk => ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Quotient.out q).2
  · refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨k, hk⟩ : K₀) :
      K₀ ⧸ K.subgroupOf K₀))
    exact Subgroup.mem_subgroupOf.1 h

theorem exists_eval_decomposition (hσ : IsSmooth σ) {m : ℕ} {R : Finset (GL (Fin n) F)}
    (hR₀ : ∀ x ∈ R, x ∈ integralGL F n)
    (hR : ∀ k ∈ integralGL F n, ∃ x ∈ R, x⁻¹ * k ∈ congruenceSubgroup F n m)
    (lam : Module.Dual ℂ (parabolicIndSpace F n β σ)) :
    ∃ ℓ : GL (Fin n) F → Module.Dual ℂ W,
      (∀ x, ℓ x ∈ fixedVectors (Representation.dual σ)
        ((congruenceSubgroup F n m).subgroupOf (levi F n β))) ∧
      ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m),
        lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) := by
  classical
  have : LocallyCompactSpace (levi F n β) :=
    isClosed_levi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set K := congruenceSubgroup F n m
  set KM : Subgroup (levi F n β) := K.subgroupOf (levi F n β)
  have hKMc : IsCompact (KM : Set (levi F n β)) :=
    isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m)
  have hKMo : IsOpen (KM : Set (levi F n β)) :=
    isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m)
  set e := fixedProj σ hσ hKMc hKMo

  let E : fixedVectors (parabolicInd F n β σ) K →ₗ[ℂ] (R → W) :=
    LinearMap.pi fun x : R =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) (x : GL (Fin n) F)) ∘ₗ
        (parabolicIndSpace F n β σ).subtype ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype
  have hE : ∀ ψ, E ψ = 0 → ψ = 0 := by
    intro ψ hψ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL' (β := β) g
    obtain ⟨x, hxR, hxk⟩ := hR k hk
    have h0 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) x = 0 := by
      have := congrFun hψ ⟨x, hxR⟩
      simpa [E] using this
    have hfix := ψ.2 (x⁻¹ * k) hxk
    have h1 : ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * k) =
        ((ψ : parabolicIndSpace F n β σ) : GL (Fin n) F → W) (p * x) := by
      have := congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (p * x)) hfix
      simp only [coe_indRep_apply] at this
      rw [← this, mul_assoc, mul_inv_cancel_left]
    rw [h1, ((ψ : parabolicIndSpace F n β σ).2.1 ⟨p, hp⟩ x), h0]
    simp
  have hker : LinearMap.ker E = ⊥ := LinearMap.ker_eq_bot'.2 hE
  obtain ⟨E', hE'⟩ := LinearMap.exists_leftInverse_of_injective (K := ℂ)
    (V := fixedVectors (parabolicInd F n β σ) K) (V' := R → W) E hker
  let L := lam ∘ₗ (fixedVectors (parabolicInd F n β σ) K).subtype ∘ₗ E'
  refine ⟨fun x => if hx : x ∈ R then
      L ∘ₗ LinearMap.single ℂ (fun _ : R => W) ⟨x, hx⟩ ∘ₗ (fixedVectors σ KM).subtype ∘ₗ e
    else 0, fun x => ?_, fun ψ hψ => ?_⟩
  · by_cases hx : x ∈ R
    · dsimp only
      rw [dif_pos hx, mem_fixedVectors_dual]
      intro k hk w
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [fixedProj_apply_act hσ hKMc hKMo hk]
    · dsimp only
      rw [dif_neg hx]
      exact zero_mem _
  · have hval : ∀ x ∈ R, ((fixedProj σ hσ hKMc hKMo ((ψ : GL (Fin n) F → W) x) :
        fixedVectors σ KM) : W) = (ψ : GL (Fin n) F → W) x := fun x hx =>
      fixedProj_apply_of_mem hσ hKMc hKMo
        (apply_mem_fixedVectors (f := ⟨ψ, hψ⟩) (hR₀ x hx))
    have hEψ : E ⟨ψ, hψ⟩ = ∑ x : R, LinearMap.single ℂ (fun _ : R => W) x
        ((ψ : GL (Fin n) F → W) x) := by
      funext y
      simp [E, Finset.sum_apply, Pi.single_apply]
    have hlam : lam ψ = L (E ⟨ψ, hψ⟩) := by
      simp only [L, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [← LinearMap.comp_apply E' E, hE', LinearMap.id_apply]
    rw [hlam, hEψ, map_sum, ← Finset.sum_coe_sort R]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [dif_pos x.2]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hval x x.2]

end Decomposition

section Integral

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

theorem integral_mul_coeff_eq (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {K : Subgroup (GL (Fin n) F)} (hKc : IsCompact (K : Set (GL (Fin n) F)))
    (hKo : IsOpen (K : Set (GL (Fin n) F)))
    {lam : Module.Dual ℂ (parabolicIndSpace F n β σ)}
    {φ : parabolicIndSpace F n β σ} (hφ : φ ∈ fixedVectors (parabolicInd F n β σ) K)
    {R : Finset (GL (Fin n) F)} {ℓ : GL (Fin n) F → Module.Dual ℂ W}
    (hdec : ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) K,
      lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x))
    {h : GL (Fin n) F → ℂ} (hh : HasCompactSupport h) (hhl : ∀ k ∈ K, ∀ g, h (k * g) = h g)
    (hhr : ∀ k ∈ K, ∀ g, h (g * k) = h g) :
    ∫ g, h g * lam (parabolicInd F n β σ g φ) ∂μ =
      ∑ x ∈ R, ∫ g, h g * ℓ x ((φ : GL (Fin n) F → W) (x * g)) ∂μ := by
  classical
  let Ko : OpenSubgroup (GL (Fin n) F) := ⟨K, hKo⟩
  have hφk : ∀ k ∈ K, parabolicInd F n β σ k φ = φ := fun k hk => hφ k hk

  have hfin : (QuotientGroup.mk '' tsupport h : Set (GL (Fin n) F ⧸ K)).Finite :=
    finite_image_mk_tsupport Ko hh

  have hL : ∫ g, h g * lam (parabolicInd F n β σ g φ) ∂μ = μ.real (K : Set (GL (Fin n) F)) •
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ) := by
    refine integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_
    show h (g * k) * lam (parabolicInd F n β σ (g * k) φ) = h g * lam (parabolicInd F n β σ g φ)
    rw [hhr k hk, map_mul, Module.End.mul_apply, hφk k hk]
  have hR : ∀ x ∈ R, ∫ g, h g * ℓ x ((φ : GL (Fin n) F → W) (x * g)) ∂μ = μ.real (K : Set (GL (Fin n) F)) •
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out)) := by
    intro x _
    refine integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_
    show h (g * k) * ℓ x ((φ : GL (Fin n) F → W) (x * (g * k))) = h g * ℓ x ((φ : GL (Fin n) F → W) (x * g))
    have := congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (x * g)) (hφk k hk)
    simp only [coe_indRep_apply] at this
    rw [hhr k hk, ← mul_assoc, this]

  set ψ : parabolicIndSpace F n β σ := ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out • parabolicInd F n β σ c.out φ
    with hψdef
  have hψsupp : (Function.support fun c : GL (Fin n) F ⧸ K =>
      h c.out • parabolicInd F n β σ c.out φ).Finite :=
    hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]),
      QuotientGroup.out_eq' c⟩
  have hψK : ψ ∈ fixedVectors (parabolicInd F n β σ) K := by
    intro k hk
    rw [hψdef, map_finsum (parabolicInd F n β σ k) hψsupp]
    have hterm : ∀ c : GL (Fin n) F ⧸ K,
        parabolicInd F n β σ k (h c.out • parabolicInd F n β σ c.out φ) =
        (fun c : GL (Fin n) F ⧸ K => h c.out • parabolicInd F n β σ c.out φ)
          (MulAction.toPerm k c) := by
      intro c
      have hmk : (QuotientGroup.mk (k * c.out) : GL (Fin n) F ⧸ K) = MulAction.toPerm k c := by
        show QuotientGroup.mk (k * c.out) = k • c
        conv_rhs => rw [← QuotientGroup.out_eq' c]
        rfl
      obtain ⟨j, hj, hjeq⟩ : ∃ j ∈ K, k * c.out = (MulAction.toPerm k c).out * j := by
        refine ⟨((MulAction.toPerm k c).out)⁻¹ * (k * c.out), ?_, by group⟩
        have := QuotientGroup.eq.1 ((QuotientGroup.out_eq' (MulAction.toPerm k c)).trans hmk.symm)
        simpa using this
      have hhc : h c.out = h (MulAction.toPerm k c).out := by
        rw [← hhl k hk c.out, hjeq, hhr j hj]
      dsimp only
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, hjeq, map_mul, Module.End.mul_apply,
        hφk j hj, hhc]
    rw [finsum_congr hterm]
    exact finsum_comp_equiv (MulAction.toPerm k) (f := fun c : GL (Fin n) F ⧸ K =>
      h c.out • parabolicInd F n β σ c.out φ)

  have h1 : lam ψ = ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ) := by
    rw [hψdef, map_finsum lam hψsupp]
    simp only [map_smul, smul_eq_mul]
  have h2 : ∀ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) =
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out)) := by
    intro x _
    let ev : parabolicIndSpace F n β σ →ₗ[ℂ] W :=
      LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) x ∘ₗ
        (parabolicIndSpace F n β σ).subtype
    have hev : (ψ : GL (Fin n) F → W) x = ev ψ := rfl
    rw [hev, hψdef, map_finsum ev hψsupp, map_finsum (ℓ x)]
    · refine finsum_congr fun c => ?_
      simp [ev, coe_indRep_apply]
    · exact hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]),
        QuotientGroup.out_eq' c⟩
  rw [hL, ← h1, hdec ψ hψK, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hR x hx, h2 x hx]

end Integral

end GodementJacquet

end GroundTheory.Automorphic
