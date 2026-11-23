import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

open UpperTheory.V.Sd.Eis

private theorem exists_addChar_fourier_coeff_ne_zero_of_ne_zero {α : Type} [AddCommGroup α] [Fintype α] (F : α → ℂ) (hF : F ≠ 0) :
    ∃ ψ : AddChar α ℂ, ∑ a, F a * ψ (-a) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hF
  funext x
  have key : ∑ ψ : AddChar α ℂ, ∑ a, F a * ψ (x - a) = (Fintype.card α : ℂ) * F x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite, sub_eq_zero]
    rw [Finset.sum_eq_single x]
    · simp [mul_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have key2 : ∑ ψ : AddChar α ℂ, ∑ a, F a * ψ (x - a) = 0 := by
    apply Finset.sum_eq_zero
    intro ψ _
    simp_rw [sub_eq_add_neg, AddChar.map_add_eq_mul, mul_left_comm (F _), ← Finset.mul_sum, h ψ,
      mul_zero]
  have hc : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := key.symm.trans key2
  simpa [hc] using this

theorem UpperTheory.exists_character_separation :
    UpperTheory.V.Sd.Eis.CharPick := by
  intro T _ U₀ hU₀ f₀ hf₀ hinv
  classical
  have inv_out : ∀ (V : Subgroup T) (w : T → ℂ), (∀ t u, u ∈ V → w (t * u) = w t) →
      ∀ t : T, w ((QuotientGroup.mk t : T ⧸ V).out) = w t := by
    intro V w hw t
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul V t
    rw [hh, hw _ _ h.2]
  haveI : Fintype (T ⧸ U₀) := Fintype.ofFinite _
  let F : Additive (T ⧸ U₀) → ℂ := fun a => f₀ (Additive.toMul a).out
  have hF : F ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hf₀
    intro h0
    apply ht
    have := congrFun h0 (Additive.ofMul (QuotientGroup.mk t))
    simp only [F, toMul_ofMul, Pi.zero_apply] at this
    rw [inv_out U₀ f₀ hinv t] at this
    exact this
  obtain ⟨ψ, hψ⟩ := exists_addChar_fourier_coeff_ne_zero_of_ne_zero F hF
  let χ : T →* ℂˣ :=
    { toFun := fun t => ⟨ψ (Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀)),
        ψ (-(Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀))),
        by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
        by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [AddChar.map_add_eq_mul] }
  have hχval : ∀ t, (((χ t)⁻¹ : ℂˣ) : ℂ) = ψ (-(Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀))) :=
    fun t => rfl
  have hχU₀ : ∀ u ∈ U₀, χ u = 1 := by
    intro u hu
    ext
    simp [χ, (QuotientGroup.eq_one_iff u).mpr hu]
  let aV : Subgroup T → (T → ℂ) → ℂ := fun V h =>
    ∑ᶠ q : T ⧸ V, h q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ)
  have aV_lin : ∀ V : Subgroup T, V.FiniteIndex → ∀ (c : ℂ) (p p' : T → ℂ),
      aV V (c • p + p') = c * aV V p + aV V p' := by
    intro V hV c p p'
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    simp only [aV, finsum_eq_sum_of_fintype, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have aV_zero : ∀ V : Subgroup T, aV V 0 = 0 := by
    intro V; simp [aV]
  have kill : ∀ V : Subgroup T, V.FiniteIndex → V ≤ U₀ → ∀ g : T → ℂ,
      (∀ t u, u ∈ V → g (t * u) = g t) → ∀ s, aV V (fun t => g (t * s)) = (χ s : ℂ) * aV V g := by
    intro V hV hVU g hg s
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    let φ : T → ℂ := fun t => g t * (((χ t)⁻¹ : ℂˣ) : ℂ)
    have hφ : ∀ t u, u ∈ V → φ (t * u) = φ t := by
      intro t u hu
      simp only [φ, map_mul, hχU₀ u (hVU hu), mul_one, hg t u hu]
    simp only [aV, finsum_eq_sum_of_fintype]
    have hre : ∑ q : T ⧸ V, g q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ)
        = ∑ q : T ⧸ V, g (q * (QuotientGroup.mk s : T ⧸ V)).out
            * (((χ (q * (QuotientGroup.mk s : T ⧸ V)).out)⁻¹ : ℂˣ) : ℂ) :=
      (Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk s : T ⧸ V))
        (fun q => g q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ))).symm
    rw [hre, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    have hq : q * (QuotientGroup.mk s : T ⧸ V) = QuotientGroup.mk (q.out * s) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have h2 := inv_out V φ hφ (q.out * s)
    rw [hq]
    change _ = _ * φ _
    rw [h2]
    simp only [φ, map_mul, mul_inv, Units.val_mul]
    have hs1 : (χ s : ℂ) * (((χ s)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    linear_combination (-(g (q.out * s) * (((χ q.out)⁻¹ : ℂˣ) : ℂ))) * hs1
  have fiber : ∀ V : Subgroup T, V ≤ U₀ → V.FiniteIndex → aV V f₀ ≠ 0 := by
    intro V hVU hV
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    let π : T ⧸ V →* T ⧸ U₀ := QuotientGroup.map V U₀ (MonoidHom.id T) (fun x hx => hVU hx)
    let φ0 : T → ℂ := fun t => f₀ t * (((χ t)⁻¹ : ℂˣ) : ℂ)
    have hφ0 : ∀ t u, u ∈ U₀ → φ0 (t * u) = φ0 t := by
      intro t u hu
      simp only [φ0, map_mul, hχU₀ u hu, mul_one, hinv t u hu]
    let Kf : T ⧸ U₀ → ℂ := fun r => φ0 r.out
    have hH : ∀ q : T ⧸ V, f₀ q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ) = Kf (π q) := by
      intro q
      have : π q = QuotientGroup.mk q.out := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [this]
      exact (inv_out U₀ φ0 hφ0 q.out).symm
    have hsurj : ∀ r : T ⧸ U₀, r ∈ Set.range π := by
      intro r
      refine ⟨QuotientGroup.mk r.out, ?_⟩
      change (QuotientGroup.mk r.out : T ⧸ U₀) = r
      exact QuotientGroup.out_eq' r
    have hcard : ∀ r : T ⧸ U₀, (Finset.univ.filter fun q => π q = r).card
        = (Finset.univ.filter fun q => π q = 1).card :=
      fun r => MonoidHom.card_fiber_eq_of_mem_range π (hsurj r) (hsurj 1)
    have hpos : (Finset.univ.filter fun q => π q = 1).card ≠ 0 := by
      rw [Finset.card_ne_zero]
      exact ⟨1, by simp⟩
    have hsumK : ∑ r, Kf r ≠ 0 := by
      have e : ∑ r, Kf r = ∑ a, F a * ψ (-a) := by
        refine Fintype.sum_equiv Additive.ofMul _ _ (fun r => ?_)
        simp only [Kf, φ0, F, hχval, QuotientGroup.out_eq', toMul_ofMul]
      rw [e]; exact hψ
    simp only [aV, finsum_eq_sum_of_fintype, hH]
    rw [← Finset.sum_fiberwise' Finset.univ π Kf]
    simp only [Finset.sum_const, hcard, nsmul_eq_mul, ← Finset.mul_sum]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hpos) hsumK
  let Kset : Set (T → ℂ) := {p | ∃ (U : Subgroup T) (g : T → ℂ) (s : T), U.FiniteIndex ∧
      (∀ t u, u ∈ U → g (t * u) = g t) ∧ p = (fun t => g (t * s)) - (χ s : ℂ) • g}
  have key : ∀ p : T → ℂ, p ∈ Submodule.span ℂ Kset → ∃ V : Subgroup T, V ≤ U₀ ∧ V.FiniteIndex ∧
      ∀ V' : Subgroup T, V' ≤ V → V'.FiniteIndex → aV V' p = 0 := by
    intro p hmem
    induction hmem using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨U, g, s, hU, hg, rfl⟩ := hp
      haveI := hU
      haveI := hU₀
      refine ⟨U ⊓ U₀, inf_le_right, inferInstance, fun V' hV' hV'f => ?_⟩
      have hg' : ∀ t u, u ∈ V' → g (t * u) = g t :=
        fun t u hu => hg t u (Subgroup.mem_inf.mp (hV' hu)).1
      have e : (fun t => g (t * s)) - (χ s : ℂ) • g = (-(χ s : ℂ)) • g + (fun t => g (t * s)) := by
        funext t; simp; ring
      rw [e, aV_lin V' hV'f, kill V' hV'f (hV'.trans inf_le_right) g hg' s]
      ring
    | zero => exact ⟨U₀, le_rfl, hU₀, fun V' _ _ => aV_zero V'⟩
    | add x y _ _ hx hy =>
      obtain ⟨V1, hV1U, hV1f, hV1⟩ := hx
      obtain ⟨V2, hV2U, hV2f, hV2⟩ := hy
      haveI := hV1f
      haveI := hV2f
      refine ⟨V1 ⊓ V2, inf_le_left.trans hV1U, inferInstance, fun V' hV' hV'f => ?_⟩
      have := aV_lin V' hV'f 1 x y
      rw [one_smul, one_mul] at this
      rw [this, hV1 V' (hV'.trans inf_le_left) hV'f, hV2 V' (hV'.trans inf_le_right) hV'f, add_zero]
    | smul c x _ hx =>
      obtain ⟨V1, hV1U, hV1f, hV1⟩ := hx
      refine ⟨V1, hV1U, hV1f, fun V' hV' hV'f => ?_⟩
      have := aV_lin V' hV'f c x 0
      rw [add_zero, aV_zero, add_zero] at this
      rw [this, hV1 V' hV' hV'f, mul_zero]
  have hnot : f₀ ∉ Submodule.span ℂ Kset := by
    intro hmem
    obtain ⟨V, hVU, hVf, hV⟩ := key f₀ hmem
    exact fiber V hVU hVf (hV V le_rfl hVf)
  obtain ⟨L, hL, hLK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨χ, L, hχU₀, hL, ?_⟩
  intro U hU f hf s
  have hmemK : (fun t => f (t * s)) - (χ s : ℂ) • f ∈ Submodule.span ℂ Kset :=
    Submodule.subset_span ⟨U, f, s, hU, hf, rfl⟩
  have h0 : L ((fun t => f (t * s)) - (χ s : ℂ) • f) = 0 := by
    have := Submodule.mem_map_of_mem (f := L) hmemK
    rw [hLK, Submodule.mem_bot] at this
    exact this
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0
