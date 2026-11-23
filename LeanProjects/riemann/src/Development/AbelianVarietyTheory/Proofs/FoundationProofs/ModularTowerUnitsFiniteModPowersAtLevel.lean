import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMeromorphicRootOfMemModularFunctionTowerUnStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnitsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TendstoMobCodiscreteWithinStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement

noncomputable section

open scoped MatrixGroups
open Matrix GlobalTheory.KZ Filter Topology

namespace GlobalTheory.KZ.FinLev

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

theorem neBot_Hs : (codiscreteWithin Hs).NeBot := by
  rw [← Filter.forall_mem_nonempty_iff_neBot]
  intro s hs
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs) _ hI
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  rcases hz1 with h | h
  · exact ⟨z, h⟩
  · exact absurd hz2 h

theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) := by
  rw [Filter.Germ.coe_eq]
  exact Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) h

theorem mob_mem (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : mob (ofSL γ) z ∈ Hs := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties.1 _ _ hz

theorem mob_mul (γ δ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) :
    mob (ofSL (γ * δ)) z = mob (ofSL γ) (mob (ofSL δ) z) := by
  rw [map_mul]; exact GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties.2.1 _ _ _ hz

theorem mob_ofSL_one (z : ℂ) : mob (ofSL 1) z = z := by
  rw [map_one]; exact GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties.2.2.1 z

theorem mob_mob_inv (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ Hs) : mob (ofSL γ) (mob (ofSL γ⁻¹) z) = z := by
  rw [← mob_mul _ _ hz, mul_inv_cancel, mob_ofSL_one]

theorem diff_comp {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (γ : SL(2, ℤ)) :
    DifferentiableOn ℂ (fun z => a (mob (ofSL γ) z)) Hs :=
  ha.comp (GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties.2.2.2.2.1 _) (fun _ hz => mob_mem γ hz)

theorem eqOn_of_germ {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (h : (a : Mero) = (b : Mero)) : ∀ z ∈ Hs, a z = b z :=
  GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units.2.1 a b ha hb h

theorem eqOn_of_eventually {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (h : ∀ᶠ z in codiscreteWithin Hs, a z = b z) : ∀ z ∈ Hs, a z = b z :=
  eqOn_of_germ ha hb (Filter.Germ.coe_eq.2 h)

theorem germ_ne_zero {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) {z₀ : ℂ} (hz₀ : z₀ ∈ Hs) (h : a z₀ ≠ 0) :
    (a : Mero) ≠ 0 := by
  intro h0
  exact h (eqOn_of_germ ha (differentiableOn_const 0) h0 z₀ hz₀)

theorem exists_ne_zero {a : ℂ → ℂ} (h : (a : Mero) ≠ 0) : ∃ z ∈ Hs, a z ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (germ_eq_of_eqOn (ψ := fun _ => 0) hc)

theorem eventually_ne_zero {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) {z₀ : ℂ} (hz₀ : z₀ ∈ Hs) (h : a z₀ ≠ 0) :
    ∀ᶠ z in codiscreteWithin Hs, a z ≠ 0 :=
  (GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units.2.2 a ha (germ_ne_zero ha hz₀ h)).1

theorem comp_ne_zero {a : ℂ → ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ Hs) (h : a z₀ ≠ 0) (γ : SL(2, ℤ)) :
    ∃ z ∈ Hs, a (mob (ofSL γ) z) ≠ 0 :=
  ⟨mob (ofSL γ⁻¹) z₀, mob_mem _ hz₀, by rwa [mob_mob_inv γ hz₀]⟩

theorem exists_both_ne_zero {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ Hs) (hz₂ : z₂ ∈ Hs) (h₁ : a z₁ ≠ 0) (h₂ : b z₂ ≠ 0) :
    ∃ z ∈ Hs, a z ≠ 0 ∧ b z ≠ 0 := by
  haveI := neBot_Hs
  have hs : ∀ᶠ z in codiscreteWithin Hs, z ∈ Hs := Filter.self_mem_codiscreteWithin Hs
  obtain ⟨z, hz, h1, h2⟩ := (hs.and ((eventually_ne_zero ha hz₁ h₁).and (eventually_ne_zero hb hz₂ h₂))).exists
  exact ⟨z, hz, h1, h2⟩

theorem comp_eventually {φ ψ : ℂ → ℂ} (γ : SL(2, ℤ)) (h : ∀ᶠ z in codiscreteWithin Hs, φ z = ψ z) :
    ∀ᶠ z in codiscreteWithin Hs, φ (mob (ofSL γ) z) = ψ (mob (ofSL γ) z) :=
  (GlobalTheory.T.tendsto_mob_codiscreteWithin_codiscreteWithin (ofSL γ)).eventually h

theorem const_of_pow_eq {u v : ℂ → ℂ} (hu : DifferentiableOn ℂ u Hs) (hv : DifferentiableOn ℂ v Hs) {m : ℕ}
    (hm : 0 < m) (h : ∀ z ∈ Hs, u z ^ m = v z ^ m) {z₀ : ℂ} (hz₀ : z₀ ∈ Hs) (hv0 : v z₀ ≠ 0) :
    ∃ ζ : ℂ, ζ ^ m = 1 ∧ ∀ z ∈ Hs, u z = ζ * v z := by
  set ζ := u z₀ / v z₀ with hζdef
  have hζ : ζ ^ m = 1 := by rw [hζdef, div_pow, h z₀ hz₀, div_self (pow_ne_zero _ hv0)]
  refine ⟨ζ, hζ, ?_⟩
  have hn : Hs ∈ 𝓝 z₀ := isOpen_Hs.mem_nhds hz₀
  have hvc : ContinuousAt v z₀ := hv.continuousOn.continuousAt hn
  have hcont : ContinuousAt (fun z => u z / v z) z₀ := (hu.continuousOn.continuousAt hn).div hvc hv0
  let T : Finset ℂ := (Polynomial.nthRootsFinset m (1 : ℂ)).erase ζ
  have hT : IsClosed (T : Set ℂ) := T.finite_toSet.isClosed
  have hnT : (T : Set ℂ)ᶜ ∈ 𝓝 ζ := hT.isOpen_compl.mem_nhds (by simp [T])
  have h1 : ∀ᶠ z in 𝓝 z₀, u z / v z ∈ (T : Set ℂ)ᶜ := hcont hnT
  have h2 : ∀ᶠ z in 𝓝 z₀, v z ≠ 0 := hvc.eventually_ne hv0
  have hloc : u =ᶠ[𝓝 z₀] fun z => ζ * v z := by
    filter_upwards [h1, h2, hn] with z h1 h2 h3
    have hr : (u z / v z) ^ m = 1 := by rw [div_pow, h z h3, div_self (pow_ne_zero _ h2)]
    have hmem : u z / v z ∈ Polynomial.nthRootsFinset m (1 : ℂ) := (Polynomial.mem_nthRootsFinset hm 1).2 hr
    have he : u z / v z = ζ := by
      by_contra hne
      exact h1 (Finset.mem_erase.2 ⟨hne, hmem⟩)
    rw [← he, div_mul_cancel₀ _ h2]
  have hua : AnalyticOnNhd ℂ u Hs := hu.analyticOnNhd isOpen_Hs
  have hva : AnalyticOnNhd ℂ (fun z => ζ * v z) Hs := (hv.const_mul ζ).analyticOnNhd isOpen_Hs
  exact fun z hz => hua.eqOn_of_preconnected_of_eventuallyEq hva isPreconnected_Hs hz₀ hloc hz

end GlobalTheory.KZ.FinLev

namespace GlobalTheory.KZ.FinLev

def RootRel (a b : ℂ → ℂ) (γ : SL(2, ℤ)) (ζ : ℂ) : Prop :=
  ∀ z ∈ Hs, a (mob (ofSL γ) z) * b z = ζ * (a z * b (mob (ofSL γ) z))

theorem rel_one (a b : ℂ → ℂ) : RootRel a b 1 1 := by
  intro z _
  rw [mob_ofSL_one, one_mul]

theorem rel_inv {a b : ℂ → ℂ} {γ : SL(2, ℤ)} {ζ : ℂ} (hζ : ζ ≠ 0) (h : RootRel a b γ ζ) :
    RootRel a b γ⁻¹ ζ⁻¹ := by
  intro z hz
  have e := h _ (mob_mem γ⁻¹ hz)
  rw [mob_mob_inv γ hz] at e
  rw [e, ← mul_assoc, inv_mul_cancel₀ hζ, one_mul]

theorem rel_mul {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs) {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ Hs) (hz₂ : z₂ ∈ Hs) (h₁ : a z₁ ≠ 0) (h₂ : b z₂ ≠ 0) {γ δ : SL(2, ℤ)} {ζ η : ℂ}
    (hγ : RootRel a b γ ζ) (hδ : RootRel a b δ η) : RootRel a b (γ * δ) (ζ * η) := by
  obtain ⟨w₁, hw₁, e₁⟩ := comp_ne_zero hz₁ h₁ δ
  obtain ⟨w₂, hw₂, e₂⟩ := comp_ne_zero hz₂ h₂ δ
  have hev := (eventually_ne_zero (diff_comp ha δ) hw₁ e₁).and (eventually_ne_zero (diff_comp hb δ) hw₂ e₂)
  have hs : ∀ᶠ z in codiscreteWithin Hs, z ∈ Hs := Filter.self_mem_codiscreteWithin Hs
  refine eqOn_of_eventually ((diff_comp ha (γ * δ)).mul hb)
    ((ha.mul (diff_comp hb (γ * δ))).const_mul (ζ * η)) ?_
  filter_upwards [hev, hs] with z hn hz
  obtain ⟨n1, n2⟩ := hn
  have e1 := hγ _ (mob_mem δ hz)
  have e2 := hδ z hz
  show a (mob (ofSL (γ * δ)) z) * b z = ζ * η * (a z * b (mob (ofSL (γ * δ)) z))
  rw [mob_mul γ δ hz]
  apply mul_right_cancel₀ (mul_ne_zero n1 n2)
  linear_combination (a (mob (ofSL δ) z) * b z) * e1 +
    (ζ * a (mob (ofSL δ) z) * b (mob (ofSL γ) (mob (ofSL δ) z))) * e2

theorem char_exists {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {M m : ℕ} (hm : 0 < m)
    {f : X.K} (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) {a b : ℂ → ℂ}
    (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs) (hab : X.an f * (b : Mero) ^ m = (a : Mero) ^ m)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ Hs) (hz₂ : z₂ ∈ Hs) (h₁ : a z₁ ≠ 0) (h₂ : b z₂ ≠ 0)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma M) : ∃ ζ : ℂ, ζ ^ m = 1 ∧ RootRel a b γ ζ := by
  obtain ⟨φ, -, hφ, -⟩ := X.an_exp f
  have E1 : ∀ᶠ z in codiscreteWithin Hs, φ z * b z ^ m = a z ^ m := by
    rw [hφ, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq] at hab
    filter_upwards [hab] with z hz
    simpa using hz
  have E2 : ∀ᶠ z in codiscreteWithin Hs, φ z = φ (mob (ofSL γ) z) := by
    have h := X.an_sl (ofSL γ) f φ hφ
    rw [hf γ hγ, hφ] at h
    exact Filter.Germ.coe_eq.1 h
  have E3 := comp_eventually γ E1
  have hu := (diff_comp ha γ).mul hb
  have hv := ha.mul (diff_comp hb γ)
  have hpow : ∀ z ∈ Hs, (fun z => (a (mob (ofSL γ) z) * b z) ^ m) z = (fun z => (a z * b (mob (ofSL γ) z)) ^ m) z :=
    eqOn_of_eventually (hu.pow m) (hv.pow m) (by
      filter_upwards [E1, E2, E3] with z e1 e2 e3
      beta_reduce at e3 ⊢
      linear_combination (-(b z) ^ m) * e3 + (b (mob (ofSL γ) z)) ^ m * e1 -
        ((b (mob (ofSL γ) z)) ^ m * (b z) ^ m) * e2)
  obtain ⟨w₂, hw₂, e₂⟩ := comp_ne_zero hz₂ h₂ γ
  obtain ⟨z₀, hz₀, n1, n2⟩ := exists_both_ne_zero ha (diff_comp hb γ) hz₁ hw₂ h₁ e₂
  exact const_of_pow_eq hu hv hm hpow hz₀ (mul_ne_zero n1 n2)

end GlobalTheory.KZ.FinLev

namespace GlobalTheory.KZ.FinLev

theorem quot_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {M m : ℕ} (hM : 0 < M)
    (hm : 0 < m) (f r : X.Kˣ) {a b a' b' : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (ha' : DifferentiableOn ℂ a' Hs) (hb' : DifferentiableOn ℂ b' Hs)
    (hab : X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m)
    (hab' : X.an (r : X.K) * (b' : Mero) ^ m = (a' : Mero) ^ m)
    {z₂ z₃ : ℂ} (hz₂ : z₂ ∈ Hs) (hz₃ : z₃ ∈ Hs) (h₂ : b z₂ ≠ 0) (h₃ : a' z₃ ≠ 0)
    (hrel : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ ζ : ℂ, RootRel a b γ ζ ∧ RootRel a' b' γ ζ) :
    ∃ g : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (g : X.K) = g) ∧ (f : X.K) = r * (g : X.K) ^ m := by
  have hs : ∀ᶠ z in codiscreteWithin Hs, z ∈ Hs := Filter.self_mem_codiscreteWithin Hs
  have hAd : DifferentiableOn ℂ (a * b') Hs := ha.mul hb'
  have hBd : DifferentiableOn ℂ (b * a') Hs := hb.mul ha'
  obtain ⟨z₀, hz₀, n1, n2⟩ := exists_both_ne_zero hb ha' hz₂ hz₃ h₂ h₃
  have hB0 : (b * a') z₀ ≠ 0 := by simp [n1, n2]
  have hBev : ∀ᶠ z in codiscreteWithin Hs, (b * a') z ≠ 0 := eventually_ne_zero hBd hz₀ hB0
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs,
      (a * b') (mob (ofSL γ) z) * (b * a') z = (a * b') z * (b * a') (mob (ofSL γ) z) := by
    intro γ hγ z hz
    obtain ⟨ζ, h1, h2⟩ := hrel γ hγ
    have e1 := h1 z hz
    have e2 := h2 z hz
    simp only [Pi.mul_apply]
    linear_combination (b' (mob (ofSL γ) z) * a' z) * e1 - (a z * b (mob (ofSL γ) z)) * e2
  have hFr : X.an ((f * r⁻¹ : X.Kˣ) : X.K) * X.an (r : X.K) = X.an (f : X.K) := by
    rw [← map_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have hFAB : X.an ((f * r⁻¹ : X.Kˣ) : X.K) * ((b * a' : ℂ → ℂ) : Mero) ^ m = ((a * b' : ℂ → ℂ) : Mero) ^ m := by
    rw [Filter.Germ.coe_mul, Filter.Germ.coe_mul]
    linear_combination (-(X.an ((f * r⁻¹ : X.Kˣ) : X.K) * (b : Mero) ^ m)) * hab' +
      ((b : Mero) ^ m * (b' : Mero) ^ m) * hFr + (b' : Mero) ^ m * hab
  obtain ⟨φ, -, hφ, -⟩ := X.an_exp ((f * r⁻¹ : X.Kˣ) : X.K)
  have E1 : ∀ᶠ z in codiscreteWithin Hs, φ z * (b * a') z ^ m = (a * b') z ^ m := by
    have h := hFAB
    rw [hφ, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq] at h
    filter_upwards [h] with z hz
    simpa only [Pi.mul_apply, Pi.pow_apply] using hz
  have hgerm : ∀ γ ∈ CongruenceSubgroup.Gamma M,
      ((fun z => (a * b') (mob (ofSL γ) z) * (b * a') z : ℂ → ℂ) : Mero) =
        ((fun z => (a * b') z * (b * a') (mob (ofSL γ) z) : ℂ → ℂ) : Mero) :=
    fun γ hγ => germ_eq_of_eqOn (hinv γ hγ)
  have hpoly : ∃ P : Polynomial X.K, P ≠ 0 ∧ P.eval₂ X.an ((((a * b') / (b * a') : ℂ → ℂ)) : Mero) = 0 := by
    refine ⟨Polynomial.X ^ m - Polynomial.C ((f * r⁻¹ : X.Kˣ) : X.K), Polynomial.X_pow_sub_C_ne_zero hm _, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hφ, ← Filter.Germ.coe_pow, sub_eq_zero,
      Filter.Germ.coe_eq]
    filter_upwards [E1, hBev] with z e hz
    simp only [Pi.pow_apply, Pi.div_apply]
    rw [div_pow, ← e]
    field_simp
  obtain ⟨g₀, hg₀⟩ := X.sat (a * b') (b * a') M hM hAd hBd (germ_ne_zero hBd hz₀ hB0) hgerm hpoly
  obtain ⟨ψ, -, hψ, -⟩ := X.an_exp g₀
  have G1 : ∀ᶠ z in codiscreteWithin Hs, ψ z * (b * a') z = (a * b') z := by
    rw [hψ, ← Filter.Germ.coe_mul, Filter.Germ.coe_eq] at hg₀
    filter_upwards [hg₀] with z hz
    simpa only [Pi.mul_apply] using hz
  haveI : Nontrivial Mero := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units.1
  have hinj : Function.Injective X.an := X.an.injective
  have hpowg : g₀ ^ m = ((f * r⁻¹ : X.Kˣ) : X.K) := by
    apply hinj
    rw [map_pow, hψ, hφ, ← Filter.Germ.coe_pow, Filter.Germ.coe_eq]
    filter_upwards [G1, E1, hBev] with z g e hz
    simp only [Pi.pow_apply]
    apply mul_right_cancel₀ (pow_ne_zero m hz)
    rw [e, ← g, mul_pow]
  have hg0 : g₀ ≠ 0 := by
    intro h
    rw [h, zero_pow hm.ne'] at hpowg
    exact (f * r⁻¹).ne_zero hpowg.symm
  have hinvg : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) g₀ = g₀ := by
    intro γ hγ
    apply hinj
    rw [X.an_sl (ofSL γ) g₀ ψ hψ, hψ, Filter.Germ.coe_eq]
    obtain ⟨w, hw, hw0⟩ := comp_ne_zero hz₀ hB0 γ
    filter_upwards [comp_eventually γ G1, G1, hBev, eventually_ne_zero (diff_comp hBd γ) hw hw0, hs]
      with z g1 g2 m1 m2 hz
    beta_reduce at g1 m2 ⊢
    have e := hinv γ hγ z hz
    apply mul_right_cancel₀ (mul_ne_zero m1 m2)
    linear_combination ((b * a') z) * g1 - ((b * a') (mob (ofSL γ) z)) * g2 + e
  refine ⟨Units.mk0 g₀ hg0, hinvg, ?_⟩
  rw [Units.val_mk0, hpowg, Units.val_mul, mul_left_comm, Units.mul_inv, mul_one]

end GlobalTheory.KZ.FinLev

namespace GlobalTheory.KZ.FinLev

theorem finite_mod_powers : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (M m : ℕ), 0 < M → 0 < m → ∃ R : Finset X.Kˣ, ∀ f : X.Kˣ, f ∈ X.Un m →
      (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ r ∈ R, ∃ g : X.Kˣ,
        (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (g : X.K) = g) ∧ ∃ c : Ω, c ≠ 0 ∧
          (f : X.K) = r * (g : X.K) ^ m * algebraMap Ω X.K c := by
  intro Ω _ _ _ ε X hε hj M m hM hm
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : Nontrivial Mero := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units.1
  haveI : Group.FG SL(2, ℤ) :=
    ⟨⟨{ModularGroup.S, ModularGroup.T}, by simpa using SpecialLinearGroup.SL2Z_generators⟩⟩
  obtain ⟨S, hS⟩ := (Group.fg_iff_subgroup_fg (CongruenceSubgroup.Gamma M)).1 (Subgroup.fg_of_index_ne_zero _)
  have hSmem : ∀ s ∈ S, s ∈ CongruenceSubgroup.Gamma M := fun s hs => hS ▸ Subgroup.subset_closure hs
  let Sset := {f : X.Kˣ // f ∈ X.Un m ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f}
  have hroot : ∀ f : Sset, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧
      X.an (f.1 : X.K) * (b : Mero) ^ m = (a : Mero) ^ m :=
    fun f => GlobalTheory.T.exists_meromorphic_root_of_mem_modularFunctionTower_Un ε X hε hj m hm f.1 f.2.1
  choose A B hA hB hB0 hAB using hroot
  have hAnz : ∀ f : Sset, ∃ z ∈ Hs, A f z ≠ 0 := by
    intro f
    apply exists_ne_zero
    intro h0
    have hu : IsUnit (X.an (f.1 : X.K) * (B f : Mero) ^ m) :=
      ((f.1.isUnit).map X.an).mul ((GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units.2.2 (B f) (hB f) (hB0 f)).2.pow m)
    rw [hAB f, h0, zero_pow hm.ne'] at hu
    exact not_isUnit_zero hu
  have hBnz : ∀ f : Sset, ∃ z ∈ Hs, B f z ≠ 0 := fun f => exists_ne_zero (hB0 f)
  choose zA hzA hAz using hAnz
  choose zB hzB hBz using hBnz
  have hchar : ∀ (f : Sset) (s : S), ∃ ζ : ℂ, ζ ^ m = 1 ∧ RootRel (A f) (B f) s ζ :=
    fun f s => char_exists X hm f.2.2 (hA f) (hB f) (hAB f) (hzA f) (hzB f) (hAz f) (hBz f) (hSmem s s.2)
  choose Z hZ hZrel using hchar
  let sig : Sset → (S → Polynomial.nthRootsFinset m (1 : ℂ)) :=
    fun f s => ⟨Z f s, (Polynomial.mem_nthRootsFinset hm 1).2 (hZ f s)⟩
  let rep : (S → Polynomial.nthRootsFinset m (1 : ℂ)) → X.Kˣ :=
    fun σ => if h : ∃ f : Sset, sig f = σ then (h.choose).1 else 1
  refine ⟨Finset.univ.image rep, ?_⟩
  intro f hfU hfinv
  let f' : Sset := ⟨f, hfU, hfinv⟩
  have hex : ∃ g : Sset, sig g = sig f' := ⟨f', rfl⟩
  have hrep : rep (sig f') = hex.choose.1 := dif_pos hex
  have hsig : sig hex.choose = sig f' := hex.choose_spec
  have hsame : ∀ s : S, Z hex.choose s = Z f' s := fun s => congrArg Subtype.val (congrFun hsig s)
  let r : Sset := hex.choose
  let H : Subgroup SL(2, ℤ) :=
    { carrier := {γ | ∃ ζ : ℂ, ζ ^ m = 1 ∧ RootRel (A f') (B f') γ ζ ∧ RootRel (A r) (B r) γ ζ}
      mul_mem' := by
        rintro γ δ ⟨ζ, hζ, h1, h2⟩ ⟨η, hη, h3, h4⟩
        exact ⟨ζ * η, by rw [mul_pow, hζ, hη, one_mul],
          rel_mul (hA f') (hB f') (hzA f') (hzB f') (hAz f') (hBz f') h1 h3,
          rel_mul (hA r) (hB r) (hzA r) (hzB r) (hAz r) (hBz r) h2 h4⟩
      one_mem' := ⟨1, one_pow m, rel_one _ _, rel_one _ _⟩
      inv_mem' := by
        rintro γ ⟨ζ, hζ, h1, h2⟩
        have hζ0 : ζ ≠ 0 := by
          rintro rfl
          rw [zero_pow hm.ne'] at hζ
          exact zero_ne_one hζ
        exact ⟨ζ⁻¹, by rw [inv_pow, hζ, inv_one], rel_inv hζ0 h1, rel_inv hζ0 h2⟩ }
  have hle : CongruenceSubgroup.Gamma M ≤ H := by
    rw [← hS, Subgroup.closure_le]
    intro s hs
    have h := hZrel r ⟨s, hs⟩
    rw [hsame] at h
    show ∃ ζ : ℂ, ζ ^ m = 1 ∧ RootRel (A f') (B f') s ζ ∧ RootRel (A r) (B r) s ζ
    exact ⟨Z f' ⟨s, hs⟩, hZ f' ⟨s, hs⟩, hZrel f' ⟨s, hs⟩, h⟩
  obtain ⟨g, hg, hfg⟩ := quot_pow X hM hm f r.1 (hA f') (hB f') (hA r) (hB r) (hAB f') (hAB r) (hzB f') (hzA r)
    (hBz f') (hAz r) (fun γ hγ => by
      have h : ∃ ζ : ℂ, ζ ^ m = 1 ∧ RootRel (A f') (B f') γ ζ ∧ RootRel (A r) (B r) γ ζ := hle hγ
      obtain ⟨ζ, -, h1, h2⟩ := h
      exact ⟨ζ, h1, h2⟩)
  refine ⟨r.1, Finset.mem_image.2 ⟨sig f', Finset.mem_univ _, hrep⟩, g, hg, 1, one_ne_zero, ?_⟩
  rw [map_one, mul_one]
  exact hfg

end GlobalTheory.KZ.FinLev
