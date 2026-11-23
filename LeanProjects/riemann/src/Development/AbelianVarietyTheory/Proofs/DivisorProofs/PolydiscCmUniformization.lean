import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatSumCmp

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem defCoord_sub (φ : I → E →+* ℂ) (z : I → ℂ) (x x' : E) (i : I) :
    defCoord φ z (x - x') i = defCoord φ z x i - defCoord φ z x' i := by
  simp only [defCoord, map_sub]; ring

theorem defCoord_zero (φ : I → E →+* ℂ) (z : I → ℂ) (i : I) : defCoord φ z 0 i = 0 := by
  simp [defCoord]

theorem defCoord_ne_zero (φ : I → E →+* ℂ) (z : I → ℂ) (hz : z ∈ polydisc I) (x : E) (hx : x ≠ 0) (i : I) :
    defCoord φ z x i ≠ 0 := by
  intro h
  have h0 : φ i x ≠ 0 := by simpa using hx
  have h1 : φ i x = -(z i * starRingEnd ℂ (φ i x)) := eq_neg_of_add_eq_zero_left h
  have h2 : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖ := by
    conv_lhs => rw [h1]
    simp
  have h3 : 0 < ‖φ i x‖ := norm_pos_iff.2 h0
  have h4 := hz i
  nlinarith

theorem defCoord_mul (φ : I → E →+* ℂ) (z : I → ℂ) (a x : E) (i : I) (ha : starRingEnd ℂ (φ i a) = φ i a) :
    defCoord φ z (a * x) i = φ i a * defCoord φ z x i := by
  simp only [defCoord, map_mul, ha]; ring

theorem prod_cpow_ofReal {J : Type} (s : Finset J) (f : J → ℝ) (hf : ∀ i, 0 ≤ f i) (r : ℂ) :
    ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ r = (((∏ i ∈ s, f i : ℝ)) : ℂ) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i)]

theorem defTerm_eq (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (σ : ℂ) (x : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ k z σ x =
      (∏ i, defCoord φ z x i)⁻¹ ^ k * ((‖∏ i, defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, norm_prod,
    prod_cpow_ofReal _ _ (fun _ => norm_nonneg _)]

theorem lattice_unit_mul (c : Ideal (OF E)) (y : (Af E)ˣ) (u : (OF E)ˣ) (x : E) (hx : x ∈ lattice c y) :
    algebraMap (OF E) E (u : OF E) * x ∈ lattice c y := by
  unfold lattice at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [map_mul, _root_.mul_assoc]
  refine Subring.mul_mem _ ?_ hx
  apply Subring.le_topologicalClosure
  refine Subring.mem_map.2 ⟨_, ?_, rfl⟩
  exact Subring.subset_closure (Or.inl ⟨(u : OF E), rfl⟩)

end GlobalTheory.LatSumCmp

namespace GlobalTheory.LatSumCmp

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt latM_eq_dual eisClass_mk latPt_ne_zero)

section Pairs

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def vPt (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (p : FR E × FR E) : Fin (Module.finrank ℚ (FR E)) → ℂ :=
  fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j p.1 : ℂ) + (e j p.2 : ℂ) * τ (e j)))

def wPt (φ : I → E →+* ℂ) (z : I → ℂ) (ue : Fin (Module.finrank ℚ (FR E)) ≃ I) (x : E) :
    Fin (Module.finrank ℚ (FR E)) → ℂ :=
  fun j ↦ defCoord φ z x (ue j)

theorem vPt_apply (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (p : FR E × FR E) (j : Fin (Module.finrank ℚ (FR E))) :
    vPt e τ lam p j = lam j * latPt τ p (e j) := rfl

theorem vPt_inj (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (hτ : τ ∈ halfSpace (FR E)) (hlam : ∀ j, lam j ≠ 0)
    {p p' : FR E × FR E} (h : vPt e τ lam p = vPt e τ lam p') : p = p' := by
  have j0 : Fin (Module.finrank ℚ (FR E)) := ⟨0, Module.finrank_pos⟩
  have h1 := congrFun h j0
  simp only [vPt] at h1
  have h2 := mul_left_cancel₀ (hlam j0) h1
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 := mul_left_cancel₀ hc h2
  have him := congrArg Complex.im h3
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, zero_add, add_zero] at him
  have hb : e j0 p.2 = e j0 p'.2 := mul_right_cancel₀ (hτ (e j0)).ne' him
  have hb' : p.2 = p'.2 := (e j0).injective hb
  rw [hb'] at h3
  have ha : ((e j0 p.1 : ℝ) : ℂ) = e j0 p'.1 := add_right_cancel h3
  have ha' : p.1 = p'.1 := (e j0).injective (by exact_mod_cast ha)
  exact Prod.ext ha' hb'

theorem vPt_unit (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (a : FR E) (p : FR E × FR E) :
    vPt e τ lam (a * p.1, a * p.2) = fun j ↦ (e j a : ℂ) * vPt e τ lam p j := by
  funext j
  simp only [vPt, map_mul, Complex.ofReal_mul]; ring

theorem wPt_unit (φ : I → E →+* ℂ) (z : I → ℂ) (ue : Fin (Module.finrank ℚ (FR E)) ≃ I)
    (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (he : ∀ j (x : FR E), (e j x : ℂ) = φ (ue j) (x : E))
    (a : FR E) (x : E) : wPt φ z ue ((a : E) * x) = fun j ↦ (e j a : ℂ) * wPt φ z ue x j := by
  funext j
  simp only [wPt]
  rw [defCoord_mul φ z (a : E) x (ue j) (by rw [← he]; exact Complex.conj_ofReal _), he]

end Pairs

end GlobalTheory.LatSumCmp

namespace GlobalTheory.LatSumCmp

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt latM_eq_dual eisClass_mk latPt_ne_zero)

section Equiv

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem out_spec {L : Set E} (q : modUnits L) : ∃ u : (OF E)ˣ, ∃ x ∈ L, x ≠ 0 ∧
    q.1.out = algebraMap (OF E) E (u : OF E) * x := by
  obtain ⟨x, hx, hx0, hq⟩ := q.2
  obtain ⟨u, hu⟩ : (unitRel (E := E)).r x q.1.out :=
    Quotient.exact (show Quotient.mk unitRel x = Quotient.mk unitRel q.1.out by rw [Quotient.out_eq, hq])
  exact ⟨u, x, hx, hx0, hu⟩

theorem out_mem {L : Set E} (hLu : ∀ u : (OF E)ˣ, ∀ x ∈ L, algebraMap (OF E) E (u : OF E) * x ∈ L)
    (q : modUnits L) : q.1.out ∈ L ∧ q.1.out ≠ 0 := by
  obtain ⟨u, x, hx, hx0, hq⟩ := out_spec q
  rw [hq]
  exact ⟨hLu u x hx, mul_ne_zero ((u.isUnit.map (algebraMap (OF E) E)).ne_zero) hx0⟩

theorem exists_equiv (φ : I → E →+* ℂ) (z : I → ℂ) (hz : z ∈ polydisc I) (ue : Fin (Module.finrank ℚ (FR E)) ≃ I)
    (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (he : ∀ j (x : FR E), (e j x : ℂ) = φ (ue j) (x : E))
    (τ : (FR E →+* ℝ) → ℂ) (hτ : τ ∈ halfSpace (FR E)) (lam : Fin (Module.finrank ℚ (FR E)) → ℂ)
    (hlam : ∀ j, lam j ≠ 0) (𝔞 𝔟 : FracId (FR E)) (L : Set E)
    (hLu : ∀ u : (OF E)ˣ, ∀ x ∈ L, algebraMap (OF E) E (u : OF E) * x ∈ L)
    (hL : ∀ w, (∃ x ∈ L, w = wPt φ z ue x) ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, w = vPt e τ lam (m, β)) :
    ∃ ψ : modUnits L ≃ Quotient (latRel 𝔞 𝔟), ∀ q, ∃ p : LatPair 𝔞 𝔟, ψ q = Quotient.mk _ p ∧
      wPt φ z ue q.1.out = vPt e τ lam p.1 := by
  classical
  have j0 : Fin (Module.finrank ℚ (FR E)) := ⟨0, Module.finrank_pos⟩
  have hpair : ∀ x ∈ L, x ≠ 0 → ∃ p : LatPair 𝔞 𝔟, wPt φ z ue x = vPt e τ lam p.1 := by
    intro x hx hx0
    obtain ⟨m, hm, β, hβ, h⟩ := (hL _).1 ⟨x, hx, rfl⟩
    refine ⟨⟨(m, β), by rw [latM_eq_dual]; exact hm, hβ, ?_⟩, h⟩
    intro h0
    apply defCoord_ne_zero φ z hz x hx0 (ue j0)
    have := congrFun h j0
    rw [h0] at this
    simpa [vPt, wPt] using this
  choose pr hpr using fun q : modUnits L => hpair q.1.out (out_mem hLu q).1 (out_mem hLu q).2
  let ψ : modUnits L → Quotient (latRel 𝔞 𝔟) := fun q => Quotient.mk _ (pr q)
  have hinj : Function.Injective ψ := by
    intro q1 q2 h
    obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    have key : wPt φ z ue q2.1.out = wPt φ z ue ((((ε : 𝓞 (FR E)) : FR E) : E) * q1.1.out) := by
      rw [hpr q2, show (pr q2).1 = (_ * (pr q1).1.1, _ * (pr q1).1.2) from Prod.ext h1 h2, vPt_unit,
        wPt_unit φ z ue e he, hpr q1]
    have hx : q2.1.out = (((ε : 𝓞 (FR E)) : FR E) : E) * q1.1.out := by
      by_contra hne
      apply defCoord_ne_zero φ z hz _ (sub_ne_zero.2 hne) (ue j0)
      rw [defCoord_sub]; exact sub_eq_zero.2 (congrFun key j0)
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    exact Quotient.sound ⟨ε, hx⟩
  have hsurj : Function.Surjective ψ := by
    intro cl
    obtain ⟨p, rfl⟩ := Quotient.exists_rep cl
    have hm : p.1.1 ∈ dualLat 𝔞 := by
      have h0 : ∀ a : FR E, a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 → a ∈ dualLat 𝔞 := fun a ha => by
        rw [latM_eq_dual] at ha; exact ha
      exact h0 _ p.2.1
    obtain ⟨x, hx, hxw⟩ := (hL (vPt e τ lam p.1)).2 ⟨p.1.1, hm, p.1.2, p.2.2.1, rfl⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := congrFun hxw j0
      simp only [vPt_apply, wPt, defCoord_zero] at this
      exact mul_ne_zero (hlam j0) (latPt_ne_zero hτ p.2.2.2 (e j0)) this
    let q : modUnits L := ⟨Quotient.mk _ x, x, hx, hx0, rfl⟩
    refine ⟨q, ?_⟩
    obtain ⟨u, hu⟩ : (unitRel (E := E)).r x q.1.out := Quotient.exact (Quotient.out_eq q.1).symm
    have hcoe : algebraMap (OF E) E (u : OF E) = (((u : OF E) : FR E) : E) := rfl
    have key : vPt e τ lam (pr q).1 = vPt e τ lam (((u : OF E) : FR E) * p.1.1, ((u : OF E) : FR E) * p.1.2) := by
      rw [← hpr q, vPt_unit, hu, hcoe, wPt_unit φ z ue e he, ← hxw]
    have := vPt_inj e τ lam hτ hlam key
    show Quotient.mk _ (pr q) = Quotient.mk _ p
    exact (Quotient.sound (show (latRel 𝔞 𝔟).r p (pr q) from ⟨u, congrArg Prod.fst this, congrArg Prod.snd this⟩)).symm
  exact ⟨Equiv.ofBijective ψ ⟨hinj, hsurj⟩, fun q => ⟨pr q, rfl, hpr q⟩⟩

theorem defTerm_pair (φ : I → E →+* ℂ) (z : I → ℂ) (ue : Fin (Module.finrank ℚ (FR E)) ≃ I)
    (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)) (τ : (FR E →+* ℝ) → ℂ)
    (lam : Fin (Module.finrank ℚ (FR E)) → ℂ) (x : E) (p : FR E × FR E)
    (hW : wPt φ z ue x = vPt e τ lam p) (k : ℕ) (σ : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ k z σ x =
      ((∏ j, lam j)⁻¹ ^ k * ((‖∏ j, lam j‖ : ℝ) : ℂ) ^ (-2 * σ)) * eisTerm k σ τ p := by
  rw [defTerm_eq]
  have hP : ∏ i, defCoord φ z x i = (∏ j, lam j) * ∏ t, latPt τ p t := by
    rw [← Equiv.prod_comp ue (fun i => defCoord φ z x i), ← Equiv.prod_comp e (fun t => latPt τ p t),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => congrFun hW j
  rw [hP]
  unfold eisTerm
  rw [_root_.mul_inv, _root_.mul_pow, norm_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  ring

end Equiv

end GlobalTheory.LatSumCmp

namespace GlobalTheory.LatSumCmp

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (LatPair latRel eisClass eisTerm latPt eisClass_mk)

theorem defSum_eq_eis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔞 𝔟 : FracId (FR E))
    (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ → ∀ s : ℕ, 1 ≤ s →
    ∀ z ∈ polydisc I, ∀ (ue : Fin (Module.finrank ℚ (FR E)) ≃ I) (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ))
      (τ : (FR E →+* ℝ) → ℂ) (lam : Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ j (x : FR E), (e j x : ℂ) = φ (ue j) (x : E)) → τ ∈ halfSpace (FR E) → (∀ j, lam j ≠ 0) →
      (∀ w : Fin (Module.finrank ℚ (FR E)) → ℂ, (∃ x ∈ lattice c y, w = fun j ↦ defCoord φ z x (ue j)) ↔
        ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
          w = fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j)))) →
      ∀ G, IsEis 𝔞 𝔟 (2 * s) G → ∀ g, IsDefSum φ (2 * s) (lattice c y) g →
        g z = (cWt E (2 * s) : ℂ) * ((∏ j, lam j)⁻¹) ^ (2 * s) * G τ := by
  intro E _ _ _ I _ 𝔞 𝔟 φ c y _ _ s hs z hz ue e τ lam he hτ hlam hL G hG g hg
  classical
  obtain ⟨ψ, hψ⟩ := exists_equiv φ z hz ue e he τ hτ lam hlam 𝔞 𝔟 (lattice c y)
    (fun u x hx => lattice_unit_mul c y u x hx) hL
  set A : ℂ → ℂ := fun σ => (∏ j, lam j)⁻¹ ^ (2 * s) * ((‖∏ j, lam j‖ : ℝ) : ℂ) ^ (-2 * σ) with hA
  have hterm : ∀ (σ : ℂ) (q : modUnits (lattice c y)),
      GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ (2 * s) z σ q.1.out = A σ * eisClass 𝔞 𝔟 (2 * s) σ τ (ψ q) := by
    intro σ q
    obtain ⟨p, hp, hW⟩ := hψ q
    rw [hp, eisClass_mk 𝔞 𝔟 (even_two_mul s), defTerm_pair φ z ue e τ lam _ _ hW]
  have hsum : ∀ σ : ℂ, ∀ S, HasSum (eisClass 𝔞 𝔟 (2 * s) σ τ) S →
      HasSum (fun q : modUnits (lattice c y) => GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ (2 * s) z σ q.1.out) (A σ * S) := by
    intro σ S h
    simp only [hterm]
    exact ((Equiv.hasSum_iff ψ).2 h).mul_left (A σ)
  have hA0 : A 0 = (∏ j, lam j)⁻¹ ^ (2 * s) := by simp [hA]
  obtain ⟨G', hG', hgz⟩ := hg z hz
  suffices hG'eq : G' = A 0 * G τ by rw [hgz, hG'eq, hA0]; ring
  rcases eq_or_ne s 1 with rfl | hs1
  · obtain ⟨H', hH'd, hH's, rfl⟩ := hG'.2 (by norm_num)
    obtain ⟨H, hH, rfl⟩ := hG.2 (by norm_num)
    have hτ' : τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf (FR E) := hτ
    have hkey : ∀ σ : ℂ, 0 < σ.re → H' σ = A σ * H σ τ := by
      intro σ hσ
      obtain ⟨hsm, hHe⟩ := hH.1 σ hσ τ hτ'
      have h1 : HasSum (eisClass 𝔞 𝔟 2 σ τ) (H σ τ) := by rw [hHe]; exact hsm.hasSum
      exact (hH's σ hσ).unique (hsum σ _ h1)
    let U : Set ℂ := {σ | -1 / 2 < σ.re}
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hUc : IsPreconnected U := (convex_halfSpace_re_gt (-1 / 2)).isPreconnected
    have hf : AnalyticOnNhd ℂ H' U := hH'd.analyticOnNhd hUo
    have hn : ((‖∏ j, lam j‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun j _ => hlam j))
    have hAd : Differentiable ℂ A := fun σ =>
      (differentiableAt_const _).mul (((differentiableAt_const (-2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn))
    have hHd : DifferentiableOn ℂ (fun σ => H σ τ) U := hH.2.2 [] τ hτ'
    have hg' : AnalyticOnNhd ℂ (fun σ => A σ * H σ τ) U := (hAd.differentiableOn.mul hHd).analyticOnNhd hUo
    have hev : H' =ᶠ[nhds 1] (fun σ => A σ * H σ τ) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by simp)] with σ hσ
      exact hkey σ hσ
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg' hUc (show (-1 / 2 : ℝ) < (1 : ℂ).re by norm_num) hev
      (show (-1 / 2 : ℝ) < (0 : ℂ).re by norm_num)
  · have hk : 2 * s ≠ 2 := by omega
    have h2 := hsum 0 _ (hG.1 hk τ hτ)
    have hd : ∀ x : E, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm φ (2 * s) z 0 x = ∏ i, (defCoord φ z x i)⁻¹ ^ (2 * s) := by
      intro x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defTerm]
    simp only [hd] at h2
    exact (hG'.1 hk).unique h2

end GlobalTheory.LatSumCmp
