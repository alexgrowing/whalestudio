import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThickDiv

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem resTop_scal {V : Type} [CommRing V] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of V)) (W : Y.Opens) (a : V) :
    Out.resTop W (scal p a) = constFn p W a := rfl

theorem thick_appTop {V : Type} [CommRing V] (I : Ideal V) (e : ℕ) (a : V) :
    (thick V I e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ I ^ (e + 1)))).inv.hom (Ideal.Quotient.mk (I ^ (e + 1)) a) := by
  have h := congrArg (fun g => g.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  exact h.symm

theorem app_constFn_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (e : ℕ)
    (X : Over (Spec (CommRingCat.of V))) (W : X.left.Opens) {a : V} (ha : a ∈ I ^ (e + 1)) :
    ((fstG I e X).left.app W).hom (constFn X.hom W a) = 0 := by
  have h0 : ((thick V I e).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) = 0 := by
    rw [thick_appTop, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hc := congrArg (fun φ => (φ.appLE ⊤ ((pullback.fst X.hom (thick V I e)) ⁻¹ᵁ W) (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) (pullback.condition (f := X.hom) (g := thick V I e))
  have h1 : ((pullback.snd X.hom (thick V I e) ≫ thick V I e).appLE ⊤
      ((pullback.fst X.hom (thick V I e)) ⁻¹ᵁ W) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) = 0 := by
    change ((pullback X.hom (thick V I e)).presheaf.map _).hom
      (((pullback.snd X.hom (thick V I e)).app _).hom
        (((thick V I e).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a))) = 0
    rw [h0, map_zero, map_zero]
  have hn := congrArg (fun φ => φ.hom ((X.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)))
    ((pullback.fst X.hom (thick V I e)).naturality (homOfLE (show W ≤ X.hom ⁻¹ᵁ ⊤ by simp)).op)
  exact hn.trans (hc.trans h1)

private theorem ker_thick_appTop_le_span_pow_succ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (e : ℕ) :
    RingHom.ker (thick V (maximalIdeal V) e).appTop.hom ≤
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (ϖ ^ (e + 1))} := by
  intro x hx
  obtain ⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b = x :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x, by simp⟩
  rw [RingHom.mem_ker, thick_appTop] at hx
  have hb : Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)) b = 0 := by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ maximalIdeal V ^ (e + 1)))).hom.hom hx
  rw [Ideal.Quotient.eq_zero_iff_mem, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  exact Ideal.mem_span_singleton.2 ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c, map_mul _ _ _⟩

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem dvd_of_app_eq_zero_of_isAffineOpen (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) {U : X.left.Opens} (hU : IsAffineOpen U) (f : Γ(X.left, U))
    (hf : ((fstG (maximalIdeal V) e X).left.app U).hom f = 0) : constFn X.hom U (ϖ ^ (e + 1)) ∣ f := by
  have hm := GlobalTheory.ProperFunctions.mem_map_ker_of_app_eq_zero
    (IsPullback.of_hasPullback X.hom (thick V (maximalIdeal V) e)) hU f hf
  have hm2 := Ideal.map_mono (ker_thick_appTop_le_span_pow_succ hϖ e) hm
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm2
  exact hm2

theorem cst_dvd_gs_of_app_eq_zero (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) (W : X.left.Opens) (f : Γ(X.left, W))
    (hf : ((fstG (maximalIdeal V) e X).left.app W).hom f = 0) (x : X.left) (hx : x ∈ W) :
    cst X.hom x (ϖ ^ (e + 1)) ∣ gs (𝟙 X.left) x W f := by
  obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.left.isBasis_affineOpens hx
  have hr : ((fstG (maximalIdeal V) e X).left.app U).hom
      ((X.left.presheaf.map (homOfLE hUW).op).hom f) = 0 := by
    have hn := congrArg (fun φ => φ.hom f) ((fstG (maximalIdeal V) e X).left.naturality (homOfLE hUW).op)
    refine hn.trans ?_
    change (_ : _ →+* _) (((fstG (maximalIdeal V) e X).left.app W).hom f) = 0
    rw [hf, map_zero]
  obtain ⟨g, hg⟩ := dvd_of_app_eq_zero_of_isAffineOpen hϖ X e hU _ hr
  have hgerm := gs_appLE (𝟙 X.left) W U hUW (𝟙 X.left) x hxU f
  rw [Category.id_comp] at hgerm
  have hres : (Scheme.Hom.appLE (𝟙 X.left) W U hUW).hom f = (X.left.presheaf.map (homOfLE hUW).op).hom f := rfl
  rw [← hgerm, hres, hg, gs_mul _ _ _ hxU, gs_constFn _ _ _ _ hxU, Category.id_comp]
  exact dvd_mul_right _ _

theorem app_eq_zero_iff (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) (W : X.left.Opens) (f : Γ(X.left, W)) :
    ((fstG (maximalIdeal V) e X).left.app W).hom f = 0 ↔
      ∃ g : Γ(X.left, W), f = Out.resTop W (scal X.hom (ϖ ^ (e + 1))) * g := by
  rw [resTop_scal]
  constructor
  · intro hf
    exact exists_div X.hom (pow_ne_zero _ hϖ.ne_zero) W f
      (fun x hx => cst_dvd_gs_of_app_eq_zero hϖ X e W f hf x hx)
  · rintro ⟨g, rfl⟩
    rw [map_mul, app_constFn_eq_zero (maximalIdeal V) e X W
      (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) _), zero_mul]

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X : Over (Spec (CommRingCat.of V))) [Flat X.hom] (N : LB X.left) (σ : LB.Sec N) (e : ℕ), (∀ j, ((fstG (maximalIdeal V) e X).left.app _).hom (σ.f j) = 0) ↔ ∃ τ : LB.Sec N, SecIsMul X.hom (ϖ ^ (e + 1)) σ τ := by
  intro V _ _ _ ϖ hϖ X _ N σ e
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := exists_div_sec X.hom (pow_ne_zero (e + 1) hϖ.ne_zero) σ
      (fun j x hx => cst_dvd_gs_of_app_eq_zero hϖ X e (N.U j) (σ.f j) (h j) x hx)
    exact ⟨τ, fun j => by rw [hτ j, resTop_scal]⟩
  · rintro ⟨τ, hτ⟩ j
    exact (app_eq_zero_iff hϖ X e (N.U j) (σ.f j)).2 ⟨τ.f j, hτ j⟩

end GlobalTheory.ThickDiv
