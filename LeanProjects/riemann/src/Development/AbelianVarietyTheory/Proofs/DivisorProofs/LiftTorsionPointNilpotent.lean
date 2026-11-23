import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.FiniteLocalLifts.SmLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem TorsionLift.pushPt_pow {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') :
    ∀ n : ℕ, pushPt h.1.w (x ^ n) = (pushPt h.1.w x) ^ n := by
  have h1 : pushPt h.1.w (1 : T ⟶ G') = 1 := by
    have e := h.2 T 1 1 (pushPt h.1.w 1) (pushPt h.1.w 1) rfl rfl
    have e' : pushPt h.1.w (1 : T ⟶ G') * pushPt h.1.w 1 = pushPt h.1.w 1 :=
      Over.OverMorphism.ext (by rw [e, _root_.mul_one]; rfl)
    exact mul_eq_left.1 e'
  intro n
  induction n with
  | zero => rw [pow_zero, pow_zero, h1]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact (Over.OverMorphism.ext (h.2 T (x ^ n) x (pushPt h.1.w (x ^ n)) (pushPt h.1.w x) rfl rfl)).symm

theorem TorsionLift.exists_torsion_lift : ∀ {R : Type} [CommRing R] [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ), (∀ x ∈ RingHom.ker π, IsNilpotent x) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (G₀ : Over (Sp ℂ)) [GrpObj G₀] (i : G₀.left ⟶ G.left), IsGrpPullback G₀ G (spMap (π : R →+* ℂ)) i →
    ∀ (N : ℕ), 1 ≤ N → ∀ (p : 𝟙_ (Over (Sp ℂ)) ⟶ G₀), p ^ N = 1 →
    ∃ q : 𝟙_ (Over (Sp R)) ⟶ G, q ^ N = 1 ∧ p.left ≫ i = spMap (π : R →+* ℂ) ≫ q.left := by
  intro R _ _ π hnil G _ _ _ G₀ _ i hG N hN p hp
  have hn : IsUnit (N : Γ(Sp R, ⊤)) := by
    let f : ℂ →+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap ℂ R)
    rw [← map_natCast f N]
    exact (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map f
  have := GrpTangent.etale_torsion G hn
  have hP := GrpTangent.isPullback_torsion G N
  have e : ∀ {T : Scheme.{0}} (q : T ⟶ Sp R), (1 : Over.mk q ⟶ G).left = q ≫ η[G].left := by
    intro T q
    rw [Hom.one_def, Over.comp_left]; rfl
  let y₀ := pushPt hG.1.w p
  have hy₀ : y₀ ^ N = 1 := by
    rw [← TorsionLift.pushPt_pow hG p N, hp]
    have := TorsionLift.pushPt_pow hG (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G₀) 0
    rwa [pow_zero, pow_zero] at this
  have w : y₀.left ≫ (mulN G N).left = (𝟙 (Sp ℂ) ≫ spMap (π : R →+* ℂ)) ≫ η[G].left := by
    rw [← Over.comp_left, GrpTangent.comp_mulN, hy₀, e]
    rfl
  let x₀ : Sp ℂ ⟶ (torsion G N).left := hP.lift y₀.left _ w
  have hx₀₁ : x₀ ≫ (torsion G N).hom = 𝟙 (Sp ℂ) ≫ spMap (π : R →+* ℂ) := hP.lift_snd _ _ w
  have hx₀₂ : x₀ ≫ (torsion.ι G N).left = p.left ≫ i := hP.lift_fst _ _ w
  have hsurj : Function.Surjective π := fun c => ⟨algebraMap ℂ R c, by simp⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair (torsion G N).hom (x₀ (IsLocalRing.closedPoint ℂ)) (O := ⊤) trivial
  obtain ⟨x, hx₁, hx₂⟩ := exists_lift_of_smooth_of_isAffineOpen (torsion G N).hom (isAffineOpen_top _) hV
    (fun _ _ => trivial) (CommRingCat.ofHom (π : R →+* ℂ)) (𝟙 _) x₀ (by rw [hx₀₁]; rfl)
    (fun _ _ => trivial) (range_subset_opens_of_isLocalRing x₀ hxV) (by
      intro R' A _ _ _ _ _ _ π' hπ' φ
      have : Algebra.FormallySmooth R' A := inferInstance
      exact ReciprocityTheory.ChartRestriction.G.Pdiv.FiniteLocalHoms.exists_lift_nil π'
        (fun c => (hsurj c).imp fun b hb => (hπ' b).trans hb)
        (fun a ha => hnil a (by rw [RingHom.mem_ker] at ha ⊢; rw [← ha]; exact (hπ' a).symm)) φ)
  let q : 𝟙_ (Over (Sp R)) ⟶ G := Over.homMk (U := 𝟙_ (Over (Sp R))) (x ≫ (torsion.ι G N).left) (by
    rw [Category.assoc, Over.w]; exact hx₂)
  refine ⟨q, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    rw [← GrpTangent.comp_mulN, Over.comp_left, e]
    change (x ≫ (torsion.ι G N).left) ≫ _ = _
    rw [Category.assoc, hP.w, ← Category.assoc, hx₂]
    rfl
  · change _ = _ ≫ x ≫ (torsion.ι G N).left
    rw [← Category.assoc, hx₁, hx₀₂]

end GlobalTheory
