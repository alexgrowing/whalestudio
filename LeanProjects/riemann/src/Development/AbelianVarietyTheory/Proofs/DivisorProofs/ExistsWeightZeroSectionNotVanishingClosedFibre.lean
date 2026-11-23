import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSecValueIsUnit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SquareUnits ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic

noncomputable section

namespace GlobalTheory.Mum.SecBZeroBpf

theorem unitAt_pow {S : Scheme.{0}} [IsLocallyNoetherian S] (hL : Laws) (P : PolAV S) {K : Type} [Field K]
    [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk t ⟶ P.A) (m : ℕ) :
    UnitAt P.L ![(translPt P.A (1 : Over.mk t ⟶ P.A)).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1]
      ((ptSecT P.A x).left (IsLocalRing.closedPoint K)) := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : AlgebraicGeometry.IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 := GlobalTheory.ThetaRep.finrank_secM hL.secBaseChange P (n := 1) le_rfl t
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let p : (Over.mk t).left := IsLocalRing.closedPoint K
  let y := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    GlobalTheory.NoBasePoint.unitAt_transl P.isLB θ k a y (by
      rw [← GlobalTheory.NoBasePoint.ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hL.square S P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (GlobalTheory.NoBasePoint.unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := GlobalTheory.NoBasePoint.exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := GlobalTheory.NoBasePoint.exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  exact main m 1

theorem mem_basicOpen_of_isUnit {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (hz : r z ∈ U) (a : Γ(Y, U))
    (h : IsUnit (gs r z U a)) : r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U hz] at h
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen r a) z).2 ((Z.mem_basicOpen _ z hz).2 h)

theorem c_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) : D.c 0 = η[D.P.A] := by
  have h := D.c_add 0 0
  rw [add_zero] at h
  have h' : D.c 0 * D.c 0 = D.c 0 := h.symm
  rw [mul_eq_left] at h'
  rw [h']
  show toUnit _ ≫ η[D.P.A] = η[D.P.A]
  rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem _root_.GlobalTheory.Mum.exists_secB_zero_mem_basicOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (k : ℕ), 2 ≤ k → ∀ x : D.toPre.P.A.left,
      D.toPre.P.A.hom x = closedPoint R →
      ∃ (σ : D.toPre.SecB k 0) (j : Fin 4 → D.toPre.P.L.ι), x ∈ D.toPre.P.A.left.basicOpen (σ.f j) := by
  intro R _ _ _ hB D k hk x hx
  haveI : IsNoetherianRing R := hB.1.1
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hTW : DVR.TwistBCSpanStatement := DVR.twistBCSpan_of GlobalTheory.twistBaseChange
  let P := D.toPre.P
  let K := AlgebraicClosure (P.A.left.residueField x)
  let u : Spec (CommRingCat.of K) ⟶ P.A.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (P.A.left.residueField x) K)) ≫ P.A.left.fromSpecResidueField x
  have hu : ∀ q, u q = x := fun q => (Scheme.Hom.comp_apply _ _ q).trans (Scheme.fromSpecResidueField_apply x _)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (u ≫ P.A.hom)
  let f : R →+* K := φ.hom
  have hφ' : Spec.map (CommRingCat.ofHom f) = u ≫ P.A.hom := hφ
  have e2 : (u ≫ P.A.hom) (closedPoint K) = closedPoint R :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg _ (hu _)).trans hx)
  have e : (Spec.map (CommRingCat.ofHom f)) (closedPoint K) = closedPoint R := by rw [hφ']; exact e2
  have e3 : Ideal.comap f (maximalIdeal K) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal e
  have hf : IsLocalHom f := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ maximalIdeal R := (mem_maximalIdeal a).2 hna
    rw [← e3] at h1
    exact (mem_maximalIdeal _).1 h1 ha⟩
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom f))
  let xb : T ⟶ P.A := Over.homMk u hφ'.symm
  let y := (ptSecT P.A xb).left (closedPoint K)
  have hy : (snd T P.A).left y = x := by
    have e4 : ptSecT P.A xb ≫ snd T P.A = xb := lift_snd _ _
    have e5 := congrArg (fun q => q.left (closedPoint K)) e4
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at e5
    exact e5.trans (hu _)
  have c0 := c_zero D.toPre
  have a0 : (snd T P.A).left ≫ D.toPre.famφB 0 0 = (snd T P.A).left := Category.comp_id _
  have a1 : (snd T P.A).left ≫ D.toPre.famφB 0 1 = (translPt P.A (1 : T ⟶ P.A)).left := by
    show (snd T P.A ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0)).left = _
    congr 1
    have e1 : snd T P.A ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit _ ≫ D.toPre.c 0) =
        snd T P.A * (toUnit _ ≫ D.toPre.c 0) := by
      refine (MonObj.comp_mul (snd T P.A) (𝟙 _) (toUnit _ ≫ D.toPre.c 0)).trans ?_
      rw [Category.comp_id, ← Category.assoc, comp_toUnit]
    rw [e1, mul_comm, GlobalTheory.NoBasePoint.translPt_eq, c0, MonObj.comp_one]
    rfl
  have a2 : (snd T P.A).left ≫ D.toPre.famφB 0 2 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ D.toPre.c 0).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left, c0]
  have a3 : (snd T P.A).left ≫ D.toPre.famφB 0 3 = (T ⊗ P.A).hom ≫ (η[P.A]).left := by
    show (snd T P.A ≫ toUnit _ ≫ η[D.toPre.P.A]).left = _
    rw [← Category.assoc, comp_toUnit, Over.comp_left, Over.toUnit_left]
  obtain ⟨σ, hσ⟩ : UnitAt P.L (fun i => (snd T P.A).left ≫ D.toPre.famφB 0 i) (DegPre.famε k) y := by
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      (unitAt_pow hL P (Spec.map (CommRingCat.ofHom f)) xb (k - 2))
    rw [Fin.sum_univ_four, a0, a1, a2, a3, Fin.sum_univ_two]
    have hk' : ((k - 2 : ℕ) : ℤ) + 1 = (k : ℤ) - 1 := by omega
    simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hk']
    abel
  obtain ⟨m, c', β, hβ⟩ := hTW R D.toPre k (by omega) 0 K f hf σ
  choose J hJ using fun ψ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (ψ y)
  have hJ' : Good P.L y J := hJ
  have e6 := SectionScalarValuation.sval_lin (fun l => (fst T P.A).left.appTop.hom (c' l))
      (fun l => SectionArithmetic.pullSec (β l) (snd T P.A).left) (fun j => hβ j) (𝟙 _) y hJ'
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum ((congrArg IsUnit e6).mp (hσ J hJ'))
  have hi' := isUnit_of_mul_isUnit_right hi
  rw [SectionArithmetic.sval_pullSec _ _ (𝟙 _) y hJ', Category.id_comp] at hi'
  rw [← hy]
  exact ⟨β i, _, mem_basicOpen_of_isUnit _ y _ (hJ'.mem _ _) _ hi'⟩

end GlobalTheory.Mum.SecBZeroBpf
