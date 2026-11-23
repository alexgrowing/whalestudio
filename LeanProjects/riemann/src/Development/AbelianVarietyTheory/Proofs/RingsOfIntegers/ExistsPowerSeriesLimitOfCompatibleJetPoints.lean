import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrder

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit.LimEx

variable {V : Type} [CommRing V] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem isLocalRing_jet [IsLocalRing V] (m : ℕ) : IsLocalRing (Jet V κ m) :=
  haveI : Nontrivial (Jet V κ m) := (jetAug : Jet V κ m →ₐ[V] V).toRingHom.domain_nontrivial
  IsLocalRing.of_surjective' (jetA κ m : MvPowerSeries κ V →ₐ[V] Jet V κ m).toRingHom
    (fun a => GlobalTheory.ChartCmp.FrameRatio.psJet_surj m a)

theorem exists_ringHom_of_jets {A : Type} [CommRing A] (φ : ∀ m, A →+* Jet V κ m)
    (h : ∀ m a, (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) (φ (m + 1) a) = φ m a) :
    ∃ ψ : A →+* MvPowerSeries κ V, ∀ m a, jetA κ m (ψ a) = φ m a := by
  choose f hf using fun a => GermD.exists_ps_of_jets (fun m => φ m a) (fun m => h m a)
  have hf' : ∀ a m, jetA κ m (f a) = φ m a := hf
  have ext : ∀ {p q : MvPowerSeries κ V}, (∀ m, jetA κ m p = jetA κ m q) → p = q :=
    fun hpq => FrameBiextId.ps_ext hpq
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun m a => hf' a m⟩
  · exact ext fun m => by rw [hf', map_one, map_one]
  · exact fun a b => ext fun m => by rw [map_mul, hf', hf', hf', map_mul]
  · exact ext fun m => by rw [hf', map_zero, map_zero]
  · exact fun a b => ext fun m => by rw [map_add, hf', hf', hf', map_add]

theorem exists_limit_hom [IsLocalRing V] {Y : Scheme.{0}} (p : Y ⟶ Spec (.of V))
    (x : ∀ m, Spec (.of (Jet V κ m)) ⟶ Y)
    (hx : ∀ m, Spec.map (CommRingCat.ofHom
      ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)) ≫ x (m + 1) = x m)
    (hp : ∀ m, x m ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (Jet V κ m)))) :
    ∃ g : Spec (.of (MvPowerSeries κ V)) ⟶ Y,
      g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (MvPowerSeries κ V))) ∧
      ∀ m, Spec.map (CommRingCat.ofHom ((jetA κ m : MvPowerSeries κ V →ₐ[V] Jet V κ m) :
        MvPowerSeries κ V →+* Jet V κ m)) ≫ g = x m := by
  have hloc := fun m => isLocalRing_jet (V := V) (κ := κ) m
  let y : Y := x 0 (closedPoint (Jet V κ 0))
  have hy : ∀ m, x m (closedPoint (Jet V κ m)) = y := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [← ih, ← hx m]
      refine Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _).symm
      have : IsLocalHom (CommRingCat.ofHom
          ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)).hom :=
        IsLocalHom.of_surjective _ (fun a => by
          obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
          exact ⟨Ideal.Quotient.mk _ q, rfl⟩)
      have h1 := Spec_closedPoint (f := CommRingCat.ofHom
          ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m))
      exact congrArg (x (m + 1)) h1.symm
  choose φ hφ using fun m => (GlobalTheory.existsUnique_factor_stalk (x m) (hy m)).exists
  have hc : ∀ m a, (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) ((φ (m + 1)).hom a) = (φ m).hom a := by
    intro m a
    have h1 : Spec.map (CommRingCat.ofHom
        ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)) ≫
        Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono (Y.fromSpecStalk y), Category.assoc, hφ, hφ, hx m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom a)
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_jets (fun m => (φ m).hom) hc
  obtain ⟨s, hs⟩ := Spec.map_surjective (Y.fromSpecStalk y ≫ p)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk y, ?_, fun m => ?_⟩
  · rw [Category.assoc, ← hs, ← Spec.map_comp]
    congr 1
    ext1
    refine RingHom.ext fun c => FrameBiextId.ps_ext fun m => ?_
    have h1 : Spec.map (φ m) ≫ Spec.map s = Spec.map (CommRingCat.ofHom (algebraMap V (Jet V κ m))) := by
      rw [hs, ← Category.assoc, hφ, hp]
    rw [← Spec.map_comp] at h1
    have h2 : (φ m).hom (s.hom c) = algebraMap V (Jet V κ m) c := congr($(Spec.map_injective h1).hom c)
    exact ((hψ m (s.hom c)).trans h2).trans ((jetA κ m).commutes c).symm
  · rw [← hφ m, ← Spec.map_comp_assoc]
    congr 2
    ext1
    exact RingHom.ext fun a => hψ m a

theorem exists_isLimit : ∀ (V : Type) [CommRing V] [IsLocalRing V] (G : Over (Sp V)) (d : ℕ)
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G),
    (∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m) →
    ∃ X : limO V d 1 ⟶ G, IsLimit x X := by
  intro V _ _ G d x hx
  obtain ⟨g, hg, hg'⟩ := exists_limit_hom (V := V) (κ := Fin 1 × Fin d) G.hom (fun m => (x m).left)
    (fun m => congrArg CommaMorphism.left (hx m))
    (fun m => (Over.w (x m)).trans (Category.comp_id _))
  exact ⟨Over.homMk g (hg.trans (Category.comp_id _).symm), fun m => Over.OverMorphism.ext (hg' m)⟩

end GlobalTheory.TransUnit.LimEx
