import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf

noncomputable section

namespace GlobalTheory.UnivJetBaseChange

section General
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.ChartBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback)
attribute [local instance] Over.cartesianMonoidalCategory

variable {R R' : Type} [CommRing R] [CommRing R']

def IsUnivSp (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (κ : Type)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R κ m) ⟶ G) : Prop :=
  (∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m) ∧ (∀ m, spMap (jetAug R κ m) ≫ x m = 1) ∧
  ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), RingHom.ker aug ^ (m + 1) = ⊥ →
    ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 →
      ∃! ψ : JetR R κ m →ₐ[R] A, aug.comp ψ = jetAug R κ m ∧ y = spMap ψ ≫ x m

variable [Algebra R R'] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)

theorem isUnivSp_baseChange [IsLocalRing R] {κ : Type} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R κ m) ⟶ G}
    (hx : IsUnivSp G κ x) {x' : ∀ m : ℕ, sp (R₀ := R') (JetR R' κ m) ⟶ G'}
    (hx' : ∀ m, push hπ (x' m) = spMap (jetCoeff R R' κ m) ≫ x m) :
    IsUnivSp G' κ x' := by
  refine ⟨fun m => push_injective hπ ?_, fun m => push_injective hπ ?_, ?_⟩
  · rw [push_spMap, hx', hx', ← hx.1 m, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp]
    congr 2
    refine jet_ext fun j => ?_
    show jetTruncR R' _ m (jetCoeff R R' _ _ (zR _ j)) = jetCoeff R R' _ _ (zR _ j)
    rw [jetCoeff_zR, jetCoeff_zR]
    rfl
  · rw [push_spMap, hx', push_one, ← Category.assoc, spMap_comp]
    have : ((jetAug R' κ m).restrictScalars R).comp (jetCoeff R R' κ m) =
        (Algebra.ofId R R').comp (jetAug R κ m) := by
      refine jet_ext fun j => ?_
      show jetAug R' _ m (jetCoeff R R' _ _ (zR _ j)) = algebraMap R R' (jetAug R _ m (zR m j))
      rw [jetCoeff_zR, jetAug_zR, jetAug_zR, map_zero]
    rw [this, ← spMap_comp, Category.assoc, hx.2.1, MonObj.comp_one]
  intro A _ _ aug m hJ y hy
  letI : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨C⟩ := exists_chart G
  let q : A →ₐ[R] R' := aug.restrictScalars R
  have hq : Function.Surjective q := fun r => ⟨algebraMap R' A r, aug.commutes r⟩
  have hJq : (RingHom.ker q) ^ (m + 1) = ⊥ := hJ
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJq (push hπ y) (by
    rw [← push_spMap, hy, push_one])
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug R κ m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩)
    (ker_jetAug_pow _ m) (x m) (hx.2.1 m)
  let h₀ := fibLift q (eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJq) (ReciprocityTheory.ChartRestriction.G.Chart.pt C h₀) (by
    rw [spMap_pt]
    exact pt_eps_self C)
  have hb : ∀ j, fibSnd q (ψ₀ (zR m j)) ∈ RingHom.ker aug := fun j => by
    show q _ = 0
    rw [fib_cond, show fibFst q (ψ₀ (zR m j)) = 0 from (AlgHom.congr_fun ha _).trans (jetAug_zR m j), map_zero]
  refine ⟨jetLift R' (RingHom.ker aug) hJ _ hb, ⟨jet_ext fun j => ?_, push_injective hπ ?_⟩, ?_⟩
  · rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]
    exact hb j
  · have : ((jetLift R' (RingHom.ker aug) hJ _ hb).restrictScalars R).comp (jetCoeff R R' κ m) =
        (fibSnd q).comp ψ₀ := by
      refine jet_ext fun j => ?_
      show jetLift R' (RingHom.ker aug) hJ _ hb (jetCoeff R R' _ _ (zR _ j)) = _
      rw [jetCoeff_zR, jetLift_zR]
      rfl
    rw [push_spMap, hx', ← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, ← hψ₀, spMap_pt, hh]
    rfl
  · rintro ψ ⟨hψa, hψ⟩
    let v := (ψ.restrictScalars R).comp (jetCoeff R R' κ m)
    have hv : q.comp v = (Algebra.ofId R R').comp (jetAug R κ m) := by
      refine jet_ext fun j => ?_
      show aug.comp ψ (jetCoeff R R' _ _ (zR _ j)) = algebraMap R R' (jetAug R _ m (zR m j))
      rw [jetCoeff_zR, hψa, jetAug_zR, jetAug_zR, map_zero]
    have hvk : h = v.comp k := by
      apply pt_injective C
      rw [← hh, hψ, push_spMap, hx', ← Category.assoc, spMap_comp, hk, spMap_pt]
    have e := hu (fibLift q (jetAug R κ m) v hv) ⟨rfl, by
      rw [hk, spMap_pt]
      congr 1
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s⟩
    refine jet_ext fun j => ?_
    rw [jetLift_zR, ← e]
    show _ = ψ (jetCoeff R R' _ _ (zR _ j))
    rw [jetCoeff_zR]

end General

section Convert
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type} [CommRing V] {G : Over (Sp V)} {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B]

def toSp (y : overAt (𝟙 (Sp V)) A ⟶ G) : Chart.sp (R₀ := V) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _))

def ofSp (y : Chart.sp (R₀ := V) A ⟶ G) : overAt (𝟙 (Sp V)) A ⟶ G :=
  Over.homMk y.left ((Over.w y).trans (Category.comp_id _).symm)

theorem toSp_inj {y y' : overAt (𝟙 (Sp V)) A ⟶ G} : toSp y = toSp y' ↔ y = y' :=
  ⟨fun h => Over.OverMorphism.ext (congrArg (fun k => k.left) h), fun h => h ▸ rfl⟩

theorem toSp_one [GrpObj G] : toSp (1 : overAt (𝟙 (Sp V)) A ⟶ G) = 1 := by
  have : toSp (1 : overAt (𝟙 (Sp V)) A ⟶ G) =
      (Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.comp_id _)) :
        Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A) ≫ (1 : overAt (𝟙 (Sp V)) A ⟶ G) :=
    Over.OverMorphism.ext (Category.id_comp _).symm
  rw [this, MonObj.comp_one]

theorem isUnivJ_iff [GrpObj G] {κ : Type} (z : GlobalTheory.PowGerm.JetPts G κ) :
    GlobalTheory.PowGerm.IsUnivJ G κ z ↔ IsUnivSp G κ (fun m => toSp (z m)) := by
  refine and_congr (forall_congr' fun m => ?_) (and_congr (forall_congr' fun m => ?_) ?_)
  · rw [← toSp_inj]
    exact Iff.rfl
  · rw [← toSp_inj, toSp_one]
    exact Iff.rfl
  · constructor
    · intro H A _ _ aug m hJ y hy
      have := H A aug m hJ (ofSp y) (by rw [← toSp_inj, toSp_one]; exact hy)
      simp only [← toSp_inj] at this
      exact this
    · intro H A _ _ aug m hJ y hy
      have := H A aug m hJ (toSp y) (by rw [← toSp_inj, toSp_one] at hy; exact hy)
      simp only [← toSp_inj]
      exact this

end Convert

end GlobalTheory.UnivJetBaseChange

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem GlobalTheory.UnivJetBaseChange.exists_univ_pullback : ∀ (V V' : Type) [CommRing V] [IsLocalRing V] [CommRing V'] (φ : V →+* V') (G : Over (Sp V)) [GrpObj G] (G' : Over (Sp V')) [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G (spMap φ) F → ∀ (κ : Type) (z : GlobalTheory.PowGerm.JetPts G κ), GlobalTheory.PowGerm.IsUnivJ G κ z → ∃ z' : GlobalTheory.PowGerm.JetPts G' κ, GlobalTheory.PowGerm.IsUnivJ G' κ z' ∧ ∀ m, (z' m).left ≫ F = spMap (jetCoef φ κ m) ≫ (z m).left := by
  intro V V' _ _ _ φ G _ G' _ F hF κ z hz
  letI : Algebra V V' := φ.toAlgebra
  have hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap V V'))) F := hF
  choose x' hx' using fun m => GlobalTheory.ChartBaseChange.push_surjective hπ
    (Chart.spMap (GlobalTheory.ChartBaseChange.jetCoeff V V' κ m) ≫ GlobalTheory.UnivJetBaseChange.toSp (z m))
  refine ⟨fun m => GlobalTheory.UnivJetBaseChange.ofSp (x' m), (GlobalTheory.UnivJetBaseChange.isUnivJ_iff _).2
    (GlobalTheory.UnivJetBaseChange.isUnivSp_baseChange hπ ((GlobalTheory.UnivJetBaseChange.isUnivJ_iff z).1 hz) hx'), fun m => ?_⟩
  have e : (GlobalTheory.ChartBaseChange.jetCoeff V V' κ m).toRingHom = jetCoef φ κ m :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun p => GlobalTheory.ChartBaseChange.jetCoeff_mk m p)
  rw [← e]
  exact congrArg (fun k => k.left) (hx' m)
