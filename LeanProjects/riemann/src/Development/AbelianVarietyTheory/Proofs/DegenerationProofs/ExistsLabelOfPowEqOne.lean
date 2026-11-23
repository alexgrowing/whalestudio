import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem pow_eq_one_iff_of_isGrpPullback {S S' X : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {a' : X ⟶ S'} {a : X ⟶ S} (e : a = a' ≫ f)
    (x' : Over.mk a' ⟶ G') (x : Over.mk a ⟶ G) (hx : x.left = x'.left ≫ φ) (m : ℕ) :
    x' ^ m = 1 ↔ x ^ m = 1 := by
  subst e
  have hx' : x = pushHom h (Over.mk a') x' := Over.OverMorphism.ext hx
  have inj : Function.Injective (pushHom h (Over.mk a')) := fun y y' hy => by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) hy
    · rw [Over.w y, Over.w y']
  have : x ^ m = pushHom h (Over.mk a') (x' ^ m) := by rw [map_pow]; exact congrArg (· ^ m) hx'
  rw [this]
  exact (map_eq_one_iff _ inj).symm

theorem epi_spMap_of_field {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    letI := i.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (inferInstance : Module.Flat K L)
  have : Surjective (spMap i) := ⟨fun x => ⟨(⊥ : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_label_of_pow_eq_one : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real)
    (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N →
    ∀ h : baseOver (Sp u.V) ⟶ u.G, h ^ m = 1 → ∃ b : S.Gam, m • b = 0 ∧ GlobalTheory.UnitTheta.Extends u b h := by
  intro o Ω _ _ _ S ρ p _ y₀ u m hm h hh
  have := u.U.gen_hom
  have hw : h.left ≫ u.G.hom = 𝟙 _ := Over.w h
  let x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V) :=
    pullback.lift (jK u.V ≫ h.left) (𝟙 _) (by rw [Category.assoc, hw]; simp)
  have hx₁ : x ≫ pullback.fst _ _ = jK u.V ≫ h.left := pullback.lift_fst _ _ _
  have hx₂ : x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  let i : Sp (PadicAlgCl p) ⟶ Sp (FractionRing u.V) := spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))
  have : Epi i := epi_spMap_of_field _
  have hy : spMap y₀ = i ≫ spMap u.yK :=
    (congrArg spMap u.fac).symm.trans (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom _))
  have hψ : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK) (u.U.gen.hom.left ≫ u.φ) :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  let x' : Over.mk i ⟶ (Over.pullback (jK u.V)).obj u.G :=
    Over.homMk (i ≫ x) (by
      show (i ≫ x) ≫ pullback.snd _ _ = i
      rw [Category.assoc, hx₂, Category.comp_id])
  let t : Over.mk (i ≫ jK u.V) ⟶ baseOver (Sp u.V) := Over.homMk (i ≫ jK u.V) (by simp)
  have h₀ : (t ≫ h) ^ m = 1 := by
    have := (map_pow (preHom (G := u.G) t) h m).symm.trans ((congrArg _ hh).trans (map_one _))
    exact this
  have h₁ : x' ^ m = 1 :=
    (pow_eq_one_iff_of_isGrpPullback (isGrpPullback_pullback u.G (jK u.V)) rfl x' (t ≫ h) (by
      show (i ≫ jK u.V) ≫ h.left = (i ≫ x) ≫ pullback.fst _ _
      rw [Category.assoc, Category.assoc, hx₁]) m).2 h₀
  let z : Over.mk (spMap y₀) ⟶ ρ.P.A := Over.homMk (x'.left ≫ u.U.gen.hom.left ≫ u.φ) (by
    show (x'.left ≫ u.U.gen.hom.left ≫ u.φ) ≫ ρ.P.A.hom = spMap y₀
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w x', hy]; rfl)
  have h₂ : z ^ m = 1 := (pow_eq_one_iff_of_isGrpPullback hψ hy x' z rfl m).1 h₁
  have h₃ : z ^ (S.r * S.N) = 1 := by
    obtain ⟨c, hc⟩ := hm
    rw [hc, pow_mul, h₂, one_pow]
  obtain ⟨b, hb, -⟩ := ρ.pt_bij (PadicAlgCl p) (spMap y₀) z h₃
  have h0 : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  refine ⟨b, ?_, x, hx₁, hx₂, ?_⟩
  · refine (ρ.pt_bij (PadicAlgCl p) (spMap y₀) 1 (one_pow _)).unique ?_ ?_
    · rw [hp, ← h₂, ← hb]
      exact map_pow (preHom (G := ρ.P.A) _) _ m
    · rw [h0]
      exact map_one (preHom (G := ρ.P.A) _)
  · have e : spMap y₀ ≫ (ρ.pt b).left = (i ≫ x) ≫ u.U.gen.hom.left ≫ u.φ := congrArg (fun w => w.left) hb
    rw [← cancel_epi i, ← Category.assoc i (spMap u.yK), ← hy, e, Category.assoc]

end GlobalTheory.UnitTheta
