import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartBaseChangeRigGerm

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ChartRigBC

open GlobalTheory.RawChartGermBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0) (d : ℕ)

theorem jetCoef_eq (κ : Type) (m : ℕ) : jetCoef ψ κ m = jetBC ψ κ m :=
  RingHom.ext fun a => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl

theorem subst_jetCoef (m n n' : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (φ' : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S') (h : ∀ p, φ' p = MvPolynomial.map ψ (φ p)) :
    (Formalism.L2.Pj.homAt x1 (jetSubstP m φ')).left ≫ spMap (jetCoef ψ (Fin n × Fin d) m) =
      spMap (jetCoef ψ (Fin n' × Fin d) m) ≫ (Formalism.L2.Pj.homAt x0 (jetSubstP m φ)).left := by
  obtain rfl : φ' = fun p => MvPolynomial.map ψ (φ p) := funext h
  rw [jetCoef_eq, jetCoef_eq]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem aug_jetCoef (m n : ℕ) :
    (Formalism.L2.Pj.homAt x1 (jetAug : Jet S' (Fin n × Fin d) m →ₐ[S'] S')).left ≫ spMap (jetCoef ψ (Fin n × Fin d) m) =
      spMap ψ ≫ (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S)).left := by
  rw [jetCoef_eq]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetAug_comp_jetBC ψ _ m)

theorem overAt_hom_comp :
    (overAt (spMap ψ ≫ x0) S').hom = spMap ψ ≫ (overAt x0 S).hom := by
  change spMap (algebraMap S' S') ≫ spMap ψ ≫ x0 = spMap ψ ≫ spMap (algebraMap S S) ≫ x0
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact spMap_comp_eq _ _ _ _ (RingHom.ext fun _ => rfl)

theorem val_eLG_bc (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G)
    (hx : ∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left)
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m)
    (he : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m))))
    (wP : PrimTyG t) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jOG x1 d m 1).left) (z : Z) {J}
    (hJ : Good t.PP.L z J) :
    val (eLG t x1 d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP m) r z J =
      val (eLG t x0 d x act e wP m) (r ≫ spMap (jetCoef ψ (Fin 1 × Fin d) m)) z J := by
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine congrArg (fun q => val wP q z J) ?_
    exact (congrArg (r ≫ ·) (hx m)).trans (Category.assoc _ _ _).symm
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine (val_corr hJ (he m) _).trans ((val_pull hJ _ _ _).trans ?_)
    refine congrArg (fun q => val (e m) q z J) ?_
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine congrArg (r ≫ ·) (subst_jetCoef ψ x0 x1 d m 2 1 _ _ ?_)
    rintro ⟨i, j⟩
    fin_cases i
    · exact (MvPolynomial.map_X ψ _).symm
    · exact (map_psIn ψ d m _ _).symm

end GlobalTheory.ChartRigBC

namespace GlobalTheory

open ChartRigBC in

theorem rigidificationAtOrigin_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (wP : PrimTyG t), wP.IsGen → Rig0G t x0 d x act e wP → Rig0G t x1 d x' (fun a i => (MvPowerSeries.map ψ (act a i))) e' wP := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 hx1 d x x' hx e e' _ _ he act wP _ h0
  have hL := t.PP.isLB
  refine corr_of_val hL fun y J hJ => ?_
  refine (val_pull hJ _ _ _).trans ((val_eLG_bc t ψ x0 x1 d act x x' hx e e' he wP 0 _ y hJ).trans ?_)
  refine Eq.trans ?_ (GermB.val_rigT _ _ _ _ _ y J hJ).symm
  have h1 := (val_pull hJ _ _ _).symm.trans ((val_corr hJ h0 (spMap ψ)).trans (GermB.val_rigT _ _ _ _ _ y J hJ))
  refine (congrArg (fun q => val (eLG t x0 d x act e wP 0) q y J) ?_).trans
    (h1.trans (congrArg (fun q => val t.PP.rig q y J) ?_))
  · rw [Category.id_comp]; exact aug_jetCoef ψ x0 x1 d 0 1
  · subst hx1
    rw [Category.id_comp]; exact (overAt_hom_comp ψ x0).symm

end GlobalTheory
