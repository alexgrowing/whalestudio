import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudFourierTermSubSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecBGenericAgree

variable {R : Type} [CommRing R] [IsDomain R]

theorem isUnit_jK_app (c : R) (hc : c ≠ 0) :
    IsUnit ((jK R).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have h := congrArg (fun q => q.hom c)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  have hu : IsUnit (algebraMap R (FractionRing R) c) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)).isUnit
  have := hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
  rw [h] at this
  exact this

theorem isUnit_gs (Q : DegPre R) (c : R) (hc : c ≠ 0) (z : (DegPre.BF Q (FractionRing R)).left) :
    IsUnit (gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := by
  have e1 : (DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom =
      ((fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
    rw [Over.w (DegPre.prB Q (FractionRing R)), Category.assoc]
    exact (Over.w (fst (TF (R := R) (FractionRing R)) Q.P.A)).symm
  rw [e1, ← gs_pull ((fst (TF (R := R) (FractionRing R)) Q.P.A).left ≫ jFK (R := R) (FractionRing R)) (jK R) z ⊤ trivial,
    gs_eq _ z (jK R ⁻¹ᵁ ⊤) trivial]
  exact ((isUnit_jK_app c hc).map _).map _

theorem f_eq (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R) (hc : c ≠ 0)
    (H : ∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι),
      Good Q.P.L z J →
      gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
          sval s (DegPre.prB Q (FractionRing R)).left z J =
        gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) *
          sval s' (DegPre.prB Q (FractionRing R)).left z J)
    (j : Fin 4 → Q.P.L.ι) : s.f j = s'.f j := by
  set p := (DegPre.prB Q (FractionRing R)).left
  have H' : ∀ z J, Good Q.P.L z J → sval s p z J = sval s' p z J := fun z J hJ =>
    (isUnit_gs Q c hc z).mul_left_cancel (H z J hJ)
  refine GlobalTheory.IntegralExpansion.prB_app_injective Q _ (fn_ext fun y hy => ?_)
  choose I hI using fun χ : (DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left => exists_chart Q.P.isLB (χ y)
  have hI' : Good Q.P.L y I := hI
  have m := hI'.mem (DegPre.famφB Q β) p
  rw [gs_pull (𝟙 _) p y _ hy, gs_pull (𝟙 _) p y _ hy, Category.id_comp]
  exact (sec_trans s p y hy m).trans ((congrArg _ (H' y I hI')).trans (sec_trans s' p y hy m).symm)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (β : Q.X) (s s' : Q.SecB k β) (c : R), c ≠ 0 → (∀ (z : (DegPre.BF Q (FractionRing R)).left) (J : ((DegPre.BF Q (FractionRing R)).left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s (DegPre.prB Q (FractionRing R)).left z J = gs ((DegPre.prB Q (FractionRing R)).left ≫ Q.P.A.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval s' (DegPre.prB Q (FractionRing R)).left z J) → ∀ (Z : Scheme.{0}) (x : Z ⟶ Q.P.A.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval s x z J = sval s' x z J := by
  intro R _ _ Q k β s s' c hc H Z x z J _
  have hf : s.f = s'.f := funext (f_eq Q k β s s' c hc H)
  show gs x z _ (s.f _) = gs x z _ (s'.f _)
  rw [hf]

end GlobalTheory.SecBGenericAgree
