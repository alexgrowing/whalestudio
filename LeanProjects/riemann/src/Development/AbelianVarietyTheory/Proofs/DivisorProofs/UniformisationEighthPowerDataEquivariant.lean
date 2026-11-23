import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianUniformisingEighthPowerIsPowerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerDegDataLatticeIsoEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerEndomorphismActsByIntMatriStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.PowEq

theorem endU_exists (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (hCN : IsCN V₁)
    (D : DegData V₁ (maximalIdeal V₁)) (P : PolAV (Sp (FractionRing V₁))) (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (maximalIdeal V₁) D P G) (aA : P.A ⟶ P.A) (haA : IsMonHom aA) :
    ∃ E : EndU U.toUnifPre, E.aA = aA := by
  have hadm : AdmBase V₁ (maximalIdeal V₁) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  haveI := hCN.1
  haveI := hCN.2.1
  have := U.gen_hom
  have hinv : IsMonHom U.gen.inv := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds V₁
    (FractionRing V₁) G G hG hG (U.gen.hom ≫ aA ≫ U.gen.inv)
  obtain ⟨E, -, hE⟩ := GlobalTheory.UT.exists_degenerationEndomorphism_of_admissibleBase V₁ (maximalIdeal V₁) hadm D P G hG U F aA hF haA
    (by rw [hF']; simp)
  exact ⟨E, hE⟩

theorem isMonHom_of_matrix : ∀ (S : Scheme.{0}) (X Y : Over S) [GrpObj X] [GrpObj Y] [IsCommMonObj Y] (pr : Fin 8 → (X ⟶ Y)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over S) (y' : Fin 8 → (T' ⟶ Y)), ∃! x : T' ⟶ X, ∀ a, x ≫ pr a = y' a) → ∀ (f : X ⟶ X) (a : Matrix (Fin 8) (Fin 8) ℤ), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → IsMonHom f := by
  intro S X Y _ _ _ pr hpr hu f a hf
  haveI : ∀ v, IsMonHom (pr v) := hpr
  refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_
  have hz : ∀ (z : T ⟶ X) (u : Fin 8), z ≫ f ≫ pr u = ∏ v, (z ≫ pr v) ^ a u v := by
    intro z u
    let φz : (X ⟶ Y) →* (T ⟶ Y) := ⟨⟨(z ≫ ·), MonObj.comp_one z⟩, MonObj.comp_mul z⟩
    rw [hf u, List.prod_ofFn]
    exact (map_prod φz _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow φz _ _)
  refine (hu T fun u => ((x * y) ≫ f) ≫ pr u).unique (fun u => rfl) (fun u => ?_)
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hz, hz, hz]
  simp only [MonObj.mul_comp, mul_zpow, Finset.prod_mul_distrib]

end GlobalTheory.Poinc.Sep.PowEq

open GlobalTheory.Poinc.Sep.PowEq in

theorem GlobalTheory.Poinc.Sep.unif_pow_equivariant : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)), SiegPB c F.univ y → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G), ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ aA : P.A ⟶ P.A, (∀ u, aA ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → ∃ E : EndU U.toUnifPre, E.aA = aA ∧ ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN hinj hfin D₀ e₀ hR G₀ _ _ A₀ U₀ y α α₂ hsa hpb hsq hlb P c hc pr hpr hpru hPL G _ _ hG D U
  obtain ⟨φc, φ₂, hφc, hsq', hlb', hlev⟩ := hc
  obtain ⟨q, hq, hqu, hqc⟩ := GlobalTheory.T.semiAbelian_uniformising_eighthPower_isPower_model g n o ζ F V₁ hCN D₀ G₀ A₀ U₀ y α hsa hpb P c φc hφc pr hpr hpru G hG D U
  obtain ⟨e, hS, heq⟩ := GlobalTheory.T.eighthPowerDegData_latticeIso_equivariant g n o ζ F W hW V Q V₁ ρ hCN hinj hfin D₀ e₀ hR G₀ A₀ U₀ y α α₂ hsa hpb hsq hlb P c
    φc φ₂ hφc hsq' hlb' hlev pr hpr hpru hPL G hG D U q hq hqu hqc
  refine ⟨e, hS, fun a a' ha aA haA => ?_⟩
  obtain ⟨E, hE⟩ := endU_exists V₁ hCN D P G hG U aA (isMonHom_of_matrix _ P.A c.A pr hpr hpru aA a haA)
  refine ⟨E, hE, heq a a' ha E (GlobalTheory.T.uniformisedEighthPower_endomorphism_acts_by_intMatrix g n o ζ F V₁ hCN D₀ G₀ A₀ U₀ y α hsa hpb P c φc hφc pr hpr G hG D U q hq hqc
    a E ?_)⟩
  rw [hE]
  exact haA
