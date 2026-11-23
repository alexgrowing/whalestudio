import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceUniqueRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackFstComm
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.AbDatum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbDatum

open GlobalTheory.HodgeSub GlobalTheory.HodgeSub.Nat GlobalTheory.TanFibre MonObj
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)

theorem form_comp_hom {k : Type} [CommRing k] {X : Scheme.{0}} {A : Over X} [GrpObj A] {x : Sp k ⟶ X}
    {G : Over (Sp k)} [GrpObj G] {ψ : G.left ⟶ A.left} (hp : IsGrpPullback G A x ψ)
    (f : A ⟶ A) [IsMonHom f] (f' : G ⟶ G) [IsMonHom f'] (hf : f'.left ≫ ψ = ψ ≫ f.left)
    {y : specO k (DualNumber k) ⟶ G} (hy : epsZero k ≫ y = η) (hy' : epsZero k ≫ y ≫ f' = η)
    (w : (y.left ≫ ψ) ≫ A.hom = (specO k (DualNumber k)).hom ≫ x)
    (we : sec (epsZero k) ≫ y.left ≫ ψ = x ≫ unitSec A)
    (w' : ((y ≫ f').left ≫ ψ) ≫ A.hom = (specO k (DualNumber k)).hom ≫ x)
    (we' : sec (epsZero k) ≫ (y ≫ f').left ≫ ψ = x ≫ unitSec A) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V)
    (s : Γ(omega A, V)) :
    (form w' we').app ⊤ (QCoh.pullbackSections x (omega A) h s) =
      (form w we).app ⊤ (QCoh.pullbackSections x (omega A) h ((omegaMap f).app V s)) := by
  have nat := omegaBase_naturality hp hp f f' hf
  have e₁ := form_eq_fibre hp hy w we
  have e₂ := form_eq_fibre hp hy' w' we'
  have e₃ := cotMap_comp (IsMonHom.one_hom f') hy rfl hy'
  have key : form w' we' = (Scheme.Modules.pullback x).map (omegaMap f) ≫ form w we :=
    e₂.trans <| (congrArg (fun z ↦ omegaBase hp ≫ z ≫ (epsIso k).hom) e₃.symm).trans <|
      (congrArg (omegaBase hp ≫ ·) (Category.assoc _ _ _)).trans <| (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ cotMap y hy ≫ (epsIso k).hom) nat.symm).trans <| (Category.assoc _ _ _).trans <|
      congrArg ((Scheme.Modules.pullback x).map (omegaMap f) ≫ ·) e₁.symm
  refine (congr(($key).app ⊤ (QCoh.pullbackSections x (omega A) h s))).trans ?_
  exact congrArg ((form w we).app ⊤) (QCoh.pullback_map_app_pullbackSections x (omegaMap f) h s)

theorem corr_pull {T : Scheme.{0}} {A : Over T} [GrpObj A] (f : A ⟶ A) [IsMonHom f] {V : T.Opens}
    (hV : IsAffineOpen V) (s : Γ(omega A, V)) (c : primDR (onAff A hV)) (hc : HodgeSub.Corr A hV s c) :
    HodgeSub.Corr A hV ((omegaMap f).app V s)
      (primPull (dp0 Γ(T, V)) (𝟙 _) (A := onAff A hV) (B := onAff A hV) ((Over.pullback hV.fromSpec).map f) c) := by
  intro v h hv w we
  let f' : onAff A hV ⟶ onAff A hV := (Over.pullback hV.fromSpec).map f
  have hp : IsGrpPullback (onAff A hV) A hV.fromSpec _ := isGrpPullback_pullback A hV.fromSpec
  have hv' := hv.push f'
  have t := hv'.1
  have w' : ((v ≫ f').left ≫ pullback.fst A.hom hV.fromSpec) ≫ A.hom =
      (Pdiv.specO Γ(T, V) (DualNumber Γ(T, V))).hom ≫ hV.fromSpec := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ hV.fromSpec) (Over.w (v ≫ f'))
  have we' : sec (epsZero Γ(T, V)) ≫ (v ≫ f').left ≫ pullback.fst A.hom hV.fromSpec =
      hV.fromSpec ≫ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec A := by
    rw [← Category.assoc]
    exact (congrArg (· ≫ pullback.fst A.hom hV.fromSpec) t).trans (unitSec_comp hp)
  exact (hc (v ≫ f') _ hv' w' we').trans (congrArg (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom
    (form_comp_hom hp f f' (pullback.lift_fst _ _ _) (epsZero_comp_of_isTangent hv.1)
      (epsZero_comp_of_isTangent t) w we w' we' hV.fromSpec_preimage_self.ge s))

theorem isEquivariant_hodgeIncl : GlobalTheory.CovTop.Hypotheses2 → ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (A : Over T) [GrpObj A] [QuasiSeparated A.hom] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (i : OAct O A) (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (ρ : O →+* End H) (a : omega A ⟶ H), IsDRAct e i ρ → IsHodgeIncl e a → IsEquivariant (omegaAct i) ρ a := by
  intro P O _ T A _ _ g hA hg i H e ρ a hρ ha x
  haveI := i.hom x
  refine hom_ext_affine fun V hV s ↦ (e V hV).injective ?_
  have h₁ := (ha V hV ((omegaMap (i.act x)).app V s)).2
  have h₂ := corr_pull (i.act x) hV s _ (ha V hV s).2
  have h₃ := corr_unique P T A g hA hg V hV _ _ _ h₁ h₂
  exact h₃.trans (hρ x V hV _).symm

end GlobalTheory.AbDatum
