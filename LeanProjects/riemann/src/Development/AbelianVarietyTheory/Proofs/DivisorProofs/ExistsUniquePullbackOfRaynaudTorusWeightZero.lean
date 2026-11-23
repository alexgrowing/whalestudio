import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section
open GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht

namespace GlobalTheory.Heat.Descend

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O}

theorem q_props (Y : Ray oa) : Flat Y.q.left ∧ Surjective Y.q.left ∧ QuasiCompact Y.q.left := by
  obtain ⟨c⟩ := GlobalTheory.TorusModel.nonempty_gtCoord GlobalTheory.allSixLaws.1.globalFns Y.isGt ⊥ 0
  have := c.q_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  let F := fstG (⊥ : Ideal R) 0 Y.H
  let j := inv F.left
  have hF : F.left ≫ Y.H.hom = (thickObj R ⊥ 0 Y.H).hom ≫ thick R ⊥ 0 := Over.w F
  let ξ := Y.Φ Y.H (𝟙 _)
  obtain ⟨x, hx⟩ := GlobalTheory.TorusCoord.exists_point c (T := Y.H) (Y.H.hom ≫ inv (thick R ⊥ 0)) (by simp) ξ
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf c (T := Y.H) j (by
    rw [← hF]; exact IsIso.inv_hom_id_assoc _ _)
  let b : Y.H ⟶ Y.H := (Y.Φ Y.H).symm ξ'
  have hb : Y.Φ Y.H b = ξ' := Equiv.apply_symm_apply _ _
  let a := x ≫ F.left
  have ha : a ≫ Y.H.hom = Y.H.hom := by
    rw [Category.assoc, hF]
    exact GlobalTheory.TorusCoord.IsPointOf.comp_hom c hx
  let a' : Y.H ⟶ Y.H := Over.homMk a ha
  have haj : a ≫ j = x := by simp [a, j]
  have e1 : b.left ≫ x = j := by
    have h1 : GtPt.IsPull b.left ξ (Y.Φ Y.H (b ≫ 𝟙 _)) := Y.rep.1 Y.H Y.H b (𝟙 _)
    rw [Category.comp_id, hb] at h1
    exact (GlobalTheory.TorusCoord.IsPointOf.pull c hx h1).unique_left c hξ'
  have e1' : b.left ≫ a = 𝟙 _ := by
    rw [← Category.assoc, e1]; simp [j]
  have e2 : a' ≫ b = 𝟙 _ := by
    have h2 : GtPt.IsPull a (Y.Φ Y.H b) (Y.Φ Y.H (a' ≫ b)) := Y.rep.1 Y.H Y.H a' b
    rw [hb] at h2
    have h3 := GlobalTheory.TorusCoord.IsPointOf.pull c hξ' h2
    rw [haj] at h3
    exact (Y.Φ Y.H).injective (h3.unique_right c hx)
  have e2' : a ≫ b.left = 𝟙 _ := congrArg (·.left) e2
  have : IsIso a := ⟨⟨b.left, e2', e1'⟩⟩
  have hq : Y.q.left = a ≫ j ≫ c.q.left ≫ pullback.fst Q.P.A.hom (thick R ⊥ 0) := by
    rw [← Category.assoc a j, haj, ← GlobalTheory.TorusCoord.pG_left]
    exact hx.1
  rw [hq]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def chrUnit {S : Type} [CommRing S] {φ : R →+* S} (τ : Over.mk (spMap φ) ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q))
    (χ : GlobalTheory.RayEv.Chr Q) : Sˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.toMonoidHom
    (IsUnit.of_mul_eq_one ((coord τ).hom (AddMonoidAlgebra.single (-χ) 1)) (by
      rw [← map_mul, AddMonoidAlgebra.single_mul_single, add_neg_cancel, _root_.mul_one]
      exact map_one _)).unit

theorem unitOn_chrUnit {S : Type} [CommRing S] {φ : R →+* S}
    (τ : Over.mk (spMap φ) ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (χ : GlobalTheory.RayEv.Chr Q) :
    (unitOn (chrUnit τ χ)).val = (coord τ).hom (AddMonoidAlgebra.single χ 1) := by
  simp [unitOn, chrUnit]

theorem cv_translate (Y : Ray oa) {S : Type} [CommRing S] {φ : R →+* S}
    (τ : Over.mk (spMap φ) ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (x : Over.mk (spMap φ) ⟶ Y.H) :
    ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ ((τ ≫ Y.i) * x)).s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (chrUnit τ χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J := by
  intro χ y J hJ
  have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x (τ ≫ Y.i))).2 χ y J hJ
  have C : IsCub (DVR.th Q (T := Over.mk (spMap φ)) y J) := isCub_cubV Q.cub hJ
  rw [(Y.Φ_i τ).1, C.face₃, _root_.mul_one] at h1
  rw [mul_comm (τ ≫ Y.i) x]
  show GlobalTheory.TorusModel.cv _ χ y J = _ * GlobalTheory.TorusModel.cv _ χ y J
  rw [h1, mul_comm]
  congr 1
  apply Units.ext
  rw [(Y.Φ_i τ).2 χ y J hJ, ← gs_unit (𝟙 _) y ⊤ trivial]
  exact congrArg (gs (𝟙 _) y ⊤) (unitOn_chrUnit τ χ).symm

theorem invariant (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V))
    (hf : IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f) (Z : Over (Sp R)) (t : Z ⟶ splitTorus (Sp R) (GlobalTheory.RayEv.Chr Q)) (g : Z ⟶ Y.H)
    (h₁ : ⊤ ≤ ((t ≫ Y.i) * g).left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)) :
    (((t ≫ Y.i) * g).left.appLE _ ⊤ h₁).hom f = (g.left.appLE _ ⊤ h₂).hom f := by
  rw [← sub_eq_zero]
  refine GlobalTheory.Heat.Adjust.eq_zero_of_valR_points ⊤ _ fun S _ p hp => ?_
  rw [WtAlg.valR_sub' p ⊤ hp, HolHom.valR_appLE p _ _ _ _ _ hp, HolHom.valR_appLE p _ _ _ _ _ hp, sub_eq_zero]
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (p ≫ Z.hom)
  let φ : R →+* S := φ'.hom
  have hφ : p ≫ Z.hom = spMap φ := hφ'.symm
  let P : Over.mk (spMap φ) ⟶ Z := Over.homMk p hφ
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  have e : P ≫ ((t ≫ Y.i) * g) = ((P ≫ t) ≫ Y.i) * (P ≫ g) := by rw [MonObj.comp_mul, Category.assoc]
  have hq : (P ≫ ((t ≫ Y.i) * g)) ≫ Y.q = (P ≫ g) ≫ Y.q := by
    rw [e, MonObj.mul_comp, Category.assoc, Y.i_q, MonObj.comp_one, _root_.one_mul]
  have hc : ∀ χ y J, Good Q.P.L y J →
      val ((Y.Φ _ (P ≫ ((t ≫ Y.i) * g))).s χ) (𝟙 _) y J =
        gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (chrUnit (P ≫ t) χ)) * val ((Y.Φ _ (P ≫ g)).s χ) (𝟙 _) y J := by
    rw [e]; exact cv_translate Y (P ≫ t) (P ≫ g)
  have key := hf S φ (P ≫ g) (P ≫ ((t ≫ Y.i) * g)) (chrUnit (P ≫ t)) _ _ rfl rfl
    (fun z _ => h₂ (Set.mem_univ (p z))) (fun z _ => h₁ (Set.mem_univ (p z))) hq hc
  rw [WtAlg.c_zero _ _ _ hc, Units.val_one, _root_.one_mul] at key
  exact key

end GlobalTheory.Heat.Descend

namespace GlobalTheory.Heat

theorem exists_unique_pbT_of_isWt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsWt Y 0 _ f → ∃! f' : Γ(Q.P.A.left, V), pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = f := by
  intro R _ _ Q O _ _ _ oa Y V f hf
  obtain ⟨h1, h2, h3⟩ := Descend.q_props Y
  have H := GlobalTheory.invariant_functions_descend (Sp R) Y.H Q.P.A _ Y.q Y.i Y.q_linear.isMonHom Y.i_linear.isMonHom
    h1 h2 h3 Y.isKernel V
  have hp : ∀ f', pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = (Y.q.left.app V).hom f' := fun f' => by
    rw [GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
  obtain ⟨a, ha⟩ := H.2.2 f (fun Z t g h₁ h₂ => Descend.invariant Y V f hf Z t g h₁ h₂)
  exact ⟨a, (hp a).trans ha, fun b hb => H.1 (((hp b).symm.trans hb).trans ha.symm)⟩

end GlobalTheory.Heat
