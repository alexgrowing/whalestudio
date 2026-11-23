import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitOfStalks
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ThetaEigen

theorem gs_pow {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem sval_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (pr : Y ⟶ X) (a b : ℤ) (l : ℕ)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => a)))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => b)))
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) : sval t r z J = sval th r z J ^ l := by
  have key : ∀ j : L.ι, (t.f (fun _ => j) : Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j))) =
      (show Γ(Y, LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) from th.f (fun _ => j)) ^ l := fun j =>
    fn_ext (V := LB.wchart L (fun _ : Fin 1 => pr) (fun _ => j)) fun y hy => by
      obtain ⟨I, hI, e⟩ := exists_good L hL y (K := PUnit) (fun _ => 𝟙 Y ≫ pr) (fun _ => j) (fun _ _ _ => rfl)
        (fun _ => Set.mem_iInter.1 hy 0)
      have := hp y I hI
      rw [sval_of t _ y I (fun _ => j) (fun _ => e PUnit.unit),
        sval_of th _ y I (fun _ => j) (fun _ => e PUnit.unit)] at this
      exact this.trans (gs_pow _ y _ hy _ l).symm
  exact (congrArg (gs r z _) (key _)).trans (gs_pow r z _ (hJ.mem (fun _ : Fin 1 => pr) r) _ l)

theorem exists_gen_of_eigen {X Y : Scheme.{0}} [IsIntegral Y] (hN : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {L : LB X} (hL : L.IsLB) (pr m : Y ⟶ X) (τ : Y ⟶ Y) (hm : τ ≫ pr = m) (l : ℕ) (hl : 1 ≤ l)
    (th : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => ((1 : ℕ) : ℤ))))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => pr) (fun _ => (l : ℤ)))) (h0 : ∃ j, th.f j ≠ 0)
    (hp : ∀ y J, Good L y J → sval t (𝟙 Y) y J = sval th (𝟙 Y) y J ^ l) (c : Γ(Y, ⊤)ˣ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![pr, m] ![(l : ℤ), -(l : ℤ)])) (hα : α.IsGen)
    (H : ∀ y J, Good L y J →
      gs (𝟙 Y) y ⊤ c.val * sval t (𝟙 Y) y J = (val α (𝟙 Y) y J).val * sval t (𝟙 Y ≫ τ) y J) :
    ∃ r : LB.Gen (LB.LinComb L (K := Fin 2) ![m, pr] ![1, -1]), r.IsGen := by
  obtain ⟨s₁, h₁⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => m) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, hm, Nat.cast_one])
    (DVR.pullSec L _ _ th τ)
  obtain ⟨s₂, h₂⟩ := exists_sec hL (K' := PUnit) (φ' := fun _ => pr) (ε' := fun _ => 1)
    (fun U _ h => by simp only [Fin.prod_univ_one, Fintype.prod_unique, Nat.cast_one]) th
  obtain ⟨u, hu, h₃⟩ := exists_gen hL (K' := Fin 2) (φ' := ![m, pr]) (ε' := ![(l : ℤ), -(l : ℤ)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, inv_inv]
      exact _root_.mul_comm _ _)
    (DVR.scaleGen c (LB.invGen L _ _ α)) (DVR.scaleGen_isGen _ _ (DVR.invGen_isGen _ _ _ _ hα))
  have h₄ : ∀ y J, Good L y J → val u (𝟙 Y) y J = gm (𝟙 Y) y ⊤ c * (val α (𝟙 Y) y J)⁻¹ := fun y J hJ =>
    (h₃ _ _ y J hJ).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res _ y le_top (hJ.mem ![pr, m] (𝟙 Y)) c) (val_inv α (𝟙 Y))))
  obtain ⟨r, hr, -⟩ := RootUnit.exists_gen_of_pow X Y hN L hL m pr l hl s₁ s₂ u hu
    (by
      obtain ⟨y⟩ : Nonempty Y := inferInstance
      choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
      have hJ' : Good L y J := hJ
      refine ⟨fun _ => J (𝟙 Y ≫ pr), fun e => ?_⟩
      refine RootUnit.sec_gs_ne_zero th h0 y _ (hJ'.mem (fun _ : Fin 1 => pr) (𝟙 Y)) ?_
      refine (h₂ _ _ y J hJ').symm.trans ((congrArg (gs (𝟙 Y) y _) e).trans ?_)
      exact (RootUnit.gs_id y _ (hJ'.mem (fun _ : PUnit => pr) (𝟙 Y)) _).trans (map_zero _))
    (fun y J hJ => by
      have e₁ := (h₁ _ (𝟙 Y) y J hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ th τ _ y hJ)
      have e₂ := h₂ _ (𝟙 Y) y J hJ
      have e := H y J hJ
      rw [hp y J hJ, sval_pow hL pr _ _ l th t hp _ y J hJ, gs_unit _ y ⊤ (by trivial)] at e
      refine (congrArg (· ^ l) e₁).trans (Eq.trans ?_ (congrArg₂ (fun a b => Units.val a * b ^ l) (h₄ y J hJ) e₂).symm)
      change _ = Units.val (_ * _) * _
      rw [Units.val_mul, mul_right_comm, e, mul_right_comm, Units.mul_inv, _root_.one_mul])
  exact ⟨r, hr⟩

theorem main : ∀ (S : Scheme.{0}) (P : PolAV S) (F : Type) [Field F] (p : Spec (CommRingCat.of F) ⟶ S) (l : ℕ), 1 ≤ l → ∀ (th : EA P p 1) (t : EA P p l) (θ : ThetaGrp P.A P.L (l : ℤ) (Over.mk p)) (c : Fˣ), th ≠ 0 → (∀ z J, Good P.L z J → sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((l : ℕ) : ℤ)) t.sec (𝟙 _) z J = sval (L := P.L) (φ := fun _ : Fin 1 => (snd (Over.mk p) P.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th.sec (𝟙 _) z J ^ l) → IsActOf P.A P.L (l : ℤ) θ t.sec (c.val • t).sec → θ.pt = 1 := by
  intro S P F _ p l hl th t θ c h0 hp hθ
  haveI := P.isAb.smooth
  haveI := P.isAb.geomConnected
  haveI : IsIntegral (Over.mk p).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  haveI := isIntegral_tensor_left_of_smooth_grpObj S P.A (Over.mk p)
  have hs : Smooth (fst (Over.mk p) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst p P.A.hom))
  have hN := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hs).2.1
  let φ : F →+* Γ((Over.mk p ⊗ P.A).left, ⊤) :=
    (fst (Over.mk p) P.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  obtain ⟨r, hr⟩ := exists_gen_of_eigen (fun y => (hN y).2) P.isLB (snd (Over.mk p) P.A).left
    (translPt P.A θ.pt).left (translT P.A θ.pt).left (by rw [← Over.comp_left, translT, lift_snd]) l hl th.sec t.sec
    (not_forall.1 fun h => h0 ((SecMod.eq_zero_iff th).2 h)) hp (Units.map φ.toMonoidHom c) θ.φ θ.isGen
    (fun y J hJ => (SecMod.sval_smul hJ (𝟙 _) c.val t).symm.trans (ThetaLin.sval_of_isTwistPull P.A hθ (𝟙 _) y hJ))
  exact P.ktriv F p θ.pt fun _ => ⟨⊤, trivial, exists_isGen_pull (translDiff P.A P.L θ.pt) r hr _⟩

end GlobalTheory.ThetaEigen

end
