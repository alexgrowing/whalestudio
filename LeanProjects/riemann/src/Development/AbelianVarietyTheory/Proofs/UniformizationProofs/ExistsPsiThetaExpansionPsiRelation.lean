import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisTwistField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullBValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalNeZeroOfIsIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.PsiExists

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h := DVR.cPoint_add D T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem comp_famφT {T T₀ : Over (Spec (CommRingCat.of R))} (r : T ⟶ T₀ ⊗ D.P.A) (α : D.X) (k : Fin 4) :
    r.left ≫ famφT D T₀ α k = ![(r ≫ snd T₀ D.P.A).left, ((r ≫ snd T₀ D.P.A) * cT D T α).left, (cT D T α).left,
      (1 : T ⟶ D.P.A).left] k := by
  have c : r ≫ cT D _ α = cT D T α := by rw [← Category.assoc, comp_toUnit]
  fin_cases k
  · rfl
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul r (snd T₀ D.P.A) (cT D _ α)).trans (congrArg _ c))
  · exact congrArg (fun q => q.left) c
  · exact congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) r)

theorem famφT_eq (T₀ : Over (Spec (CommRingCat.of R))) (α : D.X) :
    famφT D T₀ α = ![(snd T₀ D.P.A).left, (snd T₀ D.P.A * cT D _ α).left, (cT D _ α).left,
      (1 : T₀ ⊗ D.P.A ⟶ D.P.A).left] := rfl

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_pullB {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) :
    ∃ s : Raw D F k, PullB D F φ k f s := by
  have H : ∀ α, FormEq (Sum.elim (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i)
      (fun e : PEmpty => (e.elim : (DegPre.BF D F).left ⟶ D.P.A.left))) (Sum.elim (DegPre.famε k) fun e => e.elim)
      (DegPre.famφ D F α) (DegPre.famε k) := by
    intro α U _ h
    have e : (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i) = DegPre.famφ D F α := by
      funext i
      rw [comp_famφT, whiskerRight_snd]; rfl
    rw [e, Fintype.prod_sum_type]
    simp
  choose s hs using fun α => exists_sec D.P.isLB (H α)
    (pullMulSec (f α) (φ ▷ D.P.A).left (LB.oneGen D.P.L) (oneGen_isGen _))
  refine ⟨s, fun α z J hJ => ?_⟩
  refine (hs α _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one, Category.id_comp]

theorem isIso_trF (χ : D.X) : IsIso (DegPre.trF D F χ) := by
  have key : ∀ a b : D.X, a + b = 0 → DegPre.trF D F a ≫ DegPre.trF D F b = 𝟙 _ := by
    intro a b hab
    have c : DegPre.trF D F a ≫ cT D _ b = cT D _ b := by rw [← Category.assoc, comp_toUnit]
    have e : DegPre.trF D F a ≫ (snd (TF (R := R) F) D.P.A * cT D _ b) = snd _ _ := by
      rw [MonObj.comp_mul, c, show DegPre.trF D F a ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ a from lift_snd _ _,
        _root_.mul_assoc]
      have := (DVR.cPoint_add D (DegPre.BF D F) a b).symm
      rw [hab] at this
      rw [show cT D (DegPre.BF D F) a * cT D _ b = 1 from this.trans (cT_zero D _), _root_.mul_one]
    have e' : DegPre.trF D F a ≫ fst _ _ = fst _ _ := lift_fst _ _
    exact (comp_lift _ _ _).trans ((congrArg₂ lift e' e).trans lift_fst_snd)
  exact ⟨DegPre.trF D F (-χ), key _ _ (add_neg_cancel χ), key _ _ (neg_add_cancel χ)⟩

theorem exists_translate (χ : D.X) (s₀ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε 1))) :
    ∃ h : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval h r z J = sval s₀ (r ≫ (DegPre.trF D F χ).left) z J *
          (val (D.psi χ) (r ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J *
            val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
              (r ≫ (DegPre.BF D F).hom) z J).val := by
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have H : FormEq (Sum.elim (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i)
      (Sum.elim (fun _ : PUnit => κ.left ≫ ptK (D.c χ)) (fun _ : PUnit => (DegPre.BF D F).hom ≫ eSec D.P.A)))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) (DegPre.famφ D F χ) (DegPre.famε 1) := by
    intro U _ h
    have e₁ : (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i) =
        ![(snd (TF (R := R) F) D.P.A * cT D _ χ).left, (snd (TF (R := R) F) D.P.A * cT D _ χ).left,
          (1 : DegPre.BF D F ⟶ D.P.A).left, (1 : DegPre.BF D F ⟶ D.P.A).left] := by
      funext i
      refine (comp_famφT D (DegPre.trF D F χ) 0 i).trans ?_
      rw [cT_zero, _root_.mul_one,
        show DegPre.trF D F χ ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ χ from lift_snd _ _]
    have e₂ : κ.left ≫ ptK (D.c χ) = (cT D (DegPre.BF D F) χ).left :=
      congrArg (fun q => q.left) (show κ ≫ cT D _ χ = cT D _ χ by rw [← Category.assoc, comp_toUnit])
    have e₃ : (DegPre.BF D F).hom ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left := rfl
    rw [e₁, e₂, e₃, show DegPre.famφ D F χ = _ from famφT_eq D (TF (R := R) F) χ, Fintype.prod_sum_type,
      Fintype.prod_sum_type]
    simp [Fin.prod_univ_four, DegPre.famε, _root_.mul_assoc]
  obtain ⟨h, hh⟩ := exists_sec D.P.isLB H (pullMulSec s₀ (DegPre.trF D F χ).left
    (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi χ) κ.left)
      (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (DegPre.BF D F).hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) _) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)))
  refine ⟨h, fun Z r z J hJ => (hh Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)⟩
  exact congrArg (fun u : (Z.presheaf.stalk z)ˣ => sval s₀ (r ≫ (DegPre.trF D F χ).left) z J * u.val)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)))

def constVal {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) : F →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem constVal_eq {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    constVal p z c = gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := (gs_eq p z ⊤ trivial _).symm

theorem exists_ratio (h₁ : Laws) (h₂ : Laws2) (χ : D.X)
    (s t : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1))) (hs : ∃ j, s.f j ≠ 0) (ht : ∃ j, t.f j ≠ 0) :
    ∃ a : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z a.val * sval t r z J := by
  obtain ⟨b, hb⟩ := exists_basis_twist_field h₁ h₂ R D F 1 le_rfl χ
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have key : ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)), (∃ j, s.f j ≠ 0) →
      ∃ c : F, c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z c * sval (b i₀) r z J := by
    rintro s ⟨j, hj⟩
    obtain ⟨c, hc, -⟩ := hb s
    have hc' : ∀ j, s.f j = DegPre.constBF D F (c i₀) _ * (b i₀).f j := fun j =>
      (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨c i₀, fun h0 => hj ?_, fun Z r z J hJ => ?_⟩
    · rw [hc', h0, DegPre.constBF, map_zero, map_zero, map_zero, zero_mul]
    · rw [constVal_eq]
      exact (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl))
  obtain ⟨c, hc0, hc⟩ := key s hs
  obtain ⟨d, hd0, hd⟩ := key t ht
  refine ⟨Units.mk0 (c / d) (div_ne_zero hc0 hd0), fun Z r z J hJ => ?_⟩
  rw [hc Z r z J hJ, hd Z r z J hJ, ← _root_.mul_assoc, ← map_mul, Units.val_mk0, div_mul_cancel₀ c hd0]

theorem exists_psi_of_section (h₁ : Laws) (h₂ : Laws2) (i : (TK R).left ⟶ Spec (CommRingCat.of F))
    (hi : i ≫ jFK (R := R) F = 𝟙 _) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (hf : ∀ α, ∃ j, (f α).f j ≠ 0) :
    ∃ ψ : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)),
      (∀ χ, (ψ χ).IsGen) ∧ ∀ (χ : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ 𝟙_ _) (κ : T ⟶ TK R)
        (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (f χ) (lift ρ y).left z J =
          (val (ψ χ) κ.left z J * rigV D z J).val * sval (f 0) (lift ρ (y * cT D T χ)).left z J := by
  obtain ⟨s, hs⟩ := exists_pullB D F (toUnit _) 1 f
  have hs0 := fun α => (pullB_ne_zero_iff R D F 1 f s hs α).2 (hf α)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  choose h hh using fun χ => exists_translate D F χ (s 0)
  have hh0 : ∀ χ, ∃ j, (h χ).f j ≠ 0 := fun χ => by
    obtain ⟨J, hJ⟩ := exists_good_pt (Z := (DegPre.BF D F).left) D.P.isLB (genericPoint _)
    have := isIso_trF D F χ
    have : IsIso (DegPre.trF D F χ).left := inferInstanceAs (IsIso ((Over.forget _).map (DegPre.trF D F χ)))
    rw [exists_ne_zero_iff_sval_ne_zero _ hJ, hh χ _ _ _ J hJ, Category.id_comp]
    exact mul_ne_zero (sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s 0) (hs0 0) _ _ _ J hJ) (Units.ne_zero _)
  choose a ha using fun χ => exists_ratio D F h₁ h₂ χ (s χ) (h χ) (hs0 χ) (hh0 χ)
  let u : D.X → Γ((TK R).left, ⊤)ˣ := fun χ => Units.map (i.app ⊤).hom.toMonoidHom (unitOn (a χ))
  refine ⟨fun χ => GlobalTheory.UU.scaleGen (u χ) (D.psi χ), fun χ => GlobalTheory.UU.scaleGen_isGen _ (D.psi_gen χ), ?_⟩
  intro χ T ρ κ y z J hJ
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by rw [Category.assoc, hi, Category.comp_id]
  let κ' : T ⟶ TF (R := R) F := Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ)))
  have hρ : κ' ≫ toUnit _ = ρ := toUnit_unique _ _
  have v₁ := pullB_values R D _ _ _ 1 f s hs χ T κ' y z J hJ
  have v₂ := pullB_values R D _ _ _ 1 f s hs 0 T κ' (y * cT D T χ) z J hJ
  rw [hρ] at v₁ v₂
  have a₁ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left = κ.left ≫ i :=
    congrArg (fun q => q.left) (lift_fst κ' y)
  have a₂ : (lift κ' y).left ≫ (DegPre.trF D F χ).left = (lift κ' (y * cT D T χ)).left := by
    refine congrArg (fun q => q.left) (?_ : lift κ' y ≫ DegPre.trF D F χ = _)
    refine (comp_lift _ _ _).trans (congrArg₂ lift (lift_fst _ _) ?_)
    refine (MonObj.comp_mul (lift κ' y) (snd _ D.P.A) (cT D _ χ)).trans ?_
    rw [lift_snd, ← Category.assoc, comp_toUnit]
  have a₃ : (lift κ' y).left ≫ (DegPre.BF D F).hom = T.hom := Over.w _
  have a₄ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F = κ.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jFK (R := R) F) a₁).trans hκ)
  have w₁ := ha χ _ (lift κ' y).left z J hJ
  have w₂ := hh χ _ (lift κ' y).left z J hJ
  rw [a₂, a₃, a₄] at w₂
  rw [a₁] at w₁
  have w₃ := GlobalTheory.UU.val_scaleGen (u χ) (D.psi χ) κ.left hJ
  have w₄ : (gm κ.left z ⊤ (u χ)).val = constVal (κ.left ≫ i) z (a χ).val :=
    (gs_unit κ.left z ⊤ trivial _).symm.trans ((gs_pull κ.left i z ⊤ trivial _).trans (constVal_eq _ _ _).symm)
  have alg : ∀ (A : Type) [CommRing A] (x₁ x₂ s₁ s₂ t c : A) (p q u v : Aˣ), s₁ = x₁ → s₂ = x₂ → s₁ = c * t →
      t = s₂ * (p * q).val → v = u * p → u.val = c → x₁ = (v * q).val * x₂ := by
    intro A _ x₁ x₂ s₁ s₂ t c p q u v e₁ e₂ e₃ e₄ e₅ e₆
    rw [← e₁, ← e₂, e₃, e₄, e₅, ← e₆]
    simp only [Units.val_mul]
    ring
  exact alg _ _ _ _ _ _ _ _ _ _ _ v₁ v₂ w₁ w₂ w₃ w₄

end GlobalTheory.PsiExists

namespace GlobalTheory

theorem exists_psi_psiRel : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), (∀ α, ∃ j, (f α).f j ≠ 0) → ∃ ψ h, PsiRel (setPsi D ψ h) (𝟙_ _) f := by
  intro h₁ h₂ R _ _ D f hf
  obtain ⟨ψ, h, H⟩ := PsiExists.exists_psi_of_section D (FractionRing R) h₁ h₂ (𝟙 _)
    ((Category.id_comp _).trans (Spec.map_id _)) f hf
  exact ⟨ψ, h, H⟩

end GlobalTheory
end
