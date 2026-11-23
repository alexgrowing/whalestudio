import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenLiftOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BiLift

section Gen
variable {X Y Y₀ : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_val_lift (hL : L.IsLB) (f : Y₀ ⟶ Y) [IsClosedImmersion f] [Surjective f] [IsAffine Y]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t₀ : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε)) (ht₀ : t₀.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₀) (z : Z) (J), Good L z J → val t (r ≫ f) z J = val t₀ r z J := by
  have le : ∀ j : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull f).U j ≤ LB.wchart L (fun k => f ≫ φ k) (j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k
  let c : LB.Gen ((LB.LinComb L φ ε).pull f) := ⟨fun j => res (le j) (t₀.s (j PUnit.unit))⟩
  have hc : c.IsGen := isGen_of_gm (M := LB.LinComb L φ ε) c fun y j j' hj hj' => by
    refine (gm_res _ y _ hj _).trans ((gen_trans ht₀ (𝟙 Y₀) y (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) ?_ (gm_res _ y _ hj' _).symm))
    unfold trF
    symm
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_linComb L φ ε (𝟙 Y₀ ≫ f) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans ?_
    simp only [Category.assoc]
  obtain ⟨t, ht, e⟩ := GenLift.exists_genPull_eq f (LB.isLB_linComb hL φ ε) c hc
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  rw [val_of t (r ≫ f) z J (fun k => J (r ≫ f ≫ φ k)) (fun k => by rw [Category.assoc])]
  have hm := hJ.mem (fun k => f ≫ φ k) r
  have hm' : r z ∈ ((LB.LinComb L φ ε).pull f).U (fun _ k => J (r ≫ f ≫ φ k)) :=
    mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k)
  have e' := congrArg (fun q : LB.Gen ((LB.LinComb L φ ε).pull f) => gm r z _ (q.s fun _ k => J (r ≫ f ≫ φ k))) e
  refine Eq.trans ?_ (e'.trans (gm_res r z _ hm' _))
  exact ((gm_res r z _ hm' _).trans (gm_pull r f z _ (mem_pull.1 hm') _)).symm

theorem unit_eq_one {u : Γ(Y, ⊤)ˣ}
    (h : ∀ y : Y, ∃ (W : Y.Opens) (hy : y ∈ W), gm W.ι (⟨y, hy⟩ : W.toScheme) ⊤ u = 1) : u = 1 :=
  unit_ext fun y _ => by
    obtain ⟨W, hy, e⟩ := h y
    exact gm_inj W.ι (⟨y, hy⟩ : W.toScheme) (U := ⊤) (U' := ⊤) trivial trivial (e.trans (map_one _).symm)

end Gen

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

def lam {Y : Over S} (a x : Y ⟶ G) : Fin 4 → (Y.left ⟶ G.left) := ![(a * x).left, a.left, x.left, (1 : Y ⟶ G).left]

theorem comp_lam {Y Z : Over S} (r : Z ⟶ Y) (a x : Y ⟶ G) (k : Fin 4) : r.left ≫ lam a x k = lam (r ≫ a) (r ≫ x) k := by
  fin_cases k
  · exact congrArg (·.left) (MonObj.comp_mul r a x)
  · rfl
  · rfl
  · exact congrArg (·.left) (MonObj.comp_one (M := G) r)

theorem prod_lam {Y : Over S} (a x : Y ⟶ G) {U : Type} [CommGroup U] (h : (Y.left ⟶ G.left) → U) :
    ∏ k, h (lam a x k) ^ Oε k = h (a * x).left * (h a.left)⁻¹ * (h x.left)⁻¹ * h (1 : Y ⟶ G).left := by
  simp [Fin.prod_univ_four, lam, Oε]

theorem exists_pull_lam {Y Z : Over S} (r : Z ⟶ Y) {a x : Y ⟶ G} {a' x' : Z ⟶ G} (ha : r ≫ a = a') (hx : r ≫ x = x')
    (s : LB.Gen (LB.LinComb L.L (lam a x) Oε)) (hs : s.IsGen) :
    ∃ s' : LB.Gen (LB.LinComb L.L (lam a' x') Oε), s'.IsGen ∧
      ∀ (W : Scheme.{0}) (q : W ⟶ Z.left) (z : W) (J), Good L.L z J → val s' q z J = val s (q ≫ r.left) z J := by
  subst ha hx
  obtain ⟨s', hs', e⟩ := exists_gen L.isLB (φ' := lam (r ≫ a) (r ≫ x)) (ε' := Oε)
    (fun U _ h => by simp only [comp_lam]) (LB.pullGen L.L _ _ s r.left) (DVR.pullGen_isGen _ _ _ _ hs _)
  exact ⟨s', hs', fun W q z J hJ => (e W q z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_defect {Y : Over S} (a b x : Y ⟶ G) {φ₁ φ₂ φ₃ : Fin 4 → (Y.left ⟶ G.left)}
    (h₁ : FormEq φ₁ Oε (lam (a * b) x) Oε) (h₂ : FormEq φ₂ Oε (lam a x) Oε) (h₃ : FormEq φ₃ Oε (lam b x) Oε)
    (s₁ : LB.Gen (LB.LinComb L.L φ₁ Oε)) (s₂ : LB.Gen (LB.LinComb L.L φ₂ Oε)) (s₃ : LB.Gen (LB.LinComb L.L φ₃ Oε))
    (g₁ : s₁.IsGen) (g₂ : s₂.IsGen) (g₃ : s₃.IsGen) :
    ∃ f : Γ(Y.left, ⊤)ˣ, ∀ (Z : Over S) (r : Z ⟶ Y) (z : Z.left) (J), Good L.L z J →
      val s₁ r.left z J = gm r.left z ⊤ f * (cubV c z J (r ≫ a) (r ≫ b) (r ≫ x) * val s₂ r.left z J * val s₃ r.left z J) := by
  obtain ⟨f, hf⟩ := TorusCoord.exists_ratio L.isLB (fun U _ h => by
      refine Eq.trans ?_ (DVR.prod_sum₂ (K := thK ⊕ Fin 4) (K' := Fin 4) (U := U) _
        (DVR.prod_sum₂ (K := thK) (K' := Fin 4) (U := U) _ (prod_cub a b x h) ((h₂ U h).trans (prod_lam a x h)))
        ((h₃ U h).trans (prod_lam b x h))).symm
      rw [h₁ U h, prod_lam]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) s₁ g₁
    (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift b x)).left) s₂) s₃)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) g₂) g₃)
  refine ⟨f, fun Z r z J hJ => (hf _ r.left z J hJ).trans (congrArg _ ?_)⟩
  exact (val_mul hJ _ _ _).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_cub c r hJ _ _ _))))

omit [GrpObj G] [IsCommMonObj G] in
theorem formEq_refl {Y : Over S} (φ : Fin 4 → (Y.left ⟶ G.left)) : FormEq φ Oε φ Oε := fun _ _ _ => rfl

theorem formEq_symm {Y : Over S} (a x : Y ⟶ G) : FormEq (lam a x) Oε (lam x a) Oε := fun U _ h => by
  rw [prod_lam, prod_lam, mul_comm x a, mul_right_comm (h _) (h a.left)⁻¹]

variable {H Y : Over S} [GrpObj H] {i : H ⟶ G} [IsMonHom i] {x : Y ⟶ G}

theorem exists_defect₁ (s : LB.Gen (LB.LinComb L.L (lam (fst H Y ≫ i) (snd H Y ≫ x)) Oε)) (hs : s.IsGen) :
    ∃ f : Γ((H ⊗ H ⊗ Y).left, ⊤)ˣ, ∀ (Z : Over S) (t t' : Z ⟶ H) (y : Z ⟶ Y) (z : Z.left) (J), Good L.L z J →
      val s (lift (t * t') y).left z J = gm (lift t (lift t' y)).left z ⊤ f *
        (cubV c z J (t ≫ i) (t' ≫ i) (y ≫ x) * val s (lift t y).left z J * val s (lift t' y).left z J) := by
  let p : H ⊗ H ⊗ Y ⟶ H := fst _ _
  let p' : H ⊗ H ⊗ Y ⟶ H := snd _ _ ≫ fst _ _
  let q : H ⊗ H ⊗ Y ⟶ Y := snd _ _ ≫ snd _ _
  obtain ⟨s₁, g₁, e₁⟩ := exists_pull_lam (lift (p * p') q) (a' := p ≫ i * p' ≫ i) (x' := q ≫ x)
    (by rw [lift_fst_assoc, MonObj.mul_comp]) (lift_snd_assoc _ _ _) s hs
  obtain ⟨s₂, g₂, e₂⟩ := exists_pull_lam (lift p q) (lift_fst_assoc _ _ _) (lift_snd_assoc _ _ _) s hs
  obtain ⟨s₃, g₃, e₃⟩ := exists_pull_lam (lift p' q) (lift_fst_assoc _ _ _) (lift_snd_assoc _ _ _) s hs
  obtain ⟨f, hf⟩ := exists_defect c _ _ _ (formEq_refl _) (formEq_refl _) (formEq_refl _) s₁ s₂ s₃ g₁ g₂ g₃
  refine ⟨f, fun Z t t' y z J hJ => ?_⟩
  have e := hf Z (lift t (lift t' y)) z J hJ
  rw [e₁ _ _ z J hJ, e₂ _ _ z J hJ, e₃ _ _ z J hJ] at e
  simpa only [← Over.comp_left, comp_lift, MonObj.comp_mul, p, p', q, lift_fst, lift_snd, lift_fst_assoc,
    lift_snd_assoc, Category.assoc] using e

omit [IsMonHom i] [GrpObj H] in

theorem exists_defect₂ (s : LB.Gen (LB.LinComb L.L (lam (fst H G ≫ i) (snd H G)) Oε)) (hs : s.IsGen) :
    ∃ f : Γ((H ⊗ G ⊗ G).left, ⊤)ˣ, ∀ (Z : Over S) (t : Z ⟶ H) (y : Z ⟶ G ⊗ G) (z : Z.left) (J), Good L.L z J →
      val s (lift t (y ≫ fst _ _ * y ≫ snd _ _)).left z J = gm (lift t y).left z ⊤ f *
        (cubV c z J (t ≫ i) (y ≫ fst _ _) (y ≫ snd _ _) * val s (lift t (y ≫ fst _ _)).left z J *
          val s (lift t (y ≫ snd _ _)).left z J) := by
  let p : H ⊗ G ⊗ G ⟶ H := fst _ _
  let q : H ⊗ G ⊗ G ⟶ G := snd _ _ ≫ fst _ _
  let q' : H ⊗ G ⊗ G ⟶ G := snd _ _ ≫ snd _ _
  obtain ⟨s₁, g₁, e₁⟩ := exists_pull_lam (lift p (q * q')) (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨s₂, g₂, e₂⟩ := exists_pull_lam (lift p q) (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨s₃, g₃, e₃⟩ := exists_pull_lam (lift p q') (lift_fst_assoc _ _ _) (lift_snd _ _) s hs
  obtain ⟨f, hf⟩ := exists_defect c _ _ _ (formEq_symm _ _) (formEq_symm _ _) (formEq_symm _ _) s₁ s₂ s₃ g₁ g₂ g₃
  refine ⟨f, fun Z t y z J hJ => ?_⟩
  have e := hf Z (lift t y) z J hJ
  rw [e₁ _ _ z J hJ, e₂ _ _ z J hJ, e₃ _ _ z J hJ, (isCub_cubV c hJ).s12, (isCub_cubV c hJ).s01] at e
  simpa only [← Over.comp_left, comp_lift, MonObj.comp_mul, p, q, q', lift_fst, lift_snd, lift_fst_assoc,
    lift_snd_assoc, Category.assoc] using e

end GlobalTheory.UU.BiLift
end
