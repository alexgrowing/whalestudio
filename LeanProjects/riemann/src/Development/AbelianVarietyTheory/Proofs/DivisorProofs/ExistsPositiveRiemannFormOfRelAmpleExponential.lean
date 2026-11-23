import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreExponentialKernelFullLatticeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorImFormIntegralOnLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem im_dot_mulVec_star_zsmul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℤ) (v w : Fin g → ℂ) :
    ((c • v) ⬝ᵥ Hm *ᵥ star w).im = c * (v ⬝ᵥ Hm *ᵥ star w).im := by
  rw [smul_dotProduct, zsmul_eq_mul, Complex.mul_im]
  simp

theorem im_dot_mulVec_star_zsmul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℤ) (v w : Fin g → ℂ) :
    (v ⬝ᵥ Hm *ᵥ star (c • w)).im = c * (v ⬝ᵥ Hm *ᵥ star w).im := by
  rw [star_zsmul, Matrix.mulVec_smul, dotProduct_smul, zsmul_eq_mul, Complex.mul_im]
  simp

theorem exists_riemannForm_of_relAmple : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → Out.RelAmple G L → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (La : Type) [AddCommGroup La] (P : La →+ (Fin g → ℂ)), IsExp y e → Function.Injective P → (∀ z, e z = 1 ↔ z ∈ P.range) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ (∀ x x', (hermForm Hm (P x) (P x')).im = EF x x') ∧ (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  intro X G _ _ g hG hsm L hL hamp y e La _ P he hP hker
  obtain ⟨Λ, hd, hfull, hΛ⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice X G g hG hsm y e he
  obtain ⟨hadd, honto, hhol, -, -⟩ := he
  letI : GrpObj ((Over.pullback y).obj G) := Functor.grpObjObj
  haveI : IsCommMonObj ((Over.pullback y).obj G) := Functor.isCommMonObj_obj
  have hp : IsGrpPullback ((Over.pullback y).obj G) G y (pullback.fst G.hom y) := isGrpPullback_pullback G y
  have hLA : (L.pull (pullback.fst G.hom y)).IsLB := LB.isLB_pull hL _
  obtain ⟨hA, hampA, -⟩ := GlobalTheory.pol_pull X (Sp ℂ) G ((Over.pullback y).obj G) y (pullback.fst G.hom y) L
    (L.pull (pullback.fst G.hom y)) hL hLA hG hp (GlobalTheory.PolBaseChange.lbIso_refl hLA)
  let L₀ : LB G.left := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
  let u₀ : HolUnif ((Over.pullback y).obj G) (L₀.pull (pullback.fst G.hom y)) g :=
    GlobalTheory.OrthoMetric.fibreUnif hp (L := L₀) e Λ.toAddSubgroup (fun _ _ => 1) hadd honto hΛ hd hfull hhol
      (fun _ => differentiableOn_const _) (fun _ _ _ => one_ne_zero)
      (fun j j' z hz => by
        show (1 : ℂ) = valAt' (e z).left (⊤ ⊓ ⊤) (1 : Γ(G.left, ⊤ ⊓ ⊤)ˣ).val * 1
        rw [_root_.mul_one]
        exact (valAt'_one _ hz).symm)
  obtain ⟨u, Hm, χ, hex, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif _ hA _ g u₀ _ hLA
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple _ hA _ hLA (hampA hamp) g u Hm χ hF.1 hF.2.1 hF.2.2
  have hAH : u.IsAH Hm χ := GlobalTheory.TorusRM.isAH_of_isFactorAH hF hpos
  have huΛ : ∀ z, z ∈ u.Λ ↔ z ∈ P.range := fun z => by
    rw [← u.ker, hex]
    exact (u₀.ker z).trans ((hΛ z).symm.trans (hker z))
  have hmem : ∀ a, P a ∈ u.Λ := fun a => (huΛ _).2 ⟨a, rfl⟩
  choose N hN using fun a b => GlobalTheory.TorusRM.ahFactor_im_int g _ _ u Hm χ hLA hF (P a) (hmem a) (P b) (hmem b)
  let EF : LinearMap.BilinForm ℤ La := LinearMap.mk₂ ℤ N
    (fun a a' b => Int.cast_injective (α := ℝ) (by
      push_cast; rw [← hN, ← hN, ← hN, map_add, add_dotProduct, Complex.add_im]))
    (fun c a b => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hN, ← hN, map_zsmul]
      exact im_dot_mulVec_star_zsmul_left Hm c _ _))
    (fun a b b' => Int.cast_injective (α := ℝ) (by
      push_cast; rw [← hN, ← hN, ← hN, map_add, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im]))
    (fun c a b => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hN, ← hN, map_zsmul]
      exact im_dot_mulVec_star_zsmul_right Hm c _ _))
  have hEF : ∀ a b, EF a b = N a b := fun _ _ => rfl
  have tr : ∀ (t : Sp ℂ ⟶ X), (𝟙_ (Over (Sp ℂ))).hom ≫ y = t → ∀ (k : ℤ)
      (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G) (x₀ x₀' : Over.mk t ⟶ G) (c : Γ(Sp ℂ, ⊤)ˣ),
      x₀.left = x.left ≫ pullback.fst G.hom y → x₀'.left = x'.left ≫ pullback.fst G.hom y →
      Out.WeilIs _ (L.pull (pullback.fst G.hom y)) k x x' c → Out.WeilIs G L k x₀ x₀' c := by
    intro t ht
    subst ht
    intro k x x' x₀ x₀' c h1 h2 hw
    exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm X (Sp ℂ) G _ y _ L _ hL hLA hp
      (GlobalTheory.PolBaseChange.lbIso_refl hLA) (𝟙_ _) k x x' x₀ x₀' c h1 h2).1 hw
  have hexl : ∀ z, (e z).left = (u.ex z).left ≫ pullback.fst G.hom y := fun z => by
    rw [hex]
    exact (GlobalTheory.OrthoMetric.liftPt_comp hp (e z)).symm
  refine ⟨Hm, EF, hF.1, fun z hz => hpos z hz, fun x x' => (hN x x').trans (by rw [hEF]), ?_⟩
  intro k a b c hk hc
  have hw := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm _ hA _ hLA g u Hm χ hAH k (P a) (P b) c hk (hmem a) (hmem b)
    (by rw [hc, hN a b, hEF, Complex.ofReal_intCast])
  exact tr y (Category.id_comp y) k _ _ _ _ _ (hexl _) (hexl _) hw

end GlobalTheory
