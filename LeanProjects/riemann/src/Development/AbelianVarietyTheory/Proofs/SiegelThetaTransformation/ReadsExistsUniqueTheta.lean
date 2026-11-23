import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.VtFrRdA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.Dict

theorem isHolFam_fibrePoint {S : Scheme.{0}} (G : Over S) [GrpObj G] {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (ex : (Fin g → ℂ) → (Over.mk x0 ⟶ G)) (hol : IsHolTo Set.univ (fun z => (ex z).left)) :
    IsHolFam (fun z => (vtfQ G (ex z)).left) := by
  have hol' : IsHolFam (fun z => (ex z).left) := fun U f => by
    simpa only [Set.mem_univ, true_and] using hol U f
  have he : ∀ z, (ex z).left ≫ G.hom = x0 := fun z => Over.w (ex z)
  have h := isHolFam_vtfLift G.hom x0 (fun z => (ex z).left) he hol'
  let σ : pullback G.hom x0 ⟶ (Over.mk x0 ⊗ G).left := (pullbackSymmetry G.hom x0).hom
  have hσ : ∀ z, vtfLift G.hom x0 (fun z => (ex z).left) he z ≫ σ = (vtfQ G (ex z)).left := fun z => by
    refine vtf_pt_uniq G (ex z) _ ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullbackSymmetry_hom_comp_snd G.hom x0)).trans
        (pullback.lift_fst _ _ _))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullbackSymmetry_hom_comp_fst G.hom x0)).trans
        (pullback.lift_snd _ _ _))
  intro U f
  have h2 := h (σ ⁻¹ᵁ U) ((σ.app U).hom f)
  simp only [← hσ]
  exact ⟨h2.1, h2.2.congr fun z _ => (valAt'_comp _ σ U f).symm⟩

theorem hx_add_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (z a w : Fin g → ℂ) (t : ℂ) :
    hx X bas idx x (z + t • a) w = hx X bas idx x z w + t * hx X bas idx x a w := by
  simp only [hx, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem reads_existsUnique_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x))), (∃! θ, A.Reads k F θ) ∧ ∀ θ, A.Reads k F θ → Differentiable ℂ θ ∧ ∀ v ∈ L, (A.χ v)⁻¹ ^ k • fock X bas idx x k (pv X idx x v) θ = θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A _ _ _ k F
  have hcov : ∀ z, ∃ j, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    have hm : (A.ex z).left cpt ∈ (⨆ i, Xo.univ.t.PP.L.U i) := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨j, top_le_of_mem hj⟩
  have hrd : ∀ θ, A.Reads k F θ → ∀ j z, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' (vtfQ Xo.univ.t.G (A.ex z)).left
        ((LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x)).U (fun _ => j)) (F.f (fun _ => j)) =
      θ z * A.fr j z ^ (k : ℤ) := fun θ h j z hj =>
    h j z _ (vtfQ_snd _ _) (vtfQ_fst _ _) hj
  have hne : ∀ j z (m : ℤ), ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → A.fr j z ^ m ≠ 0 :=
    fun j z m hj => zpow_ne_zero m (A.fr_ne j z hj)
  refine ⟨?_, fun θ h => ⟨fun z => ?_, fun v hv => ?_⟩⟩
  · choose ch hch using hcov
    refine ⟨fun z => valAt' (vtfQ Xo.univ.t.G (A.ex z)).left
        ((LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x)).U (fun _ => ch z)) (F.f (fun _ => ch z)) /
        A.fr (ch z) z ^ (k : ℤ), ?_, fun θ h => ?_⟩
    · intro j z pt h1 h2 hj
      obtain rfl := vtf_pt_uniq Xo.univ.t.G (A.ex z) pt h1 h2
      exact vtf_read Xo.univ.t.G Xo.univ.t.PP.L F (A.ex z) (fun j => A.fr j z) (fun j j' => A.fr_g j j' z)
        (ch z) j (hch z) hj _ (div_mul_cancel₀ _ (hne _ _ _ (hch z))).symm
    · funext z
      rw [hrd θ h _ z (hch z), mul_div_cancel_right₀ _ (hne _ _ _ (hch z))]
  · obtain ⟨j, hj⟩ := hcov z
    have ho : IsOpen {w | ⊤ ≤ (A.ex w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      simpa only [Set.mem_univ, true_and] using (A.hol (Xo.univ.t.PP.L.U j) 0).1
    have hn := ho.mem_nhds hj
    have hd := (isHolFam_fibrePoint Xo.univ.t.G A.ex A.hol _ (F.f (fun _ => j))).2.mono
      (fun w (hw : w ∈ {w | ⊤ ≤ (A.ex w).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) =>
        vtf_chart Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (A.ex w) (fun _ => j) hw)
    have hq := (hd.differentiableAt hn).mul (((A.fr_hol j).differentiableAt hn).zpow (m := -(k : ℤ))
      (Or.inl (A.fr_ne j z hj)))
    refine hq.congr_of_eventuallyEq ?_
    filter_upwards [hn] with w hw
    have h1 := hrd θ h j w hw
    refine Eq.trans ?_ (congrArg (· * A.fr j w ^ (-(k : ℤ))) h1.symm)
    rw [_root_.zpow_neg, mul_inv_cancel_right₀ (hne _ _ _ hw)]
  · funext z
    obtain ⟨j, hj⟩ := hcov z
    have hex : A.ex (z + pv X idx x v) = A.ex z := by
      rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
    have hj' : ⊤ ≤ (A.ex (z + pv X idx x v)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
      rw [hex]; exact hj
    have h2 := hrd θ h j _ hj'
    rw [hex, hrd θ h j z hj, A.fr_per v hv j z hj, mul_zpow, ← _root_.mul_assoc] at h2
    have h3 := mul_right_cancel₀ (hne _ _ _ hj') h2
    have hχ : A.χ v ≠ 0 := fun h0 => by simpa [h0] using A.χ_norm v hv
    simp only [Pi.smul_apply, fock, smul_eq_mul]
    rw [← h3, hx_add_smul, zpow_natCast, mul_pow, ← Complex.exp_nat_mul]
    set a := hx X bas idx x z (pv X idx x v)
    set b := hx X bas idx x (pv X idx x v) (pv X idx x v)
    have h4 : cexp (-((k : ℂ) * Real.pi * (a + 1 / 2 * b))) * cexp (k * (Real.pi * a + Real.pi / 2 * b)) = 1 := by
      rw [← Complex.exp_add]
      refine Eq.trans (congrArg cexp ?_) Complex.exp_zero
      ring
    have h5 : (A.χ v)⁻¹ ^ k * A.χ v ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ hχ, one_pow]
    linear_combination (θ z * ((A.χ v)⁻¹ ^ k * A.χ v ^ k)) * h4 + θ z * h5

end GlobalTheory.Dict
