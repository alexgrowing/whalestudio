import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactUnitPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTranslationSectionSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodChartTranslationLiftStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsHolToPrecomp
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat om0)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm (IsRegVar hermMat eval₂ bas relCot dRel IsRelAcyclic)
open GlobalTheory GlobalTheory.TorsionForm
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.RelCotAb

theorem resM_frame {S : Scheme.{0}} (A : Over S) [GrpObj A] [QuasiSeparated A.hom] {g : ℕ}
    (hE : GlobalTheory.VB.IsVB (omega A) g) (c₀ : GlobalTheory.VB.Chart (omega A) g) (W₁ : A.left.Opens)
    (hU : c₀.U ≤ unitSec A ⁻¹ᵁ W₁) (h : Fin g → Γ(A.left, W₁)) (hh : ∀ a, c₀.e a = dUnit A hU (h a))
    {T : A.left.Opens} (hT : T ≤ A.hom ⁻¹ᵁ c₀.U)
    (hW' : T ≤ Limits.pullback.diagonal A.hom ⁻¹ᵁ (divMap A ⁻¹ᵁ W₁)) (a : Fin g) :
    GlobalTheory.Twist.resM (relCot A.hom) hT (((c₀.pull hE A.hom).map (relCotIso A)).e a) =
      GlobalTheory.Conormal.d (Limits.pullback.diagonal_fst A.hom) hW' ((divMap A).app W₁ (h a)) := by
  rw [Scheme.Hom.app_eq_appLE, ← relCotIso_hom_d A hU hT hW' le_rfl, ← hh a]
  refine (GlobalTheory.Twist.app_resM (relCotIso A).hom hT _).symm.trans (congrArg _ ?_)
  exact QCoh.res_pullbackSections A.hom (omega A) le_rfl hT _

theorem diagonal_divMap {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    Limits.pullback.diagonal A.hom ≫ divMap A = A.hom ≫ unitSec A := by
  rw [← unitPair_snd A, ← diag_shear_left A]
  exact (Category.assoc _ _ _).symm

theorem cot_mulVec_crd : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) (D : ℕ) (A : Over S) [GrpObj A]
    [QuasiSeparated A.hom] (g : ℕ) (w : VMetric p (omega A) g) (σ : k →+* ℂ) (c : AlgChart p σ D)
    (τ : V D → Matrix (Fin g) (Fin g) ℂ) (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ), IsPeriodChart w c τ ex →
    ∀ (v : V D) (z : Fin g → ℂ), v ∈ c.e.target → ∀ (c₀ : GlobalTheory.VB.Chart (omega A) g) (W₁ : A.left.Opens)
      (hU : c₀.U ≤ unitSec A ⁻¹ᵁ W₁) (h : Fin g → Γ(A.left, W₁)), (∀ a, c₀.e a = dUnit A hU (h a)) →
      c.e.symm v ∈ ptsIn p σ c₀.U → ∀ (W : A.left.Opens) (F : Γ(A.left, W)), ex (v, z) ∈ ptsIn _ σ W →
      (Matrix.of fun i a => cot ex W₁ (h a) v i) *ᵥ
          ((c₀.pull w.isVB A.hom).map (GlobalTheory.RelCotAb.relCotIso A)).crd _ σ (dRel A.hom W F) (ex (v, z)) =
        cotAt ex W F (v, z) := by
  intro k _ S p D A _ _ g w σ c τ ex H v z hv c₀ W₁ hU h hh hc W F hW
  have h₁ := (H.2.2 v hv).1
  let c₁ := (c₀.pull w.isVB A.hom).map (relCotIso A)
  have hT : W ⊓ c₁.U ≤ A.hom ⁻¹ᵁ c₀.U := inf_le_right
  have hx : ex (v, z) ∈ ptsIn (A.hom ≫ p) σ (W ⊓ c₁.U) := by
    refine mem_ptsIn_inf.2 ⟨hW, ?_⟩
    change ⊤ ≤ ((ex (v, z)).1 ≫ A.hom) ⁻¹ᵁ c₀.U
    rw [h₁ z]
    exact hc
  have hW' : W ⊓ c₁.U ≤ Limits.pullback.diagonal A.hom ⁻¹ᵁ (divMap A ⁻¹ᵁ W₁) :=
    (Conormal.le_preimage_of_comp (diagonal_divMap A)).2 (hT.trans (A.hom.preimage_mono hU))
  have hol : IsHolTo Set.univ (fun u : Fin g → ℂ => (ex (v, z + u)).1) :=
    FrameHol.isHolTo_precomp H.2.1 isOpen_univ (β := fun u : Fin g → ℂ => (v, z + u)) (by fun_prop)
      fun _ _ => ⟨hv, trivial⟩
  have hs : GlobalTheory.Twist.resM (relCot A.hom) (inf_le_left : W ⊓ c₁.U ≤ W) (dRel A.hom W F) =
      ∑ a, (c₁.isFrame.basis inf_le_right).repr
          (GlobalTheory.Twist.resM (relCot A.hom) (inf_le_left : W ⊓ c₁.U ≤ W) (dRel A.hom W F)) a •
        GlobalTheory.Conormal.d (Limits.pullback.diagonal_fst A.hom) hW' ((divMap A).app W₁ (h a)) := by
    refine ((c₁.isFrame.basis inf_le_right).sum_repr _).symm.trans (Finset.sum_congr rfl fun a _ => ?_)
    rw [VB.IsFrame.basis_apply]
    exact congrArg _ (resM_frame A w.isVB c₀ W₁ hU h hh hT hW' a)
  have e := GlobalTheory.T.holomorphic_translation_section_sum A g (fun u => ex (v, z + u)) (fun u => (h₁ _).trans (h₁ _).symm) hol W _ inf_le_left F
    (by simpa only [add_zero] using hx) g _ _ (fun _ => hW') _ hs
  have sh (z' : Fin g → ℂ) (e : z' = z) (u : Fin g → ℂ)
      (hz : (ex (v, z')).1 ≫ A.hom = (ex (v, z + u)).1 ≫ A.hom) (a : Fin g) :
      ev _ σ (divMap A ⁻¹ᵁ W₁) ((divMap A).app W₁ (h a)) (pairPt A (ex (v, z')) (ex (v, z + u)) hz) =
        ev (A.hom ≫ p) σ W₁ (h a) (ex (v, u)) := by
    subst e
    exact GlobalTheory.T.period_chart_translation_lift k S p D A g w σ c τ ex H v hv _ u hz W₁ (h a)
  simp only [sh (z + 0) (add_zero z)] at e
  rw [fderiv_comp_add_left (f := fun u => ev (A.hom ≫ p) σ W F (ex (v, u)))] at e
  simp only [add_zero] at e
  funext i
  rw [cotAt]
  simp only [e, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, mulVec, dotProduct,
    of_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end GlobalTheory.RelCotAb
