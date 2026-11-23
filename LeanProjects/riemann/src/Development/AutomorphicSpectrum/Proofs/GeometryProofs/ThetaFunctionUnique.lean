import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionsFiniteDimStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnifStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

variable {X Y : Scheme.{0}}

theorem valF_eq_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valF x U f = valAt' x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · rw [valF, dif_pos h, valAt', dif_pos h, valAt]
  · rw [valF, dif_neg h, valAt', dif_neg h]

theorem top_le_wchart {K : Type} [Fintype K] (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (i : L.ι)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U i) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : K => φ) (fun _ => i) :=
  fun p hp => Set.mem_iInter.2 fun _ => by
    have := h hp
    simpa using this

theorem valAt'_g_const {K : Type} [Fintype K] [Unique K] (L : LB X) (φ : Y ⟶ X) (e : ℤ) (x : Sp ℂ ⟶ Y) (i i' : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))) :
    valAt' x _ ((LB.LinComb L (K := K) (fun _ => φ) (fun _ => e)).g (fun _ => i) (fun _ => i')).val =
      valAt' (x ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val ^ e := by
  have hle : LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i') ≤
      φ ⁻¹ᵁ (L.U i ⊓ L.U i') :=
    le_inf (inf_le_left.trans (LB.wchart_le L _ _ default)) (inf_le_right.trans (LB.wchart_le L _ _ default))
  have key : ((LB.LinComb L (K := K) (fun _ => φ) (fun _ => e)).g (fun _ => i) (fun _ => i') :
      Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ) =
      (res hle (pullU φ _ (L.g i i'))) ^ e :=
    Fintype.prod_unique (M := Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ) _
  refine (congrArg (fun u : Γ(Y, LB.wchart L (fun _ : K => φ) (fun _ => i) ⊓
    LB.wchart L (fun _ : K => φ) (fun _ => i'))ˣ => valAt' x _ u.val) key).trans ?_
  refine (valAt'_units_zpow x h _ e).trans ?_
  congr 1
  exact (valAt'_map x _ _ h).trans (valAt'_comp x φ _ _)

end GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameFn
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ}

theorem exists_chart_pt (a : ArchFrame P z g) (w : Fin g → ℂ) : ∃ i, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i := by
  have h : a.pt w (default : PrimeSpectrum ℂ) ∈ (⨆ i, P.L.U i : G.left.Opens) := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 h
  exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩

theorem top_le_frame (a : ArchFrame P z g) (w : Fin g → ℂ) (i : P.L.ι) (h : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) :
    ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (P.L.pull a.φ).U (fun _ => i) :=
  top_le_wchart (K := PUnit) P.L a.φ (a.u.ex w).left i h

theorem top_le_sec (a : ArchFrame P z g) (n : ℕ) (w : Fin g → ℂ) (i : P.L.ι) (h : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) :
    ⊤ ≤ a.pt w ⁻¹ᵁ (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => i) :=
  top_le_wchart (K := Fin 1) P.L (𝟙 G.left) (a.pt w) i (by simpa using h)

theorem fr_change (a : ArchFrame P z g) (w : Fin g → ℂ) (i j : P.L.ι) (hi : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i)
    (hj : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U j) :
    a.u.fr (fun _ => i) w = valAt' (a.pt w) (P.L.U i ⊓ P.L.U j) (P.L.g i j).val * a.u.fr (fun _ => j) w := by
  have h : ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ ((P.L.pull a.φ).U (fun _ => i) ⊓ (P.L.pull a.φ).U (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨top_le_frame a w i hi, top_le_frame a w j hj⟩
  refine (a.u.fr_compat _ _ w h).trans ?_
  have := valAt'_g_const (K := PUnit) P.L a.φ 1 (a.u.ex w).left i j h
  rw [zpow_one] at this
  exact congrArg (· * a.u.fr (fun _ => j) w) this

theorem sec_change (a : ArchFrame P z g) {n : ℕ} (s : Out.H0 P.L n) (w : Fin g → ℂ) (i j : P.L.ι)
    (hi : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i) (hj : ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U j) :
    valF (a.pt w) _ (s.f fun _ => i) =
      valAt' (a.pt w) (P.L.U i ⊓ P.L.U j) (P.L.g i j).val ^ n * valF (a.pt w) _ (s.f fun _ => j) := by
  have h : ⊤ ≤ a.pt w ⁻¹ᵁ ((LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => i) ⊓
      (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (n : ℤ))).U (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨top_le_sec a n w i hi, top_le_sec a n w j hj⟩
  have e := congrArg (valAt' (a.pt w) _) (s.compat (fun _ => i) (fun _ => j))
  rw [valAt'_mul, valAt'_map _ _ _ h, valAt'_map _ _ _ h] at e
  have t := valAt'_g_const (K := Fin 1) P.L (𝟙 G.left) (n : ℤ) (a.pt w) i j h
  rw [Category.comp_id, zpow_natCast] at t
  rw [valF_eq_valAt', valF_eq_valAt', e, t]

theorem unique_fn (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) : ∃! θ, a.IsFn s θ := by
  choose c hc using exists_chart_pt a
  have hne : ∀ w i, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i → a.u.fr (fun _ => i) w ≠ 0 :=
    fun w i h => a.u.fr_ne _ w (top_le_frame a w i h)
  refine ⟨fun w => valF (a.pt w) _ (s.f fun _ => c w) / a.u.fr (fun _ => c w) w ^ n, ?_, ?_⟩
  · intro i w hi
    have h1 := fr_change a w i (c w) hi (hc w)
    have h2 := sec_change a s w i (c w) hi (hc w)
    have n1 := hne w (c w) (hc w)
    show _ = _ / _ * _
    rw [h2, h1, mul_pow]
    field_simp
  · intro θ hθ
    funext w
    have := hθ (c w) w (hc w)
    rw [this, mul_div_assoc, div_self (pow_ne_zero _ (hne w _ (hc w))), _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Sl.FrameFn

theorem GlobalTheory.CompanionTheory.Ar.Sl.frame_fn_existsUnique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n), ∃! θ, a.IsFn s θ :=
  by
  intro S G _ _ P z g a n s
  exact GlobalTheory.CompanionTheory.Ar.Sl.FrameFn.unique_fn a n s
