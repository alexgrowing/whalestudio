import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOneSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatDoubledPairSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsAtTauChart

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DerOneCH

open PositivityTheory.Rg.Sw.Glob.DerOneH

variable {D : D7} {n : ℕ} {V : HSp D} {θ : InfFam D} {τ : D.what₂.Tau}

theorem frame_lie {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool}
    {fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr) (hX : IsUe ε X) :
    fr * X * fr⁻¹ ∈ lieAt V τ := by
  obtain ⟨hd, hJ, -⟩ := hfr
  have hi : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hd
  have hiH : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hi, Matrix.conjTranspose_one]
  show (fr * X * fr⁻¹)ᴴ * gramAt D V τ + gramAt D V τ * (fr * X * fr⁻¹) = 0
  calc (fr * X * fr⁻¹)ᴴ * gramAt D V τ + gramAt D V τ * (fr * X * fr⁻¹)
      = (fr⁻¹)ᴴ * Xᴴ * frᴴ * gramAt D V τ * (fr * fr⁻¹) +
          ((fr⁻¹)ᴴ * frᴴ) * gramAt D V τ * (fr * X * fr⁻¹) := by
        rw [hi, hiH]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    _ = (fr⁻¹)ᴴ * (Xᴴ * Matrix.diagonal (sgn ε) + Matrix.diagonal (sgn ε) * X) * fr⁻¹ := by
        rw [← hJ]; simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem hhT_eq {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool}
    {fr X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr) (t : ℝ) :
    hhT θ V τ fr X t = oneP θ V τ (fr * X * fr⁻¹) t := by
  have hu : IsUnit fr := (Matrix.isUnit_iff_isUnit_det fr).2 hfr.1
  unfold hhT oneP
  congr 1
  have h1 : t • (fr * X * fr⁻¹) = fr * ((t : ℂ) • X) * fr⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Complex.coe_smul]
  rw [h1, Matrix.exp_conj _ _ hu]

theorem compAt_mul {r : ℕ} (τ' : D.what₂.Tau) (A : Matrix (Fin r) (Fin r) (AE D)) (z : Mx D r n) :
    compAt θ τ' (HMul.hMul A z) = HMul.hMul (compAt θ τ' A) (compAt θ τ' z) := by
  show Matrix.map (HMul.hMul A z) ⇑((θ τ').comp (infPart D)) =
    HMul.hMul (Matrix.map A ⇑((θ τ').comp (infPart D))) (Matrix.map z ⇑((θ τ').comp (infPart D)))
  exact Matrix.map_mul

theorem finPart_mul {r : ℕ} (A : Matrix (Fin r) (Fin r) (AE D)) (z : Mx D r n) :
    (HMul.hMul A z).map (finPart D) = HMul.hMul (A.map (finPart D)) (z.map (finPart D)) :=
  Matrix.map_mul

open Classical in
theorem comp_oneP (hθ : IsInfFam θ) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) (t : ℝ)
    (τ' : D.what₂.Tau) :
    compAt θ τ' (mt V (oneP θ V τ Y t)) = if τ' = τ then NormedSpace.exp (t • Y) else 1 := by
  have h := (GlobalTheory.RegSch.ChartDer.isAtTau_iff θ V τ _ _).1 (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t)
  split_ifs with e
  · subst e; exact h.1
  · exact h.2.1 τ' e

theorem fin_oneP (hθ : IsInfFam θ) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ) (t : ℝ) :
    (mt V (oneP θ V τ Y t)).map (finPart D) = 1 :=
  ((GlobalTheory.RegSch.ChartDer.isAtTau_iff θ V τ _ _).1 (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hY t)).2.2

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem diff_entry {m : ℕ} (Y : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    Differentiable ℝ fun u : ℝ => ((NormedSpace.exp (u • Y) : Matrix (Fin m) (Fin m) ℂ) * C) i j := by
  have : (fun u : ℝ => ((NormedSpace.exp (u • Y) : Matrix (Fin m) (Fin m) ℂ) * C) i j) =
      fun u => ∑ k, (NormedSpace.exp (u • Y) : Matrix (Fin m) (Fin m) ℂ) i k * C k j := by
    funext u; rfl
  rw [this]
  exact Differentiable.fun_sum fun k _ => fun u => ((GlobalTheory.Mem.Lift.hasDerivAt_exp_entry Y u i k).differentiableAt).mul_const _

end

theorem key (hθ : IsInfFam θ) {Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hY : Y ∈ lieAt V τ)
    (Φ : schwartzA θ V.rank n) :
    Continuous Φ.1 ∧ ∀ z : Mx D V.rank n, Differentiable ℝ fun u : ℝ => Φ.1 (HMul.hMul (mt V (oneP θ V τ Y u)) z) := by
  classical
  obtain ⟨φ, hφ⟩ := Φ
  refine Submodule.span_induction (p := fun φ _ => Continuous φ ∧ ∀ z : Mx D V.rank n,
      Differentiable ℝ fun u : ℝ => φ (HMul.hMul (mt V (oneP θ V τ Y u)) z)) ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨f, g, hg, rfl⟩
    have hC : Continuous fun x : Mx D V.rank n => fun τ i j => compAt θ τ x i j :=
      continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply j).comp ((continuous_apply i).comp (GlobalTheory.RealWeil.continuous_compAt hθ τ V.rank n))
    have hF : Continuous fun x : Mx D V.rank n => fun i j => finPart D (x i j) :=
      continuous_pi fun i => continuous_pi fun j =>
        GlobalTheory.SchwartzSch.continuous_finPart'.comp ((continuous_apply j).comp (continuous_apply i))
    refine ⟨(f.continuous.comp hC).mul (hg.1.continuous.comp hF), fun z => ?_⟩
    have e : (fun u : ℝ => (fun x : Mx D V.rank n => f (fun τ i j => compAt θ τ x i j) *
        g (fun i j => finPart D (x i j))) (HMul.hMul (mt V (oneP θ V τ Y u)) z)) =
        fun u => f (fun τ' i j => ((if τ' = τ then NormedSpace.exp (u • Y) else 1) * compAt θ τ' z) i j) *
          g (fun i j => finPart D (z i j)) := by
      funext u
      dsimp only
      have h1 : (fun τ' i j => compAt θ τ' (HMul.hMul (mt V (oneP θ V τ Y u)) z) i j) =
          fun τ' i j => ((if τ' = τ then NormedSpace.exp (u • Y) else 1) * compAt θ τ' z) i j := by
        funext τ' i j; rw [compAt_mul, comp_oneP hθ hY]
      have h2 : (fun i j => finPart D ((HMul.hMul (mt V (oneP θ V τ Y u)) z : Mx D V.rank n) i j)) =
          fun i j => finPart D (z i j) := by
        have h := finPart_mul (mt V (oneP θ V τ Y u)) z
        rw [fin_oneP hθ hY, Matrix.one_mul] at h
        funext i j; exact congrFun (congrFun h i) j
      rw [h1, h2]
    rw [e]
    refine Differentiable.mul_const (f.differentiable.comp ?_) _
    refine differentiable_pi.2 fun τ' => differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
    by_cases h : τ' = τ
    · simp only [h, if_true]
      exact diff_entry Y (compAt θ τ z) i j
    · simp only [h, if_false, Matrix.one_mul]
      exact differentiable_const _
  · exact ⟨continuous_const, fun z => by simpa using differentiable_const (0 : ℂ)⟩
  · rintro x y - - ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨h1.add h3, fun z => (h2 z).add (h4 z)⟩
  · rintro a x - ⟨h1, h2⟩
    exact ⟨continuous_const.mul h1, fun z => (h2 z).const_mul a⟩

end PositivityTheory.Rg.Sw.Glob.DerOneCH

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.DerOneH PositivityTheory.Rg.Sw.Glob.DerOneCH

theorem curveSt : CurveSt := by
  intro D n V θ τ s ε fr X hθ hs hfr hX
  have hY := frame_lie hfr hX
  have hh : ∀ t, hhT θ V τ fr X t = oneP θ V τ (fr * X * fr⁻¹) t := hhT_eq hfr
  have hadd : ∀ a b, hhT θ V τ fr X (a + b) = hhT θ V τ fr X a * hhT θ V τ fr X b := fun a b => by
    simp only [hh]; exact GlobalTheory.Mem.Lift.oneP_add hθ hY a b
  refine ⟨by rw [hh]; exact GlobalTheory.Mem.Lift.oneP_zero hθ, hadd, fun Φ => ⟨fun y => ?_, fun z t => ?_⟩⟩
  · have hc : Continuous fun p : GA D V × ℝ => HMul.hMul (mt V (hhT θ V τ fr X p.2)) (HMul.hMul (mt V p.1⁻¹) y) := by
      simp only [hh]
      exact ((GlobalTheory.RealWeil.continuous_mt V).1.comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ hY).comp continuous_snd)).matrix_mul
        (((GlobalTheory.RealWeil.continuous_mt V).2.comp continuous_fst).matrix_mul continuous_const)
    exact (key hθ hY Φ).1.comp hc
  · set w := HMul.hMul (mt V (hhT θ V τ fr X t)) z with hw
    have hdiff : DifferentiableAt ℝ (fun v : ℝ => Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X v)) w)) 0 := by
      simp only [hh]; exact (key hθ hY Φ).2 w 0
    have hd0 : HasDerivAt (fun v : ℝ => Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X v)) w))
        (DX θ V τ fr X Φ.1 w) 0 := hdiff.hasDerivAt
    have h1 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd0)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X u)) z) = Φ.1 (HMul.hMul (mt V (hhT θ V τ fr X (u - t))) w)
    rw [hw, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.mt_mul V, ← hadd, sub_add_cancel]

end PositivityTheory.Rg.Sw.Glob
