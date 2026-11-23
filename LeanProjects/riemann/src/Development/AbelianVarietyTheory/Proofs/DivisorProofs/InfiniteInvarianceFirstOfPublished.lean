import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartUnfoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartFoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarStabilizerTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartEqualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalPartProductStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.LemF

theorem infInvA_holds : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.InfInvA := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he ei ev hle K hK X om om' om₁ om₁' hT hT₁ μK μ hμK hμ l hl₀
  have t1 := GlobalTheory.T.config_A_local_part_theta hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  have t2 := GlobalTheory.T.config_A_local_part_integral hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  have t3 := GlobalTheory.T.config_A_local_part_unfold hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  have t4 := GlobalTheory.T.config_A_local_part_fold hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  have t5 := GlobalTheory.T.config_A_local_part_compare hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  have t7 := GlobalTheory.T.config_A_local_part_equal hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁ K hK μK μ hμK hμ l
  have t9 := GlobalTheory.T.config_A_local_part_product hP F E σ B b a' G G₁ H H' hC e he ei ev hle X om om' om₁ om₁' hT hT₁
  refine ⟨fun u hu huI f => by rw [t1 u hu huI f], fun g₀ g hL hg hg₀ f => by rw [t2 g₀ g hL hg hg₀ f]; exact hl₀ g₀ hg₀ _, ?_⟩
  intro g hg f
  obtain ⟨m, hm⟩ := GlobalTheory.T.levi_section_archimedean F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo
  have hfix : ∀ x : UA σ G.V.J, mat x *ᵥ incV F H.x = incV F H.x →
      actAB (cA σ) ((x, 1) : UA σ G.V.J × UA σ G.W.J) (shiftA H H' 1) = shiftA H H' 1 := by
    intro x hx
    have h : mat x * Matrix.vecMulVec (incV F H.x) (incV F H'.y) = Matrix.vecMulVec (incV F H.x) (incV F H'.y) :=
      (Matrix.mul_vecMulVec _ _ _).trans (by rw [hx])
    simp only [actAB, shiftA, Units.val_one, one_smul, Prod.snd_one, Prod.fst]
    simpa [mat] using h
  have hunipfix : ∀ n ∈ unip σ G.V H, mat n *ᵥ incV F H.x = incV F H.x := by
    intro n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx => exact hx.1
    | one => rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
    | mul x y _ _ hx hy => rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hy, hx]
    | inv x _ hx =>
      conv_lhs => rw [← hx]
      rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  obtain ⟨j, hj⟩ := hT.geo.even
  have hlt := hT.geo.lt
  have hzr : (((b + 2 - a') / 2 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) - ((b + a' : ℕ) : ℝ) / 2 := by
    have h2 : 2 * ((b + 2 - a') / 2) + a' = b + 2 := by omega
    have h2' : (2 : ℝ) * (((b + 2 - a') / 2 : ℕ) : ℝ) + (a' : ℝ) = (b : ℝ) + 2 := by exact_mod_cast h2
    push_cast
    linarith
  have key : ∀ (f' : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (k : UA σ G.V.J), k ∈ UAt σ G.V (evI F) →
      ∀ y : (AE F E)ˣ, y ∈ idelesAt E (evI F) →
      l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f' k y) =
        l (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) (locOpInf (om (m y⁻¹ * k, 1)) f'))) *
          (((absE F E y : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro f' k hk y hy
    obtain ⟨hL, hmU⟩ := hm y⁻¹ (inv_mem hy)
    have h5 := t5 y⁻¹ (m y⁻¹) (inv_mem hy) hL hmU (locOpInf (om (k, 1)) f')
    rw [t3 (m y⁻¹) hmU k hk f', inv_inv] at h5
    rw [h5, coneInfInt]
    simp only [map_smul, smul_eq_mul]
    have hν : ((X.ν y⁻¹ : Circle) : ℂ)⁻¹ = (X.ν y : ℂ) := by simp
    have habs : absE F E y⁻¹ = (absE F E y)⁻¹ := map_inv _ _
    have hr : (0 : ℝ) < (absE F E y : ℝ) := by
      have h1 : absE F E y * absE F E y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have h0 : absE F E y ≠ 0 := fun h => by rw [h, zero_mul] at h1; exact zero_ne_one h1
      exact_mod_cast pos_iff_ne_zero.2 h0
    rw [hν, habs]
    have hreal : ((absE F E y : ℝ)) ^ ((b + 2 - a') / 2) =
        ((absE F E y : ℝ))⁻¹ ^ (((b + a' : ℕ) : ℝ) / 2) * (absE F E y : ℝ) ^ ((b + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, hzr, Real.inv_rpow hr.le, Real.rpow_sub hr]
      field_simp
    have hc : ((absE F E y : ℝ) : ℂ) ^ ((b + 2 - a') / 2) =
        ((((absE F E y : ℝ))⁻¹ ^ (((b + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (((absE F E y : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, hreal, Complex.ofReal_mul]
    rw [hc]
    push_cast
    ring
  have e1 : ∀ g' ∈ UAt σ G.V (evI F), ∀ (k : KAt K (evI F)) (y : idelesAt E (evI F)),
      l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) (locOpInf (om (g', 1)) f) k.1 y.1) =
        (fun x : UA σ G.V.J => l (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) (locOpInf (om (x, 1)) f))))
          (m y.1⁻¹ * k.1 * g') * (((absE F E y.1 : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    intro g' hg' k y
    have hmk : m y.1⁻¹ * k.1 ∈ UAt σ G.V (evI F) :=
      (UAtSub σ G.V (evI F)).mul_mem (hm _ (inv_mem y.2)).2 k.2.2
    rw [key _ k.1 k.2.2 y.1 y.2, t3 (m y.1⁻¹ * k.1) hmk g' hg' f]
  have e2 : ∀ (k : KAt K (evI F)) (y : idelesAt E (evI F)),
      l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f k.1 y.1) =
        (fun x : UA σ G.V.J => l (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) (locOpInf (om (x, 1)) f))))
          (m y.1⁻¹ * k.1) * (((absE F E y.1 : ℝ) ^ ((b + 1 : ℕ) : ℝ) : ℝ) : ℂ) := fun k y => key f k.1 k.2.2 y.1 y.2
  simp only [e1 g hg, e2]
  refine GlobalTheory.T.config_A_haar_stabilizer F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo K hK μK μ hμK hμ m hm (fun x : UA σ G.V.J => l (ei (locOpInf (G.M.co.rho B.ψ (partInf F (shiftA H H' 1))) (locOpInf (om (x, 1)) f))))
    (l.continuous.comp_continuousOn (t9 f)) ?_ ?_ ?_ g hg
  · intro n hn hnI x hx
    beta_reduce
    rw [← t3 n hnI x hx f]
    have h4 := t4 n hnI (shiftA H H' 1) (locOpInf (om (x, 1)) f)
    rw [hfix n (hunipfix n hn)] at h4
    rw [← h4, t1 n hn hnI]
  · intro g₀ g' hL hg' hg₀ x hx
    beta_reduce
    rw [← t3 g' hg' x hx f]
    have h4 := t4 g' hg' (shiftA H H' 1) (locOpInf (om (x, 1)) f)
    rw [hfix g' (by simpa using hL.1)] at h4
    rw [← h4, t2 g₀ g' hL hg' hg₀, hl₀ g₀ hg₀]
  · intro g' hg'
    exact (t7 (locOpInf (om (g', 1)) f)).congr (Eventually.of_forall fun p => e1 g' hg' p.1 p.2)

end GlobalTheory.ThK.LemF
