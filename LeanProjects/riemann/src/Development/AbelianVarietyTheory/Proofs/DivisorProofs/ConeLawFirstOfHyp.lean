import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalEigenPartitionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalTriplePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviShiftTransposeRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTorusMemIdelesAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorCharacterIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartEvalStabilizerStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem coneA_one_mem_UAt {n : ℕ} (X : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ X.J) ∈ UAt σ X ev :=
  (UAtSub σ X ev).one_mem

theorem coneA_isLevi_one {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (H' : Plane E d d₁) :
    IsLevi H' 1 (1 : UA σ W₁.J) (1 : UA σ W.J) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec, Units.val_one, one_smul]
  · rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul]
  · rw [GlobalTheory.StabHaar.mat_one, GlobalTheory.StabHaar.mat_one, Matrix.one_mul, Matrix.mul_one]

theorem coneA_fac_one (χ : Chr F E) (z : ℝ) : fac χ z 1 = 1 := by
  simp [fac]

theorem coneA_locOp_one {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (v : Pl F)
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) : locOp v (om (1, 1)) φ = φ :=
  locOp_of_fix (fun Φ _ => by rw [show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one]; rfl) hφ

theorem coneLawA : GlobalTheory.FunPr.Hypotheses₂ → ConeLawA := by
  intro hPr F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he ei ev hev K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hPr
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hP₁ := GlobalTheory.ThK.Inhab.pairV hT₁
  have mul := GlobalTheory.T.local_operator_mul_of_classicalTheorems hPr F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP v
  have law := GlobalTheory.T.config_a_local_eigen_partition hPr F E σ B b a' G G₁ H H' hc e he ei ev hev X om om' om₁ om₁' hT hT₁ v
  have cov := GlobalTheory.T.local_weil_action_compatibility hPr F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP v
  have FS := GlobalTheory.T.local_part_eval_stabilizer hPr F E σ B b a' G G₁ H H' hc e he ei ev hev K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ
  have hSB : ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ev v ψ ∈ SB (Fin b × Fin (b + a') → Fv F v) :=
    fun ψ hψ => (hev.2.1 v).2 ▸ Submodule.mem_map_of_mem hψ
  have h1V := coneA_one_mem_UAt (σ := σ) G.V (evFin F v)
  have h1W := coneA_one_mem_UAt (σ := σ) G.W (evFin F v)
  have h1W₁ := coneA_one_mem_UAt (σ := σ) G₁.W (evFin F v)

  have hsum : ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ∃ (N : ℕ) (g : Fin N → (Fin b × Fin (b + a') → Fv F v) → ℂ)
      (c : Fin N → ℂ), (∀ i, g i ∈ SB (Fin b × Fin (b + a') → Fv F v)) ∧
      coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ = ∑ i, c i • g i ∧
      ∀ (L : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ((Fin b × Fin (b + a') → Fv F v) → ℂ)) (y : Fin b × Fin (b + a') → Fv F v),
          ∫ k, ∫ l, L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) (locOp v (om (k.1, 1)) φ))) y *
            (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK = ∑ i, c i * L (g i) y := by
    intro φ hφ
    obtain ⟨N, g, c, hg, hL⟩ := FS φ hφ
    refine ⟨N, g, c, hg, ?_, hL⟩
    funext y
    have := hL LinearMap.id y
    simp only [LinearMap.id_apply] at this
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact this
  have hconeSB : ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ ∈ SB (Fin b × Fin (b + a') → Fv F v) := by
    intro φ hφ
    obtain ⟨N, g, c, hg, he, -⟩ := hsum φ hφ
    rw [he]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hg i)

  have hcomm : ∀ k ∈ UAt σ G.V (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      locOp v (om (k, 1)) (locOp v (om (1, h)) φ) = locOp v (om (1, h)) (locOp v (om (k, 1)) φ) := by
    intro k hk h hh φ hφ
    rw [← mul (k, 1) (1, h) hk h1W h1V hh φ hφ, ← mul (1, h) (k, 1) h1V hh hk h1W φ hφ]
    congr 2
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, mul_one, one_mul]
  refine ⟨hconeSB, ?_, ?_⟩
  ·
    intro u hu huv φ hφ
    funext y
    refine integral_congr_ae (Eventually.of_forall fun k => integral_congr_ae (Eventually.of_forall fun l => ?_))
    have hk : k.1 ∈ UAt σ G.V (evFin F v) := k.2.2
    simp only [coneFinInt]
    congr 2
    rw [hcomm k.1 hk u huv φ hφ]
    set ψ := locOp v (om (k.1, 1)) φ with hψdef
    have hψ : ψ ∈ SB _ := locOp_mem v _ φ
    have e2 := cov 1 u h1V huv (shiftA H H' l.1 * (mat u⁻¹)ᵀ) ψ hψ
    rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, GlobalTheory.StabHaar.mat_mul_inv,
      Matrix.transpose_one, Matrix.mul_one] at e2
    rw [← e2]
    have e3 := law 1 1 1 (coneA_isLevi_one H') h1W h1W₁ u hu huv _ (locOp_mem v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1 * (mat u⁻¹)ᵀ))) ψ)
    rw [mul_one] at e3
    rw [e3, coneA_fac_one, one_smul, coneA_locOp_one om₁ v (hSB _ (locOp_mem v _ ψ))]
    exact congrFun (GlobalTheory.T.config_a_local_triple_place hPr F E σ B b a' G G₁ H H' hc e he ei ev hev X om om' hT v u⁻¹ (inv_mem hu) l.1 ψ hψ) y
  ·
    intro t h₁ m hl hm hh₁ φ hφ
    obtain ⟨htv, hτv⟩ := GlobalTheory.T.levi_torus_mem_ideles_at_place F E σ B b a' G G₁ H H' hc v t h₁ m hl hm
    set τ : idelesAt E (evFin F v) := ⟨Units.map (cA σ : AE F E →* AE F E) t, hτv⟩ with hτdef

    have hex : ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), ∃ ψ₁, ψ₁ ∈ SB (Fin b × Fin (b + a') → Fv F v) ∧
        Acts (evFin F v) (om₁ (1, h₁)) ψ ψ₁ := fun ψ hψ =>
      ((hA F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP₁ v).1 1 (coneA_one_mem_UAt G₁.V _) h₁ hh₁ ψ hψ).exists
    let f : SB (Fin b × Fin (b + a') → Fv F v) →ₗ[ℂ] ((Fin b × Fin (b + a') → Fv F v) → ℂ) :=
      { toFun := fun ψ => locOp v (om₁ (1, h₁)) ψ.1
        map_add' := fun ψ ψ' => by
          have := locOp_lin (om₁ (1, h₁)).isLinear hex 1 1 ψ.2 ψ'.2
          simpa using this
        map_smul' := fun c ψ => by
          have := locOp_lin (om₁ (1, h₁)).isLinear hex c 0 ψ.2 ψ.2
          simpa using this }
    obtain ⟨L, hL⟩ := LinearMap.exists_extend f
    have hLe : ∀ ψ (hψ : ψ ∈ SB (Fin b × Fin (b + a') → Fv F v)), L ψ = locOp v (om₁ (1, h₁)) ψ :=
      fun ψ hψ => LinearMap.congr_fun hL ⟨ψ, hψ⟩
    obtain ⟨N, g, c, hg, heq, hLsum⟩ := hsum φ hφ
    obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
    haveI := hμ
    have hν0 : (X.ν τ.1 : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hab0 : ((absE F E τ.1 : ℝ) : ℂ) ≠ 0 := by
      have : absE F E τ.1 ≠ 0 := ((Group.isUnit τ.1).map (absE F E)).ne_zero
      exact_mod_cast this
    set z := (b + 2 - a') / 2 with hz
    set c₀ : ℂ := fac X.β (((b + 2 : ℕ) : ℝ) / 2) t * ((X.ν τ.1 : ℂ) * ((absE F E τ.1 : ℝ) : ℂ) ^ z)⁻¹ with hc₀

    have hint : ∀ (k : KAt K (evFin F v)) (l : idelesAt E (evFin F v)) (y : Fin b × Fin (b + a') → Fv F v),
        coneFinInt B G.M om v (ev v) (shiftA H H') X.ν z (locOp v (om (1, m)) φ) k.1 l.1 y =
          c₀ * (L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' (l * τ).1))) (locOp v (om (k.1, 1)) φ))) y *
            (X.ν (l * τ).1 : ℂ) * ((absE F E (l * τ).1 : ℝ) : ℂ) ^ z) := by
      intro k l y
      have hk : k.1 ∈ UAt σ G.V (evFin F v) := k.2.2
      set ψ := locOp v (om (k.1, 1)) φ with hψdef
      have hψ : ψ ∈ SB _ := locOp_mem v _ φ
      have e2 := cov 1 m h1V hm (shiftA H H' (l * τ).1) ψ hψ
      rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mul] at e2
      erw [GlobalTheory.T.levi_shift_transpose_relation F E σ _ _ _ _ G.W G₁.W H H' t h₁ m hl l.1] at e2
      have e3 := law t h₁ m hl hm hh₁ 1 (Subgroup.one_mem _) h1W _
        (locOp_mem v (G.M.co.rho B.ψ (partFin v (shiftA H H' (l * τ).1))) ψ)
      rw [one_mul] at e3
      simp only [coneFinInt]
      rw [hcomm k.1 hk m hm φ hφ, ← hψdef, ← e2, e3, hLe _ (hSB _ (locOp_mem v _ ψ))]
      have hmulν : (X.ν (l * τ).1 : ℂ) = (X.ν l.1 : ℂ) * (X.ν τ.1 : ℂ) := by
        rw [Subgroup.coe_mul, map_mul, Circle.coe_mul]
      have hmula : ((absE F E (l * τ).1 : ℝ) : ℂ) = ((absE F E l.1 : ℝ) : ℂ) * ((absE F E τ.1 : ℝ) : ℂ) := by
        rw [Subgroup.coe_mul, map_mul]; push_cast; ring
      rw [hmulν, hmula, Pi.smul_apply, smul_eq_mul, hc₀, mul_pow]
      field_simp
    funext y
    have hfin := hLsum L y
    simp only [coneFin]
    simp_rw [hint]
    simp_rw [integral_const_mul]
    have hsub : ∀ k : KAt K (evFin F v), (∫ l, L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' (l * τ).1)))
        (locOp v (om (k.1, 1)) φ))) y * (X.ν (l * τ).1 : ℂ) * ((absE F E (l * τ).1 : ℝ) : ℂ) ^ z ∂μ) =
        ∫ l, L (ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l.1))) (locOp v (om (k.1, 1)) φ))) y *
          (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z ∂μ := fun k =>
      integral_mul_right_eq_self (fun l : idelesAt E (evFin F v) => L (ev v (locOp v (G.M.co.rho B.ψ
        (partFin v (shiftA H H' l.1))) (locOp v (om (k.1, 1)) φ))) y * (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z) τ
    simp_rw [hsub]
    rw [hfin, Pi.smul_apply, smul_eq_mul, ← hLe _ (hconeSB φ hφ), heq, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hc₀, GlobalTheory.T.local_factor_character_identity F E σ B b a' G X om om' hT t]

end GlobalTheory.ThK.LemF
