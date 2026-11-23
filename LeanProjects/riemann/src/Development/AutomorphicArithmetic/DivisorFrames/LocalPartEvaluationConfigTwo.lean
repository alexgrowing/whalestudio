import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AutomorphicArithmetic.DivisorFrames.LocalThetaPartitionTripleAlt
import Development.AutomorphicArithmetic.DivisorFrames.UnitaryStabilizerLiftsToSmallerSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalEigenTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartOperatorCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

private theorem rho_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {U : Type} [AddCommGroup U] [Module R U]
    {B : U → U → R} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar R ℂ)
    (Φ : (κ → R) → ℂ) : co.rho ψ 0 Φ = Φ := by
  funext z
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

private theorem sigR_sigR' {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    show a ⊗ₜ[F] σ (σ x) = _
    rw [hσ]

private theorem atV_incV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : Pl F) (x : Fin n → E) (i : Fin n) : atV v (incV F x) i = inclR (F := F) (Fv F v) (x i) := by
  change evFin F v 1 ⊗ₜ[F] x i = (1 : Fv F v) ⊗ₜ[F] x i
  rw [map_one]

private theorem pair_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (x y : Fin n → E)
    (hxy : form σ J x y = 1) (c : AE F E) (a : Fv F v ⊗[F] E) :
    pairV σ J v (atV v (c • incV F x)) (fun i => sigR (Fv F v) σ a * atV v (incV F y) i) = compFin F E v c * a := by
  have h1 : ∀ i, atV v (c • incV F x) i = compFin F E v c * inclR (F := F) (Fv F v) (x i) := fun i => by
    rw [← atV_incV]
    simp only [atV, Pi.smul_apply, smul_eq_mul, map_mul]
  have h2 : ∀ e : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := fun _ => rfl
  have h3 := congrArg (inclR (F := F) (Fv F v)) hxy
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, map_one] at h3
  simp only [pairV, dotProduct, Matrix.mulVec, h1, map_mul, sigR_sigR' _ hσ, atV_incV, h2, Matrix.map_apply]
  rw [← mul_one (compFin F E v c * a), ← h3]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem acts_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {v : Pl F}
    {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {φ φ₁ : (κ → Fv F v) → ℂ} (c : ℂ) (h : Acts (evFin F v) T φ φ₁) :
    Acts (evFin F v) (fun Ψ => c • T Ψ) φ (c • φ₁) := by
  intro r hr
  show c • T _ = _
  rw [h r hr]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem UpperTheory.local_part_evaluation_config_two :
    GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
                 (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
                 ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', GlobalTheory.ThK.LemF.IsLocPart G.M' G₁.M' e' ei' ev' →
                 ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F), ∀ l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
                   (∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l (locOp v (om₁' (g₀, 1)) ψ) = l ψ) →
                   ∀ k ∈ UAt σ G.V' (evFin F v), ∀ t : (AE F E)ˣ, mat k *ᵥ incV F H.x = (t : AE F E) • incV F H.x →
                   ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ∀ s : Fv F v ⊗[F] E,
                   l (evS B G.M' v (ev' v) H H' (locOp v (om' (k, 1)) φ) s) =
                     GlobalTheory.ThK.LemF.fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t * l (evS B G.M' v (ev' v) H H' φ (compFin F E v (t : AE F E) * s)) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' ei' ev' hl X om om' om₁ om₁' hT hT₁ v l hlinv k hk t hkx φ hφ s
  have hA := GlobalTheory.T.theta_action_exists hP
  have P' := GlobalTheory.ThK.Inhab.pairV' hT
  have P₁' := GlobalTheory.ThK.Inhab.pairV' hT₁
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.AdelicU.cm_conj_conj hT.base.cm
  have hone : ∀ {n : ℕ} (Y : Spc F E n), (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun Y u _ => by simp [mat]
  have hmem : ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ev' v φ ∈ SB (Fin b × Fin (a + b) → Fv F v) :=
    fun φ hφ => (hl.2.1 v).2 ▸ Submodule.mem_map_of_mem hφ
  obtain ⟨g₀, hg₀, m, u, hu, hL, hkum⟩ := UpperTheory.unitary_stabilizer_lifts_to_smaller_space F E σ B _ _ _ _ _ _ G.V' G₁.V' H hT.base hT.geo.hV' hC.hH v k hk t hkx
  obtain ⟨hU, hLaw⟩ := GlobalTheory.ThK.EvLawBLeft.globalLaw hP F E σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁
  have step1 : ∀ φ' ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      l (ev' v (locOp v (om' (k, 1)) φ')) = GlobalTheory.ThK.LemF.fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t * l (ev' v φ') := by
    intro φ' hφ'
    have hact : ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), Acts (evFin F v)
        (fun Ψ => GlobalTheory.ThK.LemF.fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t • om₁' (g₀, 1) Ψ) ψ
        (GlobalTheory.ThK.LemF.fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t • locOp v (om₁' (g₀, 1)) ψ) :=
      fun ψ hψ => acts_smul _ (acts_locOp_om hA P₁' hg₀ (hone _) hψ)
    have key := GlobalTheory.T.local_part_operator_compatible F E σ B.ψ _ _ _ _ G.V' G.W G₁.V' G₁.W G.M' G₁.M' hT.geo.hM' hT₁.geo.hM' e' ei' ev' hl v
      (om' (k, 1)) (fun Ψ => GlobalTheory.ThK.LemF.fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t • om₁' (g₀, 1) Ψ)
      (fun Φ hΦ => by
        have e : om' (k, 1) Φ = om' (u, 1) (om' (m, 1) Φ) := by
          rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, hkum]
        rw [e, hU u hu _ ((hT.weil'.isUSplitting).pres _ _ hΦ), hLaw t g₀ m hL Φ hΦ])
      (fun ψ hψ => ⟨_, locOp_mem _ _ _, acts_locOp_om hA P' hk (hone _) hψ⟩)
      (fun ψ hψ => ⟨_, (SB _).smul_mem _ (locOp_mem _ _ _), hact ψ hψ⟩) φ' hφ'
    rw [key, locOp_eq (hmem φ' hφ') ((SB _).smul_mem _ (locOp_mem _ _ _)) (hact _ (hmem φ' hφ')), map_smul,
      hlinv g₀ hg₀ _ (hmem φ' hφ'), smul_eq_mul]
  have hz : ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), evS B G.M' v (ev' v) H H' ψ 0 = ev' v ψ := by
    intro ψ hψ
    rw [evS, uS_zero, partFin, smul_zero, locOp_of_fix (fun Φ _ => rho_zero' _ _ Φ) hψ]
  have h11 : ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      locOp v (om' ((1 : UA σ G.V'.J), (1 : UA σ G.W.J))) ψ = ψ := fun ψ hψ =>
    locOp_of_fix (fun Φ _ => by
      show (om' 1) Φ = Φ
      rw [map_one]
      rfl) hψ
  have hinv : mat k⁻¹ *ᵥ incV F H.x = ((t⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.x := by
    have h1 : mat k⁻¹ * mat k = 1 := by
      show mat (k⁻¹ * k) = 1
      rw [inv_mul_cancel]
      rfl
    have h2 := congrArg (fun z => ((t⁻¹ : (AE F E)ˣ) : AE F E) • mat k⁻¹ *ᵥ z) hkx
    simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul] at h2
    exact h2.symm
  have h1x : mat (1 : UA σ G.V'.J)⁻¹ *ᵥ incV F H.x = (1 : AE F E) • incV F H.x := by
    rw [inv_one, one_smul]
    exact Matrix.one_mulVec _
  have A := UpperTheory.local_theta_partition_triple_alt hP F E σ B a b G G₁ H H' hC e' he' ei' ev' hl X om om' om₁ om₁' hT hT₁ v k hk φ hφ
    (fun i => sigR (Fv F v) σ (compFin F E v (t : AE F E) * s) * atV v (incV F H.y) i) 0
  have A1 := UpperTheory.local_theta_partition_triple_alt hP F E σ B a b G G₁ H H' hC e' he' ei' ev' hl X om om' om₁ om₁' hT hT₁ v 1 (hone _) φ hφ
    (fun i => sigR (Fv F v) σ (compFin F E v (t : AE F E) * s) * atV v (incV F H.y) i) 0
  rw [hinv, pair_eq hσ _ v _ _ hC.hH.xy, zero_add, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul,
    hz _ (locOp_mem _ _ _)] at A
  rw [h1x, pair_eq hσ _ v _ _ hC.hH.xy, zero_add, map_one, one_mul, h11 _ (locOp_mem _ _ _), h11 _ hφ,
    hz _ (locOp_mem _ _ _)] at A1
  rw [← A, ← A1, step1 _ (locOp_mem _ _ _)]
