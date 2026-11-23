import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section Gen

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def ptMat (c c' : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K := !![c 0, c' 0; c 1, c' 1]

private theorem ptMat_cont (c : Fin 2 → K) : Continuous (ptMat c) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [ptMat] <;> first | exact continuous_const | exact continuous_apply _

private theorem slice_mem {a : Matrix (Fin 2) (Fin 2) K → ℂ}
    (ha : a ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K)) (c : Fin 2 → K) :
    (fun c' => a (ptMat c c')) ∈ localSchwartzBruhatPi K := by
  have hl : Function.LeftInverse (fun X : Matrix (Fin 2) (Fin 2) K => (![X 0 1, X 1 1] : Fin 2 → K))
      (ptMat c) := by
    intro c'
    ext i
    fin_cases i <;> simp [ptMat]
  have hg : Continuous (fun X : Matrix (Fin 2) (Fin 2) K => (![X 0 1, X 1 1] : Fin 2 → K)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_id.matrix_elem 0 1
    · exact continuous_id.matrix_elem 1 1
  exact ⟨ha.1.comp_continuous (ptMat_cont c),
    ha.2.comp_isClosedEmbedding (hl.isClosedEmbedding hg (ptMat_cont c))⟩

private theorem comp_coord_mem {f : (Fin 2 × Fin 2 → K) → ℂ} (hf : f ∈ localSchwartzBruhatPi K) :
    f ∘ matrixCoordHomeomorph (Fin 2) K ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K) :=
  ⟨hf.1.comp_continuous (matrixCoordHomeomorph (Fin 2) K).continuous,
    hf.2.comp_homeomorph (matrixCoordHomeomorph (Fin 2) K)⟩

variable [MeasurableSpace K] [BorelSpace K]

private noncomputable def PG (ψ : AddChar K Circle) (a : Matrix (Fin 2) (Fin 2) K → ℂ)
    (X : Matrix (Fin 2) (Fin 2) K) : ℂ :=
  localFourierPi ψ (fun c' => a (ptMat (fun i => X i 1) c')) ![-X 1 0, X 0 0]

private theorem PG_add {ψ : AddChar K Circle} (hψ : Continuous ψ)
    {a b : Matrix (Fin 2) (Fin 2) K → ℂ}
    (ha : a ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K))
    (hb : b ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K)) :
    PG ψ (a + b) = PG ψ a + PG ψ b := by
  funext X
  exact congrFun (localFourierPi_add hψ
    (integrable_of_mem_localSchwartzBruhatPi (slice_mem ha _))
    (integrable_of_mem_localSchwartzBruhatPi (slice_mem hb _))) _

private theorem PG_smul (ψ : AddChar K Circle) (s : ℂ) (a : Matrix (Fin 2) (Fin 2) K → ℂ) :
    PG ψ (s • a) = s • PG ψ a := by
  funext X
  exact congrFun (localFourierPi_smul (ψ := ψ) s (fun c' => a (ptMat (fun i => X i 1) c'))) _

private noncomputable def outF (ψ : AddChar K Circle) (g : Fin 2 × Fin 2 → K → ℂ) : Fin 2 × Fin 2 → K → ℂ :=
  fun p => ![![GroundTheory.LocalField.localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ (g (1, 1)), g (0, 0)],
    ![fun x => GroundTheory.LocalField.localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ (g (0, 1)) (-x), g (1, 0)]] p.1 p.2

private theorem PG_tensor (ψ : AddChar K Circle) (g : Fin 2 × Fin 2 → K → ℂ) :
    PG ψ (localTensor g ∘ matrixCoordHomeomorph (Fin 2) K) =
      localTensor (outF ψ g) ∘ matrixCoordHomeomorph (Fin 2) K := by
  funext X
  have hs : (fun c' : Fin 2 → K => (localTensor g ∘ matrixCoordHomeomorph (Fin 2) K) (ptMat (fun i => X i 1) c')) =
      (g (0, 0) (X 0 1) * g (1, 0) (X 1 1)) • localTensor ![g (0, 1), g (1, 1)] := by
    funext c'
    simp [localTensor, Fintype.prod_prod_type, Fin.prod_univ_two, ptMat, coe_matrixCoordHomeomorph, matrixCoord]
    ring
  rw [PG, hs, localFourierPi_smul, localFourierPi_localTensor]
  simp [localTensor, Fintype.prod_prod_type, Fin.prod_univ_two, outF, coe_matrixCoordHomeomorph, matrixCoord]
  ring

private theorem PG_mem {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {f : (Fin 2 × Fin 2 → K) → ℂ} (hf : f ∈ localSchwartzBruhatPi K) :
    PG ψ (f ∘ matrixCoordHomeomorph (Fin 2) K) ∈
      GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K) := by
  rw [localSchwartzBruhatPi_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨N, a⟩, rfl⟩ := hg
    rw [PG_tensor]
    refine comp_coord_mem (localTensor_mem fun p => ?_)
    have h1 : ∀ {u : K → ℂ}, u ∈ GroundTheory.LocalField.schwartzBruhat K →
        GroundTheory.LocalField.localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ u ∈ GroundTheory.LocalField.schwartzBruhat K :=
      fun hu => GroundTheory.LocalField.localFourier_mem_schwartzBruhat _ hψ hψ1 hu
    have h0 : ∀ q : Fin 2 × Fin 2, cosetInd (GroundTheory.LocalField.valBall K N) (a q) ∈ GroundTheory.LocalField.schwartzBruhat K :=
      fun q => cosetInd_valBall_mem N (a q)
    obtain ⟨i, j⟩ := p
    fin_cases i <;> fin_cases j
    · exact h1 (h0 _)
    · exact h0 _
    · have := h1 (h0 (0, 1))
      exact ⟨this.1.comp_continuous continuous_neg, this.2.comp_homeomorph (Homeomorph.neg K)⟩
    · exact h0 _
  | zero =>
    have : (0 : (Fin 2 × Fin 2 → K) → ℂ) ∘ matrixCoordHomeomorph (Fin 2) K = (0 : ℂ) • (0 : Matrix (Fin 2) (Fin 2) K → ℂ) := by
      funext X; simp
    rw [this, PG_smul, zero_smul]
    exact zero_mem _
  | add g h hg hh ihg ihh =>
    rw [← localSchwartzBruhatPi_eq_span] at hg hh
    have : (g + h) ∘ matrixCoordHomeomorph (Fin 2) K =
        g ∘ matrixCoordHomeomorph (Fin 2) K + h ∘ matrixCoordHomeomorph (Fin 2) K := rfl
    rw [this, PG_add hψ (comp_coord_mem hg) (comp_coord_mem hh)]
    exact add_mem ihg ihh
  | smul c g _ ih =>
    have : (c • g) ∘ matrixCoordHomeomorph (Fin 2) K = c • (g ∘ matrixCoordHomeomorph (Fin 2) K) := rfl
    rw [this, PG_smul]
    exact Submodule.smul_mem _ c ih

private theorem PG_mem' {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {a : Matrix (Fin 2) (Fin 2) K → ℂ}
    (ha : a ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K)) :
    PG ψ a ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K) := by
  have hf : a ∘ (matrixCoordHomeomorph (Fin 2) K).symm ∈ localSchwartzBruhatPi K :=
    ⟨ha.1.comp_continuous (matrixCoordHomeomorph (Fin 2) K).symm.continuous,
      ha.2.comp_homeomorph (matrixCoordHomeomorph (Fin 2) K).symm⟩
  have h := PG_mem hψ hψ1 hf
  have he : (a ∘ (matrixCoordHomeomorph (Fin 2) K).symm) ∘ matrixCoordHomeomorph (Fin 2) K = a := by
    funext X
    simp
  rwa [he] at h

end Gen

private theorem Pt_eq_PG {F : Type} [Field F] [NumberField F] (v : P F) (a : M2 v → ℂ) :
    Pt a = PG (localAdelicChar F v) a := by
  funext X
  unfold Pt PG localFourierPi
  refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
  have h : X 0 0 * c' 1 - X 1 0 * c' 0 = ∑ i, c' i * (![-X 1 0, X 0 0] : Fin 2 → Kv v) i := by
    simp [Fin.sum_univ_two]
    ring
  simp only [ψl, h]
  rfl

theorem UpperTheory.ConvolutionTheory.R2.I.ptMem :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∃ T : SB (M2 v) →ₗ[ℂ] SB (M2 v), ∀ a, (T a).1 = Pt a.1 := by
  intro F _ _ v
  have hc := continuous_localAdelicChar (K := F) v
  have h1 := localAdelicChar_ne_one (K := F) (v := v)
  refine ⟨{ toFun := fun a => ⟨Pt a.1, ?_⟩, map_add' := ?_, map_smul' := ?_ }, fun a => rfl⟩
  · rw [Pt_eq_PG]
    exact PG_mem' hc h1 a.2
  · intro a b
    apply Subtype.ext
    change Pt (a.1 + b.1) = Pt a.1 + Pt b.1
    rw [Pt_eq_PG, Pt_eq_PG, Pt_eq_PG]
    exact PG_add hc a.2 b.2
  · intro s a
    apply Subtype.ext
    change Pt (s • a.1) = s • Pt a.1
    rw [Pt_eq_PG, Pt_eq_PG]
    exact PG_smul _ s a.1
