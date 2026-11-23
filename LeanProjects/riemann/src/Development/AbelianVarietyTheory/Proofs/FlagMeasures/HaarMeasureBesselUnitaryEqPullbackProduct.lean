import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PullHaarW

open Formalism.L2.SG.RealObj

section Gen

variable {k r n : ℕ} {ε : Fin n → Bool} {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
  {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ}

theorem trG_memUH (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r) (γ : Formalism.REAL.UJ ε) :
    trG Q Qi γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hγ : (Formalism.MainNotions.S.uMat γ)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat γ = Formalism.REAL.Jm ε := γ.2
  have hQi := Formalism.L2.SG.Pf.Choice.qiHqi ε h2 hg
  show (Qi * Formalism.MainNotions.S.uMat γ * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qi * Formalism.MainNotions.S.uMat γ * Q) = Formalism.QuantumDeterminants.Hpk k r
  calc (Qi * Formalism.MainNotions.S.uMat γ * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qi * Formalism.MainNotions.S.uMat γ * Q)
      = Qᴴ * ((Formalism.MainNotions.S.uMat γ)ᴴ * (Qiᴴ * Formalism.QuantumDeterminants.Hpk k r * Qi) * Formalism.MainNotions.S.uMat γ) * Q := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hQi, hγ, hg]

theorem trG_surj (hn : n = 2 * r + k + 1) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r) {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : ∃ γ : Formalism.REAL.UJ ε, trG Q Qi γ = x := by
  subst hn
  have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
  have hQiH := Formalism.L2.SG.Pf.Choice.qiHqi ε h2 hg
  have hγ : (Q * x * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * x * Qi) = Formalism.REAL.Jm ε := by
    calc (Q * x * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * x * Qi)
        = Qiᴴ * (xᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * x) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hg, hx', hQiH]
  refine ⟨Formalism.L2.SG.Pf.WFL.toUJ (Q * x * Qi) hγ, ?_⟩
  show Qi * (Q * x * Qi) * Q = x
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem trG_fix (h2 : Q * Qi = 1) (γ : Formalism.REAL.UJ ε) (w : Fin n → ℂ) :
    trG Q Qi γ *ᵥ (Qi *ᵥ w) = Qi *ᵥ w ↔ Formalism.MainNotions.S.uMat γ *ᵥ w = w := by
  have key : trG Q Qi γ *ᵥ (Qi *ᵥ w) = Qi *ᵥ (Formalism.MainNotions.S.uMat γ *ᵥ w) := by
    simp only [trG, Matrix.mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [key]
  constructor
  · intro h
    have e : ∀ y, Q *ᵥ (Qi *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have h' : Q *ᵥ (Qi *ᵥ (Formalism.MainNotions.S.uMat γ *ᵥ w)) = Q *ᵥ (Qi *ᵥ w) := congrArg _ h
    rwa [e, e] at h'
  · intro h
    rw [h]

theorem trG_fix_single (h1 : Qi * Q = 1) (h2 : Q * Qi = 1) (γ : Formalism.REAL.UJ ε) (i : Fin (2 * r + k + 1)) (c : ℂ)
    (w : Fin n → ℂ) (hQ : Q *ᵥ Pi.single i 1 = c • w) :
    trG Q Qi γ *ᵥ Pi.single i 1 = Pi.single i 1 ↔ Formalism.MainNotions.S.uMat γ *ᵥ w = w := by
  have hb : (Pi.single i 1 : Fin (2 * r + k + 1) → ℂ) = Qi *ᵥ (c • w) := by
    rw [← hQ, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hc : c ≠ 0 := by
    rintro rfl
    have h0 : (Pi.single i 1 : Fin (2 * r + k + 1) → ℂ) = 0 := by rw [hb, zero_smul, Matrix.mulVec_zero]
    have h := congrFun h0 i
    simp at h
  rw [hb, trG_fix h2, Matrix.mulVec_smul]
  constructor
  · intro h
    exact smul_right_injective _ hc h
  · intro h
    rw [h]

end Gen

section Set

variable {D : D7} {X : HidaSetting D}

theorem trG_mem_UW_iff (C : Choice X 1) (u : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) ↔
      (∀ a, Formalism.MainNotions.S.uMat γ *ᵥ rv X.B.I (vOf X τ) (X.eR a) = rv X.B.I (vOf X τ) (X.eR a)) ∧
      (∀ a, Formalism.MainNotions.S.uMat γ *ᵥ rv X.B.I (vOf X τ) (X.fR a) = rv X.B.I (vOf X τ) (X.fR a)) ∧
      Formalism.MainNotions.S.uMat γ *ᵥ rv X.B.I (vOf X τ) (X.zR u) = rv X.B.I (vOf X τ) (X.zR u) := by
  obtain ⟨h1, h2, hg, hef⟩ := C.isT τ
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_setOf_eq, zB, Formalism.QuantumDeterminants.bvec]
  rw [trG_fix h2]
  constructor
  · rintro ⟨-, ha, hz⟩
    exact ⟨fun a => (trG_fix_single h1 h2 γ _ _ _ (hef a a rfl).1).1 (ha a).1,
      fun a => (trG_fix_single h1 h2 γ _ _ _ (hef a a rfl).2).1 (ha a).2, hz⟩
  · rintro ⟨he, hf, hz⟩
    exact ⟨trG_memUH h2 hg γ, fun a => ⟨(trG_fix_single h1 h2 γ _ _ _ (hef a a rfl).1).2 (he a),
      (trG_fix_single h1 h2 γ _ _ _ (hef a a rfl).2).2 (hf a)⟩, hz⟩

theorem mem_Hset_iff (C : Choice X 1) (u : D.what₂.Word) (x : X.B.I.Ginf) :
    x ∈ Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) ↔
      ∀ τ, Matrix.of (trI C x τ) ∈ Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
  simp only [trI, Equiv.apply_symm_apply]
  simp_rw [trG_mem_UW_iff C u]
  constructor
  · intro hx τ
    exact ⟨fun a => hx _ _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => hx _ _ (Or.inl (Or.inr ⟨a, rfl⟩)),
      hx _ _ (Or.inr rfl)⟩
  · intro h v y hy
    obtain ⟨τ, rfl⟩ : ∃ τ, v = vOf X τ := ⟨X.pl v, (X.pl.symm_apply_apply v).symm⟩
    obtain ⟨he, hf, hz⟩ := h τ
    rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hy
    · exact he a
    · exact hf a
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hz

end Set

open Formalism.L2.SG.RealObj.InfCut.ProductExactness

section Meas

variable {D : D7} {X : HidaSetting D}

theorem n_eq' : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  rw [X.n_eq, dimS_eq]

theorem trI_eq (C : Choice X 1) : trI C = Pi.map (fun τ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) =>
    (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) γ) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) ∘
    (Homeomorph.piCongrLeft (Y := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm := by
  funext x τ
  simp [trI, Pi.map]
  rfl

theorem trI_closedEmb (C : Choice X 1) : Topology.IsClosedEmbedding (trI C) := by
  rw [trI_eq]
  exact (Topology.IsClosedEmbedding.piMap fun τ => Formalism.L2.SG.Pf.BaseOf.trG_closedEmb n_eq'
    (X.B.I.ε (vOf X τ)) (C.isT τ).2.1).comp (Homeomorph.piCongrLeft _).symm.isClosedEmbedding

theorem UW_sub_range (C : Choice X 1) (u : D.what₂.Word) :
    {y : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | ∀ τ, Matrix.of (y τ) ∈
      Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)} ⊆ Set.range (trI C) := by
  intro y hy
  have h : ∀ τ, ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), trG (C.Q τ) (C.Qi τ) γ = Matrix.of (y τ) := fun τ =>
    trG_surj n_eq' (C.isT τ).1 (C.isT τ).2.1 (C.isT τ).2.2.1 (hy τ).1
  choose γ hγ using h
  refine ⟨Homeomorph.piCongrLeft (Y := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm γ, ?_⟩
  funext τ
  have key : (Homeomorph.piCongrLeft (Y := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm γ) (vOf X τ) = γ τ :=
    congrFun (Homeomorph.symm_apply_apply
      (Homeomorph.piCongrLeft (Y := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm) γ) τ
  simp only [trI]
  rw [key, hγ τ]
  rfl

end Meas

theorem pullH : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ X.muH u Set.univ = c ∧
      ∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muH u A = c * Measure.pi (C.muW u) (trI C '' A) := by
  intro D X C _ _ u
  have he : MeasurableEmbedding (trI C) := (trI_closedEmb C).measurableEmbedding
  haveI : ∀ τ, SigmaFinite (C.muW u τ) := fun τ => (C.muW_haar u τ).1
  set μ := Measure.pi (C.muW u) with hμ
  set P : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := Set.univ.pi (fun τ =>
    {m | Matrix.of m ∈ Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)}) with hP
  have hPc : μ Pᶜ = 0 := PiM.pi_conc _ _ fun τ => (C.muW_haar u τ).2.2.1
  have hPr : P ⊆ Set.range (trI C) := fun y hy => UW_sub_range C u (fun τ => hy τ (Set.mem_univ τ))
  have hrc : μ (Set.range (trI C))ᶜ = 0 := measure_mono_null (Set.compl_subset_compl.2 hPr) hPc
  set ρ := μ.comap (trI C) with hρ
  have hρA : ∀ A, ρ A = μ (trI C '' A) := fun A => he.comap_apply μ A
  have hμ1 : μ Set.univ = 1 := by
    rw [hμ, Measure.pi_univ]
    simp [C.muW_one]
  have hρ1 : ρ Set.univ = 1 := by
    rw [hρA, Set.image_univ, ← hμ1]
    refine le_antisymm (measure_mono (Set.subset_univ _)) ?_
    calc μ Set.univ ≤ μ (Set.range (trI C)) + μ (Set.range (trI C))ᶜ := measure_univ_le_add_compl _
      _ = μ (Set.range (trI C)) := by rw [hrc, add_zero]
  haveI : IsFiniteMeasure ρ := ⟨by rw [hρ1]; exact ENNReal.one_lt_top⟩
  have hρ0 : ρ ≠ 0 := fun h => by
    have h1 := hρ1
    rw [h] at h1
    simp at h1
  have hHc : ρ (HinfG X u : Set X.B.I.Ginf)ᶜ = 0 := by
    rw [HinfG_coe, hρA]
    refine measure_mono_null ?_ hPc
    rintro _ ⟨x, hx, rfl⟩ hy
    exact hx ((mem_Hset_iff C u x).2 fun τ => hy τ (Set.mem_univ τ))
  have hmapρ : ρ.map (trI C) = μ := by
    rw [hρ, he.map_comap, Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hrc)]
  have hinv : ∀ s ∈ HinfG X u, ρ.map (fun x => s * x) = ρ := by
    intro s hs
    have hs' := (mem_Hset_iff C u s).1 (by rw [← HinfG_coe]; exact hs)
    have hcomm : trI C ∘ (fun x => s * x) =
        (fun y τ => Formalism.QuantumDeterminants.lmulM (Matrix.of (trI C s τ)) (y τ)) ∘ trI C := by
      funext x τ
      show C.Qi τ * (Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (x (vOf X τ))) * C.Q τ =
        C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * C.Q τ * (C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ)
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), (C.isT τ).2.1, Matrix.one_mul]
    have hLm : Measurable (fun (y : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) τ =>
        Formalism.QuantumDeterminants.lmulM (Matrix.of (trI C s τ)) (y τ)) :=
      measurable_pi_lambda _ fun τ => (Formalism.L2.SG.Pf.WFL.measurable_lmulM _).comp (measurable_pi_apply τ)
    have hμL : μ.map (fun y τ => Formalism.QuantumDeterminants.lmulM (Matrix.of (trI C s τ)) (y τ)) = μ := by
      haveI : ∀ τ, SigmaFinite ((C.muW u τ).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (trI C s τ)))) := fun τ => by
        rw [(C.muW_haar u τ).2.2.2 _ (hs' τ)]
        infer_instance
      rw [hμ, Measure.pi_map_pi (fun τ => (Formalism.L2.SG.Pf.WFL.measurable_lmulM _).aemeasurable)]
      congr 1
      funext τ
      exact (C.muW_haar u τ).2.2.2 _ (hs' τ)
    rw [← he.comap_map (ρ.map (fun x => s * x)), Measure.map_map he.measurable (measurable_const_mul s), hcomm,
      ← Measure.map_map hLm he.measurable, hmapρ, hμL]
  obtain ⟨hσ, h0, hc, hi⟩ := X.muH_haar u
  haveI := hσ
  rw [← HinfG_coe] at hc hi
  obtain ⟨κ, hκ0, hκT, hκ⟩ := PiM.uniq_on_closed (HinfG X u) (HinfG_closed X u) (X.muH u) ρ hc hHc hi hinv h0 hρ0
  refine ⟨κ, hκ0, hκT, ?_, fun A _ => ?_⟩
  · rw [hκ, Measure.smul_apply, hρ1, smul_eq_mul, mul_one]
  · rw [hκ, Measure.smul_apply, hρA, smul_eq_mul]

end GlobalTheory.PullHaarW
