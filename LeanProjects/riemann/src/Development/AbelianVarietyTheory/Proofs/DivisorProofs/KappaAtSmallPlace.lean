import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]

theorem norm_ev_intAf_le {i : E →+* PadicAlgCl l} {ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l} (h : EvOk i ev)
    (z : E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.intAf F E) :
    ‖ev ((Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm z)‖ ≤ 1 := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨y, rfl⟩
    · rw [Algebra.TensorProduct.comm_symm_tmul, h.1]
      exact GlobalTheory.AdeleEv.norm_int_le i b
    · rw [Algebra.TensorProduct.comm_symm_tmul]
      exact h.2.1 _ y.2
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [map_neg, map_neg, norm_neg]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

end Int

end GlobalTheory.FrameOf

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem incOf_mem_range {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (τ : D.what₂.Tau) (x : D.host.E) :
    incOf D e0 b τ x ∈ Set.range e0 := by
  cases b
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem kapAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : KapAt p j P w := by
  intro _ e0 b ev rk _ hev
  obtain ⟨y, hy⟩ := exists_levInt p j (p.R.mu w)
  refine ⟨fun _ => 1, fun _ => rfl, fun κ τ a c => ?_⟩
  have hk : kapMat p j (p.R.mu w) ev (fun _ => 1) rk κ τ a c = ev τ (matOf j κ.1 (rk a) (rk c)) := by
    simp [kapMat, Matrix.submatrix_apply, Matrix.map_apply]
  rw [hk]
  refine ⟨?_, ?_⟩
  · refine IntermediateField.adjoin.mono _ _ _ ?_ ((hev τ).2.2.2 _)
    rintro _ ⟨x, rfl⟩
    exact incOf_mem_range e0 b τ x
  · have hz : Formalism.IndefR.Lev.swapAE D (matOf j κ.1 (rk a) (rk c)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← hy κ (rk a) (rk c)]
      exact ((y κ).val (rk a) (rk c)).2
    have h := norm_ev_intAf_le (hev τ) _ hz
    have he : (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm
        (Formalism.IndefR.Lev.swapAE D (matOf j κ.1 (rk a) (rk c))) = matOf j κ.1 (rk a) (rk c) :=
      (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm_apply_apply _
    rwa [he] at h

theorem kapSt : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, fun _ _ _ _ p _ _ j P _ _ _ w _ _ _ => kapAt p j P w⟩⟩⟩

end Pt

end GlobalTheory.FrameOf
