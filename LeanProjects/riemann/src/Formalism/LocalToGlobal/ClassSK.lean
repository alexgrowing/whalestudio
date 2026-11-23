import Formalism.LocalToGlobal.ClassS
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

structure TiedDataSK (ex : Extra D L hT Gi Gl K Y cX) extends toTiedDataS : LinkedFamilyData ex where

  ker : Ker.KerEntTied ex

  crd : ∀ (u : D.what₂.Word) i, i ≤ D.R.m → GL (Fin (D.R.N i)) D.host.E
  crd_gram : ∀ u i (hi : i ≤ D.R.m),
    cT (Forms.sigD D : D.host.E →+* D.host.E) (crd u i hi).1 * (crd u i hi).1 = Forms.gramN D i hi

  crd_lat : ∀ u i (hi : i ≤ D.R.m) (x : Fin (D.R.N i) → D.host.E),
    x ∈ Forms.selfDualLatticeCoords D i hi ↔ ∀ a, ((crd u i hi).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

  ker_sharp : ∀ μ, (ker.cst μ).sharp = true

  ker_frm : ∀ u μ i (hi : i ≤ D.R.m) (y : (D.chTw u μ).Y i) (τ : D.what₂.Tau),
    (ker.O u μ).frm i y τ = Forms.atInf (Forms.embT D) (crd u i hi).1 τ * (Forms.twYS tw.ch cols.forms u μ i hi y).1 τ

def LinkedFamilyKernelCondition (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (TiedDataSK ex)

theorem TiedDataSK.kernel_frame_at_infinity {ex : Extra D L hT Gi Gl K Y cX} (T : TiedDataSK ex) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m)
    (y : (D.mem u).C.Y i) (τ : D.what₂.Tau) :
    (T.ker.O u D.what₂.mu0).frm i (Herm.yCast D u i y) τ =
      Forms.atInf (Forms.embT D) (T.crd u i hi).1 τ * (Forms.eYS (T.cols.forms u) i hi y).1 τ := by
  rw [T.ker_frm]
  congr 2
  simp only [Forms.twYS, Equiv.trans_apply]
  rw [T.tw.chM.eY u i hi, Equiv.symm_apply_apply]

theorem TiedDataSK.ker_de {ex : Extra D L hT Gi Gl K Y cX} (T : TiedDataSK ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ)
    (hi : i ≤ D.R.m) (y : (D.chTw u μ).Y i) (τ : D.what₂.Tau) :
    (D.chTw u μ).de i y τ = Forms.embT D τ (T.crd u i hi).1.det * ((Forms.twYS T.tw.ch T.cols.forms u μ i hi y).1 τ).det := by
  rw [(T.ker.O u μ).frm_de i hi y τ, T.ker_frm u μ i hi y τ, Matrix.det_mul]
  congr 1
  simp only [Forms.atInf]
  exact (RingHom.map_det _ _).symm

end

def LinkedFamiliesKernelFrame : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, LinkedFamilyKernelCondition (Fm.ex x hx i)

theorem LinkedFamiliesKernelFrame.c2s {eps : ℝ} {Fm : FamP eps} (h : LinkedFamiliesKernelFrame Fm) : LinkedFamiliesLevelClass Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx hx0 i => let ⟨T⟩ := h x hx hx0 i; ⟨T.toTiedDataS⟩⟩

end Formalism.L2
