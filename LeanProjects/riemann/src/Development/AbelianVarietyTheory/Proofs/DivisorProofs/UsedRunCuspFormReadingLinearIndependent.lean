import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ShareOn.Reading
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castFrame_castFrame_symm {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (hΨ : Ψ = Ψ')
    (x : Frame Ψ' r) : castFrame hΨ (castFrame hΨ.symm x) = x := by
  subst hΨ; rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem rdLin_linearIndependent {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
    {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
    {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type}
    [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (n : ℕ)
    (b : Fin n → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) :
    LinearIndependent (recB (h.laws v).p.toLawsCore).KO b → LinearIndependent ℂ (fun k => rdLin h ha (b k)) := by
  intro hb
  have hJ := (GlobalTheory.ReadingTieCheck.tieRead_holds (h.laws v).p ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩).2 (p.κ i)
  let b' : Fin n → cusp ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c ((r.used v).full.U ((i : ℕ) + 1))
      (wtA (p.κ i)) (p.κ i).n :=
    fun k => ⟨(b k).1, cutR_le (r.used v).full.C ((i : ℕ) + 1) (p.κ i) (b k).2⟩
  have hb' : LinearIndependent (r.used v).full.Q.c.F b' := by
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    apply Subtype.ext
    have h1 := congrArg Subtype.val hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at h1 ⊢
    exact h1
  have hR := hJ n b' hb'
  rw [Fintype.linearIndependent_iff] at hR ⊢
  intro g hg
  apply hR g
  have hoff : ∀ k, rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n (b' k) ∈
      offZero ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X :=
    fun k => rdU_mem_offZero _ _
  have claim : ∀ c, (∑ k, g k • rdC ((r.used v).full.U ((i : ℕ) + 1)) (r.used v).full.σ₀ (wtA (p.κ i)) (p.κ i).n
      (b' k)) (e c) = 0 := by
    intro c
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hx : x ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).dom
    · have hy : castFrame (psi_eq ha c).symm x ∈ M.dom :=
        (mem_dom_iff ha c _).1 (by rw [castFrame_castFrame_symm]; exact hx)
      have := congrFun (congrFun hg c) ⟨_, hy⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, rdLin_apply, rdFun,
        castFrame_castFrame_symm] at this
      exact this
    · exact Finset.sum_eq_zero fun k _ => by rw [hoff k (e c) x hx, mul_zero]
  funext k'
  have := claim (e.symm k')
  rw [e.apply_symm_apply] at this
  exact this

end GlobalTheory.ShareOn.Reading
