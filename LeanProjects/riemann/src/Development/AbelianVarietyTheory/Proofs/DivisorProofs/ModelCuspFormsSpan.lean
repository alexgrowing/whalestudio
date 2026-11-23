import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false

namespace GlobalTheory.ShareOn.Reading

section Onto
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ss_transport {X X' : Data E r} (hX : X = X') {Ψ : Finset (E →+* ℂ)} (h1 : X.Ψ = Ψ) (h2 : X'.Ψ = Ψ)
    (g : Frame Ψ r → ℂ) (la : Wt Ψ r) (la' : Wt X'.Ψ r)
    (hla : ∀ τ (t1 : τ ∈ Ψ) (t2 : τ ∈ X'.Ψ) a, la ⟨τ, t1⟩ a = la' ⟨τ, t2⟩ a)
    (hg : (fun x => g (castFrame h1 x)) ∈ X.SS (castWt h1 la)) :
    (fun y => g (castFrame h2 y)) ∈ X'.SS la' := by
  subst hX
  have hw : castWt h1 la = la' := by
    funext τ a
    exact hla τ.1 _ τ.2 a
  rw [← hw]
  exact hg

end Onto

theorem rdFun_onto {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
    {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C]
    {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) :
    0 < badN D → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (G : C → Frame M.Ψ D.R.r → ℂ), G ∈ M.SS ka →
      ∃ (m : ℕ) (α : Fin m → ℂ) (Fs : Fin m → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
        ∀ c, ∀ x ∈ M.dom, G c x = ∑ k, α k * rdFun h ha (Fs k) c x := by
  intro hN hnV G hG
  classical
  have ha' : ∀ k, (M.comp (e.symm k)).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k := fun k => by
    rw [ha (e.symm k), e.apply_symm_apply]
  have hΨk : ∀ k, M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ := fun k => by
    rw [← ha' k]; exact (M.comp_Ψ _).symm
  have hb' : ∀ k τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k ⟨τ, h2⟩ a := by
    intro k
    obtain ⟨c, rfl⟩ := e.surjective k
    exact hb c

  have hf : 0 < D.R.f := lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) i.2) D.R.m_le_f
  have hTau : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; exact hf
  obtain ⟨τ0⟩ := hTau
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (p.κ i).n := by
    rw [(p.fw.kap i τ0).2.2]; exact hnV
  have hOnto : RdOnto (h.laws v).p ((i : ℕ) + 1) (p.κ i) :=
    GlobalTheory.Shares.rdOnto_rec GlobalTheory.chartIndependence_unconditional D (r.used v).full.toTop (h.laws v).p ((i : ℕ) + 1)
      (GlobalTheory.OnTies.inR_succ i) (h.laws v).sh
      (GlobalTheory.RunIn.gamAt_of_lawsCore D _ (h.laws v).p.toLawsCore) hN
      (GlobalTheory.Dict.gram_xi_eq_of_lawsFull (h.laws v)) (p.κ i) hn
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA (h.laws v).p (GlobalTheory.OnTies.inR_succ i) _ (lastPos_kappa p i))
  let f : ∀ k : ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp, Frame (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ D.R.r → ℂ := fun k y => G (e.symm k) (castFrame (hΨk k).symm y)
  have hfm : ∀ k, f k ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).SS (laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k) := fun k =>
    ss_transport (ha' k) (M.comp_Ψ (e.symm k)) (hΨk k).symm (G (e.symm k)) ka _ (hb' k) (hG (e.symm k))
  obtain ⟨m, α, Fs, -, hsum⟩ := hOnto f hfm
  refine ⟨m, α, Fs, fun c x hx => ?_⟩
  have hy := (mem_dom_iff ha c x).2 hx
  have key := hsum (e c) _ hy
  have hl : f (e c) (castFrame (psi_eq ha c) x) = G c x := by
    show G (e.symm (e c)) (castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x)) = G c x
    have hc : e.symm (e c) = c := e.symm_apply_apply c
    have hx' : castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x) = x := rfl
    rw [hx', hc]
  rw [← hl, key]
  rfl

end GlobalTheory.ShareOn.Reading
