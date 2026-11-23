import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtEmbedding
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ShareOn.Reading

theorem cast_mem_SS_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X Y : Data E r} (hXY : X = Y)
    (hΨ : X.Ψ = Y.Ψ) {la : Wt Y.Ψ r} {la' : Wt X.Ψ r}
    (hla : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ Y.Ψ) a, la' ⟨τ, h1⟩ a = la ⟨τ, h2⟩ a) {G : Frame Y.Ψ r → ℂ}
    (hG : G ∈ Y.SS la) : (fun x => G (castFrame hΨ x)) ∈ X.SS la' := by
  subst hXY
  have e : la' = la := by funext τ a; exact hla τ.1 τ.2 τ.2 a
  subst e
  exact hG

theorem rdFun_mem_SS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), rdFun h ha F ∈ M.SS ka := by
  intro D L hT Gi Gl Kc Y cX ex Csz p r h i C _ M ka v e ha hb F c
  have key := GlobalTheory.ReadingTieCheck.reading_mem_SS (h.laws v).p ((i : ℕ) + 1) (p.κ i) F (e c)
  exact cast_mem_SS_of_eq (ha c) ((M.comp_Ψ c).trans (psi_eq ha c)) (fun τ h1 h2 a => hb c τ _ h2 a) key

end GlobalTheory.ShareOn.Reading
