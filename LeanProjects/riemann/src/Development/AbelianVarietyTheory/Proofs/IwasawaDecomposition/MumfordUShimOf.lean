import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam

namespace GlobalTheory.ShFam.Mumford

theorem flagDeg_reindex {ι κ : Type} {_ : Fintype ι} {_ : DecidableEq ι} {_ : Fintype κ} {_ : DecidableEq κ} (e : ι ≃ κ) (N : ℕ)
    (lam : ι → Fin N → ℝ) : Formalism.DegreeFormula.flagDeg κ N (fun τ i => lam (e.symm τ) i) = Formalism.DegreeFormula.flagDeg ι N lam := by
  rw [GlobalTheory.FlagPoly.flagDegFormula, GlobalTheory.FlagPoly.flagDegFormula, Formalism.DegreeFormula.dimFl, Formalism.DegreeFormula.dimFl, Fintype.card_congr e,
    Formalism.DegreeFormula.weylProd, Formalism.DegreeFormula.weylProd]
  congr 1
  exact (Fintype.prod_equiv e _ _ fun τ => by simp).symm

open Classical in

theorem src (h : GlobalTheory.Published.MumfordProportionality) {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A}
    (s : FinalTheorems S κ) (L : CmList A) (Φ : s.Flag) (k : s.Comp) (la : D.what₂.Tau → Fin N → ℤ) :
    (((Φ.C k).Y.inter (fun _ => s.Lw L Φ k la) : ℤ) : ℝ) =
      GlobalTheory.TrueCx.covol ((s.U κ.σ₀).X k) * Formalism.DegreeFormula.flagDeg D.what₂.Tau N (fun τ i => (la τ i : ℝ)) := by
  have hU := s.isUnf
  have hσ := κ.good_σ₀
  show (((Φ.C k).Y.inter (fun _ => (Φ.C k).Lw (S.wt L la)) : ℤ) : ℝ) = _
  obtain ⟨Dw, hp, rfl, h2, Xo, sys⟩ := S
  rw [h _ _ _ _ _ _ _ _ _ s.T _ κ.e κ.σ₀ (s.U κ.σ₀) hσ hU Φ k]
  congr 1
  exact flagDeg_reindex L.ψ _ fun τ i => (la τ i : ℝ)

theorem mumfordU_shimOf : GlobalTheory.Published.MumfordProportionality → ∀ (D : D7) (A : Amb D) (F : SrcFam A) (L : CmList A)
    (C : CxSt D.what₂.LL) (K : CutSt C) (R : ResSt C) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))
    (ng : NgPkg) (k : Kits F L C jC ng) (w : Dat D (Lv A)), MumfordU (shimOf K R k w) :=
  fun h _ _ F L _ _ _ _ _ k w c la => src h (F.at w) L (k.at w).Φ c la

end GlobalTheory.ShFam.Mumford
