import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo.FrameModels

theorem card_signs {n p q : ℕ} (hpq : p + q = n) :
    (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p ∧
      (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = false).card = q := by
  have h1 : (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p := by
    have : (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true) =
        Finset.univ.map (Fin.castLEEmb (by omega : p ≤ n)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_map]
      constructor
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        simp
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  refine ⟨h1, ?_⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun a : Fin n => decide ((a : ℕ) < p) = true)
  simp only [Bool.not_eq_true] at h2
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  omega

open Formalism.L2.NTheta in

theorem goodPar_holPar {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n) :
    GoodPar n p q (holPar p q (kapW h p q)) := by
  have hs : StrictAnti fun a : Fin n => ((lamAt h a : ℚ) : ℝ) := fun a b hab => by
    have := GlobalTheory.HolDict.lamAt_strictAnti h hn hab
    show ((lamAt h b : ℚ) : ℝ) < ((lamAt h a : ℚ) : ℝ)
    exact_mod_cast this
  refine ⟨fun a => (lamAt h a : ℝ), fun a => decide ((a : ℕ) < p), ⟨hs, fun a => lamAt h a, fun a => rfl,
    GlobalTheory.HolDict.holPar_kapW_eq h hn hpq⟩, ⟨hs, fun a => ?_⟩, (card_signs hpq).1, (card_signs hpq).2⟩
  obtain ⟨z, hz⟩ := lamAt_int h a
  obtain ⟨s, hs'⟩ := odd_r R
  refine ⟨z - s, ?_⟩
  have hn' : ((n : ℕ) : ℝ) = 2 * s + 1 := by rw [hn, hs']; push_cast; rfl
  show ((lamAt h a : ℚ) : ℝ) - _ = _
  rw [hz, hn']
  push_cast
  ring

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hl, r, hr, hS⟩, ⟨-, hi⟩, hp, hq⟩ := h
  have hs : StrictAnti fun a => -lam (Fin.rev a) := fun a b hab => neg_lt_neg (hl (Fin.rev_lt_rev.2 hab))
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a), ⟨hs, fun a => -r (Fin.rev a), fun a => by simp [hr], ?_⟩,
    ⟨hs, fun a => ?_⟩, ?_, ?_⟩
  · rw [hS]
    ext z
    simp only [dualPar, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨Fin.rev a, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨Fin.rev a, rfl⟩, rfl⟩
  · obtain ⟨m, hm⟩ := hi (Fin.rev a)
    refine ⟨-m - n + 1, ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by simp)

variable {D : D7}

theorem sig_add (i : Fin D.R.m) (ρ : D.what₂.Tau) :
    ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := by
  rw [show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (Nat.le_add_left _ _) i.2 _, rank_Wc i]
  have := D.R.m_add_three_le_k
  have hi := i.2
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem goodPar_parAt (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    GoodPar (Wc D i).rank ((Wc D i).sig (tauE D ρ)).1 ((Wc D i).sig (tauE D ρ)).2 (parAt (Wc D i) σ ρ) := by
  have h := goodPar_holPar (D.hc (lab σ ρ)) (rank_Wc i) (sig_add i ρ)
  unfold Links.parAt
  split_ifs
  · exact h
  · exact goodPar_dualPar h

theorem parAt_congr (W : HSp D) {σ σ' : D.what₂.LL →+* ℂ} (h : labE σ = labE σ') : parAt W σ = parAt W σ' := by
  have hl : lab σ = lab σ' := by
    funext ρ
    unfold lab
    rw [h]
  funext ρ
  unfold Links.parAt kapAt
  rw [h, hl]

theorem exists_frameKs : GlobalTheory.Published.DiscreteSeriesExists → ∀ (D : D7) (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x, D.embE x ∈ (algebraMap Ks D.what₂.LL).range) → ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ), FrameKs Ks MW := by
  intro hP D Ks _ _ hK
  classical
  have hne : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), Nonempty (DSModel (Wc D i) (parAt (Wc D i) σ)) := fun i σ =>
    GlobalTheory.Published.dsExists_of_discreteSeriesExists hP D _ _ (D.sp.W_sig _) (goodPar_parAt i σ)
  have hx : ∀ (V : HSp D) (S S' : D.what₂.Tau → SPar) (h : Nonempty (DSModel V S)) (h' : Nonempty (DSModel V S')), S = S' →
      ∀ ρ, x0Mat (Classical.choice h) ρ = x0Mat (Classical.choice h') ρ := by
    intro V S S' h h' e ρ
    subst e
    rfl
  refine ⟨fun i σ => Classical.choice (hne i σ), fun i σ σ' hσ ρ => hx _ _ _ _ _ (parAt_congr _ ?_) ρ, fun i σ hσ τ a => ?_⟩
  · funext τ
    ext x
    obtain ⟨y, hy⟩ := hK (D.host.sigmaOf (D.eTau τ).1 x)
    show σ (D.embE (D.host.sigmaOf (D.eTau τ).1 x)) = σ' (D.embE (D.host.sigmaOf (D.eTau τ).1 x))
    rw [← hy]
    exact RingHom.congr_fun hσ y
  · have he := (Classical.choice (hne i σ)).enum τ
    have e : parAt (Wc D i) σ τ = Formalism.L2.NTheta.holPar _ _ (kapAt (Wc D i) σ τ) := if_pos (hσ τ)
    rw [e] at he
    exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (sig_add i τ) he a).2

end GlobalTheory.RealGeo.FrameModels
