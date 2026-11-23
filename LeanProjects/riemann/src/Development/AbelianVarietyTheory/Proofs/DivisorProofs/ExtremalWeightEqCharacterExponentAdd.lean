import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCharacterDetPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfolding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

open GlobalTheory.HolRead in

theorem extWt_arr_eq_wtCol {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : HCParam D.R) (p q : ℕ)
    (hpq : p + q = D.R.r) (hr : V.rank = D.R.r) (ρ : D.what₂.Tau)
    (hS : S ρ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) (c : Fin V.rank) :
    extWt M ρ (arr (nNeg (M.ε ρ)) c) = (wtCol h p q c : ℝ) := by
  have hn : p + q = V.rank := hpq.trans hr.symm
  have hp : p ≤ V.rank := by omega
  have he : IsEnum (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) (M.lam ρ) (M.ε ρ) := hS ▸ M.enum ρ
  have hε : ∀ a, M.ε ρ a = decide ((a : ℕ) < p) := fun a => (isEnum_holPar_kapW h hr hn he a).2
  obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW h p q hpq) he
  have hc := c.2
  by_cases hcq : (c : ℕ) < q
  · rw [extWt_arr M ρ hp hε c (Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨c, hcq⟩ : Fin p ⊕ Fin q)))
      (by rw [if_pos (by omega)]; simp), hx]
    simp only [wtCol, if_pos hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inr]
  · rw [extWt_arr M ρ hp hε c (Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩ : Fin p ⊕ Fin q)))
      (by rw [if_neg (by omega)]; simp; omega), hx]
    simp only [wtCol, if_neg hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inl]

theorem muVal_castDict {D : D7} {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV
  exact h

theorem extWt_eq_laU_add : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC (Wc D i), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) u = ∏ ρ, (archM (Wc D i) (R.θ ρ) u).det ^ e ρ) ∧ ∀ k ρ (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin (Wc D i).rank, w ρ a = (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) k τ (Fin.cast (rank_Wc i) a) + e ρ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht i σ hσ hV w hw
  choose e he using fun ρ => (D.hc (lab σ ρ)).e_int i
  refine ⟨fun ρ => -e ρ, ?_, fun k ρ τ hτ a => ?_⟩
  · exact GlobalTheory.HolRead.mu_real_eq_prod_det D R.θ _ _ _ e hM.inf (muVal_castDict hV (ht.laws.muVal _ (inR i) _ hσ))
      fun ρ => he ρ ▸ (ht.chiR i σ hσ).2.2.1 ρ
  · have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
    have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
      have := D.R.m_add_three_le_k
      have hi := i.2
      simp only [Ranks.sigW, Ranks.r]
      omega
    have h1 := extWt_arr_eq_wtCol (R.MW i σ) (D.hc (lab σ ρ)) _ _ (hs ▸ hr :
      ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r) (rank_Wc i) ρ
      (if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)) a
    rw [← hw ρ a, hs] at h1
    rw [GlobalTheory.HolRead.SecWt.laU_eq_wtCol D T κ ht.laws ht.alg ht.kap i σ hσ e (fun ρ => (he ρ).symm) k ρ τ hτ,
      Int.cast_injective h1]
    simp

end GlobalTheory.HolDict
