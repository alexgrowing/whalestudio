import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentConjugationStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentActionCocycleStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct

namespace GlobalTheory.Per.ThetaAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem actHom_tPt {L A : HSp D} (hr : L.rank ≤ A.rank) (c : D.host.E) (γ : GA D A) (a : Fin A.rank → AE D) :
    actHom L A 1 γ (tPt L A c a) = tPt L A c ((Formalism.L2.Theta.mt A γ).mulVec a) := by
  have h1 : cM (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  unfold actHom
  rw [if_pos hr, BesselCompare.mt_one, h1, Matrix.one_mul]
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tPt, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem heis_at_zero (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u : WA V W) (f : WA V W → ℂ) :
    Heisenberg₂ ψ V W u f 0 = f u := by
  simp only [Heisenberg₂, symplH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

variable {X : ThetaX D} {T : ThetaTied D X}

theorem exists_heis (Wl : WeilTied D X T) {V W : HSp D} (hne : V.rank ≠ W.rank) (u : WA V W) (Φ : X.Sch V W) :
    ∃ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) := by
  have h1 : Wl.evS V W Φ ∈ {f | IsThetaFun Wl.ψ V W f} := by
    rw [← Wl.evS_range V W hne]; exact ⟨Φ, rfl⟩
  have h2 : Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) ∈ Set.range (Wl.evS V W) := by
    rw [Wl.evS_range V W hne]; exact GlobalTheory.Mem.ThetaClosed.isThetaFun_heis Wl.ψ_std h1 u
  exact h2

theorem isThetaFun_jacOp (Wl : WeilTied D X T) {L A : HSp D} (hne : L.rank ≠ A.rank) (c : D.host.E)
    (a : Fin A.rank → AE D) (t : AE D) (Φ : X.Sch L A) :
    IsThetaFun Wl.ψ L A (jacOp Wl.ψ L A c a t (Wl.evS L A Φ)) := by
  obtain ⟨Φ', h⟩ := exists_heis Wl hne (tPt L A c a) Φ
  have h2 : jacOp Wl.ψ L A c a t (Wl.evS L A Φ) ∈ Set.range (Wl.evS L A) :=
    ⟨Wl.ψ (cenCo L c t) • Φ', by rw [map_smul, h]; rfl⟩
  rw [Wl.evS_range L A hne] at h2
  exact h2

theorem theta_aut : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → ∀ (Φ : X.Sch L A) (g : GA D A), ∀ n ∈ d.N, (∀ γ ∈ d.N, γ ∈ GQ B → d.theta Wl.ψ (omZ Wl L A Φ) (γ * n) g = d.theta Wl.ψ (omZ Wl L A Φ) n g) ∧ ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → d.theta Wl.ψ (omZ Wl L A Φ) (δ * n * δ⁻¹) (γ * g) = d.theta Wl.ψ (omZ Wl L A Φ) n g := by
  intro D X T Wl L A B ι d hA1 Φ g n hn
  have hL : L.rank = 1 := d.line.rank_one
  have hlt : L.rank < A.rank := hL ▸ hA1
  obtain ⟨hrat, -, -, hconj⟩ := GlobalTheory.T.theta_unipotent_conjugation D L A B ι d
  refine ⟨fun γ hγ hq => ?_, fun γ hγ δ hδ => ?_⟩
  · obtain ⟨ha, ht, -⟩ := GlobalTheory.T.theta_unipotent_action_cocycle D L A B ι d γ hγ n hn
    have h1 := ((hrat Wl.ψ Wl.ψ_std.1).1 γ hq).2 _
      (isThetaFun_jacOp Wl hlt.ne d.c (d.aCo n) (d.tCo n) (Wl.om L A X.etaT⁻¹ (X.etaT ^ A.rank) (1, g) Φ))
    unfold FJDat.theta FJDat.jac at *
    rw [ha, ht, ← jacOp_mul Wl.ψ hlt.le]
    exact h1
  · obtain ⟨-, ha, ht, -⟩ := hconj δ γ hδ n hn
    rw [d.theta_eq, d.theta_eq, ha, ht, ← actHom_tPt hlt.le]
    congr 1
    obtain ⟨Φ', h⟩ := exists_heis Wl hlt.ne (tPt L A d.c (d.aCo n)) (Wl.om L A X.etaT⁻¹ (X.etaT ^ A.rank) (1, g) Φ)
    have h1 := Wl.om_heis L A _ _ hlt.ne (resEta_line T hL) (resEta_pow T _) 1 γ _ _ _ h
    have h2 := Wl.om_aut L A _ _ hlt.ne (resEta_line T hL) (resEta_pow T _) 1 (one_mem _) γ hγ Φ'
    rw [h1, h, heis_at_zero, heis_at_zero, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at h2
    exact h2

end GlobalTheory.Per.ThetaAut
