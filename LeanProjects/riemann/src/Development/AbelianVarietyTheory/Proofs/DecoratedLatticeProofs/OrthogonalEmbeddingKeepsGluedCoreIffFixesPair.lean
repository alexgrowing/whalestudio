import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.StabPair

open GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_sec_any (p : SplitPt D k) {S : HSp D} (h : GA D S) (y : Fin S.rank → k) :
    Formalism.L2.Theta.mt S h *ᵥ (fun i => p.sec (y i)) = fun i => p.sec ((((Formalism.L2.Theta.mt S h).map p.pr) *ᵥ y) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sec_mul, p.sec_pr, mul_comm p.e, mul_assoc, e_mul_sec]

theorem col_mulVec {m : Type} [Fintype m] (Y : m → k) (t : Fin 1 → k) :
    Matrix.replicateCol (Fin 1) Y *ᵥ t = t 0 • Y := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.replicateCol, mul_comm]

theorem vec_emb {p : SplitPt D k} {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) {n : Type} [Fintype n]
    [DecidableEq n] {β : GlobalTheory.FinPl.Frame p A n} {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} (hs : IsSumFrame o ζ β β₀)
    (g : GL n k) (x : n ⊕ Fin 1 → k) :
    (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (β₀.b *ᵥ x) =
      β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr) := by
  have hA : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jA.map p.pr = o.jA.map p.pr * (β.b * g.val * β.b') := by
    rw [← Matrix.map_mul, o.emb_jA, Matrix.map_mul, β.gl_mat]
  have hB : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr * o.jB.map p.pr = o.jB.map p.pr := by
    rw [← Matrix.map_mul, o.emb_jB]
    simp
  have hz : (fun i => p.pr (ratV (vecB o ζ) i)) = o.jB.map p.pr *ᵥ (fun j => p.pr (incA D (ζ j))) := by
    funext i
    simp [ratV, vecB, Matrix.mulVec, dotProduct, OrthDec.jB, rat]
  have hY : (Formalism.L2.Theta.mt S (o.emb (β.gl g, 1))).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) =
      (fun i => p.pr (ratV (vecB o ζ) i)) := by
    rw [hz, Matrix.mulVec_mulVec, hB]
  rw [hs, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec, col_mulVec, col_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hY,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA]
  have e : o.jA.map p.pr * (β.b * g.val * β.b') * β.b = (o.jA.map p.pr * β.b) * g.val := by
    simp only [Matrix.mul_assoc, β.b'b, Matrix.mul_one]
  rw [e, ← Matrix.mulVec_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem mem_glued_iff {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    {β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)} {M : Lat S} {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (hG : GluedW β₀ M q m P) (x : n ⊕ Fin 1 → k) :
    (fun i => p.sec ((β₀.b *ᵥ x) i)) ∈ latV S M (· = p.v) ↔
      ∃ s : 𝒪[k], x ∘ Sum.inl - s • P.vec ∈ P.ker ∧ m * x (Sum.inr 0) = q.inv * s := by
  rw [hG x, GlobalTheory.LevelUnfold.mem_gluedS, Sum.elim_comp_inl]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  simp [Fin.forall_fin_one]

theorem glued_stab {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    {g : GL n k} (hP : g • P = P) {u : n → k} {t : k}
    (h : ∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) :
    ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := by
  obtain ⟨hk, hv⟩ := (GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec).1 hP
  obtain ⟨s, h1, h2⟩ := h
  refine ⟨s, ?_, h2⟩
  have h3 : g • (u - s • P.vec) ∈ P.ker := hk ▸ Submodule.smul_mem_pointwise_smul _ g _ h1
  have e : g.val *ᵥ u - s • P.vec = g • (u - s • P.vec) + s • (g • P.vec - P.vec) := by
    rw [smul_sub, smul_sub, smul_comm g s]
    change _ = g • u - _ + _
    change _ = g.val *ᵥ u - _ + _
    abel
  rw [e]
  exact add_mem h3 (P.ker.smul_mem s hv)

theorem glued_zero {n : Type} [Fintype n] [DecidableEq n] {q : GlobalTheory.LatPair.Unif k} {m : k} {P : GlobalTheory.LatPair.Pair k n}
    (u : n → k) : (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * 0 = q.inv * s) ↔ u ∈ P.ker := by
  constructor
  · rintro ⟨s, h1, h2⟩
    have hs : (s : k) = 0 := by
      rw [mul_zero, eq_comm, mul_eq_zero] at h2
      exact h2.resolve_left (inv_ne_zero q.ne_zero)
    have hs' : s = 0 := Subtype.ext hs
    simpa [hs'] using h1
  · intro h
    exact ⟨0, by simpa using h, by simp⟩

end GlobalTheory.Core.Mi.LatMatch.StabPair

open GlobalTheory.Core.Mi.LatMatch.StabPair in

theorem GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n), IsSumFrame o ζ β β₀ → IsSelfDualC S M → m ≠ 0 → GluedW β₀ M q m P → ∀ g : GL n k, Moves S (o.emb (β.gl g, 1)) M M (· = p.v) ↔ g • P = P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M q m P hs hM hm hG g
  have hE : ∀ x : n ⊕ Fin 1 → k, Formalism.L2.Theta.mt S (o.emb (β.gl g, 1)) *ᵥ (fun i => p.sec ((β₀.b *ᵥ x) i)) =
      fun i => p.sec ((β₀.b *ᵥ Sum.elim (g.val *ᵥ (x ∘ Sum.inl)) (x ∘ Sum.inr)) i) := fun x => by
    rw [mt_sec_any, vec_emb o ζ hs]
  constructor
  · intro hmov
    have hGG : ∀ (u : n → k) (t : k), (∃ s : 𝒪[k], u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s) ↔
        ∃ s : 𝒪[k], g.val *ᵥ u - s • P.vec ∈ P.ker ∧ m * t = q.inv * s := fun u t => by
      have := hmov (fun i => p.sec ((β₀.b *ᵥ Sum.elim u fun _ => t) i)) (fun i => GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _)
      rw [hE, mem_glued_iff hG, mem_glued_iff hG] at this
      simpa only [Sum.elim_comp_inl, Sum.elim_comp_inr, Sum.elim_inr, Function.comp_apply] using this
    rw [GlobalTheory.LatPair.Pair.smul_eq_iff P.hasVal_vec]
    have hker : ∀ u, u ∈ P.ker ↔ g.val *ᵥ u ∈ P.ker := fun u => by
      rw [← glued_zero (q := q) (m := m), ← glued_zero (q := q) (m := m), hGG]
    refine ⟨?_, ?_⟩
    · ext y
      rw [GlobalTheory.LatPair.mem_smul_iff, hker]
      change g.val *ᵥ ((g⁻¹ : GL n k).val *ᵥ y) ∈ P.ker ↔ _
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    · have h1 : ∃ s : 𝒪[k], P.vec - s • P.vec ∈ P.ker ∧ m * (m⁻¹ * q.inv) = q.inv * s :=
        ⟨1, by simp, by rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul]; simp⟩
      obtain ⟨s, h2, h3⟩ := (hGG _ _).1 h1
      have hq : q.inv ≠ 0 := inv_ne_zero q.ne_zero
      have hs : (s : k) = 1 := by
        rw [← mul_assoc, mul_inv_cancel₀ hm, one_mul] at h3
        exact mul_left_cancel₀ hq (h3.symm.trans (mul_one _).symm)
      have hs' : s = 1 := Subtype.ext hs
      change g.val *ᵥ P.vec - P.vec ∈ P.ker
      simpa [hs'] using h2
  · intro hP
    refine (sMoves_one _ _ _ _).1 (GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S M M 1 _ hM hM (normOneAt_one _) fun x => ?_)
    rw [map_one, one_smul]
    obtain ⟨y, rfl⟩ : ∃ y, x = β₀.b *ᵥ y := ⟨β₀.b' *ᵥ x, by rw [Matrix.mulVec_mulVec, β₀.bb', Matrix.one_mulVec]⟩
    rw [vec_emb o ζ hs, mem_glued_iff hG, mem_glued_iff hG]
    simp only [Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply]
    refine ⟨glued_stab hP, fun h => ?_⟩
    have := glued_stab (inv_smul_eq_iff.2 hP.symm) h
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
