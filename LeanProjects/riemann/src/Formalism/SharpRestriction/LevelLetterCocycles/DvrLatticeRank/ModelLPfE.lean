import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfC

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLE

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem exists_fin_sum {O M N' : Type*} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N']
    [Module O N'] (t : M ⊗[O] N') : ∃ (m : ℕ) (a : Fin m → M) (s : Fin m → N'), t = ∑ j, a j ⊗ₜ s j := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a s => exact ⟨1, fun _ => a, fun _ => s, by simp⟩
  | add t t' ht ht' =>
    obtain ⟨m, a, s, rfl⟩ := ht
    obtain ⟨m', a', s', rfl⟩ := ht'
    refine ⟨m + m', Fin.append a a', Fin.append s s', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem toLA_tmul (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (s : ↥S) :
    toLA W T π' c S (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) :=
  rfl

theorem smulLA_tmul (a : LetA O n) (e : W.EE) (s : LcQ W T π' c) :
    smulLA W T π' c a (e ⊗ₜ s) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ s := rfl

theorem smulLA_smulLA (a b : LetA O n) (x : LA W T π' c) :
    smulLA W T π' c a (smulLA W T π' c b x) = smulLA W T π' c (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e s => simp only [smulLA_tmul, map_mul, mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem smul_eq_smulLA (o : O) (x : LA W T π' c) :
    o • x = smulLA W T π' c (algebraMap O (LetA O n) o) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e s =>
    rw [smulLA_tmul, TensorProduct.smul_tmul', Algebra.smul_def,
      IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  | add x y hx hy => rw [smul_add, map_add, hx, hy]

theorem rep_exists {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨m, a, s, rfl⟩ := exists_fin_sum t
  have hs : ∀ j, ∃ yy : ↥(NcS W T (c - 1)), Submodule.Quotient.mk yy = ((s j : ↥(⊤ : Submodule O _)) :
      LcQ W T π' c) := fun j => Submodule.Quotient.mk_surjective _ _
  choose yy hyy using hs
  refine ⟨m, a, fun j => (yy j : W.DD T), ⟨fun j => (yy j).2, ?_⟩⟩
  rw [← ht, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [toLA_tmul, ← hyy j]
  rfl

theorem rep_append {x x' : LA W T π' c} {m m' : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    {a' : Fin m' → ↥W.AΔ} {y' : Fin m' → W.DD T} (h : IsRepL W T π' Eπ h' c x a y)
    (h₂ : IsRepL W T π' Eπ h' c x' a' y') :
    IsRepL W T π' Eπ h' c (x + x') (Fin.append a a') (Fin.append y y') := by
  obtain ⟨hy, hx⟩ := h
  obtain ⟨hy', hx'⟩ := h₂
  refine ⟨fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact hy j
    · rw [Fin.append_right]; exact hy' j
  · rw [map_add, hx, hx', Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.append_left]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.append_right]

theorem expS_append (ζ : LL) {m m' : ℕ} (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T)
    (a' : Fin m' → ↥W.AΔ) (y' : Fin m' → W.DD T) :
    expS W T c ζ (fun j => ((Fin.append a a' j : ↥W.AΔ) : LetA O n)) (Fin.append y y') =
      expS W T c ζ (fun j => (a j : LetA O n)) y + expS W T c ζ (fun j => (a' j : LetA O n)) y' := by
  funext i
  simp only [expS, Pi.add_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem rep_smul {x : LA W T π' c} {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    (h : IsRepL W T π' Eπ h' c x a y) {b : LetA O n} (hb : b ∈ W.AΔ) :
    IsRepL W T π' Eπ h' c (smulLA W T π' c b x) (fun j => ⟨b * a j, W.AΔ.mul_mem hb (a j).2⟩) y := by
  obtain ⟨hy, hx⟩ := h
  refine ⟨hy, ?_⟩
  rw [smulLA_smulLA, mul_comm, ← smulLA_smulLA, hx, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smulLA_tmul, ← map_mul]
  congr 2
  ring

end Generic

end Formalism.MainNotions.N.Ln34.MLE

end
