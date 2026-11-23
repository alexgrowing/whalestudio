import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScPhiSymmApply

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section ScaleA6

variable {E : Type} [CommRing E] {O : Subring E} {cj : E →+* E} {qi : E} {r : ℕ} {T T' α : E}

theorem phi_inl (h : ScHyp O cj qi T T' α) (Y : Ix r → O) (b : Fin (r + 1)) :
    ((scPhi h Y (Sum.inl b) : O) : E) = (Y (Sum.inl b) : E) := by
  rw [scPhi_coe, vecMul_scC_inl]

theorem phi_inr (h : ScHyp O cj qi T T' α) (Y : Ix r → O) (b : Fin (r + 1)) :
    ((scPhi h Y (Sum.inr b) : O) : E) = (Y (Sum.inr b) : E) * cj (if b = Fin.last r then α else 1) +
      (if b = Fin.last r then (Y (Sum.inl (Fin.last r)) : E) * cj ((α - 1) * qi) else 0) := by
  rw [scPhi_coe, vecMul_scC_inr]

theorem phi_comb (h : ScHyp O cj qi T T' α) (q : E) (hq : q * qi = 1) (Y : Ix r → O) (b : Fin (r + 1)) :
    ((scPhi h Y (Sum.inl b) : O) : E) + q * (scPhi h Y (Sum.inr b) : O) =
      cj (if b = Fin.last r then α else 1) * ((Y (Sum.inl b) : E) + q * Y (Sum.inr b)) := by
  rw [phi_inl, phi_inr]
  by_cases hb : b = Fin.last r
  · subst hb
    simp only [if_true, map_mul, map_sub, map_one, h.qic]
    linear_combination ((Y (Sum.inl (Fin.last r)) : E) * (cj α - 1)) * hq
  · simp [hb]

def psiD (α : E) (cj : E →+* E) (x : E × E) : E × E := (cj α * x.1, cj α * x.2)

theorem psiD_inj (h : ScHyp O cj qi T T' α) : Function.Injective (psiD α cj) := by
  intro x y hxy
  simp only [psiD, Prod.mk.injEq] at hxy
  obtain ⟨h1, h2⟩ := hxy
  have u : ∀ a b : E, cj α * a = cj α * b → a = b := fun a b hab => by
    calc a = α * (cj α * a) := by linear_combination (-a) * h.αn
      _ = α * (cj α * b) := by rw [hab]
      _ = b := by linear_combination b * h.αn
  exact Prod.ext (u _ _ h1) (u _ _ h2)

variable (q : E)

def scTr (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    DDg O cj qi Zh T T' × DDg O cj qi Zh T T' × (E × E) × (E × E) →
      DDg O cj qi (Zh * dlast r α) T T' × DDg O cj qi (Zh * dlast r α) T T' × (E × E) × (E × E) :=
  fun p => (scBar h Zh p.1, scBar h Zh p.2.1, p.2.2.1, psiD α cj p.2.2.2)

theorem scTr_inj (h : ScHyp O cj qi T T' α) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Function.Injective (scTr h Zh) := by
  intro p p' hp
  simp only [scTr, Prod.mk.injEq] at hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact Prod.ext ((scBar h Zh).injective h1)
    (Prod.ext ((scBar h Zh).injective h2) (Prod.ext h3 (psiD_inj h h4)))

private theorem coe_sub_eq_mul_iff_sub_eq_smul (hqO : q ∈ O) (Y Y' Y'' : Ix r → O) :
    (∀ i, (Y i : E) - Y' i = q * Y'' i) ↔ Y - Y' = (⟨q, hqO⟩ : O) • Y'' := by
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  rw [Subtype.ext_iff]
  simp

theorem gamCon_iff (h : ScHyp O cj qi T T' α) (hqO : q ∈ O) (Y Y' Y'' : Ix r → O) :
    ((∀ a : Fin r, Y (Sum.inl a.castSucc) = 0) ∧
      (∀ a : Fin r, (Y' (Sum.inl a.castSucc) : E) + q * Y' (Sum.inr a.castSucc) = 0) ∧
      (∀ i, (Y i : E) - Y' i = q * Y'' i)) ↔
    ((∀ a : Fin r, scPhi h Y (Sum.inl a.castSucc) = 0) ∧
      (∀ a : Fin r, ((scPhi h Y' (Sum.inl a.castSucc) : O) : E) + q * (scPhi h Y' (Sum.inr a.castSucc) : O) = 0) ∧
      (∀ i, ((scPhi h Y i : O) : E) - (scPhi h Y' i : O) = q * (scPhi h Y'' i : O))) := by
  have hne : ∀ a : Fin r, a.castSucc ≠ Fin.last r := fun a => (Fin.castSucc_lt_last a).ne
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine forall_congr' fun a => ?_
    constructor
    · intro hy
      apply Subtype.ext
      rw [phi_inl, hy]
    · intro hy
      apply Subtype.ext
      rw [← phi_inl h, hy]
  · refine forall_congr' fun a => ?_
    rw [phi_inl, phi_inr, if_neg (hne a), if_neg (hne a), map_one, mul_one, add_zero]
  · rw [coe_sub_eq_mul_iff_sub_eq_smul q hqO, coe_sub_eq_mul_iff_sub_eq_smul q hqO, ← map_sub, ← map_smul, (scPhi h).injective.eq_iff]

end ScaleA6

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
