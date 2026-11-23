import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPCont
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGContDiffAt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialRaisingTopOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

namespace ContPf

section ring

variable {R : Type*} [Ring R] (a c d : ℕ → R)

def K (lo : ℕ) : ℕ → R
  | 0 => 1
  | 1 => a lo
  | n + 2 => a (lo + n + 1) * K lo (n + 1) - c (lo + n + 1) * d (lo + n) * K lo n

def Sep : Prop :=
  ∀ i j, i ≠ j → Commute (a i) (a j) ∧ Commute (a i) (c j) ∧ Commute (a i) (d j) ∧ Commute (c i) (c j) ∧
    Commute (c i) (d j) ∧ Commute (d i) (d j)

variable {a c d}

theorem cp_K_both (h : Sep a c d) : ∀ n lo, K a c d lo (n + 2) =
    a lo * K a c d (lo + 1) (n + 1) - c (lo + 1) * d lo * K a c d (lo + 2) n
  | 0, lo => by
    simp only [K, mul_one, Nat.add_zero]
    rw [(h lo (lo + 1) (by omega)).1.eq]
  | 1, lo => by
    have e1 : K a c d lo 3 = a (lo + 2) * (a (lo + 1) * a lo - c (lo + 1) * d lo) - c (lo + 2) * d (lo + 1) * a lo := by
      show a (lo + 1 + 1) * K a c d lo 2 - c (lo + 1 + 1) * d (lo + 1) * K a c d lo 1 = _
      simp only [K, mul_one, Nat.add_zero]
    have e2 : K a c d (lo + 1) 2 = a (lo + 2) * a (lo + 1) - c (lo + 2) * d (lo + 1) := by
      simp only [K, mul_one]
    have e3 : K a c d (lo + 2) 1 = a (lo + 2) := rfl
    rw [e1, e2, e3]
    have h01 := h lo (lo + 1) (by omega)
    have h02 := h lo (lo + 2) (by omega)
    have h12 := h (lo + 1) (lo + 2) (by omega)
    have h20 := h (lo + 2) lo (by omega)
    have h21 := h (lo + 2) (lo + 1) (by omega)

    have t1 : a (lo + 2) * (a (lo + 1) * a lo) = a lo * (a (lo + 2) * a (lo + 1)) := by
      rw [← mul_assoc]
      exact (h20.1.mul_left h01.1.symm).eq
    have t2 : a (lo + 2) * (c (lo + 1) * d lo) = c (lo + 1) * d lo * a (lo + 2) :=
      (h21.2.1.mul_right h20.2.2.1).eq
    have t3 : c (lo + 2) * d (lo + 1) * a lo = a lo * (c (lo + 2) * d (lo + 1)) :=
      ((h02.2.1.mul_right h01.2.2.1)).eq.symm
    rw [mul_sub, t1, t2, t3, mul_sub]
    abel
  | n + 2, lo => by
    have ih1 := cp_K_both h (n + 1) lo
    have ih0 := cp_K_both h n lo
    have eL : K a c d lo (n + 2 + 2) = a (lo + n + 3) * K a c d lo (n + 3) -
        c (lo + n + 3) * d (lo + n + 2) * K a c d lo (n + 2) := by
      show a (lo + (n + 2) + 1) * K a c d lo (n + 2 + 1) - c (lo + (n + 2) + 1) * d (lo + (n + 2)) * K a c d lo (n + 2) = _
      rw [show lo + (n + 2) + 1 = lo + n + 3 by omega, show lo + (n + 2) = lo + n + 2 by omega]
    have eA : K a c d (lo + 1) (n + 2 + 1) = a (lo + n + 3) * K a c d (lo + 1) (n + 2) -
        c (lo + n + 3) * d (lo + n + 2) * K a c d (lo + 1) (n + 1) := by
      show a (lo + 1 + (n + 1) + 1) * K a c d (lo + 1) (n + 1 + 1) -
        c (lo + 1 + (n + 1) + 1) * d (lo + 1 + (n + 1)) * K a c d (lo + 1) (n + 1) = _
      rw [show lo + 1 + (n + 1) + 1 = lo + n + 3 by omega, show lo + 1 + (n + 1) = lo + n + 2 by omega]
    have eB : K a c d (lo + 2) (n + 2) = a (lo + n + 3) * K a c d (lo + 2) (n + 1) -
        c (lo + n + 3) * d (lo + n + 2) * K a c d (lo + 2) n := by
      show a (lo + 2 + n + 1) * K a c d (lo + 2) (n + 1) - c (lo + 2 + n + 1) * d (lo + 2 + n) * K a c d (lo + 2) n = _
      rw [show lo + 2 + n + 1 = lo + n + 3 by omega, show lo + 2 + n = lo + n + 2 by omega]
    rw [show n + 2 + 1 = n + 3 by omega] at eA
    rw [eL, show n + 3 = n + 1 + 2 by omega, ih1, ih0, eA, eB]
    rw [show n + 1 + 1 = n + 2 by omega]
    have hx0 := h (lo + n + 3) lo (by omega)
    have hx1 := h (lo + n + 3) (lo + 1) (by omega)
    have hy0 := h (lo + n + 2) lo (by omega)
    have hy1 := h (lo + n + 2) (lo + 1) (by omega)
    have hz1 := h lo (lo + n + 3) (by omega)
    have hz2 := h (lo + 1) (lo + n + 3) (by omega)

    have gα : Commute (a (lo + n + 3)) (a lo) := hx0.1
    have gβ : Commute (a (lo + n + 3)) (c (lo + 1) * d lo) := hx1.2.1.mul_right hx0.2.2.1
    have dα : Commute (c (lo + n + 3) * d (lo + n + 2)) (a lo) :=
      hz1.2.1.symm.mul_left (h lo (lo + n + 2) (by omega)).2.2.1.symm
    have dβ : Commute (c (lo + n + 3) * d (lo + n + 2)) (c (lo + 1) * d lo) :=
      ((hx1.2.2.2.1.mul_right (hx0.2.2.2.2.1)).mul_left
        ((h (lo + 1) (lo + n + 2) (by omega)).2.2.2.2.1.symm.mul_right hy0.2.2.2.2.2))
    simp only [mul_sub]
    set γ := a (lo + n + 3)
    set α := a lo
    set β := c (lo + 1) * d lo
    set δ := c (lo + n + 3) * d (lo + n + 2)
    have f1 : ∀ x, γ * (α * x) = α * (γ * x) := fun x => by rw [← mul_assoc, gα.eq, mul_assoc]
    have f2 : ∀ x, γ * (β * x) = β * (γ * x) := fun x => by rw [← mul_assoc, gβ.eq, mul_assoc]
    have f3 : ∀ x, δ * (α * x) = α * (δ * x) := fun x => by rw [← mul_assoc, dα.eq, mul_assoc]
    have f4 : ∀ x, δ * (β * x) = β * (δ * x) := fun x => by rw [← mul_assoc, dβ.eq, mul_assoc]
    rw [f1, f2, f3, f4]
    abel

end ring

section chains

variable {R : Type*} [Ring R] (a c d : ℕ → R)

def bu : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => (a i * (bu i).1 - c i * (bu i).2, d i * (bu i).1)

def td (r : ℕ) : ℕ → Fin 2 → R
  | 0, b => if b = 0 then 1 else 0
  | 1, b => if 1 ≤ r then (if b = 0 then a (r - 1) else d (r - 1)) else 0
  | m + 2, b => if m + 2 ≤ r then a (r - (m + 2)) * td r (m + 1) b - c (r - (m + 1)) * d (r - (m + 2)) * td r m b else 0

variable {a c d}

theorem cp_bu : ∀ i, (bu a c d i).1 = K a c d 0 i ∧ (bu a c d (i + 1)).2 = d i * K a c d 0 i
  | 0 => ⟨rfl, by simp [bu, K]⟩
  | 1 => ⟨by simp [bu, K], by simp [bu, K]⟩
  | i + 2 => by
    obtain ⟨h1, h1'⟩ := cp_bu (i + 1)
    obtain ⟨-, h0'⟩ := cp_bu i
    have e : (bu a c d (i + 2)).1 = K a c d 0 (i + 2) := by
      show a (i + 1) * (bu a c d (i + 1)).1 - c (i + 1) * (bu a c d (i + 1)).2 = _
      rw [h1, h0']
      show _ = a (0 + i + 1) * K a c d 0 (i + 1) - c (0 + i + 1) * d (0 + i) * K a c d 0 i
      rw [Nat.zero_add, mul_assoc]
    refine ⟨e, ?_⟩
    show d (i + 2) * (bu a c d (i + 2)).1 = _
    rw [e]

theorem cp_td (h : Sep a c d) (r : ℕ) : ∀ m, m ≤ r →
    td a c d r m 0 = K a c d (r - m) m ∧ td a c d r (m + 1) 1 = (if m + 1 ≤ r then d (r - 1) * K a c d (r - (m + 1)) m else 0)
  | 0, _ => by
    refine ⟨by simp [td, K], ?_⟩
    simp only [td, zero_add]
    split_ifs <;> simp_all [K]
  | 1, hm => by
    refine ⟨by simp [td, K, hm], ?_⟩
    by_cases h2 : 2 ≤ r
    · simp only [td, show 0 + 2 ≤ r from h2, if_true, h2, show (1 : ℕ) ≤ r by omega, one_ne_zero, if_false]
      simp only [show ¬ (1 : Fin 2) = 0 from by decide, if_false, mul_zero, sub_zero]
      have hc := (h (r - (0 + 2)) (r - 1) (by omega)).2.2.1
      rw [hc.eq]
      simp [K]
    · simp only [td, show ¬ (0 + 2 ≤ r) by omega, if_false, show ¬ (1 + 1 ≤ r) by omega]
  | m + 2, hm => by
    obtain ⟨i1, i1'⟩ := cp_td h r (m + 1) (by omega)
    obtain ⟨i0, i0'⟩ := cp_td h r m (by omega)
    have hb := cp_K_both h m (r - (m + 2))
    rw [show r - (m + 2) + 1 = r - (m + 1) by omega, show r - (m + 2) + 2 = r - m by omega] at hb
    refine ⟨?_, ?_⟩
    · show (if m + 2 ≤ r then a (r - (m + 2)) * td a c d r (m + 1) 0 - c (r - (m + 1)) * d (r - (m + 2)) * td a c d r m 0
        else 0) = _
      rw [if_pos hm, i1, i0, hb]
    · show (if m + 1 + 2 ≤ r then a (r - (m + 1 + 2)) * td a c d r (m + 1 + 1) 1 -
          c (r - (m + 1 + 1)) * d (r - (m + 1 + 2)) * td a c d r (m + 1) 1 else 0) = _
      by_cases h3 : m + 3 ≤ r
      · rw [if_pos (by omega), if_pos (by omega), i1', if_pos (by omega), i0', if_pos (by omega)]
        have hb2 := cp_K_both h m (r - (m + 3))
        rw [show r - (m + 3) + 1 = r - (m + 2) by omega, show r - (m + 3) + 2 = r - (m + 1) by omega] at hb2
        rw [show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega, show r - (m + 2 + 1) = r - (m + 3) by omega,
          show m + 2 + 1 = m + 3 by omega]
        rw [hb2, mul_sub]
        have ca := (h (r - (m + 3)) (r - 1) (by omega)).2.2.1
        have cc := (h (r - (m + 2)) (r - 1) (by omega)).2.2.2.2.1
        have cd := (h (r - (m + 3)) (r - 1) (by omega)).2.2.2.2.2
        rw [← mul_assoc (a (r - (m + 3))) (d (r - 1)), ca.eq,
          ← mul_assoc (c (r - (m + 2)) * d (r - (m + 3))) (d (r - 1)), (cc.mul_left cd).eq]
        simp only [mul_assoc]
      · rw [if_neg (by omega), if_neg (by omega)]

end chains

theorem cp_td_bu {R : Type*} [Ring R] {a c d : ℕ → R} (h : Sep a c d) (r : ℕ) :
    td a c d r r 0 = (bu a c d r).1 ∧ td a c d r r 1 = (bu a c d r).2 := by
  refine ⟨?_, ?_⟩
  · rw [(cp_td h r r le_rfl).1, (cp_bu r).1, Nat.sub_self]
  · rcases r with _ | s
    · simp [td, bu]
    · rw [(cp_td h (s + 1) s (by omega)).2, if_pos le_rfl, (cp_bu s).2]
      simp

section ops

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def opE (l : Fin r) (i : Fin 6) : Module.End ℂ (WSm r X) where
  toFun f := ⟨opL l i f, Formalism.FourierDecayAlt.P.PBN.MC.opL_mem l i f.2⟩
  map_add' f g := Subtype.ext (Formalism.FourierDecayAlt.P.PBN.MC.opL_add l i f.2 g.2)
  map_smul' s f := Subtype.ext (Formalism.FourierDecayAlt.P.PBN.MC.opL_smul l i f.2 s)

theorem opE_comm (l k : Fin r) (hlk : l ≠ k) (p q : Fin 6) : Commute (opE (X := X) l p) (opE k q) := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  exact Formalism.QuantumDeterminants.commuting_functional_holds r X l k p q f f.2 (Or.inl hlk)

variable (X) in

def eS (i : ℕ) (p : Fin 6) : Module.End ℂ (WSm r X) := if h : i < r then opE ⟨i, h⟩ p else 0

theorem eS_comm (i j : ℕ) (hij : i ≠ j) (p q : Fin 6) : Commute (eS (r := r) X i p) (eS X j q) := by
  unfold eS
  split_ifs with hi hj hj
  · exact opE_comm _ _ (fun e => hij (congrArg Fin.val e)) p q
  · exact Commute.zero_right _
  · exact Commute.zero_left _
  · exact Commute.zero_left _

variable (X) in
def aS (Y : ℂ) (i : ℕ) : Module.End ℂ (WSm r X) := algebraMap ℂ _ Y + eS X i 0

theorem cp_sep (Y : ℂ) : Sep (aS (r := r) X Y) (eS X · 1) (eS X · 2) := by
  intro i j hij
  have hA : ∀ z : Module.End ℂ (WSm r X), Commute (eS X i 0) z → Commute (aS X Y i) z := fun z hz =>
    (Algebra.commute_algebraMap_left Y z).add_left hz
  have hA' : ∀ z : Module.End ℂ (WSm r X), Commute (eS X j 0) z → Commute z (aS X Y j) := fun z hz =>
    ((Algebra.commute_algebraMap_left Y z).add_left hz).symm
  refine ⟨hA _ (hA' _ (eS_comm i j hij 0 0).symm), hA _ (eS_comm i j hij 0 1), hA _ (eS_comm i j hij 0 2),
    eS_comm i j hij 1 1, eS_comm i j hij 1 2, eS_comm i j hij 2 2⟩

theorem cp_vAB (Y : ℂ) : ∀ i, i ≤ r → ∀ f : WSm r X,
    (Q.vAB r Y i).1 (f : (Fin r → ℂ) → X) = (((bu (aS X Y) (eS X · 1) (eS X · 2) i).1 f : WSm r X) : (Fin r → ℂ) → X) ∧
      (Q.vAB r Y i).2 (f : (Fin r → ℂ) → X) = (((bu (aS X Y) (eS X · 1) (eS X · 2) i).2 f : WSm r X) : (Fin r → ℂ) → X)
  | 0, _, f => ⟨rfl, rfl⟩
  | i + 1, hi, f => by
    obtain ⟨h1, h2⟩ := cp_vAB Y i (by omega) f
    have hir : i < r := by omega
    simp only [Q.vAB, dif_pos hir, bu, aS, eS, dif_pos hir]
    refine ⟨?_, ?_⟩
    · rw [h1, h2]
      rfl
    · rw [h1]
      rfl

theorem cp_tdU (Y : ℂ) (b : Fin 2) : ∀ m, ∀ f : WSm r X,
    tdU r Y m b (f : (Fin r → ℂ) → X) = ((td (aS X Y) (eS X · 1) (eS X · 2) r m b f : WSm r X) : (Fin r → ℂ) → X)
  | 0, f => by
    fin_cases b <;> simp [tdU, td]
  | 1, f => by
    by_cases h1 : 1 ≤ r
    · have hr : r - 1 < r := by omega
      fin_cases b
      · simp only [tdU, td, dif_pos h1, if_pos h1, Fin.zero_eta, if_true, aS, eS, dif_pos hr]
        rfl
      · simp only [tdU, td, dif_pos h1, if_pos h1, Fin.mk_one, one_ne_zero, if_false, eS, dif_pos hr]
        rfl
    · simp only [tdU, td, dif_neg h1, if_neg h1]
      rfl
  | m + 2, f => by
    by_cases h2 : m + 2 ≤ r
    · have ih1 := cp_tdU Y b (m + 1) f
      have ih0 := cp_tdU Y b m f
      have hr2 : r - (m + 2) < r := by omega
      have hr1 : r - (m + 1) < r := by omega
      simp only [tdU, td, dif_pos h2, if_pos h2]
      rw [ih1, ih0]
      simp only [aS, eS, dif_pos hr2, dif_pos hr1]
      rfl
    · simp only [tdU, td, dif_neg h2, if_neg h2]
      rfl

end ops

section loc

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def Loc (T : ((Fin r → ℂ) → X) → (Fin r → ℂ) → X) : Prop :=
  ∀ f₁ f₂ x, f₁ =ᶠ[nhds x] f₂ → T f₁ =ᶠ[nhds x] T f₂

theorem loc_id : Loc (r := r) (X := X) id := fun _ _ _ h => h

theorem loc_zero : Loc (r := r) (X := X) (fun _ => 0) := fun _ _ _ _ => Filter.EventuallyEq.rfl

theorem loc_pOp (l : Fin r) : Loc (X := X) (pOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [pOp, wirt, hy.fderiv_eq]

theorem loc_cOp (l : Fin r) : Loc (X := X) (cOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [cOp, hy]

theorem loc_ciOp (l : Fin r) : Loc (X := X) (ciOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [ciOp, hy]

theorem loc_comp {S T : ((Fin r → ℂ) → X) → (Fin r → ℂ) → X} (hS : Loc S) (hT : Loc T) :
    Loc (fun f => S (T f)) := fun _ _ x h => hS _ _ x (hT _ _ x h)

theorem loc_add {S T : ((Fin r → ℂ) → X) → (Fin r → ℂ) → X} (hS : Loc S) (hT : Loc T) :
    Loc (fun f => S f + T f) := by
  intro f₁ f₂ x h
  filter_upwards [hS _ _ x h, hT _ _ x h] with y h1 h2
  simp only [Pi.add_apply, h1, h2]

theorem loc_sub {S T : ((Fin r → ℂ) → X) → (Fin r → ℂ) → X} (hS : Loc S) (hT : Loc T) :
    Loc (fun f => S f - T f) := by
  intro f₁ f₂ x h
  filter_upwards [hS _ _ x h, hT _ _ x h] with y h1 h2
  simp only [Pi.sub_apply, h1, h2]

theorem loc_smul (Y : ℂ) {S : ((Fin r → ℂ) → X) → (Fin r → ℂ) → X} (hS : Loc S) : Loc (fun f => Y • S f) := by
  intro f₁ f₂ x h
  filter_upwards [hS _ _ x h] with y h1
  simp only [Pi.smul_apply, h1]

theorem loc_tdU (Y : ℂ) (b : Fin 2) : ∀ m, Loc (tdU (X := X) r Y m b)
  | 0 => by
    unfold tdU
    split_ifs
    · exact loc_id
    · exact loc_zero
  | 1 => by
    unfold tdU
    split_ifs
    · exact loc_add (loc_smul Y loc_id) (loc_pOp _)
    · exact loc_ciOp _
    · exact loc_zero
  | m + 2 => by
    have ih1 := loc_tdU Y b (m + 1)
    have ih0 := loc_tdU Y b m
    unfold tdU
    split_ifs
    · exact loc_sub (loc_add (loc_smul Y ih1) (loc_comp (loc_pOp _) ih1)) (loc_comp (loc_cOp _) (loc_comp (loc_ciOp _) ih0))
    · exact loc_zero

theorem loc_vAB (Y : ℂ) : ∀ i, Loc (X := X) (Q.vAB r Y i).1 ∧ Loc (X := X) (Q.vAB r Y i).2
  | 0 => ⟨loc_id, loc_zero⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := loc_vAB Y i
    by_cases hi : i < r
    · simp only [Q.vAB, dif_pos hi]
      exact ⟨loc_sub (loc_add (loc_smul Y h1) (loc_comp (loc_pOp _) h1)) (loc_comp (loc_cOp _) h2),
        loc_comp (loc_ciOp _) h1⟩
    · simp only [Q.vAB, dif_neg hi]
      exact ⟨h1, h2⟩

theorem cp_cutoff (O : Set (Fin r → ℂ)) (hO : IsOpen O) (hOm : O ⊆ OmX r) (f : (Fin r → ℂ) → X)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O) (c : Fin r → ℂ) (hc : c ∈ O) :
    ∃ f' ∈ WSm r X, f' =ᶠ[nhds c] f := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO c hc
  let φ : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hts : tsupport φ ⊆ O := by
    rw [φ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show ε / 2 < ε; linarith)).trans hball
  refine ⟨fun x => ((φ x : ℝ) : ℂ) • f x, ⟨?_, ?_⟩, ?_⟩
  · apply ContDiff.contDiffOn
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ((φ x : ℝ) : ℂ)) x :=
        (Complex.ofRealCLM.contDiff.comp φ.contDiff).contDiffAt
      exact h1.smul (hf.contDiffAt (hO.mem_nhds hx))
    · have hn : x ∉ tsupport φ := fun h => hx (hts h)
      have hz : (φ : (Fin r → ℂ) → ℝ) =ᶠ[nhds x] 0 := by
        first
          | exact not_mem_tsupport_iff_eventuallyEq.1 hn
          | exact notMem_tsupport_iff_eventuallyEq.1 hn
      apply (contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp [hy]
  · intro x hx
    have hxO : x ∉ O := fun h => hx (hOm h)
    have h0 : φ x = 0 := by
      first
        | exact image_eq_zero_of_nmem_tsupport (fun h => hxO (hts h))
        | exact image_eq_zero_of_notMem_tsupport (fun h => hxO (hts h))
    simp [h0]
  · filter_upwards [Metric.ball_mem_nhds c φ.rIn_pos] with y hy
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    simp

end loc

end ContPf

open ContPf in
theorem residue_continuity_holds : JDRCont := by
  intro X _ _ r Y O hO hOm f hf c hc b
  obtain ⟨f', hf'm, hf'e⟩ := cp_cutoff O hO hOm f hf c hc
  have e1 : tdU r Y r b f c = tdU r Y r b f' c := ((loc_tdU Y b r) f f' c hf'e.symm).eq_of_nhds
  have ev := loc_vAB (X := X) (r := r) Y r
  have h3 := cp_tdU Y b r ⟨f', hf'm⟩
  have h4 := cp_vAB Y r le_rfl ⟨f', hf'm⟩
  have h5 := cp_td_bu (cp_sep (X := X) (r := r) Y) r
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · have e2 : (Q.vAB r Y r).1 f c = (Q.vAB r Y r).1 f' c := (ev.1 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, if_true]
    rw [e1, e2]
    change tdU r Y r 0 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vAB r Y r).1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.1, h5.1]
  · have e2 : (Q.vAB r Y r).2 f c = (Q.vAB r Y r).2 f' c := (ev.2 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, show ¬ ((1 : Fin 2) = 0) by decide, if_false]
    rw [e1, e2]
    change tdU r Y r 1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vAB r Y r).2 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.2, h5.2]

end

end Formalism.FourierDecayAlt.P.CutMP
