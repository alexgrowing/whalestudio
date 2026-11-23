import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousOnZpart
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousLinearMat

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

def psi (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (A : Set (Matrix (Fin n) (Fin n) k)) (h : Sp k n → ℂ)
    (p : Sp k n) : ℂ :=
  {q : Sp k n | q.1 ∈ CC Z}.indicator (fun q => A.indicator 1 (zpart Z q.1) * h (q.1 - zpart Z q.1, q.2)) p

theorem psi_of_mem {A : Set (Matrix (Fin n) (Fin n) k)} {h : Sp k n → ℂ} {p : Sp k n} (hp : p.1 ∈ CC Z) :
    psi Z A h p = A.indicator 1 (zpart Z p.1) * h (p.1 - zpart Z p.1, p.2) := by
  unfold psi
  exact Set.indicator_of_mem (s := {q : Sp k n | q.1 ∈ CC Z}) hp _

theorem psi_of_not {A : Set (Matrix (Fin n) (Fin n) k)} {h : Sp k n → ℂ} {p : Sp k n} (hp : p.1 ∉ CC Z) :
    psi Z A h p = 0 := by
  unfold psi
  exact Set.indicator_of_notMem (s := {q : Sp k n | q.1 ∈ CC Z}) hp _

def OO (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Set (Sp k n) := {p | p.1 ∈ CC Z ∧ p.2 ≠ 0}

def tr (c : Matrix (Fin n) (Fin n) k) (p : Sp k n) : Sp k n := (p.1 + c, p.2)

theorem psi_add (A : Set (Matrix (Fin n) (Fin n) k)) (h h' : Sp k n → ℂ) :
    psi Z A (h + h') = psi Z A h + psi Z A h' := by
  funext p
  by_cases hp : p.1 ∈ CC Z
  · rw [Pi.add_apply, psi_of_mem hp, psi_of_mem hp, psi_of_mem hp, Pi.add_apply, mul_add]
  · rw [Pi.add_apply, psi_of_not hp, psi_of_not hp, psi_of_not hp, add_zero]

theorem psi_smul (A : Set (Matrix (Fin n) (Fin n) k)) (c : ℂ) (h : Sp k n → ℂ) :
    psi Z A (c • h) = c • psi Z A h := by
  funext p
  by_cases hp : p.1 ∈ CC Z
  · rw [Pi.smul_apply, psi_of_mem hp, psi_of_mem hp, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_left_comm]
  · rw [Pi.smul_apply, psi_of_not hp, psi_of_not hp, smul_zero]

theorem psi_tr (hZ : CR Z) (A : Set (Matrix (Fin n) (Fin n) k)) (h : Sp k n → ℂ) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) : (fun p => psi Z A h (tr c p)) = psi Z ((fun a => a - c) '' A) h := by
  funext p
  have himg : ∀ z, z ∈ (fun a => a - c) '' A ↔ z + c ∈ A := fun z =>
    ⟨fun ⟨a, ha, e⟩ => by rw [← e, sub_add_cancel]; exact ha,
      fun hz => ⟨z + c, hz, add_sub_cancel_right z c⟩⟩
  by_cases hp : p.1 ∈ CC Z
  · have h1 := cc_add hZ (x := p.1) hc
    have hm : (tr c p).1 ∈ CC Z := h1.1.2 hp
    rw [psi_of_mem hm, psi_of_mem hp]
    simp only [tr, h1.2 hp, add_sub_add_right_eq_sub]
    congr 1
    by_cases hz : zpart Z p.1 + c ∈ A
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((himg _).2 hz), Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz ((himg _).1 h'))]
  · have hm : (tr c p).1 ∉ CC Z := fun h' => hp ((cc_add hZ (x := p.1) hc).1.1 h')
    rw [psi_of_not hm, psi_of_not hp]

theorem psi_hom (hZ : CR Z) (A : Set (Matrix (Fin n) (Fin n) k)) (h : Sp k n → ℂ) (t : kˣ) :
    (fun p => psi Z A h (hom t p)) = psi Z (((t⁻¹ : kˣ) : k) • A) (fun q => h (hom t q)) := by
  funext p
  have hmem : ∀ z, z ∈ ((((t⁻¹ : kˣ) : k)) • A) ↔ (t : k) • z ∈ A := fun z => by
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (Units.ne_zero _), Units.val_inv_eq_inv_val, inv_inv]
  by_cases hp : p.1 ∈ CC Z
  · have h1 := cc_smul hZ (t : k) hp
    have hm : (hom t p).1 ∈ CC Z := h1.1
    rw [psi_of_mem hm, psi_of_mem hp]
    simp only [hom, h1.2, smul_sub]
    congr 1
    by_cases hz : (t : k) • zpart Z p.1 ∈ A
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hmem _).2 hz), Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz ((hmem _).1 h'))]
  · have hm : (hom t p).1 ∉ CC Z := fun h' => by
      have h2 := (cc_smul hZ ((t : k)⁻¹) h').1
      change (t : k)⁻¹ • ((t : k) • p.1) ∈ CC Z at h2
      rw [inv_smul_smul₀ (Units.ne_zero t)] at h2
      exact hp h2
    rw [psi_of_not hm, psi_of_not hp]

theorem psi_act (hZ : CR Z) (A : Set (Matrix (Fin n) (Fin n) k)) (h : Sp k n → ℂ) {g : GL (Fin n) k} (hg : g ∈ Gz Z) :
    (fun p => psi Z A h (act g p)) = psi Z A (fun q => h (act g q)) := by
  funext p
  have hg' : g⁻¹ ∈ Gz Z := fun a ha => by
    have e := hg a ha
    calc a * ↑g⁻¹ = (↑g⁻¹ * ↑g) * a * ↑g⁻¹ := by rw [Units.inv_mul, one_mul]
      _ = ↑g⁻¹ * (↑g * a) * ↑g⁻¹ := by simp only [mul_assoc]
      _ = ↑g⁻¹ * (a * ↑g) * ↑g⁻¹ := by rw [e]
      _ = ↑g⁻¹ * a * (↑g * ↑g⁻¹) := by simp only [mul_assoc]
      _ = ↑g⁻¹ * a := by rw [Units.mul_inv, mul_one]
  by_cases hp : p.1 ∈ CC Z
  · have h1 := cc_conj hZ hg hp
    have hm : (act g p).1 ∈ CC Z := h1.1
    have hz := (zpart_spec hp).1
    have key : (g : Matrix (Fin n) (Fin n) k) * (p.1 - zpart Z p.1) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        (g : Matrix (Fin n) (Fin n) k) * p.1 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) -
          zpart Z p.1 := by
      rw [mul_sub, sub_mul, ← hg _ hz, mul_assoc (zpart Z p.1), Units.mul_inv, mul_one]
    rw [psi_of_mem hm, psi_of_mem hp]
    simp only [act, h1.2, key]
  · have hm : (act g p).1 ∉ CC Z := fun h' => by
      have h2 := (cc_conj hZ hg' h').1
      simp only [act, inv_inv, mul_assoc, Units.inv_mul, Units.inv_mul_cancel_left,
        Units.mul_inv, mul_one] at h2
      exact hp h2
    rw [psi_of_not hm, psi_of_not hp]

theorem psi_zero (hZ : CR Z) (A : Set (Matrix (Fin n) (Fin n) k)) {h : Sp k n → ℂ}
    (h0 : ∀ p ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k)), h p = 0) : psi Z A h = 0 := by
  funext p
  by_cases hp : p.1 ∈ CC Z
  · rw [psi_of_mem hp, h0 _ ⟨sub_mem_NB hZ hp, Set.mem_univ _⟩, mul_zero, Pi.zero_apply]
  · rw [psi_of_not hp, Pi.zero_apply]

end PositivityTheory.RgUd.TP.Nil.Fib2

end
