import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.CuspCharRep

open Formalism.IrreducibleCountingLemmas.TYPES GlobalTheory.GLq GlobalTheory.FiniteGL

variable {g : ℕ} [Fact g.Prime]

theorem mem_unipRadical_twoBlocks_iff {d a : ℕ} (had : a ≤ d) (x : Gn g d) :
    x ∈ unipRadical (ZMod g) (twoBlocks d a) ↔
      (InPar a (x : Mt g d) ∧ tl a (x : Mt g d) = 1 ∧ br a (d - a) (x : Mt g d) = 1) := by
  rw [mem_unipRadical]
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · have := h i j (by simp [twoBlocks]; split_ifs <;> omega)
      have hne : i ≠ j := fun e => by rw [e] at hi; omega
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    · funext i j
      have := h ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [twoBlocks, i.2, j.2])
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show (i : ℕ) < d ∧ (j : ℕ) < d by omega)]
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
    · funext i j
      have := h ⟨a + i, by omega⟩ ⟨a + j, by omega⟩ (by simp [twoBlocks])
      rw [Matrix.sub_apply, sub_eq_zero] at this
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show a + (i : ℕ) < d ∧ a + (j : ℕ) < d by omega)]
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
  · rintro ⟨hP, htl, hbr⟩ i j hij
    rw [Matrix.sub_apply, sub_eq_zero]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · have := congrFun (congrFun htl ⟨i, hi⟩) ⟨j, hj⟩
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (show (i : ℕ) < d ∧ (j : ℕ) < d from ⟨i.2, j.2⟩)] at this
      rw [this]
      simp [Matrix.one_apply, Fin.ext_iff]
    · exfalso
      simp [twoBlocks, hi, hj] at hij
    · have hne : i ≠ j := fun e => by rw [e] at hi; exact hi hj
      rw [hP i j hj (not_lt.1 hi), Matrix.one_apply_ne hne]
    · have := congrFun (congrFun hbr ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN] at this
      rw [dif_pos (show a + ((i : ℕ) - a) < d ∧ a + ((j : ℕ) - a) < d by omega)] at this
      have ei : (⟨a + ((i : ℕ) - a), by omega⟩ : Fin d) = i := Fin.ext (by simp; omega)
      have ej : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin d) = j := Fin.ext (by simp; omega)
      rw [ei, ej] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp only [Fin.ext_iff]
      split_ifs with h1 h2 h2 <;> first | rfl | omega

open scoped Classical in

theorem res_one_one_eq {d a : ℕ} (had : a ≤ d) (χ : Gn g d → ℂ) :
    res a (d - a) χ 1 1 =
      ((g : ℂ) ^ (a * (d - a)))⁻¹ * ∑ u : unipRadical (ZMod g) (twoBlocks d a), χ u := by
  unfold res
  congr 1
  rw [← Finset.sum_filter]
  refine Finset.sum_subtype _ (fun x => ?_) χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Units.val_one]
  exact (mem_unipRadical_twoBlocks_iff had x).symm

open scoped Classical in

theorem res_character_eq_zero_iff {d a : ℕ} (had : a ≤ d) (V : FDRep ℂ (Gn g d)) :
    res a (d - a) (fun x => V.character x) 1 1 = 0 ↔
      ∀ v : V, (∀ u ∈ unipRadical (ZMod g) (twoBlocks d a), V.ρ u v = v) → v = 0 := by
  rw [res_one_one_eq had, mul_eq_zero]
  have hg : ((g : ℂ) ^ (a * (d - a)))⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero))
  simp only [hg, false_or]
  have h := GlobalTheory.GoodTypeGeneric.sum_character_eq_zero_iff
    (V.ρ.comp (unipRadical (ZMod g) (twoBlocks d a)).subtype)
  have e : ∀ u : unipRadical (ZMod g) (twoBlocks d a),
      Representation.character (V.ρ.comp (unipRadical (ZMod g) (twoBlocks d a)).subtype) u = V.character u := fun u => rfl
  simp only [e] at h
  rw [h]
  constructor
  · intro H v hv
    exact H v fun u => hv u u.2
  · intro H v hv
    exact H v fun u hu => hv ⟨u, hu⟩

def cb (d a : ℕ) : Fin d → Fin 2 := fun i => if (i : ℕ) < a then 0 else 1

theorem val_cb (d a : ℕ) (i : Fin d) : ((cb d a i : Fin 2) : ℕ) = twoBlocks d a i := by
  simp only [cb, twoBlocks]
  split_ifs <;> rfl

theorem mem_unipRadical_of_mem_unip {d a : ℕ} {u : Gn g d} (hu : u ∈ unip (ZMod g) (cb d a)) :
    u ∈ unipRadical (ZMod g) (twoBlocks d a) := by
  obtain ⟨⟨hA, -⟩, hD⟩ := hu
  rw [mem_unipRadical]
  intro i j hij
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases e : cb d a i = cb d a j
  · rw [hD i j e]
    simp
  · have hlt : cb d a j < cb d a i := by
      rw [Fin.lt_iff_val_lt_val, val_cb, val_cb]
      have e' : twoBlocks d a i ≠ twoBlocks d a j := fun h => e (Fin.ext (by rw [val_cb, val_cb, h]))
      omega
    have hne : i ≠ j := fun h => e (by rw [h])
    rw [hA i j hlt, if_neg hne, sub_zero]

theorem glEquiv_mem_unip {d a s : ℕ} (b : Fin d → Fin s) (z : Fin s) (hz : ∀ i, z ≤ b i) (σ : Fin d ≃ Fin d)
    (hσ : ∀ k : Fin d, (k : ℕ) < a ↔ b (σ k) = z) {u : Gn g d} (hu : u ∈ unipRadical (ZMod g) (twoBlocks d a)) :
    glEquiv (ZMod g) σ u ∈ unip (ZMod g) b := by
  have htb : ∀ i, twoBlocks d a (σ.symm i) = if b i = z then 0 else 1 := by
    intro i
    have h := hσ (σ.symm i)
    rw [Equiv.apply_symm_apply] at h
    simp only [twoBlocks]
    by_cases hb : b i = z
    · simp [hb, h.2 hb]
    · simp [hb, mt h.1 hb]
  have hent : ∀ w : Gn g d, w ∈ unipRadical (ZMod g) (twoBlocks d a) → ∀ i j, (b j = z ∨ b i ≠ z) →
      ((glEquiv (ZMod g) σ w : Gn g d) : Mt g d) i j = if i = j then 1 else 0 := by
    intro w hw i j hij
    rw [Formalism.L2.PT.coe_glEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]
    have h0 := (mem_unipRadical.1 hw) (σ.symm i) (σ.symm j) (by
      rw [htb, htb]
      rcases hij with h | h
      · by_cases h' : b j = z <;> simp [h, h']
      · by_cases h' : b j = z <;> simp [h, h'])
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply] at h0
    rw [h0]
    simp [σ.symm.injective.eq_iff]
  have hlt : ∀ i j, b j < b i → b i ≠ z := fun i j h e => by
    have := hz j
    rw [e] at h
    exact absurd (lt_of_le_of_lt this h) (lt_irrefl _)
  have hne : ∀ i j : Fin d, b j < b i → i ≠ j := fun i j h e => by rw [e] at h; exact lt_irrefl _ h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j h
    rw [hent u hu i j (Or.inr (hlt i j h)), if_neg (hne i j h)]
  · intro i j h
    rw [← map_inv, hent u⁻¹ (inv_mem hu) i j (Or.inr (hlt i j h)), if_neg (hne i j h)]
  · intro i j h
    rw [hent u hu i j (by by_cases e : b i = z <;> simp_all)]

theorem exists_perm_first {d s : ℕ} (b : Fin d → Fin s) (z : Fin s) :
    ∃ σ : Fin d ≃ Fin d, ∀ k : Fin d, (k : ℕ) < Fintype.card {i // b i = z} ↔ b (σ k) = z := by
  classical
  set a := Fintype.card {i // b i = z} with ha
  have had : a ≤ d := (Fintype.card_subtype_le _).trans (by simp)
  have hca : Fintype.card {k : Fin d // (k : ℕ) < a} = a := by
    rw [Fintype.card_congr (show {k : Fin d // (k : ℕ) < a} ≃ Fin a from
      { toFun := fun k => ⟨k.1, k.2⟩
        invFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 had⟩, i.2⟩
        left_inv := fun k => rfl
        right_inv := fun i => rfl }), Fintype.card_fin]
  let e1 : {k : Fin d // (k : ℕ) < a} ≃ {i // b i = z} := Fintype.equivOfCardEq (by rw [hca])
  let e2 : {k : Fin d // ¬ (k : ℕ) < a} ≃ {i // ¬ b i = z} := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hca])
  refine ⟨((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))), fun k => ?_⟩
  by_cases hk : (k : ℕ) < a
  · have e : ((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
        ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))) k = (e1 ⟨k, hk⟩ : Fin d) := by
      simp only [Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_pos (p := fun k : Fin d => (k : ℕ) < a) hk]
      rfl
    rw [e]
    exact ⟨fun _ => (e1 ⟨k, hk⟩).2, fun _ => hk⟩
  · have e : ((Equiv.sumCompl fun k : Fin d => (k : ℕ) < a).symm.trans
        ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun i => b i = z))) k = (e2 ⟨k, hk⟩ : Fin d) := by
      simp only [Equiv.trans_apply]
      rw [Equiv.sumCompl_symm_apply_of_neg (p := fun k : Fin d => (k : ℕ) < a) hk]
      rfl
    rw [e]
    exact ⟨fun h => absurd h hk, fun h => absurd h (e2 ⟨k, hk⟩).2⟩

end GlobalTheory.CuspCharRep

namespace GlobalTheory.CuspCharRep

open Formalism.IrreducibleCountingLemmas.TYPES GlobalTheory.GLq GlobalTheory.FiniteGL

theorem isCusp_character_iff_isCuspidal : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))),
    1 ≤ d → CategoryTheory.Simple V →
      (GlobalTheory.GLq.IsCusp (fun x => V.character x) ↔ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V) := by
  intro g _ d V hd hV
  unfold GlobalTheory.GLq.IsCusp
  constructor
  · rintro ⟨-, -, hres⟩ s b hb hs v hv
    let z : Fin s := ⟨0, by omega⟩
    have hz : ∀ i, z ≤ b i := fun i => show (0 : ℕ) ≤ (b i : ℕ) from Nat.zero_le _
    obtain ⟨σ, hσ⟩ := exists_perm_first b z
    have ha0 : 0 < Fintype.card {i // b i = z} :=
      Fintype.card_pos_iff.2 ⟨⟨(hb z).choose, (hb z).choose_spec⟩⟩
    have had : Fintype.card {i // b i = z} < d := by
      obtain ⟨j, hj⟩ := hb ⟨1, by omega⟩
      have h := Fintype.card_subtype_lt (p := fun i => b i = z) (x := j)
        (by rw [hj]; simp [Fin.ext_iff, z])
      simpa using h
    have hw := (res_character_eq_zero_iff had.le V).1 (hres _ ha0 had)
    let P := GlobalTheory.SerOSys.TranspLabel.permGL (K := ZMod g) σ
    have key : V.ρ P⁻¹ v = 0 := hw _ fun u hu => by
      have h1 := hv _ (glEquiv_mem_unip b z hz σ hσ hu)
      rw [GlobalTheory.SerOSys.TranspLabel.glEquiv_perm] at h1
      calc V.ρ u (V.ρ P⁻¹ v) = V.ρ (P⁻¹ * (P * u * P⁻¹)) v := by
            rw [show P⁻¹ * (P * u * P⁻¹) = u * P⁻¹ by group, map_mul, Module.End.mul_apply]
        _ = V.ρ P⁻¹ v := by rw [map_mul, Module.End.mul_apply, h1]
    calc v = V.ρ (P * P⁻¹) v := by rw [mul_inv_cancel, map_one, Module.End.one_apply]
      _ = 0 := by rw [map_mul, Module.End.mul_apply, key, map_zero]
  · intro hc
    refine ⟨by omega, ⟨V, hV, fun _ => rfl⟩, fun a ha had => ?_⟩
    rw [res_character_eq_zero_iff had.le V]
    intro v hv
    refine hc 2 (cb d a) ?_ le_rfl v fun u hu => hv u (mem_unipRadical_of_mem_unip hu)
    intro k
    fin_cases k
    · exact ⟨⟨0, by omega⟩, by simp [cb, ha]⟩
    · exact ⟨⟨a, had⟩, by simp [cb]⟩

end GlobalTheory.CuspCharRep
