import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeValuesSameParameters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.TjChar

open GlobalTheory.WeylGL (tor tor_val tor_add tor_const_comm IntM intM_tor intM_doset)

theorem sum_ite_lt (n m : ℕ) : ∑ j : Fin n, (if (j : ℕ) < m then (1 : ℤ) else 0) = min (n : ℤ) m := by
  rw [Finset.sum_boole, Fin.card_filter_val_lt]
  push_cast
  rfl

theorem antitone_eq {n k : ℕ} {a : Fin n → ℤ} (ha : Antitone a) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i, a i ≤ 1)
    (hs : ∑ i, a i = (k : ℤ)) (i : Fin n) : a i = if (i : ℕ) < k then 1 else 0 := by
  have hi := i.2
  have hc : a i = 0 ∨ a i = 1 := by
    have := h0 i
    have := h1 i
    omega
  rcases hc with hc | hc
  · have hle : ∑ j, a j ≤ ∑ j : Fin n, (if (j : ℕ) < (i : ℕ) then (1 : ℤ) else 0) := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hj
      · exact h1 j
      · have : a j ≤ a i := ha (Fin.le_def.2 (by omega))
        omega
    rw [hs, sum_ite_lt] at hle
    have : k ≤ (i : ℕ) := by omega
    rw [hc, if_neg (by omega)]
  · have hle : ∑ j : Fin n, (if (j : ℕ) < (i : ℕ) + 1 then (1 : ℤ) else 0) ≤ ∑ j, a j := by
      refine Finset.sum_le_sum fun j _ => ?_
      split_ifs with hj
      · have : a i ≤ a j := ha (Fin.le_def.2 (by omega))
        omega
      · exact h0 j
    rw [hs, sum_ite_lt] at hle
    have : (i : ℕ) < k := by
      push_cast at hle
      omega
    rw [hc, if_pos this]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {ϖ : w.adicCompletion E}

theorem ordL_eq_of_v {x : w.adicCompletion E} {m : ℤ} (h : Valued.v x = WithZero.exp (-m)) : ordL x = m := by
  have hx : Valued.v x ≠ 0 := by
    rw [h]
    exact WithZero.exp_ne_zero
  have e : WithZero.unzero hx = Multiplicative.ofAdd (-m) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  unfold ordL
  rw [dif_neg hx, e]
  simp

theorem v_zpow_eq (hu : IsUnifV E w ϖ) (m : ℤ) : Valued.v (ϖ ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, hu]
  have : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) := rfl
  rw [this, ← WithZero.exp_zsmul]
  simp

theorem v_prod_zpow (hu : IsUnifV E w ϖ) (a : Fin n → ℤ) (s : Finset (Fin n)) :
    Valued.v (∏ i ∈ s, ϖ ^ a i) = WithZero.exp (-∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, map_mul, ih, v_zpow_eq hu, ← WithZero.exp_add]
    congr 1
    ring

theorem ordL_det (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    ordL (c * tor h0 a * d : GL (Fin n) (w.adicCompletion E)).val.det = ∑ i, a i := by
  apply ordL_eq_of_v
  have h1 : Valued.v c.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hc
  have h2 : Valued.v d.val.det = 1 := GlobalTheory.SphGal.isUnitAt_det_of_mem hd
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, h1, h2, tor_val,
    Matrix.det_diagonal, v_prod_zpow hu]
  simp

theorem tor_inv (h0 : ϖ ≠ 0) (a : Fin n → ℤ) : (tor h0 a)⁻¹ = tor h0 (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← tor_add]
  ext1
  simp [tor_val]

theorem tor_one_val (h0 : ϖ ≠ 0) (x : GL (Fin n) (w.adicCompletion E)) :
    (tor h0 (fun _ => 1) * x : GL (Fin n) (w.adicCompletion E)).val = ϖ • x.val := by
  ext i j
  simp [tor_val, Matrix.diagonal_mul]

theorem intM_iff {c d x y : GL (Fin n) (w.adicCompletion E)} (hc : c ∈ GLint (Fin n) (Ov E w))
    (hd : d ∈ GLint (Fin n) (Ov E w)) (e : x = c * y * d) : IntM x ↔ IntM y :=
  ⟨fun h => intM_doset h ⟨c⁻¹, Subgroup.inv_mem _ hc, d⁻¹, Subgroup.inv_mem _ hd, by rw [e]; group⟩,
    fun h => intM_doset h ⟨c, hc, d, hd, e⟩⟩

theorem isInt_iff (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    IsInt w (c * tor h0 a * d : GL (Fin n) (w.adicCompletion E)).val ↔ ∀ i, 0 ≤ a i :=
  (intM_iff hc hd rfl).trans (intM_tor h0 hu a)

theorem isInt_dual_iff (h0 : ϖ ≠ 0) (hu : IsUnifV E w ϖ) {c d : GL (Fin n) (w.adicCompletion E)}
    (hc : c ∈ GLint (Fin n) (Ov E w)) (hd : d ∈ GLint (Fin n) (Ov E w)) (a : Fin n → ℤ) :
    IsInt w (ϖ • ((c * tor h0 a * d : GL (Fin n) (w.adicCompletion E))⁻¹).val) ↔ ∀ i, a i ≤ 1 := by
  rw [← tor_one_val h0]
  have e : tor h0 (fun _ => 1) * (c * tor h0 a * d)⁻¹ = d⁻¹ * tor h0 ((fun _ => 1) + -a) * c⁻¹ := by
    rw [tor_add, _root_.mul_inv_rev, _root_.mul_inv_rev, tor_inv, ← mul_assoc (tor h0 fun _ => 1) d⁻¹, tor_const_comm]
    group
  have h := (intM_iff (Subgroup.inv_mem _ hd) (Subgroup.inv_mem _ hc) e).trans (intM_tor h0 hu _)
  refine h.trans (forall_congr' fun i => ?_)
  simp

end GlobalTheory.CompanionTheory.CtS.TjChar

namespace GlobalTheory.CompanionTheory.CtS

open GlobalTheory.CompanionTheory.CtS.TjChar in

theorem Tj_eq_ite : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n k : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → k ≤ n → ∀ g : GL (Fin n) (w.adicCompletion E), Tj ℂ n (Ov E w) ϖ k g = if IsInt w g.val ∧ IsInt w (ϖ • (g⁻¹).val) ∧ ordL g.val.det = (k : ℤ) then 1 else 0 := by
  intro E _ _ w n k ϖ hu hk g
  have h0 : ϖ ≠ 0 := fun h => by simp [IsUnifV, h] at hu
  rw [GlobalTheory.WeylGL.Tj_eq h0 k]
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨a, ha, c, hc, d, hd, rfl⟩ := GlobalTheory.WeylGL.cartan h0 hu g
    have ha0 := (isInt_iff h0 hu hc hd a).1 h1
    have ha1 := (isInt_dual_iff h0 hu hc hd a).1 h2
    rw [ordL_det h0 hu hc hd] at h3
    have e : a = fun i : Fin n => if (i : ℕ) < k then 1 else 0 :=
      funext (antitone_eq ha ha0 ha1 h3)
    subst e
    exact GlobalTheory.WeylGL.dosetInd_of_mem ⟨c, hc, d, hd, rfl⟩
  · refine GlobalTheory.WeylGL.dosetInd_of_not ?_
    rintro ⟨c, hc, d, hd, rfl⟩
    refine h ⟨(isInt_iff h0 hu hc hd _).2 fun i => ?_, (isInt_dual_iff h0 hu hc hd _).2 fun i => ?_, ?_⟩
    · split_ifs <;> omega
    · split_ifs <;> omega
    · rw [ordL_det h0 hu hc hd, sum_ite_lt, min_eq_right (by exact_mod_cast hk)]

end GlobalTheory.CompanionTheory.CtS
