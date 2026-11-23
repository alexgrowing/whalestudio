import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateGramSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceCompPosOfAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementCentralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCasimirElementMulPosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.CasimirOrder

open Matrix

variable {O : Type} [Ring O] {r : ℕ}

theorem exists_W_of_casimir (x : Module.Basis (Fin r) ℤ O) (s : O →+ O) (φ : O →+ ℤ)
    (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a)
    (hp : ∀ a, a ≠ 0 → 0 < φ (s a * a))
    (hcen : ∀ a, a * casimir x s φ = casimir x s φ * a)
    (hpos : ∀ u, u ≠ 0 → 0 < φ (s (casimir x s φ * u) * u)) :
    ∃ (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), ((W + Wᵀ).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧
      ∑ i, ∑ j, W i j • (s (x i) * x j) = (d : O) := by
  classical
  set C := casimir x s φ with hC
  have sC : s C = C := casimir_star hs hss hφs
  set s' : O →+ O := s.comp (AddMonoidHom.mulLeft C) with hs'
  have hs'a : ∀ u, s' u = s u * C := fun u => by simp [hs', hs, sC]
  have b'symm : ∀ u v, form s' φ u v = form s' φ v u := by
    intro u v
    simp only [form_apply, hs'a]
    rw [← hφs (s u * C * v), hs, hs, hss, sC, ← _root_.mul_assoc]
  have bsymm := form_symm hs hss hφs
  set G := gram (⇑x) s φ with hG
  set G' := gram (⇑x) s' φ with hG'
  have hGpd : (G.map (Int.cast : ℤ → ℝ)).PosDef :=
    posDef_gram x (form s φ) bsymm fun w hw => by simpa using hp w hw
  have hG'pd : (G'.map (Int.cast : ℤ → ℝ)).PosDef := by
    refine posDef_gram x (form s' φ) b'symm fun w hw => ?_
    have h := hpos w hw
    simp only [form_apply, hs'a]
    rwa [hs, sC] at h
  have hδ : 0 < G.det := by
    have := hGpd.det_pos
    rw [← Int.cast_det] at this
    exact_mod_cast this
  have hδ' : 0 < G'.det := by
    have := hG'pd.det_pos
    rw [← Int.cast_det] at this
    exact_mod_cast this
  set A := G.adjugate with hA
  set A' := G'.adjugate with hA'
  have hAs : ∀ i j, A i j = A j i := adjugate_gram_symm hs hss hφs
  have hG't : G'ᵀ = G' := by
    ext i j
    simp only [transpose_apply, hG', gram_eq, of_apply]
    exact b'symm _ _
  have hA's : ∀ i j, A' i j = A' j i := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose G')
    rw [hG't] at h
    simpa using h.symm
  have L1' : ∀ v, G'.det • v = ∑ i, ∑ j, (A' i j * φ (s (x i) * C * v)) • x j := by
    intro v
    have h := det_smul_eq_sum x (form s' φ) b'symm v
    rw [← gram_eq] at h
    simpa only [form_apply, hs'a] using h
  have L1 : ∀ v, G.det • v = ∑ i, ∑ j, (A i j * φ (s (x i) * v)) • x j := by
    intro v
    have h := det_smul_eq_sum x (form s φ) bsymm v
    rw [← gram_eq] at h
    simpa only [form_apply] using h
  set C₁ : O := ∑ i, ∑ j, A' i j • (s (x i) * x j) with hC₁
  have lhs : G'.det • C = ∑ k, ∑ l, ∑ i, ∑ j,
      (A k l * (A' i j * φ (s (x i) * C * x l))) • (s (x k) * x j) := by
    conv_lhs => rw [hC, casimir]
    simp only [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm, ← mul_smul_comm, L1' (x l), Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, smul_smul]
  have rhs : C * (G.det • C₁) = ∑ i, ∑ j, ∑ a, ∑ b,
      (A' i j * (A a b * φ (s (x a) * (C * x i)))) • (s (x b) * x j) := by
    rw [hC₁, Finset.smul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : C * (G.det • (A' i j • (s (x i) * x j))) = A' i j • (s (G.det • (C * x i)) * x j) := by
      rw [mul_smul_comm, mul_smul_comm, map_zsmul, smul_mul_assoc, hs, sC, smul_comm, ← _root_.mul_assoc,
        ← hcen]
    rw [e, L1 (C * x i)]
    simp only [map_sum, map_zsmul, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
  have swap4 : ∀ f : Fin r → Fin r → Fin r → Fin r → O,
      ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ i, ∑ j, ∑ l, ∑ k, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ i, ∑ j, f k l i j = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ l, ∑ k, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have key : G'.det • C = C * (G.det • C₁) := by
    rw [lhs, rhs, swap4]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    have hb := b'symm (x i) (x l)
    simp only [form_apply, hs'a] at hb
    rw [hAs l k, ← _root_.mul_assoc (s (x l)), hb]
    ring_nf
  have hC1 : G.det • C₁ = ((G'.det : ℤ) : O) := by
    by_contra hne
    have hw : ((G'.det : ℤ) : O) - G.det • C₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    have h := hpos _ hw
    have h0 : C * (((G'.det : ℤ) : O) - G.det • C₁) = 0 := by
      rw [mul_sub, ← key, ← Int.cast_comm, ← zsmul_eq_mul, sub_self]
    rw [h0, map_zero, zero_mul, map_zero] at h
    exact lt_irrefl _ h
  refine ⟨G.det • A', G'.det.toNat, ?_, by omega, ?_⟩
  · have hadj : (G'.map (Int.cast : ℤ → ℝ)).adjugate = A'.map Int.cast := by
      rw [hA']; exact ((Int.castRingHom ℝ).map_adjugate G').symm
    have e : ((G.det • A' + (G.det • A')ᵀ).map (Int.cast : ℤ → ℝ)) =
        ((2 * G.det : ℤ) : ℝ) • (G'.map (Int.cast : ℤ → ℝ)).adjugate := by
      rw [hadj]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
        hA's j i]
      push_cast; ring
    rw [e]
    exact (adjugate_posDef hG'pd).smul (by exact_mod_cast (by omega : (0 : ℤ) < 2 * G.det))
  · have e : ∑ i, ∑ j, (G.det • A') i j • (s (x i) * x j) = G.det • C₁ := by
      rw [hC₁, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul, mul_smul]
    rw [e, hC1, ← Int.cast_natCast, Int.toNat_of_nonneg hδ'.le]

end GlobalTheory.CasimirOrder

namespace GlobalTheory.CasimirOrder

variable {p : ℕ} [Fact p.Prime]

def htStar (D : Datum p) : D.O →+ D.O :=
  (MulOpposite.opAddEquiv.symm.toAddMonoidHom).comp D.star.toAddMonoidHom

@[simp] theorem htStar_apply (D : Datum p) (a : D.O) : htStar D a = (D.star a).unop := rfl

noncomputable def htTrace (D : Datum p) : D.O →+ ℤ where
  toFun a := LinearMap.trace ℤ D.La (DistribMulAction.toLinearMap ℤ D.La a)
  map_zero' := by
    have : DistribMulAction.toLinearMap ℤ D.La (0 : D.O) = 0 := by ext y; exact zero_smul _ _
    rw [this, map_zero]
  map_add' a b := by
    have : DistribMulAction.toLinearMap ℤ D.La (a + b) =
        DistribMulAction.toLinearMap ℤ D.La a + DistribMulAction.toLinearMap ℤ D.La b := by
      ext y; exact add_smul _ _ _
    rw [this, map_add]

theorem htTrace_mul_comm (D : Datum p) (a b : D.O) : htTrace D (a * b) = htTrace D (b * a) := by
  haveI := D.freeLa; haveI := D.finLa
  have hm : ∀ a b : D.O, DistribMulAction.toLinearMap ℤ D.La (a * b) =
      DistribMulAction.toLinearMap ℤ D.La a * DistribMulAction.toLinearMap ℤ D.La b := by
    intro a b; ext y; exact mul_smul _ _ _
  show LinearMap.trace ℤ D.La _ = LinearMap.trace ℤ D.La _
  rw [hm, hm, LinearMap.trace_mul_comm]

noncomputable def htForm (D : Datum p) : D.O →+ ℤ := htTrace D + (htTrace D).comp (htStar D)

theorem htStar_mul (D : Datum p) (a b : D.O) : htStar D (a * b) = htStar D b * htStar D a := by
  simp [map_mul]

theorem htStar_star (D : Datum p) (a : D.O) : htStar D (htStar D a) = a := by
  simpa using D.star_star a

theorem exists_W_datum (D : Datum p) : ∃ (r : ℕ) (x : Module.Basis (Fin r) ℤ D.O) (W : Matrix (Fin r) (Fin r) ℤ)
    (d : ℕ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧
      ∑ i, ∑ j, W i j • (htStar D (x i) * x j) = (d : D.O) := by
  haveI := D.freeO; haveI := D.finO
  have hs := htStar_mul D
  have hss := htStar_star D
  have hφs : ∀ a, htForm D (htStar D a) = htForm D a := by
    intro a; simp only [htForm, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hss, add_comm]
  have hφc : ∀ a b, htForm D (a * b) = htForm D (b * a) := by
    intro a b
    simp only [htForm, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hs]
    rw [htTrace_mul_comm D a b, htTrace_mul_comm D (htStar D b)]
  have hp : ∀ a, a ≠ 0 → 0 < htForm D (htStar D a * a) := by
    intro a ha
    simp only [htForm, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, hs, hss]
    have h : 0 < LinearMap.trace ℤ D.La (DistribMulAction.toLinearMap ℤ D.La (a * (D.star a).unop)) := by
      first
        | exact GlobalTheory.UPel.HT.trace_mul_star_pos p D a ha
        | exact GlobalTheory.UPel.HT.trace_mul_star_pos D a ha
        | exact GlobalTheory.UPel.HT.trace_mul_star_pos a ha
    have h' : htTrace D (htStar D a * a) = htTrace D (a * htStar D a) := htTrace_mul_comm D _ _
    have h'' : 0 < htTrace D (a * htStar D a) := h
    omega
  exact ⟨_, Module.finBasis ℤ D.O, exists_W_of_casimir (Module.finBasis ℤ D.O) (htStar D) (htForm D) hs hss hφs hp
    (GlobalTheory.T.integralCasimirElement_central _ _ _ hs hss hφc hφs hp) (GlobalTheory.T.integralCasimirElement_mul_pos _ _ _ hs hss hφc hφs hp)⟩

end GlobalTheory.CasimirOrder

theorem GlobalTheory.CasimirOrder.exists_posdef_relation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ (r : ℕ) (e : Fin r → D.Oᵐᵒᵖ) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), Submodule.span ℤ (Set.range e) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧ ∑ i, ∑ j, W i j • (e j * MulOpposite.op ((D.star (e i).unop).unop)) = (d : D.Oᵐᵒᵖ) := by
  intro p _ D
  obtain ⟨r, x, W, d, hW, hd, hsum⟩ := GlobalTheory.CasimirOrder.exists_W_datum D
  refine ⟨_, fun i => MulOpposite.op (x i), W, d, ?_, hW, hd, ?_⟩
  · have h := x.mulOpposite.span_eq
    convert h using 3
    all_goals first
      | exact Subsingleton.elim _ _
      | (funext i; simp)
  · rw [← MulOpposite.op_natCast, ← hsum, Finset.op_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.op_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulOpposite.op_smul, MulOpposite.op_mul]
    rfl
