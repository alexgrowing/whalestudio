import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.C
open Formalism.L2.Th1.G
open Formalism.L2.Th1.G.PairedSquareConstantCoefficients
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

theorem GramSeries_proof : GramSeries := by
  intro K _ n m _ _ c A
  rw [linSub_sqSum]
  simp only [sq, Finset.sum_mul, Finset.mul_sum, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

namespace GramFrameCompositionLinFacts

section Alg

variable {K : Type} [Field K]

theorem linSub_linSub {n m p : Type} [Finite n] [Fintype m] [Fintype p] (A : n → m → K)
    (B : m → p → K) (f : MvPowerSeries n K) :
    linSub B (linSub A f) = linSub (fun i x => ∑ w, A i w * B w x) f := by
  unfold linSub
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_lin A) (hasSubst_lin B)]
  congr 1
  funext i
  rw [← linSub, ← linSubHom_apply, map_sum]
  simp only [map_mul, linSubHom_apply, linSub_X]
  have hc : ∀ w, linSubHom B (MvPowerSeries.C (A i w)) = MvPowerSeries.C (A i w) := fun w => by
    rw [linSubHom_apply, linSub_C]
  simp only [hc, Finset.mul_sum, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finset.sum_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [linSub_C]
  ring

theorem hasSubst_block {ι B : Type} [Finite ι] (k : B) :
    MvPowerSeries.HasSubst (fun i : ι => (MvPowerSeries.X (k, i) : MvPowerSeries (B × ι) K)) := by
  have hs : MvPowerSeries.HasSubst (fun i : ι => (MvPowerSeries.X (k, i) : MvPowerSeries (B × ι) K)) := by
    classical
    refine ⟨fun s => by simp, fun dd => ?_⟩
    refine Set.Subsingleton.finite ?_
    intro s hs t ht
    by_contra hne
    apply hs
    rw [MvPowerSeries.coeff_X, if_neg]
    rintro rfl
    apply ht
    rw [MvPowerSeries.coeff_X, if_neg]
    intro h
    exact hne (Prod.ext_iff.mp (Finsupp.single_left_injective one_ne_zero h)).2
    all_goals simp_all
  exact hs

theorem inBlock_C {ι B : Type} (k : B) (r : K) :
    inBlock k (MvPowerSeries.C r : MvPowerSeries ι K) = MvPowerSeries.C r := by
  have hs : MvPowerSeries.HasSubst (fun i : ι => (MvPowerSeries.X (k, i) : MvPowerSeries (B × ι) K)) := by
    classical
    refine ⟨fun s => by simp, fun dd => ?_⟩
    refine Set.Subsingleton.finite ?_
    intro s hs t ht
    by_contra hne
    apply hs
    rw [MvPowerSeries.coeff_X, if_neg]
    rintro rfl
    apply ht
    rw [MvPowerSeries.coeff_X, if_neg]
    intro h
    exact hne (Prod.ext_iff.mp (Finsupp.single_left_injective one_ne_zero h)).2
  unfold inBlock
  rw [← MvPowerSeries.coe_substAlgHom hs]
  first
    | exact (MvPowerSeries.substAlgHom hs).commutes r
    | simpa using (MvPowerSeries.substAlgHom hs).commutes r
    | simp [← MvPowerSeries.algebraMap_apply']

theorem inBlock_X {ι B : Type} [Finite ι] (k : B) (i : ι) :
    inBlock k (MvPowerSeries.X i : MvPowerSeries ι K) = MvPowerSeries.X (k, i) := by
  have hs : MvPowerSeries.HasSubst (fun i : ι => (MvPowerSeries.X (k, i) : MvPowerSeries (B × ι) K)) := by
    classical
    refine ⟨fun s => by simp, fun dd => ?_⟩
    refine Set.Subsingleton.finite ?_
    intro s hs t ht
    by_contra hne
    apply hs
    rw [MvPowerSeries.coeff_X, if_neg]
    rintro rfl
    apply ht
    rw [MvPowerSeries.coeff_X, if_neg]
    intro h
    exact hne (Prod.ext_iff.mp (Finsupp.single_left_injective one_ne_zero h)).2
    all_goals simp_all
  unfold inBlock
  exact MvPowerSeries.subst_X hs i

theorem inBlock_sum {ι B α : Type} (k : B) (s : Finset α) (f : α → MvPowerSeries ι K) :
    inBlock k (∑ a ∈ s, f a) = ∑ a ∈ s, inBlock k (f a) := by
  have hs : MvPowerSeries.HasSubst (fun i : ι => (MvPowerSeries.X (k, i) : MvPowerSeries (B × ι) K)) := by
    classical
    refine ⟨fun s => by simp, fun dd => ?_⟩
    refine Set.Subsingleton.finite ?_
    intro s hs t ht
    by_contra hne
    apply hs
    rw [MvPowerSeries.coeff_X, if_neg]
    rintro rfl
    apply ht
    rw [MvPowerSeries.coeff_X, if_neg]
    intro h
    exact hne (Prod.ext_iff.mp (Finsupp.single_left_injective one_ne_zero h)).2
  unfold inBlock
  rw [← MvPowerSeries.coe_substAlgHom hs]
  exact map_sum (MvPowerSeries.substAlgHom hs) f s

theorem inBlock_smul {ι B : Type} (k : B) (r : K) (f : MvPowerSeries ι K) :
    inBlock k (r • f) = r • inBlock k f := by
  have hs : MvPowerSeries.HasSubst (fun i : ι => (MvPowerSeries.X (k, i) : MvPowerSeries (B × ι) K)) := by
    classical
    refine ⟨fun s => by simp, fun dd => ?_⟩
    refine Set.Subsingleton.finite ?_
    intro s hs t ht
    by_contra hne
    apply hs
    rw [MvPowerSeries.coeff_X, if_neg]
    rintro rfl
    apply ht
    rw [MvPowerSeries.coeff_X, if_neg]
    intro h
    exact hne (Prod.ext_iff.mp (Finsupp.single_left_injective one_ne_zero h)).2
    all_goals simp_all
  unfold inBlock
  exact MvPowerSeries.subst_smul hs r f

def diag4 {n ν : Type} (M : n → ν → K) (w : Fin 4 × n) (y : Fin 4 × ν) : K :=
  if w.1 = y.1 then M w.2 y.2 else 0

theorem gramFrameComposition_form_fact {n ν : Type} [Fintype ν] (M : n → ν → K) (k : Fin 4) (i : n) :
    (∑ y, MvPowerSeries.C (diag4 M (k, i) y) * MvPowerSeries.X y : MvPowerSeries (Fin 4 × ν) K) =
      ∑ x, MvPowerSeries.C (M i x) * MvPowerSeries.X (k, x) := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
  · simp [diag4]
  · intro b _ hb
    simp [diag4, Ne.symm hb]
  · simp

theorem linSub_diag4_inBlock {n ν : Type} [Finite n] [Fintype ν] (M : n → ν → K) (k : Fin 4)
    (T : MvPowerSeries n K) : linSub (diag4 M) (inBlock k T) = inBlock k (linSub M T) := by
  unfold linSub inBlock
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_block k) (hasSubst_lin _),
    MvPowerSeries.subst_comp_subst_apply (hasSubst_lin M) (hasSubst_block k)]
  congr 1
  funext i
  rw [← inBlock, ← linSub, linSub_X, gramFrameComposition_form_fact, inBlock_sum]
  simp only [inBlock_mul, inBlock_C, inBlock_X]

theorem linSub_diag4_tens4 {n ν : Type} [Finite n] [Fintype ν] (M : n → ν → K)
    (T : MvPowerSeries n K) : linSub (diag4 M) (tens4 T) = tens4 (linSub M T) := by
  unfold tens4
  rw [← linSubHom_apply, map_prod]
  simp only [linSubHom_apply, linSub_diag4_inBlock]

theorem pair_row {H : Type} [Fintype H] [DecidableEq H] {N0 N1 : ℕ} (u : H → K)
    (x : Fin 4 × ((Bool × H) × Fin N0 × Fin N1)) :
    (∑ y : Fin 4 × ((Bool × H) × Fin N0 × Fin N1), MvPowerSeries.C
        (if x.1 = y.1 ∧ x.2.1.2 = y.2.1.2 ∧ x.2.2 = y.2.2 ∧ x.2.1.1 ≠ y.2.1.1 then u x.2.1.2 else 0) *
        MvPowerSeries.X x * MvPowerSeries.X y :
      MvPowerSeries (Fin 4 × ((Bool × H) × Fin N0 × Fin N1)) K) =
      MvPowerSeries.C (u x.2.1.2) * MvPowerSeries.X x *
        MvPowerSeries.X (x.1, ((!x.2.1.1, x.2.1.2), x.2.2)) := by
  classical
  rw [Finset.sum_eq_single (x.1, ((!x.2.1.1, x.2.1.2), x.2.2))]
  · obtain ⟨a, ⟨⟨b, h⟩, p⟩⟩ := x
    simp
  · rintro ⟨a', ⟨⟨b', h'⟩, p'⟩⟩ _ hne
    obtain ⟨a, ⟨⟨b, h⟩, p⟩⟩ := x
    rw [if_neg]
    · simp
    rintro ⟨rfl, rfl, rfl, hb⟩
    apply hne
    cases b <;> cases b' <;> simp_all
  · simp

theorem pair_form {H : Type} [Fintype H] [DecidableEq H] {N0 N1 : ℕ} (u : H → K) :
    (∑ x : Fin 4 × ((Bool × H) × Fin N0 × Fin N1), ∑ y : Fin 4 × ((Bool × H) × Fin N0 × Fin N1),
      MvPowerSeries.C
        (if x.1 = y.1 ∧ x.2.1.2 = y.2.1.2 ∧ x.2.2 = y.2.2 ∧ x.2.1.1 ≠ y.2.1.1 then u x.2.1.2 else 0) *
        MvPowerSeries.X x * MvPowerSeries.X y :
      MvPowerSeries (Fin 4 × ((Bool × H) × Fin N0 × Fin N1)) K) =
      MvPowerSeries.C 2 * ∑ a : Fin 4, inBlock a (betaPair H N0 N1 u) := by
  simp only [pair_row]
  unfold betaPair
  simp only [inBlock_sum, inBlock_mul, inBlock_C, inBlock_X]
  rw [show (MvPowerSeries.C 2 : MvPowerSeries (Fin 4 × ((Bool × H) × Fin N0 × Fin N1)) K) = 2 from map_ofNat _ 2]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.mul_sum, ← Finset.sum_add_distrib, Bool.not_true, Bool.not_false]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun p0 _ => Finset.sum_congr rfl fun p1 _ => ?_
  ring

def quadForm {m : Type} [Fintype m] (q : m → m → K) : MvPowerSeries m K :=
  ∑ x, ∑ y, MvPowerSeries.C (q x y) * MvPowerSeries.X x * MvPowerSeries.X y

theorem cc_quadForm {m : Type} [Fintype m] (q : m → m → K) :
    MvPowerSeries.constantCoeff (quadForm q) = 0 := by
  unfold quadForm
  simp [map_sum, map_mul]

theorem jetsIn_quadForm {R : Subring K} {m : Type} [Fintype m] {q : m → m → K}
    (hq : ∀ x y, q x y ∈ R) : JetsIn R (quadForm q) := by
  intro κ
  refine R.mul_mem (natCast_mem R _) ?_
  classical
  unfold quadForm
  simp only [map_sum]
  refine R.sum_mem fun x _ => R.sum_mem fun y _ => ?_
  rw [mul_assoc, MvPowerSeries.coeff_C_mul, MvPowerSeries.X_def, MvPowerSeries.X_def,
    MvPowerSeries.monomial_mul_monomial, MvPowerSeries.coeff_monomial]
  split_ifs
  · simpa using hq x y
  · simp

variable [CharZero K]

theorem gramFrameComposition_mvExp_fact {ι : Type} [Finite ι] {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    tens4 (mvExp f) = mvExp (∑ k : Fin 4, inBlock k f) := by
  classical
  have hcc : ∀ k : Fin 4, MvPowerSeries.constantCoeff (inBlock k f) = 0 := fun k => by
    have h := Formalism.L2.Th1.G.HurwitzJetIntegrality.coeff_inBlock_embDomain k f 0
    rw [Finsupp.embDomain_zero] at h
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  obtain ⟨h0, _, hadd, _⟩ := formalExpLaws' K (Fin 4 × ι)
  unfold tens4
  simp only [inBlock_mvExp _ hf]
  have key : ∀ s : Finset (Fin 4),
      ∏ k ∈ s, mvExp (inBlock k f) = mvExp (∑ k ∈ s, inBlock k f) := by
    intro s
    refine Finset.induction_on s (by simp [h0]) ?_
    intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, hadd _ _ (hcc a) ?_]
    rw [map_sum]
    exact Finset.sum_eq_zero fun k _ => hcc k
  exact key Finset.univ

end Alg

end GramFrameCompositionLinFacts

open GramFrameCompositionLinFacts

theorem ShapeLin_proof : ShapeLin := by
  intro K _ _ _ l linv ph d hlog h1 hph hS hd h2 n _ T γ G hG hT H _ _ N0 N1 M Cm u th q hCm hγ hth hq hgram
  classical
  have hmem : ∀ x : K, x ∈ Formalism.G.unitBall K ↔ ‖x‖ ≤ 1 := fun x => Formalism.ELL.SubstitutionCoefficientCongruence.mem_unitBall
  obtain ⟨h0, _, hadd, _⟩ := formalExpLaws' K ((Bool × H) × Fin N0 × Fin N1)
  obtain ⟨h04, _, hadd4, _⟩ := formalExpLaws' K (Fin 4 × ((Bool × H) × Fin N0 × Fin N1))
  have hccβ : MvPowerSeries.constantCoeff (betaPair H N0 N1 u) = 0 := by
    unfold betaPair
    simp
  have hccB : ∀ a : Fin 4, MvPowerSeries.constantCoeff (inBlock a (betaPair H N0 N1 u)) = 0 := fun a => by
    have h := Formalism.L2.Th1.G.HurwitzJetIntegrality.coeff_inBlock_embDomain a (betaPair H N0 N1 u) 0
    rw [Finsupp.embDomain_zero] at h
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hccβ]
  have hccbe : MvPowerSeries.constantCoeff (∑ a : Fin 4, inBlock a (betaPair H N0 N1 u)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun a _ => hccB a
  have hccs : ∀ {ι : Type} (r : K) (f : MvPowerSeries ι K), MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (r • f) = 0 := fun r f hf => by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]
  have hQ : JetsIntegral (quadForm q) :=
    (jetsInNorm K _ _).mpr (jetsIn_quadForm (fun x y => (hmem _).mpr (hq x y)))
  have hgram' : linSub Cm (sqSum (fun _ => (1 : K))) =
      MvPowerSeries.C 2 * ∑ a : Fin 4, inBlock a (betaPair H N0 N1 u) + MvPowerSeries.C th * quadForm q := by
    rw [GramSeries_proof]
    simp only [one_mul, hgram, map_add, add_mul, Finset.sum_add_distrib]
    rw [pair_form]
    congr 1
    unfold quadForm
    simp only [map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  obtain ⟨J, hJ, hJeq⟩ := shapeOrth K l linv ph d hlog h1 hph hS (Fin 4 × n) (fun _ => (1 : K))
    (fun _ => by simp) G hG
  have hS0th : ‖jet l ph 2 * th‖ ≤ 1 := by
    rw [norm_mul]
    have hdpos : 0 < ‖(d : K)‖ := norm_pos_iff.mpr hd
    calc ‖jet l ph 2‖ * ‖th‖ ≤ ‖(d : K)‖ ^ (-(1 / 2 : ℝ)) * ‖(d : K)‖ ^ (1 / 2 : ℝ) :=
          mul_le_mul hS.1 hth (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = 1 := by rw [← Real.rpow_add hdpos]; simp
  obtain ⟨sg, hsg, hsgeq⟩ := shapeCong K (Fin 4 × n) (Fin 4 × ((Bool × H) × Fin N0 × Fin N1))
    (jet l ph 2) th (fun _ => (1 : K)) Cm (∑ a : Fin 4, inBlock a (betaPair H N0 N1 u)) (quadForm q)
    h2 hS0th hCm hccbe (cc_quadForm q) hQ hgram' J hJ
  have hdiag : (fun i x => ∑ w, γ i w * Cm w x) = diag4 M := by
    funext ⟨a, i⟩ ⟨b, x⟩
    rw [hγ]
    rfl
  have htens : tens4 (linSub M T) =
      mvExp ((-(jet l ph 2)) • ∑ a : Fin 4, inBlock a (betaPair H N0 N1 u)) * sg := by
    rw [← hsgeq, ← hJeq, ← hT, linSub_linSub, hdiag, linSub_diag4_tens4]
  have hsm : ∑ k : Fin 4, inBlock k (jet l ph 2 • betaPair H N0 N1 u) =
      jet l ph 2 • ∑ a : Fin 4, inBlock a (betaPair H N0 N1 u) := by
    rw [Finset.smul_sum]
    simp only [inBlock_smul]
  refine ⟨linSub M T * mvExp (jet l ph 2 • betaPair H N0 N1 u), ?_, ?_⟩
  · rw [jetsInNorm]
    refine jetsFourth K _ _ _ ?_ ?_
    · intro c hc
      rw [hmem] at hc ⊢
      rw [norm_pow] at hc
      by_contra hlt
      push_neg at hlt
      have : 1 < ‖c‖ ^ 4 := one_lt_pow₀ hlt (by norm_num)
      linarith
    · rw [← jetsInNorm, tensor_four_mul, htens, gramFrameComposition_mvExp_fact (hccs _ _ hccβ), hsm]
      have e : mvExp ((-(jet l ph 2)) • ∑ a : Fin 4, inBlock a (betaPair H N0 N1 u)) *
          mvExp (jet l ph 2 • ∑ a : Fin 4, inBlock a (betaPair H N0 N1 u)) = 1 := by
        rw [← hadd4 _ _ (hccs _ _ hccbe) (hccs _ _ hccbe), neg_smul, neg_add_cancel, h04]
      rw [mul_right_comm, e, one_mul]
      exact hsg
  · show linSub M T = mvExp ((-(jet l ph 2)) • betaPair H N0 N1 u) *
      (linSub M T * mvExp (jet l ph 2 • betaPair H N0 N1 u))
    rw [mul_left_comm, ← hadd _ _ (hccs _ _ hccβ) (hccs _ _ hccβ), neg_smul, neg_add_cancel, h0, mul_one]

end Formalism.L2.Th1.GD
