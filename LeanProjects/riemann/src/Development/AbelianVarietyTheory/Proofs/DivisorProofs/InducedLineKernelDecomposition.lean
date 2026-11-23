import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorOfCharCentral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeMatrixCharacterLeviBlockExists
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AutomorphicArithmetic.LocalEmbeddings.LineCellScalars

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.CuspBlock GlobalTheory.JacLineSplit

noncomputable section

namespace GlobalTheory.JacLineSplit.Eigen

open GlobalTheory.LeviBlockExponentLocal GlobalTheory.SplitWeil

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem deltaHalf_positionOne {N : ℕ} (h : 2 ≤ N) (x : kˣ) :
    (deltaHalf k (fun j : Fin 3 => Fin (tripSizes 1 (N - 2) N j)) (firstBlockScalar k N x) : ℂ) =
      (absPow k (((N : ℂ) - 1) / 2) x : ℂ) := by
  rw [deltaHalf_apply, Fin.prod_univ_three, firstBlockScalar_apply, firstBlockScalar_apply, firstBlockScalar_apply]
  simp only [if_true, show ((1 : Fin 3) = 0) = False from by decide, show ((2 : Fin 3) = 0) = False from by decide,
    if_false, map_one, mul_one]
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin (tripSizes 1 (N - 2) N 0)) x) = x := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show Matrix.det (Matrix.scalar (Fin 1) (x : k)) = x
    rw [Matrix.det_fin_one]
    simp
  rw [hd]
  have e1 : ∀ n : ℕ, ∀ inst : Fintype (Fin n), @Fintype.card (Fin n) inst = n := fun n inst => by
    convert Fintype.card_fin n
  have hm : modExp (fun j : Fin 3 => Fin (tripSizes 1 (N - 2) N j)) 0 = (N : ℤ) - 1 := by
    unfold modExp
    simp only [Fin.sum_univ_three, Finset.sum_filter, Fintype.card_fin]
    simp [tripSizes]
    omega
  rw [hm]
  push_cast
  rfl

end Lemmas

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem col_outer (a a' : ℕ) (h : 2 ≤ a + a')
    (b : SizeMatrix (fun j : Fin 2 => Fin (![a, a'] j)) (fun j : Fin 3 => Fin (tripSizes 1 (a + a' - 2) (a + a') j)))
    (j : Fin 3) (hj : j ≠ 1) : b.1 0 j + b.1 1 j = 1 := by
  have := b.2.2 j
  simp only [Fin.sum_univ_two, Fintype.card_fin] at this
  rw [this]
  fin_cases j
  · simp [tripSizes]
  · exact absurd rfl hj
  · simp [tripSizes]; omega

private def rowOf (a a' : ℕ)
    (b : SizeMatrix (fun j : Fin 2 => Fin (![a, a'] j)) (fun j : Fin 3 => Fin (tripSizes 1 (a + a' - 2) (a + a') j)))
    (j : Fin 3) : Fin 2 := if b.1 0 j = 1 then 0 else 1

private theorem rowOf_spec (a a' : ℕ) (h : 2 ≤ a + a')
    (b : SizeMatrix (fun j : Fin 2 => Fin (![a, a'] j)) (fun j : Fin 3 => Fin (tripSizes 1 (a + a' - 2) (a + a') j)))
    (j : Fin 3) (hj : j ≠ 1) (i : Fin 2) : b.1 i j = if i = rowOf a a' b j then 1 else 0 := by
  have hc := col_outer a a' h b j hj
  unfold rowOf
  by_cases h0 : b.1 0 j = 1
  · rw [if_pos h0]
    fin_cases i
    · simpa using h0
    · simp; omega
  · rw [if_neg h0]
    fin_cases i
    · simp; omega
    · simp; omega

private theorem sizeMatrix_eq (a a' : ℕ) (h : 2 ≤ a + a')
    (b b' : SizeMatrix (fun j : Fin 2 => Fin (![a, a'] j)) (fun j : Fin 3 => Fin (tripSizes 1 (a + a' - 2) (a + a') j)))
    (h0 : rowOf a a' b 0 = rowOf a a' b' 0) (h2 : rowOf a a' b 2 = rowOf a a' b' 2) : b = b' := by
  have e0 : ∀ i, b.1 i 0 = b'.1 i 0 := fun i => by
    rw [rowOf_spec a a' h b 0 (by decide) i, rowOf_spec a a' h b' 0 (by decide) i, h0]
  have e2 : ∀ i, b.1 i 2 = b'.1 i 2 := fun i => by
    rw [rowOf_spec a a' h b 2 (by decide) i, rowOf_spec a a' h b' 2 (by decide) i, h2]
  apply Subtype.ext
  funext i j
  have r := b.2.1 i
  have r' := b'.2.1 i
  rw [Fin.sum_univ_three] at r r'
  fin_cases j
  · exact e0 i
  · have := e0 i; have := e2 i; simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at *; omega
  · exact e2 i

end Main

private theorem rows_eq_of_exp (a a' : ℕ) (haa : a' < a) (x y x' y' : Fin 2)
    (he : (1 - ((![a, a'] x : ℕ) : ℝ)) + (((![a, a'] y : ℕ) : ℝ) - 1) / 2 =
      (1 - ((![a, a'] x' : ℕ) : ℝ)) + (((![a, a'] y' : ℕ) : ℝ) - 1) / 2) : x = x' ∧ y = y' := by
  have : (a' : ℝ) < a := by exact_mod_cast haa
  fin_cases x <;> fin_cases y <;> fin_cases x' <;> fin_cases y' <;> simp at he ⊢ <;> linarith

private theorem norm_absPow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℂ) (x : kˣ) : ‖(absPow k s x : ℂ)‖ = nabs k x ^ s.re := by
  rw [val_absPow, Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k x)]

private theorem step_scalar {G V U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {ρ : Representation ℂ G V} (A B : Subrepresentation ρ) (σ : Representation ℂ G U)
    (φ : (subQuot A B).Equiv σ) (x : G) (c : ℂ) (hc : ∀ w, σ x w = c • w) :
    ∀ v ∈ A.toSubmodule, ρ x v - c • v ∈ B.toSubmodule := by
  intro v hv
  let xq : A.toSubmodule ⧸ Submodule.comap A.toSubmodule.subtype B.toSubmodule := Submodule.Quotient.mk ⟨v, hv⟩
  have hq : subQuot A B x xq = c • xq := by
    apply φ.toLinearEquiv.injective
    have h1 : φ.toLinearEquiv (subQuot A B x xq) = σ x (φ.toLinearEquiv xq) :=
      Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap x xq
    refine h1.trans ((hc _).trans ?_)
    exact (φ.toLinearEquiv.map_smul _ _).symm
  have h2 := (Submodule.Quotient.eq _).1 (show
    (Submodule.Quotient.mk (A.toRepresentation x ⟨v, hv⟩) :
      A.toSubmodule ⧸ Submodule.comap A.toSubmodule.subtype B.toSubmodule) =
      Submodule.Quotient.mk (c • (⟨v, hv⟩ : A.toSubmodule)) from hq)
  exact h2

section Geo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem geo_chain (hG : JacquetOfInducedFiltration k)
    {α β n : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n]
    {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    (e : (Σ i, m i) ≃ n) (e' : (Σ j, m' j) ≃ n) (χ' : Levi k m →* ℂˣ) (hχ : IsSmoothChar χ') :
    ∃ (M : ℕ) (bb : Fin M ≃ SizeMatrix m m') (fr : ∀ t, ∀ i, (Σ j, Fin ((bb t).1 i j)) ≃ m i)
      (gc : ∀ t, ∀ j, (Σ i, Fin ((bb t).1 i j)) ≃ m' j)
      (S : Fin (M + 1) → Submodule ℂ (Jacquet (parInd e (ofChar χ')) (unipRad k e'))),
      S 0 = ⊥ ∧ S (Fin.last M) = ⊤ ∧ ∀ (x : Levi k m') (s : β → kˣ)
        (hx : ∀ j, x j = Matrix.GeneralLinearGroup.scalar _ (s j)) (t : Fin M),
        ∀ v ∈ S t.succ, jac e' (parInd e (ofChar χ')) x v -
          ((cellScalar (fr t) (gc t) χ' ⟨x, mem_relParab_of_scalar (gc t) x s hx⟩ : ℂˣ) : ℂ) • v ∈ S t.castSucc := by
  obtain ⟨M, bb, hbb⟩ := hG α β n m m' e e'
  obtain ⟨S, -, h0, htop, hS⟩ := hbb ℂ (ofChar χ') ((isSmooth_ofChar_iff _).2 hχ)
  refine ⟨M, bb, fun t => (bb t).nonempty_rows.some, fun t => (bb t).nonempty_cols.some,
    fun t => (S t).toSubmodule, by simp only [h0]; rfl, by simp only [htop]; rfl, fun x s hx t => ?_⟩
  exact step_scalar _ _ _ (Classical.choice (hS t _ _)) x _
    (cellFunctor_ofChar_central _ _ _ _ (mem_relParab_of_scalar _ x s hx) (comm_of_scalar x s hx))

private theorem group_rows {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (h : 2 ≤ N)
    (π : Representation ℂ (GL (Fin N) k) V) {M : ℕ} (row : Fin M → Fin 2) (c : Fin 2 → kˣ → ℂ) (f : V)
    (w : Fin M → Jacquet π (unipRad k (linePlace h))) (hw : Submodule.Quotient.mk f = ∑ t, w t)
    (hwe : ∀ t y, jac (linePlace h) π (firstBlockScalar k N y) (w t) = c (row t) y • w t) :
    ∃ fa fb : V, f - fa - fb ∈ twKer π (unipRad k (linePlace h)) 1 ∧
      (∀ x : kˣ, π (leviEmb k (linePlace h) (firstBlockScalar k N x)) fa -
        ((absPow k (((N : ℂ) - 1) / 2) x : ℂ) * c 0 x) • fa ∈ twKer π (unipRad k (linePlace h)) 1) ∧
      (∀ x : kˣ, π (leviEmb k (linePlace h) (firstBlockScalar k N x)) fb -
        ((absPow k (((N : ℂ) - 1) / 2) x : ℂ) * c 1 x) • fb ∈ twKer π (unipRad k (linePlace h)) 1) := by
  have key : ∀ (i : Fin 2) (g : V),
      Submodule.Quotient.mk g = ∑ t ∈ Finset.univ.filter (fun t => row t = i), w t →
      ∀ x : kˣ, π (leviEmb k (linePlace h) (firstBlockScalar k N x)) g -
        ((absPow k (((N : ℂ) - 1) / 2) x : ℂ) * c i x) • g ∈ twKer π (unipRad k (linePlace h)) 1 := by
    intro i g hg x
    have h1 : jac (linePlace h) π (firstBlockScalar k N x) (Submodule.Quotient.mk g) = c i x • Submodule.Quotient.mk g := by
      rw [hg, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [hwe, (Finset.mem_filter.1 ht).2]
    rw [jac_mk, Units.val_inv_eq_inv_val, deltaHalf_positionOne h, inv_smul_eq_iff₀ (Units.ne_zero _), smul_smul] at h1
    apply (Submodule.Quotient.eq _).1
    exact h1
  obtain ⟨fa, hfa⟩ := Submodule.Quotient.mk_surjective _ (∑ t ∈ Finset.univ.filter (fun t => row t = 0), w t)
  obtain ⟨fb, hfb⟩ := Submodule.Quotient.mk_surjective _ (∑ t ∈ Finset.univ.filter (fun t => row t = 1), w t)
  refine ⟨fa, fb, ?_, key 0 fa hfa, key 1 fb hfb⟩
  rw [sub_sub]
  apply (Submodule.Quotient.eq _).1
  refine hw.trans ?_
  rw [Submodule.Quotient.mk_add, hfa, hfb,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun t => row t = 0)]
  congr 2
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  generalize row t = r
  fin_cases r <;> simp

private theorem split_of_chain {V : Type} [AddCommGroup V] [Module ℂ V] (a a' : ℕ) (haa : a' < a) (h : 2 ≤ a + a')
    (χ : Fin 2 → kˣ →* ℂˣ) (hun : ∀ j, IsUnitaryChar (χ j))
    (π : Representation ℂ (GL (Fin (a + a')) k) V) (M : ℕ)
    (bb : Fin M ≃ SizeMatrix (fun j : Fin 2 => Fin (![a, a'] j))
      (fun j : Fin 3 => Fin (tripSizes 1 (a + a' - 2) (a + a') j)))
    (fr : ∀ t, ∀ i, (Σ j, Fin ((bb t).1 i j)) ≃ Fin (![a, a'] i))
    (gc : ∀ t, ∀ j, (Σ i, Fin ((bb t).1 i j)) ≃ Fin (tripSizes 1 (a + a' - 2) (a + a') j))
    (S : Fin (M + 1) → Submodule ℂ (Jacquet π (unipRad k (linePlace h))))
    (hS0 : S 0 = ⊥) (hStop : S (Fin.last M) = ⊤)
    (step : ∀ (x : Levi k (fun j : Fin 3 => Fin (tripSizes 1 (a + a' - 2) (a + a') j))) (s : Fin 3 → kˣ)
      (hx : ∀ j, x j = Matrix.GeneralLinearGroup.scalar _ (s j)) (t : Fin M),
      ∀ v ∈ S t.succ, jac (linePlace h) π x v - ((cellScalar (fr t) (gc t) (pairChar k ![a, a'] χ)
        ⟨x, mem_relParab_of_scalar (gc t) x s hx⟩ : ℂˣ) : ℂ) • v ∈ S t.castSucc) (f : V) :
    ∃ fa fb : V, f - fa - fb ∈ twKer π (unipRad k (linePlace h)) 1 ∧
      (∀ x : kˣ, π (leviEmb k (linePlace h) (firstBlockScalar k (a + a') x)) fa -
        ((χ 0 x : ℂ) * (absPow k ((a' : ℂ) / 2) x : ℂ)) • fa ∈ twKer π (unipRad k (linePlace h)) 1) ∧
      (∀ x : kˣ, π (leviEmb k (linePlace h) (firstBlockScalar k (a + a') x)) fb -
        ((χ 1 x : ℂ) * (absPow k ((a : ℂ) / 2) x : ℂ)) • fb ∈ twKer π (unipRad k (linePlace h)) 1) := by
  obtain ⟨ϖ, -, hϖ⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one k
  have hp0 : 0 < nabs k ϖ := nabs_pos' k ϖ
  let xT : Levi k (fun j : Fin 3 => Fin (tripSizes 1 (a + a' - 2) (a + a') j)) :=
    firstBlockScalar k (a + a') (ϖ ^ 2) * thirdBlockScalar k (a + a') ϖ
  let sT : Fin 3 → kˣ := fun j => (if j = 0 then ϖ ^ 2 else 1) * (if j = 2 then ϖ else 1)
  have hxT : ∀ j, xT j = Matrix.GeneralLinearGroup.scalar _ (sT j) := fun j => by
    simp only [xT, sT, Pi.mul_apply, firstBlockScalar_apply, thirdBlockScalar_apply, map_mul]
  let lam : Fin M → ℂ := fun t =>
    ((cellScalar (fr t) (gc t) (pairChar k ![a, a'] χ) ⟨xT, mem_relParab_of_scalar (gc t) xT sT hxT⟩ : ℂˣ) : ℂ)
  let nu : Fin M → kˣ → ℂ := fun t y =>
    ((cellScalar (fr t) (gc t) (pairChar k ![a, a'] χ)
      ⟨firstBlockScalar k (a + a') y, mem_relParab_of_scalar (gc t) _ _ (firstBlockScalar_apply (a + a') y)⟩ : ℂˣ) : ℂ)
  have hr : ∀ t (j : Fin 3), j ≠ 1 → (bb t).1 (rowOf a a' (bb t) j) j = 1 := fun t j hj => by
    rw [rowOf_spec a a' h (bb t) j hj]; simp
  have hlam : ∀ t, lam t = ((χ (rowOf a a' (bb t) 0) (ϖ ^ 2) : ℂ) *
      (absPow k ((1 - ((![a, a'] (rowOf a a' (bb t) 0) : ℕ) : ℂ)) / 2) (ϖ ^ 2) : ℂ)) *
      ((χ (rowOf a a' (bb t) 2) ϖ : ℂ) * (absPow k ((((![a, a'] (rowOf a a' (bb t) 2) : ℕ) : ℂ) - 1) / 2) ϖ : ℂ)) := by
    intro t
    have e : (⟨xT, mem_relParab_of_scalar (gc t) xT sT hxT⟩ : relParab k (gc t)) =
        ⟨firstBlockScalar k (a + a') (ϖ ^ 2), firstBlockScalar_mem_relParab (gc t) _⟩ *
          ⟨thirdBlockScalar k (a + a') ϖ, thirdBlockScalar_mem_relParab (gc t) _⟩ := rfl
    simp only [lam]
    rw [e, cellScalar_mul, Units.val_mul, cellScalar_positionOne_pair a a' χ (bb t) (fr t) (gc t) (ϖ ^ 2) _ (hr t 0 (by decide)),
      cellScalar_positionThree_pair a a' χ (bb t) (fr t) (gc t) ϖ _ h (hr t 2 (by decide))]
  have hnorm : ∀ t, ‖lam t‖ = nabs k ϖ ^ ((1 - ((![a, a'] (rowOf a a' (bb t) 0) : ℕ) : ℝ)) +
      (((![a, a'] (rowOf a a' (bb t) 2) : ℕ) : ℝ) - 1) / 2) := by
    intro t
    rw [hlam t, norm_mul, norm_mul, norm_mul, hun, hun, one_mul, one_mul, norm_absPow, norm_absPow,
      pow_two, nabs_mul', Real.rpow_add hp0]
    congr 1
    · rw [Real.mul_rpow hp0.le hp0.le, ← Real.rpow_add hp0]
      congr 1; simp
    · congr 1; simp
  have hinj : Function.Injective lam := by
    intro t s hts
    have h1 := congrArg norm hts
    rw [hnorm, hnorm] at h1
    have h2 := congrArg Real.log h1
    rw [Real.log_rpow hp0, Real.log_rpow hp0] at h2
    have hl : Real.log (nabs k ϖ) ≠ 0 := (Real.log_neg hp0 hϖ).ne
    obtain ⟨e0, e2⟩ := rows_eq_of_exp a a' haa _ _ _ _ (mul_right_cancel₀ hl h2)
    exact bb.injective (sizeMatrix_eq a a' h _ _ e0 e2)
  have hnu : ∀ t y, nu t y = (χ (rowOf a a' (bb t) 0) y : ℂ) *
      (absPow k ((1 - ((![a, a'] (rowOf a a' (bb t) 0) : ℕ) : ℂ)) / 2) y : ℂ) := fun t y =>
    cellScalar_positionOne_pair a a' χ (bb t) (fr t) (gc t) y _ (hr t 0 (by decide))
  obtain ⟨w, hw, hwe⟩ := chain_split_simultaneous_eigen M S hS0 hStop (jac (linePlace h) π xT)
    (fun y : kˣ => jac (linePlace h) π (firstBlockScalar k (a + a') y))
    (fun y => by
      show jac (linePlace h) π (firstBlockScalar k (a + a') y) * jac (linePlace h) π xT =
        jac (linePlace h) π xT * jac (linePlace h) π (firstBlockScalar k (a + a') y)
      rw [← map_mul, ← map_mul, firstBlockScalar_comm])
    lam hinj nu (fun t v hv => step xT sT hxT t v hv)
    (fun t y v hv => step _ _ (firstBlockScalar_apply (a + a') y) t v hv) (Submodule.Quotient.mk f)
  obtain ⟨fa, fb, h1, h2, h3⟩ := group_rows h π (fun t => rowOf a a' (bb t) 0)
    (fun i y => (χ i y : ℂ) * (absPow k ((1 - ((![a, a'] i : ℕ) : ℂ)) / 2) y : ℂ)) f w hw
    (fun t y => by rw [← hnu t y]; exact hwe t y)
  have hs : ∀ (i : Fin 2) (s : ℂ) (x : kˣ), (((a + a' : ℕ) : ℂ) - 1) / 2 + (1 - ((![a, a'] i : ℕ) : ℂ)) / 2 = s →
      (absPow k ((((a + a' : ℕ) : ℂ) - 1) / 2) x : ℂ) *
        ((χ i x : ℂ) * (absPow k ((1 - ((![a, a'] i : ℕ) : ℂ)) / 2) x : ℂ)) = (χ i x : ℂ) * (absPow k s x : ℂ) := by
    intro i s x hs
    rw [← hs, absPow_add, MonoidHom.mul_apply, Units.val_mul]
    ring
  refine ⟨fa, fb, h1, fun x => ?_, fun x => ?_⟩
  · rw [← hs 0 _ x (by simp; ring)]; exact h2 x
  · rw [← hs 1 _ x (by simp; ring)]; exact h3 x

end Geo

end GlobalTheory.JacLineSplit.Eigen

end

theorem _root_.GlobalTheory.T.induced_line_kernel_decomposition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.GeometricLemmaFiltration → ∀ (a a' : ℕ), a' < a → ∀ (h : 2 ≤ a + a') (χ : Fin 2 → kˣ →* ℂˣ),
    (∀ j, IsSmoothChar (χ j)) → (∀ j, IsUnitaryChar (χ j)) → ∀ f : IndAA k a a' χ, ∃ fa fb : IndAA k a a' χ,
      f - fa - fb ∈ lineKer k a a' h χ ∧
      (∀ x : kˣ, indAA k a a' χ (leviEmb k (linePlace h) (firstBlockScalar k (a + a') x)) fa -
        ((χ 0 x : ℂ) * (absPow k ((a' : ℂ) / 2) x : ℂ)) • fa ∈ lineKer k a a' h χ) ∧
      (∀ x : kˣ, indAA k a a' χ (leviEmb k (linePlace h) (firstBlockScalar k (a + a') x)) fb -
        ((χ 1 x : ℂ) * (absPow k ((a : ℂ) / 2) x : ℂ)) • fb ∈ lineKer k a a' h χ) := by
  intro k _ _ _ _ hG a a' haa h χ hsm hun f
  have hchar : IsSmoothChar (pairChar k ![a, a'] χ) := by
    unfold pairChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) ?_ fun j _ => ?_
    · unfold IsSmoothChar; simp
    · exact (hsm j).detChar.comp _ (continuous_apply j)
  obtain ⟨M, bb, fr, gc, S, h0, htop, step⟩ := Eigen.geo_chain (hG k) (pairPlace (N := a + a') ![a, a'] rfl)
    (linePlace h) (pairChar k ![a, a'] χ) hchar
  exact Eigen.split_of_chain a a' haa h χ hun (indAA k a a' χ) M bb fr gc S h0 htop step f
