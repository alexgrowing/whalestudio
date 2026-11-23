import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section A
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem isColChar_full {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) :
    IsColChar ψ (TypeDatum.full k (n ⊕ Fin c)).toLevel 1 1 := by
  intro g u _ hm
  have hK : IntM (u * embX c (g : GL n k)).val := by
    have : u * embX c (g : GL n k) ∈ (TypeDatum.full k (n ⊕ Fin c)).J := by simpa using hm
    exact intM_of_mem_KO this
  have hs : simpleSum u ∈ 𝒪[k] := by
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    split_ifs
    · have := hK (.inr i) (.inr j)
      rw [Units.val_mul, ← fromBlocks_toBlocks u.val] at this
      change (_ * fromBlocks _ 0 0 1 : Matrix _ _ k) _ _ ∈ _ at this
      simpa [fromBlocks_multiply, toBlocks₂₂] using this
    · exact zero_mem _
  rw [hψ.eq_one (show _ ∈ cball (1 : kˣ) from hs)]
  change _ = _ * (((1 : ℂˣ)⁻¹ : ℂˣ) : ℂ)
  simp

variable [MeasurableSpace k] [BorelSpace k]

omit [DecidableEq n] in

theorem hat_coset {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : ε ∈ 𝒪[k]) (y₀ : n → k) {η : n → k} (hη : ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n 1) (Submodule.Quotient.mk y₀)) η = ψ (ε * (η ⬝ᵥ y₀)) := by
  have := hν.1
  have := secondCountable k
  unfold hat
  rw [← integral_add_left_eq_self _ y₀]
  have e : ∀ y : n → k, cosetInd (box n 1) (Submodule.Quotient.mk y₀) (y₀ + y) * (ψ (ε * (η ⬝ᵥ (y₀ + y))) : ℂ) =
      (Set.pi Set.univ fun _ => (𝒪[k] : Set k)).indicator (fun _ => (ψ (ε * (η ⬝ᵥ y₀)) : ℂ)) y := fun y => by
    have hy : (y₀ + y ∈ {y' : n → k | Submodule.Quotient.mk (p := box n 1) y' = Submodule.Quotient.mk y₀}) ↔
        y ∈ Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
      simp [Submodule.Quotient.eq, mem_box, Valuation.mem_integer_iff]
    by_cases h : y ∈ Set.pi Set.univ fun _ => (𝒪[k] : Set k)
    · have hi : ε * (η ⬝ᵥ y) ∈ 𝒪[k] := mul_mem hε (sum_mem fun i _ => mul_mem (hη i) (h i trivial))
      rw [cosetInd, Set.indicator_of_mem (hy.2 h), Set.indicator_of_mem h, dotProduct_add, mul_add,
        AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi)]
      simp
    · rw [cosetInd, Set.indicator_of_notMem (mt hy.1 h), Set.indicator_of_notMem h, zero_mul]
  simp only [e]
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => (isOpen_int k).measurableSet), Measure.real,
    Measure.pi_pi]
  simp [hν.2]

omit [DecidableEq n] [DecidableEq n'] in

theorem opE_ne_zero' (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hΦ : Φ ∈ SB _)
    (h01 : ∀ x, Φ x ≠ 0 → Φ x = ψ (ch x)) {x₀ : Matrix n n' k} {e₀} (he : Φ (affPt p x₀ e₀) ≠ 0) :
    opE ψ ν p Φ x₀ ≠ 0 := by
  classical
  have := secondCountable k
  have := t2Space k
  have hc : Continuous (affPt (c := c) p x₀) := by
    refine continuous_const.add (continuous_pi fun r => continuous_pi fun s => ?_)
    by_cases hf : Free p (r, s)
    · simp only [Matrix.of_apply, dif_pos hf]; exact continuous_apply _
    · simp only [Matrix.of_apply, dif_neg hf]; exact continuous_const
  have key : ∀ e, Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) = (‖Φ (affPt p x₀ e)‖ : ℝ) := fun e => by
    by_cases h : Φ (affPt p x₀ e) = 0
    · simp [h]
    · rw [h01 _ h, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, Circle.norm_coe]; simp
  unfold opE
  simp only [key]
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (hΦ.1.continuous.comp hc).norm ?_
    (fun _ => norm_nonneg _) (x := e₀) (norm_ne_zero_iff.2 he)).ne'
  refine HasCompactSupport.intro (IsCompact.image hΦ.2
    (f := fun x (rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) =>
      x rs.1.1 rs.1.2 - basePt c x₀ rs.1.1 rs.1.2) (by fun_prop))
    fun e he' => norm_eq_zero.2 (by_contra fun h => he' ⟨_, subset_tsupport _ h, ?_⟩)
  funext ⟨⟨r, s⟩, hf⟩
  simp [affPt, hf]

end A

section B
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}

def wt (ϖ : kˣ) : n ⊕ Fin c → k := Sum.elim (fun _ => 1) fun i => (ϖ : k) ^ (i.val + 1)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] in
theorem wt_ne_zero (ϖ : kˣ) (i : n ⊕ Fin c) : wt ϖ i ≠ 0 := by
  rcases i with i | i <;> simp [wt]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_val (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) : (typeFrame ϖ o).bas.val = diagonal (wt ϖ) := by
  change fromBlocks 1 0 0 (diagonal _) = _
  rw [← diagonal_one, fromBlocks_diagonal]; congr

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem typeFrame_inv (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ o).bas⁻¹).val = diagonal fun i => (wt ϖ i)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_val, diagonal_mul_diagonal, ← diagonal_one]
  congr; funext i; exact mul_inv_cancel₀ (wt_ne_zero ϖ i)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coords_typeFrame (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (i : ι) (j : ι') :
    (typeFrame ϖ o).coords (typeFrame ϖ o') x i j = (wt ϖ (o i))⁻¹ * x (o i) (o' j) * wt ϖ (o' j) := by
  rw [LatFrame.coords, typeFrame_val, typeFrame_inv, submatrix_apply, mul_diagonal, diagonal_mul]; rfl

end B

section C
variable [MeasurableSpace k] [BorelSpace k] {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]

theorem typeChain_entry_ne_zero (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ) (s c : ℕ)
    (h : 0 + 1 + c = s) (P : TypeDatum k (κ ⊕ Fin (s + 1))) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j))
    (hP : ∀ g : P.J, (P.rho (μ 1) g : ℂ) =
      ψ (∑ i : Fin s, (g : GL (κ ⊕ Fin (s + 1)) k).val (.inr i.castSucc) (.inr i.succ) / ϖ)) :
    DoubleCoset.mk _ _ 1 ∈ (typeChain t ϖ P μ hμ).idx ψ ν 0 c h 1 ∧
      (typeChain t ϖ P μ hμ).entry ψ ν 0 c h 1 1 ≠ 0 := by
  obtain rfl : s = c + 1 := by omega
  set T := typeChain t ϖ P μ hμ
  have hT : T.Regular := Chain.ofType_regular _ _ _ _ _
  let o := stdOrd κ t (l := c + 1 + 1) (0 + 1) (c + 1) (by omega)
  let o' := stdOrd κ t (l := c + 1 + 1) 0 (c + 1 + 1) (by omega)
  let Q := P.reindex (ixZero _ t)
  have hQ : ∀ x, T.Phi 0 (c + 1) (by omega) x = Q.Phi t (μ 1)
      (((typeFrame ϖ o).coords (typeFrame ϖ o') x).submatrix (ixSucc _ t 0) id) := fun x => rfl
  have b1 : ∀ i : Fin (c + 1), o (.inl (.inr i.castSucc)) = .inr i := fun i => standardOrderExtendedBasis_apply_low_block κ t _ _ _ i
  have b2 : ∀ i : Fin (c + 1 + 1), o' (.inl (.inr i)) = .inr i := fun i => standardOrderExtendedBasis_apply_low_block κ t _ _ _ i
  let x : Matrix _ _ k := Matrix.of fun r q =>
    wt ϖ r * (fromBlocks (1 : Matrix _ _ k) 0 0 0).submatrix o.symm o'.symm r q * (wt ϖ q)⁻¹
  have a1 : ∀ i, o.symm (.inr i) = .inl (.inr ⟨i.val, by omega⟩) := fun i =>
    o.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block κ t _ _ _ i).symm
  have a2 : ∀ i, o'.symm (.inr i) = .inl (.inr ⟨i.val, by omega⟩) := fun i =>
    o'.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block κ t _ _ _ i).symm
  have a3 : ∀ i, o.symm (.inl (.inl (.inr i))) = .inl (.inr ⟨c + 1 + i.val, by omega⟩) := fun i =>
    o.symm_apply_eq.2 (stdOrd_f κ t _ _ _ i).symm
  have a4 : ∀ i, o.symm (.inl (.inl (.inl i))) = .inl (.inl i) := fun i => o.symm_apply_eq.2 rfl
  have a5 : ∀ i, o'.symm (.inl (.inl (.inl i))) = .inl (.inl i) := fun i => o'.symm_apply_eq.2 rfl
  have a6 : ∀ i, o.symm (.inl (.inr i)) = .inr i := fun i => o.symm_apply_eq.2 rfl
  obtain ⟨e, he⟩ := exists_affPt (p := 1) (x := x) (by
    rintro (r | r) (i | i) hf
    · rfl
    · have hi : i.val = 0 := by simp only [Free] at hf; omega
      rcases r with (r | r) | r
      · simp [x, basePt, a2, a4]
      · simp [x, basePt, a2, a3, hi]
      · simp [x, basePt, a2, a6]
    · rcases i with (i | i) | i
      · simp [x, basePt, a1, a5]
      · exact i.elim0
      · exact i.1.elim0
    · by_cases hri : r.val = i.val
      · simp [x, basePt, a1, a2, wt, hri]
      · simp [x, basePt, a1, a2, Matrix.one_apply, wt, hri, Fin.ext_iff])
  have hflat : flat ψ ν (T.mu (0 + 1)) (T.Phi 0 (c + 1) (by omega)) 1 1 ≠ 0 := by
    rw [flat, om_one]
    refine fun h0 => opE_ne_zero' ψ ν 1 (hT.1 0 (c + 1) (by omega)) (fun y hy => ?_) (e₀ := e) ?_
      (congrFun h0 x.toBlocks₁₁)
    · rw [hQ] at hy ⊢
      obtain ⟨⟨g, hg, eg⟩, h2⟩ := (Q.Phi_ne_zero_iff _).1 hy
      rw [Q.Phi_of_mem _ ⟨g, hg⟩ eg h2]
      have := hP ⟨(reGL (ixZero _ t)).symm g, hg⟩
      rw [TypeDatum.rho_apply, Units.val_mul, ← det_reGL (ixZero _ t), MulEquiv.apply_symm_apply] at this
      refine this.trans (congrArg _ (congrArg _ (Finset.sum_congr rfl fun i _ => ?_)))
      change g.val (.inl (.inr i.castSucc)) (.inl (.inr i.succ)) / _ = _
      rw [eg]
      change (typeFrame ϖ o).coords (typeFrame ϖ o') y (.inl (.inr i.castSucc)) (.inl (.inr i.succ)) / _ = _
      rw [coords_typeFrame, b1, b2]
      simp only [wt, Sum.elim_inr, Fin.val_succ]
      field_simp
      ring
    · rw [he, hQ]
      have ex : (typeFrame ϖ o).coords (typeFrame ϖ o') x = fromBlocks 1 0 0 0 := by
        ext i j
        rw [coords_typeFrame]
        have := wt_ne_zero ϖ (o i)
        have := wt_ne_zero ϖ (o' j)
        simp only [x, of_apply, submatrix_apply, Equiv.symm_apply_apply]
        field_simp
      rw [ex, Q.Phi_ne_zero_iff]
      refine ⟨⟨1, one_mem _, ?_⟩, fun i j => ?_⟩
      · ext (i | i) (j | j)
        · simp [ixSucc, toRows₁, Matrix.one_apply]
        · exact j.1.elim0
        · exact i.1.elim0
        · exact i.1.elim0
      · rcases j with j | j <;> simp [ixSucc, toRows₂]
  exact ⟨⟨1, rfl, hflat⟩, fun h0 => hflat ((xi_eq_zero_iff ψ ν _ _ (hT.2.2 _ _ _).1 (hT.2.2 _ _ _).2.1 _ _ _).1 h0)⟩

theorem typeChain_principal_entry_ne_zero {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] {ϖ : kˣ} (hϖ : ∀ z : k, valuation k z < 1 → valuation k z ≤ valuation k (ϖ : k)) (s c : ℕ)
    (h : 0 + 1 + c = s) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    (typeChain t ϖ (TypeDatum.principal k (κ ⊕ Fin (s + 1))) μ hμ).entry ψ ν 0 c h 1 1 ≠ 0 := by
  refine (typeChain_entry_ne_zero ψ ν ϖ s c h _ μ hμ fun g => ?_).2
  have hi : ∑ i : Fin s, (g : GL (κ ⊕ Fin (s + 1)) k).val (.inr i.castSucc) (.inr i.succ) / ϖ ∈ 𝒪[k] := sum_mem fun i _ => by
    have := hϖ _ (mem_KOne.1 g.2 (.inr i.castSucc) (.inr i.succ))
    rw [Matrix.sub_apply, Matrix.one_apply_ne (by simp [Fin.ext_iff]), sub_zero] at this
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ this zero_le
  rw [hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi), TypeDatum.rho_apply, tame_det_of_mem_KOne (hμ 1) g.2]
  change ((1 * 1⁻¹ : ℂˣ) : ℂ) = _
  simp

omit [MeasurableSpace k] [BorelSpace k] in

theorem typeChain_adapted {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) {s : ℕ} (P : TypeDatum k (κ ⊕ Fin (s + 1)))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (A : RepFam k s (XIx κ t))
    (hA : (typeChain t ϖ P μ hμ).RepsInStab A) :
    (typeChain t ϖ P μ hμ).Adapted A (box _ ϖ⁻¹) (box _ 1) := by
  intro g hg x₀ y
  let F := typeFrame ϖ (stdOrd κ t (l := s + 1) (s + 1) 0 rfl)
  let F' := typeFrame ϖ (stdOrd κ t (l := s + 1) s (0 + 1) rfl)
  have hK : reGL F'.ord (F'.conj.symm g) ∈ KO k _ := by
    have := mem_stabLat.1 (hA s 0 rfl g hg)
    have e := F'.conj_apply (F'.conj.symm g)
    rw [MulEquiv.apply_symm_apply] at e
    change F'.bas⁻¹ * g * F'.bas ∈ _ at this
    rw [e] at this
    simpa [mul_assoc] using this
  have hK' : F'.conj.symm g ∈ KO k _ :=
    ((TypeDatum.full k _).reindex F'.ord.symm).le_KO (show (reGL F'.ord.symm).symm _ ∈ KO k _ from hK)
  obtain ⟨u, rfl⟩ := F'.conj.surjective g
  rw [MulEquiv.symm_apply_apply] at hK'
  have hΨ : ∀ y, (typeChain t ϖ P μ hμ).Psi (F'.conj u) x₀ y =
      μ (s + 1) (Matrix.GeneralLinearGroup.det u) *
        P.iterPhi t μ hμ s (F.coords F' (withCol x₀ y) * u.val) := fun y => by
    have := congrFun (F.om_transport F' (μ (s + 1)) u 1 (P.iterPhi t μ hμ s)) (withCol x₀ y)
    rw [map_one] at this
    refine this.trans ?_
    rw [LatFrame.transport, om_of_mem_KO _ hK' (one_mem _)]
    simp
  refine ⟨fun h i => ?_, fun z hz => ?_⟩
  · rw [hΨ] at h
    have h1 : IntM (F.coords F' (withCol x₀ y) * u.val) := fun i l => by
      simpa using TypeDatum.intM_of_Phi_ne_zero _ _ (right_ne_zero_of_mul h) ((ixSucc _ t s).symm i) l
    have h2 := h1.mul (mem_KO.1 hK').2 (F.ord.symm (.inl i)) (F'.ord.symm (.inr 0))
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, coords_typeFrame] at h2
    simp only [F, F', typeFrame, Equiv.apply_symm_apply, wt, withCol] at h2
    have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
    have h3 : valuation k (y i) * valuation k (ϖ : k) ≤ 1 := by simpa [Valuation.mem_integer_iff] using h2
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← one_mul _⁻¹, le_mul_inv_iff₀ h0]
    exact h3
  · rw [hΨ, hΨ]
    have e : F.coords F' (withCol x₀ (y + z)) = F.coords F' (withCol x₀ y) + F.coords F' (withCol 0 z) := by
      ext i j
      rw [Matrix.add_apply, coords_typeFrame, coords_typeFrame, coords_typeFrame]
      generalize stdOrd κ t (l := s + 1) (s + 1) 0 rfl i = i'
      generalize stdOrd κ t (l := s + 1) s (0 + 1) rfl j = j'
      rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp [withCol, mul_add, add_mul]
    have m : MaxM (F.coords F' (withCol 0 z)) := fun i j => by
      rw [coords_typeFrame]
      generalize stdOrd κ t (l := s + 1) (s + 1) 0 rfl i = i'
      generalize stdOrd κ t (l := s + 1) s (0 + 1) rfl j = j'
      rcases i' with i' | i' <;> rcases j' with j' | j' <;> simp [withCol, wt]
      exact mul_lt_one_of_nonneg_of_lt_one_right (by simpa using hz i') zero_le hϖ
    rw [e, Matrix.add_mul]
    congr 1
    have m' := m.mul_intM (intM_of_mem_KO hK')
    generalize F.coords F' (withCol 0 z) * u.val = w at m' ⊢
    generalize F.coords F' (withCol x₀ y) * u.val = w'
    exact TypeDatum.Phi_add _ (hμ _) (w'.submatrix (ixSucc _ t s) id) (y := w.submatrix (ixSucc _ t s) id)
      fun _ _ => m' _ _

end C

section D
variable {κ t : Type*} [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem coords_surjective {ι ι' Y Y' : Type*} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') : Function.Surjective (F.coords F') := fun w =>
  ⟨F.bas.val * w.submatrix F.ord.symm F'.ord.symm * (F'.bas⁻¹).val, by
    simp only [LatFrame.coords, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]; simp⟩

theorem typeChain_coupIdx {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) {s : ℕ} (P : TypeDatum k (κ ⊕ Fin (s + 1)))
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (A : RepFam k s (XIx κ t))
    (hA : (typeChain t ϖ P μ hμ).RepsInStab A) (h1 : 1 ∈ A s 0 rfl) :
    ∃ yb ∈ (typeChain t ϖ P μ hμ).coupIdx A (box _ ϖ⁻¹) (box _ 1),
      (typeChain t ϖ P μ hμ).xiPen (box _ 1) 1 yb ≠ 0 := by
  have H := typeChain_adapted hϖ P μ hμ A hA
  obtain ⟨x, hx⟩ := coords_surjective (typeFrame ϖ (stdOrd κ t (l := s + 1) (s + 1) 0 rfl))
    (typeFrame ϖ (stdOrd κ t (l := s + 1) s (0 + 1) rfl))
    ((fromRows (1 : Matrix _ _ k) (0 : Matrix t _ k)).submatrix (ixSucc _ t s).symm id)
  have hne : (typeChain t ϖ P μ hμ).Psi 1 x.toBlocks₁₁ (fun r => x (.inl r) (.inr 0)) ≠ 0 := by
    rw [Chain.Psi, om_one, withCol_blocks]
    change P.iterPhi t μ hμ s (LatFrame.coords _ _ x) ≠ 0
    rw [hx, TypeDatum.iterPhi, TypeDatum.Phi_ne_zero_iff]
    simp only [submatrix_submatrix, Equiv.symm_comp_self, Function.comp_id, submatrix_id_id]
    exact ⟨⟨1, one_mem _, by simp⟩, by simpa using maxM_zero⟩
  exact ⟨_, ⟨_, (H 1 h1 _ _).1 hne, rfl, 1, h1, _, hne⟩,
    fun h0 => hne ((Chain.xiPen_mk H h1 _ _).symm.trans (congrFun h0 _))⟩

theorem twistChain_reps_zero [MeasurableSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ϖ : kˣ)
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (ν' : ℕ → kˣ →* ℂˣ) :
    let T := twistChain 0 t κ δ hδ ν'
    let A : RepFam k 0 (XIx κ t) := fun _ _ _ => {1}
    T.IsRepSystem A ψ ν ∧ T.RepsInStab A ∧ T.RepsMeet A ∧ T.RepsNormal A ϖ ∧ T.RepsOne A := by
  refine ⟨⟨fun _ _ => rfl, fun j c h => by omega⟩, ?_, ?_, ?_, fun _ _ _ _ hg _ => hg⟩
  · rintro j c h _ rfl; exact one_mem _
  · rintro j c h _ rfl y
    change _ ∈ latOf (1 * 1) ↔ _
    simp [mem_latOf_one]
  · rintro j c h _ rfl
    refine ⟨0, 0, by simp, by simp, ?_⟩
    change latOf (1 * 1) = _
    congr 1
    refine Units.ext ?_
    rw [normalBasis_val, mul_one, Units.val_one, ← fromBlocks_one]
    congr 1
    · ext; simp
    · simp

end D

end GlobalTheory.StepData.Model
