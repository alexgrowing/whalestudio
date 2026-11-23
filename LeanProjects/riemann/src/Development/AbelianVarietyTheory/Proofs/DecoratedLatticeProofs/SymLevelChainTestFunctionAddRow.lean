import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain.RowShift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_add_row {n : Type} [Fintype n] [DecidableEq n] {g : GL n k} (hg : g ∈ KO k n) (a : n) (w : n → k)
    (hw : ∀ s, w s ∈ 𝒪[k]) (h : valuation k ((w ᵥ* (g⁻¹).val) a) < 1) :
    ∃ g' ∈ KO k n, g'.val = g.val + vecMulVec (Pi.single a 1) w ∧
      ∀ μ : kˣ →* ℂˣ, IsTame μ → μ (Matrix.GeneralLinearGroup.det g') = μ (Matrix.GeneralLinearGroup.det g) := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hg
  have hE : ∀ w : n → k, (∀ s, w s ∈ 𝒪[k]) → IntM (vecMulVec (Pi.single a (1 : k)) w) := fun w hw i j => by
    rw [vecMulVec_apply, Pi.single_apply]
    split_ifs
    · simpa using hw j
    · simp
  set f := w ᵥ* (g⁻¹).val with hf
  have hfi : ∀ s, f s ∈ 𝒪[k] := fun s => sum_mem fun i _ => mul_mem (hw i) (h2 i s)
  set F : Matrix n n k := vecMulVec (Pi.single a 1) f with hF
  have hFF : MaxM (F * F) := fun i j => by
    rw [hF, vecMulVec_mul_vecMulVec, vecMulVec_apply, dotProduct_single, mul_one, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply]
    split_ifs
    · rw [one_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h (hfi j)
    · simp
  obtain ⟨u, hu, eu⟩ := exists_mem_KO_of_mul (A := 1 + F) (A' := 1 + -F) (intM_one.add (hE f hfi))
    (intM_one.add (hE f hfi).neg) (by
      have : (1 + F) * (1 + -F) - 1 = -(F * F) := by noncomm_ring
      rw [this]; exact hFF.neg)
  refine ⟨u * g, mul_mem hu hg, ?_, fun μ hμ => ?_⟩
  · rw [Units.val_mul, eu, Matrix.add_mul, Matrix.one_mul, hF, vecMulVec_mul, hf, vecMul_vecMul, Units.inv_mul,
      vecMul_one]
  · rw [map_mul, map_mul, hμ (Matrix.GeneralLinearGroup.det u), one_mul]
    rw [Matrix.GeneralLinearGroup.val_det_apply, eu, hF, vecMulVec_eq Unit,
      det_one_add_replicateCol_mul_replicateRow, dotProduct_single, mul_one, add_sub_cancel_left]
    exact h

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem exists_mem_iter (hP : S.Pattern t) (j : ℕ) (q : Fin (s + 1)) (hq : q.val + 1 ≤ S.ρ)
    (w : Ix (Fin κ ⊕ Fin (s + 1)) t j → k) (hw : ∀ b, w b ∈ 𝒪[k])
    (h0 : ∀ l : Fin (s + 1), l.val ≤ q.val + 1 → w (.inl (.inr l)) = 0) (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (g : (S.P.iter t S.μ S.tame j).J) :
    ∃ g' : (S.P.iter t S.μ S.tame j).J,
      g'.1.val = g.1.val + vecMulVec (Pi.single (.inl (.inr q)) 1) w ∧
      (S.P.iter t S.μ S.tame j).rho μ g' = (S.P.iter t S.μ S.tame j).rho μ g := by
  obtain ⟨hg, hgp⟩ := (hP j g.1).1 g.2
  obtain ⟨hgi, hgip⟩ := (hP j g.1⁻¹).1 (inv_mem g.2)
  obtain ⟨g', hg', e, hd⟩ := exists_add_row hg (.inl (.inr q)) w hw (by
    refine Valuation.map_sum_lt _ one_ne_zero fun b _ => ?_
    by_cases hb : w b = 0
    · simp [hb]
    · have hne : b ≠ .inl (.inr q) := by
        rintro rfl; exact hb (h0 q (by omega))
      have hnf : ¬ FreeIx S.ρ b (.inl (.inr q)) := by
        rcases b with (b | b) | b
        · simp only [FreeIx, FreeTop]; omega
        · simp only [FreeIx, FreeTop]
          intro hlt
          exact hb (h0 b (by have := Fin.lt_def.1 hlt; omega))
        · simp [FreeIx]
      have := hgip b _ hnf
      rw [Matrix.one_apply_ne hne, sub_zero] at this
      rw [map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (hw b) zero_le this)
  have ent : ∀ a b, (a ≠ .inl (.inr q) ∨ w b = 0) → g'.val a b = g.1.val a b := by
    intro a b hab
    rw [e, Matrix.add_apply, vecMulVec_apply]
    rcases hab with hab | hab
    · rw [Pi.single_eq_of_ne hab, zero_mul, add_zero]
    · rw [hab, mul_zero, add_zero]
  have hm : g' ∈ (S.P.iter t S.μ S.tame j).J := by
    refine (hP j g').2 ⟨hg', fun a b hab => ?_⟩
    rw [ent a b]
    · exact hgp a b hab
    · by_cases ha : a = .inl (.inr q)
      · subst ha
        right
        rcases b with (b | b) | b
        · simp only [FreeIx, FreeTop] at hab; omega
        · simp only [FreeIx, FreeTop] at hab
          exact h0 b (by have := Fin.lt_def.not.1 hab; omega)
        · simp [FreeIx] at hab
      · exact Or.inl ha
  refine ⟨⟨g', hm⟩, e, ?_⟩
  rw [TypeDatum.rho_apply, TypeDatum.rho_apply, hd μ hμ]
  congr 1
  obtain ⟨a, D, ea, hD, el⟩ := GlobalTheory.SymBridge.iter_lam_closed k _ t S.P S.μ S.tame j g
  obtain ⟨a', D', ea', hD', el'⟩ := GlobalTheory.SymBridge.iter_lam_closed k _ t S.P S.μ S.tame j ⟨g', hm⟩
  have eD : D' = D := by
    funext i
    refine Units.ext ?_
    rw [(hD i).2, (hD' i).2]
    ext x y
    exact ent _ _ (Or.inl (by simp))
  have ela : S.P.lam a' = S.P.lam a := by
    refine Units.ext ?_
    rw [S.sym.2, S.sym.2]
    have e1 : simpleSum a'.1 = simpleSum a.1 := by
      unfold simpleSum
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      split_ifs with hxy
      · rw [ea, ea']
        refine ent _ _ ?_
        by_cases hx : x = q
        · subst hx; exact Or.inr (h0 y hxy.le)
        · exact Or.inl (by simpa using hx)
      · rfl
    have e2 : a'.1.val.toBlocks₁₁ = a.1.val.toBlocks₁₁ := by
      rw [ea, ea']
      ext x y
      exact ent _ _ (Or.inl (by simp))
    rw [e1, e2]
  rw [el, el', eD, ela]

theorem extZ_add_row (hP : S.Pattern t) (j : ℕ) (q : Fin (s + 1)) (hq : q.val + 1 ≤ S.ρ)
    (w : Ix (Fin κ ⊕ Fin (s + 1)) t j → k) (hw : ∀ b, w b ∈ 𝒪[k])
    (h0 : ∀ l : Fin (s + 1), l.val ≤ q.val + 1 → w (.inl (.inr l)) = 0) (μ : kˣ →* ℂˣ) (hμ : IsTame μ)
    (M : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t j) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k) :
    extZ _ ((S.P.iter t S.μ S.tame j).rho μ) (M + vecMulVec (Pi.single (.inl (.inr q)) 1) w) =
      extZ _ ((S.P.iter t S.μ S.tame j).rho μ) M := by
  by_cases h : ∃ g ∈ (S.P.iter t S.μ S.tame j).J, g.val = M
  · obtain ⟨g, hg, rfl⟩ := h
    obtain ⟨g', e, er⟩ := exists_mem_iter S t hP j q hq w hw h0 μ hμ ⟨g, hg⟩
    rw [← e, extZ_coe, extZ_coe _ _ ⟨g, hg⟩, er]
  · rw [extZ_of_not _ _ h, extZ_of_not]
    rintro ⟨g, hg, e⟩
    obtain ⟨g', e', -⟩ := exists_mem_iter S t hP j q hq (-w) (fun b => neg_mem (hw b))
      (fun l hl => by simp [h0 l hl]) μ hμ ⟨g, hg⟩
    refine h ⟨g', g'.2, ?_⟩
    rw [e', e, vecMulVec_neg, add_neg_cancel_right]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem coords_typeFrame {ι ι' n n' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype n]
    [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ} (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (a : ι) (b : ι') :
    (typeFrame ϖ o).coords (typeFrame ϖ o') x a b =
      Sum.elim (fun _ => 1) (fun i : Fin c => (((ϖ ^ (i.val + 1))⁻¹ : kˣ) : k)) (o a) * x (o a) (o' b) *
        Sum.elim (fun _ => 1) (fun i : Fin c' => ((ϖ ^ (i.val + 1) : kˣ) : k)) (o' b) := by
  have e : ((typeFrame ϖ o).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) (fun i : Fin c => (((ϖ ^ (i.val + 1))⁻¹ : kˣ) : k))) := by
    rw [← fromBlocks_diagonal]
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have e' : ((typeFrame ϖ o').bas).val =
      diagonal (Sum.elim (fun _ => 1) (fun i : Fin c' => ((ϖ ^ (i.val + 1) : kˣ) : k))) := by
    rw [← fromBlocks_diagonal, diagonal_one]
    rfl
  unfold LatFrame.coords
  rw [e, e', submatrix_apply, mul_diagonal, diagonal_mul]
  rfl

theorem phi_add_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ (j c : ℕ) (H : j + c = s) (q : Fin c), q.val + 1 ≤ S.ρ → ∀ (x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), (∀ s', x (Sum.inr q) (Sum.inl s') = 0) → ∀ v : XIx (Fin κ) t j → k, (S.T t).Phi j c H (x + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0) = if ∀ s', valuation k ((((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') ≤ 1 then (S.T t).Phi j c H x else 0 := by
  intro k _ _ _ _ s κ S t _ _ hP j c H q hq x hx v
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  let q' : Fin (s + 1) := ⟨q.val, by omega⟩
  have hoq : o (.inl (.inr q')) = .inr q := standardOrderExtendedBasis_apply_low_block _ _ _ _ _ q
  let w : Ix (Fin κ ⊕ Fin (s + 1)) t j → k := fun b =>
    Sum.elim (fun s' => (((S.ϖ ^ (q.val + 1))⁻¹ : kˣ) : k) * v s') 0 (o' b)
  let C : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k →
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t j ⊕ t) (Ix (Fin κ ⊕ Fin (s + 1)) t j) k := fun z =>
    ((typeFrame S.ϖ o).coords (typeFrame S.ϖ o') z).submatrix (ixSucc _ t j) id
  have hPhi : ∀ z, (S.T t).Phi j c H z = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) (C z) := fun z => rfl
  set x' := x + Matrix.of fun r s' => if r = Sum.inr q then Sum.elim v 0 s' else 0 with hx'
  have key : ∀ a b, C x' a b = C x a b + if a = .inl (.inl (.inr q')) then w b else 0 := by
    intro a b
    have hiff : o (ixSucc _ t j a) = .inr q ↔ a = .inl (.inl (.inr q')) := by
      rw [← hoq, o.apply_eq_iff_eq, ← (ixSucc (Fin κ ⊕ Fin (s + 1)) t j).apply_eq_iff_eq]; rfl
    simp only [C, submatrix_apply, coords_typeFrame, hx', Matrix.add_apply, Matrix.of_apply, id, mul_add, add_mul]
    congr 1
    by_cases ha : a = .inl (.inl (.inr q'))
    · rw [if_pos ha, if_pos (hiff.2 ha), hiff.2 ha]
      simp only [w]
      rcases o' b with y | y <;> simp
    · rw [if_neg ha, if_neg (hiff.not.2 ha), mul_zero, zero_mul]
  have e2 : (C x').toRows₂ = (C x).toRows₂ := by
    ext a b; simp [toRows₂, key]
  have e1 : (C x').toRows₁ = (C x).toRows₁ + vecMulVec (Pi.single (.inl (.inr q')) 1) w := by
    ext a b
    simp only [toRows₁, Matrix.of_apply, key, Matrix.add_apply, vecMulVec_apply, Pi.single_apply, Sum.inl.injEq,
      ite_mul, one_mul, zero_mul]
  rw [hPhi, hPhi]
  split_ifs with hv
  · unfold TypeDatum.Phi
    rw [e1, e2, extZ_add_row S t hP j q' hq w ?_ ?_ _ (S.tame _)]
    · intro b
      simp only [w]
      rcases o' b with y | y
      · exact hv y
      · exact zero_mem _
    · intro l hl
      have hl' : l.val ≤ q.val + 1 := hl
      have : o' (.inl (.inr l)) = .inr ⟨l.val, by omega⟩ := standardOrderExtendedBasis_apply_low_block (Fin κ) t j (c + 1) _ ⟨l.val, by omega⟩
      simp only [w, this]; rfl
  · by_contra hne
    refine hv fun y => ?_
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hne (.inl (.inl (.inr q'))) (o'.symm (.inl y))
    rw [key, if_pos rfl] at this
    have h0 : C x (.inl (.inl (.inr q'))) (o'.symm (.inl y)) = 0 := by
      change (typeFrame S.ϖ o).coords (typeFrame S.ϖ o') x (.inl (.inr q')) (o'.symm (.inl y)) = 0
      rw [coords_typeFrame, hoq, o'.apply_symm_apply, hx, mul_zero, zero_mul]
    rw [h0, zero_add] at this
    simp only [w, o'.apply_symm_apply, Sum.elim_inl] at this
    exact this

end GlobalTheory.SymChain.RowShift
