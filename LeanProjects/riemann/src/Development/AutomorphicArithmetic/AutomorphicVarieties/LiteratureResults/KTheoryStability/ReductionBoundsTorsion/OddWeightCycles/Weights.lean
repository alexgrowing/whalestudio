import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.WOneOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.Weights

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockEvaluationBounds

open BlockInvariants BlockInvariants.AlternatingWeights

namespace AlternatingWeights

variable {L : Type} [Field L] [NumberField L]

theorem tmC_relabel {N q : ℕ} (ρ c : Equiv.Perm (Fin q)) (w0 : InfinitePlace L) (Y : Fin q → HS L N) :
    tmC (c⁻¹ * ρ * c) (fun _ => w0) Y = tmC ρ (fun _ => w0) (Y ∘ ⇑c⁻¹) := by
  unfold tmC
  rw [if_pos (fun _ => rfl), if_pos (fun _ => rfl)]
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap', Function.comp_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr c (Equiv.refl _)) _ _ (fun a => ?_)
  refine Fintype.prod_equiv c _ _ (fun i => ?_)
  simp [Equiv.arrowCongr_apply, Equiv.Perm.mul_apply]

theorem tmC_inv_star {N q : ℕ} (ρ : Equiv.Perm (Fin q)) (w0 : InfinitePlace L) (Y : Fin q → HS L N) :
    tmC ρ⁻¹ (fun _ => w0) Y = star (tmC ρ (fun _ => w0) Y) := by
  unfold tmC
  rw [if_pos (fun _ => rfl), if_pos (fun _ => rfl)]
  simp only [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, LinearMap.coe_toContinuousLinearMap', star_sum, star_prod]
  refine Fintype.sum_equiv (Equiv.arrowCongr ρ (Equiv.refl _)) _ _ (fun b => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [ent, mat, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_id, Function.comp_apply,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hh := ((Y i).2 w0).apply (b i) (b (ρ⁻¹ i))
  simp only [Matrix.of_apply] at hh ⊢
  simp only [id, Equiv.symm_apply_apply, ← Equiv.Perm.inv_def]
  have e : ρ⁻¹ (ρ i) = i := by simp
  rw [e]
  exact hh.symm

theorem rot_rev (q : ℕ) :
    (Fin.revPerm : Equiv.Perm (Fin q))⁻¹ * finRotate q * Fin.revPerm = (finRotate q)⁻¹ := by
  rcases q with _ | n
  · exact Subsingleton.elim _ _
  · rw [eq_inv_iff_mul_eq_one]
    ext i
    simp [Equiv.Perm.inv_def, finRotate_succ_apply, Fin.revPerm_apply, Fin.rev_add]

theorem alt_relabel {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f g : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (τ : Equiv.Perm (Fin q))
    (h : ∀ v, f v = g (v ∘ τ)) :
    ContinuousMultilinearMap.alternatization f =
      ((Equiv.Perm.sign τ : ℤ) : ℝ) • ContinuousMultilinearMap.alternatization g := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, ContinuousMultilinearMap.alternatization_apply_apply,
    ContinuousMultilinearMap.alternatization_apply_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, h, Equiv.Perm.coe_mul, Function.comp_assoc]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> simp [hs]

theorem alt_zero' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ) (σ : Equiv.Perm (Fin q))
    (hf : ∀ v, f (v ∘ σ) = -f v) (hs : Equiv.Perm.sign σ = 1) :
    ContinuousMultilinearMap.alternatization f = 0 := by
  have h2 := alt_relabel f (-f) σ (fun v => by
    rw [ContinuousMultilinearMap.neg_apply, hf, neg_neg])
  rw [hs, map_neg] at h2
  ext v
  have h3 := congrArg (fun F => F v) h2
  simp at h3
  simp
  linarith

theorem const_of_cycle {q : ℕ} {α : Type} (σ : Equiv.Perm (Fin q)) (w : Fin q → α)
    (hw : ∀ i, w (σ i) = w i) (a b : Fin q) (hab : σ.SameCycle a b) : w a = w b := by
  obtain ⟨k, rfl⟩ := hab
  have key : ∀ n : ℕ, ∀ x, w ((σ ^ n) x) = w x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ', Equiv.Perm.mul_apply, hw, ih]
  rcases k with n | n
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact (key n a).symm
  · have e : (σ ^ (n + 1)) ((σ ^ (n + 1))⁻¹ a) = a := by simp
    rw [zpow_negSucc, ← key (n + 1) ((σ ^ (n + 1))⁻¹ a), e]

theorem sameCycle_of_ncyc {q : ℕ} (σ : Equiv.Perm (Fin q)) (h : ncyc σ = 1) (x y : Fin q) : σ.SameCycle x y := by
  have h1 := (Nat.card_eq_one_iff_unique.mp h).1
  exact Quotient.exact (Subsingleton.elim (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x) (Quotient.mk _ y))

theorem conj_rot {q : ℕ} (σ : Equiv.Perm (Fin q)) (h : ncyc σ = 1) :
    ∃ c : Equiv.Perm (Fin q), σ = c⁻¹ * finRotate q * c := by
  rcases q with _ | _ | n
  · exact ⟨1, Subsingleton.elim _ _⟩
  · refine ⟨1, ?_⟩
    apply Equiv.ext
    intro i
    apply Fin.ext
    have h1 := (σ i).2
    have h2 := ((1⁻¹ * finRotate (0 + 1) * 1 : Equiv.Perm (Fin (0 + 1))) i).2
    omega
  · have hsc := sameCycle_of_ncyc σ h
    have hne : σ ≠ 1 := by
      intro h1
      have h01 := hsc 0 1
      rw [h1] at h01
      simp at h01
    obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra hc
      push_neg at hc
      exact hne (Equiv.ext hc)
    have hall : ∀ y, σ y ≠ y := fun y hy => hx (((hsc x y).apply_eq_self_iff).mpr hy)
    have hcyc : σ.IsCycle := ⟨x, hx, fun y _ => hsc x y⟩
    have hsupp : σ.support = Finset.univ := by
      ext y
      simp [Equiv.Perm.mem_support, hall y]
    have hct : σ.cycleType = (finRotate (n + 2)).cycleType := by
      rw [hcyc.cycleType, isCycle_finRotate.cycleType, hsupp, support_finRotate]
    obtain ⟨c, hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr hct)
    exact ⟨c, by rw [← hc]; group⟩

end AlternatingWeights

open AlternatingWeights

theorem wRot : WRot := by
  intro q hq
  have hs : ∀ x y : Fin q, (finRotate q).SameCycle x y := by
    intro x y
    rcases q with _ | _ | n
    · exact x.elim0
    · obtain rfl : x = y := Fin.ext (by have := x.2; have := y.2; omega)
      exact Equiv.Perm.SameCycle.refl _ _
    · exact isCycle_finRotate.sameCycle
        (by rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _)
        (by rw [← Equiv.Perm.mem_support, support_finRotate]; exact Finset.mem_univ _)
  rw [ncyc, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Quotient.inductionOn₂ a b (fun x y => Quotient.sound (hs x y))⟩,
    ⟨Quotient.mk _ ⟨0, hq⟩⟩⟩

theorem wOneOdd : WOneOdd := by
  intro L _ _ N q x hodd hx
  obtain ⟨σ, w, ε⟩ := x
  have hq : 0 < q := hodd.pos
  have hx' : ncyc σ = 1 := hx
  by_cases hw : ∀ i, w (σ i) = w i
  · obtain ⟨w0, rfl⟩ : ∃ w0, w = fun _ => w0 :=
      ⟨w ⟨0, hq⟩, funext fun i => const_of_cycle σ w hw i ⟨0, hq⟩ (sameCycle_of_ncyc σ hx' i ⟨0, hq⟩)⟩
    obtain ⟨c, rfl⟩ := conj_rot σ hx'
    have hrel : AT (N := N) ((c⁻¹ * finRotate q * c, fun _ => w0, ε) : Pat L q) =
        ((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ) • AT (N := N) ((finRotate q, fun _ => w0, ε) : Pat L q) := by
      simp only [AT]
      apply alt_relabel
      intro v
      simp only [tmR, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, tmC_relabel]
    have hrev : ∀ Y : Fin q → HS L N, tmC (finRotate q) (fun _ => w0) (Y ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin q))⁻¹)
        = star (tmC (finRotate q) (fun _ => w0) Y) := by
      intro Y
      rw [← tmC_relabel, rot_rev, tmC_inv_star]
    have hrev' : ∀ Y : Fin q → HS L N, tmC (finRotate q) (fun _ => w0) (Y ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin q)))
        = star (tmC (finRotate q) (fun _ => w0) Y) := by
      intro Y
      simpa using hrev Y
    have hvan : AT (N := N) ((finRotate q, fun _ => w0, true) : Pat L q) = 0 ∨
        AT (N := N) ((finRotate q, fun _ => w0, false) : Pat L q) = 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹)) with hs | hs
      · left
        simp only [AT]
        apply alt_zero' _ ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹) _ hs
        intro v
        simp [tmR, hrev']
      · right
        have h2 := alt_relabel (tmR (N := N) (finRotate q) (fun _ => w0) false)
          (tmR (finRotate q) (fun _ => w0) false) ((Fin.revPerm : Equiv.Perm (Fin q))⁻¹)
          (fun v => by simp [tmR, hrev'])
        rw [hs] at h2
        simp only [AT]
        ext v
        have h3 := congrArg (fun F => F v) h2
        simp at h3
        simp
        linarith
    rcases hvan with h0 | h0 <;> cases ε
    · exact ⟨((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ), w0, by rw [hrel, h0, add_zero]⟩
    · exact ⟨0, w0, by rw [hrel, h0, smul_zero, zero_smul]⟩
    · exact ⟨0, w0, by rw [hrel, h0, smul_zero, zero_smul]⟩
    · exact ⟨((Equiv.Perm.sign c⁻¹ : ℤ) : ℝ), w0, by rw [hrel, h0, zero_add]⟩
  · refine ⟨0, w ⟨0, hq⟩, ?_⟩
    rw [zero_smul]
    have h0 : tmR (N := N) σ w ε = 0 := by
      ext v
      simp only [tmR, tmC, if_neg hw, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
        ContinuousMultilinearMap.zero_apply, map_zero]
    simp only [AT]
    rw [h0, map_zero]

end PositivityTheory.KB.BlockEvaluationBounds

end
