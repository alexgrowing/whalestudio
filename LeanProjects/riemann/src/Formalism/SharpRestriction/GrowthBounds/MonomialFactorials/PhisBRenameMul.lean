import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusAOf
import Formalism.PolynomialDimension.MultinomialDepth.TieOps

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

section Free

variable {k σ : Type} [Field k] {r : ℕ}

theorem tieE_mul_free (w e : Fin r → σ) (F m : MvPolynomial σ k) :
    Formalism.GM.tieE w e (F * m) = Formalism.GM.tieE w e F * m := by
  simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, mul_assoc]

theorem tieF_mul_free (w e : Fin r → σ) (F m : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) m = 0)
    (he : ∀ c, pderiv (e c) m = 0) : Formalism.GM.tieF w e (F * m) = Formalism.GM.tieF w e F * m := by
  have key : ∀ (v : σ) (G : MvPolynomial σ k), pderiv v m = 0 → pderiv v (G * m) = pderiv v G * m := by
    intro v G hv
    rw [Derivation.leibniz, hv, smul_zero, zero_add, smul_eq_mul, mul_comm]
  unfold Formalism.GM.tieF
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  show pderiv (w c) (pderiv (e c) (F * m)) = pderiv (w c) (pderiv (e c) F) * m
  rw [key _ _ (he c), key _ _ (hw c)]

theorem tiePhi_mul_free (w e : Fin r → σ) (o n z : ℕ) (F m : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) m = 0)
    (he : ∀ c, pderiv (e c) m = 0) : Formalism.GM.tiePhi w e o n z (F * m) = Formalism.GM.tiePhi w e o n z F * m := by
  have hE : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieE w e) ^ j) (G * m) = ((Formalism.GM.tieE w e) ^ j) G * m := by
    intro j
    induction j with
    | zero => intro G; rfl
    | succ j ih =>
      intro G
      rw [pow_succ']
      show Formalism.GM.tieE w e (((Formalism.GM.tieE w e) ^ j) (G * m)) =
        Formalism.GM.tieE w e (((Formalism.GM.tieE w e) ^ j) G) * m
      rw [ih, tieE_mul_free]
  have hF : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieF w e) ^ j) (G * m) = ((Formalism.GM.tieF w e) ^ j) G * m := by
    intro j
    induction j with
    | zero => intro G; rfl
    | succ j ih =>
      intro G
      rw [pow_succ']
      show Formalism.GM.tieF w e (((Formalism.GM.tieF w e) ^ j) (G * m)) =
        Formalism.GM.tieF w e (((Formalism.GM.tieF w e) ^ j) G) * m
      rw [ih, tieF_mul_free w e _ m hw he]
  unfold Formalism.GM.tiePhi
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, hF, hE,
    smul_mul_assoc]

theorem foldr_mul_free {ι : Type*} (l : List ι) (f : ι → MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (m : MvPolynomial σ k)
    (h : ∀ i ∈ l, ∀ F, f i (F * m) = f i F * m) (F : MvPolynomial σ k) :
    (l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) (F * m) = (l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) F * m := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), h i (by simp)]

theorem foldr_rename {τ : Type} {ι : Type*} (l : List ι) (em : σ → τ)
    (f : ι → MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (g : ι → MvPolynomial τ k →ₗ[k] MvPolynomial τ k)
    (h : ∀ i ∈ l, ∀ F, g i (rename em F) = rename em (f i F)) (F : MvPolynomial σ k) :
    (l.foldr (fun i acc => g i ∘ₗ acc) LinearMap.id) (rename em F) =
      rename em ((l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) F) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), h i (by simp)]

end Free

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem phisB_rename_mul (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hm : ∀ (a : Fin N) (c : Fin r), pderiv (Sum.inl (Fin.castSucc a, c)) m = 0) :
    phisB p (r := r) G j jp (rename (Formalism.GM.M.chainEmb N r G.T.t) y * m) =
      rename (Formalism.GM.M.chainEmb N r G.T.t) (G.T.phis p (r := r) (G.lettersAt j jp) y) * m := by
  obtain ⟨-, hpos, -, hN⟩ := hB
  have hlt : ∀ i : Fin G.T.t, G.T.pos i + 1 < N := fun i => by have := hpos i; omega
  have hfin0 : ∀ i : Fin G.T.t, Formalism.GM.M.finPos N (G.T.pos i) =
      Fin.castSucc (⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.finPos, Fin.coe_castSucc]
    have := hlt i
    omega
  have hfin1 : ∀ i : Fin G.T.t, Formalism.GM.M.finPos N (G.T.pos i + 1) =
      Fin.castSucc (⟨G.T.pos i + 1, hlt i⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.finPos, Fin.coe_castSucc]
    have := hlt i
    omega
  have hlet0 : ∀ i : Fin G.T.t, G.letterAt (G.T.pos i) = (⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.BlockData.letterAt]
    have := hlt i
    omega
  have hlet1 : ∀ i : Fin G.T.t, G.letterAt (G.T.pos i + 1) = (⟨G.T.pos i + 1, hlt i⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.BlockData.letterAt]
    have := hlt i
    omega
  have hinj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
    intro x y h
    simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
    exact Prod.ext h.1 h.2
  unfold phisB
  rw [foldr_mul_free]
  · congr 1
    unfold Formalism.GM.M.TieData.phis
    refine foldr_rename _ _ _ _ (fun i _ F => ?_) y
    simp only [Formalism.GM.M.TieData.phi, dif_pos (hlt i), Formalism.GM.M.tiePhiAt]
    rw [hfin0, hfin1, hlet0, hlet1]
    exact Formalism.CountingSumsFrames.TO.tiePhi_rename (Formalism.GM.M.chainEmb N r G.T.t) hinj
      (fun c : Fin r => ((⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N), c))
      (fun c : Fin r => ((⟨G.T.pos i + 1, hlt i⟩ : Fin N), c)) _ _ _ F
  · intro i _ F
    exact tiePhi_mul_free _ _ _ _ _ F m (fun c => by rw [hfin0]; exact hm _ c)
      (fun c => by rw [hfin1]; exact hm _ c)

end Level

end Formalism.MainNotions.G.SymmetricFormBlocks

end
