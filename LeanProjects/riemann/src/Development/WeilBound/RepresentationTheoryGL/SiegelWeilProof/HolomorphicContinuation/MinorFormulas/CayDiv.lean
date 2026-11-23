import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.CayDivA

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

variable {n : ℕ}

def Sop (s : ℂ) (m n : ℕ) : Set (Module.End ℂ (Fm n)) :=
  Set.range fun x : Bool × Fin n × Fin n => opH s m x.1 x.2.1 x.2.2

theorem list_prod_eq_foldr {ρ : ℕ} (f : Fin ρ → Module.End ℂ (Fm n)) (L : List (Fin ρ)) :
    (L.map f).prod = L.foldr (fun k g => f k ∘ₗ g) LinearMap.id := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, Module.End.mul_eq_comp]; rfl

theorem rcp_adjoin (s : ℂ) (m : ℕ) {T : Module.End ℂ (Fm n)} (hT : T ∈ Algebra.adjoin ℂ (Sop s m n)) : RCP T := by
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact opH_rcp s m _ _ _
  | algebraMap r =>
    intro R q
    simp only [Module.algebraMap_end_apply, smul_mul_assoc]
  | add x y _ _ hx hy => exact rcp_add hx hy
  | mul x y _ _ hx hy => rw [Module.End.mul_eq_comp]; exact rcp_comp hx hy

theorem divZ_mono {i j : ℕ} {Q : Fm n} (hQ : DivZ i Q) (h : j ≤ i) : DivZ j Q := fun e =>
  (pow_dvd_pow _ h).trans (hQ e)

theorem cayDiv_of : CayDivOf := by
  intro hC hMZ hMZ' hNull n m s hs hm
  classical
  have hcomm : ∀ a ∈ Sop s m n, ∀ b ∈ Sop s m n, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hC n s m x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2
  letI : CommRing (Algebra.adjoin ℂ (Sop s m n)) := Algebra.adjoinCommRingOfComm ℂ hcomm
  let g : Bool × Fin n × Fin n → Algebra.adjoin ℂ (Sop s m n) :=
    fun x => ⟨opH s m x.1 x.2.1 x.2.2, Algebra.subset_adjoin ⟨x, rfl⟩⟩
  let φ : PAB n →ₐ[ℂ] Algebra.adjoin ℂ (Sop s m n) := MvPolynomial.aeval g
  have hφX : ∀ x, ((φ (X x) : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) = opH s m x.1 x.2.1 x.2.2 :=
    fun x => by simp [φ, g]
  have hcoe_det : ∀ {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) (Algebra.adjoin ℂ (Sop s m n))),
      ((M.det : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) =
        ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : ℂ) •
          (List.finRange ρ).foldr (fun k g => ((M k (σ k) : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) ∘ₗ g)
            LinearMap.id := by
    intro ρ M
    rw [← Matrix.det_transpose, Matrix.det_apply]
    change (Algebra.adjoin ℂ (Sop s m n)).val _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, Fin.prod_univ_def, map_list_prod, List.map_map,
      ← list_prod_eq_foldr]
    rfl
  have hcoe_minor : ∀ (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n),
      ((φ (minorPolynomial b I J) : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) = minorOp s m b I J := by
    intro b ρ I J
    rw [show minorPolynomial b I J = Matrix.det (Matrix.of fun p q : Fin ρ => (X (b, I p, J q) : PAB n)) from rfl,
      AlgHom.map_det, hcoe_det]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hφX]
    rfl
  have hcoe_cay : ((φ (Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))) :
      Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) = cayF s m := by
    rw [show Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) =
        Matrix.det (Matrix.of fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) from rfl,
      AlgHom.map_det, hcoe_det]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_add, Subalgebra.coe_add, hφX]
    rfl
  have hpow : ∀ (x : Algebra.adjoin ℂ (Sop s m n)) (N : ℕ) (Q : Fm n),
      ((x ^ N : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) Q = (x : Module.End ℂ (Fm n))^[N] Q := by
    intro x N Q
    rw [SubmonoidClass.coe_pow, Module.End.pow_apply]
  have hdivA : ∀ (x : Algebra.adjoin ℂ (Sop s m n)) {i : ℕ} {Q : Fm n}, DivZ i Q →
      DivZ i ((x : Module.End ℂ (Fm n)) Q) := fun x _ _ hQ => divZ_of_rcp (rcp_adjoin s m x.2) hQ
  have hr0 : 0 < n - m := Nat.sub_pos_of_lt hm
  obtain ⟨N₁, hN₁⟩ := hNull n m hm (n - m)
  refine ⟨N₁, fun N hN => ?_⟩
  have hmem := Ideal.mul_mem_left _
    ((Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))) ^ (N - N₁)) hN₁
  rw [pow_sub_mul_pow _ hN] at hmem
  have H := Submodule.span_induction
    (p := fun x _ => DivZ (n - m) (((φ x : Algebra.adjoin ℂ (Sop s m n)) : Module.End ℂ (Fm n)) 1))
    ?mem ?zero ?add ?smul hmem
  · rw [map_pow, hpow, hcoe_cay] at H
    exact H
  case mem =>
    intro x hx
    obtain ⟨i, j, hij, hcase⟩ := hx
    rcases hcase with ⟨hi, hj, rfl⟩ | ⟨hi, hj, I, J, rfl⟩ | ⟨hi, hj, I, J, rfl⟩ | ⟨hi, hj, I, J, I', J', rfl⟩
    · omega
    · rw [map_pow, hpow, hcoe_minor]
      exact divZ_mono (hMZ' n s hs m j (n - m) (by omega) I J) (by omega)
    · rw [map_pow, hpow, hcoe_minor]
      exact divZ_mono (hMZ n s hs m i (n - m) (by omega) I J) (by omega)
    · rw [map_mul, map_pow, map_pow, Subalgebra.coe_mul, Module.End.mul_apply, hpow, hpow, hcoe_minor, hcoe_minor]
      have hAT : (minorOp s m true I' J')^[n - m] 1 ∈ AT n :=
        iterate_AT (fun Q hQ => minorOp_true_AT s m I' J' hQ) _ (Subalgebra.one_mem _)
      have hpd := pderiv_false_AT hAT
      rw [← mul_one ((minorOp s m true I' J')^[n - m] 1), lcp_iterate (minorOp_false_lcp s m I J hpd)]
      exact divZ_mono (divZ_mul (hMZ' n s hs m j (n - m) (by omega) I' J') (hMZ n s hs m i (n - m) (by omega) I J))
        (by omega)
  case zero => simp [divZ_zero]
  case add =>
    intro x y _ _ hx hy
    rw [map_add, Subalgebra.coe_add, LinearMap.add_apply]
    exact divZ_add hx hy
  case smul =>
    intro a x _ hx
    rw [smul_eq_mul, map_mul, Subalgebra.coe_mul, Module.End.mul_apply]
    exact hdivA _ hx

end PositivityTheory.Rg.Sw.SP
