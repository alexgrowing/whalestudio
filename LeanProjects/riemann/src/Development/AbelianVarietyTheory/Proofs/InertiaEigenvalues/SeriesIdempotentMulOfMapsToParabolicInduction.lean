import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfSuppAdds

noncomputable section

namespace GlobalTheory.SerSys.Prod

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders TensorProduct GlobalTheory.GLq.Opp MonoidAlgebra
open scoped Classical

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

private theorem entN_eq_apply_of_lt {A : Type} [Zero A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (i j : ℕ) (hi : i < N)
    (hj : j < N) : entN M i j = M ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [entN, hi, hj]

theorem blk_eq_par (x : Gn g a) (y : Gn g b) : blk a b (a + b) x y = par finSumFinEquiv x 0 y := by
  have hM : (fun i j : Fin (a + b) =>
      if (i : ℕ) < a ∧ (j : ℕ) < a then entN (x : Mt g a) i j
      else if a ≤ (i : ℕ) ∧ a ≤ (j : ℕ) then entN (y : Mt g b) (i - a) (j - a) else 0) =
      ((par finSumFinEquiv x 0 y : Gn g (a + b)) : Mt g (a + b)) := by
    funext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [par_apply]
    rcases i with i | i <;> rcases j with j | j <;> simp [entN]
  show toG _ = _
  rw [hM]
  unfold toG
  rw [dif_pos (Units.isUnit _)]
  exact Units.ext (IsUnit.unit_spec _)

theorem exists_eq_par (u : Gn g (a + b)) (h0 : InPar a (u : Mt g (a + b))) (h1 : tl a (u : Mt g (a + b)) = 1)
    (h2 : br a b (u : Mt g (a + b)) = 1) : ∃ B, u = par finSumFinEquiv (1 : Gn g a) B (1 : Gn g b) := by
  refine ⟨fun i j => (u : Mt g (a + b)) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)), ?_⟩
  have hM : ∀ s t : Fin a ⊕ Fin b, (u : Mt g (a + b)) (finSumFinEquiv s) (finSumFinEquiv t) =
      Matrix.fromBlocks (1 : Mt g a)
        (fun i j => (u : Mt g (a + b)) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)))
        (0 : Matrix (Fin b) (Fin a) (ZMod g)) (1 : Mt g b) s t := by
    intro s t
    rcases s with s | s <;> rcases t with t | t
    · exact (entN_eq_apply_of_lt (u : Mt g (a + b)) s t (Nat.lt_add_right b s.isLt) (Nat.lt_add_right b t.isLt)).symm.trans
        (congrFun (congrFun h1 s) t)
    · rfl
    · exact h0 _ _ (by simp) (by simp)
    · exact (entN_eq_apply_of_lt (u : Mt g (a + b)) (a + s) (a + t) (Nat.add_lt_add_left s.isLt a)
        (Nat.add_lt_add_left t.isLt a)).symm.trans (congrFun (congrFun h2 s) t)
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
  exact (hM s t).trans (par_apply finSumFinEquiv (1 : Gn g a)
    (fun i j => (u : Mt g (a + b)) (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) (1 : Gn g b) s t).symm

theorem single_mul_eN {n : ℕ} (σ : Fin a ⊕ Fin b ≃ Fin n) (B : Matrix (Fin a) (Fin b) (ZMod g)) :
    single (par σ 1 B 1) (1 : ℂ) * eN g σ = eN g σ := by
  unfold eN
  rw [Finset.mul_sum]
  simp only [single_mul_single, one_mul, par_mul, Units.val_one, Matrix.one_mul, Matrix.mul_one, mul_one]
  exact Fintype.sum_equiv (Equiv.addRight B) _ _ (fun C => by simp [add_comm])

private theorem asAlgebraHom_mapDomain_apply_eq_sum {G H U : Type} [Group G] [Fintype G] [Group H] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ H U) (i : G →* H) (c : MonoidAlgebra ℂ G) (w : U) :
    ρ.asAlgebraHom (mapDomainAlgHom ℂ ℂ i c) w = ∑ x, c.coeff x • ρ (i x) w := by
  rw [← comp_alg, GlobalTheory.GLp.Supp.alg_apply]
  rfl

theorem vanish (S : Sys g) {U : Type} [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (Gn g (a + b)) U)
    (F f₁ f₂ : (ZMod g)[X]) (hF : F ≠ f₁ * f₂) (u : U) :
    ρ.asAlgebraHom (eN g finSumFinEquiv * mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (S.e a f₁) *
      mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (S.e b f₂) * S.e (a + b) F) u = 0 := by
  have hNA0 : Commute (eN g finSumFinEquiv)
      (mapDomainAlgHom ℂ ℂ (inA (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))) (S.e a f₁)) :=
    commute_map (inA finSumFinEquiv) (eN g finSumFinEquiv)
      (fun (x : Gn g a) (c : ℂ) => eN_comm finSumFinEquiv x (1 : Gn g b) c) (S.e a f₁)
  have hNB0 : Commute (eN g finSumFinEquiv)
      (mapDomainAlgHom ℂ ℂ (inB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))) (S.e b f₂)) :=
    commute_map (inB finSumFinEquiv) (eN g finSumFinEquiv)
      (fun (y : Gn g b) (c : ℂ) => eN_comm finSumFinEquiv (1 : Gn g a) y c) (S.e b f₂)
  have hAB0 := commute_AB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) (S.e a f₁) (S.e b f₂)
  set N : MonoidAlgebra ℂ (Gn g (a + b)) := eN g finSumFinEquiv with hN
  set A := mapDomainAlgHom ℂ ℂ (inA (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))) (S.e a f₁) with hA
  set B := mapDomainAlgHom ℂ ℂ (inB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))) (S.e b f₂) with hB
  have hNA : Commute N A := hNA0
  have hNB : Commute N B := hNB0
  have hAB : Commute A B := hAB0
  have hAA : A * A = A := by rw [hA, ← map_mul, S.idem]
  have hBB : B * B = B := by rw [hB, ← map_mul, S.idem]
  set v := ρ.asAlgebraHom (N * A * B * S.e (a + b) F) u with hv
  have eA : A * (N * A * B * S.e (a + b) F) = N * A * B * S.e (a + b) F := by
    calc A * (N * A * B * S.e (a + b) F) = (A * N) * A * B * S.e (a + b) F := by simp only [mul_assoc]
      _ = N * (A * A) * B * S.e (a + b) F := by rw [← hNA.eq]; simp only [mul_assoc]
      _ = N * A * B * S.e (a + b) F := by rw [hAA]
  have hvA : ρ.asAlgebraHom A v = v := by
    rw [hv, ← Module.End.mul_apply, ← map_mul, eA]
  have eB : B * (N * A * B * S.e (a + b) F) = N * A * B * S.e (a + b) F := by
    calc B * (N * A * B * S.e (a + b) F) = (B * N) * A * B * S.e (a + b) F := by simp only [mul_assoc]
      _ = N * (B * A) * B * S.e (a + b) F := by rw [← hNB.eq]; simp only [mul_assoc]
      _ = N * A * (B * B) * S.e (a + b) F := by rw [← hAB.eq]; simp only [mul_assoc]
      _ = N * A * B * S.e (a + b) F := by rw [hBB]
  have hvB : ρ.asAlgebraHom B v = v := by
    rw [hv, ← Module.End.mul_apply, ← map_mul, eB]
  have hrad : ∀ w : Gn g (a + b), InPar a (w : Mt g (a + b)) → tl a (w : Mt g (a + b)) = 1 →
      br a b (w : Mt g (a + b)) = 1 → ρ w v = v := by
    intro w h0 h1 h2
    obtain ⟨C, rfl⟩ := exists_eq_par w h0 h1 h2
    have e1 : ρ (par finSumFinEquiv 1 C 1) v =
        ρ.asAlgebraHom (single (par finSumFinEquiv 1 C 1) (1 : ℂ)) v := by
      rw [Representation.asAlgebraHom_single, one_smul]
    have eC : single (par finSumFinEquiv 1 C 1) (1 : ℂ) * (N * A * B * S.e (a + b) F) =
        N * A * B * S.e (a + b) F := by
      calc single (par finSumFinEquiv 1 C 1) (1 : ℂ) * (N * A * B * S.e (a + b) F)
        = (single (par finSumFinEquiv 1 C 1) (1 : ℂ) * eN g finSumFinEquiv) * A * B * S.e (a + b) F := by
            rw [hN]; simp only [mul_assoc]
        _ = N * A * B * S.e (a + b) F := by rw [single_mul_eN, hN]
    rw [e1, hv, ← Module.End.mul_apply, ← map_mul, eC]
  have hsumA : ∑ x : Gn g a, (S.e a f₁).coeff x • ρ (blk a b (a + b) x 1) v = v := by
    simp only [blk_eq_par]
    conv_rhs => rw [← hvA]
    rw [hA, asAlgebraHom_mapDomain_apply_eq_sum]
    rfl
  have hsumB : ∑ y : Gn g b, (S.e b f₂).coeff y • ρ (blk a b (a + b) 1 y) v = v := by
    simp only [blk_eq_par]
    conv_rhs => rw [← hvB]
    rw [hB, asAlgebraHom_mapDomain_apply_eq_sum]
    rfl
  have hm := S.mul a b (a + b) rfl f₁ f₂ U ρ v hrad hsumA hsumB
  have h0 : ρ.asAlgebraHom (S.e (a + b) (f₁ * f₂)) v = 0 := by
    rw [hv, ← Module.End.mul_apply, ← map_mul, ← S.central (a + b) F (N * A * B), ← mul_assoc,
      S.orth _ _ _ (Ne.symm hF), zero_mul, map_zero, LinearMap.zero_apply]
  rw [← hm]
  exact h0

variable {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

theorem has_of_eqv (S : Sys g) {n : ℕ} (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (i : Gn g a →* Gn g n) (T : fixK1 π →ₗ[ℂ] W)
    (h : ∀ x u, T (repK π (i (red g a x)) u) = σ (inc g a x) (T u)) (f : (ZMod g)[X]) (u : fixK1 π)
    (hne : T ((repK π).asAlgebraHom (mapDomainAlgHom ℂ ℂ i (S.e a f)) u) ≠ 0) : Has S σ f := by
  set E := mapDomainAlgHom ℂ ℂ i (S.e a f) with hE
  have hlift : ∀ (y : Gn g a) (w : fixK1 π), σ (lift g a y) (T w) = T (repK π (i y) w) := by
    intro y w
    show σ (inc g a (Function.invFun (red g a) y)) (T w) = _
    rw [← h, red_invFun]
  have key : ∀ w : fixK1 π, actK σ (S.e a f) (T w) = T ((repK π).asAlgebraHom E w) := by
    intro w
    rw [hE, asAlgebraHom_mapDomain_apply_eq_sum, map_sum]
    simp only [actK, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, hlift]
  refine ⟨T ((repK π).asAlgebraHom E u), ?_, ?_⟩
  · rw [mem_principalCongruenceFixedVectors_iff]
    intro k hk
    rw [← h, hk]
    simp
  · rw [key, ← Module.End.mul_apply, ← map_mul, hE, ← map_mul, S.idem]
    exact hne

private theorem inc_apply_eq_algebraMap {n : ℕ} (k : GL (Fin n) ℤ_[g]) (i j : Fin n) :
    ((inc g n k : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) i j =
      algebraMap ℤ_[g] ℚ_[g] ((k : Matrix (Fin n) (Fin n) ℤ_[g]) i j) := rfl

private theorem det_inc_eq_map_det {n : ℕ} (k : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.det (inc g n k) =
      Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
  apply Units.ext
  show ((inc g n k : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]).det =
    algebraMap ℤ_[g] ℚ_[g] ((k : Matrix (Fin n) (Fin n) ℤ_[g]).det)
  rw [RingHom.map_det]
  rfl

private theorem levi_par_of_apply_eq_zero_of_lt {a b : ℕ} {V₀ W₀ W₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup W₀]
    [Module ℂ W₀] [AddCommGroup W₁] [Module ℂ W₁] (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V₀)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W₀) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W₁)
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V₀ →ₗ[ℂ] W₀ ⊗[ℂ] W₁) (h₁ : IsUnram ν₁) (h₂ : IsUnram ν₂)
    (hΛ : ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) →
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) →
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) →
      ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
        TensorProduct.map (σ x) (ρ y) (Λ v))
    (x : GL (Fin a) ℤ_[g]) (B : Matrix (Fin a) (Fin b) ℤ_[g]) (y : GL (Fin b) ℤ_[g]) (w : V₀) :
    Λ (π (inc g (a + b) (parZ x B y)) w) = TensorProduct.map (σ (inc g a x)) (ρ (inc g b y)) (Λ w) := by
  have c1 : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) →
      ((inc g (a + b) (parZ x B y) : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0 := by
    intro i j hj hi
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
    rw [inc_apply_eq_algebraMap, parZ_apply]
    rcases s with s | s
    · simp at hi
      omega
    · rcases t with t | t
      · simp
      · simp at hj
  have c2 : ∀ i j : Fin a, ((inc g a x : GL (Fin a) ℚ_[g]) : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      entN ((inc g (a + b) (parZ x B y) : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j := by
    intro i j
    rw [entN_eq_apply_of_lt _ _ _ (Nat.lt_add_right b i.isLt) (Nat.lt_add_right b j.isLt)]
    have ei : (⟨i, Nat.lt_add_right b i.isLt⟩ : Fin (a + b)) = finSumFinEquiv (Sum.inl i) := Fin.ext (by simp)
    have ej : (⟨j, Nat.lt_add_right b j.isLt⟩ : Fin (a + b)) = finSumFinEquiv (Sum.inl j) := Fin.ext (by simp)
    rw [ei, ej, inc_apply_eq_algebraMap, inc_apply_eq_algebraMap, parZ_apply, Matrix.fromBlocks_apply₁₁]
  have c3 : ∀ i j : Fin b, ((inc g b y : GL (Fin b) ℚ_[g]) : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      entN ((inc g (a + b) (parZ x B y) : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g])
        (a + i) (a + j) := by
    intro i j
    rw [entN_eq_apply_of_lt _ _ _ (Nat.add_lt_add_left i.isLt a) (Nat.add_lt_add_left j.isLt a)]
    have ei : (⟨a + i, Nat.add_lt_add_left i.isLt a⟩ : Fin (a + b)) = finSumFinEquiv (Sum.inr i) := Fin.ext (by simp)
    have ej : (⟨a + j, Nat.add_lt_add_left j.isLt a⟩ : Fin (a + b)) = finSumFinEquiv (Sum.inr j) := Fin.ext (by simp)
    rw [ei, ej, inc_apply_eq_algebraMap, inc_apply_eq_algebraMap, parZ_apply, Matrix.fromBlocks_apply₂₂]
  rw [hΛ _ _ _ c1 c2 c3 w, det_inc_eq_map_det, det_inc_eq_map_det, h₁, h₂, mul_one, Units.val_one, one_smul]

private theorem exists_blocks_entN_eq {a b : ℕ} (p : GL (Fin (a + b)) ℚ_[g])
    (hp : ∀ i j : Fin (a + b), j < i → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) :
    ∃ (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) ∧
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) := by
  have hdiag : ∀ i, (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i i ≠ 0 := by
    have h1 : (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 p.isUnit).ne_zero
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hp i j hij)] at h1
    exact fun i => Finset.prod_ne_zero_iff.1 h1 i (Finset.mem_univ _)
  let xm : Matrix (Fin a) (Fin a) ℚ_[g] := fun i j => entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j
  let ym : Matrix (Fin b) (Fin b) ℚ_[g] := fun i j =>
    entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)
  have hx : IsUnit xm.det := by
    have ht : xm.BlockTriangular id := by
      intro i j hij
      show entN _ _ _ = _
      rw [entN_eq_apply_of_lt _ _ _ (Nat.lt_add_right b i.isLt) (Nat.lt_add_right b j.isLt)]
      exact hp _ _ (by rw [Fin.mk_lt_mk]; exact hij)
    rw [Matrix.det_of_isUpperTriangular ht]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    show entN _ _ _ ≠ 0
    rw [entN_eq_apply_of_lt _ _ _ (Nat.lt_add_right b i.isLt) (Nat.lt_add_right b i.isLt)]
    exact hdiag _
  have hy : IsUnit ym.det := by
    have ht : ym.BlockTriangular id := by
      intro i j hij
      show entN _ _ _ = _
      rw [entN_eq_apply_of_lt _ _ _ (Nat.add_lt_add_left i.isLt a) (Nat.add_lt_add_left j.isLt a)]
      exact hp _ _ (by rw [Fin.mk_lt_mk]; exact Nat.add_lt_add_left hij a)
    rw [Matrix.det_of_isUpperTriangular ht]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    show entN _ _ _ ≠ 0
    rw [entN_eq_apply_of_lt _ _ _ (Nat.add_lt_add_left i.isLt a) (Nat.add_lt_add_left i.isLt a)]
    exact hdiag _
  exact ⟨Matrix.nonsingInvUnit xm hx, Matrix.nonsingInvUnit ym hy, fun i j => rfl, fun i j => rfl⟩

private theorem nonzero_lemma_7 {a b : ℕ} {V₀ W₀ W₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup W₀]
    [Module ℂ W₀] [AddCommGroup W₁] [Module ℂ W₁] (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V₀)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W₀) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W₁)
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V₀ →ₗ[ℂ] W₀ ⊗[ℂ] W₁)
    (hΛ : ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) →
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) →
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) →
      ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
        TensorProduct.map (σ x) (ρ y) (Λ v))
    (hπ : IsIrrRep π) (hΛ0 : Λ ≠ 0) (v0 : V₀) (hv0 : v0 ≠ 0) :
    ∃ k : GL (Fin (a + b)) ℤ_[g], Λ (π (inc g (a + b) k) v0) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let Z : Submodule ℂ V₀ := ⨅ h : GL (Fin (a + b)) ℚ_[g], LinearMap.ker (Λ ∘ₗ π h)
  have hmem : ∀ w, w ∈ Z ↔ ∀ h, Λ (π h w) = 0 := by
    intro w
    simp [Z, Submodule.mem_iInf]
  have hZ : ∀ h, ∀ w ∈ Z, π h w ∈ Z := by
    intro h w hw
    rw [hmem] at hw ⊢
    intro h'
    rw [← Module.End.mul_apply, ← map_mul]
    exact hw _
  rcases hπ.2 Z hZ with hb | ht
  · apply hv0
    have hv : v0 ∈ Z := by
      rw [hmem]
      intro h
      obtain ⟨p, k, hp, rfl⟩ := exists_upper_mul_inc g (a + b) h
      obtain ⟨x, y, hx, hy⟩ := exists_blocks_entN_eq p hp
      rw [map_mul, Module.End.mul_apply,
        hΛ p x y (fun i j hj hi => hp i j (by rw [Fin.lt_def]; omega)) hx hy, hcon k, map_zero, smul_zero]
    rw [hb] at hv
    exact (Submodule.mem_bot ℂ).1 hv
  · apply hΛ0
    refine LinearMap.ext fun w => ?_
    have hw : w ∈ Z := ht ▸ Submodule.mem_top
    have h1 := (hmem w).1 hw 1
    simpa using h1

theorem series_of_mapsToProd (g : ℕ) [Fact g.Prime] (S : Sys g) (n a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W']
    [Module ℂ W'] (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (hπ : IsIrrRep π) (hM : MapsToProd π σ ρ) (F : (ZMod g)[X]) (hF : Has S π F) :
    ∃ f f', Has S σ f ∧ Has S ρ f' ∧ F = f * f' := by
  obtain ⟨hn, ν₁, ν₂, Λ, hν₁, hν₂, hΛ0, hΛ⟩ := hM
  subst hn
  obtain ⟨v, hv, hvF⟩ := hF
  obtain ⟨-, hfix⟩ := finite_group_acts_on_fixK1 g (a + b) V π
  set v0 := actK π (S.e (a + b) F) v with hv0def
  have hv0 : v0 ∈ fixK1 π := by
    rw [hv0def]
    simp only [actK, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ((hfix v hv).1 x)
  have hv0F : actK π (S.e (a + b) F) v0 = v0 := by
    rw [hv0def, ← (hfix v hv).2.2.2.1, S.idem]
  obtain ⟨k, hk⟩ := nonzero_lemma_7 π σ ρ ν₁ ν₂ Λ hΛ hπ hΛ0 v0 hvF
  have hv1 : π (inc g (a + b) k) v0 ∈ fixK1 π := padicIntGL_smul_mem_principalCongruenceFixed π hv0 k
  have hv1F : actK π (S.e (a + b) F) (π (inc g (a + b) k) v0) = π (inc g (a + b) k) v0 := by
    have e1 : π (inc g (a + b) k) v0 = actK π (single (red g (a + b) k) 1) v0 := by
      rw [actK_single, one_smul]
      exact (hfix v0 hv0).2.1 k
    rw [e1, ← (hfix v0 hv0).2.2.2.1, S.central, (hfix v0 hv0).2.2.2.1, hv0F]
  set u1 : fixK1 π := ⟨π (inc g (a + b) k) v0, hv1⟩ with hu1
  have hu1F : (repK π).asAlgebraHom (S.e (a + b) F) u1 = u1 :=
    Subtype.ext (by rw [repK_alg]; exact hv1F)
  set T0 : fixK1 π →ₗ[ℂ] W ⊗[ℂ] W' := Λ ∘ₗ (fixK1 π).subtype with hT0
  have hT0u1 : T0 u1 ≠ 0 := hk
  have hrad : ∀ (C : Matrix (Fin a) (Fin b) (ZMod g)),
      T0 ∘ₗ repK π (par finSumFinEquiv 1 C 1) = T0 := by
    intro C
    refine LinearMap.ext fun w => ?_
    have hr : red g (a + b) (parZ 1 (C.map fun c : ZMod g => ((c.val : ℕ) : ℤ_[g])) 1) =
        par finSumFinEquiv 1 C 1 := by
      rw [red_parZ, map_one, map_one]
      congr 1
      ext i j
      simp
    simp only [hT0, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [← hr, repK_red, levi_par_of_apply_eq_zero_of_lt π σ ρ ν₁ ν₂ Λ hν₁ hν₂ hΛ]
    simp
  have hN : ∀ w, T0 ((repK π).asAlgebraHom (eN g finSumFinEquiv) w) = T0 w :=
    eN_left finSumFinEquiv (repK π) T0 hrad
  have hTA : ∀ (P : W ⊗[ℂ] W' →ₗ[ℂ] W),
      (∀ (A : W →ₗ[ℂ] W) (y : W ⊗[ℂ] W'), P (TensorProduct.map A LinearMap.id y) = A (P y)) →
      ∀ x u, (P ∘ₗ T0) (repK π (inA finSumFinEquiv (red g a x)) u) = σ (inc g a x) ((P ∘ₗ T0) u) := by
    intro P hP x u
    have hr : red g (a + b) (parZ x 0 1) = inA finSumFinEquiv (red g a x) := by
      show _ = par _ _ _ _
      rw [red_parZ, map_one]
      congr 1
      ext i j
      simp
    have hρ1 : ρ (inc g b 1) = LinearMap.id := by rw [map_one, map_one]; rfl
    simp only [hT0, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [← hr, repK_red, levi_par_of_apply_eq_zero_of_lt π σ ρ ν₁ ν₂ Λ hν₁ hν₂ hΛ, hρ1, hP]
  have hTB : ∀ (P : W ⊗[ℂ] W' →ₗ[ℂ] W'),
      (∀ (A : W' →ₗ[ℂ] W') (y : W ⊗[ℂ] W'), P (TensorProduct.map LinearMap.id A y) = A (P y)) →
      ∀ y u, (P ∘ₗ T0) (repK π (inB finSumFinEquiv (red g b y)) u) = ρ (inc g b y) ((P ∘ₗ T0) u) := by
    intro P hP y u
    have hr : red g (a + b) (parZ 1 0 y) = inB finSumFinEquiv (red g b y) := by
      show _ = par _ _ _ _
      rw [red_parZ, map_one]
      congr 1
      ext i j
      simp
    have hσ1 : σ (inc g a 1) = LinearMap.id := by rw [map_one, map_one]; rfl
    simp only [hT0, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [← hr, repK_red, levi_par_of_apply_eq_zero_of_lt π σ ρ ν₁ ν₂ Λ hν₁ hν₂ hΛ, hσ1, hP]
  by_contra hno
  push Not at hno
  apply hT0u1
  obtain ⟨Ta, hTa⟩ := S.sum a
  obtain ⟨Tb, hTb⟩ := S.sum b
  have hterm : ∀ f₁ f₂, T0 ((repK π).asAlgebraHom (eN g finSumFinEquiv *
      mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (S.e a f₁) *
      mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (S.e b f₂) * S.e (a + b) F) u1) = 0 := by
    intro f₁ f₂
    by_cases hF : F = f₁ * f₂
    · have e : eN g finSumFinEquiv * mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (S.e a f₁) *
          mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (S.e b f₂) * S.e (a + b) F =
          eN g finSumFinEquiv * ((mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (S.e a f₁) *
          mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (S.e b f₂)) * S.e (a + b) F) := by
        simp only [mul_assoc]
      rw [e, map_mul, Module.End.mul_apply, hN, map_mul, Module.End.mul_apply, hu1F]
      by_contra hz
      obtain ⟨P, hP0, hP⟩ := exists_dual_right _ hz
      obtain ⟨P', hP0', hP'⟩ := exists_dual_left _ hz
      have h1 : Has S σ f₁ := has_of_eqv S π σ (inA finSumFinEquiv) (P ∘ₗ T0) (hTA P hP) f₁
        ((repK π).asAlgebraHom (mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (S.e b f₂)) u1) (by
          rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
          exact hP0)
      have h2 : Has S ρ f₂ := has_of_eqv S π ρ (inB finSumFinEquiv) (P' ∘ₗ T0) (hTB P' hP') f₂
        ((repK π).asAlgebraHom (mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (S.e a f₁)) u1) (by
          rw [LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
            ← (commute_AB (g := g) finSumFinEquiv (S.e a f₁) (S.e b f₂)).eq]
          exact hP0')
      exact hno f₁ f₂ h1 h2 hF
    · rw [vanish S (repK π) F f₁ f₂ hF u1, map_zero]
  have hone : (1 : MonoidAlgebra ℂ (Gn g (a + b))) = ∑ f₁ ∈ Ta, ∑ f₂ ∈ Tb,
      mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (S.e a f₁) * mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (S.e b f₂) := by
    rw [← Finset.sum_mul_sum, ← map_sum (mapDomainAlgHom ℂ ℂ (inA (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))))
      (S.e a) Ta, ← map_sum (mapDomainAlgHom ℂ ℂ (inB (g := g) (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))))
      (S.e b) Tb, hTa, hTb, map_one, map_one, one_mul]
  have hX : eN g finSumFinEquiv * 1 * S.e (a + b) F = ∑ f₁ ∈ Ta, ∑ f₂ ∈ Tb, eN g finSumFinEquiv *
      mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (S.e a f₁) *
      mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (S.e b f₂) * S.e (a + b) F := by
    rw [hone, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f₂ _ => ?_
    simp only [mul_assoc]
  have e1 : T0 u1 = T0 ((repK π).asAlgebraHom (eN g finSumFinEquiv * 1 * S.e (a + b) F) u1) := by
    rw [mul_one, map_mul, Module.End.mul_apply, hu1F, hN]
  have hsum : T0 u1 = ∑ f₁ ∈ Ta, ∑ f₂ ∈ Tb, T0 ((repK π).asAlgebraHom (eN g finSumFinEquiv *
      mapDomainAlgHom ℂ ℂ (inA finSumFinEquiv) (S.e a f₁) *
      mapDomainAlgHom ℂ ℂ (inB finSumFinEquiv) (S.e b f₂) * S.e (a + b) F) u1) := by
    rw [e1, hX, map_sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun f₁ _ => ?_
    rw [map_sum, LinearMap.sum_apply, map_sum]
  rw [hsum]
  exact Finset.sum_eq_zero fun f₁ _ => Finset.sum_eq_zero fun f₂ _ => hterm f₁ f₂

end GlobalTheory.SerSys.Prod
