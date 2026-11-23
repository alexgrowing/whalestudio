import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
namespace GlobalTheory.CapelliRoots

theorem kill_left {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (p : Fin n) (ℓ : V →ₗ[ℂ] ℂ) (h1 : ∀ b, b ≠ p → ∀ v, ℓ (E p b v) = 0) :
    ∀ (L : List (Module.End ℂ V)), (∀ X ∈ L, ∃ (x : ℂ) (c d : Fin n), d ≠ p ∧ X = Formalism.REAL.Tm E x c d) →
      ∀ b, b ≠ p → ∀ w, ℓ (L.prod (E p b w)) = 0 := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _ b hb w; simpa using h1 b hb w
  | append_singleton L X ih =>
    intro hL b hb w
    obtain ⟨x, c, d, hd, rfl⟩ := hL X (by simp)
    have hL' : ∀ Y ∈ L, ∃ (x : ℂ) (c d : Fin n), d ≠ p ∧ Y = Formalism.REAL.Tm E x c d :=
      fun Y hY => hL Y (by simp [hY])
    have hS : ∀ s : ℂ, algebraMap ℂ (Module.End ℂ V) s * E p b = E p b * algebraMap ℂ _ s :=
      fun s => Algebra.commutes s _
    have h := hE c d p b
    rw [if_neg hd] at h
    have h' := sub_eq_iff_eq_add.mp h
    have hcomm : Formalism.REAL.Tm E x c d * E p b =
        E p b * Formalism.REAL.Tm E x c d - (if b = c then E p d else 0) := by
      unfold Formalism.REAL.Tm
      split_ifs with hcd hbc hbc
      · rw [add_mul, mul_add, hS, h', if_pos hbc]; abel
      · rw [add_mul, mul_add, hS, h', if_neg hbc]; abel
      · rw [add_mul, mul_add, zero_mul, mul_zero, h', if_pos hbc]; abel
      · rw [add_mul, mul_add, zero_mul, mul_zero, h', if_neg hbc]; abel
    have hw := LinearMap.congr_fun hcomm w
    rw [List.prod_append, List.prod_singleton, Module.End.mul_apply]
    by_cases hbc : b = c
    · simp only [hbc, if_true, LinearMap.sub_apply, Module.End.mul_apply] at hw
      subst hbc
      rw [hw, map_sub, map_sub, ih hL' b hb, ih hL' d hd, sub_zero]
    · simp only [hbc, if_false, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, sub_zero] at hw
      rw [hw, ih hL' b hb]

theorem poly_of_list {V : Type} [AddCommGroup V] [Module ℂ V] :
    ∀ (L : List (ℂ → Module.End ℂ V)),
      (∀ f ∈ L, ∃ (c : ℂ) (D : Module.End ℂ V), ∀ u, f u = algebraMap ℂ _ (c * u) + D) →
      ∀ (ℓ : V →ₗ[ℂ] ℂ) (w : V), ∃ P : Polynomial ℂ, ∀ u, ℓ ((L.map (fun f => f u)).prod w) = P.eval u := by
  intro L
  induction L with
  | nil => intro _ ℓ w; exact ⟨Polynomial.C (ℓ w), by simp⟩
  | cons f L ih =>
    intro hL ℓ w
    obtain ⟨c, D, hf⟩ := hL f (by simp)
    have hL' := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    obtain ⟨P1, hP1⟩ := ih hL' ℓ w
    obtain ⟨P2, hP2⟩ := ih hL' (ℓ ∘ₗ D) w
    refine ⟨Polynomial.C c * Polynomial.X * P1 + P2, fun u => ?_⟩
    have e2 := hP2 u
    simp only [LinearMap.comp_apply] at e2
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hf, LinearMap.add_apply, map_add,
      Module.algebraMap_end_apply, map_smul, smul_eq_mul, hP1, e2, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X]

theorem two_roots {n : ℕ} (f : Fin n → ℂ) (r1 r2 : ℂ) (G : Polynomial ℂ) (k : ℂ) (hk : k ≠ 0)
    (h : ∀ u, (∏ s, (u - f s)) * k = (u - r1) * (u - r2) * G.eval u) :
    ∃ i j, i ≠ j ∧ f i = r2 ∧ f j = r1 := by
  open Polynomial in
  have hQ : (∏ s, (X - C (f s))) * C k = (X - C r1) * (X - C r2) * G := by
    apply Polynomial.funext; intro u
    simp [Polynomial.eval_prod, h u]
  open Polynomial in
  have hdvd : (X - C r1) * (X - C r2) ∣ ∏ s, (X - C (f s)) := by
    refine ⟨G * C k⁻¹, ?_⟩
    calc ∏ s, (X - C (f s)) = (∏ s, (X - C (f s))) * C k * C k⁻¹ := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hk, C_1, mul_one]
      _ = _ := by rw [hQ]; ring
  open Polynomial in
  have hne : (∏ s, (X - C (f s))) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun s _ => X_sub_C_ne_zero _)
  have hle := Polynomial.roots.le_of_dvd hne hdvd
  open Polynomial in
  have hr : (∏ s, (X - C (f s))).roots = Finset.univ.val.map f := by
    rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map f), Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl
  open Polynomial in
  have hr2 : ((X - C r1) * (X - C r2)).roots = r1 ::ₘ {r2} := by
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C, roots_X_sub_C]
    rfl
  rw [hr, hr2] at hle
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp (Multiset.mem_of_le hle (Multiset.mem_cons_self _ _))
  have hu : Finset.univ.val = j ::ₘ (Finset.univ.val.erase j) :=
    (Multiset.cons_erase (Finset.mem_univ_val j)).symm
  rw [hu, Multiset.map_cons, hj, Multiset.cons_le_cons_iff] at hle
  obtain ⟨i, hi, hi2⟩ := Multiset.mem_map.mp (Multiset.mem_of_le hle (Multiset.mem_singleton_self _))
  refine ⟨i, j, ?_, hi2, hj⟩
  exact ((Multiset.Nodup.mem_erase_iff Finset.univ.nodup).mp hi).1

end GlobalTheory.CapelliRoots

namespace GlobalTheory.CapelliRoots
open Formalism.REAL

theorem Tm_ne {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (x : ℂ) (a b : Fin n) (h : a ≠ b) : Formalism.REAL.Tm E x a b = E a b := by
  simp [Formalism.REAL.Tm, h]

theorem Tm_diag_apply {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (ℓ : V →ₗ[ℂ] ℂ) (a : Fin n) (γ : ℂ) (h : ∀ v, ℓ (E a a v) = γ * ℓ v) (x : ℂ) (w : V) :
    ℓ (Formalism.REAL.Tm E x a a w) = (x + γ) * ℓ w := by
  simp [Formalism.REAL.Tm, Module.algebraMap_end_apply, h, add_mul]

theorem Tm_comm {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (p c d : Fin n) (hc : c ≠ p) (hd : d ≠ p) (x y : ℂ) :
    Commute (Formalism.REAL.Tm E y p p) (Formalism.REAL.Tm E x c d) := by
  have h := hE p p c d
  rw [if_neg (Ne.symm hc), if_neg hd, sub_zero, sub_eq_zero] at h
  unfold Formalism.REAL.Tm
  rw [if_pos rfl]
  refine Commute.add_left (Algebra.commute_algebraMap_left _ _) (Commute.add_right ?_ h)
  split_ifs
  · exact Algebra.commute_algebraMap_right _ _
  · exact Commute.zero_right _

theorem Tm_affine {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (g : ℂ) (a b : Fin n) : ∃ (c : ℂ) (D : Module.End ℂ V), ∀ u,
      Formalism.REAL.Tm E (u - g) a b = algebraMap ℂ _ (c * u) + D := by
  by_cases h : a = b
  · refine ⟨1, algebraMap ℂ _ (-g) + E a b, fun u => ?_⟩
    simp only [Formalism.REAL.Tm, if_pos h, one_mul, ← add_assoc, ← map_add, sub_eq_add_neg]
  · exact ⟨0, E a b, fun u => by simp [Formalism.REAL.Tm, h]⟩

theorem perm_ends {m : ℕ} (p q : Fin (m + 2)) (hpq : p ≠ q) :
    ∃ τ : Equiv.Perm (Fin (m + 2)), τ 0 = q ∧ τ (Fin.last (m + 1)) = p := by
  have hx : Equiv.swap 0 q p ≠ 0 := by
    intro h
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact hpq h
  have h0l : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by simp [Fin.ext_iff]
  refine ⟨Equiv.swap 0 q * Equiv.swap (Fin.last (m + 1)) (Equiv.swap 0 q p), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h0l hx.symm, Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

theorem term_eq {V : Type} [AddCommGroup V] [Module ℂ V] {m : ℕ} (E : Fin (m+2) → Fin (m+2) → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (p q : Fin (m+2)) (ℓ : V →ₗ[ℂ] ℂ) (α β : ℂ)
    (h1 : ∀ b, b ≠ p → ∀ v, ℓ (E p b v) = 0) (h2 : ∀ a, a ≠ q → ∀ v, ℓ (E a q v) = 0)
    (h3 : ∀ v, ℓ (E p p v) = α * ℓ v) (h4 : ∀ v, ℓ (E q q v) = β * ℓ v)
    (τ σ : Equiv.Perm (Fin (m+2))) (hτ0 : τ 0 = q) (hτl : τ (Fin.last (m+1)) = p) (u : ℂ) (v : V) :
    ℓ ((List.ofFn fun k : Fin (m+2) => Formalism.REAL.Tm E (u - ((k : ℕ) : ℂ)) (τ (σ k)) (τ k)).prod v) =
      (u + β) * (u - ((m : ℂ) + 1) + α) *
        (if σ 0 = 0 ∧ σ (Fin.last (m+1)) = Fin.last (m+1) then
          ℓ ((List.ofFn fun i : Fin m => Formalism.REAL.Tm E (u - (((i.castSucc.succ : Fin (m+2)) : ℕ) : ℂ))
              (τ (σ i.castSucc.succ)) (τ i.castSucc.succ)).prod v) else 0) := by
  set F : Fin (m+2) → Module.End ℂ V := fun k => Formalism.REAL.Tm E (u - ((k : ℕ) : ℂ)) (τ (σ k)) (τ k) with hF
  by_cases hl : σ (Fin.last (m+1)) = Fin.last (m+1)
  · by_cases h0 : σ 0 = 0
    · rw [if_pos ⟨h0, hl⟩, List.ofFn_succ, List.ofFn_succ']
      simp only [List.prod_cons, List.concat_eq_append, List.prod_append, List.prod_singleton,
        List.prod_nil, mul_one, Module.End.mul_apply]
      have hcomm : Commute (F (Fin.last m).succ)
          (List.ofFn fun i : Fin m => F i.castSucc.succ).prod := by
        apply Commute.list_prod_right
        intro X hX
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hX
        have hne : (i.castSucc.succ : Fin (m+2)) ≠ Fin.last (m+1) := by
          simp [Fin.ext_iff]; omega
        have hσne : σ i.castSucc.succ ≠ Fin.last (m+1) := fun h => hne (σ.injective (h.trans hl.symm))
        simp only [hF, Fin.succ_last, hl, hτl]
        exact Tm_comm E hE p _ _ (fun h => hσne (τ.injective (h.trans hτl.symm)))
          (fun h => hne (τ.injective (h.trans hτl.symm))) _ _
      have hw := LinearMap.congr_fun hcomm.eq v
      simp only [Module.End.mul_apply] at hw
      rw [← hw]
      simp only [hF, h0, hτ0, Fin.succ_last, hl, hτl]
      rw [Tm_diag_apply E ℓ q β h4, Tm_diag_apply E ℓ p α h3]
      simp only [Fin.val_zero, Fin.val_last, Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one, Nat.cast_succ]
      ring
    · rw [if_neg (fun h => h0 h.1), mul_zero, List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
      have hne : τ (σ 0) ≠ q := fun h => h0 (τ.injective (h.trans hτ0.symm) |>.trans rfl)
      simp only [hF, hτ0]
      rw [Tm_ne E _ _ _ hne]
      exact h2 _ hne _
  · rw [if_neg (fun h => hl h.2), mul_zero]
    have hσk0 : σ (σ.symm (Fin.last (m+1))) = Fin.last (m+1) := σ.apply_symm_apply _
    have hk0 : σ.symm (Fin.last (m+1)) ≠ Fin.last (m+1) := fun h => hl (by rw [h] at hσk0; exact hσk0)
    have hk0v : ((σ.symm (Fin.last (m+1)) : Fin (m+2)) : ℕ) < m + 1 := by
      exact Fin.val_lt_last hk0
    have hτk0 : τ (σ.symm (Fin.last (m+1))) ≠ p := fun h => hk0 (τ.injective (h.trans hτl.symm))
    have hlen : ((σ.symm (Fin.last (m+1)) : Fin (m+2)) : ℕ) < (List.ofFn F).length := by rw [List.length_ofFn]; omega
    rw [← List.take_append_drop ((σ.symm (Fin.last (m+1)) : Fin (m+2)) : ℕ) (List.ofFn F),
      List.drop_eq_getElem_cons hlen, List.getElem_ofFn]
    simp only [List.prod_append, List.prod_cons, Module.End.mul_apply]
    have hFk0 : F (σ.symm (Fin.last (m+1))) = E p (τ (σ.symm (Fin.last (m+1)))) := by
      simp only [hF, hσk0, hτl]
      exact Tm_ne E _ _ _ hτk0.symm
    simp only [Fin.eta]
    rw [hFk0]
    refine kill_left E hE p ℓ h1 _ ?_ _ hτk0 _
    intro X hX
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hX
    have hj1 : j < ((σ.symm (Fin.last (m+1)) : Fin (m+2)) : ℕ) := lt_of_lt_of_le hj (min_le_left _ _)
    have hj2 : j < m + 2 := by omega
    refine ⟨u - (j : ℂ), τ (σ ⟨j, hj2⟩), τ ⟨j, hj2⟩, ?_, ?_⟩
    · intro h
      have := τ.injective (h.trans hτl.symm)
      simp [Fin.ext_iff] at this
      omega
    · rw [List.getElem_ofFn]

end GlobalTheory.CapelliRoots

namespace GlobalTheory.CapelliRoots
open Formalism.REAL

theorem two_roots_of_parabolic_functional : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (χ : Fin n → ℂ), GlRel E → (∀ (Y : ℂ) (v : V), qdet E (Y + ((n : ℂ) - 1) / 2) v = (∏ s, (Y + χ s)) • v) → ∀ (p q : Fin n), p ≠ q → ∀ (ℓ : V →ₗ[ℂ] ℂ) (α β : ℂ), ℓ ≠ 0 → (∀ b, b ≠ p → ∀ v, ℓ (E p b v) = 0) → (∀ a, a ≠ q → ∀ v, ℓ (E a q v) = 0) → (∀ v, ℓ (E p p v) = α * ℓ v) → (∀ v, ℓ (E q q v) = β * ℓ v) → ∃ i j, i ≠ j ∧ χ i = α - ((n : ℂ) - 1) / 2 ∧ χ j = β + ((n : ℂ) - 1) / 2 := by
  intro V _ _ n E χ hE hq p q hpq ℓ α β hℓ h1 h2 h3 h4
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    refine ⟨n - 2, ?_⟩
    have := Fin.val_ne_of_ne hpq
    have := p.2
    have := q.2
    omega
  obtain ⟨τ, hτ0, hτl⟩ := perm_ends p q hpq
  have hdet : ∀ u, qdet E u = qminor E τ τ u := by
    intro u
    have r := Formalism.REAL.qSkewRow (Module.End ℂ V) (m+2) (m+2) E id id τ u
    have c := Formalism.REAL.qSkewCol (Module.End ℂ V) (m+2) (m+2) E hE τ id τ u
    simp only [Function.id_comp] at r c
    rw [c, r, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp [qdet]
  have hpolyσ : ∀ σ : Equiv.Perm (Fin (m+2)), ∃ P : Polynomial ℂ, ∀ u,
      ℓ ((List.ofFn fun i : Fin m => Formalism.REAL.Tm E (u - (((i.castSucc.succ : Fin (m+2)) : ℕ) : ℂ))
          (τ (σ i.castSucc.succ)) (τ i.castSucc.succ)).prod v) = P.eval u := by
    intro σ
    have hmem : ∀ f ∈ (List.ofFn fun i : Fin m => fun u : ℂ =>
        Formalism.REAL.Tm E (u - (((i.castSucc.succ : Fin (m+2)) : ℕ) : ℂ))
          (τ (σ i.castSucc.succ)) (τ i.castSucc.succ)),
        ∃ (c : ℂ) (D : Module.End ℂ V), ∀ u, f u = algebraMap ℂ _ (c * u) + D := by
      intro f hf
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
      exact Tm_affine E _ _ _
    obtain ⟨P, hP⟩ := poly_of_list _ hmem ℓ v
    refine ⟨P, fun u => ?_⟩
    rw [← hP u, List.map_ofFn]
    rfl
  choose P hP using hpolyσ
  let G : Polynomial ℂ := ∑ σ : Equiv.Perm (Fin (m+2)),
    if σ 0 = 0 ∧ σ (Fin.last (m+1)) = Fin.last (m+1) then
      Polynomial.C (((Equiv.Perm.sign σ : ℤ) : ℂ)) * P σ else 0
  have key : ∀ u : ℂ, (∏ s, (u - ((((m + 2 : ℕ) : ℂ) - 1) / 2 - χ s))) * ℓ v =
      (u - (-β)) * (u - ((m : ℂ) + 1 - α)) * G.eval u := by
    intro u
    have e1 := congrArg ℓ (hq (u - (((m + 2 : ℕ) : ℂ) - 1) / 2) v)
    rw [sub_add_cancel, hdet, map_smul, smul_eq_mul] at e1
    have hprod : (∏ s, (u - ((((m + 2 : ℕ) : ℂ) - 1) / 2 - χ s))) =
        ∏ s, (u - (((m + 2 : ℕ) : ℂ) - 1) / 2 + χ s) :=
      Finset.prod_congr rfl (fun s _ => by ring)
    rw [hprod, ← e1]
    unfold Formalism.REAL.qminor
    simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply,
      Module.End.intCast_apply, map_zsmul]
    simp only [term_eq E hE p q ℓ α β h1 h2 h3 h4 τ _ hτ0 hτl u v]
    simp only [G, Polynomial.eval_finset_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    split_ifs
    · rw [Polynomial.eval_mul, Polynomial.eval_C, ← hP σ u, zsmul_eq_mul]
      ring
    · simp
  obtain ⟨i, j, hij, hi, hj⟩ := two_roots (fun s => (((m + 2 : ℕ) : ℂ) - 1) / 2 - χ s) (-β)
    ((m : ℂ) + 1 - α) G (ℓ v) hv key
  refine ⟨i, j, hij, ?_, ?_⟩
  · push_cast at hi ⊢
    linear_combination -hi
  · push_cast at hj ⊢
    linear_combination -hj

end GlobalTheory.CapelliRoots
