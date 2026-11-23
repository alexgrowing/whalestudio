import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ArInt GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.Mean4O.CalcModel

section Algebra

theorem expand {J : Type} [Fintype J] [DecidableEq J] {m : ℕ} (G : MultilinearMap ℝ (fun _ : Fin m => J → ℝ) ℝ)
    (a : Fin m → J → ℝ) : G a = ∑ r : Fin m → J, (∏ l, a l (r l)) * G fun l => Pi.single (r l) 1 := by
  have e : a = fun l => ∑ j, a l j • (Pi.single j 1 : J → ℝ) := by
    funext _ i
    simp [Pi.single_apply]
  conv_lhs => rw [e, G.map_sum]
  simp only [G.map_smul_univ, smul_eq_mul]

theorem continuous_form {J : Type} [Fintype J] {m : ℕ} (G : MultilinearMap ℝ (fun _ : Fin m => J → ℝ) ℝ) :
    Continuous G := by
  classical
  rw [show (G : _ → ℝ) = _ from funext (expand G)]
  fun_prop

theorem diag_zero_of_int {J : Type} [Fintype J] {m : ℕ} (G : MultilinearMap ℝ (fun _ : Fin m => J → ℝ) ℝ)
    (h : ∀ n : J → ℤ, G (fun _ j => (n j : ℝ)) = 0) (a : J → ℝ) : G (fun _ => a) = 0 := by
  classical
  let P : MvPolynomial J ℝ := ∑ r : Fin m → J,
    (∏ k, MvPolynomial.X (r k)) * MvPolynomial.C (G fun k => Pi.single (r k) 1)
  have hP : ∀ a : J → ℝ, MvPolynomial.eval a P = G (fun _ => a) := by
    intro a
    rw [expand]
    simp only [P, map_sum, map_mul, map_prod, MvPolynomial.eval_X, MvPolynomial.eval_C]
  have h0 : P = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective) fun x hx => ?_
    choose n hn using fun j => hx j (Set.mem_univ j)
    obtain rfl : x = fun j => (n j : ℝ) := funext fun j => (hn j).symm
    rw [hP, h, map_zero]
  rw [← hP, h0, map_zero]

theorem diag_add_smul {J : Type} [Fintype J] {e : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (e + 1) => J → ℝ) ℝ)
    (hs : ∀ (v : Fin (e + 1) → J → ℝ) (ρ : Equiv.Perm (Fin (e + 1))), F (v ∘ ρ) = F v) (d : J → ℝ)
    (h : ∀ a, F (Fin.cons d fun _ => a) = 0) (a : J → ℝ) (t : ℝ) : F (fun _ => a + t • d) = F (fun _ => a) := by
  let Fc : ContinuousMultilinearMap ℝ (fun _ : Fin (e + 1) => J → ℝ) ℝ := ⟨F, continuous_form F⟩
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F (fun _ => a + t • d)) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => fun _ : Fin (e + 1) => a + t • d) (fun _ => d) t :=
      hasDerivAt_pi.2 fun _ => by simpa using ((hasDerivAt_id t).smul_const d).const_add a
    have h2 := (Fc.hasFDerivAt (fun _ => a + t • d)).comp_hasDerivAt t h1
    rw [ContinuousMultilinearMap.linearDeriv_apply] at h2
    refine h2.congr_deriv (Finset.sum_eq_zero fun i _ => ?_)
    refine Eq.trans (congrArg F ?_) ((hs _ (Equiv.swap 0 i)).trans (h (a + t • d)))
    funext l
    by_cases hl : l = i
    · subst hl
      simp
    · rw [Function.update_of_ne hl, Function.comp_apply]
      have : Equiv.swap 0 i l ≠ 0 := fun h0 => hl (by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h0
        exact h0)
      obtain ⟨l', hl'⟩ := Fin.exists_succ_eq.2 this
      rw [← hl', Fin.cons_succ]
  simpa using is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0

theorem diag_zero {ι : Type} [Fintype ι] [DecidableEq ι] {e : ℕ}
    (F : MultilinearMap ℝ (fun _ : Fin (e + 1) => Option ι → ℝ) ℝ)
    (hs : ∀ (v : Fin (e + 1) → Option ι → ℝ) (ρ : Equiv.Perm (Fin (e + 1))), F (v ∘ ρ) = F v)
    (h0 : ∀ n : Option ι → ℤ, n none = 0 → F (fun _ j => (n j : ℝ)) = 0)
    (h1 : ∀ n : Option ι → ℤ, F (Fin.cons (Pi.single none 1) fun _ j => (n j : ℝ)) = 0) (a : Option ι → ℝ) :
    F (fun _ => a) = 0 := by
  refine diag_zero_of_int F (fun n => ?_) a
  have h2 := diag_zero_of_int (F.curryLeft (Pi.single none 1)) h1
  have h3 := diag_add_smul F hs _ h2 (fun j => ((Function.update n none 0 j : ℤ) : ℝ)) (n none)
  rw [h0 _ (by simp)] at h3
  refine Eq.trans (congrArg F ?_) h3
  funext _ j
  cases j <;> simp

def linL (J : Type) [Fintype J] : (J → ℝ) →ₗ[ℝ] MvPolynomial J ℝ where
  toFun := lin
  map_add' a b := by simp [lin, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [lin, Finset.smul_sum, MvPolynomial.smul_eq_C_mul, mul_assoc]

def prodForm {J V : Type} [Fintype J] [AddCommGroup V] [Module ℝ V] (m : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ)
    (f : V →ₗ[ℝ] J → ℝ) : MultilinearMap ℝ (fun _ : Fin m => V) ℝ :=
  Φ.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℝ (Fin m) (MvPolynomial J ℝ)).compLinearMap
    fun _ => (linL J).comp f)

theorem prodForm_apply {J V : Type} [Fintype J] [AddCommGroup V] [Module ℝ V] (m : ℕ)
    (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] J → ℝ) (v : Fin m → V) :
    prodForm m Φ f v = Φ (∏ l, lin (f (v l))) := rfl

theorem prodForm_symm {J V : Type} [Fintype J] [AddCommGroup V] [Module ℝ V] (m : ℕ)
    (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] J → ℝ) (v : Fin m → V) (ρ : Equiv.Perm (Fin m)) :
    prodForm m Φ f (v ∘ ρ) = prodForm m Φ f v := by
  rw [prodForm_apply, prodForm_apply]
  exact congrArg Φ (Equiv.prod_comp ρ fun l => lin (f (v l)))

end Algebra

section Levi

variable {e : ℕ} {M : Man e}

def leviL (K : Calc M) (σ : Fin (M.n + 1)) (j : Fin (M.A σ).n) (y : Fin e → ℂ) (hy : y ∈ ((M.A σ).chart j).target)
    (w : Fin e → ℂ) : K.V →ₗ[ℝ] ℝ where
  toFun v := leviAt (M.A σ) (K.c1 v σ) j y w
  map_add' v v' := by
    rw [K.isOneCochain_add v v' σ j y hy w]
    have h := levi_add_smul 1 (LeviOnly.pot_two (K.firstChern_isPotential v σ) _ j hy ((K.c1 v σ).mem_U _))
      (LeviOnly.pot_two (K.firstChern_isPotential v' σ) _ j hy ((K.c1 v' σ).mem_U _)) w
    simp only [one_mul] at h
    exact h
  map_smul' c v := by
    rw [K.firstChern_smul_leviEq c v σ j y hy w]
    have h := levi_add_smul (f := fun _ => (0 : ℝ)) c contDiffAt_const
      (LeviOnly.pot_two (K.firstChern_isPotential v σ) _ j hy ((K.c1 v σ).mem_U _)) w
    have h2 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
    simp only [zero_add, h2] at h
    exact h

end Levi

section Main

open InhabCalc

variable {e : ℕ} {M : Man e} {ι : Type} [Fintype ι] (P : ι → M.Pot) (hP : ∀ i σ, IsPotential (M.A σ) (P i σ))

theorem calcOf_num_zero (v : Fin (e + 1) → (ι → ℝ) × smSub M) (hv : ∀ l, (v l).2 = 0) :
    (calcOf M P hP).num v = 0 := by
  refine (symForm_apply _ _ _ v).trans (Finset.sum_eq_zero fun s _ => ?_)
  have : (((s.piecewise (fun i => ((LinearMap.inr ℝ (ι → ℝ) (smSub M)).comp (LinearMap.snd ℝ _ _)) (v i))
      fun i => ((LinearMap.inl ℝ (ι → ℝ) (smSub M)).comp (LinearMap.fst ℝ _ _)) (v i)) ∘ pick s) 0).2 = 0 := by
    by_cases h : pick s 0 ∈ s <;> simp [Finset.piecewise, h, hv]
  show intL M P hP _ _ = 0
  rw [LinearMap.snd_apply, this, map_zero, MultilinearMap.zero_apply]

def calcWith (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Calc M where
  V := (ι → ℝ) × smSub M
  num := (calcOf M P hP).num + prodForm (e + 1) Φ (LinearMap.fst ℝ _ _)
  symm v ρ := congrArg₂ (· + ·) ((calcOf M P hP).symm v ρ) (prodForm_symm _ _ _ v ρ)
  c1 := (calcOf M P hP).c1
  firstChern_isPotential := (calcOf M P hP).firstChern_isPotential
  isOneCochain_add := (calcOf M P hP).isOneCochain_add
  firstChern_smul_leviEq := (calcOf M P hP).firstChern_smul_leviEq
  ar := (calcOf M P hP).ar
  c1_ar := (calcOf M P hP).c1_ar
  num_ar u hu v := by
    refine (congrArg₂ (· + ·) ((calcOf M P hP).num_ar u hu v) ?_).trans (add_zero _)
    refine (prodForm_apply _ _ _ _).trans ?_
    rw [Fin.prod_univ_succ]
    have : lin (0 : ι → ℝ) = 0 := (linL ι).map_zero
    exact (congrArg (fun x => Φ (x * _)) this).trans (by rw [zero_mul, map_zero])

theorem calcWith_top (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (a : ι → ℝ) :
    (calcWith P hP Φ).top (∑ i, a i • (show (calcWith P hP Φ).V from cls M P hP i)) = Φ (lin a ^ (e + 1)) := by
  classical
  have h : (∑ i, a i • (show (calcWith P hP Φ).V from cls M P hP i)) = ((a, 0) : (ι → ℝ) × smSub M) := by
    change (∑ i, a i • (((Pi.single i 1 : ι → ℝ), 0) : (ι → ℝ) × smSub M)) = _
    refine Prod.ext ?_ ?_
    · funext j
      simp [Prod.fst_sum, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [h]
  refine (congrArg₂ (· + ·) (calcOf_num_zero P hP _ fun _ => rfl) (prodForm_apply _ _ _ _)).trans ?_
  rw [zero_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem numOn_of (H : Published.ArChange) (hX : IsArithVar p e) {ε : (k →+* ℂ) → Fin (M.n + 1)}
    {π : ∀ σ, CxPts p σ → M.X (ε σ)} {ν : ℝ} {L : ι → HermLB p} (K : Calc M) (v : ι → K.V)
    (hC : K.ChernOn ε π ν L v)
    (h0 : ∀ n : ι → ℤ, (comb L n).IsSelfInter (ν * K.top (∑ i, (n i : ℝ) • v i))) : K.NumOn ε π ν L v := by
  classical
  intro u hu hu' hc Φ hΦ a
  let θ : (Option ι → ℝ) →ₗ[ℝ] K.V :=
    ∑ i, (LinearMap.proj (some i)).smulRight (v i) + (LinearMap.proj none).smulRight (K.ar u)
  have hθ : ∀ a, θ a = ∑ i, a (some i) • v i + a none • K.ar u := fun a => by
    simp [θ, LinearMap.sum_apply]
  have key := diag_zero (prodForm (e + 1) Φ LinearMap.id - ν • K.num.compLinearMap fun _ => θ)
    (fun w ρ => ?_) (fun n hn => ?_) (fun n => ?_) a
  · rw [MultilinearMap.sub_apply, sub_eq_zero, prodForm_apply] at key
    simpa [hθ, Calc.top] using key
  · simp only [MultilinearMap.sub_apply, prodForm_symm, MultilinearMap.smul_apply,
      MultilinearMap.compLinearMap_apply]
    exact congrArg (fun x => _ - ν • x) (K.symm (fun l => θ (w l)) ρ)
  · have hi : (comb (fun o : Option ι => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu' hc) L) n).Isometric
        (comb L fun i => n (some i)) := HermLB.icls_eq_iff.1 (by simp [icls_comb, hn])
    have := HermLB.IsSelfInter.unique hX (hi.isSelfInter hX (hΦ.1 n)) (h0 _)
    rw [MultilinearMap.sub_apply, sub_eq_zero, prodForm_apply]
    simpa [hθ, hn, Calc.top] using this
  · let L' : Option ι → HermLB p := fun o => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu' hc) L
    let A : Option (Option ι) → Option ι → ℤ := fun j => Pi.single (j.getD none) 1
    have hΦ' := ((Published.arIso_holds k X p e hX).2 _ L' Φ hΦ).2.2 (Option (Option ι))
      (fun o => o.elim (fnB (M.pull ε π ((2 : ℝ) • u)) hu' hc) L') A
      (fun j => by cases j <;> exact isometric_comb_single L' _)
    have h1 := H k X p e hX _ L' _ hu' hc _ hΦ' n
    have h2u : M.Smooth ((2 : ℝ) • u) := (smSub M).smul_mem 2 hu
    rw [hC u hu hu' hc n _ h2u, ← K.num_ar _ h2u (fun _ => _), map_smul, K.num.cons_smul] at h1
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, map_pow, MvPolynomial.aeval_X,
      MvPolynomial.aeval_rename, A, lin_single, Function.comp_def, Option.getD_some, Option.getD_none,
      MvPolynomial.aeval_X_left_apply] at h1
    rw [MultilinearMap.sub_apply, sub_eq_zero, prodForm_apply, Fin.prod_univ_succ]
    have h3 : lin (Pi.single none 1 : Option ι → ℝ) = MvPolynomial.X none := by
      simp [lin, Pi.single_apply, apply_ite MvPolynomial.C]
    have h4 : (fun l => θ ((Fin.cons (Pi.single none 1) fun _ j => (n j : ℝ) : Fin (e + 1) → Option ι → ℝ) l)) =
        Fin.cons (K.ar u) fun _ => ∑ i, (n (some i) : ℝ) • v i + (n none : ℝ) • K.ar u := by
      funext l
      refine Fin.cases ?_ (fun l => ?_) l <;> simp [hθ]
    simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, h3, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, MultilinearMap.smul_apply, MultilinearMap.compLinearMap_apply, h4, h1, smul_eq_mul]
    ring

end Main

end GlobalTheory.Mean4O.CalcModel
