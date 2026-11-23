import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Mathlib.Algebra.MvPolynomial.Funext

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.L2.Pj MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k K : Type} [Field k] [Field K]

theorem eval_aeval' {ι κ : Type} (g : ι → MvPolynomial κ k) (x : κ → k) (Q : MvPolynomial ι k) :
    eval x (aeval g Q) = eval (fun ℓ => eval x (g ℓ)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ℓ hp => simp only [map_mul, hp, aeval_X, eval_X]

theorem rowInv_map [Infinite k] (io : k →+* K) {P : MvPolynomial (Letter Ty r n) k} (hP : RowInv r n k P) :
    RowInv r n K (P.map io) := by
  classical
  intro σ i i' hi t
  let g : Letter Ty r n → MvPolynomial (Option (Letter Ty r n)) k := fun ℓ =>
    if ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ then X (some ℓ) + X none * X (some ⟨σ, i', ℓ.2.2⟩) else X (some ℓ)
  let ψ : Option (Letter Ty r n) → MvPolynomial (Letter Ty r n) K := fun o => Option.elim o (C t) X
  have hΦ : aeval g P = rename some P := by
    refine MvPolynomial.funext fun x => ?_
    have e := congrArg (eval (x ∘ some)) (hP σ i i' hi (x none))
    rw [eval_rename, ← e, eval_aeval', rowShift, eval_aeval']
    refine congrArg (fun f => eval f P) (funext fun ℓ => ?_)
    by_cases hc : ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ <;> simp [g, hc]
  have h1 : ∀ Q : MvPolynomial (Letter Ty r n) k,
      rowShift r n K σ i i' t (Q.map io) = aeval ψ ((aeval g Q).map io) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simp [ψ]
    | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
    | mul_X p ℓ hp =>
      simp only [map_mul, hp, map_X, aeval_X]
      congr 1
      by_cases hc : ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ <;> simp [rowShift, g, ψ, hc]
  have h2 : aeval ψ ((rename some P).map io) = P.map io := by
    rw [map_rename, aeval_rename]
    have : (ψ ∘ some) = X := rfl
    rw [this, aeval_X_left_apply]
  rw [h1, hΦ, h2]

theorem rowDeg_map (io : k →+* K) {a : Ty → ℕ → ℕ} {P : MvPolynomial (Letter Ty r n) k} (hP : RowDeg r n k a P) :
    RowDeg r n K a (P.map io) := by
  intro m hm
  rw [support_map_of_injective _ io.injective] at hm
  exact hP m hm

theorem harmK_map (io : k →+* K) {cc : Ty → Ty} {isX : Ty → Prop} {P : MvPolynomial (Letter Ty r n) k}
    (hP : P ∈ harmK r n k cc isX (fun _ => 1)) : P.map io ∈ harmK r n K cc isX (fun _ => 1) := by
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hP ⊢
  intro τ hτ a a'
  have e : lap r n K 1 τ (cc τ) a a' (P.map io) = (lap r n k 1 τ (cc τ) a a' P).map io := by
    simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Derivation.coeFn_coe,
      pderiv_map, map_sum, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
    split_ifs <;> simp [pderiv_map]
  rw [e, hP τ hτ a a', map_zero]

end Gen

def FFVMapSt0 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    [StarRing (𝓞 E)] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
    ∀ (T : CDVR) (io : c.F →+* T.Fr), P.map io ∈ FFV (Dw := Dw) T a n

theorem ffvMap : FFVMapSt0 := by
  intro E _ _ _ H Dw l c _ a n P hP T io
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hP
  have : CharZero T.Fr := charZero_of_injective_algebraMap (IsFractionRing.injective T.V T.Fr)
  have : Infinite c.F := Infinite.of_injective (fun m : ℕ => (m : c.F)) fun m m' h => by
    have := congrArg io h
    simpa using this
  refine ⟨⟨harmK_map io h1, rowInv_map io h2, rowDeg_map io h3⟩, fun m => ?_⟩
  rw [coeff_map]
  have hi : IsIntegral ℤ (P.coeff m) := h4 m
  obtain ⟨p, hpm, hp⟩ := hi
  have hV : IsIntegral T.V (io (P.coeff m)) := by
    refine ⟨p.map (Int.castRingHom T.V), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
      (io.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, hp, map_zero]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hV
  exact ⟨y, hy⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
