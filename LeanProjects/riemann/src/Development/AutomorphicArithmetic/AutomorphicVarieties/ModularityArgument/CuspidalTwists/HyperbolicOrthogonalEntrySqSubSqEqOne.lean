import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu.RankFourHodgeWeights

section Alg

variable {R : Type} [CommRing R]

theorem flg_eq (x σ : R) : flg x σ = !![1, 0, 0, 0; σ, 1, 0, 0; -(x * σ), -x, 1, 0; x, 0, -σ, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

theorem adj_flg (x σ : R) : adj (flg x σ) = !![1, 0, 0, 0; -σ, 1, 0, 0; 0, x, 1, 0; -x, x * σ, σ, 1] := by
  rw [flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

theorem diag (c x σ y : R) (g t : M2 R)
    (h1 : g 0 0 + g 0 1 * x = y) (h2 : g 1 1 - x * g 0 1 = 1)
    (ht1 : t 1 1 = t 0 0) (ht2 : t 1 0 = t 0 1) (i : Fin 4) :
    (adj (flg x σ) * (c • tn g t) * flg x σ) i i =
      c * ![y * (t 0 0 + t 0 1 * σ), y * (t 0 0 - t 0 1 * σ), t 0 0 + t 0 1 * σ, t 0 0 - t 0 1 * σ] i := by
  rw [adj_flg, flg_eq]
  fin_cases i
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 + t 0 1 * σ)) * h1
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 - t 0 1 * σ)) * h1
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 + t 0 1 * σ)) * h2
  · simp [tn, Matrix.mul_apply, Fin.sum_univ_succ, ht1, ht2]
    linear_combination (c * (t 0 0 - t 0 1 * σ)) * h2

theorem hyperbolicOrthogonal_entry_sq_sub_sq_eq_one (t : M2 R) (h : tᵀ * !![1, 0; 0, -1] * t = !![1, 0; 0, -1]) (ht2 : t 1 0 = t 0 1) :
    t 0 0 * t 0 0 - t 0 1 * t 0 1 = 1 := by
  have := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at this
  rw [ht2] at this
  linear_combination this

theorem fin_cg {α : Type} [CommGroup α] (E D : α) (j : ℤ) (n m : ℕ) (hD : D ^ 2 = E ^ j) (i : Fin 4) :
    (D * ![E ^ n * E ^ m, E ^ n * (E ^ m)⁻¹, E ^ m, (E ^ m)⁻¹] i) ^ 2 =
      E ^ (j + 2 * ![(n : ℤ) + m, (n : ℤ) - m, (m : ℤ), -(m : ℤ)] i) := by
  rw [mul_pow, hD, zpow_add]
  congr 1
  fin_cases i <;> simp <;> group

end Alg

private theorem psi_map {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4) (s : Γ) :
    (P.map f).ψ v i s = f (P.ψ v i s) := by
  have a : adj ((P.n v).map f) = (adj (P.n v)).map f := by
    ext i j
    simp [adj_apply]
  have b : (P.map f).r s = (P.r s).map f := rfl
  have c : (P.map f).n v = (P.n v).map f := rfl
  rw [PD.ψ, b, c, a, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

private theorem cont_emb (E : Type) [Field E] [NumberField E] [Algebra E Ω] : Continuous (galEmb ℚ E Ω) := by
  haveI : FaithfulSMul E Ω := (faithfulSMul_iff_algebraMap_injective E Ω).2 (algebraMap E Ω).injective
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  exact (galEmbTop ℚ E Ω).1.continuous

private theorem cont_res (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := cont_emb F

private theorem toB_chi (c : Coef l) (g : G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl

theorem psi_eq (d : Dat Ω l) (T : Tower d.D) (v : T.ι) (s : G T.F Ω) (hs : resQ T.F s ∈ Ine (F := ℚ) (T.pl v)) (i : Fin 4) :
    (d.Q T).ψ v i s = ((toC d.h d.δ (resQ T.F s) * ![chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m,
      chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹,
      chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m, (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹] i : d.c₁.Oˣ) : d.c₁.O) := by
  have hA := T.ovl v
  have hD := Ine_le_Dec _ hs
  have hK := d.quad.split _ hA hD
  obtain ⟨h1, h2⟩ := d.mod.ine _ hA _ hs
  obtain ⟨ht1, ht2⟩ := d.tau.on _ hK
  have hp := d.tau.ine _ hA _ hs
  have hσ : d.s (T.pl v) * d.s (T.pl v) = 1 := by
    rcases d.tau.sgn (T.pl v) with h | h <;> rw [h] <;> ring
  have hf : d.τ (resQ T.F s) 0 0 * d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.τ (resQ T.F s) 0 1 = 1 :=
    hyperbolicOrthogonal_entry_sq_sub_sq_eq_one _ (d.tau.form (resQ T.F s)) ht2
  have hm : d.τ (resQ T.F s) 0 0 - d.τ (resQ T.F s) 0 1 * d.s (T.pl v) =
      (((chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹ : d.c₁.Oˣ) : d.c₁.O) := by
    refine Units.eq_inv_of_mul_eq_one_right ?_
    rw [← hp]
    linear_combination hf - d.τ (resQ T.F s) 0 1 * d.τ (resQ T.F s) 0 1 * hσ
  have e : (d.Q T).ψ v i s = (adj (flg (d.x (T.pl v)) (d.s (T.pl v))) *
      (((toC d.h d.δ (resQ T.F s) : d.c₁.Oˣ) : d.c₁.O) • tn (d.ρ₁ (resQ T.F s)) (d.τ (resQ T.F s))) *
      flg (d.x (T.pl v)) (d.s (T.pl v))) i i := rfl
  rw [e, diag _ _ _ _ _ _ h1 h2 ht1 ht2 i, hp, hm, Units.val_mul]
  congr 1
  fin_cases i <;> simp [Units.val_mul]

end UpperTheory.V.Cu.RankFourHodgeWeights

open UpperTheory.V.Cu

theorem UpperTheory.V.Cu.wtsOf4 : WtsOf4 := by
  intro Ω _ _ _ l _ d T U j hU hj
  refine ⟨U.comap (resQ T.F), hU.preimage (RankFourHodgeWeights.cont_res T.F), fun v i s hs => ?_⟩
  have hI : resQ T.F s ∈ Ine (F := ℚ) (T.pl v) := ⟨hs.2.1, hs.2.2⟩
  have e3 : toB d.δ (resQ T.F s) ^ 2 = cycBar T.F Ω l s ^ j := by
    have := congrArg (Units.map (algebraMap d.c.O (PadicAlgCl l)).toMonoidHom) (hj _ hs.1)
    rw [map_pow, map_zpow] at this
    exact this.trans (congrArg (· ^ j) (RankFourHodgeWeights.toB_chi d.c (resQ T.F s)))
  have hk : (d.k : ℤ) - 1 = ((d.k - 1 : ℕ) : ℤ) := by
    have := d.big
    omega
  dsimp only
  rw [RankFourHodgeWeights.psi_map, RankFourHodgeWeights.psi_eq d T v s hI i, hk]
  have key := RankFourHodgeWeights.fin_cg (cycBar T.F Ω l s) (toB d.δ (resQ T.F s)) j (d.k - 1) d.m e3 i
  have hδ : (Units.map (algebraMap d.c₁.O (PadicAlgCl l)).toMonoidHom) (toC d.h d.δ (resQ T.F s)) = toB d.δ (resQ T.F s) :=
    Units.ext rfl
  have hE : (Units.map (algebraMap d.c₁.O (PadicAlgCl l)).toMonoidHom) (chiO ℚ Ω l d.c₁.O (resQ T.F s)) = cycBar T.F Ω l s :=
    Units.ext rfl
  have hU : (Units.map (algebraMap d.c₁.O (PadicAlgCl l)).toMonoidHom)
      (toC d.h d.δ (resQ T.F s) * ![chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m,
        chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ (d.k - 1) * (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹,
        chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m, (chiO ℚ Ω l d.c₁.O (resQ T.F s) ^ d.m)⁻¹] i) =
      toB d.δ (resQ T.F s) * ![cycBar T.F Ω l s ^ (d.k - 1) * cycBar T.F Ω l s ^ d.m,
        cycBar T.F Ω l s ^ (d.k - 1) * (cycBar T.F Ω l s ^ d.m)⁻¹, cycBar T.F Ω l s ^ d.m, (cycBar T.F Ω l s ^ d.m)⁻¹] i := by
    rw [← hδ, ← hE]
    fin_cases i <;> simp [map_mul, map_pow, map_inv]
  rw [← key, ← hU, Units.val_pow_eq_pow_val, Units.coe_map]
  rfl
