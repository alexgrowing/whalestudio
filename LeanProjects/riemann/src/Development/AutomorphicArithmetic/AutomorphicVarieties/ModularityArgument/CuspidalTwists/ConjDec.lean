import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open scoped Matrix

namespace UpperTheory.V.Cu

section Alg

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem tn_map (f : R →+* R') (g t : M2 R) : (tn g t).map f = tn (g.map f) (t.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

private theorem flg_map (f : R →+* R') (x s : R) : (flg x s).map f = flg (f x) (f s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem adj_flg (x s : R) : adj (flg x s) = nA (-s) * tn (low (-x)) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev] <;> ring

private theorem conj_flg (a x y s s' : R) (g t : M2 R) :
    adj (flg y s') * (a • tn g t) * flg x s = a • (nA (-s') * tn (low (-y) * g * low x) t * nA s) := by
  have e : tn (low (-y) * g * low x) t = tn (low (-y)) 1 * tn g t * tn (low x) 1 := by
    rw [← tn_mul, ← tn_mul, one_mul, mul_one]
  rw [adj_flg, e, flg]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

private theorem isUp_mid (a : R) {m t : M2 R} {s s' : R} (hm01 : m 0 1 = 0) (hm10 : m 1 0 = 0) (ht01 : t 0 1 = 0)
    (ht10 : t 1 0 = 0) (hs1 : t 1 1 * s = t 0 0 * s') (hs2 : t 1 1 * s' = t 0 0 * s) :
    IsUp (a • (nA (-s') * tn m t * nA s)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [nA, tn, Matrix.mul_apply, Fin.sum_univ_succ, hm01, hm10, ht01, ht10] at hij ⊢ <;>
    first
    | linear_combination (a * m 0 0) * hs1
    | linear_combination (-(a * m 0 0)) * hs1
    | linear_combination (a * m 1 1) * hs2

end Alg

private theorem conj_dec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {A A' : ValuationSubring Ω} {g s : G ℚ Ω}
    (hA : ∀ x, g x ∈ A' ↔ x ∈ A) (hs : s ∈ Dec (F := ℚ) A') : g⁻¹ * s * g ∈ Dec (F := ℚ) A :=
  UpperTheory.V.conjGal_mem_Dec (τ := RingEquiv.refl ℚ) (σ := g.toRingEquiv) (fun x => g.commutes x) hA hs

private theorem key {R : Type} [Field R] {g s t : M2 R} {x y : R} (h : g * t = s * g) (hg0 : g 0 0 ≠ 0)
    (hg : g 1 1 = 1 ∧ g 0 1 = 0) (hs : s 1 1 = 1 ∧ s 0 1 = 0) (ht : t 1 1 = 1 ∧ t 0 1 = 0) (hne : s 0 0 ≠ 1)
    (hx : t 1 0 + t 1 1 * x = (t 0 0 + t 0 1 * x) * x) (hy : s 1 0 + s 1 1 * y = (s 0 0 + s 0 1 * y) * y) :
    g 1 0 + g 1 1 * x - (g 0 0 + g 0 1 * x) * y = 0 := by
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hg.1, hg.2, hs.1, hs.2, ht.1, ht.2] at h0 h1 hx hy ⊢
  have e : t 0 0 = s 0 0 := mul_left_cancel₀ hg0 (by linear_combination h0)
  rw [e] at h1 hx
  refine mul_left_cancel₀ (sub_ne_zero.2 hne) ?_
  linear_combination h1 - hx + g 0 0 * hy

private theorem phi_ne {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (h : D.Good) (pr : Bool) (k : ℕ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Dec (F := ℚ) A, Raw.bar (Phi D pr k) s ≠ 1 := by
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  obtain ⟨u, hu, -⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l _ A hl.out (h.pl_over l hl.out) hA
  have hc : chiO ℚ Ω l c.O (D.sg l) = 1 := by simp [chiO, h.sg_cyc]
  have e : Phi D pr k (u⁻¹ * D.sg l * u) = (D.ξ * D.Psi ^ (if pr then (-1 : ℤ) else 1)) (D.sg l) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
    cases pr <;> simp [Phi, phi, Raw.Psi, Chr.Psi, hc]
  exact ⟨_, hu _ (h.sg_frob l hT).1, fun h' => h.condD l hT _
    ((congrArg (fun z : c.Oˣ => residue c.O (z : c.O)) e).symm.trans h')⟩

theorem overOf4 : OverOf4 := by
  intro Ω _ _ _ l _ d T hT R _ f hf
  refine ⟨rfl, fun v' => ?_⟩
  obtain ⟨v, g, hg⟩ := (d.T₀.cover (T.pl v') (T.ovl v')).exists
  refine ⟨v, g, hg, ?_⟩
  obtain ⟨s, hs, hne⟩ := phi_ne d.D d.ctx.1 d.T₀.pr d.k (T.pl v') (T.ovl v')
  have ht : (resQ d.T₀.F g)⁻¹ * s * resQ d.T₀.F g ∈ Dec (F := ℚ) (d.T₀.pl v) := conj_dec hg hs
  have h1 : ∀ t, ((d.ρ₁ t).map f) 1 1 = 1 ∧ ((d.ρ₁ t).map f) 0 1 = 0 := fun t =>
    ⟨by simpa [sub_eq_zero] using hf _ (d.mod.red t).2.1, hf _ (d.mod.red t).2.2⟩
  have h0 : ∀ t, ((d.ρ₁ t).map f) 0 0 = f (inc d.h (Phi d.D d.T₀.pr d.k t)) := fun t => by
    simpa [sub_eq_zero] using hf _ (d.mod.red t).1
  have hk := key (g := (d.ρ₁ (resQ d.T₀.F g)).map f) (s := (d.ρ₁ s).map f)
    (t := (d.ρ₁ ((resQ d.T₀.F g)⁻¹ * s * resQ d.T₀.F g)).map f) (x := f (d.x (d.T₀.pl v))) (y := f (d.x (T.pl v')))
    (by rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul]; congr 2; group)
    (by rw [h0]; exact (((Phi d.D d.T₀.pr d.k _).isUnit.map (inc d.h)).map f).ne_zero) (h1 _) (h1 _) (h1 _)
    (fun h => by
      rw [h0] at h
      have hn : ¬ IsUnit ((Phi d.D d.T₀.pr d.k s : d.c.O) - 1) := fun hu => by
        have := ((hu.map (inc d.h)).map f).ne_zero
        rw [map_sub, map_sub, map_one, map_one, h, sub_self] at this
        exact this rfl
      refine hne ?_
      show residue d.c.O (Phi d.D d.T₀.pr d.k s : d.c.O) = 1
      rw [← map_one (residue d.c.O)]
      exact Ideal.Quotient.eq.2 hn)
    (by simpa using congrArg f (d.mod.flag _ (d.T₀.ovl v) _ ht))
    (by simpa using congrArg f (d.mod.flag _ (T.ovl v') _ hs))
  have z01 : f (d.τ (resQ d.T₀.F g) 0 1) = 0 := hf _ (d.tau.red _).2
  have hsg := d.tau.mov (d.T₀.pl v) (T.pl v') (resQ d.T₀.F g) (d.T₀.ovl v) hg
  have hτ : ((d.τ (resQ d.T₀.F g)).map f) 1 0 = 0 ∧
      ((d.τ (resQ d.T₀.F g)).map f) 1 1 * f (d.s (d.T₀.pl v)) = ((d.τ (resQ d.T₀.F g)).map f) 0 0 * f (d.s (T.pl v')) ∧
      ((d.τ (resQ d.T₀.F g)).map f) 1 1 * f (d.s (T.pl v')) = ((d.τ (resQ d.T₀.F g)).map f) 0 0 * f (d.s (d.T₀.pl v)) := by
    simp only [Matrix.map_apply]
    by_cases hK : resQ d.T₀.F g ∈ d.K'.fixingSubgroup
    · obtain ⟨e1, e2⟩ := d.tau.on _ hK
      rw [e1, e2, hsg.1 hK, z01]
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨e1, e2⟩ := d.tau.off _ hK
      rw [e1, e2, hsg.2 hK, map_neg, map_neg, map_neg, z01]
      exact ⟨neg_zero, by ring, by ring⟩
  have e : ((d.Q d.T₀).map f).r g =
      f (toC d.h d.δ (resQ d.T₀.F g)) • tn ((d.ρ₁ (resQ d.T₀.F g)).map f) ((d.τ (resQ d.T₀.F g)).map f) := by
    rw [← tn_map]
    ext i j
    exact map_mul f _ _
  have e1 : ((d.Q d.T₀).map f).n v = flg (f (d.x (d.T₀.pl v))) (f (d.s (d.T₀.pl v))) := by
    rw [← flg_map]; rfl
  have e2 : ((d.Q T).map f).n v' = flg (f (d.x (T.pl v'))) (f (d.s (T.pl v'))) := by
    rw [← flg_map]; rfl
  rw [e, e1, e2, conj_flg]
  refine isUp_mid _ ?_ ?_ (by simpa using z01) hτ.1 hτ.2.1 hτ.2.2
  · simp only [low, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (h1 (resQ d.T₀.F g)).2
  · simp only [low, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination hk

end UpperTheory.V.Cu

end
