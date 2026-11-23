import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu.RankFourResidualFlag

section Alg

variable {R : Type} [CommRing R]

def mat (P b e : R) : M4 R := !![P, 0, 0, 0; 0, P * e, 0, 0; 0, -(b * e), e, 0; b, 0, 0, 1]

theorem flg_eq (x s : R) : flg x s = !![1, 0, 0, 0; s, 1, 0, 0; -(x * s), -x, 1, 0; x, 0, -s, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flg, tn, nA, low, Matrix.mul_apply, Fin.sum_univ_succ]

theorem flg_map {R' : Type} [CommRing R'] (f : R →+* R') (x s : R) : (flg x s).map f = flg (f x) (f s) := by
  rw [flg_eq, flg_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem flg_10 (x s : R) : flg x s 1 0 = s := by
  rw [flg_eq]
  simp

theorem conj_diag (x s dl P b e : R) (i : Fin 4) :
    (adj (flg x s) * (dl • mat P b e) * flg x s) i i = (dl • mat P b e) i i := by
  rw [flg_eq]
  fin_cases i <;> simp [adj_apply, mat, Matrix.mul_apply, Fin.sum_univ_succ, sgn, Fin.rev]

theorem mat_supp {S : Finset (ℤ × ℤ)} (h1 : wt 2 1 ∈ S) (h2 : wt 3 0 ∈ S) (dl P b e : R) : SuppM S (dl • mat P b e) := by
  intro i j hij hw
  fin_cases i <;> fin_cases j <;> first | (simp [mat]; done) | exact absurd h1 hw | exact absurd h2 hw | exact absurd rfl hij

theorem tn_map {R' : Type} [CommRing R'] (f : R →+* R') (g t : M2 R) : (tn g t).map f = tn (g.map f) (t.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn]

theorem tn_eq (g t : M2 R) (hg : g 0 1 = 0) (ht1 : t 0 1 = 0) (ht2 : t 1 0 = 0) (ht0 : t 0 0 = 1)
    (hg1 : g 1 1 = 1) : tn g t = mat (g 0 0) (g 1 0) (t 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tn, mat, hg, ht1, ht2, ht0, hg1]

theorem res_mul {O : Type} [CommRing O] [IsLocalRing O] (u v : Oˣ) {t : ResidueField O}
    (h : residue O ((u * v⁻¹ : Oˣ) : O) = t) : residue O (u : O) = t * residue O (v : O) := by
  have e : (u : O) = ((u * v⁻¹ : Oˣ) : O) * (v : O) := by simp
  rw [e, map_mul, h]

end Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem chi_mul {c : Coef l} (D : Raw Ω c) (pr : Bool) (g : G ℚ Ω) :
    chi D pr 0 g * chi D pr 3 g = chi D pr 1 g * chi D pr 2 g := by
  cases pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]

private theorem inc_mem {c c' : Coef l} (h : c.O ≤ c'.O) {x : c.O}
    (hx : x ∈ maximalIdeal c.O) : inc h x ∈ maximalIdeal c'.O := by
  have hint : (inc h).IsIntegral := by
    intro y
    obtain ⟨p, hp, e⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] c.O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact e
  haveI : IsLocalHom (inc h) := hint.isLocalHom (Subalgebra.inclusion_injective h)
  exact map_nonunit (inc h) x hx

theorem eq_of_res {c c' : Coef l} (h : c.O ≤ c'.O) {R : Type} [CommRing R]
    (f : c'.O →+* R) (hf : ∀ y ∈ maximalIdeal c'.O, f y = 0) {x y : c.O} (e : residue c.O x = residue c.O y) :
    f (inc h x) = f (inc h y) := by
  have h1 : x - y ∈ maximalIdeal c.O := by
    rw [← residue_eq_zero_iff, map_sub, e, sub_self]
  have h2 := hf _ (inc_mem h h1)
  rwa [map_sub, map_sub, sub_eq_zero] at h2

end UpperTheory.V.Cu.RankFourResidualFlag

open UpperTheory.V.Cu.RankFourResidualFlag in
theorem UpperTheory.V.Cu.resOf4 : UpperTheory.V.Cu.ResOf4 := by
  intro Ω _ _ _ l _ d T hT W R _ f hf
  have hpr : T.pr = d.T₀.pr := hT.pr

  have h00 : ∀ g, f (d.ρ₁ g 0 0) = f (inc d.h (Phi d.D d.T₀.pr d.k g : d.c.O)) := fun g => by
    have := hf _ (d.mod.red g).1
    rwa [map_sub, sub_eq_zero] at this
  have h11 : ∀ g, f (d.ρ₁ g 1 1) = 1 := fun g => by
    have := hf _ (d.mod.red g).2.1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have h01 : ∀ g, f (d.ρ₁ g 0 1) = 0 := fun g => hf _ (d.mod.red g).2.2
  have t00 : ∀ g, f (d.τ g 0 0) = 1 := fun g => by
    have := hf _ (d.tau.red g).1
    rwa [map_sub, sub_eq_zero, map_one] at this
  have t01 : ∀ g, f (d.τ g 0 1) = 0 := fun g => hf _ (d.tau.red g).2
  have hne : ∀ u : d.c.Oˣ, f (inc d.h (u : d.c.O)) ≠ 0 := fun u => by
    have : IsUnit (f (inc d.h (u : d.c.O))) := (u.isUnit.map (inc d.h)).map f
    exact this.ne_zero

  have sgnK : ∀ g : G T.F Ω, ∃ e : R, (e = 1 ∨ e = -1) ∧ f (d.τ (resQ T.F g) 1 1) = e ∧ f (d.τ (resQ T.F g) 1 0) = 0 ∧
      f (inc d.h (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) * e ∧
      f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O)) = f (inc d.h (chi d.D d.T₀.pr 3 (resQ T.F g) : d.c.O)) * e := by
    intro g
    have hres : resQ d.T₀.F (resLe hT.le g) = resQ T.F g := AlgEquiv.ext fun _ => rfl
    have hrb : ∀ t : ResidueField d.c.O, d.T₀.rb wAl (resLe hT.le g) = t →
        residue d.c.O (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O) =
          t * residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) := fun t ht => by
      apply res_mul
      simp only [Tower.rb, Fr.rt, Tower.fr, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.comp_apply, wAl, zpow_one,
        zpow_zero, mul_one, hres] at ht
      exact ht
    have hprod := congrArg (fun u : d.c.Oˣ => f (inc d.h (u : d.c.O))) (chi_mul d.D d.T₀.pr (resQ T.F g))
    simp only [Units.val_mul, map_mul] at hprod
    have h0 := hne (chi d.D d.T₀.pr 0 (resQ T.F g))
    by_cases hK : resQ T.F g ∈ d.K'.fixingSubgroup
    · have e1 := hrb 1 (d.quad.on _ (by rwa [hres]))
      rw [one_mul] at e1
      have e2 := eq_of_res d.h f hf e1.symm
      obtain ⟨a1, a2⟩ := d.tau.on _ hK
      refine ⟨1, Or.inl rfl, by rw [a1, t00], by rw [a2, t01], by rw [e2, mul_one], ?_⟩
      rw [e2] at hprod
      rw [mul_one]
      exact (mul_left_cancel₀ h0 hprod).symm
    · have e1 := hrb (-1) (d.quad.off _ (by rwa [hres]))
      have e1' : residue d.c.O (chi d.D d.T₀.pr 1 (resQ T.F g) : d.c.O) =
          residue d.c.O (-(chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) := by
        rw [map_neg, e1]
        ring
      have e2 := eq_of_res d.h f hf e1'
      rw [map_neg, map_neg] at e2
      obtain ⟨a1, a2⟩ := d.tau.off _ hK
      refine ⟨-1, Or.inr rfl, by rw [a1, map_neg, t00], by rw [a2, map_neg, t01, neg_zero], by rw [e2]; ring, ?_⟩
      rw [e2] at hprod
      have := mul_left_cancel₀ h0 (hprod.trans (by ring) : _ = f (inc d.h (chi d.D d.T₀.pr 0 (resQ T.F g) : d.c.O)) *
        (-f (inc d.h (chi d.D d.T₀.pr 2 (resQ T.F g) : d.c.O))))
      rw [this]
      ring

  have hr : ∀ g, ((d.Q T).map f).r g = f (inc d.h (d.δ (resQ T.F g) : d.c.O)) •
      tn ((d.ρ₁ (resQ T.F g)).map f) ((d.τ (resQ T.F g)).map f) := fun g => by
    rw [← tn_map]
    ext i j
    exact map_mul f _ _
  have key : ∀ g : G T.F Ω, ∃ e P b dl : R, ((d.Q T).map f).r g = dl • mat P b e ∧
      (f.comp (inc d.h)) ((T.fr W).χ 0 g : d.c.O) = dl * P ∧ (f.comp (inc d.h)) ((T.fr W).χ 1 g : d.c.O) = dl * (P * e) ∧
      (f.comp (inc d.h)) ((T.fr W).χ 2 g : d.c.O) = dl * e ∧ (f.comp (inc d.h)) ((T.fr W).χ 3 g : d.c.O) = dl := by
    intro g
    obtain ⟨e, -, he, he10, e1, e2⟩ := sgnK g
    have hrg := hr g
    have hχ : ∀ i, (f.comp (inc d.h)) ((T.fr W).χ i g : d.c.O) =
        f (inc d.h (chi d.D d.T₀.pr i (resQ T.F g) : d.c.O)) := fun i => by
      rw [← hpr]
      rfl
    generalize resQ T.F g = g' at he he10 e1 e2 hrg hχ
    have r0 : f (inc d.h (chi d.D d.T₀.pr 0 g' : d.c.O)) =
        f (inc d.h (d.δ g' : d.c.O)) * f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)) := by
      rw [← map_mul, ← map_mul]
      apply eq_of_res d.h f hf
      rw [map_mul]
      exact d.tw.red0 g'
    have r3 := eq_of_res d.h f hf (d.tw.red3 g')
    refine ⟨e, f (inc d.h (Phi d.D d.T₀.pr d.k g' : d.c.O)), f (d.ρ₁ g' 1 0), f (inc d.h (d.δ g' : d.c.O)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrg, tn_eq _ _ (by rw [Matrix.map_apply]; exact h01 _) (by rw [Matrix.map_apply]; exact t01 _)
        (by rw [Matrix.map_apply]; exact he10) (by rw [Matrix.map_apply]; exact t00 _) (by rw [Matrix.map_apply]; exact h11 _)]
      simp only [Matrix.map_apply]
      rw [h00, he]
    · rw [hχ 0]
      exact r0
    · rw [hχ 1, e1, r0]
      ring
    · rw [hχ 2, e2, r3]
    · rw [hχ 3]
      exact r3
  have hn : ∀ v, ((d.Q T).map f).n v = flg (f (d.x (T.pl v))) (f (d.s (T.pl v))) := fun v => flg_map f _ _
  have hs : ∀ S : Finset (ℤ × ℤ), wt 2 1 ∈ S → wt 3 0 ∈ S → Supp S ((d.Q T).map f).r := fun S h1 h2 g => by
    obtain ⟨e, P, b, dl, h, -⟩ := key g
    rw [h]
    exact mat_supp h1 h2 dl P b e
  have hsM : Supp nM ((d.Q T).map f).r := hs nM (by decide) (by decide)
  refine ⟨⟨fun g i => ?_, fun (v : T.ι) s _ i => ?_, Or.inr hsM⟩, hsM, ⟨hs aA (by decide) (by decide), fun v => ?_⟩, fun g => ?_⟩
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key g
    rw [h]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · obtain ⟨e, P, b, dl, h, c0, c1, c2, c3⟩ := key s
    show (adj (((d.Q T).map f).n v) * ((d.Q T).map f).r s * ((d.Q T).map f).n v) i i = _
    rw [hn v, h, conj_diag]
    fin_cases i
    exacts [c0.symm, c1.symm, c2.symm, (mul_one dl).trans c3.symm]
  · rw [hn, flg_10]
    rcases d.tau.sgn (T.pl v) with h | h <;> rw [h] <;> simp
  · rw [Matrix.det_fin_two, map_sub, map_mul, map_mul, h00, h11, h01]
    ring
