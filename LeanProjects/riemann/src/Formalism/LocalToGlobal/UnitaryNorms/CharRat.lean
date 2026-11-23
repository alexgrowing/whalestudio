import Formalism.LocalToGlobal.UnitaryNorms.CharTied

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem ide_fst_mul {L : Type} [Field L] [NumberField L] (a b : Ideles L) (w : InfinitePlace L) :
    ((a * b : Ideles L) : AdeleRing (𝓞 L) L).1 w = (a : AdeleRing (𝓞 L) L).1 w * (b : AdeleRing (𝓞 L) L).1 w := rfl

theorem infDiag_fst {L : Type} [Field L] [NumberField L] (k : Lˣ) (w : InfinitePlace L) :
    ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L).1 w = algebraMap L w.Completion (k : L) := by
  classical
  have h : ∀ s : Finset (InfinitePlace L),
      (((∏ w' ∈ s, (infIdele L w').comp (atInf w')) k : Ideles L) : AdeleRing (𝓞 L) L).1 w =
        if w ∈ s then algebraMap L w.Completion (k : L) else 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, MonoidHom.mul_apply, ide_fst_mul, ih]
      by_cases hwa : w = a
      · subst hwa
        rw [if_neg ha, mul_one, if_pos (Finset.mem_insert_self _ _)]
        exact infIdele_fst_self L w _
      · have h1 : (((infIdele L a).comp (atInf a)) k : AdeleRing (𝓞 L) L).1 w = 1 := infIdele_fst_ne L a w hwa _
        rw [h1, one_mul]
        simp [Finset.mem_insert, hwa]
  have := h Finset.univ
  rwa [if_pos (Finset.mem_univ _)] at this

theorem isFinIdele_diag {L : Type} [Field L] [NumberField L] (k : Lˣ) :
    IsFinIdele (diagUnits L k * (infDiag k)⁻¹) := by
  intro w
  have h1 : ((infDiag k * (infDiag k)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 w = 1 := by
    rw [mul_inv_cancel]; rfl
  rw [ide_fst_mul, infDiag_fst] at h1
  rw [ide_fst_mul]
  exact h1

theorem DtTied.rat_val {D : D7} {C : CharFrame D} (T : DtTied D C) (χ : HChar D.host.E) (f : D.Dt →* ℂˣ)
    (hf : ∀ a : Ideles D.host.E, IsFinIdele a → f (T.eDt a) = χ.1 a) :
    letI := D.host.cmStar
    ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
      f (D.e1Dt z) = (χ.inf k)⁻¹ := by
  intro k z hz
  have h1 : T.eDt (infDiag k) = 1 := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, map_prod]
    exact Finset.prod_eq_one fun w _ => T.inf w _
  have h2 := hf _ (isFinIdele_diag k)
  rw [map_mul, map_inv, h1, inv_one, mul_one, T.rat k z hz, map_mul, map_inv, χ.2.2 k, one_mul] at h2
  exact h2

theorem DtTied.muTil_rat {D : D7} {C : CharFrame D} (T : DtTied D C) (j : Fin D.R.m) :
    letI := D.host.cmStar
    ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
      D.muTil (j.1 + 1) (D.e1Dt z) = ((C.mu0 j).inf k)⁻¹ :=
  T.rat_val (C.mu0 j) _ (T.muTil_eq j)

theorem DtTied.chiD_rat {D : D7} {C : CharFrame D} (T : DtTied D C) :
    letI := D.host.cmStar
    ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
      D.chiD (D.e1Dt z) = (C.chiPsi.inf k)⁻¹ :=
  T.rat_val C.chiPsi _ T.chiD_eq

theorem emb_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.GG) (x : H.E) :
    H.emb g (H.conj x) = starRingEnd ℂ (H.emb g x) := by
  exact H.conjE_apply (H.emb g) x

theorem IsChiPsi.rat {R : Ranks} {H : Formalism.BasicNotions.Host R} {χ : HChar H.E} (h : IsChiPsi H χ) (k : H.Eˣ) (z : H.E)
    (hz : z * H.conj (k : H.E) = k) : (((χ.inf k)⁻¹ : ℂˣ) : ℂ) = ∏ g : R.Psi, (H.emb (g : R.GG) z)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, h.inf k, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  congr 1
  have hx : H.emb (g : R.GG) (k : H.E) ≠ 0 := (map_ne_zero _).mpr k.ne_zero
  have h1 : H.emb (g : R.GG) z * starRingEnd ℂ (H.emb (g : R.GG) (k : H.E)) = H.emb (g : R.GG) (k : H.E) := by
    rw [← emb_conj, ← map_mul, hz]
  show (H.emb (g : R.GG) (k : H.E) / ((‖H.emb (g : R.GG) (k : H.E)‖ : ℝ) : ℂ)) ^ (2 : ℤ) = _
  set x := H.emb (g : R.GG) (k : H.E) with hxdef
  have hc : starRingEnd ℂ x ≠ 0 := (map_ne_zero _).mpr hx
  have h2 : ((‖x‖ : ℝ) : ℂ) ^ 2 = x * starRingEnd ℂ x := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h3 : H.emb (g : R.GG) z = x / starRingEnd ℂ x := (eq_div_iff hc).mpr h1
  rw [zpow_ofNat, div_pow, h2, h3]
  field_simp

theorem hasInf_even_rat {R : Ranks} {H : Formalism.BasicNotions.Host R} {χ : HChar H.E} {m : R.Psi → ℤ}
    (h : χ.HasInf (embPsi H) (fun g => 2 * m g)) (k : H.Eˣ) (z : H.E) (hz : z * H.conj (k : H.E) = k) :
    ((χ.inf k : ℂˣ) : ℂ) = ∏ g : R.Psi, H.emb (g : R.GG) z ^ m g := by
  rw [h k]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hx : H.emb (g : R.GG) (k : H.E) ≠ 0 := (map_ne_zero _).mpr k.ne_zero
  have h1 : H.emb (g : R.GG) z * starRingEnd ℂ (H.emb (g : R.GG) (k : H.E)) = H.emb (g : R.GG) (k : H.E) := by
    rw [← emb_conj, ← map_mul, hz]
  show (H.emb (g : R.GG) (k : H.E) / ((‖H.emb (g : R.GG) (k : H.E)‖ : ℝ) : ℂ)) ^ (2 * m g) = _
  set x := H.emb (g : R.GG) (k : H.E) with hxdef
  have hc : starRingEnd ℂ x ≠ 0 := (map_ne_zero _).mpr hx
  have h2 : ((‖x‖ : ℝ) : ℂ) ^ 2 = x * starRingEnd ℂ x := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h3 : H.emb (g : R.GG) z = x / starRingEnd ℂ x := (eq_div_iff hc).mpr h1
  rw [zpow_mul]
  congr 1
  rw [zpow_ofNat, div_pow, h2, h3]
  field_simp

theorem DtTied.muTil_rat' {D : D7} {C : CharFrame D} (T : DtTied D C) (j : Fin D.R.m) (m : D.R.Psi → ℤ)
    (hm : ∀ g, (m g : ℚ) = eExp D j g) :
    letI := D.host.cmStar
    ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
      ((D.muTil (j.1 + 1) (D.e1Dt z) : ℂˣ) : ℂ) = ∏ g : D.R.Psi, D.host.emb (g : D.R.GG) (z : D.host.E) ^ m g := by
  intro k z hz
  obtain ⟨n, hn, hinf⟩ := (C.isMu0 j).inf
  have e : n = fun g => 2 * (-m g) := funext fun g => by
    have h0 : (n g : ℚ) = 2 * -eExp D j g := hn g
    rw [← hm g] at h0
    exact_mod_cast h0
  subst e
  rw [T.muTil_rat j k z hz, Units.val_inv_eq_inv_val, hasInf_even_rat hinf k z hz, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun g _ => by rw [zpow_neg, inv_inv]

end Formalism.L2.Host
