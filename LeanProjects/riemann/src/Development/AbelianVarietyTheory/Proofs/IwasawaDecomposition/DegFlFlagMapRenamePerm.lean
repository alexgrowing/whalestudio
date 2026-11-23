import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.Schubert

theorem degFl_rename_perm {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (ρ : ι → Equiv.Perm (Fin N))
    (P : MvPolynomial (ι × Fin N) ℝ) :
    Formalism.DegreeFormula.degFl ι N (rename (fun x : ι × Fin N => (x.1, ρ x.1 x.2)) P) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * Formalism.DegreeFormula.degFl ι N P := by
  set f : ι × Fin N → ι × Fin N := fun x => (x.1, ρ x.1 x.2) with hfdef
  have hinj : Function.Injective f := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    simp only [hfdef, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp [(ρ a).injective h2]
  have hsurj : Function.Surjective f := by
    rintro ⟨a, j⟩
    exact ⟨(a, (ρ a).symm j), by simp [hfdef]⟩
  have hexp : ∀ σ : ι → Equiv.Perm (Fin N),
      Formalism.DegreeFormula.permExp (σ * ρ⁻¹) = (Formalism.DegreeFormula.permExp σ).mapDomain f := by
    intro σ
    ext y
    obtain ⟨⟨a, i⟩, rfl⟩ := hsurj y
    rw [Finsupp.mapDomain_apply hinj]
    simp [Formalism.DegreeFormula.permExp, hfdef, Pi.mul_apply, Pi.inv_apply]
  have hsgn : ∀ σ : ι → Equiv.Perm (Fin N),
      (∏ τ, ((Equiv.Perm.sign ((σ * ρ⁻¹) τ) : ℤ) : ℝ)) =
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * ∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ) := by
    intro σ
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Pi.mul_apply, Pi.inv_apply, Equiv.Perm.sign_inv]
  have key : ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
        (rename f P).coeff (Formalism.DegreeFormula.permExp σ) =
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) * ∑ σ : ι → Equiv.Perm (Fin N),
        (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * P.coeff (Formalism.DegreeFormula.permExp σ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight (ρ⁻¹ : ι → Equiv.Perm (Fin N))), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Equiv.coe_mulRight, hsgn, hexp, coeff_rename_mapDomain _ hinj]
    ring
  unfold Formalism.DegreeFormula.degFl
  rw [key]
  ring

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem perm_val_congr {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    {a b : E →+* ℂ} (e : a = b) (i : ℕ) (h1 : i < Dw.mult a) (h2 : i < Dw.mult b) :
    ((w a ⟨i, h1⟩ : Fin (Dw.mult a)) : ℕ) = ((w b ⟨i, h2⟩ : Fin (Dw.mult b)) : ℕ) := by
  subst e; rfl

theorem sign_perm_congr {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    {a b : E →+* ℂ} (e : a = b) : Equiv.Perm.sign (w a) = Equiv.Perm.sign (w b) := by
  subst e; rfl

def flagPerm {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H) :
    Equiv.Perm (Fin (Dw.p + Dw.q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr
    ((finCongr (GlobalTheory.PointChern.mult_of_mem Dw τ.2)).permCongr (w τ.1))
    (Fin.revPerm.permCongr ((finCongr (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ))).permCongr
      (w (conjEmb τ.1)))))

theorem sign_flagPerm {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H) :
    Equiv.Perm.sign (flagPerm Dw w τ) = Equiv.Perm.sign (w τ.1) * Equiv.Perm.sign (w (conjEmb τ.1)) := by
  simp only [flagPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

theorem flagPerm_big {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin (Dw.mult τ.1)) (hi : (i : ℕ) < Dw.p + Dw.q) :
    ((flagPerm Dw w τ ⟨i, hi⟩ : Fin (Dw.p + Dw.q)) : ℕ) = ((w τ.1 i : Fin (Dw.mult τ.1)) : ℕ) := by
  have hp : (i : ℕ) < Dw.p := by
    have h1 := i.2; have h2 := GlobalTheory.PointChern.mult_of_mem Dw τ.2; omega
  have e : (⟨i, hi⟩ : Fin (Dw.p + Dw.q)) = Fin.castAdd Dw.q ⟨i, hp⟩ := rfl
  rw [e]
  unfold flagPerm
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.coe_castAdd, Equiv.permCongr_apply]
  simp

theorem flagPerm_small {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) {σ : E →+* ℂ}
    (hσ : ¬ σ (H.rt : E) = H.rt0) (i : Fin (Dw.mult σ)) (hi : Dw.p + (Dw.q - 1 - (i : ℕ)) < Dw.p + Dw.q) :
    ((flagPerm Dw w ⟨conjEmb σ, GlobalTheory.AllWt.conj_mem hσ⟩ ⟨Dw.p + (Dw.q - 1 - (i : ℕ)), hi⟩ : Fin (Dw.p + Dw.q)) : ℕ) =
      Dw.p + (Dw.q - 1 - ((w σ i : Fin (Dw.mult σ)) : ℕ)) := by
  have hq : (i : ℕ) < Dw.q := by
    have h1 := i.2; have h2 := GlobalTheory.PointChern.mult_of_not_mem Dw hσ; omega
  have e : (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), hi⟩ : Fin (Dw.p + Dw.q)) = Fin.natAdd Dw.p ⟨Dw.q - 1 - i, by omega⟩ := rfl
  rw [e]
  unfold flagPerm
  rw [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.coe_natAdd, Equiv.permCongr_apply, Equiv.permCongr_apply]
  simp only [Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev, finCongr_apply, finCongr_symm, Fin.coe_cast]
  have key : ∀ x : Fin (Dw.mult (conjEmb (conjEmb σ))), (x : ℕ) = (i : ℕ) →
      ((w (conjEmb (conjEmb σ)) x : Fin _) : ℕ) = ((w σ i : Fin (Dw.mult σ)) : ℕ) := by
    rintro ⟨x, hx⟩ hxi
    simp only at hxi
    subst hxi
    exact perm_val_congr Dw w (GlobalTheory.AllWt.conjEmb_conjEmb σ) _ _ i.2
  rw [key _ (by simp; omega)]
  omega

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flagMap_rename {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ)))
    (Q : MvPolynomial (GlobalTheory.GoodMetric.Root Dw.mult) ℝ) :
    flagMap Dw (rename (fun x : GlobalTheory.GoodMetric.Root Dw.mult =>
        (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root Dw.mult)) Q) =
      rename (fun x : GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) => (x.1, flagPerm Dw w x.1 x.2)) (flagMap Dw Q) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun x => ?_
  simp only [AlgHom.comp_apply, rename_X, flagMap, aeval_X]
  obtain ⟨σ, i⟩ := x
  by_cases h : σ (H.rt : E) = H.rt0
  · simp only [flagRoot, dif_pos h, rename_X]
    congr 2
    exact Fin.ext (flagPerm_big Dw w ⟨σ, h⟩ i _).symm
  · simp only [flagRoot, dif_neg h, map_neg, rename_X]
    congr 3
    exact Fin.ext (flagPerm_small Dw w h i _).symm

theorem prod_sign_eq {H : Host E} (Dw : Datum H) (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) :
    (∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) = ∏ τ : GlobalTheory.AllWt.Psi H, Equiv.Perm.sign (flagPerm Dw w τ) := by
  simp only [sign_flagPerm, Finset.prod_mul_distrib]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  refine Fintype.prod_equiv
    { toFun := fun τ => (⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩ : GlobalTheory.AllWt.Psi H)
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1) } _ _ ?_
  intro τ
  simp only [Equiv.coe_fn_mk]
  exact sign_perm_congr Dw w (GlobalTheory.AllWt.conjEmb_conjEmb τ.1).symm

end GlobalTheory.Schubert

namespace GlobalTheory.Schubert

theorem degFl_flagMap_rename_perm (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (w : ∀ τ, Equiv.Perm (Fin (Dw.mult τ))) (Q : MvPolynomial (GlobalTheory.GoodMetric.Root Dw.mult) ℝ) :
    Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw (MvPolynomial.rename
              (fun x : GlobalTheory.GoodMetric.Root Dw.mult => (⟨x.1, w x.1 x.2⟩ : GlobalTheory.GoodMetric.Root Dw.mult)) Q)) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) *
        Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (GlobalTheory.Schubert.flagMap Dw Q) := by
  rw [flagMap_rename, degFl_rename_perm, prod_sign_eq]
  push_cast
  rfl

end GlobalTheory.Schubert
