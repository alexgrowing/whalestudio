import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.NormAICOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut Polynomial

namespace LateralTheory.E.NormPf.AffPf

theorem aic_intClosure {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (h : GlobalTheory.EtC.AIC B) :
    GlobalTheory.EtC.AIC (integralClosure A B) := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map (algebraMap (integralClosure A B) B)) (hp.map _)
    (by rwa [natDegree_map_eq_of_injective Subtype.val_injective])
  have hint : IsIntegral (integralClosure A B) a := ⟨p, hp, by rwa [eval₂_eq_eval_map]⟩
  have hA : IsIntegral A a := by
    first
    | exact hint.trans
    | exact isIntegral_trans a hint
    | exact IsIntegral.tower_top hint
  have hm : a ∈ integralClosure A B := hA
  refine ⟨⟨a, hm⟩, ?_⟩
  apply Subtype.val_injective
  have e : ((eval (⟨a, hm⟩ : integralClosure A B) p : integralClosure A B) : B) =
      eval a (p.map (algebraMap (integralClosure A B) B)) := by
    rw [Polynomial.eval_map]
    exact (Polynomial.eval₂_hom (algebraMap (integralClosure A B) B) (⟨a, hm⟩ : integralClosure A B)).symm
  rw [e, ha]
  rfl

theorem aic_field (K : Type) [Field K] [IsAlgClosed K] : GlobalTheory.EtC.AIC K := by
  intro p _ hd
  exact IsAlgClosed.exists_root p (by rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hd)]; exact_mod_cast hd.ne')

theorem aic_subsingleton (R : Type) [CommRing R] [Subsingleton R] : GlobalTheory.EtC.AIC R :=
  fun _ _ _ => ⟨0, Subsingleton.elim _ _⟩

theorem aic_specK (K : Type) [Field K] [IsAlgClosed K] (V : (Spec (CommRingCat.of K)).Opens) :
    GlobalTheory.EtC.AIC Γ(Spec (CommRingCat.of K), V) := by
  by_cases hV : (V : Set (Spec (CommRingCat.of K))).Nonempty
  · have h : V = ⊤ := by
      obtain ⟨y, hy⟩ := hV
      ext x
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      have : x = y := Subsingleton.elim (α := PrimeSpectrum K) x y
      rwa [this]
    subst h
    exact OpenPf.aic_of_equiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (aic_field K)
  · have h : V = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hV ⟨x, hx⟩
    subst h
    exact aic_subsingleton _

theorem affAIC : AICPf.AffAIC := by
  intro K _ _ W g _ _ U hU
  let := (g.app U).hom.toAlgebra
  exact OpenPf.aic_of_equiv (g.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
    (aic_intClosure (aic_specK K _))

end LateralTheory.E.NormPf.AffPf

end
