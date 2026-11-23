import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisBasisModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingleton
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPushout_of_bases {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (g' : S →+* S') (f' : R' →+* S') (hc : g'.comp f = f'.comp g) {ι : Type} :
    letI := f.toAlgebra; letI := f'.toAlgebra
    ∀ (b : Module.Basis ι R S) (b' : Module.Basis ι R' S'), (∀ i, g' (b i) = b' i) →
      CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom g')
        (CommRingCat.ofHom f') := by
  letI := f.toAlgebra; letI := g.toAlgebra; letI := g'.toAlgebra; letI := f'.toAlgebra
  letI : Algebra R S' := (f'.comp g).toAlgebra
  intro b b' hb
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hc x).symm
  have hbc : IsBaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap := by
    refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis R' b).equiv b' (Equiv.refl _)) fun m => ?_
    have : (((Algebra.TensorProduct.basis R' b).equiv b' (Equiv.refl _)).toLinearMap.restrictScalars R ∘ₗ
        TensorProduct.mk R R' S 1) = (IsScalarTower.toAlgHom R S S').toLinearMap := b.ext fun i => by
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
        IsScalarTower.coe_toAlgHom']
      rw [← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
      exact (hb i).symm
    exact LinearMap.congr_fun this m
  haveI : Algebra.IsPushout R R' S S' := ⟨hbc⟩
  haveI : Algebra.IsPushout R S R' S' := Algebra.IsPushout.symm inferInstance
  exact CommRingCat.isPushout_of_isPushout R S R' S'

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem exists_basis_quot_of_map_eq {S A : Type} [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (J : Ideal A)
    (hJ : I.map s = J) (hle : I ≤ J.comap s) {ι : Type} (b₀ : ι → A)
    (h : letI := (Ideal.quotientMap (I.map s) s Ideal.le_comap_map).toAlgebra
      ∃ b : Module.Basis ι (S ⧸ I) (A ⧸ I.map s), ∀ i, b i = Ideal.Quotient.mk _ (b₀ i)) :
    letI := (Ideal.quotientMap J s hle).toAlgebra
    ∃ b : Module.Basis ι (S ⧸ I) (A ⧸ J), ∀ i, b i = Ideal.Quotient.mk _ (b₀ i) := by
  subst hJ
  exact h

theorem map_adI_pow {R : Type} [CommRing R] {l : ℕ} {B B' : Obj l R} (f : Hom B B') (hI : B.I.map f.f = B'.I)
    (m : ℕ) : (adI B ^ m).map f.f = adI B' ^ m := by
  rw [Ideal.map_pow, adI, adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem env_map_tb_b {bk : BK K} {B B' : Obj l ↥(OL K)} {t p : B.A} {k : Hom B B'} {En : Env bk B t p}
    {En' : Env bk B' (k.f t) (k.f p)} (k' : Hom En.Q En'.Q) (h1 : k'.comp En.inl = En'.inl.comp k)
    (h2 : k'.comp En.inr = En'.inr) (α : Digits l) : k'.f (En.tb.b α) = En'.tb.b α := by
  have hreg : En'.inl.f (k.f t) ∈ nonZeroDivisors En'.Q.A :=
    by
    haveI := En'.Q.inv
    exact mem_nonZeroDivisors_of_invertible_span_singleton _ _ (Module.Invertible.congr (LinearEquiv.ofEq _ _ En'.I_eq))
  have e1 : ∀ a, k'.f (En.inl.f a) = En'.inl.f (k.f a) := fun a => by
    have := congrArg (fun h => Hom.f h a) h1
    exact this
  have e2 : k'.f (BK.hf En.inr X) = BK.hf En'.inr X := by
    have := congrArg (fun h => Hom.f h X) h2
    exact this
  have hw : k'.f En.w = En'.w := by
    have a1 := congrArg k'.f En.w_eq
    have a2 := En'.w_eq
    have a3 : k'.f (En.inl.f p + En.inl.f t * En.w) = En'.inl.f (k.f p) + En'.inl.f (k.f t) * k'.f En.w := by
      simp only [map_add, map_mul, e1]
    have : En'.inl.f (k.f t) * (k'.f En.w - En'.w) = 0 := by linear_combination -a3 - a1 + e2 + a2
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hreg).2 _ (by rw [mul_comm]; exact this))
  have hδ : ∀ i : ℕ, k'.f (En.Q.D.δ^[i] En.w) = En'.Q.D.δ^[i] En'.w := fun i =>
    (Function.Semiconj.iterate_right (f := k'.f) k'.f_δ i En.w).trans (congrArg (En'.Q.D.δ^[i]) hw)
  calc k'.f (En.tb.b α) = k'.f (α.1.prod fun i n => (En.Q.D.δ^[i] En.w) ^ n) := congrArg k'.f (En.tb_b α)
    _ = α.1.prod fun i n => k'.f ((En.Q.D.δ^[i] En.w) ^ n) := map_finsuppProd k'.f _ _
    _ = α.1.prod fun i n => (En'.Q.D.δ^[i] En'.w) ^ n :=
      Finsupp.prod_congr fun i _ => (map_pow _ _ _).trans (congrArg (· ^ α.1 i) (hδ i))
    _ = En'.tb.b α := (En'.tb_b α).symm

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem env_isPO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B B' : Obj l ↥(OL K)) (t p : B.A)
    (k : Hom B B') (En : Env bk B t p) (En' : Env bk B' (k.f t) (k.f p)),
    ∃ k' : Hom En.Q En'.Q, IsPO En.inl k k' En'.inl := by
  intro l _ K bk B B' t p k En En'
  obtain ⟨k', ⟨h1, h2⟩, -⟩ := En.univ En'.Q (En'.inl.comp k) En'.inr
  have e1 : ∀ a, k'.f (En.inl.f a) = En'.inl.f (k.f a) := fun a => by
    have := congrArg (fun h => Hom.f h a) h1
    exact this
  refine ⟨k', ⟨h1, fun m => ?_⟩⟩
  have q1 := map_adI_pow En.inl (GlobalTheory.T.prism_hom_map_ideal_eq l _ B En.Q En.inl) m
  have q2 := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B.A En.Q.A En.inl.f (adI B) (Digits l) En.tb m
  have q3 := exists_basis_quot_of_map_eq En.inl.f (adI B ^ m) (adI En.Q ^ m) q1 (adI_pow_le En.inl m) En.tb.b q2
  obtain ⟨b, hb⟩ := q3
  have r1 := map_adI_pow En'.inl (GlobalTheory.T.prism_hom_map_ideal_eq l _ B' En'.Q En'.inl) m
  have r2 := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B'.A En'.Q.A En'.inl.f (adI B') (Digits l) En'.tb m
  have r3 := exists_basis_quot_of_map_eq En'.inl.f (adI B' ^ m) (adI En'.Q ^ m) r1 (adI_pow_le En'.inl m) En'.tb.b r2
  obtain ⟨b', hb'⟩ := r3
  refine isPushout_of_bases (qmap En.inl m) (qmap k m) (qmap k' m) (qmap En'.inl m) ?_ b b' fun α => ?_
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    exact congrArg (Ideal.Quotient.mk (adI En'.Q ^ m)) (e1 a)
  · exact (congrArg (qmap k' m) (hb α)).trans ((qmap_mk k' m _).trans
      ((congrArg (Ideal.Quotient.mk (adI En'.Q ^ m)) (env_map_tb_b k' h1 h2 α)).trans (hb' α).symm))

end GlobalTheory.BSP
