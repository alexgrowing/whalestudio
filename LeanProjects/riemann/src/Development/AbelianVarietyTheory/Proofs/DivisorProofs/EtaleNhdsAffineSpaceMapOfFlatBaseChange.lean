import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.EtaleAtDescent

open TensorProduct

theorem notMem_support_of_flat {B D M N : Type} [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module D N] [IsScalarTower B D N]
    (φ : M →ₗ[B] N) (hφ : Function.Injective (φ.liftBaseChange D)) (Q : PrimeSpectrum D)
    (hQ : Q ∉ Module.support D N) : PrimeSpectrum.comap (algebraMap B D) Q ∉ Module.support B M := by
  rw [Module.notMem_support_iff'] at hQ ⊢
  intro x
  by_contra hx
  push Not at hx
  obtain ⟨f, hf, hfx⟩ := hQ (φ x)
  have h0 : f ⊗ₜ[B] x = 0 := hφ (by simpa using hfx)
  have hex := Module.Flat.lTensor_exact D (LinearMap.exact_subtype_ker_map (LinearMap.toSpanSingleton B M x))
  obtain ⟨z, hz⟩ := (hex (f ⊗ₜ[B] 1)).1 (by simpa using h0)
  have key : ∀ z : D ⊗[B] LinearMap.ker (LinearMap.toSpanSingleton B M x),
      TensorProduct.rid B D (LinearMap.lTensor D (LinearMap.ker (LinearMap.toSpanSingleton B M x)).subtype z) ∈
        Q.asIdeal := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add]; exact Q.asIdeal.add_mem ha hb
    | tmul d r =>
      have hr : algebraMap B D r.1 ∈ Q.asIdeal := by
        by_contra h
        exact hx r.1 h (LinearMap.mem_ker.1 r.2)
      simpa [Algebra.smul_def] using Q.asIdeal.mul_mem_right d hr
  have := key z
  rw [hz] at this
  exact hf (by simpa using this)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem mem_etaleLocus_of_flat {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.Flat A C] (Q : PrimeSpectrum (C ⊗[A] B)) (hQ : Q ∈ Algebra.etaleLocus C (C ⊗[A] B)) :
    PrimeSpectrum.comap (algebraMap B (C ⊗[A] B)) Q ∈ Algebra.etaleLocus A B := by
  rw [Algebra.etaleLocus_eq_compl_support] at hQ ⊢
  haveI : Module.Flat B (C ⊗[A] B) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv A B C (C ⊗[A] B)).toLinearEquiv.symm
  refine ⟨notMem_support_of_flat (KaehlerDifferential.map A C B (C ⊗[A] B)) ?_ Q hQ.1,
    notMem_support_of_flat (Algebra.H1Cotangent.map A C B (C ⊗[A] B)) ?_ Q hQ.2⟩
  · have hc : (KaehlerDifferential.tensorKaehlerEquivBase A C B (C ⊗[A] B) : _ → _) =
        (KaehlerDifferential.map A C B (C ⊗[A] B)).liftBaseChange (C ⊗[A] B) ∘
          (Algebra.IsPushout.cancelBaseChange A C B (C ⊗[A] B) Ω[B⁄A]).symm := by
      funext z
      induction z with
      | zero => simp
      | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        rw [KaehlerDifferential.tensorKaehlerEquivBase_tmul, Function.comp_apply,
          Algebra.IsPushout.cancelBaseChange_symm_tmul, LinearMap.liftBaseChange_tmul, algebraMap_smul]
    have hi := (KaehlerDifferential.tensorKaehlerEquivBase A C B (C ⊗[A] B)).injective
    rw [hc] at hi
    exact hi.of_comp_right (LinearEquiv.surjective _)
  · have hc : (Algebra.tensorH1CotangentOfFlat A B C : _ → _) =
        (Algebra.H1Cotangent.map A C B (C ⊗[A] B)).liftBaseChange (C ⊗[A] B) ∘
          (Algebra.IsPushout.cancelBaseChange A C B (C ⊗[A] B) (Algebra.H1Cotangent A B)).symm := by
      funext z
      induction z with
      | zero => simp
      | add x y hx hy => simp only [Function.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        rw [Algebra.tensorH1CotangentOfFlat_tmul, Function.comp_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul,
          LinearMap.liftBaseChange_tmul, algebraMap_smul]
    have hi := (Algebra.tensorH1CotangentOfFlat A B C).injective
    rw [hc] at hi
    exact hi.of_comp_right (LinearEquiv.surjective _)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem exists_etale_spec {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    [Module.Flat A C] [Algebra.FinitePresentation A B] (W : (Spec (.of (C ⊗[A] B))).Opens)
    (p : Spec (.of (C ⊗[A] B))) (hp : p ∈ W)
    (hW : Etale (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))))) :
    ∃ V : (Spec (.of B)).Opens, Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[A] B))) p ∈ V ∧
      Etale (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hf⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp W.isOpen
  let j := Spec.map (CommRingCat.ofHom (algebraMap (C ⊗[A] B) (Localization.Away f)))
  have hj : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    refine subset_trans ?_ hf
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le
  have h1 : Etale (IsOpenImmersion.lift W.ι j hj ≫ W.ι ≫
      Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B)))) := inferInstance
  rw [IsOpenImmersion.lift_fac_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
    HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap] at h1
  have h2 := mem_etaleLocus_of_flat p (Algebra.basicOpen_subset_etaleLocus_iff_etale.2 h1 hpf)
  rw [Algebra.mem_etaleLocus_iff] at h2
  obtain ⟨g, hg, hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := A)
    (PrimeSpectrum.comap (algebraMap B (C ⊗[A] B)) p).asIdeal
  let i := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  refine ⟨i.opensRange, ?_, ?_⟩
  · exact (PrimeSpectrum.localization_away_comap_range (Localization.Away g) g).ge hg
  · have h3 : Etale (i ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq,
        HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
      exact hE
    rw [← i.isoOpensRange_inv_comp, Category.assoc]
    infer_instance

theorem exists_etale_of_isAffine {U T S : Scheme.{0}} [IsAffine S] (τ : U ⟶ S) (h : T ⟶ S)
    [LocallyOfFinitePresentation τ] [Flat h] (W : (pullback τ h).Opens) (p : ↥(pullback τ h)) (hp : p ∈ W)
    (hW : Etale (W.ι ≫ pullback.snd τ h)) : ∃ V : U.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  obtain ⟨B, i, _, q, hq⟩ := U.exists_Spec_apply_eq (pullback.fst τ h p)
  obtain ⟨C, k, _, t, ht⟩ := T.exists_Spec_apply_eq (pullback.snd τ h p)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ τ ≫ S.isoSpec.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (k ≫ h ≫ S.isoSpec.hom)
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  letI : Algebra B (C ⊗[Γ(S, ⊤)] B) := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.FinitePresentation Γ(S, ⊤) B := by
    have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 this
  haveI : Module.Flat Γ(S, ⊤) C := by
    have : Flat (Spec.map ψ) := by rw [hψ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 this
  have hpb : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[Γ(S, ⊤)] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B)))) (Spec.map φ) (Spec.map ψ) :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct Γ(S, ⊤) C B)).flip
  let m := pullback.map (Spec.map φ) (Spec.map ψ) τ h i k S.isoSpec.inv (by simp [hφ]) (by simp [hψ])
  have hm : IsOpenImmersion m := inferInstance
  have hpm : p ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨q, hq⟩, ⟨t, ht⟩⟩
  let j := hpb.isoPullback.hom ≫ m
  have j1 : j ≫ pullback.fst τ h = Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[Γ(S, ⊤)] B))) ≫ i := by
    simp only [j, m, pullback.map, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc]
  have j2 : j ≫ pullback.snd τ h = Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B))) ≫ k := by
    simp only [j, m, pullback.map, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc]
  obtain ⟨p', rfl⟩ : ∃ p', j p' = p := by
    obtain ⟨p₀, rfl⟩ := hpm
    obtain ⟨p₁, rfl⟩ := hpb.isoPullback.hom.surjective p₀
    exact ⟨p₁, by simp [j]⟩
  have h1 : Etale ((j ∣_ W) ≫ W.ι ≫ pullback.snd τ h) := inferInstance
  rw [morphismRestrict_ι_assoc, j2, ← Category.assoc] at h1
  have h2 := Etale.of_comp ((j ⁻¹ᵁ W).ι ≫ Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[Γ(S, ⊤)] B)))) k
  obtain ⟨V, hV, hE⟩ := exists_etale_spec (j ⁻¹ᵁ W) p' hp h2
  refine ⟨i ''ᵁ V, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, j1, Scheme.Hom.comp_apply]
    exact ⟨_, hV, rfl⟩
  · have hE' : Etale (V.ι ≫ Spec.map φ) := hE
    have e : (i ''ᵁ V).ι ≫ τ = (i.isoImage V).inv ≫ (V.ι ≫ Spec.map φ) ≫ S.isoSpec.inv := by
      simp [hφ]
    rw [e]
    infer_instance

theorem etale_nhds_of_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (U : Over (Sp R)) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)), LocallyOfFiniteType U.hom → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)), Flat h → ∀ (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), p ∈ W → Etale (W.ι ≫ pullback.snd τ h) → ∃ V : U.left.Opens, pullback.fst τ h p ∈ V ∧ Etale (V.ι ≫ τ) := by
  intro R _ _ _ hR U g τ hU hτ T h hh W p hp hW
  haveI := hR.1
  haveI : LocallyOfFiniteType (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hU
  haveI : LocallyOfFiniteType τ := locallyOfFiniteType_of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  haveI : IsLocallyNoetherian 𝔸(Fin g; Sp R) := LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin g; Sp R) ↘ Sp R)
  exact exists_etale_of_isAffine τ h W p hp hW

end GlobalTheory.EtaleAtDescent
