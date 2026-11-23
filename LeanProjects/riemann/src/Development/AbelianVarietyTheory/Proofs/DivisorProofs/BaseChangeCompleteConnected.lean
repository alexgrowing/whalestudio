import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem flat_injective_dvr {V O : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing O] [IsDomain O]
    (φ : V →+* O) (hφ : Function.Injective φ) : Flat (Spec.map (CommRingCat.ofHom φ)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  change φ.Flat
  algebraize [φ]
  change Module.Flat V O
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  rintro t ⟨⟨a, ha⟩, ht⟩
  have h1 : φ a * t = 0 := ht
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd (hφ (h.trans (map_zero φ).symm)) (nonZeroDivisors.ne_zero ha)
  · exact h

theorem connected_pullback_of_geomIrr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) (hφ : Function.Injective φ)
    (_hloc : IsLocalHom φ) (X : Scheme.{0}) (s : X ⟶ Spec (.of V)) (Xw : X.Opens) (hX : IsIntegral X) (hs : Flat s)
    (hg : GeomIrr s Xw) : ConnectedSpace ↑(pullback s (Spec.map (CommRingCat.ofHom φ))) := by
  set K := FractionRing O
  set φ' := Spec.map (CommRingCat.ofHom φ)
  set ι' : Spec (.of K) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom (algebraMap O K))
  set f : V →+* K := (algebraMap O K).comp φ
  have hf : Function.Injective f := (IsFractionRing.injective O K).comp hφ
  have hfe : spMap f = ι' ≫ φ' := by
    simp only [spMap, ι', φ', f, ← Spec.map_comp]
    rfl
  haveI hWi := hg K f hf
  set Wk := pullback (Xw.ι ≫ s) (spMap f)

  let m : Wk ⟶ pullback s φ' := pullback.lift (pullback.fst _ _ ≫ Xw.ι) (pullback.snd _ _ ≫ ι') (by
    simp only [Category.assoc]
    rw [← hfe]
    exact pullback.condition)
  haveI : Flat φ' := flat_injective_dvr φ hφ
  have gfst : GeneralizingMap (pullback.fst s φ') := by
    exact Flat.generalizingMap _
  have gsnd : GeneralizingMap (pullback.snd s φ') := by
    exact Flat.generalizingMap _

  haveI : IrreducibleSpace X := inferInstance
  set η := genericPoint X
  obtain ⟨w₀⟩ := (inferInstance : Nonempty Wk)
  have hη : η ∈ Xw := by
    exact ((genericPoint_spec X).mem_open_set_iff Xw.isOpen).2
      ⟨_, trivial, (pullback.fst (Xw.ι ≫ s) (spMap f) w₀).2⟩
  have key : ∀ x : ↥(pullback s φ'), x ∈ closure (Set.range m) := by
    intro x
    obtain ⟨x₁, hx₁, hx₁s⟩ := gsnd (b := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)) (a := x)
      ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le)
    obtain ⟨x₂, hx₂, hx₂f⟩ := gfst (genericPoint_specializes (pullback.fst s φ' x₁))
    have hs₂ : pullback.snd s φ' x₂ = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := by
      have := (hx₂.map (pullback.snd s φ').continuous)
      rw [hx₁s] at this
      exact PrimeSpectrum.ext (le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 this))

    have hι : ι' (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := by
      have := bot_map (X := Spec (.of O)) (IsFractionRing.injective O K) (𝟙 _)
      exact this
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd s φ') (g := ι') x₂
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) (by rw [hs₂, hι])
    obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := Xw.ι)
      (g := pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟨η, hη⟩ z
      (by rw [Scheme.Hom.comp_apply, hz₁, hx₂f]; rfl)
    let h : pullback Xw.ι (pullback.fst (pullback.snd s φ') ι' ≫ pullback.fst s φ') ⟶ Wk :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
        simp only [Category.assoc]
        rw [pullback.condition_assoc, Category.assoc, pullback.condition, pullback.condition_assoc, hfe])
    have hm : h ≫ m = pullback.snd _ _ ≫ pullback.fst (pullback.snd s φ') ι' := by
      apply pullback.hom_ext
      · simp only [Category.assoc, m, h, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [pullback.condition]
      · simp only [Category.assoc, m, h, pullback.lift_snd, pullback.lift_snd_assoc]
        rw [pullback.condition]
    have hx₂m : x₂ ∈ Set.range m := ⟨h y, by
      rw [← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply, hy₂, hz₁]⟩
    exact closure_mono (Set.singleton_subset_iff.2 hx₂m) (hx₂.trans hx₁).mem_closure
  have hirr : IsIrreducible (Set.range m) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ Wk).image _ m.continuous.continuousOn
  have : IrreducibleSpace ↑(pullback s φ') := by
    have hcl := hirr.closure
    rw [Set.eq_univ_of_forall key] at hcl
    exact (irreducibleSpace_def _).2 hcl
  infer_instance

end GlobalTheory.FlatModel
