import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem isObU_of_cob : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (t : ∀ T : C, (F.obj T)ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsFun → (∀ T T' a, (u' T T' a : F.obj T') * mp F a (t T : F.obj T) = (t T' : F.obj T') * (u T T' a : F.obj T')) → IsObU L α u c → IsObU L α u' c := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' t c hfun hrel hob
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := hob
  have hlift : ∀ T, ∃ τ : (L.B T)ˣ, L.p T (τ : L.B T) = (t T : F.obj T) := by
    intro T
    obtain ⟨b, hb⟩ := L.surj T (t T : F.obj T)
    obtain ⟨b', hb'⟩ := L.surj T (((t T)⁻¹ : (F.obj T)ˣ) : F.obj T)
    have hn : L.p T (b * b' - 1) = 0 := by
      rw [map_sub, map_mul, map_one, hb, hb']; simp
    rw [L.ker] at hn
    have hnil : IsNilpotent (b * b' - 1) := by
      refine ⟨2, ?_⟩
      have h2 : (b * b' - 1) ^ 2 ∈ (I.map (algebraMap R (L.B T))) ^ 2 := Ideal.pow_mem_pow hn 2
      rw [← Ideal.map_pow, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h2
      simpa using h2
    have hu : IsUnit (b * b') := by simpa using hnil.isUnit_one_add
    exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by simp [hb]⟩
  choose τ hτ using hlift
  let ρu : ∀ {T T' : C} (_ : T ⟶ T'), (L.B T)ˣ →* (L.B T')ˣ := fun a ↦ Units.map (L.ρ a).toRingHom.toMonoidHom
  refine ⟨fun T T' a ↦ τ T' * v T T' a * (ρu a (τ T))⁻¹, σ, z, ?_, hσ, hc, ?_⟩
  · intro T T' a
    have hm : IsUnit (mp F a (t T : F.obj T)) := (t T).isUnit.map (mp F a)
    have hinv : (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.ρ a (τ T : L.B T) = 1 := by
      have := (ρu a (τ T)).inv_mul
      simpa [ρu] using this
    refine (hm.mul_left_inj).mp ?_
    have key : L.p T' (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.p T' (L.ρ a (τ T : L.B T)) = 1 := by
      rw [← map_mul, hinv, map_one]
    rw [hrel, ← hτ T, ← L.nat a]
    simp only [Units.val_mul, map_mul]
    rw [_root_.mul_assoc _ (L.p T' _), key, _root_.mul_one, hτ T', hv]
  · intro T T' T'' a b
    refine ⟨(hz T T' T'' a b).1, ?_⟩
    have hzb := (hz T T' T'' a b).2
    have e1 : L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T')) * L.ρ b (L.ρ a (τ T : L.B T)) = 1 := by
      have h : (((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T') * L.ρ a (τ T : L.B T) = 1 := by
        simpa [ρu] using (ρu a (τ T)).inv_mul
      rw [← map_mul, h, map_one]
    have e2 : (((ρu b (τ T'))⁻¹ : (L.B T'')ˣ) : L.B T'') * L.ρ b (τ T' : L.B T') = 1 := by
      have := (ρu b (τ T')).inv_mul
      simpa [ρu] using this
    have e3 : (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') * L.ρ b (L.ρ a (τ T : L.B T)) = 1 := by
      have := (ρu (a ≫ b) (τ T)).inv_mul
      rw [← hfun a b]
      simpa [ρu] using this
    have he : L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T')) = (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') := by
      linear_combination (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'') * e1 - (L.ρ b ((((ρu a (τ T))⁻¹ : (L.B T')ˣ) : L.B T'))) * e3
    simp only [Units.val_mul, map_mul]
    rw [he]
    linear_combination ((τ T'' : L.B T'') * L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') * (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'')) * e2 + ((τ T'' : L.B T'') * (((ρu (a ≫ b) (τ T))⁻¹ : (L.B T'')ˣ) : L.B T'')) * hzb

end GlobalTheory.LBObs
