import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalOfFiniteSubringFractionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureOfFiniteMapIntegrallyClosedSubrinStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormallyUnramifiedDifferentialsSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegrallyClosedSectionsOfSmoothComplexStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

noncomputable section

namespace GlobalTheory.W1.SchFF

def eqv {A K σ : Type} [CommRing A] [CommRing K] [SetLike σ K] [SubringClass σ K] (g : A →+* K)
    (hg : Function.Injective g) (S : σ) (hS : ∀ y, y ∈ S ↔ ∃ f, g f = y) : A ≃+* S :=
  RingEquiv.ofBijective (g.codRestrict S fun f => (hS _).2 ⟨f, rfl⟩)
    ⟨fun a b h => hg (congrArg Subtype.val h), fun y => by
      obtain ⟨f, hf⟩ := (hS y).1 y.2
      exact ⟨f, Subtype.ext hf⟩⟩

@[simp] theorem eqv_coe {A K σ : Type} [CommRing A] [CommRing K] [SetLike σ K] [SubringClass σ K] (g : A →+* K)
    (hg : Function.Injective g) (S : σ) (hS : ∀ y, y ∈ S ↔ ∃ f, g f = y) (a : A) :
    ((eqv g hg S hS a : S) : K) = g a := rfl

theorem frac (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) (h : genericPoint X ∈ U) (x : X.functionField) :
    ∃ a b : Γ(X, U), (X.presheaf.germ U _ h).hom b ≠ 0 ∧ x * (X.presheaf.germ U _ h).hom b = (X.presheaf.germ U _ h).hom a := by
  haveI : Nonempty U := ⟨⟨_, h⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) x
  have hb' : algebraMap Γ(X, U) X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem finiteEtale_functionField : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z), c ≫ s = s' → IsFinite c → Etale c → ∀ (d : ℕ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] [i1 : Algebra ℂ Z.functionField] [i2 : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], i1 = ffAlg s → i2 = ffAlg s' → (∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (f : Γ(Z, U)), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom ((c.app U).hom f) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ U (genericPoint Z) hU).hom f)) → FiniteDimensional Z.functionField Y.functionField ∧ ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) (B : Subalgebra ℂ Z.functionField) (B' : Subalgebra ℂ Y.functionField), IsAffineOpen U → (∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y) → (∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y) → (∀ y ∈ B', IsIntegral B (y : Y.functionField)) ∧ (∀ x : Z.functionField, IsIntegral B x → x ∈ B) ∧ (∀ y : Y.functionField, IsIntegral B y → y ∈ B') ∧ (∀ v ∈ B', ∃ (m : ℕ) (b : Fin m → Y.functionField) (w : Fin m → Z.functionField), (∀ j, b j ∈ B' ∧ w j ∈ B) ∧ ι1 (D ℂ Y.functionField v) = ∑ j, b j • mapDR ℂ Z.functionField Y.functionField (ι1 (D ℂ Z.functionField (w j)))) := by
  intro Z Y _ _ s s' c hcs hfin het d _ _ i1 i2 _ _ h1 h2 hcomp
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  haveI : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  haveI := hfin
  haveI := het
  have hφ : ∀ (U : Z.Opens) (hU : genericPoint Z ∈ U) (hU' : genericPoint Y ∈ c ⁻¹ᵁ U) {σ σ' : Type}
      [SetLike σ Z.functionField] [SubringClass σ Z.functionField] [SetLike σ' Y.functionField] [SubringClass σ' Y.functionField]
      (B : σ) (B' : σ') (hB : ∀ y, y ∈ B ↔ ∃ f : Γ(Z, U), (Z.presheaf.germ U (genericPoint Z) hU).hom f = y)
      (hB' : ∀ y, y ∈ B' ↔ ∃ f : Γ(Y, c ⁻¹ᵁ U), (Y.presheaf.germ (c ⁻¹ᵁ U) (genericPoint Y) hU').hom f = y),
      IsAffineOpen U → ∃ φ : B →+* B', (∀ x : B, (φ x : Y.functionField) = algebraMap Z.functionField Y.functionField x) ∧
        φ.Finite ∧ φ.FormallyUnramified ∧ Nonempty (Γ(Z, U) ≃+* B) ∧ Nonempty (Γ(Y, c ⁻¹ᵁ U) ≃+* B') := by
    intro U hU hU' σ σ' _ _ _ _ B B' hB hB' hUa
    let eB := GlobalTheory.W1.SchFF.eqv _ (germ_injective_of_isIntegral Z _ hU) B hB
    let eB' := GlobalTheory.W1.SchFF.eqv _ (germ_injective_of_isIntegral Y _ hU') B' hB'
    refine ⟨eB'.toRingHom.comp ((c.app U).hom.comp eB.symm.toRingHom), fun x => ?_, ?_, ?_, ⟨eB⟩, ⟨eB'⟩⟩
    · obtain ⟨f, rfl⟩ := eB.surjective x
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
      exact (GlobalTheory.W1.SchFF.eqv_coe _ _ _ _ _).trans (hcomp U hU hU' f)
    · exact (RingHom.Finite.of_surjective _ eB'.surjective).comp
        ((c.finite_app U hUa).comp (RingHom.Finite.of_surjective _ eB.symm.surjective))
    · have he := HasRingHomProperty.appLE @Etale c het ⟨U, hUa⟩ ⟨c ⁻¹ᵁ U, hUa.preimage c⟩ le_rfl
      rw [Scheme.Hom.appLE_eq_app] at he
      exact ((RingHom.FormallyUnramified.of_surjective eB.symm.surjective).comp
        (RingHom.Etale.formallyUnramified _ he)).comp (RingHom.FormallyUnramified.of_surjective eB'.surjective)
  have hfr : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) {σ : Type}
      [SetLike σ X.functionField] [SubringClass σ X.functionField] (B : σ),
      (∀ y, y ∈ B ↔ ∃ f : Γ(X, U), (X.presheaf.germ U _ h).hom f = y) → IsAffineOpen U →
      ∀ x : X.functionField, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a := by
    intro X _ U h σ _ _ B hB hUa x
    obtain ⟨a, b, hb, e⟩ := GlobalTheory.W1.SchFF.frac X U hUa h x
    exact ⟨_, (hB _).2 ⟨a, rfl⟩, _, (hB _).2 ⟨b, rfl⟩, hb, e⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨U₀, hU₀, hm⟩ := GlobalTheory.QCoh.exists_affine_mem (c (genericPoint Y))
    have hU₀' : genericPoint Y ∈ c ⁻¹ᵁ U₀ := hm
    have hU₀g : genericPoint Z ∈ U₀ := GlobalTheory.VB.genericPoint_mem hm
    obtain ⟨φ, hφ1, hφ2, -, -, -⟩ := hφ U₀ hU₀g hU₀' (Z.presheaf.germ U₀ _ hU₀g).hom.range
      (Y.presheaf.germ _ _ hU₀').hom.range (fun y => RingHom.mem_range) (fun y => RingHom.mem_range) hU₀
    exact GlobalTheory.T.finiteDimensional_of_finite_subring_hom_of_fractions _ _ _ _ φ hφ1 hφ2 (hfr Y _ hU₀' _ (fun y => RingHom.mem_range) (hU₀.preimage c))
  · intro U hU hU' B B' hUa hB hB'
    obtain ⟨φ, hφ1, hφ2, hφ3, ⟨eB⟩, ⟨eB'⟩⟩ := hφ U hU hU' B B' hB hB' hUa
    haveI := GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' Z s U hUa hU
    haveI := GlobalTheory.T.isIntegrallyClosed_sections_of_smooth_complex' Y s' (c ⁻¹ᵁ U) (hUa.preimage c) hU'
    haveI : IsIntegrallyClosed B := IsIntegrallyClosed.of_equiv eB
    haveI : IsIntegrallyClosed B' := IsIntegrallyClosed.of_equiv eB'
    obtain ⟨r1, r2, r3⟩ := GlobalTheory.T.integralClosure_of_finite_map_integrallyClosed_subrings ℂ _ _ B B' φ hφ1 hφ2 inferInstance inferInstance (hfr Z U hU B hB hUa)
      (hfr Y _ hU' B' hB' (hUa.preimage c))
    exact ⟨r1, r2, r3, GlobalTheory.T.formally_unramified_differentials_span ℂ _ _ B B' φ hφ1 hφ3⟩

end GlobalTheory.W1.SchFF

end
