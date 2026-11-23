import Mathlib
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

noncomputable section
namespace GlobalTheory.ClassCover

variable {L : Type} [Field L] [NumberField L]

def toIdeles : (FiniteAdeleRing (𝓞 L) L)ˣ →* Neutral.B1.Ideles L :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem eq_diag_mul_of_classOf (y : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf L (toIdeles y) = 1) :
    ∃ (k : Lˣ) (u : (FiniteAdeleRing (𝓞 L) L)ˣ),
      (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((u : FiniteAdeleRing (𝓞 L) L) P) = 1) ∧
      y = Units.map (algebraMap L (FiniteAdeleRing (𝓞 L) L)).toMonoidHom k * u := by
  obtain ⟨k, u, hu, he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L _).1 hc
  refine ⟨k, ⟨(u : AdeleRing (𝓞 L) L).2, ((u⁻¹ : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2, ?_, ?_⟩,
    fun P => (hu.2 P).1, ?_⟩
  · exact congrArg Prod.snd u.mul_inv
  · exact congrArg Prod.snd u.inv_mul
  · apply Units.ext
    have h2 : ((toIdeles y : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 =
        ((Neutral.B1.diagUnits L k * u : Neutral.B1.Ideles L) : AdeleRing (𝓞 L) L).2 := by rw [he]
    exact h2

theorem eq_ratId_mul_of_classOf (ι : AfE ℚ L ≃+* FiniteAdeleRing (𝓞 L) L) (hι : GlobalTheory.TwU.IsAdIso ι) (x : (AfE ℚ L)ˣ)
    (hc : ReciprocityTheory.Neutral.Bridge.HCFR.classOf L (toIdeles (Units.map ι.toRingHom.toMonoidHom x)) = 1) :
    ∃ (a : Lˣ) (k : (AfE ℚ L)ˣ), k ∈ intU ℚ L ∧ x = ratId ℚ L a * k := by
  obtain ⟨h1, h2⟩ := hι
  obtain ⟨a, u, hu, he⟩ := eq_diag_mul_of_classOf _ hc
  have hinv : ∀ P : HeightOneSpectrum (𝓞 L), Valued.v (((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) P) = 1 := by
    intro P
    have e : (((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) P) * ((u : FiniteAdeleRing (𝓞 L) L) P) = 1 := by
      exact congrArg (fun t : FiniteAdeleRing (𝓞 L) L => t P) (Units.inv_mul u)
    have e2 := congrArg Valued.v e
    rw [map_mul, hu P, mul_one, map_one] at e2
    exact e2
  refine ⟨a, Units.map ι.symm.toRingHom.toMonoidHom u, ?_, ?_⟩
  · rw [intU, Submonoid.mem_units_iff]
    constructor
    · show ι.symm (u : FiniteAdeleRing (𝓞 L) L) ∈ RInt ℚ L
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hu P]
    · show ι.symm ((u⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) ∈ RInt ℚ L
      rw [h2]
      intro P
      rw [RingEquiv.apply_symm_apply, hinv P]
  · apply Units.ext
    apply ι.injective
    have e := congrArg (fun t : (FiniteAdeleRing (𝓞 L) L)ˣ => (t : FiniteAdeleRing (𝓞 L) L)) he
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at e
    rw [e, Units.val_mul, map_mul]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply]
    congr 1
    rw [ratId, Units.coe_map]
    show _ = ι (inclE (F := ℚ) (E := L) (FiniteAdeleRing (𝓞 ℚ) ℚ) (a : L))
    rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, h1]

theorem exists_finset_cover : ∀ (L : Type) [Field L] [NumberField L],
    ∃ S : Finset (AfE ℚ L)ˣ, ∀ x : (AfE ℚ L)ˣ, ∃ s ∈ S, ∃ a : Lˣ, ∃ k ∈ intU ℚ L, x = s * ratId ℚ L a * k := by
  intro L _ _
  classical
  obtain ⟨ι, hι⟩ := GlobalTheory.TwU.exists_isAdIso ℚ L
  let ψ : (AfE ℚ L)ˣ →* ClassGroup (𝓞 L) :=
    (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).comp (toIdeles.comp (Units.map ι.toRingHom.toMonoidHom))
  let sel : ClassGroup (𝓞 L) → (AfE ℚ L)ˣ := fun c => if h : ∃ y, ψ y = c then h.choose else 1
  have hsel : ∀ x, ψ (sel (ψ x)) = ψ x := by
    intro x
    have h : ∃ y, ψ y = ψ x := ⟨x, rfl⟩
    simp only [sel, dif_pos h]
    exact h.choose_spec
  refine ⟨Finset.univ.image sel, fun x => ⟨sel (ψ x), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩⟩
  have hk : ψ ((sel (ψ x))⁻¹ * x) = 1 := by rw [map_mul, map_inv, hsel, inv_mul_cancel]
  obtain ⟨a, k, hk, he⟩ := eq_ratId_mul_of_classOf ι hι _ hk
  refine ⟨a, k, hk, ?_⟩
  rw [mul_assoc, ← he, mul_inv_cancel_left]

end GlobalTheory.ClassCover
