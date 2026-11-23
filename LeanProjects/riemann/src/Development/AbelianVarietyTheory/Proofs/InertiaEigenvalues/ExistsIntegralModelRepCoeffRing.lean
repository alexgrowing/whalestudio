import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.IntegralModelOverCoeff

open scoped Matrix

theorem exists_integral_conj {l : ℕ} [Fact l.Prime] {O Γ : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]))
    (a : ℕ) (ρ : Γ →* GL (Fin a) (Qbar l))
    (hc : Continuous fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)))
    (hK : ∀ g s t, ∃ x, ι x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t) :
    ∃ (r : Γ →* GL (Fin a) O) (Pm : GL (Fin a) (Qbar l)),
      ∀ g, mapRep (ι.comp (algebraMap O (FractionRing O))) r g = Pm⁻¹ * ρ g * Pm := by
  classical
  set K := FractionRing O
  choose f hf using hK
  have hιi : Function.Injective (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro A B h
    ext s t
    exact ι.injective (congrFun (congrFun h s) t)
  have hM : ∀ g, ι.mapMatrix (Matrix.of (f g)) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := by
    intro g; ext s t; exact hf g s t
  let ρ0 : Γ →* Matrix (Fin a) (Fin a) K :=
    { toFun := fun g => Matrix.of (f g)
      map_one' := hιi (by rw [hM, map_one, map_one, Units.val_one])
      map_mul' := fun g h => hιi (by rw [map_mul, hM, hM, hM, map_mul, Units.val_mul]) }
  let ρK : Γ →* GL (Fin a) K := ρ0.toHomUnits
  have hρK : ∀ g, ι.mapMatrix ((ρK g : GL _ _) : Matrix (Fin a) (Fin a) K) =
      ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) := fun g => hM g

  let Int : Set (Matrix (Fin a) (Fin a) (Qbar l)) := {M | ∀ s t, ‖M s t‖ ≤ 1}
  have hInt1 : (1 : Matrix (Fin a) (Fin a) (Qbar l)) ∈ Int := by
    intro s t
    by_cases h : s = t
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hIntMul : ∀ A B, A ∈ Int → B ∈ Int → A * B ∈ Int := by
    intro A B hA hB s t
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hA s k) (norm_nonneg _) (hB k t)
  have hIntOpen : IsOpen Int := by
    have : Int = ⋂ s, ⋂ t, (fun M : Matrix (Fin a) (Fin a) (Qbar l) => M s t) ⁻¹' Metric.closedBall 0 1 := by
      ext M; simp [Int]
    rw [this]
    exact isOpen_iInter_of_finite fun s => isOpen_iInter_of_finite fun t =>
      (IsUltrametricDist.isOpen_closedBall 0 one_ne_zero).preimage (continuous_id.matrix_elem s t)
  let U : Subgroup Γ :=
    { carrier := {g | ((ρ g : GL _ _) : Matrix _ _ _) ∈ Int ∧ ((ρ g⁻¹ : GL _ _) : Matrix _ _ _) ∈ Int}
      one_mem' := by simp [hInt1]
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        refine ⟨?_, ?_⟩
        · rw [map_mul, Units.val_mul]; exact hIntMul _ _ hg1 hh1
        · rw [mul_inv_rev, map_mul, Units.val_mul]; exact hIntMul _ _ hh2 hg2
      inv_mem' := by
        rintro g ⟨h1, h2⟩
        exact ⟨h2, by rwa [inv_inv]⟩ }
  have hUopen : IsOpen (U : Set Γ) :=
    (hIntOpen.preimage hc).inter (hIntOpen.preimage (hc.comp continuous_inv))
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hUopen
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hUint : ∀ h ∈ U, ∀ i j, ((ρK h : GL _ _) : Matrix (Fin a) (Fin a) K) i j ∈ (algebraMap O K).range := by
    intro h hh i j
    rw [GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι]
    have := congrFun (congrFun (hρK h) i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this]
    exact hh.1 i j
  obtain ⟨P, hP⟩ := GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.exists_conj_integral (O := O) a ρK U hUint
  choose e he using hP
  have hai : Function.Injective ((algebraMap O K).mapMatrix :
      Matrix (Fin a) (Fin a) O →+* Matrix (Fin a) (Fin a) K) := by
    intro A B h
    ext s t
    exact IsFractionRing.injective O K (congrFun (congrFun h s) t)
  have hE : ∀ g, (algebraMap O K).mapMatrix (Matrix.of (e g)) =
      ((P * ρK g * P⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
    intro g; ext s t; exact he g s t
  let r0 : Γ →* Matrix (Fin a) (Fin a) O :=
    { toFun := fun g => Matrix.of (e g)
      map_one' := hai (by rw [hE, map_one, map_one, mul_one, mul_inv_cancel, Units.val_one])
      map_mul' := fun g h => hai (by
        rw [map_mul, hE, hE, hE, ← Units.val_mul, map_mul]
        congr 1
        group) }
  refine ⟨r0.toHomUnits, (Units.map (ι.mapMatrix : Matrix (Fin a) (Fin a) K →+* _).toMonoidHom P)⁻¹, fun g => ?_⟩
  ext1
  rw [inv_inv]
  show (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) = _
  have : (ι.comp (algebraMap O K)).mapMatrix (Matrix.of (e g)) =
      ι.mapMatrix ((algebraMap O K).mapMatrix (Matrix.of (e g))) := by
    ext s t; rfl
  rw [this, hE, Units.val_mul, Units.val_mul, map_mul, map_mul, hρK]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [Units.coe_map_inv]
  rfl

end GlobalTheory.IntegralModelOverCoeff

namespace GlobalTheory.IntegralModelOverCoeff

open Formalism.MainNotions.SumRepresentations

theorem exists_integral_model_rep : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) (a : ℕ) (ρ : GE N →* GL (Fin a) (Qbar (N.l i))), SumRepresentations.At.ContQ N i ρ → (∀ g s t, ∃ x, A.iotaQ i x = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar (N.l i))) s t) → ∃ (r : GE N →* GL (Fin a) (N.O i)) (Pm : GL (Fin a) (Qbar (N.l i))), ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm := by
  intro R H what₂ N A i a ρ hc hK
  exact exists_integral_conj (A.iotaQ i) (A.iotaQ_alg i) a ρ hc hK

end GlobalTheory.IntegralModelOverCoeff
