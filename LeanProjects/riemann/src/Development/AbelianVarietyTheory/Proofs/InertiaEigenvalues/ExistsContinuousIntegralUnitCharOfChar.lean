import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.ContCharUnitsOL

theorem norm_algHom_apply (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (x : ↥K.1) : ‖((τ₀ x : ↥LL.1) : Om l)‖ = ‖(x : Om l)‖ := by
  have h1 : minpoly ℚ_[l] ((τ₀ x : ↥LL.1) : Om l) = minpoly ℚ_[l] x :=
    minpoly.algHom_eq ((LL.1).val.comp τ₀) ((Subtype.val_injective).comp τ₀.toRingHom.injective) x
  have h2 : minpoly ℚ_[l] (x : Om l) = minpoly ℚ_[l] x :=
    minpoly.algHom_eq (K.1).val Subtype.val_injective x
  show spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

theorem continuous_algHom (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    Continuous (fun x : ↥K.1 => τ₀ x) := by
  refine AddMonoidHomClass.continuous_of_bound τ₀ 1 (fun x => ?_)
  show ‖((τ₀ x : ↥LL.1) : Om l)‖ ≤ 1 * ‖(x : Om l)‖
  rw [norm_algHom_apply, one_mul]

theorem norm_le_one (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : ↥(GK K) →* (↥(K0 K))ˣ)
    (hc : Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))) (g : ↥(GK K)) :
    ‖(((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
  obtain ⟨B, hB⟩ := (isCompact_univ (X := ↥(GK K))).exists_bound_of_continuousOn hc.continuousOn
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
  have hpow : (((c (g ^ n) : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l) = ((((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) ^ n := by
    simp [map_pow]
  have := hB (g ^ n) (Set.mem_univ _)
  rw [hpow, norm_pow] at this
  linarith

end GlobalTheory.ContCharUnitsOL

namespace GlobalTheory.ContCharUnitsOL

theorem exists_unit_char (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (c : ↥(GK K) →* (↥(K0 K))ˣ)
    (hc : Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))) :
    ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ,
      Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧
      ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) *
        τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  let ι : ↥(K0 K) →+* ↥K.1 := algebraMap ↥(K0 K) ↥K.1
  have hι : ∀ x : ↥(K0 K), ((ι x : ↥K.1) : Om l) = (x : Om l) := fun x => rfl
  let v : ↥(GK K) → ↥LL.1 := fun g => τ₀ (ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)))
  let w : ↥(GK K) → ↥LL.1 := fun g => τ₀ (ι ((c g : (↥(K0 K))ˣ) : ↥(K0 K)))
  have hw : ∀ g, w g ∈ OL LL := fun g => by
    rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
    show ‖((τ₀ _ : ↥LL.1) : Om l)‖ ≤ 1
    rw [norm_algHom_apply, hι]
    exact norm_le_one l K c hc g
  have hv : ∀ g, v g ∈ OL LL := fun g => by
    rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
    show ‖((τ₀ _ : ↥LL.1) : Om l)‖ ≤ 1
    rw [norm_algHom_apply, hι, ← map_inv]
    exact norm_le_one l K c hc g⁻¹
  have hvw : ∀ g, v g * w g = 1 := fun g => by
    show τ₀ (ι _) * τ₀ (ι _) = 1
    rw [← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, map_one]
  have hwv : ∀ g, w g * v g = 1 := fun g => by rw [mul_comm]; exact hvw g
  let χf : ↥(GK K) → (↥(OL LL))ˣ := fun g =>
    ⟨⟨v g, hv g⟩, ⟨w g, hw g⟩, Subtype.ext (hvw g), Subtype.ext (hwv g)⟩
  let χ : ↥(GK K) →* (↥(OL LL))ˣ :=
    { toFun := χf
      map_one' := by
        apply Units.ext; apply Subtype.ext
        show τ₀ (ι (((c 1)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) = 1
        rw [map_one, inv_one, Units.val_one, map_one, map_one]
      map_mul' := fun g h => by
        apply Units.ext; apply Subtype.ext
        show τ₀ (ι (((c (g * h))⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) =
          τ₀ (ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) * τ₀ (ι (((c h)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)))
        rw [map_mul, mul_inv, Units.val_mul, map_mul, map_mul] }
  refine ⟨χ, ?_, fun g => hvw g⟩
  show Continuous v
  have hne : ∀ g, (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l) ≠ 0 := fun g h => by
    have : ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 0 := Subtype.ext h
    exact (c g).ne_zero this
  have h1 : Continuous (fun g : ↥(GK K) => ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) := by
    refine continuous_induced_rng.2 ?_
    have : (fun g : ↥(GK K) => ((ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)) : ↥K.1) : Om l)) =
        fun g => ((((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))⁻¹ := by
      funext g; rw [hι, Units.val_inv_eq_inv_val]; rfl
    rw [Function.comp_def, this]
    exact hc.inv₀ hne
  exact (continuous_algHom l K LL τ₀).comp h1

end GlobalTheory.ContCharUnitsOL

theorem GlobalTheory.ContCharUnitsOL.main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ↥(GK K) →* (↥(K0 K))ˣ), Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) → ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  intro l _ K LL τ₀ c hc
  exact GlobalTheory.ContCharUnitsOL.exists_unit_char l K LL τ₀ c hc
