import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOneAddPiOMul
import GroundTheory.LocalFields.FilteredSurj
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NormApproximationFirstLevel
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NormApproximationFiltration
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NormFiltrationComplete
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EqZeroOfMemAllPowers
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ConjugateSelfReciprocalCharpoly
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.CharpolyDvdOfAevalEqZero
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.NormEq

open GlobalTheory.UTr GroundTheory.LocalField

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem sigO_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : sigO σ h.2.1 (piO h) = piO h :=
  Subtype.ext h.2.2.1

theorem conj_mem_piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (m : ℕ)
    {a : Alg P} (ha : a ∈ piPow h P m) : conj P a ∈ piPow h P m := by
  unfold piPow at *
  rw [Ideal.mem_span_singleton] at *
  obtain ⟨b, rfl⟩ := ha
  exact ⟨conj P b, by rw [map_mul, map_pow, conj_algebraMap, sigO_piO]⟩

theorem normU_mem_filt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (m : ℕ)
    {g : (Alg P)ˣ} (hg : g ∈ filt h P m) : normU P g ∈ filt h P m := by
  rw [mem_filt] at *
  have hc : conj P (g : Alg P) - 1 ∈ piPow h P m := by
    have := conj_mem_piPow h P m hg
    rwa [map_sub, map_one] at this
  have e : ((normU P g : (Alg P)ˣ) : Alg P) - 1 = ((g : Alg P) - 1) * conj P (g : Alg P) + (conj P (g : Alg P) - 1) := by
    rw [val_normU]; ring
  rw [e]
  exact (piPow h P m).add_mem ((piPow h P m).mul_mem_right _ hg) hc

theorem div_mem_of_sub_mem {R : Type} [CommRing R] {I : Ideal R} {x u : Rˣ} (hx : (x : R) - u ∈ I) :
    ((x / u : Rˣ) : R) - 1 ∈ I := by
  have e : ((x / u : Rˣ) : R) - 1 = ((x : R) - u) * ((u⁻¹ : Rˣ) : R) := by
    rw [div_eq_mul_inv, Units.val_mul, sub_mul, Units.mul_inv]
  rw [e]; exact I.mul_mem_right _ hx

theorem normU_surj (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (hP : P.1.Separable)
    (x : (Alg P)ˣ) (hx : x ∈ plus P) : ∃ u : (Alg P)ˣ, normU P u = x := by
  have hs : ∀ b, sigO σ h.2.1 (sigO σ h.2.1 b) = b := fun b => Subtype.ext (h.1 b)
  let f : (Alg P)ˣ →* plus P := (normU P).codRestrict (plus P) (normU_mem_plus P hs)
  let E : ℕ → Subgroup (plus P) := fun m => (filt h P m).comap (plus P).subtype
  have hE : Antitone E := fun a b hab => Subgroup.comap_mono (filt_antitone h P hab)
  have hsepE : FiltrationSeparated E := by
    intro g hg
    have h0 : ((g : (Alg P)ˣ) : Alg P) - 1 = 0 := GlobalTheory.T.eq_zero_of_mem_all_powers L σ ϖ q h P _ fun m => hg m
    exact Subtype.ext (Units.ext (sub_eq_zero.1 h0))
  have hE0 : E (id 0) = ⊤ := by
    ext g; simp [E, filt_zero]
  have hmap : ∀ n, ∀ g ∈ filt h P n, f g ∈ E (id n) := fun n g hg => normU_mem_filt h P n hg
  have hgr : ∀ n, ∀ z ∈ E (id n), ∃ g ∈ filt h P n, z / f g ∈ E (id (n + 1)) := by
    intro n z hz
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨u, hu⟩ := GlobalTheory.T.norm_approximation_first_level L σ ϖ q h P hP z.1 z.2
      refine ⟨u, by rw [filt_zero]; exact Subgroup.mem_top u, ?_⟩
      show ((z.1 / normU P u : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P (0 + 1)
      exact div_mem_of_sub_mem hu
    · obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.norm_approximation_filtration L σ ϖ q h P n hn z.1 z.2 hz
      refine ⟨u, hu, ?_⟩
      show ((z.1 / normU P u : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P (n + 1)
      exact div_mem_of_sub_mem hu'
  obtain ⟨u, hu⟩ := surjective_of_graded_surjective (F := filt h P) (E := E) (filt_antitone h P) hE
    (GlobalTheory.T.norm_filtration_complete L σ ϖ q h P) hsepE f tendsto_id (filt_zero h P) hE0 hmap hgr ⟨x, hx⟩
  exact ⟨u, congrArg Subtype.val hu⟩

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq
open GlobalTheory.UTr

theorem hermUnit_eq_norm : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (y : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X]), (∀ i j, y i j ∈ intL L) → cT σ y * y = 1 → y.charpoly = Q₀.map (intL L).subtype → Q₀.Separable → ∀ t : GL (Fin n) L, (∀ i j, t.val i j ∈ intL L) → (∀ i j, (t⁻¹ : GL (Fin n) L).val i j ∈ intL L) → cT σ t.val = t.val → (∃ p : (intL L)[X], t.val = aeval y (p.map (intL L).subtype)) → ∃ s : GL (Fin n) L, s.val * y = y * s.val ∧ s.val * cT σ s.val = t.val := by
  intro L _ _ _ σ ϖ q h n y Q₀ hy hyu hch hsep t ht hti htc ⟨p, hp⟩
  let sO := sigO σ h.2.1
  let Φ : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L := (intL L).subtype.mapMatrix
  have hΦinj : Function.Injective Φ := fun a b hab => by
    ext i j; exact congrFun (congrFun hab i) j
  let yO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨y i j, hy i j⟩
  have hyO : Φ yO = y := rfl
  have hΦcT : ∀ M, Φ (cT sO M) = cT σ (Φ M) := fun M => rfl
  have hchO : yO.charpoly = Q₀ := by
    apply Polynomial.map_injective _ (intL L).subtype_injective
    rw [← hch, ← hyO]
    exact (Matrix.charpoly_map yO (intL L).subtype).symm
  have hyuO : cT sO yO * yO = 1 := hΦinj (by rw [map_mul, hΦcT, hyO, hyu, map_one])
  have hcsr : IsCsr sO Q₀ := hchO ▸ GlobalTheory.T.conjugate_self_reciprocal_charpoly _ sO n yO hyuO
  let P : Csr sO := ⟨Q₀, hcsr⟩
  have hg : aeval yO P.1 = 0 := by
    show aeval yO Q₀ = 0
    rw [← hchO]; exact Matrix.aeval_self_charpoly yO
  let ev := evalMat P yO hg
  have hev : ∀ r : (intL L)[X], ev (aeval (root P) r) = aeval yO r := fun r => by
    rw [← aeval_algHom_apply, evalMat_root]
  have hevinj : ∀ z, ev z = 0 → z = 0 := by
    intro z hz
    obtain ⟨r, rfl⟩ := exists_aeval_root P z
    rw [hev] at hz
    have hd := GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt (intL L) n yO r (hchO ▸ hsep) hz
    rw [hchO] at hd
    exact (aeval_root_eq_zero_iff P).2 hd
  have hevinj' : Function.Injective ev := (injective_iff_map_eq_zero ev).2 hevinj
  have hcomp : Φ.comp (algebraMap (intL L) (Matrix (Fin n) (Fin n) (intL L))) =
      (algebraMap L (Matrix (Fin n) (Fin n) L)).comp (intL L).subtype := by
    ext a i j
    simp only [RingHom.coe_comp, Function.comp_apply, Φ, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  have hΦaeval : ∀ r : (intL L)[X], Φ (aeval yO r) = aeval y (r.map (intL L).subtype) := by
    intro r
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, eval₂_map, hcomp, hyO]

  let tz : Alg P := aeval (root P) p
  let tO := ev tz
  have htO : Φ tO = t.val := by rw [show tO = aeval yO p from hev p, hΦaeval, hp]
  let tiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨(t⁻¹ : GL (Fin n) L).val i j, hti i j⟩
  have htiO : tO * tiO = 1 := hΦinj (by
    rw [map_mul, htO, map_one]; exact t.mul_inv)
  have hdet : IsUnit tO.det := isUnit_iff_exists_inv.2 ⟨tiO.det, by rw [← Matrix.det_mul, htiO, Matrix.det_one]⟩
  have hunit : IsUnit tz := by
    have h0 : aeval tz tO.charpoly = 0 := hevinj _ (by
      rw [← aeval_algHom_apply]; exact Matrix.aeval_self_charpoly tO)
    have hc0 : IsUnit (tO.charpoly.coeff 0) := by
      have := Matrix.det_eq_sign_charpoly_coeff tO
      rw [this] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    have e := congrArg (aeval tz) (X_mul_divX_add tO.charpoly)
    rw [h0, map_add, map_mul, aeval_X, aeval_C] at e
    have hu : IsUnit (tz * aeval tz tO.charpoly.divX) := by
      rw [eq_neg_of_add_eq_zero_left e]
      exact (hc0.map _).neg
    exact isUnit_of_mul_isUnit_left hu
  let T : (Alg P)ˣ := hunit.unit

  have hyuO' : yO * cT sO yO = 1 := mul_eq_one_comm.1 hyuO
  let gU : UJ sO (1 : Matrix (Fin n) (Fin n) (intL L)) :=
    ⟨⟨yO, cT sO yO, hyuO', hyuO⟩, by
      show cT sO yO * 1 * yO = 1
      rw [Matrix.mul_one, hyuO]⟩
  have hcT : ∀ z, cT sO (ev z) = ev (conj P z) := fun z => by
    have := cT_evalMat P gU hg z
    rwa [Matrix.mul_one, Matrix.one_mul] at this
  have htz : conj P tz = tz := hevinj' (by
    rw [← hcT]
    exact hΦinj (by rw [hΦcT, htO, htc]))
  have hT : T ∈ plus P := mem_plus.2 htz
  obtain ⟨u, hu⟩ := normU_surj L σ ϖ q h P hsep T hT
  let Ψ : Alg P →* Matrix (Fin n) (Fin n) L := (Φ.comp ev.toRingHom : Alg P →+* _)
  refine ⟨Units.map Ψ u, ?_, ?_⟩
  · show Φ (ev u) * y = y * Φ (ev u)
    rw [← hyO, ← map_mul, ← map_mul]
    congr 1
    rw [← evalMat_root P yO hg, ← map_mul, ← map_mul, mul_comm]
  · show Φ (ev u) * cT σ (Φ (ev u)) = t.val
    rw [← hΦcT, hcT, ← map_mul, ← map_mul, ← val_normU, hu, ← htO]
    rfl

end GlobalTheory.NormEq
