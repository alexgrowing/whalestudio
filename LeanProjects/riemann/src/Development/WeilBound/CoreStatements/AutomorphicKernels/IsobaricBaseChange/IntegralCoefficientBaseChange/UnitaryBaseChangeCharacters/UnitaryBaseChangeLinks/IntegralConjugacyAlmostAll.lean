import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.SeparableIntegralModelAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjOfCharpolyLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingExistsAevalOfCommuteSeparableStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralUnitaryConjugacyLatticeStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntUniq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

instance instLocalIntL : IsLocalRing (intL L) :=
  inferInstanceAs (IsLocalRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)

theorem mul_int {n : ℕ} {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L)
    (hB : ∀ i j, B i j ∈ intL L) : ∀ i j, (A * B) i j ∈ intL L := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem cT_int {σ : L →+* L} (hv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ intL L) : ∀ i j, cT σ A i j ∈ intL L := fun i j => by
  have h := hA j i
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [intL, Valuation.mem_integer_iff] at h ⊢
  rw [hv]; exact h

theorem cT_cT {σ : L →+* L} (hs : ∀ x, σ (σ x) = x) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) : cT σ (cT σ A) = A := by
  ext i j; simp [cT, hs]

theorem locConj [CompleteSpace L] {σ : L →+* L} {ϖ : L} {q : ℕ} (hσ : IsUnramInv ϖ σ q) {n : ℕ}
    (Y Y' : GL (Fin n) (intL L)) (hu : bc (intL L).subtype Y ∈ UJ σ 1) (hu' : bc (intL L).subtype Y' ∈ UJ σ 1)
    (hc : Y.val.charpoly = Y'.val.charpoly) (hs : Y.val.charpoly.Separable) :
    ∃ g ∈ UJ σ 1, bc (intL L).subtype Y' = g⁻¹ * bc (intL L).subtype Y * g := by
  set φ := (intL L).subtype with hφ
  have hv := hσ.2.1
  have hinv := hσ.1
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_conj_of_charpoly_eq_of_separable_local (intL L) n Y.val Y'.val hc hs
  have hk' : Y' = k⁻¹ * Y * k := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hk)
  set g : GL (Fin n) L := bc φ k with hg
  set y := bc φ Y with hydef
  set y' := bc φ Y' with hy'def
  have hyy : y' = g⁻¹ * y * g := by rw [hy'def, hk', map_mul, map_mul, map_inv]
  set G := g.val with hG
  set Gi := (g⁻¹ : GL (Fin n) L).val with hGi
  set ym := y.val with hym
  set ym' := y'.val with hym'
  have hGGi : G * Gi = 1 := g.mul_inv
  have hGiG : Gi * G = 1 := g.inv_mul
  have hGI : ∀ i j, G i j ∈ intL L := fun i j => (k.val i j).2
  have hGiI : ∀ i j, Gi i j ∈ intL L := fun i j => by
    have : Gi = (bc φ k⁻¹).val := by rw [map_inv]
    rw [this]; exact ((k⁻¹ : GL (Fin n) (intL L)).val i j).2
  have hyI : ∀ i j, ym i j ∈ intL L := fun i j => (Y.val i j).2
  have hyU : cT σ ym * ym = 1 := by
    have h1 : cT σ ym * 1 * ym = 1 := hu
    rwa [Matrix.mul_one] at h1
  have hyU' : cT σ ym' * ym' = 1 := by
    have h1 : cT σ ym' * 1 * ym' = 1 := hu'
    rwa [Matrix.mul_one] at h1
  have hyU'2 : ym' * cT σ ym' = 1 := mul_eq_one_comm.1 hyU'
  have hy'm : ym' = Gi * ym * G := by rw [hym', hyy, Units.val_mul, Units.val_mul]
  have hGy : G * ym' = ym * G := by
    rw [hy'm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGGi, Matrix.one_mul]
  have hGs : cT σ G * ym = ym' * cT σ G := by
    have h1 : cT σ ym' * cT σ G = cT σ G * cT σ ym := by rw [← cT_mul, ← cT_mul, hGy]
    calc cT σ G * ym = (ym' * cT σ ym') * cT σ G * ym := by rw [hyU'2, Matrix.one_mul]
      _ = ym' * (cT σ ym' * cT σ G) * ym := by simp only [Matrix.mul_assoc]
      _ = ym' * cT σ G * (cT σ ym * ym) := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = ym' * cT σ G := by rw [hyU, Matrix.mul_one]
  set T := G * cT σ G with hT
  have hT1 : T * (cT σ Gi * Gi) = 1 := by
    calc T * (cT σ Gi * Gi) = G * (cT σ G * cT σ Gi) * Gi := by simp only [hT, Matrix.mul_assoc]
      _ = 1 := by rw [← cT_mul, hGiG, cT_one, Matrix.mul_one, hGGi]
  let tU : GL (Fin n) L := ⟨T, cT σ Gi * Gi, hT1, mul_eq_one_comm.1 hT1⟩
  have hTI : ∀ i j, T i j ∈ intL L := mul_int hGI (cT_int hv hGI)
  have htiI : ∀ i j, (tU⁻¹ : GL (Fin n) L).val i j ∈ intL L := mul_int (cT_int hv hGiI) hGiI
  have hTfix : cT σ T = T := by rw [hT, cT_mul, cT_cT hinv]
  have hTy : T * ym = ym * T := by
    rw [hT, Matrix.mul_assoc, hGs, ← Matrix.mul_assoc, hGy, Matrix.mul_assoc]
  let T₀ : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨T i j, hTI i j⟩
  have hT₀ : T₀.map φ = T := by ext i j; rfl
  have hYm : Y.val.map φ = ym := rfl
  have hT₀c : T₀ * Y.val = Y.val * T₀ := by
    apply Matrix.map_injective (f := φ) Subtype.val_injective
    show (T₀ * Y.val).map φ = (Y.val * T₀).map φ
    rw [Matrix.map_mul, Matrix.map_mul, hT₀, hYm, hTy]
  obtain ⟨p, hp⟩ := GlobalTheory.T.localRing_exists_aeval_of_commute_separable (intL L) n Y.val T₀ hs hT₀c
  have hTp : tU.val = aeval ym (p.map φ) := by
    change T = _
    rw [← hT₀, hp, ← hYm, GlobalTheory.UTr.aeval_map_map]
  have hch : ym.charpoly = Y.val.charpoly.map φ := by rw [← hYm, Matrix.charpoly_map]
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.T.exists_commute_mul_cT_eq_of_integral_hermitian_polynomial L σ ϖ q hσ n ym Y.val.charpoly hyI hyU hch hs tU hTI htiI hTfix ⟨p, hTp⟩
  refine ⟨s⁻¹ * g, ?_, ?_⟩
  · set S := s.val
    set Si := (s⁻¹ : GL (Fin n) L).val
    have hSiS : Si * S = 1 := s.inv_mul
    have hh : (Si * G) * cT σ (Si * G) = 1 := by
      calc (Si * G) * cT σ (Si * G) = Si * T * cT σ Si := by rw [cT_mul]; simp only [hT, Matrix.mul_assoc]
        _ = Si * (S * cT σ S) * cT σ Si := by rw [← show S * cT σ S = T from hs2]
        _ = cT σ (Si * S) := by rw [cT_mul, ← Matrix.mul_assoc Si S, hSiS, Matrix.one_mul]
        _ = 1 := by rw [hSiS, cT_one]
    show cT σ (s⁻¹ * g).val * 1 * (s⁻¹ * g).val = 1
    rw [Matrix.mul_one, Units.val_mul]
    exact mul_eq_one_comm.1 hh
  · have hsy : s * y = y * s := Units.ext hs1
    calc y' = g⁻¹ * (s * y * s⁻¹) * g := by rw [hsy, mul_inv_cancel_right, hyy]
      _ = (s⁻¹ * g)⁻¹ * y * (s⁻¹ * g) := by group

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n → ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ y y' : UL n w, y ∈ KL n w → y' ∈ KL n w → y.1.val.charpoly = atPl w P → y'.1.val.charpoly = atPl w P → ∃ g : UL n w, y' = g⁻¹ * y * g := by
  intro E _ _ _ hU n P hP
  have hPs : P.Separable := hP.2.2.1
  filter_upwards [GlobalTheory.T.separable_integral_model_almost_all E P hPs] with w ⟨Q₀, hQs, hQ⟩
  intro y y' hy hy' hc hc'
  by_cases hsp : IsSplitAt w
  · have hsep : y.1.val.charpoly.Separable := by rw [hc]; exact hPs.map
    obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.conj_of_charpoly y.1 y'.1 hsep (hc.trans hc'.symm)
    refine ⟨⟨g, by simp [UL, hsp]⟩, Subtype.ext ?_⟩
    rw [hg]; rfl
  · obtain ⟨ϖ, q, hq, -⟩ := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hsp).2.1
    rw [KL, Subgroup.mem_subgroupOf] at hy hy'
    obtain ⟨Y, hY⟩ := hy
    obtain ⟨Y', hY'⟩ := hy'
    have hcp : ∀ (Z : GL (Fin n) (intL (w.adicCompletion E))) (z : UL n w), bc (intL _).subtype Z = z.1 →
        z.1.val.charpoly = atPl w P → Z.val.charpoly = Q₀ := by
      intro Z z hZ hz
      apply Polynomial.map_injective _ (intL (w.adicCompletion E)).subtype_injective
      rw [← Matrix.charpoly_map, hQ]
      change (bc (intL _).subtype Z).val.charpoly = _
      rw [hZ, hz]
    have hYc := hcp Y y hY hc
    have hY'c := hcp Y' y' hY' hc'
    have hmemU : ∀ z : UL n w, z.1 ∈ UJ (cj w) 1 := fun z => by
      have := z.2
      simpa [UL, hsp] using this
    obtain ⟨g, hgU, hgeq⟩ := locConj hq Y Y' (hY ▸ hmemU y) (hY' ▸ hmemU y') (hYc.trans hY'c.symm)
      (hYc ▸ hQs)
    refine ⟨⟨g, by simpa [UL, hsp] using hgU⟩, Subtype.ext ?_⟩
    show y'.1 = g⁻¹ * y.1 * g
    rw [← hY, ← hY']
    exact hgeq

end GlobalTheory.IntUniq
