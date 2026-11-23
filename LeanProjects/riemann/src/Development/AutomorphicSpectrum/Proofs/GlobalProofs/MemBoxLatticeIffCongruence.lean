import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemConjSub
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDet
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex.OnePlus

theorem nrm_det_one_add {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (hLF : LF O ϖ nrm q) {n : ℕ} {x : Matrix (Fin n) (Fin n) F}
    (hx : ∀ a b, ∃ o ∈ O, x a b = ϖ * o) : nrm (1 + x).det = 1 := by
  obtain ⟨-, hϖ, hle, hlt, -, -, -⟩ := GlobalTheory.CompanionTheory.QL.NormalisedValue.main hLF
  choose f hf hf' using hx
  let ϖ' : O := ⟨ϖ, hϖ⟩
  let y : Matrix (Fin n) (Fin n) O := fun a b => ⟨f a b, hf a b⟩
  let M : Matrix (Fin n) (Fin n) O := 1 + ϖ' • y
  have hM : O.subtype.mapMatrix M = 1 + x := by
    ext a b
    by_cases hab : a = b
    · simp [M, y, ϖ', hf', hab]
      rfl
    · simp [M, y, ϖ', hf', hab, Matrix.one_apply]
      rfl
  let π := Ideal.Quotient.mk (Ideal.span {ϖ'})
  have hπ : π ϖ' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hred : π.mapMatrix M = 1 := by
    simp only [M, map_add, map_one]
    have : π.mapMatrix (ϖ' • y) = 0 := by
      ext a b
      simp [hπ]
    rw [this, add_zero]
  have hdet : π M.det = 1 := by
    rw [RingHom.map_det, hred, Matrix.det_one]
  have hmem : M.det - 1 ∈ Ideal.span {ϖ'} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
    exact sub_eq_zero.2 hdet
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have hcoe : (1 + x).det = (M.det : F) := by
    rw [← hM, ← RingHom.map_det]
    rfl
  have hEq : (1 + x).det = 1 + (a : F) * ϖ := by
    have h2 := congrArg (Subtype.val) ha
    have h3 : (a : F) * ϖ = (M.det : F) - 1 := by simpa [ϖ'] using h2
    rw [hcoe, h3]
    ring
  have hin : (1 + x).det ∈ O := by
    rw [hcoe]
    exact M.det.2
  refine le_antisymm ((hle _).2 hin) (not_lt.1 fun hl => ?_)
  obtain ⟨o, ho, e⟩ := (hlt _).1 hl
  have h1 : (1 : F) = ϖ * (o - a) := by
    have : (1 : F) + (a : F) * ϖ = ϖ * o := by rw [← hEq, e]
    linear_combination this
  have h2 : nrm (1 : F) < 1 := (hlt 1).2 ⟨o - a, O.sub_mem ho a.2, h1⟩
  simp at h2

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ x : Matrix (Fin n) (Fin n) F, x ∈ boxAdd O β (fun _ _ => ϖ ^ T) ↔ ∃ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + x := by
  intro F _ _ _ _ O ϖ nrm q hLF n β Q hQ T hT x
  obtain ⟨-, hϖ, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.QL.NormalisedValue.main hLF
  constructor
  · rintro ⟨hbt, hent⟩
    have hx' : ∀ a b, ∃ o ∈ O, x a b = ϖ * o := fun a b => by
      obtain ⟨o, ho, e⟩ := hent a b
      have e' : x a b = ϖ ^ T * o := e
      have hTT : ϖ ^ T = ϖ * ϖ ^ (T - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hT]
      refine ⟨ϖ ^ (T - 1) * o, O.mul_mem (O.pow_mem hϖ _) ho, ?_⟩
      rw [e', hTT, mul_assoc]
    have hdet := nrm_det_one_add hLF hx'
    have hne : (1 + x).det ≠ 0 := fun e => by
      rw [e] at hdet
      simp at hdet
    let g : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + x) hne
    have hg : (g : Matrix (Fin n) (Fin n) F) = 1 + x := rfl
    have hint : IsInt O (g : Matrix (Fin n) (Fin n) F) := fun a b => by
      rw [hg, Matrix.add_apply]
      obtain ⟨o, ho, e⟩ := hx' a b
      refine O.add_mem ?_ (e ▸ O.mul_mem hϖ ho)
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq]
        exact O.one_mem
      · rw [Matrix.one_apply_ne hab]
        exact O.zero_mem
    have hgQ : g ∈ Q := by
      rw [hQ, hg]
      intro i j hij
      have hne' : i ≠ j := fun e => by
        subst e
        exact lt_irrefl _ hij
      simp [hbt hij, hne']
    refine ⟨⟨g, hgQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff hLF n g).2 ⟨hint, hdet⟩, fun a b => ?_⟩
    obtain ⟨o, ho, e⟩ := hent a b
    refine ⟨o, ho, ?_⟩
    simpa [hg] using e
  · rintro ⟨p, hp, e⟩
    rw [Subgroup.mem_subgroupOf] at hp
    obtain ⟨-, hl⟩ := hp
    have hx : x = ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 := by
      rw [e]
      simp
    refine ⟨fun i j hij => ?_, fun a b => ?_⟩
    · have h0 := (hQ _).1 p.2 hij
      have hne' : i ≠ j := fun e => by
        subst e
        exact lt_irrefl _ hij
      simp [hx, h0, hne']
    · rw [hx]
      exact hl a b

end GlobalTheory.CompanionTheory.QL.QIndex.OnePlus
