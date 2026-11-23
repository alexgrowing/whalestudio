import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import Development.WeilBound.CoreStatements.PluriharmonicCharts.AdjoinLow
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.c_fm_exists_flags_chgbasis

variable {N : ℕ} {R R' : Type} [CommRing R] [CommRing R']

def Mn (M : Matrix (Fin N) (Fin N) R) : Prop :=
  ∀ (P : Fin N → Prop) (_ : DecidablePred P), (∀ a c, a ≤ c → P c → P a) →
    (M.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det ≠ 0

theorem Mn.of_map {M : Matrix (Fin N) (Fin N) R} (f : R →+* R') (h : Mn (M.map f)) : Mn M := fun P i hP h0 =>
  h P i hP (by rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])

theorem Mn.map {M : Matrix (Fin N) (Fin N) R} (f : R →+* R') (hf : Function.Injective f) (h : Mn M) :
    Mn (M.map f) := fun P i hP h0 => by
  rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h0
  exact h P i hP ((map_eq_zero_iff f hf).1 h0)

theorem Mn.lowerUni [Nontrivial R] {M : Matrix (Fin N) (Fin N) R} (h : IsLowerUni M) : Mn M := fun P _ _ => by
  rw [h.det_submatrix P]
  exact one_ne_zero

theorem Mn.mul [IsDomain R] {M B : Matrix (Fin N) (Fin N) R} (h : Mn M) (hB : B.BlockTriangular id)
    (hd : B.det ≠ 0) : Mn (M * B) := fun P i hP => by
  have e : (M * B).submatrix (Subtype.val : {a // P a} → Fin N) (Subtype.val : {a // P a} → Fin N) =
      M.submatrix (Subtype.val : {a // P a} → Fin N) (Subtype.val : {a // P a} → Fin N) *
        B.submatrix (Subtype.val : {a // P a} → Fin N) (Subtype.val : {a // P a} → Fin N) := by
    ext a b
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ P,
      Finset.sum_eq_zero (s := Finset.univ.filter fun c => ¬ P c) (fun c hc => by
        rw [hB (show b.1 < c from not_le.1 fun e => (Finset.mem_filter.1 hc).2 (hP _ _ e b.2)), mul_zero]), add_zero,
      Finset.sum_subtype (p := P) _ (by simp)]
    rfl
  rw [e, det_mul]
  refine mul_ne_zero (h P i hP) ?_
  rw [det_of_upperTriangular hB, Finset.prod_ne_zero_iff] at hd
  rw [det_of_upperTriangular (M := B.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val) fun a b e => hB e,
    Finset.prod_ne_zero_iff]
  exact fun a _ => hd _ (Finset.mem_univ _)

theorem Mn.upper {F : Type} [Field F] {M : Matrix (Fin N) (Fin N) F} (h : Mn M) :
    ∃ B, B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsLowerUni (M * B) := by
  have hb : IsBlockDiag 0 M := fun a b e => absurd (iff_of_true a.2 b.2) e
  obtain ⟨B, -, h1, h2⟩ := hb.exists_upper fun b =>
    (h _ _ fun a c hac hc => ⟨hac.trans hc.1, iff_of_true a.2 b.2⟩).isUnit
  refine ⟨B, h1, fun h0 => ?_, h2⟩
  have := h2.det
  rw [det_mul, h0, mul_zero] at this
  exact zero_ne_one this

theorem exists_low {Ω : Type} [Field Ω] (A : Matrix (Fin N) (Fin N) Ω) (hA : IsUnit A.det) :
    ∃ l : Matrix (Fin N) (Fin N) (FractionRing (Polynomial Ω)), IsLowerUni l ∧
      Mn (A.map (algebraMap Ω (FractionRing (Polynomial Ω))) * l) := by
  let t : Polynomial Ω := Polynomial.X
  let Z : Matrix (Fin N) (Fin N) (Polynomial Ω) := t • (A⁻¹).map Polynomial.C + (1 - t) • (1 : Matrix _ _ _)
  let f := algebraMap (Polynomial Ω) (FractionRing (Polynomial Ω))
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have h1 : Mn Z := by
    refine Mn.of_map (Polynomial.evalRingHom 0) ?_
    have : Z.map (Polynomial.evalRingHom 0) = 1 := by
      ext a b
      by_cases e : a = b <;> simp [Z, t, Matrix.one_apply, e]
    rw [this]
    exact Mn.lowerUni isLowerUni_one
  have h2 : Mn (A.map Polynomial.C * Z) := by
    refine Mn.of_map (Polynomial.evalRingHom 1) ?_
    have e1 : Z.map (Polynomial.evalRingHom 1) = A⁻¹ := by
      ext a b
      simp [Z, t]
    have e2 : (A.map Polynomial.C).map (Polynomial.evalRingHom 1) = A := by
      ext a b
      simp
    rw [Matrix.map_mul, e1, e2, Matrix.mul_nonsing_inv _ hA]
    exact Mn.lowerUni isLowerUni_one
  obtain ⟨B, hB, hd, hl⟩ := (h1.map f hf).upper
  refine ⟨_, hl, ?_⟩
  have := (h2.map f hf).mul hB hd
  rw [Matrix.map_mul, Matrix.mul_assoc] at this
  exact this

variable {S : Type} {r : S → ℕ}

noncomputable def gen (Ω : Type) [Field Ω] (r : S → ℕ) (s : S) : Matrix (Fin (r s)) (Fin (r s))
    (MvPolynomial (Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1}) Ω) := fun a b =>
  if h : b < a then MvPolynomial.X ⟨s, (a, b), h⟩ else if a = b then 1 else 0

theorem gen_map {Ω : Type} [Field Ω] [Algebra Ω R] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) R)
    (hu : ∀ s, IsLowerUni (u s)) (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (s : S) :
    ((A s).map MvPolynomial.C * gen Ω r s).map (MvPolynomial.aeval (R := Ω)
      (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2)).toRingHom =
      (A s).map (algebraMap Ω R) * u s := by
  rw [Matrix.map_mul]
  congr 1
  · ext a b
    exact MvPolynomial.aeval_C _ _
  · ext a b
    rw [Matrix.map_apply, gen]
    split_ifs with h e
    · exact MvPolynomial.aeval_X _ _
    · rw [map_one, e, (hu s).1]
    · rw [map_zero, (hu s).2 a b (lt_of_le_of_ne (not_lt.1 h) e)]

end PositivityTheory.Xgp.c_fm_exists_flags_chgbasis

open PositivityTheory.Xgp.c_fm_exists_flags_chgbasis in
theorem PositivityTheory.Xgp.t_c_fm_exists_flags_chgbasis : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω), IsGenFam Ω G u → (∀ s, IsUnit (A s).det) → ∃ u' B : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G, IsGenFam Ω G u' ∧ (∀ s, IsUnit (B s).det) ∧ (∀ s a b, b < a → B s a b = 0) ∧ ∀ s, (A s).map (algebraMap Ω G) * u s = u' s * B s := by
  intro Ω G _ _ _ S _ r u A hu hA
  have hL : ∀ s, IsLowerUni (u s) := fun s => ⟨hu.1 s, hu.2.1 s⟩
  choose l hl hm using fun s => exists_low (A s) (hA s)
  have h1 : ∀ s, Mn ((A s).map (algebraMap Ω G) * u s) := fun s => by
    rw [← gen_map u hL A s]
    refine Mn.map _ hu.2.2.1 ?_
    have := hm s
    rw [← gen_map l hl A s] at this
    exact this.of_map _
  choose B hB hd hl' using fun s => (h1 s).upper
  refine ⟨fun s => (A s).map (algebraMap Ω G) * u s * B s, fun s => (B s)⁻¹, ?_,
    fun s => Matrix.isUnit_nonsing_inv_det _ (hd s).isUnit, fun s a b h => ?_,
    fun s => (Matrix.mul_nonsing_inv_cancel_right _ _ (hd s).isUnit).symm⟩
  · refine PositivityTheory.Xgp.GenFam.of_gen hu (fun s => (hl' s).1) (fun s => (hl' s).2) fun s => ?_
    generalize hF : IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) =>
      ((A q.1).map (algebraMap Ω G) * u q.1 * B q.1) q.2.1 q.2.2) = F
    have hmem : ∀ a b, ((A s).map (algebraMap Ω G) * u s * B s) a b ∈ F := fun a b =>
      hF ▸ IntermediateField.subset_adjoin _ _ ⟨⟨s, a, b⟩, rfl⟩
    have e : u s * B s = (A s)⁻¹.map (algebraMap Ω G) * ((A s).map (algebraMap Ω G) * u s * B s) := by
      rw [Matrix.mul_assoc _ (u s), ← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (hA s),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    have hmem' : ∀ a b, (u s * B s) a b ∈ F := fun a b => by
      rw [e, Matrix.mul_apply]
      exact sum_mem fun c _ => mul_mem (F.algebraMap_mem _) (hmem c b)
    let X₁ : Matrix (Fin (r s)) (Fin (r s)) F := fun a b => ⟨(u s * B s) a b, hmem' a b⟩
    have eX : X₁.map (algebraMap F G) = u s * B s := rfl
    have hX : Mn X₁ := Mn.of_map (algebraMap F G) (eX ▸ (Mn.lowerUni (hL s)).mul (hB s) (hd s))
    obtain ⟨B₁, hB₁, -, hl₁⟩ := hX.upper
    have e₁ : (X₁ * B₁).map (algebraMap F G) = u s * (B s * B₁.map (algebraMap F G)) := by
      rw [Matrix.map_mul, eX, Matrix.mul_assoc]
    have h2 := hl₁.map (algebraMap F G)
    rw [e₁] at h2
    rw [(hL s).eq_one ((hB s).mul (hB₁.map _)) h2, Matrix.mul_one] at e₁
    intro a b
    rw [← e₁]
    exact ((X₁ * B₁) a b).2
  · letI := Matrix.invertibleOfIsUnitDet _ (hd s).isUnit
    exact blockTriangular_inv_of_blockTriangular (hB s) h
