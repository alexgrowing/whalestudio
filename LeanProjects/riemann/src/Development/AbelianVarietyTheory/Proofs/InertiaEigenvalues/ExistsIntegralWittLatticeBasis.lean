import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.SatLattice

section abstract

variable {R : Type} [CommRing R] [IsDomain R] {π : R} (O : Subring R)

theorem pid_of_fact (hπ : Irreducible π) (hO : π ∈ O)
    (h4 : ∀ w ∈ O, w ≠ 0 → ∃ (k : ℕ) (v v' : R), v ∈ O ∧ v' ∈ O ∧ v * v' = 1 ∧ w = π ^ k * v) :
    IsPrincipalIdealRing O := by
  have hu : ∀ a : O, IsUnit (a : R) → IsUnit a := by
    intro a ha
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 a a.2 ha.ne_zero
    rcases k with _ | k
    · refine IsUnit.of_mul_eq_one (⟨v', hv'⟩ : O) (Subtype.ext ?_)
      simp [h2, h1]
    · exfalso
      rw [h2, pow_succ', mul_assoc] at ha
      exact hπ.not_isUnit (isUnit_of_mul_isUnit_left ha)
  have hirr : Irreducible (⟨π, hO⟩ : O) := by
    refine ⟨fun h => hπ.not_isUnit (h.map O.subtype), fun a b hab => ?_⟩
    exact (hπ.isUnit_or_isUnit (congrArg Subtype.val hab)).imp (hu a) (hu b)
  have : IsDiscreteValuationRing O := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, ?_⟩
    intro x hx
    obtain ⟨k, v, v', hv, hv', h1, h2⟩ := h4 x x.2 (fun h => hx (Subtype.ext h))
    refine ⟨k, ⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext h1, Subtype.ext (by simp [mul_comm v' v, h1])⟩, Subtype.ext ?_⟩
    simp [h2]
  infer_instance

theorem sat_pow (hπ : π ≠ 0) (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) (n : ℕ) (x : R)
    (hx : π ^ n * x ∈ O) : x ∈ O := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    obtain ⟨v, hv, h⟩ := h1 _ hx ⟨π ^ n * x, by ring⟩
    refine ih ?_
    have : π ^ n * x = v := mul_left_cancel₀ hπ (by rw [← h]; ring)
    rwa [this]

def divSub {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) : Submodule O (Fin d → O) where
  carrier := {x | ∀ i, a ∣ (Y *ᵥ fun j => (x j : R)) i}
  zero_mem' i := by
    simp [Matrix.mulVec, dotProduct]
  add_mem' {x y} hx hy i := by
    have : (fun j => ((x + y) j : R)) = (fun j => (x j : R)) + fun j => (y j : R) := rfl
    rw [this, Matrix.mulVec_add]
    exact dvd_add (hx i) (hy i)
  smul_mem' c x hx i := by
    have : (fun j => ((c • x) j : R)) = (c : R) • fun j => (x j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.dvd.mul_left (hx i) _

theorem exists_basis_matrix [IsPrincipalIdealRing O] {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (a : R) (ha : a ≠ 0)
    (haO : a ∈ O) :
    ∃ P : Matrix (Fin d) (Fin d) R, (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ (∀ i j, a ∣ (Y * P) i j) ∧
      ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
  set N := divSub O Y a with hN
  have hmem : ∀ v : Fin d → O, (⟨a, haO⟩ : O) • v ∈ N := by
    intro v i
    have : (fun j => (((⟨a, haO⟩ : O) • v) j : R)) = a • fun j => (v j : R) := rfl
    rw [this, Matrix.mulVec_smul]
    exact Dvd.intro _ rfl
  let f : (Fin d → O) →ₗ[O] N := LinearMap.codRestrict N ((⟨a, haO⟩ : O) • LinearMap.id) hmem
  have hf : Function.Injective f := by
    intro v w h
    funext i
    have := congrArg (fun z : N => ((z.1 i : O) : R)) h
    exact Subtype.ext (mul_left_cancel₀ ha this)
  have hr : Module.finrank O N = d := by
    apply le_antisymm
    · simpa using N.finrank_le
    · simpa using LinearMap.finrank_le_finrank_of_injective hf
  let b := Module.finBasisOfFinrankEq O N hr
  let P : Matrix (Fin d) (Fin d) R := Matrix.of fun i j => ((b j).1 i : R)
  have hspan : ∀ x : Fin d → R, (∀ i, x i ∈ O) → (∀ i, a ∣ (Y *ᵥ x) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ x = P *ᵥ w := by
    intro x hx hd
    let z : N := ⟨fun i => ⟨x i, hx i⟩, hd⟩
    refine ⟨fun j => (b.repr z j : R), fun j => (b.repr z j).2, funext fun i => ?_⟩
    have := congrArg (fun z : N => ((z.1 i : O) : R)) (b.sum_repr z)
    refine Eq.trans this.symm ?_
    rw [Submodule.coe_sum, Finset.sum_apply, AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  refine ⟨P, fun i j => ((b j).1 i).2, ?_, fun i j => (b j).2 i, hspan⟩
  have hcol : ∀ j : Fin d, ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ a • (Pi.single j 1 : Fin d → R) = P *ᵥ w := by
    intro j
    refine hspan _ (fun i => ?_) (fun i => ?_)
    · by_cases h : i = j
      · simp [h, haO]
      · simp [h]
    · rw [Matrix.mulVec_smul]
      exact Dvd.intro _ rfl
  choose w _ hw using hcol
  have hPQ : P * Matrix.of (fun i j => w j i) = a • (1 : Matrix (Fin d) (Fin d) R) := by
    ext i j
    have := congrFun (hw j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.single_apply] at this
    simp [Matrix.mul_apply, ← this, Matrix.one_apply]
  intro h0
  have := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ ha this.symm

theorem lattice_abstract [IsPrincipalIdealRing O] (hπ : π ≠ 0) (hO : π ∈ O)
    (h1 : ∀ w ∈ O, π ∣ w → ∃ v ∈ O, w = π * v) {d : ℕ} (Y : Matrix (Fin d) (Fin d) R) (c : ℕ) (u : Rˣ)
    (hdet : Y.det = π ^ c * u) :
    ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) R), (∀ i j, P i j ∈ O) ∧ P.det ≠ 0 ∧ π ^ m • Y' = Y * P ∧
      (∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ m • v = π ^ n • (P *ᵥ w)) ∧
      ∀ w : Fin d → R, (∀ i, w i ∈ O) → (∀ i, π ∣ (Y' *ᵥ w) i) → ∀ i, π ∣ w i := by
  obtain ⟨P, hPO, hP, hdv, hspan⟩ := exists_basis_matrix O Y (π ^ c) (pow_ne_zero _ hπ) (O.pow_mem hO c)
  choose y hy using hdv
  have hY' : π ^ c • Matrix.of y = Y * P := by
    ext i j
    simp [hy]
  have key : ∀ v : Fin d → R, (∀ i, v i ∈ O) → ∀ n : ℕ, (∀ i, π ^ n ∣ (Y *ᵥ v) i) →
        ∃ w : Fin d → R, (∀ i, w i ∈ O) ∧ π ^ c • v = π ^ n • (P *ᵥ w) := by
    intro v hv n hn
    choose z hz using hn
    have hz' : Y *ᵥ v = π ^ n • z := funext hz
    let x : Fin d → R := ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ z)
    have hx : π ^ c • v = π ^ n • x := by
      have h := congrArg (fun t => ((u⁻¹ : Rˣ) : R) • (Y.adjugate *ᵥ t)) hz'
      simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet] at h
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one, smul_comm] at h
      exact h
    have hYx : Y *ᵥ x = π ^ c • z := by
      simp only [x, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.mulVec_smul, Matrix.smul_mulVec,
        Matrix.one_mulVec, hdet]
      rw [smul_smul, mul_left_comm, Units.inv_mul, mul_one]
    obtain ⟨w, hw, hxw⟩ := hspan x (fun i => sat_pow O hπ h1 n _ (by
      have := congrFun hx i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      exact O.mul_mem (O.pow_mem hO c) (hv i))) (fun i => by rw [hYx]; exact Dvd.intro _ rfl)
    exact ⟨w, hw, by rw [hx, hxw]⟩
  refine ⟨c, P, Matrix.of y, hPO, hP, hY', key, fun w hw hd => ?_⟩
  obtain ⟨w', -, h⟩ := key (P *ᵥ w) (fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact O.sum_mem fun j _ => O.mul_mem (hPO i j) (hw j)) (c + 1) (fun i => by
    rw [Matrix.mulVec_mulVec, ← hY', Matrix.smul_mulVec, pow_succ]
    exact mul_dvd_mul_left _ (hd i))
  have h2 : P *ᵥ (w - π • w') = 0 := by
    funext i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    refine mul_left_cancel₀ (pow_ne_zero c hπ) ?_
    linear_combination this
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hP h2
  intro i
  exact ⟨w' i, sub_eq_zero.1 (congrFun h3 i)⟩

end abstract

theorem exists_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (Y1 : Matrix (Fin d) (Fin d) (WCb l)), Y1.det ≠ 0 → ∃ (m : ℕ) (P Y' : Matrix (Fin d) (Fin d) (WCb l)), (∀ i j, P i j ∈ bk.OE) ∧ P.det ≠ 0 ∧ (l : WCb l) ^ m • Y' = Y1 * P ∧ (∀ v : Fin d → WCb l, (∀ i, v i ∈ bk.OE) → ∀ n : ℕ, (∀ i, (l : WCb l) ^ n ∣ (Y1 *ᵥ v) i) → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (l : WCb l) ^ m • v = (l : WCb l) ^ n • (P *ᵥ w)) ∧ ∀ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) → (∀ i, (l : WCb l) ∣ (Y' *ᵥ w) i) → ∀ i, (l : WCb l) ∣ w i := by
  intro l _ K bk d Y1 hY
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  have hirr : Irreducible (l : WCb l) := WittVector.irreducible l
  have : PerfectRing (Cb l) l := by
    refine PerfectRing.ofSurjective _ l fun x => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
    obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
    obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
    exact ⟨algebraMap (OCb l) (Cb l) a' / algebraMap (OCb l) (Cb l) b', by
      simp [frobenius_def, div_pow, map_pow]⟩
  obtain ⟨c, u, hu⟩ := WittVector.exists_eq_pow_p_mul' Y1.det hY
  have := pid_of_fact bk.OE hirr (natCast_mem _ l) h4
  exact lattice_abstract bk.OE hirr.ne_zero (natCast_mem _ l) h1 Y1 c u hu

end GlobalTheory.SatLattice
