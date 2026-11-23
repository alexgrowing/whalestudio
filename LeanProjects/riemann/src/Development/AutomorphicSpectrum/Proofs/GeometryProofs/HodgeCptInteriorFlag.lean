import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.GrNorm
open scoped ComplexOrder Matrix

section Alg

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem exists_coeff_of_mem_flagStep {b : Fin r → E} {n : ℕ} {x : E} (hx : x ∈ flagStep Ω b n) :
    ∃ d : Fin r → Ω, (∀ l : Fin r, n ≤ l → d l = 0) ∧ x = ∑ l, d l • b l := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun l hl => ?_, ?_⟩
    · have hk' : (k : ℕ) < n := hk
      have : l ≠ k := by
        rintro rfl
        exact absurd hk' (not_lt.2 hl)
      simp [this]
    · simp [Pi.single_apply, ite_smul]
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, h1, rfl⟩ := hx
    obtain ⟨e, h2, rfl⟩ := hy
    exact ⟨d + e, fun l hl => by simp [h1 l hl, h2 l hl], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨d, h1, rfl⟩ := hx
    exact ⟨a • d, fun l hl => by simp [h1 l hl], by simp [Finset.smul_sum, mul_smul]⟩

theorem coeff_eq_of_li {b : Fin r → E} (hb : LinearIndependent Ω b) {c d : Fin r → Ω}
    (h : ∑ l, c l • b l = ∑ l, d l • b l) : c = d := by
  have := Fintype.linearIndependent_iff.1 hb (fun l => c l - d l)
    (by simp [sub_smul, Finset.sum_sub_distrib, h])
  funext l
  exact sub_eq_zero.1 (this l)

theorem exists_tri (A : Subring Ω) {b b' : Fin r → E} (hb : LinearIndependent Ω b)
    (hm : ∀ k, b' k ∈ Submodule.span A (Set.range b)) (hf : ∀ k : Fin r, b' k ∈ flagStep Ω b (k + 1)) :
    ∃ P : Fin r → Fin r → A, (∀ k, b' k = ∑ l, (P l k : Ω) • b l) ∧ ∀ l k, k < l → P l k = 0 := by
  have h1 : ∀ k, ∃ c : Fin r → A, ∑ l, c l • b l = b' k := fun k =>
    (Submodule.mem_span_range_iff_exists_fun A).1 (hm k)
  choose c hc using h1
  have h2 : ∀ k l, (c k l : Ω) • b l = c k l • b l := fun _ _ => rfl
  refine ⟨fun l k => c k l, fun k => ?_, fun l k hkl => ?_⟩
  · rw [← hc k]
    exact Finset.sum_congr rfl fun l _ => rfl
  · obtain ⟨d, hd, hx⟩ := exists_coeff_of_mem_flagStep (hf k)
    have e : (fun l => (c k l : Ω)) = d := coeff_eq_of_li hb (by rw [← hx, ← hc k]; rfl)
    have : (c k l : Ω) = 0 := by
      rw [congrFun e l]
      exact hd l hkl
    exact Subtype.ext this

theorem frame_change (A : Subring Ω) {b b' : Fin r → E} (hb : LinearIndependent Ω b)
    (hb' : LinearIndependent Ω b') (hs : Submodule.span A (Set.range b) = Submodule.span A (Set.range b'))
    (hf : ∀ s, flagStep Ω b s = flagStep Ω b' s) :
    ∃ P : Fin r → Fin r → A, (∀ k, b' k = ∑ l, (P l k : Ω) • b l) ∧ (∀ l k, k < l → P l k = 0) ∧
      ∀ k, IsUnit (P k k) := by
  have mem : ∀ (c : Fin r → E) (k : Fin r), c k ∈ flagStep Ω c (k + 1) := fun c k =>
    Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩
  obtain ⟨P, hP, hP0⟩ := exists_tri A hb (fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩)
    (fun k => (hf _).symm ▸ mem b' k)
  obtain ⟨Q, hQ, hQ0⟩ := exists_tri A hb' (fun k => hs ▸ Submodule.subset_span ⟨k, rfl⟩)
    (fun k => hf _ ▸ mem b k)
  refine ⟨P, hP, hP0, fun k => ?_⟩
  have e : (fun m => ∑ l, (P m l : Ω) * (Q l k : Ω)) = fun m => if m = k then (1 : Ω) else 0 := by
    apply coeff_eq_of_li hb
    have h1 : ∑ l, (if l = k then (1 : Ω) else 0) • b l = b k := by simp [ite_smul]
    rw [h1]
    conv_rhs => rw [hQ k]
    simp only [hP, Finset.smul_sum, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by rw [smul_comm]
  have e' := congrFun e k
  simp only [if_true] at e'
  rw [Finset.sum_eq_single k] at e'
  · have : P k k * Q k k = 1 := Subtype.ext e'
    exact IsUnit.of_mul_eq_one _ this
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hP0 k l h]; simp
    · rw [hQ0 l k h]; simp
  · simp

end Alg

section Minor

variable {r : ℕ}

theorem sum_castLE {M : Type} [AddCommMonoid M] {n : ℕ} (hn : n ≤ r) (f : Fin r → M)
    (hf : ∀ l : Fin r, n ≤ l → f l = 0) : ∑ l, f l = ∑ a : Fin n, f (Fin.castLE hn a) := by
  refine (Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ ?_ fun _ => rfl).symm
  intro l hl
  refine hf l (not_lt.1 fun h => hl ⟨⟨l, h⟩, rfl⟩)

theorem leadMinor_conj (Γ C : Matrix (Fin r) (Fin r) ℂ) (hC : ∀ l k, k < l → C l k = 0) {n : ℕ} (hn : n ≤ r) :
    leadMinor (Cᴴ * Γ * C) n =
      (∏ a : Fin n, Complex.normSq (C (Fin.castLE hn a) (Fin.castLE hn a))) * leadMinor Γ n := by
  unfold leadMinor
  rw [dif_pos hn, dif_pos hn]
  set ic := Fin.castLE hn with hι2
  have hz : ∀ (a : Fin n) (l : Fin r), n ≤ l → C l (ic a) = 0 := fun a l hl =>
    hC l (ic a) (Fin.lt_def.2 (lt_of_lt_of_le (show ((ic a : Fin r) : ℕ) < n by simp [hι2]) hl))
  have hsub : (Cᴴ * Γ * C).submatrix ic ic = (C.submatrix ic ic)ᴴ * Γ.submatrix ic ic * C.submatrix ic ic := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [sum_castLE hn _ (fun l hl => by rw [hz c l hl, mul_zero])]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    rw [sum_castLE hn _ (fun l hl => by rw [hz a l hl]; simp)]
  have hdet : (C.submatrix ic ic).det = ∏ a, C (ic a) (ic a) := by
    refine Matrix.det_of_upperTriangular ?_
    intro a c hac
    exact hC _ _ (show (c : ℕ) < a from hac)
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdet, ← map_prod Complex.normSq]
  set d := ∏ a, C (ic a) (ic a)
  have : star d * (Γ.submatrix ic ic).det * d = ((Complex.normSq d : ℝ) : ℂ) * (Γ.submatrix ic ic).det := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [this, Complex.re_ofReal_mul]

theorem sqrt_ratio_conj (Γ C : Matrix (Fin r) (Fin r) ℂ) (hC : ∀ l k, k < l → C l k = 0)
    (hd : ∀ k, C k k ≠ 0) (i : Fin r) :
    Real.sqrt (leadMinor (Cᴴ * Γ * C) (i + 1) / leadMinor (Cᴴ * Γ * C) i) =
      ‖C i i‖ * Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i) := by
  rw [leadMinor_conj Γ C hC (show (i : ℕ) + 1 ≤ r from i.2), leadMinor_conj Γ C hC i.2.le,
    Fin.prod_univ_castSucc]
  have e1 : Fin.castLE (show (i : ℕ) + 1 ≤ r from i.2) (Fin.last i) = i := by ext; simp
  have e2 : ∀ a : Fin i, Fin.castLE (show (i : ℕ) + 1 ≤ r from i.2) a.castSucc = Fin.castLE i.2.le a := fun a => by
    ext; simp
  simp only [e1, e2]
  set N := ∏ a : Fin i, Complex.normSq (C (Fin.castLE i.2.le a) (Fin.castLE i.2.le a)) with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => (map_ne_zero Complex.normSq).2 (hd _)
  have : N * Complex.normSq (C i i) * leadMinor Γ (i + 1) / (N * leadMinor Γ i) =
      ‖C i i‖ ^ 2 * (leadMinor Γ (i + 1) / leadMinor Γ i) := by
    rw [Complex.normSq_eq_norm_sq]
    by_cases h0 : leadMinor Γ i = 0
    · simp [h0]
    · field_simp
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem gram_posDef {V : Type} [AddCommGroup V] [Module ℂ V] (h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hh : ∀ v w, h w v = starRingEnd ℂ (h v w)) (hp : ∀ v, v ≠ 0 → 0 < (h v v).re) (v : Fin r → V)
    (hv : LinearIndependent ℂ v) : (Matrix.of fun p q => h (v p) (v q)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext p q
    simp [Matrix.conjTranspose_apply, hh (v p) (v q)]
  · have e : star x ⬝ᵥ ((Matrix.of fun p q => h (v p) (v q)) *ᵥ x) = h (∑ p, x p • v p) (∑ q, x q • v q) := by
      simp [dotProduct, Matrix.mulVec, map_sum, LinearMap.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    set w := ∑ p, x p • v p with hw
    have hw0 : w ≠ 0 := fun h0 => hx (funext fun p => Fintype.linearIndependent_iff.1 hv x h0 p)
    refine Complex.pos_iff.2 ⟨hp w hw0, ?_⟩
    have := congrArg Complex.im (hh w w)
    simp only [Complex.conj_im] at this
    linarith

end Minor

section Core

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} {V : Type} [AddCommGroup V]
  [Module ℂ V]

theorem span_image_unit_smul {R : Type} [Ring R] [Module R E] (c : Fin r → Rˣ) (b : Fin r → E) (T : Set (Fin r)) :
    Submodule.span R ((fun k => (c k : R) • b k) '' T) = Submodule.span R (b '' T) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have e : b k = ((c k)⁻¹ : Rˣ).val • ((c k : R) • b k) := by rw [smul_smul]; simp
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)

theorem scale_frame (A : Subring Ω) {b : Fin r → E} (hb : LinearIndependent Ω b) (c : Fin r → Aˣ) :
    LinearIndependent Ω (fun k => ((c k : A) : Ω) • b k) ∧
      Submodule.span A (Set.range fun k => ((c k : A) : Ω) • b k) = Submodule.span A (Set.range b) ∧
      ∀ s, flagStep Ω (fun k => ((c k : A) : Ω) • b k) s = flagStep Ω b s := by
  refine ⟨?_, ?_, fun s => ?_⟩
  · exact hb.units_smul fun k => Units.map A.subtype.toMonoidHom (c k)
  · have := span_image_unit_smul c b Set.univ
    rwa [Set.image_univ, Set.image_univ] at this
  · exact span_image_unit_smul (fun k => Units.map A.subtype.toMonoidHom (c k)) b _

def gramOf (h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (val : E → V) (b : Fin r → E) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun p q => h (val (b p)) (val (b q))

variable {A : Subring Ω} {φ : A →+* ℂ} {Lm : Submodule A E} {val : E → V}

theorem val_sum (h0 : val 0 = 0) (hadd : ∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e')
    (hsm : ∀ a : A, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) {b : Fin r → E} (hb : ∀ k, b k ∈ Lm)
    (a : Fin r → A) (s : Finset (Fin r)) :
    val (∑ l ∈ s, (a l : Ω) • b l) = ∑ l ∈ s, φ (a l) • val (b l) := by
  classical
  have hm : ∀ (l : Fin r), (a l : Ω) • b l ∈ Lm := fun l => Lm.smul_mem (a l) (hb l)
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert l s hl ih =>
    rw [Finset.sum_insert hl, Finset.sum_insert hl, hadd _ (hm l) _ (Lm.sum_mem fun k _ => hm k), hsm _ _ (hb l), ih]

theorem compare (h0 : val 0 = 0) (hadd : ∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e')
    (hsm : ∀ a : A, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) (h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    {b₀ b b' : Fin r → E} (hb₀ : LinearIndependent Ω b₀) (hb : LinearIndependent Ω b)
    (hb' : LinearIndependent Ω b') (hbL : ∀ k, b k ∈ Lm)
    (hs : Submodule.span A (Set.range b) = Submodule.span A (Set.range b'))
    (hf : ∀ s, flagStep Ω b s = flagStep Ω b₀ s) (hf' : ∀ s, flagStep Ω b' s = flagStep Ω b₀ s) (i : Fin r)
    {t t' : Ω} (h1 : b i - t • b₀ i ∈ flagStep Ω b₀ i) (h2 : b' i - t' • b₀ i ∈ flagStep Ω b₀ i) :
    ∃ a : A, IsUnit a ∧ (a : Ω) * t = t' ∧
      Real.sqrt (leadMinor (gramOf h val b') (i + 1) / leadMinor (gramOf h val b') i) =
        ‖φ a‖ * Real.sqrt (leadMinor (gramOf h val b) (i + 1) / leadMinor (gramOf h val b) i) := by
  classical
  obtain ⟨P, hP, hP0, hPu⟩ := frame_change A hb hb' hs fun s => (hf s).trans (hf' s).symm
  let C : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun l k => φ (P l k)
  have hval : ∀ k, val (b' k) = ∑ l, C l k • val (b l) := fun k => by
    rw [hP k]
    exact val_sum h0 hadd hsm hbL (fun l => P l k) Finset.univ
  have hG : gramOf h val b' = Cᴴ * gramOf h val b * C := by
    ext p q
    simp only [gramOf, Matrix.of_apply, hval, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
      LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, Finset.sum_mul, Complex.star_def,
      RingHom.id_apply, smul_eq_mul, map_smulₛₗ]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hC : ∀ l k, k < l → C l k = 0 := fun l k hkl => by simp [C, hP0 l k hkl]
  have hd : ∀ k, C k k ≠ 0 := fun k => ((hPu k).map φ).ne_zero
  refine ⟨P i i, hPu i, ?_, ?_⟩
  · have m1 : b' i - (P i i : Ω) • b i ∈ flagStep Ω b₀ i := by
      have e : b' i - (P i i : Ω) • b i = ∑ l ∈ Finset.univ.erase i, (P l i : Ω) • b l := by
        rw [hP i, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        abel
      rw [e]
      refine Submodule.sum_mem _ fun l hl => ?_
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hli | hli
      · exact Submodule.smul_mem _ _ (hf i ▸ Submodule.subset_span ⟨l, hli, rfl⟩)
      · rw [hP0 l i hli]
        simp
    have m2 : (t' - (P i i : Ω) * t) • b₀ i ∈ flagStep Ω b₀ i := by
      have e : (t' - (P i i : Ω) * t) • b₀ i =
          (b' i - (P i i : Ω) • b i) - (b' i - t' • b₀ i) + (P i i : Ω) • (b i - t • b₀ i) := by
        simp only [sub_smul, smul_sub, mul_smul]
        abel
      rw [e]
      exact add_mem (sub_mem m1 h2) (Submodule.smul_mem _ _ h1)
    obtain ⟨d, hd0, hx⟩ := exists_coeff_of_mem_flagStep m2
    have e2 : (Pi.single i (t' - (P i i : Ω) * t) : Fin r → Ω) = d :=
      coeff_eq_of_li hb₀ (by rw [← hx]; simp [Pi.single_apply, ite_smul])
    have e3 := congrFun e2 i
    rw [Pi.single_eq_same, hd0 i le_rfl] at e3
    exact (sub_eq_zero.1 e3).symm
  · rw [hG]
    exact sqrt_ratio_conj _ C hC hd i

theorem core (h0 : val 0 = 0) (hadd : ∀ e ∈ Lm, ∀ e' ∈ Lm, val (e + e') = val e + val e')
    (hsm : ∀ a : A, ∀ e ∈ Lm, val ((a : Ω) • e) = φ a • val e) (hloc : ∀ a : A, φ a ≠ 0 → IsUnit a)
    (h : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hh : ∀ v w, h w v = starRingEnd ℂ (h v w)) (hp : ∀ v, v ≠ 0 → 0 < (h v v).re)
    (Vq : Submodule A E) (hVL : Vq ≤ Lm)
    (hfr : ∀ b : Fin r → E, LinearIndependent Ω b → Vq = Submodule.span A (Set.range b) →
      LinearIndependent ℂ fun k => val (b k))
    {b₀ b : Fin r → E} (hb₀ : LinearIndependent Ω b₀) (hb : LinearIndependent Ω b)
    (hV : Vq = Submodule.span A (Set.range b)) (hf : ∀ s, flagStep Ω b s = flagStep Ω b₀ s) (i : Fin r)
    {t : Ω} (ht : t ≠ 0) (h1 : b i - t • b₀ i ∈ flagStep Ω b₀ i) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ (t' : Ω) (ν' : ℝ),
      (∃ (b' : Fin r → E) (Γ : Matrix (Fin r) (Fin r) ℂ), (∀ s, flagStep Ω b' s = flagStep Ω b₀ s) ∧
        LinearIndependent Ω b' ∧ Vq = Submodule.span A (Set.range b') ∧ b' i - t' • b₀ i ∈ flagStep Ω b₀ i ∧
        Γ = gramOf h val b' ∧ Γ.PosDef ∧ ν' = Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i)) ↔
      ∃ u : ℂ, u ≠ 0 ∧ (∃ a : A, (a : Ω) = t' / t ∧ φ a = u) ∧ ν' = ‖u‖ * ν := by
  classical
  have hbL : ∀ k, b k ∈ Lm := fun k => hVL (hV ▸ Submodule.subset_span ⟨k, rfl⟩)
  have hΓ : (gramOf h val b).PosDef := gram_posDef h hh hp _ (hfr b hb hV)
  refine ⟨Real.sqrt (leadMinor (gramOf h val b) (i + 1) / leadMinor (gramOf h val b) i),
    Real.sqrt_pos.2 (div_pos (leadMinor_pos_of_posDef hΓ i.2) (leadMinor_pos_of_posDef hΓ i.2.le)),
    fun t' ν' => ⟨?_, ?_⟩⟩
  · rintro ⟨b', Γ, hf', hb', hV', h2, rfl, -, rfl⟩
    obtain ⟨a, ha, e1, e2⟩ := compare h0 hadd hsm h hb₀ hb hb' hbL (hV.symm.trans hV') hf hf' i h1 h2
    exact ⟨φ a, (ha.map φ).ne_zero, ⟨a, eq_div_of_mul_eq ht e1, rfl⟩, e2⟩
  · rintro ⟨u, hu, ⟨a, e1, rfl⟩, rfl⟩
    obtain ⟨w, rfl⟩ := hloc a hu
    obtain ⟨hb', hs', hf'⟩ := scale_frame A hb (Function.update 1 i w)
    set b' : Fin r → E := fun k => (((Function.update 1 i w : Fin r → Aˣ) k : A) : Ω) • b k with hb'def
    have hbi : b' i = ((w : A) : Ω) • b i := by simp [hb'def]
    have h2 : b' i - t' • b₀ i ∈ flagStep Ω b₀ i := by
      have e : b' i - t' • b₀ i = ((w : A) : Ω) • (b i - t • b₀ i) := by
        rw [hbi, smul_sub, smul_smul, e1, div_mul_cancel₀ _ ht]
      rw [e]
      exact Submodule.smul_mem _ _ h1
    have hf'' : ∀ s, flagStep Ω b' s = flagStep Ω b₀ s := fun s => (hf' s).trans (hf s)
    have hV' : Vq = Submodule.span A (Set.range b') := hV.trans hs'.symm
    obtain ⟨a', -, e3, e4⟩ := compare h0 hadd hsm h hb₀ hb hb' hbL (hV.symm.trans hV') hf hf'' i h1 h2
    have e5 : a' = w := Subtype.ext (by
      rw [e1]
      exact eq_div_of_mul_eq ht e3)
    subst e5
    exact ⟨b', _, hf'', hb', hV', h2, rfl, gram_posDef h hh hp _ (hfr b' hb' hV'), e4.symm⟩

end Core

section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem not_inFibre {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : genPt ξ ⤳ centre z) {p : ℕ} (hp : p.Prime) :
    ¬ InFibre ξ p ⟨centre z, hz⟩ := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 := RootHt.ArchB.val_nat (ξ := ξ) (z := z) hz p
  have h2 := RootHt.ArchB.val_inv₀ hp0 h1
  intro h
  refine h ⟨fun e => hp0 ?_, ?_, ?_⟩
  · rw [e] at h1
    exact RootHt.ArchB.val_unique hξ h1 (RootHt.ArchB.val_zero hz)
  · obtain ⟨s, e, -⟩ := h1.choose_spec
    exact ⟨s, e⟩
  · obtain ⟨s, e, -⟩ := h2.choose_spec
    exact ⟨s, e⟩

theorem exists_dual (𝔐 : HodgeCpt Y S y) (hind : iSupIndep 𝔐.Vgen) (q : Cpt 𝔐.ξ)
    (hlat : 𝔐.M.lat q = ⨆ s, 𝔐.dR s q) (s : CMType H ⊕ CMType H) {r : ℕ} (b : Fin r → 𝔐.Li)
    (hli : LinearIndependent Ω b) (hfr : 𝔐.dR s q = Submodule.span (regAt 𝔐.ξ q) (Set.range b)) :
    ∃ π : Fin r → Module.Dual Ω 𝔐.Li, (∀ j l, π j (b l) = if j = l then 1 else 0) ∧
      ∀ j, ∀ e ∈ 𝔐.M.lat q, π j e ∈ regAt 𝔐.ξ q := by
  classical
  obtain ⟨W, hW, hc⟩ := (hind s).symm.exists_isCompl
  let pr : 𝔐.Li →ₗ[Ω] 𝔐.Vgen s := Submodule.linearProjOfIsCompl _ _ hc.symm
  have hker : LinearMap.ker (Fintype.linearCombination Ω b) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun m hm => funext fun k => ?_
    exact Fintype.linearIndependent_iff.1 hli m (by rwa [Fintype.linearCombination_apply] at hm) k
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hgb : ∀ l, g (b l) = Pi.single l 1 := fun l => by
    have := LinearMap.congr_fun hg (Pi.single l 1)
    simpa [Fintype.linearCombination_apply_single] using this
  have hbV : ∀ l, b l ∈ 𝔐.Vgen s := fun l => by
    have : b l ∈ 𝔐.dR s q := hfr ▸ Submodule.subset_span ⟨l, rfl⟩
    exact this.2
  have hpr : ∀ x (hx : x ∈ 𝔐.Vgen s), ((pr x : 𝔐.Vgen s) : 𝔐.Li) = x := fun x hx => by
    have := Submodule.linearProjOfIsCompl_apply_left hc.symm ⟨x, hx⟩
    exact congrArg Subtype.val this
  refine ⟨fun j => (LinearMap.proj j).comp (g.comp ((𝔐.Vgen s).subtype.comp pr)), fun j k => ?_, fun j e he => ?_⟩
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, hpr _ (hbV k), hgb, LinearMap.proj_apply]
    simp [Pi.single_apply]
  · rw [hlat] at he
    induction he using Submodule.iSup_induction' with
    | mem s' x hx =>
      by_cases e : s' = s
      · subst e
        rw [hfr] at hx
        obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
        have e1 : ∀ k, (c' k • b k) = ((c' k : regAt 𝔐.ξ q) : Ω) • b k := fun _ => rfl
        simp only [e1, map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply, hpr _ (hbV _), hgb,
          LinearMap.proj_apply]
        refine sum_mem fun k _ => ?_
        rw [smul_eq_mul]
        refine mul_mem (c' k).2 ?_
        rw [Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · have hxW : x ∈ W := hW (Submodule.mem_iSup_of_mem s' (Submodule.mem_iSup_of_mem e hx.2))
        have : pr x = 0 := Submodule.linearProjOfIsCompl_apply_right' hc.symm hxW
        simp [this]
    | zero => simpa using zero_mem _
    | add x y _ _ hx hy => simpa using add_mem hx hy

theorem injective_of_algebraic {O : Type} [CommRing O] {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F]
    (β : O →+* F) (hβ : Function.Injective β) (g : O →+* ℂ) : Function.Injective g := by
  refine (injective_iff_map_eq_zero g).2 fun o ho => ?_
  by_contra h0
  have b0 : β o ≠ 0 := fun h => h0 (hβ (h.trans (map_zero β).symm))
  have halg : IsAlgebraic ℤ (β o) := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨p, hp, hp0⟩ := halg
  obtain ⟨q, hq, hq'⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  simp only [map_zero, sub_zero, Polynomial.X_dvd_iff] at hq hq'
  have h1 : Polynomial.aeval (β o) q = 0 := by
    rw [hq, map_mul, map_pow, Polynomial.aeval_X] at hp0
    exact (mul_eq_zero.1 hp0).resolve_left (pow_ne_zero _ b0)
  have h2 : Polynomial.aeval o q = 0 := by
    apply hβ
    rw [map_zero, ← h1]
    exact (Polynomial.aeval_algHom_apply β.toIntAlgHom o q).symm
  have h3 : Polynomial.aeval (g o) q = 0 := by
    have := Polynomial.aeval_algHom_apply g.toIntAlgHom o q
    rw [h2, map_zero] at this
    exact this
  rw [ho, Polynomial.aeval_def, Polynomial.eval₂_at_zero] at h3
  exact hq' (by simpa using h3)

theorem spec_injective_point {O K : Type} [CommRing O] [Field K] (g : O →+* K) (hg : Function.Injective g)
    (p : Spec (CommRingCat.of K)) :
    ((Spec.map (CommRingCat.ofHom g)) p : PrimeSpectrum O).asIdeal = ⊥ := by
  have h0 : (p : PrimeSpectrum K).asIdeal = ⊥ :=
    @Ideal.eq_bot_of_prime K _ _ (PrimeSpectrum.isPrime (p : PrimeSpectrum K))
  change Ideal.comap g (p : PrimeSpectrum K).asIdeal = ⊥
  rw [h0]
  exact Ideal.comap_bot_of_injective g hg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

attribute [local instance] Over.cartesianMonoidalCategory in

theorem interior_pol (𝔐 : HodgeCpt Y S y) (hβ : Function.Injective β) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X)
    (hz : 𝔐.Interior z) :
    ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' 𝔐.t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.CubePf.cubePull z 𝔐.t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m m₁
  have hr : Set.range (z ≫ 𝔐.f) ⊆ Set.range (Y.jQ ≫ pullback.fst Y.s (spMap β)) := by
    rintro _ ⟨p, rfl⟩
    have hab : 𝔐.f (centre z) ∈ abLocus Y.t.G :=
      (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _).2 hz
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    letI : Algebra.IsAlgebraic ℚ c.F := by
      have := c.fin
      infer_instance
    let g : O →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
    have hg : Function.Injective g := injective_of_algebraic β hβ g
    have e : Spec.map (CommRingCat.ofHom g) = z ≫ 𝔐.f ≫ Y.s := Spec.map_preimage _
    let pt : Spec (CommRingCat.of c.F) := IsLocalRing.closedPoint c.F
    have hs : Y.s (𝔐.f (centre z)) = spMap β pt := by
      apply PrimeSpectrum.ext
      have e1 : Y.s (𝔐.f (centre z)) = Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint ℂ) := by
        rw [e]; simp only [Scheme.Hom.comp_apply]; rfl
      rw [e1]
      exact (spec_injective_point g hg _).trans (spec_injective_point β hβ pt).symm
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.s) (g := spMap β) _ _ hs
    have hw' : w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Set.mem_preimage, hw]; exact hab
    rw [Y.ab_gen] at hw'
    obtain ⟨v, rfl⟩ := hw'
    refine ⟨v, ?_⟩
    rw [Scheme.Hom.comp_apply]
    exact hw
  have := GlobalTheory.GenericPol.proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv n hr
  exact ⟨_, m₁, this.1, this.2.1⟩

theorem spec_dual_fst {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp [dualMap]

theorem tan_of_valAt {X : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ : Sp Ω' ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω' Li] {M : LieModel G ξ Li} {z : Sp ℂ ⟶ X} {e : Li}
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : IsTanAt G z w := by
  obtain ⟨hz, v, ⟨hv, -⟩, hw⟩ := h
  unfold IsTanAt at hv ⊢
  let t : Over.mk z ⟶ Over.mk (X.fromSpecStalk (centre z)) :=
    Over.homMk (Spec.map (Scheme.stalkClosedPointTo z)) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)
  have h1 : t ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) = 1 := MonObj.comp_one t
  have h2 := congrArg CommaMorphism.left h1
  rw [hw]
  refine Eq.trans ?_ h2
  change _ = Spec.map (Scheme.stalkClosedPointTo z) ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G).left
  refine Eq.trans ?_ (congrArg (fun k => Spec.map (Scheme.stalkClosedPointTo z) ≫ k) hv)
  have key := spec_dual_fst (Scheme.stalkClosedPointTo z).hom
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ v.left) key).trans (Category.assoc _ _ _))

theorem exists_sub_mem_flagStep {Ω' : Type} [Field Ω'] {E' : Type} [AddCommGroup E'] [Module Ω' E'] {r : ℕ}
    {b : Fin r → E'} (i : Fin r) {x : E'} (hx : x ∈ flagStep Ω' b (i + 1)) :
    ∃ a : Ω', x - a • b i ∈ flagStep Ω' b i := by
  classical
  obtain ⟨d, hd, rfl⟩ := exists_coeff_of_mem_flagStep hx
  refine ⟨d i, ?_⟩
  have e : ∑ l, d l • b l - d i • b i = ∑ l ∈ Finset.univ.erase i, d l • b l := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    abel
  rw [e]
  refine Submodule.sum_mem _ fun l hl => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with hli | hli
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hli, rfl⟩)
  · rw [hd l hli]
    simp

end Concrete

theorem exists_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag), Function.Injective β → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), 𝔐.Interior z → ∀ s (i : Fin (labelRk D s)) (t : Ω), ((𝔐.V s).gr (Fl.b s) i).IsGenAt ⟨centre z, 𝔐.all _⟩ t → ∃ ν : ℝ, 0 < ν ∧ ∀ (t' : Ω) (ν' : ℝ), 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) i z t' ν' ↔ ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (t' / t) u ∧ ν' = ‖u‖ * ν := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl hβ z hz s i t ht
  classical
  have hgen : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  set q : Cpt 𝔐.ξ := ⟨centre z, hgen⟩ with hq
  obtain ⟨-, -, -, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
  obtain ⟨hV, -, hlat⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S Ω K J y 𝔐 hβ q fun r hr => not_inFibre hξ hgen hr
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨ev, hev1, hev2, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z hgen Vz MR hξ hsm
  obtain ⟨h, hHI, hh, hp⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z Vz MR (interior_pol 𝔐 hβ z hz)

  let eA : 𝔐.X.presheaf.stalk q.1 ≃+* regAt 𝔐.ξ q :=
    RingEquiv.ofBijective (genMap 𝔐.ξ q).rangeRestrict ⟨fun a b e => hξ.inj q (congrArg Subtype.val e),
      (genMap 𝔐.ξ q).rangeRestrict_surjective⟩
  let φ : regAt 𝔐.ξ q →+* ℂ := (Scheme.stalkClosedPointTo z).hom.comp (eA.symm : regAt 𝔐.ξ q →+* 𝔐.X.presheaf.stalk q.1)
  have hφ : ∀ a : regAt 𝔐.ξ q, ValAt 𝔐.ξ z (a : Ω) (φ a) := fun a =>
    ⟨hgen, eA.symm a, congrArg Subtype.val (eA.apply_symm_apply a), rfl⟩
  have hloc : ∀ a : regAt 𝔐.ξ q, φ a ≠ 0 → IsUnit a := fun a ha => by
    have := CxVal.isUnit (z := z) (eA.symm a) ha
    simpa using this.map eA

  let val : 𝔐.Li → Vz := fun e => if he : e ∈ 𝔐.M.lat q then ev ⟨e, he⟩ else 0
  have hval : ∀ e (he : e ∈ 𝔐.M.lat q), val e = ev ⟨e, he⟩ := fun e he => dif_pos he
  have h0 : val 0 = 0 := by
    rw [hval 0 (zero_mem _)]
    exact map_zero ev
  have hadd : ∀ e ∈ 𝔐.M.lat q, ∀ e' ∈ 𝔐.M.lat q, val (e + e') = val e + val e' := fun e he e' he' => by
    rw [hval _ (add_mem he he'), hval e he, hval e' he']
    exact map_add ev ⟨e, he⟩ ⟨e', he'⟩
  have hsmul : ∀ a : regAt 𝔐.ξ q, ∀ e ∈ 𝔐.M.lat q, val ((a : Ω) • e) = φ a • val e := fun a e he => by
    have hm : (a : Ω) • e ∈ 𝔐.M.lat q := (𝔐.M.lat q).smul_mem a he
    rw [hval _ hm, hval e he]
    exact hev2 a (φ a) ⟨e, he⟩ (hφ a)
  have hvalAt : ∀ e (he : e ∈ 𝔐.M.lat q), 𝔐.M.ValAt z e (MR.pt (val e)) := fun e he =>
    (hev1 e _).2 ⟨he, (hval e he).symm⟩

  have hVL : 𝔐.V s q ≤ 𝔐.M.lat q := by
    rw [hV s, hlat]
    exact le_iSup (fun s' => 𝔐.dR s' q) s

  have hfr : ∀ b : Fin (labelRk D s) → 𝔐.Li, LinearIndependent Ω b →
      𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (Set.range b) → LinearIndependent ℂ fun k => val (b k) := by
    intro b hb hVb
    obtain ⟨π, hπ, hreg⟩ := exists_dual 𝔐 hind q hlat s b hb ((hV s).symm.trans hVb)
    have hbL : ∀ k, b k ∈ 𝔐.M.lat q := fun k => hVL (hVb ▸ Submodule.subset_span ⟨k, rfl⟩)
    have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (val (b k)) = if j = k then 1 else 0 := fun j => by
      obtain ⟨g, hg⟩ := GlobalTheory.T.lattice_regular_at_local_point 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z hgen Vz MR (π j) hξ (hreg j)
      refine ⟨g, fun k => hg (b k) _ _ (hvalAt _ (hbL k)) ?_⟩
      rw [hπ j k]
      split_ifs
      · exact RootHt.ArchB.val_one hgen
      · exact RootHt.ArchB.val_zero hgen
    choose g hg using hg
    refine Fintype.linearIndependent_iff.2 fun w hw j => ?_
    have := congrArg (g j) hw
    simpa [map_sum, hg, Finset.sum_ite_eq] using this

  have hGram : ∀ (b : Fin (labelRk D s) → 𝔐.Li) (Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ),
      (∀ k, b k ∈ 𝔐.M.lat q) → (𝔐.M.GramAt 𝔐.t.PP.L z b Γ ↔ Γ = gramOf h val b) := by
    intro b Γ hb
    constructor
    · rintro ⟨v, hv, hI⟩
      have e : ∀ k, v k = MR.pt (val (b k)) := fun k => by
        obtain ⟨x, hx⟩ := MR.onto (v k) (tan_of_valAt (hv k))
        have h1 := hv k
        rw [← hx] at h1
        obtain ⟨he, e2⟩ := (hev1 _ _).1 h1
        rw [hval _ he, e2, hx]
      ext p p'
      have := hI p p'
      rw [e p, e p'] at this
      exact (hHI _ _ _).1 this
    · rintro rfl
      exact ⟨fun k => MR.pt (val (b k)), fun k => hvalAt _ (hb k), fun p p' => (hHI _ _ _).2 rfl⟩

  have hb₀ : LinearIndependent Ω (Fl.b s) := by
    obtain ⟨c', u, -, -, -, hb, -⟩ := Fl.generic
    exact hb s
  obtain ⟨U, hU, b, hflag, hb⟩ := Fl.sub s q trivial
  obtain ⟨hbli, hbV⟩ := hb q trivial hU
  obtain ⟨a, ha⟩ : ∃ a : Ω, b i - a • Fl.b s i ∈ flagStep Ω (Fl.b s) i :=
    exists_sub_mem_flagStep i (hflag _ ▸ Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
  have hgr := FlagGrGen.gr_isGenAt 𝔐.X Ω 𝔐.ξ 𝔐.Li (𝔐.V s) (labelRk D s) (Fl.b s) b q i a hb₀ hflag ⟨hbli, hbV⟩ ha
  obtain ⟨d, hd⟩ : ∃ d : regAt 𝔐.ξ q, d • a = t := by
    have : t ∈ Submodule.span (regAt 𝔐.ξ q) {a} := hgr.2 ▸ ht.2 ▸ Submodule.mem_span_singleton_self t
    exact Submodule.mem_span_singleton.1 this
  obtain ⟨d', hd'⟩ : ∃ d' : regAt 𝔐.ξ q, d' • t = a := by
    have : a ∈ Submodule.span (regAt 𝔐.ξ q) {t} := ht.2 ▸ hgr.2 ▸ Submodule.mem_span_singleton_self a
    exact Submodule.mem_span_singleton.1 this
  have hdu : IsUnit d := by
    have e : (d : Ω) * d' = 1 := by
      have e1 : (d : Ω) * ((d' : Ω) * t) = t := by
        have e2 : (d' : Ω) * t = a := hd'
        rw [e2]
        exact hd
      have : ((d : Ω) * d' - 1) * t = 0 := by linear_combination e1
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right ht.1)
    exact IsUnit.of_mul_eq_one _ (Subtype.ext e : d * d' = 1)
  obtain ⟨w, rfl⟩ := hdu
  obtain ⟨hb', hs', hf'⟩ := scale_frame (regAt 𝔐.ξ q) hbli (Function.update 1 i w)
  set b' : Fin (labelRk D s) → 𝔐.Li := fun k => (((Function.update 1 i w : Fin (labelRk D s) → (regAt 𝔐.ξ q)ˣ) k :
    regAt 𝔐.ξ q) : Ω) • b k with hb'def
  have hbi : b' i = ((w : regAt 𝔐.ξ q) : Ω) • b i := by simp [hb'def]
  have h1 : b' i - t • Fl.b s i ∈ flagStep Ω (Fl.b s) i := by
    have e : b' i - t • Fl.b s i = ((w : regAt 𝔐.ξ q) : Ω) • (b i - a • Fl.b s i) := by
      have e2 : ((w : regAt 𝔐.ξ q) : Ω) * a = t := hd
      rw [hbi, smul_sub, smul_smul, e2]
    rw [e]
    exact Submodule.smul_mem _ _ ha
  obtain ⟨ν, hν, hcore⟩ := core (Lm := 𝔐.M.lat q) (φ := φ) (val := val) h0 hadd hsmul hloc h hh hp (𝔐.V s q) hVL hfr hb₀ hb'
    (hbV.trans hs'.symm) (fun s' => (hf' s').trans (hflag s')) i ht.1 h1
  refine ⟨ν, hν, fun t' ν' => ?_⟩
  have e : 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) i z t' ν' ↔
      (∃ (b' : Fin (labelRk D s) → 𝔐.Li) (Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ),
        (∀ s', flagStep Ω b' s' = flagStep Ω (Fl.b s) s') ∧ LinearIndependent Ω b' ∧
        𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (Set.range b') ∧ b' i - t' • Fl.b s i ∈ flagStep Ω (Fl.b s) i ∧
        Γ = gramOf h val b' ∧ Γ.PosDef ∧ ν' = Real.sqrt (leadMinor Γ (i + 1) / leadMinor Γ i)) := by
    constructor
    · rintro ⟨h', c', Γ, g1, ⟨g2, g3⟩, g4, g5, g6, g7⟩
      have hc' : ∀ k, c' k ∈ 𝔐.M.lat q := fun k => hVL (g3 ▸ Submodule.subset_span ⟨k, rfl⟩)
      exact ⟨c', Γ, g1, g2, g3, g4, (hGram c' Γ hc').1 g5, g6, g7⟩
    · rintro ⟨c', Γ, g1, g2, g3, g4, g5, g6, g7⟩
      have hc' : ∀ k, c' k ∈ 𝔐.M.lat q := fun k => hVL (g3 ▸ Submodule.subset_span ⟨k, rfl⟩)
      exact ⟨hgen, c', Γ, g1, ⟨g2, g3⟩, g4, (hGram c' Γ hc').2 g5, g6, g7⟩
  rw [e, hcore]
  constructor
  · rintro ⟨u, hu, ⟨a', e1, rfl⟩, e2⟩
    exact ⟨_, hu, e1 ▸ hφ a', e2⟩
  · rintro ⟨u, hu, hv, e2⟩
    obtain ⟨h', r', e3, rfl⟩ := hv
    refine ⟨_, hu, ⟨eA r', e3, ?_⟩, e2⟩
    show (Scheme.stalkClosedPointTo z).hom (eA.symm (eA r')) = _
    rw [eA.symm_apply_apply]

end GlobalTheory.CompanionTheory.Ar.GrNorm
