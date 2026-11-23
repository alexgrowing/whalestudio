import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Fake

def sqLen (v : Fin 2 → ℤ) : ℕ := (v 0 * v 0 + v 1 * v 1).toNat

theorem sqLen_cast (v : Fin 2 → ℤ) : (sqLen v : ℤ) = v 0 * v 0 + v 1 * v 1 :=
  Int.toNat_of_nonneg (by nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)])

theorem ext2 {v w : Fin 2 → ℤ} (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem sqLen_ne_zero {v : Fin 2 → ℤ} (hv : v ≠ 0) : sqLen v ≠ 0 := by
  intro h
  have h2 := sqLen_cast v
  rw [h] at h2
  push_cast at h2
  have hre : v 0 = 0 := by nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]
  have him : v 1 = 0 := by nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]
  exact hv (ext2 hre him)

def sympForm : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun v w => v 0 * w 1 - v 1 * w 0)
    (fun v v' w => by simp; ring) (fun n v w => by simp; ring)
    (fun v w w' => by simp; ring) (fun n v w => by simp; ring)

theorem sympForm_apply (v w : Fin 2 → ℤ) : sympForm v w = v 0 * w 1 - v 1 * w 0 := rfl

theorem relIndex_span_le {I : Submodule ℤ (Fin 2 → ℤ)} (hI : IsIsoSub sympForm I) {v : Fin 2 → ℤ}
    (hvI : v ∈ I) (hv : v ≠ 0) :
    (Submodule.span ℤ {v}).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 ∧
      (Submodule.span ℤ {v}).toAddSubgroup.relIndex I.toAddSubgroup ≤ sqLen v := by
  haveI : NeZero (sqLen v) := ⟨sqLen_ne_zero hv⟩
  let f : I.toAddSubgroup →+ ZMod (sqLen v) :=
    { toFun := fun w => (((w : Fin 2 → ℤ) 0 * v 0 + (w : Fin 2 → ℤ) 1 * v 1 : ℤ) : ZMod (sqLen v))
      map_zero' := by simp
      map_add' := fun a b => by
        simp only [AddSubgroup.coe_add, Pi.add_apply]
        push_cast; ring }
  have hker : f.ker ≤ (Submodule.span ℤ {v}).toAddSubgroup.addSubgroupOf I.toAddSubgroup := by
    intro w hw
    have h1 : ((sqLen v : ℕ) : ℤ) ∣ (w : Fin 2 → ℤ) 0 * v 0 + (w : Fin 2 → ℤ) 1 * v 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hw
    obtain ⟨k, hk⟩ := h1
    have h2 := hI v hvI w w.2
    rw [sympForm_apply] at h2
    have hN : ((sqLen v : ℕ) : ℤ) ≠ 0 := by exact_mod_cast sqLen_ne_zero hv
    have hs := sqLen_cast v
    rw [AddSubgroup.mem_addSubgroupOf]
    have e0 : k * v 0 = (w : Fin 2 → ℤ) 0 := by
      apply mul_left_cancel₀ hN
      linear_combination (-v 0) * hk - (w : Fin 2 → ℤ) 0 * hs + v 1 * h2
    have e1 : k * v 1 = (w : Fin 2 → ℤ) 1 := by
      apply mul_left_cancel₀ hN
      linear_combination (-v 1) * hk - (w : Fin 2 → ℤ) 1 * hs - v 0 * h2
    exact Submodule.mem_span_singleton.2 ⟨k, ext2 (by simpa using e0) (by simpa using e1)⟩
  have hdvd := AddSubgroup.index_dvd_of_le hker
  have hcard : f.ker.index = Nat.card f.range := AddSubgroup.index_ker f
  have hle : f.ker.index ≤ sqLen v := by
    rw [hcard]
    exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans (by simp)
  have hne : f.ker.index ≠ 0 := by
    rw [hcard]
    exact Nat.card_pos.ne'
  exact ⟨fun h => hne (Nat.eq_zero_of_zero_dvd (h ▸ hdvd)), (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hle⟩

theorem card_le_one {I : Submodule ℤ (Fin 2 → ℤ)} (hI : IsIsoSub sympForm I) {ρ : ℕ} {v : Fin ρ → Fin 2 → ℤ}
    (hv : ∀ a, v a ∈ I) (hli : LinearIndependent ℤ v) : ρ ≤ 1 := by
  by_contra h
  push Not at h
  let a : Fin ρ := ⟨0, by omega⟩
  let b : Fin ρ := ⟨1, h⟩
  have hab : LinearIndependent ℤ ![v a, v b] := by
    have := hli.comp ![a, b] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [a, b])
    convert this using 1
    funext i; fin_cases i <;> rfl
  have h2 := hI _ (hv a) _ (hv b)
  rw [sympForm_apply] at h2
  have hs := sqLen_cast (v a)
  have := (LinearIndependent.pair_iff.1 hab (-((v b) 0 * (v a) 0 + (v b) 1 * (v a) 1)) (sqLen (v a))
    (ext2 (by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linear_combination (v b) 0 * hs - (v a) 1 * h2) (by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linear_combination (v b) 1 * hs + (v a) 0 * h2))).2
  exact sqLen_ne_zero (hli.ne_zero a) (by exact_mod_cast this)

def cx (v : Fin 2 → ℤ) : ℂ := ⟨v 0, v 1⟩

theorem cx_add (v w : Fin 2 → ℤ) : cx (v + w) = cx v + cx w := by
  apply Complex.ext <;> simp [cx]

theorem cx_smul (a : ℤ) (v : Fin 2 → ℤ) : cx (a • v) = (a : ℂ) * cx v := by
  apply Complex.ext <;> simp [cx]

theorem cx_zero : cx 0 = 0 := by
  apply Complex.ext <;> simp [cx]

theorem normSq_cx (v : Fin 2 → ℤ) : Complex.normSq (cx v) = (v 0 : ℝ) ^ 2 + (v 1 : ℝ) ^ 2 := by
  rw [cx, Complex.normSq_mk]
  ring

theorem cx_injective {v : Fin 2 → ℤ} (h : cx v = 0) : v = 0 := by
  have h0 := congrArg Complex.re h
  have h1 := congrArg Complex.im h
  simp only [cx, Complex.zero_re, Complex.zero_im] at h0 h1
  exact ext2 (by exact_mod_cast h0) (by exact_mod_cast h1)

theorem sqLen_real (v : Fin 2 → ℤ) : (sqLen v : ℝ) = Complex.normSq (cx v) := by
  rw [normSq_cx]
  have := congrArg (Int.cast : ℤ → ℝ) (sqLen_cast v)
  push_cast at this
  rw [this]; ring

section Cusp

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

theorem codim_pos (D : ComponentData II Ψ K J Ω E) : 1 ≤ D.N - D.j := by
  have := D.j_le; have := D.two_le_N; omega

def scaledCusp (D : ComponentData II Ψ K J Ω E) (l : ((Σ k, J k) → ℂ) → ℝ)
    (hl : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → l (torusSmul c z) = l z) :
    CuspData D ℤ (Fin 2 → ℤ) where
  rank := 2
  basis := Pi.basisFun ℤ (Fin 2)
  form := sympForm
  alt v := by rw [sympForm_apply]; ring
  unimod := by
    have : (Matrix.of fun a b => sympForm (Pi.basisFun ℤ (Fin 2) a) (Pi.basisFun ℤ (Fin 2) b)).det = 1 := by
      rw [Matrix.det_fin_two]
      simp [sympForm_apply]
    rw [this]
    exact isUnit_one
  emb _ := Int.castRingHom ℂ
  normSq z v := (1 + (Fintype.card Ψ : ℝ) * ((D.N - D.j : ℕ) : ℝ) * Real.exp (l z) ^ 2) *
    Complex.normSq (cx v)
  normSq_pos _ _ v hv := mul_pos (by positivity)
    (Complex.normSq_pos.2 fun h => hv (cx_injective h))
  form_le z _ v w := by
    have h1 : ((sympForm v w : ℤ) : ℝ) ^ 2 ≤ Complex.normSq (cx v) * Complex.normSq (cx w) := by
      rw [sympForm_apply, normSq_cx, normSq_cx]
      push_cast
      nlinarith [sq_nonneg ((v 0 : ℝ) * w 0 + v 1 * w 1)]
    have h2 : 0 ≤ (Fintype.card Ψ : ℝ) * ((D.N - D.j : ℕ) : ℝ) * Real.exp (l z) ^ 2 := by positivity
    refine h1.trans (mul_le_mul ?_ ?_ (Complex.normSq_nonneg _) ?_)
    · nlinarith [Complex.normSq_nonneg (cx v)]
    · nlinarith [Complex.normSq_nonneg (cx w)]
    · exact mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  lie z _ v _ := (Real.exp (l z) : ℂ) * cx v
  lie_add _ _ v w := by funext c; simp [cx_add, mul_add]
  lie_smul _ _ a v := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, cx_smul, eq_intCast]
    ring
  lie_le z _ v := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.sq_norm]
    nlinarith [Complex.normSq_nonneg (cx v)]
  inj z _ τ I hI ρ v hv hli := by
    have hρ := card_le_one hI hv hli
    haveI : Subsingleton (Fin ρ) := Fin.subsingleton_iff_le_one.2 hρ
    refine (linearIndependent_subsingleton_index_iff _).2 fun a h => ?_
    have h0 := congrFun h ⟨0, codim_pos D⟩
    simp only [Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero, Real.exp_ne_zero, false_or] at h0
    exact hli.ne_zero a (cx_injective h0)
  torus z hz c hc := by
    constructor
    · funext v; simp only [hl z hz c hc]
    · funext τ v c'; simp only [hl z hz c hc]

theorem scaledCusp_Nz [Nonempty Ψ] (D : ComponentData II Ψ K J Ω E) {I : Submodule ℤ (Fin 2 → ℤ)} (hI0 : I ≠ ⊥)
    (hI : IsIsoSub sympForm I) : ∃ c : ℝ, 1 ≤ c ∧ ∀ l hl z,
      (scaledCusp D l hl).Nz z I = Real.exp (l z) ^ (2 * Fintype.card Ψ) * c := by
  classical
  obtain ⟨v, hvI, hv⟩ := (Submodule.ne_bot_iff I).1 hI0
  have hex : ∃ ρ v, IsNzFamily I ρ v := by
    refine ⟨1, fun _ => v, le_rfl, fun _ => hvI, linearIndependent_unique_iff.2 hv, ?_⟩
    rw [Set.range_const]
    exact (relIndex_span_le hI hvI hv).1
  have key : ∀ (ρ : ℕ) (u : Fin ρ → Fin 2 → ℤ), IsNzFamily I ρ u → ∃ c : ℝ, 1 ≤ c ∧ ∀ l hl z,
      (∏ τ, ((scaledCusp D l hl).gramLie z τ u).det.re) /
        ((Submodule.span ℤ (Set.range u)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) =
      Real.exp (l z) ^ (2 * Fintype.card Ψ) * c := by
    rintro ρ u ⟨h1, h2, h3, -⟩
    obtain rfl : ρ = 1 := le_antisymm (card_le_one hI h2 h3) h1
    have hu := h3.ne_zero 0
    obtain ⟨hi0, hi⟩ := relIndex_span_le hI (h2 0) hu
    have hr : Set.range u = {u 0} := by rw [Set.range_unique]; rfl
    rw [hr]
    set m := (Submodule.span ℤ {u 0}).toAddSubgroup.relIndex I.toAddSubgroup
    have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hi0
    have hN := sqLen_real (u 0)
    refine ⟨(((D.N - D.j : ℕ) : ℝ) * sqLen (u 0)) ^ Fintype.card Ψ / m, ?_, fun l hl z => ?_⟩
    · rw [one_le_div hm]
      have a1 : (m : ℝ) ≤ sqLen (u 0) := by exact_mod_cast hi
      have a2 : (1 : ℝ) ≤ ((D.N - D.j : ℕ) : ℝ) := by exact_mod_cast codim_pos D
      have a3 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero hi0
      have a4 : (sqLen (u 0) : ℝ) ≤ ((D.N - D.j : ℕ) : ℝ) * sqLen (u 0) := by nlinarith
      exact a1.trans (a4.trans (le_self_pow₀ (by linarith) Fintype.card_ne_zero))
    · have hg : ∀ τ, ((scaledCusp D l hl).gramLie z τ u).det.re =
          Real.exp (l z) ^ 2 * (((D.N - D.j : ℕ) : ℝ) * sqLen (u 0)) := by
        intro τ
        rw [Matrix.det_fin_one, hN]
        simp only [CuspData.gramLie, scaledCusp, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_mul, Complex.normSq_ofReal,
          ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
        ring
      simp only [hg, Finset.prod_const, Finset.card_univ, mul_pow, ← pow_mul]
      ring
  obtain ⟨c, hc, h⟩ := key _ _ hex.choose_spec.choose_spec
  exact ⟨c, hc, fun l hl z => by rw [CuspData.Nz, dif_pos hex]; exact h l hl z⟩

theorem exists_iso_line : ∃ I : Submodule ℤ (Fin 2 → ℤ), I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub sympForm I := by
  refine ⟨LinearMap.ker (sympForm ![1, 0]), ?_, ?_, ?_⟩
  · refine (Submodule.ne_bot_iff _).2 ⟨![1, 0], ?_, ?_⟩
    · simp [sympForm_apply]
    · intro h
      simpa using congrFun h 0
  · intro v n hn h
    rw [LinearMap.mem_ker, map_zsmul, smul_eq_zero] at h
    exact h.resolve_left hn
  · intro v hv w hw
    rw [LinearMap.mem_ker, sympForm_apply] at hv hw
    simp at hv hw
    simp [sympForm_apply, hv, hw]

theorem exists_cusp_of_weight [Nonempty Ψ] (D : ComponentData II Ψ K J Ω E) (U : ((Σ k, J k) → ℂ) → ℝ)
    (hU0 : ∀ z, 0 ≤ U z) (hU : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) :
    ∃ Cd : CuspData D ℤ (Fin 2 → ℤ), Cd.cuspWeight = U := by
  classical
  have hf : (0 : ℝ) < 2 * Fintype.card Ψ := by
    have : (0 : ℝ) < Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
    linarith
  let C0 := scaledCusp D (fun _ => 0) (fun _ _ _ _ => rfl)
  let T : Set ℝ := {x | ∃ I : Submodule ℤ (Fin 2 → ℤ), I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub sympForm I ∧
    x = -Real.log (C0.Nz 0 I)}
  have hTne : T.Nonempty := by
    obtain ⟨I, h1, h2, h3⟩ := exists_iso_line
    exact ⟨_, I, h1, h2, h3, rfl⟩
  have hTb : BddAbove T := by
    refine ⟨0, ?_⟩
    rintro x ⟨I, h1, -, h3, rfl⟩
    obtain ⟨c, hc, h⟩ := scaledCusp_Nz D h1 h3
    simp only [C0, h, Real.exp_zero, one_pow, _root_.one_mul]
    linarith [Real.log_nonneg hc]
  let l : ((Σ k, J k) → ℂ) → ℝ := fun z => (sSup T - U z) / (2 * Fintype.card Ψ)
  have hl : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → l (torusSmul c z) = l z :=
    fun z hz c hc => by simp only [l, hU z hz c hc]
  have hlog : ∀ z (I : Submodule ℤ (Fin 2 → ℤ)), I ≠ ⊥ → IsIsoSub sympForm I →
      -Real.log ((scaledCusp D l hl).Nz z I) = (U z - sSup T) + -Real.log (C0.Nz 0 I) := by
    intro z I h1 h3
    obtain ⟨c, hc, h⟩ := scaledCusp_Nz D h1 h3
    simp only [C0, h, Real.exp_zero, one_pow, _root_.one_mul]
    rw [Real.log_mul (by positivity) (by linarith), Real.log_pow, Real.log_exp]
    simp only [l]
    push_cast
    field_simp
    ring
  have hset : ∀ z, {x | ∃ I : Submodule ℤ (Fin 2 → ℤ), I ≠ ⊥ ∧ IsSaturated I ∧
      IsIsoSub (scaledCusp D l hl).form I ∧ x = -Real.log ((scaledCusp D l hl).Nz z I)} =
      (fun x => (U z - sSup T) + x) '' T := by
    intro z
    ext x
    constructor
    · rintro ⟨I, h1, h2, h3, rfl⟩
      exact ⟨_, ⟨I, h1, h2, h3, rfl⟩, (hlog z I h1 h3).symm⟩
    · rintro ⟨_, ⟨I, h1, h2, h3, rfl⟩, rfl⟩
      exact ⟨I, h1, h2, h3, (hlog z I h1 h3).symm⟩
  refine ⟨scaledCusp D l hl, funext fun z => ?_⟩
  have h := (OrderIso.addLeft (U z - sSup T)).map_csSup' hTne hTb
  have h' : sSup ((fun x => (U z - sSup T) + x) '' T) = U z := by
    refine h.symm.trans ?_
    simp
  rw [CuspData.cuspWeight, hset, h', max_eq_right (hU0 z)]

end Cusp

theorem every_weight_is_cusp_weight : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) [Nonempty Ψ] (U : ((Σ k, J k) → ℂ) → ℝ), (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → ∃ Cd : CuspData D ℤ (Fin 2 → ℤ), Cd.cuspWeight = U :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ D _ U hU0 hU => exists_cusp_of_weight D U hU0 hU

end GlobalTheory.CompanionTheory.Ar.Cusp.Fake
