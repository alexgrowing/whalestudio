import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OfRealVecHalfVec
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem eq_of_finite_modular_family {F : Set (ℍ → ℂ)} (hF : F.Finite)
    (hol : ∀ f ∈ F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (bdd : ∀ f ∈ F, UpperHalfPlane.IsBoundedAtImInfty f)
    (hS : ∀ f ∈ F, (fun z => f (ModularGroup.S • z)) ∈ F)
    (hT : ∀ f ∈ F, (fun z => f (ModularGroup.T • z)) ∈ F)
    {f : ℍ → ℂ} (hf : f ∈ F) (z w : ℍ) : f z = f w := by
  have key : ∀ X : ℂ, ∃ c, (∏ f ∈ hF.toFinset, (fun z => X - f z) : ℍ → ℂ) =
      Function.const _ c := by
    intro X
    set P : ℍ → ℂ := ∏ f ∈ hF.toFinset, (fun z => X - f z) with hP
    have hγ : ∀ γ : SL(2, ℤ), (∀ f ∈ F, (fun z => f (γ • z)) ∈ F) → P ∣[(0 : ℤ)] γ = P := by
      intro γ hγ
      have hinj : Function.Injective fun (f : ℍ → ℂ) (z : ℍ) => f (γ • z) := by
        intro f f' h
        funext z
        simpa using congrFun h (γ⁻¹ • z)
      have hb : Set.BijOn (fun (f : ℍ → ℂ) (z : ℍ) => f (γ • z)) F F :=
        (hF.injOn_iff_bijOn_of_mapsTo hγ).1 hinj.injOn
      ext z
      rw [ModularForm.SL_slash_apply]
      simp only [neg_zero, zpow_zero, mul_one, hP, Finset.prod_apply]
      exact Finset.prod_nbij (fun (f : ℍ → ℂ) (z : ℍ) => f (γ • z))
        (fun f hf => by simpa using hγ f (by simpa using hf)) hinj.injOn
        (by simpa using hb.surjOn) (fun f _ => rfl)
    have hs := SlashInvariantForm.slash_action_generators_SL2Z (hγ _ hS) (hγ _ hT)
    have hb : UpperHalfPlane.IsBoundedAtImInfty P := by
      refine Filter.BoundedAtFilter.prod _ fun f hf => ?_
      exact Asymptotics.IsBigO.sub (Filter.const_boundedAtFilter _ X) (bdd f (by simpa using hf))
    let M : ModularForm 𝒮ℒ 0 :=
      { toFun := P
        slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hs γ
        holo' := by
          refine Finset.prod_induction _ (fun f : ℍ → ℂ => MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
            (fun a b ha hb => ha.mul hb) mdifferentiable_const fun f hf => ?_
          exact mdifferentiable_const.sub (hol f (by simpa using hf))
        bdd_at_cusps' := fun {c} hc ↦ by
          rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
          rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
          intro γ _
          rw [hs γ]
          exact hb }
    exact ModularFormClass.levelOne_weight_zero_const M
  have hfin : ((fun f : ℍ → ℂ => f UpperHalfPlane.I) '' F).Finite := hF.image _
  refine isPreconnected_univ.constant_of_mapsTo hfin.isDiscrete
    (hol f hf).continuous.continuousOn (fun t _ => ?_) (Set.mem_univ z) (Set.mem_univ w)
  obtain ⟨c, hc⟩ := key (f t)
  have h1 := congrFun hc t
  have h2 := congrFun hc UpperHalfPlane.I
  simp only [Finset.prod_apply, Function.const_apply] at h1 h2
  rw [Finset.prod_eq_zero (f := fun c : ℍ → ℂ => f t - c t) (hF.mem_toFinset.2 hf) (sub_self _)]
    at h1
  obtain ⟨f', hf', h⟩ := Finset.prod_eq_zero_iff.1 (h2.trans h1.symm)
  exact ⟨f', hF.mem_toFinset.1 hf', (sub_eq_zero.1 h).symm⟩

variable {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ → ℂ}

theorem spInvariant_transl (hH : IsSpInvariant g H) {B : Matrix (Fin g) (Fin g) ℤ} (hB : B.IsSymm)
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    H (τ + B.map (Int.cast : ℤ → ℂ)) = H τ := by
  rw [← spAct_spTransl]
  exact hH _ (spTransl_mem_sp hB) τ hτ

theorem spAct_spDiag_eq (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    spAct (spDiag U) τ = (U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ) * τ *
      ((U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ))ᵀ := by
  rw [spAct_eq, jAut_spDiag_inv, nAut_eq, cMat_spDiag]
  simp

theorem spInvariant_conj (hH : IsSpInvariant g H) (U : (Matrix (Fin g) (Fin g) ℤ)ˣ)
    {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    H ((U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ) * τ *
      ((U : Matrix (Fin g) (Fin g) ℤ).map (Int.cast : ℤ → ℂ))ᵀ) = H τ := by
  rw [← spAct_spDiag_eq]
  exact hH _ (spDiag_mem_sp U) τ hτ

theorem spInvariant_partialInv (hH : IsSpInvariant g H) (e : Fin g)
    {τ σ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g))
    (h : ∀ i k, σ i k - σ i e * (τ e k + if e = k then 1 else 0) =
      τ i k + if i = e then (if e = k then 1 else 0) - τ e k else 0) : H σ = H τ := by
  have hm := spH_le g (spPJ_mem e)
  have hj := jAut_isUnit hm hτ
  have : σ * jAut (spPJ e) τ = nAut (spPJ e) τ := by
    have e1 : jAut (spPJ e) τ = 1 - single e e (1 : ℂ) * (τ + 1) := by
      ext i k
      by_cases hi : e = i <;> simp [jAut_eq, cMat, spPJ, toBlocks₂₁, toBlocks₂₂, mul_apply,
        one_apply, single_apply, ite_and, hi]
    have e2 : nAut (spPJ e) τ = τ + single e e (1 : ℂ) * (1 - τ) := by
      ext i k
      by_cases hi : e = i <;> simp [nAut_eq, cMat, spPJ, toBlocks₁₁, toBlocks₁₂, mul_apply,
        one_apply, single_apply, ite_and, hi]
    ext i k
    rw [e1, e2, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
    have := h i k
    by_cases hi : i = e
    · subst hi
      simpa [mul_apply, single_apply, ite_and, one_apply] using this
    · simpa [mul_apply, single_apply, ite_and, one_apply, hi, Ne.symm hi] using this
  have e2 : σ = spAct (spPJ e) τ := by
    rw [spAct_eq, ← this, Matrix.mul_nonsing_inv_cancel_right _ _ hj]
  rw [e2]
  exact hH _ hm τ hτ

def rankOneCurve (Z : Matrix (Fin g) (Fin g) ℂ) (R : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℝ)
    (s : ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  of fun i j => Z i j + R i j + s * u i * u j

theorem rankOneCurve_map_im (Z : Matrix (Fin g) (Fin g) ℂ) (R : Matrix (Fin g) (Fin g) ℝ)
    (u : Fin g → ℝ) (s : ℂ) :
    (rankOneCurve Z R u s).map Complex.im = Z.map Complex.im + s.im • vecMulVec u u := by
  ext i j
  simp [rankOneCurve, vecMulVec_apply, mul_assoc]

section Curve

variable {e : Fin g} {Z : Matrix (Fin g) (Fin g) ℂ} (hZs : Z.IsSymm) (hZe : ∀ i, Z i e = 0)
  (hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
    (Z.map Complex.im + y • vecMulVec u u).PosDef)

include hZs hZ in
theorem rankOneCurve_mem {R : Matrix (Fin g) (Fin g) ℝ} (hR : R.IsSymm) {u : Fin g → ℝ}
    (hu : u e = 1) {s : ℂ} (hs : 0 < s.im) : rankOneCurve Z R u s ∈ SiegelH (Fin g) := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [rankOneCurve, transpose_apply, of_apply, hZs.apply i j, hR.apply i j]
    ring
  · rw [rankOneCurve_map_im]
    exact hZ u hu _ hs

theorem finite_abs_le_one_mul_mem_range {c : ℝ} (hc : c ≠ 0) :
    {x : ℝ | |x| ≤ 1 ∧ c * x ∈ (Int.castRingHom ℝ).range}.Finite := by
  refine ((Set.finite_Icc (-⌈|c|⌉) ⌈|c|⌉).image fun k : ℤ => (k : ℝ) / c).subset ?_
  rintro x ⟨hx, k, hk⟩
  have hk' : (k : ℝ) = c * x := hk
  refine ⟨k, ?_, by simp only [hk']; field_simp⟩
  have h1 : |(k : ℝ)| ≤ (⌈|c|⌉ : ℤ) := by
    rw [hk', abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg c) hx).trans (Int.le_ceil _)
  exact abs_le.1 (by exact_mod_cast h1)

include hZs hZe hZ in

theorem eq_on_rankOneCurve_of_integral (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {N : ℕ} (hN : N ≠ 0) {R : Matrix (Fin g) (Fin g) ℝ} {u : Fin g → ℝ} (hu : u e = 1)
    (hR : R.IsSymm) (hRe : R e e = 0) (huN : ∀ i, N * u i ∈ (Int.castRingHom ℝ).range)
    (hRN : ∀ i, N * R i e ∈ (Int.castRingHom ℝ).range)
    (hRN2 : ∀ i j, N * N * R i j ∈ (Int.castRingHom ℝ).range) (z w : ℍ) :
    H (rankOneCurve Z R u z) = H (rankOneCurve Z R u w) := by
  set A := (Int.castRingHom ℝ).range with hA
  let ε : Fin g → ℝ := fun i => if i = e then 1 else 0
  have hεe : ε e = 1 := if_pos rfl
  have hε : ∀ i, ε i ∈ A := fun i => by
    by_cases h : i = e <;> simp [ε, h]
  have hNA : (N : ℝ) ∈ A := natCast_mem A N
  let F : Set (ℍ → ℂ) := {f | ∃ (R : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℝ), u e = 1 ∧
    R.IsSymm ∧ R e e = 0 ∧ (∀ i, N * u i ∈ A) ∧ (∀ i, N * R i e ∈ A) ∧
    (∀ i j, N * N * R i j ∈ A) ∧ f = fun z : ℍ => H (rankOneCurve Z R u z)}
  refine eq_of_finite_modular_family (F := F) ?_ ?_ ?_ ?_ ?_
    ⟨R, u, hu, hR, hRe, huN, hRN, hRN2, rfl⟩ z w
  · have hfin := finite_abs_le_one_mul_mem_range (c := (N * N : ℝ)) (by positivity)
    refine (((Set.Finite.pi' fun _ : Fin g => Set.Finite.pi' fun _ : Fin g => hfin).prod
      (Set.Finite.pi' fun _ : Fin g => hfin)).image
        fun p (z : ℍ) => H (rankOneCurve Z (of p.1) p.2 z)).subset ?_
    rintro _ ⟨R, u, hu, hR, hRe, huN, hRN, hRN2, rfl⟩
    let k : Fin g → ℤ := fun i => if i = e then 0 else ⌊u i⌋
    have hke : k e = 0 := if_pos rfl
    have hk : ∀ i, (k i : ℝ) ∈ A := fun i => intCast_mem A _
    let R₁ : Matrix (Fin g) (Fin g) ℝ := of fun i j => R i j - (k i * R j e + R i e * k j)
    have hR₁ : R₁.IsSymm := by
      ext i j
      simp only [R₁, transpose_apply, of_apply, hR.apply i j]
      ring
    refine ⟨(fun i j => Int.fract (R₁ i j), fun i => u i - k i), ⟨fun i j => ⟨?_, ?_⟩,
      fun i => ⟨?_, ?_⟩⟩, funext fun z => ?_⟩
    · exact abs_le.2 ⟨by linarith [Int.fract_nonneg (R₁ i j)], (Int.fract_lt_one _).le⟩
    · have : N * N * Int.fract (R₁ i j) = N * N * R i j - (N * k i * (N * R j e) +
          N * R i e * (N * k j)) - N * N * ⌊R₁ i j⌋ := by
        simp only [Int.fract, R₁, of_apply]
        ring
      simp only [this]
      exact sub_mem (sub_mem (hRN2 i j) (add_mem (mul_mem (mul_mem hNA (hk i)) (hRN j))
        (mul_mem (hRN i) (mul_mem hNA (hk j))))) (mul_mem (mul_mem hNA hNA) (intCast_mem A _))
    · by_cases h : i = e
      · simp [h, hu, hke]
      · simp only [k, if_neg h]
        exact abs_le.2 ⟨by linarith [Int.floor_le (u i)], by linarith [Int.lt_floor_add_one (u i)]⟩
    · simp only [mul_sub, mul_assoc]
      exact sub_mem (mul_mem hNA (huN i)) (mul_mem hNA (mul_mem hNA (hk i)))
    · have h1 := spInvariant_conj hH (rkU (-k) (Pi.single e 1) (by simp [hke]))
        (rankOneCurve_mem hZs hZ hR hu z.im_pos)
      have hfs : (of fun i j => Int.fract (R₁ i j)).IsSymm := by
        ext i j
        simp only [transpose_apply, of_apply, hR₁.apply i j]
      have h2 := spInvariant_transl hH (B := R₁.map Int.floor) (hR₁.map _)
        (rankOneCurve_mem hZs hZ hfs (u := fun i => u i - k i) (by simp [hu, hke]) z.im_pos)
      simp only
      rw [← h1, ← h2]
      congr 1
      ext i j
      have h3 : ((Int.fract (R₁ i j) : ℝ) : ℂ) = R₁ i j - (⌊R₁ i j⌋ : ℤ) := by
        rw [Int.fract]
        push_cast
        rfl
      have hZe' : ∀ i, Z e i = 0 := fun i => (hZs.apply i e).trans (hZe i)
      simp only [rkU_val, mul_apply, map_apply, Matrix.add_apply, transpose_apply, rankOneCurve,
        of_apply, h3]
      simp [one_apply, vecMulVec_apply, Pi.single_apply, add_mul, mul_add, Finset.sum_add_distrib,
        hZe, hZe', hu, hRe, R₁, hR.apply j e]
      ring
  · rintro _ ⟨R, u, hu, hR, -, -, -, -, rfl⟩
    rw [UpperHalfPlane.mdifferentiable_iff]
    have hd : Differentiable ℂ fun s : ℂ => (of.symm (rankOneCurve Z R u s) : Fin g → Fin g → ℂ) := by
      refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
      simp only [rankOneCurve, of_symm_apply, of_apply]
      fun_prop
    refine (hol.comp hd.differentiableOn fun s (hs : 0 < s.im) =>
      of_symm_mem_phDom (rankOneCurve_mem hZs hZ hR hu hs)).congr fun s hs => ?_
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hs,
      Equiv.apply_symm_apply, phSym_eq_self_of_isSymm (rankOneCurve_mem hZs hZ hR hu hs).1]
  · rintro _ ⟨R, u, hu, hR, -, -, -, -, rfl⟩
    obtain ⟨c, hc, hle⟩ := posDef_exists_mul_dotProduct_le (hZ u hu 1 one_pos)
    obtain ⟨K, hK⟩ := hb c hc
    refine UpperHalfPlane.isBoundedAtImInfty_iff.2 ⟨K, 1, fun z hz =>
      hK _ (rankOneCurve_mem hZs hZ hR hu z.im_pos) ?_⟩
    have h1 : (Z.map Complex.im + (1 : ℝ) • vecMulVec u u -
        c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef := by
      refine posSemidef_iff_dotProduct_mulVec.2 ⟨(hZ u hu 1 one_pos).1.sub ?_, fun x => ?_⟩
      · simp [IsHermitian]
      · rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul]
        simpa using hle x
    have h2 := (posSemidef_vecMulVec_self_star u).smul (sub_nonneg.2 hz)
    convert h1.add h2 using 1
    rw [rankOneCurve_map_im]
    simp only [star_trivial, UpperHalfPlane.coe_im]
    module
  · rintro _ ⟨R, u, hu, hR, hRe, huN, hRN, hRN2, rfl⟩
    have hR' : (of fun i j => R i j - u i * (ε j + R j e) - (ε i + R i e) * u j +
        2 * (ε i * ε j)).IsSymm := by
      ext i j
      simp only [transpose_apply, of_apply, hR.apply i j]
      ring
    refine ⟨_, fun i => ε i + R i e, by simp [hεe, hRe], hR', by simp [hεe, hRe, hu]; ring,
      fun i => ?_, fun i => ?_, fun i j => ?_, funext fun z => ?_⟩
    · rw [mul_add]
      exact add_mem (mul_mem hNA (hε i)) (hRN i)
    · convert sub_mem (mul_mem hNA (hε i)) (huN i) using 1
      simp only [of_apply, hεe, hRe, hu]
      ring
    · convert add_mem (sub_mem (sub_mem (hRN2 i j)
        (mul_mem (huN i) (add_mem (mul_mem hNA (hε j)) (hRN j))))
        (mul_mem (add_mem (mul_mem hNA (hε i)) (hRN i)) (huN j)))
        (mul_mem (natCast_mem A 2) (mul_mem (mul_mem hNA (hε i)) (mul_mem hNA (hε j)))) using 1
      simp only [of_apply]
      push_cast
      ring
    · symm
      refine spInvariant_partialInv hH e
        (rankOneCurve_mem hZs hZ hR hu (ModularGroup.S • z).im_pos) fun i k => ?_
      have hZe' : ∀ i, Z e i = 0 := fun i => (hZs.apply i e).trans (hZe i)
      have hz := z.ne_zero
      simp only [rankOneCurve, of_apply, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
        hZe, hZe', hεe, hu, hRe, hR.apply k e]
      by_cases hi : i = e <;> by_cases hk : k = e <;>
        simp [ε, hi, hk, eq_comm (a := e), hZe, hZe', hu, hRe, hR.apply k e] <;>
        field_simp <;> ring
  · rintro _ ⟨R, u, hu, hR, hRe, huN, hRN, hRN2, rfl⟩
    have hR' : (of fun i j => R i j + u i * u j - ε i * ε j).IsSymm := by
      ext i j
      simp only [transpose_apply, of_apply, hR.apply i j]
      ring
    refine ⟨_, u, hu, hR', by simp [hεe, hRe, hu], huN, fun i => ?_, fun i j => ?_,
      funext fun z => ?_⟩
    · convert sub_mem (add_mem (hRN i) (huN i)) (mul_mem hNA (hε i)) using 1
      simp only [of_apply, hεe, hu]
      ring
    · convert sub_mem (add_mem (hRN2 i j) (mul_mem (huN i) (huN j)))
        (mul_mem (mul_mem hNA (hε i)) (mul_mem hNA (hε j))) using 1
      simp only [of_apply]
      ring
    · rw [← spInvariant_transl hH (eJ_symm e) (rankOneCurve_mem hZs hZ hR' hu z.im_pos)]
      refine congrArg H ?_
      ext i j
      simp only [rankOneCurve, of_apply, UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd,
        Matrix.add_apply, map_apply, eJ_apply]
      by_cases hi : i = e <;> by_cases hj : j = e <;> simp [ε, hi, hj, eq_comm (a := e)] <;> ring

theorem tendsto_floor_nat_mul_div (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (⌊(n + 1 : ℝ) * x⌋ : ℝ) / (n + 1)) Filter.atTop (𝓝 x) := by
  have h := (tendsto_const_nhds (x := x)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds (fun n => ?_) fun n => ?_
  · have hn : (0 : ℝ) < n + 1 := by positivity
    simp only
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn]
    linarith [Int.lt_floor_add_one ((n + 1 : ℝ) * x)]
  · have hn : (0 : ℝ) < n + 1 := by positivity
    simp only
    rw [div_le_iff₀ hn]
    linarith [Int.floor_le ((n + 1 : ℝ) * x)]

include hZs hZe hZ in

theorem eq_on_rankOneCurve (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {u v : Fin g → ℝ} (hu : u e = 1) (hv : v e = 0) (z w : ℍ) :
    H (rankOneCurve Z (vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)) u z) =
      H (rankOneCurve Z (vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)) u w) := by
  let R : (Fin g → ℝ) → Matrix (Fin g) (Fin g) ℝ := fun v =>
    vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)
  have hR : ∀ v, (R v).IsSymm := fun v => by
    ext i j
    simp only [R, transpose_apply, Matrix.add_apply, vecMulVec_apply]
    ring
  let a : (Fin g → ℝ) → ℕ → Fin g → ℝ := fun x n i => (⌊(n + 1 : ℝ) * x i⌋ : ℝ) / (n + 1)
  have hau : ∀ n, a u n e = 1 := fun n => by
    have : ⌊(n + 1 : ℝ)⌋ = n + 1 := by exact_mod_cast Int.floor_intCast (R := ℝ) (n + 1)
    simp only [a, hu, mul_one, this]
    push_cast
    exact div_self (by positivity)
  have hav : ∀ n, a v n e = 0 := fun n => by simp [a, hv]
  have ha : ∀ x (n : ℕ) i, ((n + 1 : ℕ) : ℝ) * a x n i ∈ (Int.castRingHom ℝ).range := by
    intro x n i
    refine ⟨⌊(n + 1 : ℝ) * x i⌋, ?_⟩
    simp only [a, eq_intCast]
    push_cast
    field_simp
  have hε : ∀ i, (Pi.single e 1 : Fin g → ℝ) i ∈ (Int.castRingHom ℝ).range := fun i => by
    by_cases h : i = e <;> simp [h]
  have hlim : ∀ z : ℍ, Filter.Tendsto (fun n => H (rankOneCurve Z (R (a v n)) (a u n) z))
      Filter.atTop (𝓝 (H (rankOneCurve Z (R v) u z))) := by
    intro z
    have hm := rankOneCurve_mem hZs hZ (hR v) hu z.im_pos
    have hc : Continuous fun p : (Fin g → ℝ) × (Fin g → ℝ) =>
        (of.symm (rankOneCurve Z (R p.1) p.2 z) : Fin g → Fin g → ℂ) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [rankOneCurve, of_symm_apply, of_apply, R, Matrix.add_apply, vecMulVec_apply]
      fun_prop
    have h1 : Filter.Tendsto (fun n => (a v n, a u n)) Filter.atTop (𝓝 (v, u)) :=
      (tendsto_pi_nhds.2 fun i => tendsto_floor_nat_mul_div _).prodMk_nhds
        (tendsto_pi_nhds.2 fun i => tendsto_floor_nat_mul_div _)
    have h2 := (hol.continuousOn.continuousAt
      ((isOpen_phDom g).mem_nhds (of_symm_mem_phDom hm))).tendsto.comp
      ((hc.tendsto (v, u)).comp h1)
    simp only [Equiv.apply_symm_apply, phSym_eq_self_of_isSymm hm.1] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, Equiv.apply_symm_apply,
      phSym_eq_self_of_isSymm (rankOneCurve_mem hZs hZ (hR _) (hau n) z.im_pos).1]
  refine tendsto_nhds_unique (hlim z) ((hlim w).congr fun n => ?_)
  refine eq_on_rankOneCurve_of_integral hZs hZe hZ hol hH hb (Nat.succ_ne_zero n) (hau n) (hR _)
    (by simp [R, vecMulVec_apply, hav]) (ha u n) (fun i => ?_) (fun i j => ?_) w z
  · simpa [R, vecMulVec_apply, hav] using ha v n i
  · convert mul_mem (natCast_mem _ (n + 1))
      (add_mem (mul_mem (hε i) (ha v n j)) (mul_mem (ha v n i) (hε j))) using 1
    simp only [R, Matrix.add_apply, vecMulVec_apply]
    ring

end Curve

theorem posDef_sub_vecMulVec_add {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) (e : Fin g)
    {u : Fin g → ℝ} (hu : u e = 1) {y : ℝ} (hy : 0 < y) :
    (Y - (Y e e)⁻¹ • vecMulVec (fun i => Y i e) (fun i => Y i e) + y • vecMulVec u u).PosDef := by
  have hs : ∀ i j, Y j i = Y i j := fun i j => by simpa using hY.1.apply i j
  have he : 0 < Y e e := hY.diag_pos
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp [vecMulVec_apply, hs i j, mul_comm]
  · set a : ℝ := x ⬝ᵥ fun i => Y i e with ha
    have h1 : Y *ᵥ Pi.single e 1 = fun i => Y i e := by
      ext i
      simp
    have h2 : Pi.single e 1 ⬝ᵥ Y *ᵥ x = a := by
      rw [single_dotProduct]
      simp [ha, mulVec, dotProduct, hs e, mul_comm]
    set x' := x - (a / Y e e) • (Pi.single e 1 : Fin g → ℝ) with hx'
    have h3 : star x ⬝ᵥ (Y - (Y e e)⁻¹ • vecMulVec (fun i => Y i e) (fun i => Y i e) +
        y • vecMulVec u u) *ᵥ x = x' ⬝ᵥ Y *ᵥ x' + y * (x ⬝ᵥ u) ^ 2 := by
      simp only [star_trivial, add_mulVec, sub_mulVec, smul_mulVec, vecMulVec_mulVec, hx',
        mulVec_sub, mulVec_smul, dotProduct_add, dotProduct_sub, sub_dotProduct, dotProduct_smul,
        smul_dotProduct, h1, h2, single_dotProduct, op_smul_eq_smul, smul_eq_mul,
        dotProduct_comm _ x, ← ha]
      field_simp
      ring
    rw [h3]
    by_cases h0 : x' = 0
    · have h4 : x = (a / Y e e) • (Pi.single e 1 : Fin g → ℝ) := sub_eq_zero.1 h0
      have h5 : a / Y e e ≠ 0 := fun h => hx (by rw [h4, h, zero_smul])
      have h6 : x ⬝ᵥ u = a / Y e e := by
        rw [h4]
        simp [hu]
      rw [h0, h6, zero_dotProduct, zero_add]
      positivity
    · have := hY.dotProduct_mulVec_pos h0
      rw [star_trivial] at this
      positivity

theorem eventually_eq_column (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    (e : Fin g) {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    ∀ᶠ s in 𝓝 (0 : ℂ), H (τ + s • vecMulVec (fun i => ((τ i e).im : ℂ))
      (fun i => ((τ i e).im : ℂ))) = H τ := by
  have he : 0 < (τ e e).im := hτ.2.diag_pos (i := e)
  let u : Fin g → ℝ := fun i => (τ i e).im / (τ e e).im
  let v : Fin g → ℝ := fun i => (τ i e).re - (τ e e).re * u i
  have hu : u e = 1 := div_self he.ne'
  have hv : v e = 0 := by simp [v, hu]
  let R : Matrix (Fin g) (Fin g) ℝ := vecMulVec (Pi.single e 1) v + vecMulVec v (Pi.single e 1)
  let Z : Matrix (Fin g) (Fin g) ℂ := of fun i j => τ i j - R i j - τ e e * u i * u j
  have hZs : Z.IsSymm := by
    ext i j
    simp only [Z, R, transpose_apply, of_apply, Matrix.add_apply, vecMulVec_apply, hτ.1.apply i j]
    push_cast
    ring
  have hZe : ∀ i, Z i e = 0 := fun i => by
    apply Complex.ext
    · simp [Z, R, vecMulVec_apply, hu, v]
    · simp [Z, hu]
      simp only [u]
      field_simp
      ring
  have hZ : ∀ u : Fin g → ℝ, u e = 1 → ∀ y : ℝ, 0 < y →
      (Z.map Complex.im + y • vecMulVec u u).PosDef := fun u' hu' y hy => by
    convert posDef_sub_vecMulVec_add hτ.2 e hu' hy using 2
    ext i j
    simp [Z, vecMulVec_apply]
    simp only [u]
    field_simp
  have hc : Continuous fun s : ℂ => (τ e e + s * (τ e e).im ^ 2).im := by fun_prop
  filter_upwards [continuousAt_const.eventually_lt hc.continuousAt
    (show (0 : ℝ) < _ by simpa using he)] with s hs
  convert eq_on_rankOneCurve hZs hZe hZ hol hH hb hu hv ⟨_, hs⟩ ⟨_, he⟩ using 2
  · ext i j
    have : ((τ e e).im : ℂ) ≠ 0 := by exact_mod_cast he.ne'
    simp [rankOneCurve, Z, R, vecMulVec_apply]
    simp only [u]
    push_cast
    field_simp
    ring
  · ext i j
    simp [rankOneCurve, Z, R]
    ring

theorem fderiv_vecMulVec_eq_zero (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (e : Fin g) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) :
    fderiv ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (of x))) (of.symm τ)
      (of.symm (vecMulVec (imC τ *ᵥ fun l => (U.val e l : ℂ))
        (imC τ *ᵥ fun l => (U.val e l : ℂ)))) = 0 := by
  set w := imC τ *ᵥ fun l => (U.val e l : ℂ) with hw
  have hτ' := spAct_mem (spDiag_mem_sp U) hτ
  have h1 := eventually_eq_column hol hH hb e hτ'
  rw [spAct_spDiag_eq] at h1
  have h2 : (fun i => (((U.val.map (Int.cast : ℤ → ℂ) * τ *
      (U.val.map (Int.cast : ℤ → ℂ))ᵀ) i e).im : ℂ)) = U.val.map (Int.cast : ℤ → ℂ) *ᵥ w := by
    ext i
    rw [Matrix.mul_assoc]
    simp [hw, mul_apply, mulVec, dotProduct, imC]
  have hd : HasDerivAt (fun s : ℂ => (of.symm τ + s • of.symm (vecMulVec w w) : Fin g → Fin g → ℂ))
      (of.symm (vecMulVec w w)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const
      (of.symm (vecMulVec w w) : Fin g → Fin g → ℂ)).const_add (of.symm τ)
  have hn := (isOpen_phDom g).mem_nhds (of_symm_mem_phDom hτ)
  have h3 := (hol.differentiableAt hn).hasFDerivAt.comp_hasDerivAt_of_eq 0 hd (by simp)
  refine h3.unique ((hasDerivAt_const 0 (H τ)).congr_of_eventuallyEq ?_)
  filter_upwards [h1, hd.continuousAt.eventually (p := fun x => x ∈ phDom g) (by simpa using hn)]
    with s hs hm
  have hsym : phSym (of (of.symm τ + s • of.symm (vecMulVec w w))) = τ + s • vecMulVec w w := by
    refine phSym_eq_self_of_isSymm (hτ.1.add (IsSymm.smul ?_ s))
    exact transpose_vecMulVec w w
  have hm' : τ + s • vecMulVec w w ∈ SiegelH (Fin g) := hsym ▸ hm
  rw [Function.comp_apply, hsym, ← spInvariant_conj hH U hm', ← spInvariant_conj hH U hτ, ← hs, h2,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul,
    vecMul_transpose]

theorem siegel_eq_of_bounded (hol : IsHoloSiegel g H) (hH : IsSpInvariant g H)
    (hb : ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖H τ‖ ≤ K)
    {τ σ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) (hσ : σ ∈ SiegelH (Fin g)) :
    H τ = H σ := by
  have key : ∀ τ ∈ SiegelH (Fin g), ∀ V : Matrix (Fin g) (Fin g) ℂ, V.IsSymm →
      fderiv ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (of x))) (of.symm τ) (of.symm V) = 0 := by
    intro τ hτ V hV
    set L := fderiv ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (of x))) (of.symm τ) with hL
    let M : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun S => L (of.symm (imC τ * S * (imC τ)ᵀ))
        map_add' := fun S T => by
          rw [Matrix.mul_add, Matrix.add_mul]
          exact L.map_add _ _
        map_smul' := fun c S => by
          rw [Matrix.mul_smul, Matrix.smul_mul]
          exact L.map_smul _ _ }
    have hM : ∀ (U : (Matrix (Fin g) (Fin g) ℤ)ˣ) (e : Fin g),
        M (vecMulVec (fun l => (U.val e l : ℂ)) fun l => (U.val e l : ℂ)) = 0 := by
      intro U e
      rw [← fderiv_vecMulVec_eq_zero hol hH hb U e hτ]
      change L _ = L _
      rw [mul_vecMulVec, vecMulVec_mul, vecMul_transpose]
    have h1 : ∀ i, M (single i i 1) = 0 := fun i => by
      rw [← hM 1 i]
      congr 1
      ext a b
      simp [vecMulVec_apply, single_apply, one_apply, ite_and]
      split_ifs <;> rfl
    have h2 : ∀ i j, M (single i j 1) + M (single j i 1) = 0 := fun i j => by
      by_cases hij : i = j
      · simp [hij, h1]
      have h := hM (rkU (Pi.single i 1) (Pi.single j 1) (by simp [hij])) i
      have e : (vecMulVec (fun l => ((rkU (Pi.single i 1) (Pi.single j 1)
          (by simp [hij])).val i l : ℂ)) fun l => ((rkU (Pi.single i 1) (Pi.single j 1)
          (by simp [hij])).val i l : ℂ)) =
          single i i 1 + single j j 1 + (single i j 1 + single j i 1) := by
        ext a b
        simp only [rkU_val, vecMulVec_apply, single_apply, one_apply, ite_and, Matrix.add_apply,
          Pi.single_apply, eq_comm (b := j)]
        split_ifs <;> norm_num
      rwa [e, map_add, map_add, map_add, h1, h1, zero_add, zero_add] at h
    have h3 : ∀ S : Matrix (Fin g) (Fin g) ℂ, S.IsSymm → M S = 0 := fun S hS => by
      have e1 : M S = ∑ i, ∑ j, S i j * M (single i j 1) := by
        conv_lhs => rw [matrix_eq_sum_single S]
        simp only [map_sum, ← smul_eq_mul, ← map_smul, smul_single]
        simp
      have e2 : M S = ∑ i, ∑ j, S i j * M (single j i 1) := by
        rw [e1, Finset.sum_comm]
        simp only [hS.apply]
      have : M S + M S = 0 := by
        nth_rw 1 [e1]
        simp only [e2, ← Finset.sum_add_distrib, ← mul_add, h2, mul_zero, Finset.sum_const_zero]
      linear_combination (1 / 2 : ℂ) * this
    have hu : IsUnit (imC τ).det := by
      have : imC τ = Complex.ofRealHom.mapMatrix (τ.map Complex.im) := rfl
      rw [this, ← RingHom.map_det]
      exact hτ.2.det_pos.ne'.isUnit.map _
    have h4 := h3 ((imC τ)⁻¹ * V * ((imC τ)⁻¹)ᵀ) (by
      simp only [IsSymm, transpose_mul, transpose_transpose, hV.eq, Matrix.mul_assoc])
    rw [← h4]
    change L _ = L _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← transpose_mul, mul_nonsing_inv _ hu, transpose_one,
      Matrix.mul_one, mul_nonsing_inv_cancel_left _ _ hu]
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, τ + (t : ℂ) • (σ - τ) ∈ SiegelH (Fin g) := fun t ht => by
    have h : phSym _ ∈ SiegelH (Fin g) := (convex_phDom g).add_smul_sub_mem
      (of_symm_mem_phDom hτ) (of_symm_mem_phDom hσ) ht
    rwa [← phSym_eq_self_of_isSymm (hτ.1.add ((hσ.1.sub hτ.1).smul (t : ℂ)))]
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ =>
      H (phSym (of (of.symm τ + (t : ℂ) • of.symm (σ - τ))))) 0 t := fun t ht => by
    have h1 : HasDerivAt (fun s : ℂ => (of.symm τ + s • of.symm (σ - τ) : Fin g → Fin g → ℂ))
        (of.symm (σ - τ)) t := by
      simpa using ((hasDerivAt_id (t : ℂ)).smul_const
        (of.symm (σ - τ) : Fin g → Fin g → ℂ)).const_add (of.symm τ)
    have h2 := (hol.differentiableAt ((isOpen_phDom g).mem_nhds
      (of_symm_mem_phDom (hmem t ht)))).hasFDerivAt.comp_hasDerivAt_of_eq (t : ℂ) h1 rfl
    rw [key _ (hmem t ht) _ (hσ.1.sub hτ.1)] at h2
    exact h2.comp_ofReal
  have h := constant_of_has_deriv_right_zero
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (Set.Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 (by simp)
  simp only [ofReal_one, ofReal_zero, one_smul, zero_smul, add_zero, Equiv.apply_symm_apply,
    phSym_eq_self_of_isSymm hτ.1] at h
  have e : of (of.symm τ + of.symm (σ - τ)) = σ := add_sub_cancel τ σ
  rw [← h, e, phSym_eq_self_of_isSymm hσ.1]

theorem phHolo_of_phKoecher : PhKoecherStatement → PhHoloStatement := by
  intro hK g hg H hol hH
  have hb := hK g hg 1 le_rfl H hol
    (fun B hB τ hτ => by simpa using spInvariant_transl hH hB hτ)
    (fun U hU _ τ hτ => by
      obtain ⟨U, rfl⟩ := (isUnit_iff_isUnit_det U).2 (hU ▸ isUnit_one)
      exact spInvariant_conj hH U hτ)
  by_cases h : (SiegelH (Fin g)).Nonempty
  · obtain ⟨σ, hσ⟩ := h
    exact ⟨H σ, fun τ hτ => siegel_eq_of_bounded hol hH hb hτ hσ⟩
  · exact ⟨0, fun τ hτ => absurd ⟨τ, hτ⟩ h⟩

end GlobalTheory
