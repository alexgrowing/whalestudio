import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import GroundTheory.GlobalFields.Adele.WeakApprox
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc Filter Topology

private theorem pow_nhds {K : Type} [NontriviallyNormedField K] [CompleteSpace K] {R : Type} [Ring R] [Algebra K R]
    {ι : Type} [Fintype ι] (p : (ι → K) →ₗ[K] R) (q : R →ₗ[K] (ι → K)) (hqp : ∀ x, q (p x) = x)
    (hmul : ∀ x y, p (q (p x * p y)) = p x * p y) (o : ι → K) (ho : p o = 1) (n : ℕ) (hn : (n : K) ≠ 0)
    (P : (ι → K) → Prop) (hP : ∀ᶠ y in 𝓝 o, P y) : ∀ᶠ x in 𝓝 o, ∃ y, P y ∧ p x = p y ^ n := by
  have hpow : ∀ k x, p (q (p x ^ k)) = p x ^ k := by
    intro k x
    induction k with
    | zero => rw [pow_zero, ← ho, hqp]
    | succ k ih =>
      rw [pow_succ]
      have := hmul (q (p x ^ k)) x
      rwa [ih] at this
  let Bl : (ι → K) →ₗ[K] (ι → K) →ₗ[K] (ι → K) := LinearMap.mk₂ K (fun a b => q (p a * p b))
    (fun a a' b => by simp [add_mul]) (fun c a b => by simp [smul_mul_assoc])
    (fun a b b' => by simp [mul_add]) (fun c a b => by simp [mul_smul_comm])
  let B : (ι → K) →L[K] (ι → K) →L[K] (ι → K) :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ Bl)
  have hB : ∀ a b, B a b = q (p a * p b) := fun a b => rfl
  let f : ℕ → (ι → K) → (ι → K) := fun k x => q (p x ^ k)
  have hfs : ∀ k, f (k + 1) = fun x => B (f k x) x := by
    intro k
    funext x
    simp only [f, hB, hpow, pow_succ]
  have hfo : ∀ k, f k o = o := by
    intro k
    simp only [f, ho, one_pow]
    rw [← ho, hqp]
  have hder : ∀ k : ℕ, HasStrictFDerivAt (f k) ((k : K) • ContinuousLinearMap.id K (ι → K)) o := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_smul]
      have : f 0 = fun _ => o := by
        funext x
        simp only [f, pow_zero]
        rw [← ho, hqp]
      rw [this]
      exact hasStrictFDerivAt_const _ _
    | succ k ih =>
      rw [hfs k]
      refine (B.hasStrictFDerivAt_of_bilinear ih (hasStrictFDerivAt_id o)).congr_fderiv ?_
      ext h i
      simp [hB, hfo, ho, hqp, add_smul, add_comm]
  have hn' := hder n
  let e : (ι → K) ≃L[K] (ι → K) := (LinearEquiv.smulOfNeZero K (ι → K) (n : K) hn).toContinuousLinearEquiv
  have he : (e : (ι → K) →L[K] (ι → K)) = (n : K) • ContinuousLinearMap.id K _ :=
    ContinuousLinearMap.ext fun x => rfl
  rw [← he] at hn'
  have hmap := hn'.map_nhds_eq_of_equiv
  rw [hfo] at hmap
  rw [← hmap, Filter.eventually_map]
  filter_upwards [hP] with y hy
  exact ⟨y, hy, hpow n y⟩

private theorem int_nhds {K : Type} [NontriviallyNormedField K] [CompleteSpace K] (O : Type) [CommRing O] [IsDomain O] [Algebra O K] [IsFractionRing O K]
    (hO : ∀ᶠ s in 𝓝 (0 : K), s ∈ (algebraMap O K).range) {L : Type} [CommRing L] [Algebra K L] [Algebra O L] [IsScalarTower O K L]
    [Module.Finite K L] {ι : Type} [Fintype ι] (l : (ι → K) →ₗ[K] L) (o : ι → K) (ho : IsIntegral O (l o)) :
    ∀ᶠ x in 𝓝 o, IsIntegral O (l x) := by
  classical
  let e : ι → (ι → K) := fun i j => if i = j then 1 else 0
  have hint : ∀ i, ∃ m : nonZeroDivisors O, IsIntegral O (m • l (e i)) := fun i =>
    IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := K) (nonZeroDivisors O) (l (e i)) (Algebra.IsIntegral.isIntegral (R := K) _)
  choose m hm using hint
  have hc : ∀ i, algebraMap O K (m i) ≠ 0 := fun i =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (m i).2
  have hev : ∀ i, ∀ᶠ x in 𝓝 o, (x i - o i) / algebraMap O K (m i) ∈ (algebraMap O K).range := by
    intro i
    have hcont : Continuous (fun x : ι → K => (x i - o i) / algebraMap O K (m i)) := by fun_prop
    have ht := hcont.tendsto o
    rw [sub_self, zero_div] at ht
    exact ht.eventually hO
  filter_upwards [Filter.eventually_all.mpr hev] with x hx
  have hsplit : l x = l o + ∑ i, (x i - o i) • l (e i) := by
    have h1 : x - o = ∑ i, (x - o) i • e i := pi_eq_sum_univ (x - o)
    have h2 : l (x - o) = ∑ i, (x i - o i) • l (e i) := by
      rw [h1, map_sum]
      simp [map_smul]
    rw [← h2, ← map_add, add_sub_cancel]
  rw [hsplit]
  refine IsIntegral.add ho (IsIntegral.sum _ fun i _ => ?_)
  obtain ⟨s, hs⟩ := hx i
  have hxi : x i - o i = algebraMap O K s * algebraMap O K (m i) := by
    rw [hs, div_mul_cancel₀ _ (hc i)]
  have e2 : (x i - o i) • l (e i) = s • ((m i : O) • l (e i)) := by
    rw [hxi, mul_smul, algebraMap_smul, algebraMap_smul]
  rw [e2]
  exact (hm i).smul s

section Coord

variable {K : Type} [Field K] (Δ : K)

private def pD : (Fin 4 → K) →ₗ[K] Matrix (Fin 2) (Fin 2) (Lsq K Δ) where
  toFun x := !![⟨x 0, x 1⟩, ⟨x 2, x 3⟩; ⟨-x 2, x 3⟩, ⟨x 0, -x 1⟩]
  map_add' x y := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c x := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp

private def qD : Matrix (Fin 2) (Fin 2) (Lsq K Δ) →ₗ[K] (Fin 4 → K) where
  toFun M := ![(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im]
  map_add' x y := by
    ext i; fin_cases i <;> simp
  map_smul' c x := by
    ext i; fin_cases i <;> simp

private theorem pD_apply (x : Fin 4 → K) : pD Δ x = !![⟨x 0, x 1⟩, ⟨x 2, x 3⟩; ⟨-x 2, x 3⟩, ⟨x 0, -x 1⟩] := rfl

private theorem qD_apply (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) :
    qD Δ M = ![(M 0 0).re, (M 0 0).im, (M 0 1).re, (M 0 1).im] := rfl

private def nD (x : Fin 4 → K) : K := x 0 ^ 2 - Δ * x 1 ^ 2 + x 2 ^ 2 - Δ * x 3 ^ 2

private theorem qp (x : Fin 4 → K) : qD Δ (pD Δ x) = x := by
  ext i; fin_cases i <;> simp [pD_apply, qD_apply]

private theorem pq_mul (x y : Fin 4 → K) : pD Δ (qD Δ (pD Δ x * pD Δ y)) = pD Δ x * pD Δ y := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, qD_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem p_one : pD Δ ![1, 0, 0, 0] = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem det_p (x : Fin 4 → K) : (pD Δ x).det = algebraMap K _ (nD Δ x) := by
  change _ = (⟨nD Δ x, 0⟩ : Lsq K Δ)
  ext <;> simp [pD_apply, nD, Matrix.det_fin_two] <;> ring

private theorem mem_iff_lemma (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map star = !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
  change GeneralLinearGroup.map (starRingEnd _) g = MulAut.conj (wJ Δ)⁻¹ g ↔ _
  rw [Units.ext_iff]
  simp [wJ, MulAut.conj_apply]
  rfl

private theorem map_star_eq_conj_iff_pD_qD_eq (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) : M.map star = !![0, -1; 1, 0] * M * !![0, 1; -1, 0] ↔ pD Δ (qD Δ M) = M := by
  constructor
  · intro h
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, QuadraticAlgebra.ext_iff, Matrix.vecMul, dotProduct] at e00 e01
    obtain ⟨a1, a2⟩ := e00
    obtain ⟨b1, b2⟩ := e01
    ext i j : 2 <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, qD_apply, a1, a2, b1, b2]
  · intro h
    rw [← h]
    ext i j : 2 <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, qD_apply, Matrix.mul_apply, Fin.sum_univ_two]

private theorem mem_iff (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔ pD Δ (qD Δ g) = g := by
  rw [mem_iff_lemma, map_star_eq_conj_iff_pD_qD_eq]

private theorem pq_mt (g : DX Δ) : pD Δ (qD Δ (mt g)) = mt g := (mem_iff Δ g).1 g.2

private theorem isUnit_p (x : Fin 4 → K) : IsUnit (pD Δ x) ↔ nD Δ x ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, det_p]
  constructor
  · intro h h0
    rw [h0, map_zero] at h
    exact not_isUnit_zero h
  · intro h
    exact (IsUnit.mk0 _ h).map _

private theorem ex_mt (x : Fin 4 → K) (h : IsUnit (pD Δ x)) : ∃ g : DX Δ, mt g = pD Δ x := by
  refine ⟨⟨h.unit, (mem_iff Δ _).mpr ?_⟩, ?_⟩
  · rw [IsUnit.unit_spec, qp]
  · simp [mt]

private theorem p_map {K' : Type} [Field K'] (f : K →+* K') (x : Fin 4 → K) :
    (pD Δ x).map (lmap f Δ) = pD (f Δ) (fun i => f (x i)) := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [pD_apply, lmap]

private theorem n_map {K' : Type} [Field K'] (f : K →+* K') (x : Fin 4 → K) :
    nD (f Δ) (fun i => f (x i)) = f (nD Δ x) := by
  simp [nD]

private theorem mem_KD (O : Type) [CommRing O] [Algebra O K] (g : DX Δ) (h : ∀ i j, IsIntegral O (mt g i j)) (a : O)
    (ha : (mt g).det * algebraMap O _ a = 1) : g ∈ KD Δ O := by
  rw [KD, Subgroup.mem_subgroupOf]
  let N : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := fun i j => ⟨mt g i j, h i j⟩
  have hdet : IsUnit N.det := by
    refine IsUnit.of_mul_eq_one (algebraMap O _ a) ?_
    apply Subtype.ext
    have e := RingHom.map_det ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) N
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_one]
    rw [← ha]
    congr 1
  refine ⟨((Matrix.isUnit_iff_isUnit_det N).mpr hdet).unit, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

end Coord

private theorem loc_open {K : Type} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K] (O : Type) [CommRing O] [IsDomain O] [Algebra O K]
    [IsFractionRing O K] (hO : ∀ᶠ s in 𝓝 (0 : K), s ∈ (algebraMap O K).range) (Δ : K) (J : Subgroup (DX Δ))
    (hJ : J.relIndex (KD Δ O) ≠ 0) (g : DX Δ) :
    ∀ᶠ x in 𝓝 (qD Δ (mt g⁻¹)), ∃ j ∈ J, mt j = pD Δ x * mt g := by
  classical
  let J' := J.subgroupOf (KD Δ O)
  haveI : J'.FiniteIndex := ⟨hJ⟩
  have hm0 : J'.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpowJ : ∀ k ∈ KD Δ O, k ^ J'.normalCore.index ∈ J := by
    intro k hk
    have h1 := J'.normalCore.pow_index_mem ⟨k, hk⟩
    have h2 := J'.normalCore_le h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  let P : (Fin 4 → K) → Prop := fun y => ∃ k : DX Δ, k ∈ KD Δ O ∧ mt k = pD Δ y
  have hcont : Continuous (nD Δ) := by
    show Continuous (fun x : Fin 4 → K => x 0 ^ 2 - Δ * x 1 ^ 2 + x 2 ^ 2 - Δ * x 3 ^ 2)
    fun_prop
  have h1 : nD Δ ![1, 0, 0, 0] = 1 := by simp [nD]
  have hP : ∀ᶠ y in 𝓝 (![1, 0, 0, 0] : Fin 4 → K), P y := by
    have hent : ∀ i j, ∀ᶠ y in 𝓝 (![1, 0, 0, 0] : Fin 4 → K), IsIntegral O (pD Δ y i j) := by
      intro i j
      let l : (Fin 4 → K) →ₗ[K] Lsq K Δ :=
        { toFun := fun y => pD Δ y i j
          map_add' := by
            intro a b
            simp
          map_smul' := by
            intro c a
            simp }
      refine int_nhds O hO l _ ?_
      show IsIntegral O (pD Δ ![1, 0, 0, 0] i j)
      rw [p_one]
      by_cases hij : i = j
      · rw [hij, Matrix.one_apply_eq]
        exact isIntegral_one
      · simp [Matrix.one_apply, hij, isIntegral_zero]
    have ht : Tendsto (fun y => (nD Δ y)⁻¹ - 1) (𝓝 ![1, 0, 0, 0]) (𝓝 0) := by
      have h3 := ((hcont.tendsto ![1, 0, 0, 0]).inv₀ (by rw [h1]; exact one_ne_zero)).sub_const 1
      rwa [h1, inv_one, sub_self] at h3
    have hne : ∀ᶠ y in 𝓝 (![1, 0, 0, 0] : Fin 4 → K), nD Δ y ≠ 0 :=
      hcont.continuousAt.eventually_ne (by rw [h1]; exact one_ne_zero)
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hent i)), ht.eventually hO, hne] with y hy hy2 hy3
    obtain ⟨a0, ha0⟩ := hy2
    obtain ⟨g', hg'⟩ := ex_mt Δ y ((isUnit_p Δ y).mpr hy3)
    refine ⟨g', mem_KD Δ O g' (by rw [hg']; exact hy) (a0 + 1) ?_, hg'⟩
    rw [hg', det_p, IsScalarTower.algebraMap_apply O K (Lsq K Δ), map_add, map_one, ha0, sub_add_cancel, ← map_mul, mul_inv_cancel₀ hy3, map_one]
  have hpow := pow_nhds (pD Δ) (qD Δ) (qp Δ) (pq_mul Δ) ![1, 0, 0, 0] (p_one Δ) J'.normalCore.index (Nat.cast_ne_zero.mpr hm0) P hP
  have hT : Tendsto (fun x => qD Δ (pD Δ x * mt g)) (𝓝 (qD Δ (mt g⁻¹))) (𝓝 ![1, 0, 0, 0]) := by
    let T : (Fin 4 → K) →ₗ[K] (Fin 4 → K) := qD Δ ∘ₗ (LinearMap.mulRight K (mt g)) ∘ₗ pD Δ
    have hc : Continuous T := LinearMap.continuous_of_finiteDimensional T
    have h4 := hc.tendsto (qD Δ (mt g⁻¹))
    have e : T (qD Δ (mt g⁻¹)) = ![1, 0, 0, 0] := by
      simp only [T, LinearMap.comp_apply, LinearMap.mulRight_apply]
      rw [pq_mt]
      rw [show mt g⁻¹ * mt g = 1 by simp [mt], ← p_one Δ, qp]
    rw [e] at h4
    exact h4
  filter_upwards [hT.eventually hpow] with x hx
  obtain ⟨y, ⟨k, hk, hky⟩, hxy⟩ := hx
  refine ⟨k ^ J'.normalCore.index, hpowJ k hk, ?_⟩
  have e : pD Δ (qD Δ (pD Δ x * mt g)) = pD Δ x * mt g := by
    rw [← pq_mt Δ g]
    exact pq_mul Δ x _
  rw [← e, hxy, ← hky]
  simp [mt]

private theorem approx {F : Type} [Field F] [NumberField F] (S : Finset (Pl F)) (a : ∀ v : Pl F, Fin 4 → Kv v)
    (P : ∀ v : Pl F, (Fin 4 → Kv v) → Prop) (hP : ∀ v ∈ S, ∀ᶠ x in 𝓝 (a v), P v x) :
    ∃ x : Fin 4 → F, ∀ v ∈ S, P v fun i => cv v (x i) := by
  have h1 : DenseRange fun (x : F) (v : S) => cv v.1 x :=
    (Prod.fst_surjective.denseRange).comp (GroundTheory.Global.denseRange_algebraMap_prod_pi S ∅) continuous_fst
  have h2 := DenseRange.piMap (fun _ : Fin 4 => h1)
  have h3 : ∀ᶠ y : Fin 4 → ∀ v : S, Kv v.1 in 𝓝 fun i v => a v.1 i, ∀ v : S, P v.1 fun i => y i v := by
    refine eventually_all.2 fun v => ?_
    have hc : Continuous fun (y : Fin 4 → ∀ v : S, Kv v.1) i => y i v := by fun_prop
    exact (hc.tendsto _).eventually (hP v.1 v.2)
  obtain ⟨x, hx⟩ := h2.mem_nhds h3
  exact ⟨x, fun v hv => hx ⟨v, hv⟩⟩

private theorem loc_v {F : Type} [Field F] [NumberField F] (v : Pl F) (Δ : Kv v) (J : Subgroup (DX Δ))
    (hJ : J.relIndex (KD Δ (Ov v)) ≠ 0) (g : DX Δ) :
    ∀ᶠ x in 𝓝 (qD Δ (mt g⁻¹)), ∃ j ∈ J, mt j = pD Δ x * mt g := by
  letI : NontriviallyNormedField (Kv v) := Valued.toNontriviallyNormedField (Kv v) (WithZero (Multiplicative ℤ))
  haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
  have hO : ∀ᶠ s in 𝓝 (0 : Kv v), s ∈ (algebraMap (Ov v) (Kv v)).range := by
    have ho : IsOpen ((HeightOneSpectrum.adicCompletionIntegers F v : Set (Kv v))) := Valued.isOpen_valuationSubring _
    filter_upwards [ho.mem_nhds (HeightOneSpectrum.adicCompletionIntegers F v).zero_mem] with s hs
    exact ⟨⟨s, hs⟩, rfl⟩
  exact loc_open (Ov v) hO Δ J hJ g

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.weakD :
    UpperTheory.V.Z.Sym.Glob.WeakD := by
  intro F _ _ Δ D hD ι hι g
  classical
  let gv : ∀ v : Pl F, DX (cv v Δ) := fun v => (g : ∀ v : Pl F, DX (cv v Δ)) v
  have hJ : ∀ v ∈ D.Sg, (D.J2v v).relIndex (KD (cv v Δ) (Ov v)) ≠ 0 := by
    intro v hv
    rw [Dat.J2v, if_pos hv]
    exact (hD.sig v hv).levelTwoFiniteIndex
  obtain ⟨x, hx⟩ := approx D.Sg (fun v => qD (cv v Δ) (mt (gv v)⁻¹))
    (fun v y => ∃ j ∈ D.J2v v, mt j = pD (cv v Δ) y * mt (gv v))
    (fun v hv => loc_v v (cv v Δ) (D.J2v v) (hJ v hv) (gv v))
  obtain ⟨v0, hv0⟩ := hD.ne
  have hn : nD Δ x ≠ 0 := by
    obtain ⟨j, -, hj⟩ := hx v0 hv0
    have hu : IsUnit (pD (cv v0 Δ) fun i => cv v0 (x i)) := by
      have h1 : IsUnit (mt j) := (j : GL (Fin 2) (Lsq (Kv v0) (cv v0 Δ))).isUnit
      rw [hj] at h1
      exact isUnit_of_mul_isUnit_left h1
    rw [isUnit_p, n_map] at hu
    intro h0
    exact hu (by rw [h0, map_zero])
  obtain ⟨γ, hγ⟩ := ex_mt Δ x ((isUnit_p Δ x).mpr hn)
  have hmt : ∀ v, mt ((ι γ : ∀ v : Pl F, DX (cv v Δ)) v) = pD (cv v Δ) (fun i => cv v (x i)) := by
    intro v
    rw [hι, hγ, p_map]
  have hmem : ∀ v ∈ D.Sg, (ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v ∈ D.J2v v := by
    intro v hv
    obtain ⟨j, hj, hj'⟩ := hx v hv
    have e : (ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v = j := by
      apply Subtype.ext
      apply Units.ext
      change mt _ * mt _ = mt j
      rw [hmt, hj']
    rw [e]
    exact hj
  let uf : ∀ v : Pl F, DX (cv v Δ) := fun v => if v ∈ D.Sg then ((ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v)⁻¹ else 1
  have huf : uf ∈ RP (fun v : Pl F => DX (cv v Δ)) (fun v => KD (cv v Δ) (Ov v)) := by
    change ∀ᶠ v in Filter.cofinite, uf v ∈ KD (cv v Δ) (Ov v)
    rw [Filter.eventually_cofinite]
    refine D.Sg.finite_toSet.subset ?_
    intro v hv
    have hv2 : ¬ uf v ∈ KD (cv v Δ) (Ov v) := hv
    by_contra hv'
    apply hv2
    have e : uf v = 1 := if_neg hv'
    rw [e]
    exact (KD (cv v Δ) (Ov v)).one_mem
  refine ⟨γ, ⟨uf, huf⟩, ?_, ?_⟩
  · rw [Dat.U2, RPG.box, Subgroup.mem_iInf]
    intro v
    rw [Subgroup.mem_comap]
    change uf v ∈ D.J2v v
    by_cases hv : v ∈ D.Sg
    · have e : uf v = ((ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v)⁻¹ := if_pos hv
      rw [e]
      exact inv_mem (hmem v hv)
    · have e : uf v = 1 := if_neg hv
      rw [e]
      exact (D.J2v v).one_mem
  · intro v hv
    change (ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v * uf v = 1
    have e : uf v = ((ι γ : ∀ v : Pl F, DX (cv v Δ)) v * gv v)⁻¹ := if_pos hv
    rw [e]
    exact mul_inv_cancel _
