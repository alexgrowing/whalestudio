import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HfStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.IwasawaA
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RayClassGroupFinite

open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis
open scoped Matrix

namespace UpperTheory.V.Br.CuspStabilizer

section Aff
variable {R S : Type} [CommRing R] [CommRing S]

private theorem aff_mul (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem aff_one : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem corner_aff (s : R →ₙ+* S) (y : Rˣ) (x : R) : cornerGL 2 s (aff y x) = aff (Units.map (corner s) y) (s x) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (aff y x i j) = _
  fin_cases i <;> fin_cases j <;> simp [aff, corner]

private theorem continuous_aff [TopologicalSpace R] [IsTopologicalRing R] : Continuous fun y : Rˣ => aff y (0 : R) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop

end Aff

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (θ : TR.Rinf F) : TR.Kinf F 2 :=
  ⟨!![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq (θ v)]⟩

private noncomputable def eps (s : InfinitePlace F → ℤˣ) : TR.Kinf F 2 :=
  ⟨!![1, 0; 0, fun v => ((s v : ℤ) : ℝ)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
    rcases Int.units_eq_one_or (s v) with h | h <;> simp [h]⟩

private theorem real_dec {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0) (h3 : c * c + d * d = 1) :
    ∃ (s : ℤˣ) (t : ℝ), a = Real.cos t ∧ b = Real.sin t ∧ c = -((s : ℤ) * Real.sin t) ∧ d = (s : ℤ) * Real.cos t := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, h1, Real.sqrt_one]
  have h0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by simp [h] at hn
  have ha : a = Real.cos (Complex.arg ⟨a, b⟩) := by rw [Complex.cos_arg h0, hn, div_one]
  have hb : b = Real.sin (Complex.arg ⟨a, b⟩) := by rw [Complex.sin_arg, hn, div_one]
  have hc : c = -((a * d - b * c) * b) := by linear_combination (-c) * h1 + a * h2
  have hd : d = (a * d - b * c) * a := by linear_combination (-d) * h1 + b * h2
  have hs : (a * d - b * c) * (a * d - b * c) = 1 := by
    linear_combination (c * c + d * d) * h1 + h3 - (a * c + b * d) * h2
  rcases mul_self_eq_one_iff.1 hs with h | h
  · exact ⟨1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩
  · exact ⟨-1, _, ha, hb, by rw [← hb]; simpa [h] using hc, by rw [← ha]; simpa [h] using hd⟩

omit [NumberField F] in
private theorem dec (x : TR.Kinf F 2) : ∃ s θ, x = eps s * rot θ := by
  have h := Matrix.mem_unitaryGroup_iff.1 x.2
  have e : ∀ i j v, x.1 i 0 v * x.1 j 0 v + x.1 i 1 v * x.1 j 1 v = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v := fun i j v => by
    rw [← h]; simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply]
  choose s θ h1 h2 h3 h4 using fun v => real_dec (a := x.1 0 0 v) (b := x.1 0 1 v) (c := x.1 1 0 v) (d := x.1 1 1 v)
    (by simpa using e 0 0 v) (by simpa using e 0 1 v) (by simpa using e 1 1 v)
  refine ⟨s, θ, ?_⟩
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot, eps, Matrix.mul_apply, Fin.sum_univ_succ, h1, h2, h3, h4]

variable [IsTotallyReal F]

private def stab (M : ℕ) (g : GA F 2) : Subgroup (Ideles F) where
  carrier := {u | ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff (t * u) 0 * g ∈ Z ↔ aff t 0 * g ∈ Z}
  one_mem' := fun Z _ t => by rw [mul_one]
  mul_mem' := fun {a b} ha hb Z hZ t => by rw [← mul_assoc, hb Z hZ, ha Z hZ]
  inv_mem' := fun {a} ha Z hZ t => by rw [← ha Z hZ, inv_mul_cancel_right]

private theorem mem_stab {M : ℕ} {g : GA F 2} {u : Ideles F}
    (h1 : ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * u) 0 * g ∈ Z)
    (h2 : ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * u⁻¹) 0 * g ∈ Z) : u ∈ stab M g :=
  fun Z hZ t => ⟨fun h => by simpa only [mul_inv_cancel_right] using h2 Z hZ _ h, h1 Z hZ t⟩

private theorem stab_fin {M : ℕ} (hM : 1 ≤ M) (g : GA F 2) : (stab M g).FiniteIndex := by
  have am : ∀ t u : Ideles F, aff (t * u) (0 : Ad F) = aff u 0 * aff t 0 := fun t u => by rw [aff_mul, mul_comm]; simp
  have h1 : ∀ a : Fˣ, ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z → aff (t * diagUnits F a) 0 * g ∈ Z :=
    fun a Z hZ t h => by rw [am, mul_assoc]; exact hZ.rat a _ h
  have h2 : ∀ y : (TR.Rinf F)ˣ, (∀ v, 0 < y.val v) → ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z →
      aff (t * TR.infId F y) 0 * g ∈ Z := fun y hy Z hZ t h => by
    have := hZ.pos y hy _ h
    rw [TR.infGL, corner_aff, map_zero] at this
    rw [am, mul_assoc]; exact this
  set k := Matrix.GeneralLinearGroup.map (pFin F) g with hk
  have h3 : ∀ u : (Af F)ˣ, k⁻¹ * aff u 0 * k ∈ KLev F 2 M → ∀ Z : Set (GA F 2), Moves M Z → ∀ t, aff t 0 * g ∈ Z →
      aff (t * finId F u) 0 * g ∈ Z := fun u hu Z hZ t h => by
    have e : aff (finId F u) 0 * g = g * finGL F 2 (k⁻¹ * aff u 0 * k) := by
      have : aff (finId F u) 0 = finGL F 2 (aff u 0) := by rw [finGL, corner_aff, map_zero]; rfl
      rw [this]
      exact TR.ga_ext (by simp) (by simp [k, mul_assoc])
    rw [mul_comm t, am, mul_assoc, e, ← mul_assoc]
    exact hZ.lev _ hu _ h
  refine (UpperTheory.ray_class_group_finite F (stab M g) (fun a => mem_stab (h1 a) ?_) (fun y hy => mem_stab (h2 y hy) ?_) ?_).2
  · rw [← map_inv]; exact h1 _
  · rw [← map_inv]
    refine h2 _ fun v => ?_
    have h : y.val v * (y⁻¹).val v = 1 := congrFun y.mul_inv v
    exact (mul_pos_iff_of_pos_left (hy v)).1 (h ▸ one_pos)
  · have h4 := ((isOpen_KLev (F := F) (n := 2) hM).preimage (f := fun u : (Af F)ˣ => k⁻¹ * aff u 0 * k)
      ((continuous_const.mul continuous_aff).mul continuous_const)).mem_nhds (x := 1) (by simp [aff_one])
    filter_upwards [h4] with u hu
    refine mem_stab (h3 u hu) ?_
    rw [← map_inv]
    refine h3 _ ?_
    have e : aff u⁻¹ (0 : Af F) = (aff u 0)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [aff_mul]; simp [aff_one])
    have := (KLev F 2 M).inv_mem hu
    rw [e]
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using this

end UpperTheory.V.Br.CuspStabilizer

open UpperTheory.V.Br.CuspStabilizer in
theorem UpperTheory.V.Br.cuspSet :
    UpperTheory.V.Br.CuspSet := by
  intro F _ _ _ M hM
  haveI : CompactSpace (KLev F 2 1) := isCompact_iff_compactSpace.1 (isCompact_KLev le_rfl)
  haveI : Finite (KLev F 2 1 ⧸ (KLev F 2 M).subgroupOf (KLev F 2 1)) :=
    Subgroup.quotient_finite_of_isOpen _ ((isOpen_KLev hM).preimage continuous_subtype_val)
  let b : (InfinitePlace F → ℤˣ) × (KLev F 2 1 ⧸ (KLev F 2 M).subgroupOf (KLev F 2 1)) → GA F 2 := fun p =>
    TR.infGL F 2 (Unitary.toUnits (eps p.1)) * finGL F 2 p.2.out.1
  haveI : ∀ g : GA F 2, (stab M g).FiniteIndex := stab_fin hM
  refine ⟨⋃ p, Set.range fun q : Ideles F ⧸ stab M (b p) => aff q.out 0 * b p,
    Set.finite_iUnion fun p => Set.finite_range _, fun Z hS hZ => Set.eq_univ_of_forall fun g => ?_⟩
  have h1 : ∀ p t, aff t 0 * b p ∈ Z := fun p t => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (stab M (b p)) t
    refine (h.2 Z hZ t).1 ?_
    rw [← hh]
    exact hS (Set.mem_iUnion.2 ⟨p, _, rfl⟩)
  obtain ⟨z, y, x, r, u, hu, rfl⟩ := UpperTheory.V.Br.iwasawaA F g
  obtain ⟨s, θ, rfl⟩ := dec r
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((KLev F 2 M).subgroupOf (KLev F 2 1)) ⟨u, hu⟩
  have h2 := hZ.lev _ ((KLev F 2 M).inv_mem h.2) _ (h1 (s, QuotientGroup.mk ⟨u, hu⟩) y)
  have h3 := hZ.cent z _ (hZ.unip x _ (hZ.rot θ (Unitary.toUnits (rot θ)) rfl _ h2))
  have e1 : aff y x = aff 1 x * aff y 0 := by rw [aff_mul]; simp
  convert h3 using 1
  simp only [b, hh, e1, mul_assoc, map_mul, Subgroup.coe_mul, map_inv]
  rw [TR.infGL_comm]
  simp
