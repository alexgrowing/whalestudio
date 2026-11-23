import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrictlyConcavePolFanConeRealFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedPsdRationalRadicalConeSubsetIntConeStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

section Formulas

variable {X : Type} [AddCommGroup X]

theorem evalW_add_left (w w' : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (w + w') B = evalW w B + evalW w' B := by
  unfold evalW
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

theorem evalW_zero_left (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW (0 : (X × X) →₀ ℤ) B = 0 := by
  simp [evalW]

theorem evalW_zsmul_left (k : ℤ) (w : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (k • w) B = k * evalW w B := by
  unfold evalW
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun p _ => ?_
  simp only [smul_eq_mul, Int.cast_mul]
  ring

theorem evalW_single_left (p : X × X) (k : ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (Finsupp.single p k) B = k * B p.1 p.2 := by
  unfold evalW
  exact Finsupp.sum_single_index (by simp)

theorem evalW_finset_sum_left {ι : Type} (s : Finset ι) (f : ι → (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (∑ i ∈ s, f i) B = ∑ i ∈ s, evalW (f i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalW_zero_left]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evalW_add_left, ih]

theorem evalW_lamW (D N n : ℕ) (𝓜 : Finset ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (w : (X × X) →₀ ℤ)
    (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalW (lamW D N n 𝓜 r w a) B = D * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * evalW w B +
      ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, B (r (a M y)) (r (a M y))) := by
  simp only [lamW, evalW_zsmul_left, evalW_add_left, evalW_finset_sum_left, evalW_single_left]
  push_cast
  simp

theorem kDen_mul_evalR_baseFun {O : Type} [CommRing O] [Module.Finite ℤ O] [Module O X] [Module.Finite O X]
    [Module.Finite ℤ X] (D : ℕ) (φ : InvFun ℤ) (N n : ℕ) (𝓜 : Finset ℕ) {r : (Fin n → ℤ) →ₗ[ℤ] X}
    (hr : Function.Surjective r) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    (kDen N n 𝓜 : ℝ) * evalR (baseFun O D φ 𝓜) B = D * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φ B) +
      ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, classMin M (fun x z => B (r x) (r z)) y) := by
  have hE : ∀ M, (fineMean M).eval X (fun x z => B x z) =
      (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
    intro M
    rw [(fineMean M).eval_eq hr]
    simp [fineMean]
  have key : ∀ M ∈ 𝓜, (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (((M : ℝ) + 1) ^ n)⁻¹ =
      ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n := by
    intro M hM
    rw [← Finset.mul_prod_erase 𝓜 (fun M : ℕ => ((M : ℝ) + 1) ^ n) hM]
    have : ((M : ℝ) + 1) ^ n ≠ 0 := by positivity
    field_simp
  have hs : (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) *
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y =
      ∑ M ∈ 𝓜, (∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun M hM => by rw [← mul_assoc, key M hM]
  have h1 : evalR (baseFun O D φ 𝓜) B = D * (evalR φ B + ∑ M ∈ 𝓜, (fineMean M).eval X (fun x z => B x z)) :=
    eval_baseFun D φ 𝓜 _
  rw [h1]
  simp only [hE, kDen]
  push_cast
  calc _ = (D : ℝ) * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φ B) + N * ((∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) *
      ∑ M ∈ 𝓜, (((M : ℝ) + 1) ^ n)⁻¹ * ∑ y, classMin M (fun x z => B (r x) (r z)) y)) := by ring
    _ = _ := by
      rw [hs, Finset.mul_sum]
      simp only [mul_assoc]

theorem classMin_le_of_nonneg (M : ℕ) {n : ℕ} {B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ} (hB : ∀ x, 0 ≤ B x x)
    {y : Fin n → ZMod (M + 1)} {x : Fin n → ℤ} (hx : redV M x = y) : classMin M B y ≤ B x x :=
  csInf_le ⟨0, by rintro _ ⟨b, -, rfl⟩; exact hB b⟩ ⟨x, hx, rfl⟩

end Formulas

theorem exists_contact_baseFun_lamW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Finite ℤ X] (N m n : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ), 0 < D → IsPolFanOn (id : ℤ → ℤ) φs X → 0 < N → IsCone (id : ℤ → ℤ) φs u → StrictWith (id : ℤ → ℤ) φs N (linW w) u → Function.Surjective r → (∀ M y, redV M (a M y) = y) → ∃ A : Set (Fin m → ℤ), A.Finite ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (kDen N n 𝓜 : ℝ) * (baseFun (𝓞 E) D φs 𝓜).evalZ β ≤ evalW (lamW D N n 𝓜 r w a) (toReal β)) ∧ (∀ B ∈ psdCone H.bar X, (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i)) ∧ (∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) (∑ i, t i • toReal (u i)) = evalW (lamW D N n 𝓜 r w a) (∑ i, t i • toReal (u i))) ∧ ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) → (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
  intro E _ _ _ H D φs 𝓜 X _ _ _ _ N m n u w r a hD hφ hN hu hS hr ha
  classical
  choose F hF using fun (M : ℕ) (y : Fin n → ZMod (M + 1)) =>
    GlobalTheory.T.dickson_exists_finite_subfamily_below m (fun a' : {a' : Fin n → ℤ // redV M a' = y} => fun j => (u j (r a'.1) (r a'.1)).toNat)
  let vec : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → (Fin n → ℤ) → Fin m → ℤ :=
    fun M y a' i => u i (r (a M y)) (r (a M y)) - u i (r a') (r a')
  have hI := GlobalTheory.T.strictlyConcave_polFan_cone_real_forms X φs N m u w hφ hu hS
  have hsum : ∀ (t : Fin m → ℝ) (x z : X), (∑ i, t i • toReal (u i)) x z = ∑ i, t i * (u i x z : ℝ) := by
    intro t x z
    simp [LinearMap.sum_apply]
  have hP : 0 < ∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n := Finset.prod_pos fun _ _ => by positivity
  have hc : ∀ M ∈ 𝓜, 0 < (N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n := fun M _ =>
    mul_pos (by exact_mod_cast hN) (Finset.prod_pos fun _ _ => by positivity)
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD

  have hle_gen : ∀ B ∈ psdCone (id : ℤ → ℤ) X,
      (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B ≤ evalW (lamW D N n 𝓜 r w a) B := by
    intro B hB
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW]
    have h1 := ((hI.2 B hB).1)
    have h2 : ∀ M ∈ 𝓜, ∑ y, classMin M (fun x z => B (r x) (r z)) y ≤ ∑ y, B (r (a M y)) (r (a M y)) :=
      fun M _ => Finset.sum_le_sum fun y _ =>
        classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB (r x)) (ha M y)
    have h3 := Finset.sum_le_sum fun M hM => mul_le_mul_of_nonneg_left (h2 M hM) (hc M hM).le
    have h4 := mul_le_mul_of_nonneg_left h1 hP.le
    exact mul_le_mul_of_nonneg_left (add_le_add h4 h3) hD'.le

  have hback : ∀ B ∈ rcone u, (∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y))) →
      (kDen N n 𝓜 : ℝ) * evalR (baseFun (𝓞 E) D φs 𝓜) B = evalW (lamW D N n 𝓜 r w a) B := by
    intro B hB hcl
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW, hI.1 B hB]
    congr 2
    exact Finset.sum_congr rfl fun M hM => by rw [Finset.sum_congr rfl fun y _ => hcl M hM y]
  refine ⟨⋃ M ∈ (𝓜 : Set ℕ), ⋃ y : Fin n → ZMod (M + 1),
      (fun a' : {a' : Fin n → ℤ // redV M a' = y} => vec M y a'.1) '' (F M y : Set _), ?_, ?_, ?_, ?_, hback⟩
  · exact Set.Finite.biUnion (Finset.finite_toSet 𝓜) fun M _ =>
      Set.finite_iUnion fun y => (Finset.finite_toSet _).image _
  · intro β hβ hβ0
    have hB : toReal β ∈ psdCone H.bar X := by
      have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; simpa using hβ)
        (fun i y => by fin_cases i; simpa using hβ0 y) (fun i => by fin_cases i; simp)
      simpa using this
    rw [← evalR_toReal]
    exact hle_gen _ (GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone (𝓞 E) H.bar X hB)
  · intro B hB heq
    have hB' := GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone (𝓞 E) H.bar X hB
    rw [kDen_mul_evalR_baseFun D φs N n 𝓜 hr, evalW_lamW] at heq
    have heq' := mul_left_cancel₀ hD'.ne' heq
    have h1 := (hI.2 B hB').1
    have hy : ∀ M, ∀ y, 0 ≤ B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y := fun M y =>
      sub_nonneg.2 (classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB' (r x)) (ha M y))
    have hT : 0 ≤ ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) :=
      Finset.sum_nonneg fun M hM => mul_nonneg (hc M hM).le (Finset.sum_nonneg fun y _ => hy M y)
    have hT' : ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) =
        ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) * ∑ y, B (r (a M y)) (r (a M y)) -
        ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
          ∑ y, classMin M (fun x z => B (r x) (r z)) y := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun M _ => by rw [Finset.sum_sub_distrib, mul_sub]
    have h4 := mul_le_mul_of_nonneg_left h1 hP.le
    have hT0 : ∑ M ∈ 𝓜, ((N : ℝ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℝ) + 1) ^ n) *
        ∑ y, (B (r (a M y)) (r (a M y)) - classMin M (fun x z => B (r x) (r z)) y) = 0 := by
      linarith
    have hW : (N : ℝ) * evalR φs B = evalW w B := by
      have : (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * (N * evalR φs B) = (∏ M ∈ 𝓜, ((M : ℝ) + 1) ^ n) * evalW w B := by
        linarith
      exact mul_left_cancel₀ hP.ne' this
    have hcl : ∀ M ∈ 𝓜, ∀ y, classMin M (fun x z => B (r x) (r z)) y = B (r (a M y)) (r (a M y)) := by
      intro M hM y
      have e1 := (Finset.sum_eq_zero_iff_of_nonneg fun M hM =>
        mul_nonneg (hc M hM).le (Finset.sum_nonneg fun y _ => hy M y)).1 hT0 M hM
      have e2 := (mul_eq_zero.1 e1).resolve_left (hc M hM).ne'
      have e3 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hy M y).1 e2 y (Finset.mem_univ _)
      linarith
    have hcm : ∀ M y (x : Fin n → ℤ), redV M x = y → classMin M (fun x z => B (r x) (r z)) y ≤ B (r x) (r x) :=
      fun M y x hx => classMin_le_of_nonneg M (fun x => nonneg_of_mem_psdCone hB' (r x)) hx
    obtain ⟨t, ht0, rfl⟩ := (hI.2 B hB').2 hW
    refine ⟨t, ht0, ?_, rfl⟩
    intro v hv
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe] at hv
    obtain ⟨M, hM, y, a', ha'F, rfl⟩ := hv
    have e := hcl M hM y
    have e' := hcm M y a'.1 a'.2
    rw [e, hsum, hsum] at e'
    rw [hsum] at e
    have : ∑ i, ((vec M y a'.1 i : ℤ) : ℝ) * t i =
        ∑ i, t i * (u i (r (a M y)) (r (a M y)) : ℝ) - ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [vec]
      push_cast
      ring
    rw [this]
    linarith
  · intro t ht hA
    refine hback _ ⟨t, ht, rfl⟩ fun M hM y => ?_
    refine IsLeast.csInf_eq ⟨⟨a M y, ha M y, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a', ha'F, hle⟩ := hF M y ⟨x, hx⟩
    have hmem : vec M y a'.1 ∈ ⋃ M ∈ (𝓜 : Set ℕ), ⋃ y : Fin n → ZMod (M + 1),
        (fun a' : {a' : Fin n → ℤ // redV M a' = y} => vec M y a'.1) '' (F M y : Set _) := by
      simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
      exact ⟨M, hM, y, a', ha'F, rfl⟩
    have h1 := hA _ hmem
    have h2 : ∑ i, ((vec M y a'.1 i : ℤ) : ℝ) * t i =
        ∑ i, t i * (u i (r (a M y)) (r (a M y)) : ℝ) - ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [vec]
      push_cast
      ring
    have h3 : ∑ i, t i * (u i (r a'.1) (r a'.1) : ℝ) ≤ ∑ i, t i * (u i (r x) (r x) : ℝ) := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (ht i)
      have p1 := hu.nonneg i (r a'.1)
      have p2 := hu.nonneg i (r x)
      have p3 : (u i (r a'.1) (r a'.1)).toNat ≤ (u i (r x) (r x)).toNat := hle i
      exact_mod_cast (show u i (r a'.1) (r a'.1) ≤ u i (r x) (r x) by omega)
    show (∑ i, t i • toReal (u i)) (r (a M y)) (r (a M y)) ≤ (∑ i, t i • toReal (u i)) (r x) (r x)
    rw [hsum, hsum]
    linarith

end GlobalTheory.PolCell
