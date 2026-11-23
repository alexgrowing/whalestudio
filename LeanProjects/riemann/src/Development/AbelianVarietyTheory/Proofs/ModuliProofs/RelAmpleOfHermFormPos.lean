import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.UnimodularAndTangentOfIsAH
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EvalDivOfIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RelAmpleThetaBundleProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsThetaSeriesApplyNeZeroOfLargeForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfLifting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfComplementary

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PositiveAmple

theorem valAt'_g_linComb {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (j j' : K → L.ι) (x : Sp ℂ ⟶ Y) (h : ⊤ ≤ x ⁻¹ᵁ ((LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ ε).U j')) :
    valAt' x _ ((LB.LinComb L φ ε).g j j').val =
      ∏ k, valAt' (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  refine (valAt'_units_prod x h _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  refine (valAt'_units_zpow x h _ _).trans (congrArg (· ^ ε k) ?_)
  exact (valAt'_map x _ _ h).trans (valAt'_comp x (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val)

theorem top_le_preimage_linComb {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (j : K → L.ι) (x : Sp ℂ ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ (LB.LinComb L φ ε).U j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  simp only [top_le_preimage_iff_mem]
  exact Set.mem_iInter

theorem ext_of_values {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom]
    {Z : Type} (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (hex : Function.Surjective ex) (U : X.left.Opens)
    (a b : Γ(X.left, U))
    (h : ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ U → valAt' (ex z).left U a = valAt' (ex z).left U b) : a = b :=
  eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom X inferInstance inferInstance U a b fun x hx => by
    obtain ⟨z, rfl⟩ := hex x
    exact h z hx

theorem le_of_values {X : Over (Sp ℂ)} [LocallyOfFiniteType X.hom]
    {Z : Type} (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (hex : Function.Surjective ex) (U V : X.left.Opens)
    (H : ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ U → ⊤ ≤ (ex z).left ⁻¹ᵁ V) : U ≤ V :=
  ThetaAmple.opens_le_of_points X.hom fun x hx => by
    obtain ⟨z, hz⟩ := hex (Over.homMk x hx)
    have e : (ex z).left = x := by rw [hz]; rfl
    exact e ▸ H z

theorem exists_fn_of_values {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom]
    {Z : Type} (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (hex : Function.Surjective ex) (U : X.left.Opens) (v : Z → ℂ)
    (hreg : ∀ z₀, ⊤ ≤ (ex z₀).left ⁻¹ᵁ U → ∃ (W : X.left.Opens) (φ : Γ(X.left, W)), W ≤ U ∧
      ⊤ ≤ (ex z₀).left ⁻¹ᵁ W ∧ ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ W → valAt' (ex z).left W φ = v z) :
    ∃ a : Γ(X.left, U), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ U → valAt' (ex z).left U a = v z := by
  choose W φ hle hz hφ using fun z : {z // ⊤ ≤ (ex z).left ⁻¹ᵁ U} => hreg z.1 z.2
  have cov : U ≤ iSup W := le_of_values ex hex _ _ fun z h =>
    top_le_preimage_mono _ (le_iSup W ⟨z, h⟩) (hz ⟨z, h⟩)
  obtain ⟨a, ha, -⟩ := X.left.sheaf.existsUnique_gluing' W U (fun z => homOfLE (hle z)) cov φ (by
    intro p q
    refine ext_of_values ex hex _ _ _ fun z h => ?_
    obtain ⟨hp, hq⟩ := (top_le_preimage_inf (ex z).left _ _).1 h
    refine (valAt'_map (ex z).left _ (φ p) h).trans (Eq.trans ?_ (valAt'_map (ex z).left _ (φ q) h).symm)
    rw [hφ p z hp, hφ q z hq])
  refine ⟨a, fun z h => ?_⟩
  rw [← hφ ⟨z, h⟩ z (hz ⟨z, h⟩), ← ha ⟨z, h⟩]
  exact (valAt'_map (ex z).left _ a (hz ⟨z, h⟩)).symm

theorem exists_sec_of_values {X : Over (Sp ℂ)} [IsReduced X.left] [LocallyOfFiniteType X.hom] {M : LB X.left}
    {Z : Type} (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (hex : Function.Surjective ex) (v : M.ι → Z → ℂ)
    (hv : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ (M.U i ⊓ M.U j) →
      v i z = valAt' (ex z).left (M.U i ⊓ M.U j) (M.g i j).val * v j z)
    (hreg : ∀ i z₀, ⊤ ≤ (ex z₀).left ⁻¹ᵁ M.U i → ∃ (W : X.left.Opens) (φ : Γ(X.left, W)), W ≤ M.U i ∧
      ⊤ ≤ (ex z₀).left ⁻¹ᵁ W ∧ ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ W → valAt' (ex z).left W φ = v i z) :
    ∃ t : M.Sec, ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ M.U i → valAt' (ex z).left (M.U i) (t.f i) = v i z := by
  choose a ha using fun i => exists_fn_of_values ex hex (M.U i) (v i) (hreg i)
  refine ⟨⟨a, fun i j => ext_of_values ex hex _ _ _ fun z h => ?_⟩, ha⟩
  obtain ⟨hi, hj⟩ := (top_le_preimage_inf _ _ _).1 h
  rw [valAt'_mul, valAt'_map _ _ _ h, valAt'_map _ _ _ h, ha i z hi, ha j z hj]
  exact hv i j z h

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem exists_sec_locus [IsReduced A.left] [LocallyOfFiniteType A.hom] (u : HolUnif A L g) (hL : L.IsLB)
    (f : A ⟶ A) (F : (Fin g → ℂ) → (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (κ N : ℕ) {I : Type}
    (s : I → (lbPow L N).Sec) (hs : ⨆ i, Out.nonzeroLocus (s i) = ⊤) (θ : I → (Fin g → ℂ) → ℂ)
    (hθ : ∀ i, u.IsFnPow N (s i) (θ i)) (ψ : (Fin g → ℂ) → ℂ) (t : I → (lbPow L (κ * N)).Sec)
    (ht : ∀ i, u.IsFnPow (κ * N) (t i) fun z => θ i (F z) * ψ z) :
    ∃ r : (lbPow (LB.LinComb L (K := Fin 2) ![𝟙 A.left, f.left] ![(κ : ℤ), -1]) N).Sec,
      ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus r ↔ ψ z ≠ 0 := by
  set M := LB.LinComb L (K := Fin 2) ![𝟙 A.left, f.left] ![(κ : ℤ), -1] with hM
  have hFl : ∀ z, (u.ex z).left ≫ f.left = (u.ex (F z)).left := fun z => by rw [hF]; rfl
  have ch : ∀ (J : (lbPow M N).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow M N).U J ↔
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (J PUnit.unit 0) ∧ ⊤ ≤ (u.ex (F z)).left ⁻¹ᵁ L.U (J PUnit.unit 1) := fun J z => by
    rw [Cartier.lbPow_U M N J, ← hFl]
    exact (top_le_preimage_linComb L _ _ _ _).trans Fin.forall_fin_two
  obtain ⟨r, hr⟩ := exists_sec_of_values (M := lbPow M N) u.ex u.ex_onto
    (fun J z => ψ z * (u.fr (J PUnit.unit 0) z ^ κ / u.fr (J PUnit.unit 1) (F z)) ^ N) (fun J J' z h => by
      obtain ⟨h₁, h₂⟩ := (top_le_preimage_inf _ _ _).1 h
      have a₀ := (top_le_preimage_inf _ _ _).2 ⟨((ch J z).1 h₁).1, ((ch J' z).1 h₂).1⟩
      have a₁ := (top_le_preimage_inf _ _ _).2 ⟨((ch J z).1 h₁).2, ((ch J' z).1 h₂).2⟩
      have e := valAt'_g_linComb L ![𝟙 A.left, f.left] ![(κ : ℤ), -1] (J PUnit.unit) (J' PUnit.unit)
        (u.ex z).left ((top_le_preimage_inf _ _ _).2 ⟨Cartier.lbPow_U M N J ▸ h₁, Cartier.lbPow_U M N J' ▸ h₂⟩)
      rw [valAt'_g_linComb M _ _ J J' _ h, Fintype.prod_unique, Category.comp_id]
      erw [e]
      rw [Fin.prod_univ_two, u.fr_compat _ _ _ a₀, u.fr_compat _ _ _ a₁]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, hFl, zpow_natCast, zpow_neg, zpow_one]
      ring) (fun J z₀ h₀ => by
      obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u.ex (F z₀)).left _ hs
      have l₀ : (lbPow M N).U J ≤ (lbPow L (κ * N)).U fun _ => J PUnit.unit 0 := by
        rw [Cartier.lbPow_U, Cartier.lbPow_U M N J]
        exact LB.wchart_le L ![𝟙 A.left, f.left] (J PUnit.unit) 0
      have l₁ : (lbPow M N).U J ≤ f.left ⁻¹ᵁ (lbPow L N).U fun _ => J PUnit.unit 1 := by
        rw [Cartier.lbPow_U, Cartier.lbPow_U M N J]
        exact LB.wchart_le L ![𝟙 A.left, f.left] (J PUnit.unit) 1
      have vb : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow M N).U J →
          valAt' (u.ex z).left _ ((f.left.appLE _ _ l₁).hom ((s i).f _)) =
            θ i (F z) * u.fr (J PUnit.unit 1) (F z) ^ N := fun z hz => by
        rw [valAt'_appLE _ _ _ _ _ _ hz, hFl]
        exact hθ i _ _ (by rw [Cartier.lbPow_U]; exact ((ch J z).1 hz).2)
      obtain ⟨φ, hφ⟩ := ThetaQuotient.exists_div_basicOpen (resG _ l₀ ((t i).f _))
        ((f.left.appLE _ _ l₁).hom ((s i).f _))
      refine ⟨_, φ, Scheme.basicOpen_le _ _, ?_, fun z hz => ?_⟩
      · rw [top_le_preimage_basicOpen_iff, vb z₀ h₀]
        exact mul_ne_zero ((LatticeHom.le_preimage_nonzeroLocus_iff u hL (hθ i) _).1 hi)
          (pow_ne_zero _ (u.fr_ne _ _ ((ch J z₀).1 h₀).2))
      · have hz' := top_le_preimage_mono _ (Scheme.basicOpen_le _ _) hz
        have hb := (top_le_preimage_basicOpen_iff _ _ _).1 hz
        rw [vb z hz'] at hb
        rw [hφ _ hz, vb z hz', valAt'_res _ _ _ hz', ht i _ z (top_le_preimage_mono _ l₀ hz'), div_pow, ← pow_mul,
          _root_.mul_assoc, mul_div_mul_left _ _ (left_ne_zero_of_mul hb), mul_div_assoc])
  refine ⟨r, fun z => (ThetaAmple.top_le_preimage_iSup _ _).trans ⟨fun ⟨J, hJ⟩ => ?_, fun h => ?_⟩⟩
  · have h1 := (top_le_preimage_basicOpen_iff _ _ _).1 hJ
    rw [hr J z (top_le_preimage_of_valAt'_ne_zero _ h1)] at h1
    exact left_ne_zero_of_mul h1
  · obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u.ex z).left _ hL.cover
    obtain ⟨j, hj⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u.ex (F z)).left _ hL.cover
    refine ⟨fun _ => ![i, j], ?_⟩
    refine (top_le_preimage_basicOpen_iff _ _ _).2
      ((hr (fun _ => ![i, j]) z ((ch (fun _ => ![i, j]) z).2 ⟨hi, hj⟩)).trans_ne ?_)
    exact mul_ne_zero h (pow_ne_zero _ (div_ne_zero (pow_ne_zero _ (u.fr_ne _ _ hi)) (u.fr_ne _ _ hj)))

open Complex Matrix LatticeHom in

theorem exists_complementary (u : HolUnif A L g) (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u.Λ) (κ : ℕ)
    (hpos : ∀ z, z ≠ 0 → (hermForm Hm (F z) (F z)).re < κ * (hermForm Hm z z).re) (a : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧ ∀ θ θ₁, u.IsThetaFn Hm χ N θ →
      u.IsThetaFn Hm χ a θ₁ → u.IsThetaFn Hm χ (κ * N) (fun z => θ (F z) * (θ₁ z * G z)) := by
  obtain ⟨K, hK, hKF⟩ := exists_hermForm_pull h.1 F
  have hform : ∀ (c d : ℂ) z w, hermForm (c • Hm - d • K) z w =
      c * hermForm Hm z w - d * hermForm Hm (F z) (F w) := fun c d z w => by
    rw [← hKF]
    simp only [hermForm, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hre : ∀ z, (hermForm ((κ : ℂ) • Hm - (1 : ℂ) • K) z z).re =
      κ * (hermForm Hm z z).re - (hermForm Hm (F z) (F z)).re := fun z => by
    rw [hform]
    simp only [sub_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, _root_.one_mul]
  have hp : ∀ z, z ≠ 0 → 0 < (hermForm ((κ : ℂ) • Hm - (1 : ℂ) • K) z z).re := fun z hz => by
    rw [hre]
    exact sub_pos.2 (hpos z hz)
  obtain ⟨ρ, hρ⟩ := ThetaLarge.exists_theta_apply_ne_zero g u.Λ u.discrete u.full _ hp
  obtain ⟨C, hC⟩ := exists_le_mul_of_homogeneous _ _ (continuous_re_hermForm _) (continuous_re_hermForm Hm) hp
    (re_hermForm_real_smul _) (re_hermForm_real_smul Hm)
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (ρ + a * C)
  let φ : u.Λ → u.Λ := fun l => ⟨F l, hF l l.2⟩
  have hφ : ∀ l m, φ (l + m) = φ l + φ m := fun l m => Subtype.ext (map_add F _ _)
  have hχ : ∀ l, χ l ≠ 0 := fun l h0 => by simpa [h0] using h.2.2.1 l
  refine ⟨N₀, fun N hN z₀ => ?_⟩
  have hform' : ∀ z w, z ⬝ᵥ (((κ * N : ℕ) - a : ℂ) • Hm - (N : ℂ) • K).mulVec (star w) =
      ((κ * N : ℕ) - a : ℂ) * hermForm Hm z w - N * hermForm Hm (F z) (F w) := hform _ _
  refine (hρ (((κ * N : ℕ) - a : ℂ) • Hm - (N : ℂ) • K) (fun l => χ l ^ (κ * N) / (χ l ^ a * χ (φ l) ^ N))
    ((h.1.smul ((IsSelfAdjoint.natCast _).sub (IsSelfAdjoint.natCast _))).sub (hK.smul (IsSelfAdjoint.natCast N)))
    (fun z => ?_) (fun l => ?_) (fun l m => ?_) z₀).elim ?_
  rotate_right
  · rintro G ⟨hGd, hG0, hG⟩
    refine ⟨G, hG0, fun θ θ₁ hθ hθ₁ => ⟨?_, fun l z => ?_⟩⟩
    · exact (hθ.1.comp F.toContinuousLinearMap.differentiable).mul (hθ₁.1.mul hGd)
    · have h1 := hθ.2 (φ l) (F z)
      have h2 := hχ (φ l)
      have h3 := hχ l
      have he : cexp (Real.pi * hermForm Hm (F z) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) ^ N *
          cexp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ a *
          cexp (Real.pi * (((κ * N : ℕ) - a : ℂ) * hermForm Hm z l - N * hermForm Hm (F z) (F l)) +
            Real.pi / 2 * (((κ * N : ℕ) - a : ℂ) * hermForm Hm l l - N * hermForm Hm (F l) (F l))) =
          cexp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ (κ * N) := by
        rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        ring
      change θ (F z + F l) = (_ * cexp (Real.pi * hermForm Hm (F z) (F l) +
        Real.pi / 2 * hermForm Hm (F l) (F l))) ^ N * _ at h1
      change θ (F (z + l)) * (θ₁ (z + l) * G (z + l)) = _ * (θ (F z) * (θ₁ z * G z))
      rw [map_add, h1, hθ₁.2, hG, hform', hform', mul_pow, mul_pow, mul_pow, ← he]
      field_simp
  · rw [hform']
    change ρ * (hermForm _ z z).re ≤ _
    have h0 : 0 ≤ (hermForm ((κ : ℂ) • Hm - (1 : ℂ) • K) z z).re := by
      by_cases hz : z = 0
      · simp [hz, hermForm]
      · exact (hp z hz).le
    have h1 := mul_le_mul_of_nonneg_left (hC z) (Nat.cast_nonneg (α := ℝ) a)
    have h2 := mul_le_mul_of_nonneg_right (hN₀.trans (Nat.cast_le.2 hN)) h0
    simp only [sub_re, mul_re, sub_im, natCast_re, natCast_im, zero_mul, sub_zero]
    rw [hre] at h1 h2 ⊢
    push_cast
    linarith
  · simp only [norm_div, norm_mul, norm_pow, h.2.2.1, one_pow, div_one, _root_.mul_one]
  · have h2 := hχ (φ l)
    have h3 := hχ (φ m)
    have h4 := hχ l
    have h5 := hχ m
    have he : cexp (Real.pi * I * (hermForm Hm l m).im) ^ (κ * N) =
        cexp (Real.pi * I * (((κ * N : ℕ) - a : ℂ) * hermForm Hm l m - N * hermForm Hm (F l) (F m)).im) *
        cexp (Real.pi * I * (hermForm Hm l m).im) ^ a * cexp (Real.pi * I * (hermForm Hm (φ l) (φ m)).im) ^ N := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [φ, sub_im, sub_re, mul_im, natCast_re, natCast_im, zero_mul, add_zero, sub_zero]
      push_cast
      ring
    have h6 := Complex.exp_ne_zero (Real.pi * I * (hermForm Hm (φ l) (φ m)).im)
    have h7 := Complex.exp_ne_zero (Real.pi * I * (hermForm Hm l m).im)
    rw [hφ, semicharacter_add u hL h, semicharacter_add u hL h, hform']
    simp only [mul_pow]
    rw [he]
    field_simp

theorem isAmpleLB_of_theta (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ)
    (hsec : ∀ (k : ℕ) θ, u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ)
    (hfn : ∀ (k : ℕ) s, ∃ θ, u.IsThetaFn Hm χ k θ ∧ u.IsFnPow k s θ) (f : P.A ⟶ P.A)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (κ : ℕ)
    (hpos : ∀ z, z ≠ 0 → (hermForm Hm (F z) (F z)).re < κ * (hermForm Hm z z).re) :
    IsAmpleLB (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) := by
  have hsm := P.isAb.smooth
  have : IsReduced P.A.left := isReduced_of_smooth_complex _ P.A.hom hsm
  have hM := LB.isLB_linComb P.isLB (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]
  have hL := isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample
  have hΛ : ∀ l ∈ u.Λ, F l ∈ u.Λ := fun l hl => by
    rw [← u.ker, hF, (u.ker l).2 hl, ← (u.ker 0).2 u.Λ.zero_mem, ← hF, map_zero]
  have le := le_of_values u.ex u.ex_onto
  obtain ⟨a, ha, m, s, hs, haff⟩ := hL.exists_cover
  obtain ⟨N₀, hN₀⟩ := exists_complementary u P.isLB h F hΛ κ hpos a
  have hN : 1 ≤ a * (N₀ + 1) := Nat.mul_pos ha N₀.succ_pos
  have hs' : ⨆ i, Out.nonzeroLocus (secPow (s i) (N₀ + 1)) = ⊤ := by
    simp only [nonzeroLocus_secPow _ N₀.succ_pos, hs]
  choose θ hθ hθs using fun i => hfn _ (secPow (s i) (N₀ + 1))
  have key : ∀ z₀, ∃ r : (lbPow (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1])
      (a * (N₀ + 1))).Sec, ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ Out.nonzeroLocus r ∧ IsAffineOpen (Out.nonzeroLocus r) := by
    intro z₀
    obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u.ex z₀).left _ hs
    obtain ⟨θ₁, hθ₁, hθ₁s⟩ := hfn a (s i)
    have hmem := LatticeHom.le_preimage_nonzeroLocus_iff u P.isLB hθ₁s
    obtain ⟨G, hG0, hG⟩ := hN₀ (a * (N₀ + 1)) (N₀.le_succ.trans (Nat.le_mul_of_pos_left _ ha)) z₀
    choose t ht using fun j => hsec _ _ (hG _ _ (hθ j) hθ₁)
    obtain ⟨r, hr⟩ := exists_sec_locus u P.isLB f F hF κ _ _ hs' θ hθs (fun z => θ₁ z * G z) t ht
    refine ⟨r, (hr z₀).2 (mul_ne_zero ((hmem z₀).1 hi) hG0), ?_⟩
    have hle := le _ _ fun z hz => (hmem z).2 (left_ne_zero_of_mul ((hr z).1 hz))
    exact inf_eq_left.2 hle ▸ isAffineOpen_nonzeroLocus_inf (isLB_lbPow hM _) r (haff i)
  choose r hr hra using key
  refine ⟨hM, hL.compactSpace, fun x => ?_⟩
  obtain ⟨z, hz⟩ := TopologicalSpace.Opens.mem_iSup.1 (le ⊤ (⨆ z, Out.nonzeroLocus (r z))
    (fun z _ => top_le_preimage_mono _ (le_iSup (fun z => Out.nonzeroLocus (r z)) z) (hr z)) (Set.mem_univ x))
  exact ⟨_, hN, r z, hz, hra z⟩

end GlobalTheory.PositiveAmple

namespace GlobalTheory

open PositiveAmple in

theorem relAmple_of_hermForm_pos : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (f : P.A ⟶ P.A) (F : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)) (κ : ℕ), u.IsAH Hm χ → IsMonHom f → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, z ≠ 0 → (hermForm Hm (F z) (F z)).re < κ * (hermForm Hm z z).re) → Out.RelAmple P.A (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, f.left] ![(κ : ℤ), -1]) := by
  intro hL _ hT P u Hm χ f F κ hu _ hF hpos
  have := P.isAb.proper
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨v, H₀, χ₀, -, hv, -, -, -, -, hsec, -⟩ := hT P rig hrig
  obtain ⟨T, hTv⟩ := LatticeHom.exists_linearEquiv_of_holUnif hL.mulN P u v
  have hH := UnifCompare.hermForm_eq P.isLB u v hu hv T.toLinearMap hTv
  refine (relAmple_iff_isAmpleLB_of_isAffine P.A (LB.isLB_linComb P.isLB _ _)).2
    (isAmpleLB_of_theta P v hv (fun k θ h => ((hsec k).2 θ h).exists) (fun k s => ((hsec k).1 s).exists) f
      (T.toLinearMap ∘ₗ F ∘ₗ T.symm.toLinearMap) (fun z => ?_) κ fun z hz => ?_)
  · obtain ⟨z, rfl⟩ := T.surjective z
    simp [hTv, hF]
  · obtain ⟨z, rfl⟩ := T.surjective z
    simpa [← hH] using hpos z (fun h0 => hz (by rw [h0, map_zero]))

end GlobalTheory
