import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

private lemma valAt'_mul_of_preimage_whole {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f f' : Γ(Y, U)) : valAt' x U (f * f') = valAt' x U f * valAt' x U f' := by
  simp only [valAt', dif_pos h, valAt, map_mul]

private lemma valAt'_one' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    valAt' x U 1 = 1 := by
  simp only [valAt', dif_pos h, valAt, map_one]

private lemma preimage_whole_of_le {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (h : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ W :=
  fun _ ha => hVW (h ha)

private lemma preimage_inf_whole_of_whole {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hV : ⊤ ≤ x ⁻¹ᵁ V)
    (hW : ⊤ ≤ x ⁻¹ᵁ W) : ⊤ ≤ x ⁻¹ᵁ (V ⊓ W) :=
  fun _ ha => ⟨hV ha, hW ha⟩

private lemma valAt'_presheaf_map' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, W)) :
    valAt' x V ((Y.presheaf.map (homOfLE hVW).op).hom f) = valAt' x W f := by
  have hW : ⊤ ≤ x ⁻¹ᵁ W := preimage_whole_of_le x hVW h
  have key : Y.presheaf.map (homOfLE hVW).op ≫ x.appLE V ⊤ h = x.appLE W ⊤ hW := by
    rw [Scheme.Hom.map_appLE]
  simp only [valAt', dif_pos h, dif_pos hW, valAt]
  rw [← key]
  rfl

private lemma valAt'_res_units {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {V W : Y.Opens} (hVW : V ≤ W)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, W)ˣ) :
    valAt' x V ((res hVW f : Γ(Y, V)ˣ) : Γ(Y, V)) = valAt' x W (f : Γ(Y, W)) := by
  unfold res
  rw [Units.coe_map]
  exact valAt'_presheaf_map' x hVW h f

theorem exists_isLB_of_frames (X : Over (Sp ℂ)) {Z κ : Type} (ex : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (hex : Function.Surjective ex)
    (hext : ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X),
      ⊤ ≤ x.left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f')
    (U : κ → X.left.Opens) (hU : ⨆ i, U i = ⊤) (fr : κ → Z → ℂ)
    (hfr : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ U i → fr i z ≠ 0)
    (hreg : ∀ i j, ∃ φ : Γ(X.left, U i ⊓ U j), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ (U i ⊓ U j) →
      valAt' (ex z).left (U i ⊓ U j) φ = fr i z / fr j z) :
    ∃ tr : ∀ i j, Γ(X.left, U i ⊓ U j)ˣ, (LB.mk κ U tr).IsLB ∧ ∀ i j z,
      ⊤ ≤ (ex z).left ⁻¹ᵁ (U i ⊓ U j) →
        fr i z = valAt' (ex z).left (U i ⊓ U j) (tr i j).val * fr j z := by
  choose φ hφ using hreg
  have mem : ∀ (x : 𝟙_ (Over (Sp ℂ)) ⟶ X) {V W : X.left.Opens}, V ≤ W → ⊤ ≤ x.left ⁻¹ᵁ V →
      ⊤ ≤ x.left ⁻¹ᵁ W := fun x _ _ hVW h => preimage_whole_of_le x.left hVW h
  let ψ : ∀ i j, Γ(X.left, U i ⊓ U j) := fun i j =>
    (X.left.presheaf.map (homOfLE (inf_comm (U i) (U j)).le).op).hom (φ j i)
  have hψ : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ (U i ⊓ U j) →
      valAt' (ex z).left (U i ⊓ U j) (ψ i j) = fr j z / fr i z := by
    intro i j z hz
    rw [valAt'_presheaf_map' _ _ hz, hφ j i z (mem _ (inf_comm (U i) (U j)).le hz)]
  have hmul : ∀ i j, φ i j * ψ i j = 1 := by
    intro i j
    apply hext
    intro x hx
    obtain ⟨z, rfl⟩ := hex x
    rw [valAt'_mul_of_preimage_whole _ _ hx, valAt'_one' _ _ hx, hφ i j z hx, hψ i j z hx]
    have h1 := hfr i z (mem _ inf_le_left hx)
    have h2 := hfr j z (mem _ inf_le_right hx)
    rw [div_mul_div_comm, mul_comm (fr i z), div_self (mul_ne_zero h2 h1)]
  refine ⟨fun i j => Units.mkOfMulEqOne (φ i j) (ψ i j) (hmul i j), ⟨hU, fun i => ?_, fun i j k => ?_⟩, ?_⟩
  · apply Units.ext
    apply hext
    intro x hx
    obtain ⟨z, rfl⟩ := hex x
    rw [valAt'_res_units _ _ hx, Units.val_one, valAt'_one' _ _ hx]
    simp only [Units.val_mkOfMulEqOne]
    rw [hφ i i z (mem _ ?_ hx), div_self (hfr i z (mem _ ?_ hx))]
    all_goals simp
  · apply Units.ext
    apply hext
    intro x hx
    obtain ⟨z, rfl⟩ := hex x
    have pi := mem _ (inf_le_left.trans inf_le_left) hx
    have pj := mem _ (inf_le_left.trans inf_le_right) hx
    have pk := mem _ inf_le_right hx
    rw [Units.val_mul, valAt'_mul_of_preimage_whole _ _ hx, valAt'_res_units _ _ hx, valAt'_res_units _ _ hx,
      valAt'_res_units _ _ hx]
    simp only [Units.val_mkOfMulEqOne]
    rw [hφ i j z (preimage_inf_whole_of_whole _ pi pj), hφ j k z (preimage_inf_whole_of_whole _ pj pk), hφ i k z (preimage_inf_whole_of_whole _ pi pk)]
    have h1 := hfr i z pi
    have h2 := hfr j z pj
    have h3 := hfr k z pk
    field_simp
  · intro i j z hz
    simp only [Units.val_mkOfMulEqOne]
    rw [hφ i j z hz, div_mul_cancel₀ _ (hfr j z (mem _ inf_le_right hz))]

private lemma eC_even_mul_half_char_eq_one {g : ℕ} {a b : Fin g → ℝ} (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    {N : ℕ} (hN : Even N) (n n' : Fin g → ℤ) :
    eC ((N : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n)) = 1 := by
  have half : ∀ c : Fin g → ℝ, (∀ i, c i = 0 ∨ c i = 1 / 2) → ∃ p : Fin g → ℤ, ∀ i, (c i : ℂ) = (p i : ℂ) / 2 := by
    intro c hc
    refine ⟨fun i => if c i = 0 then 0 else 1, fun i => ?_⟩
    rcases hc i with h | h
    · simp [h]
    · have : c i ≠ 0 := by rw [h]; norm_num
      simp only [h]
      norm_num
  obtain ⟨p, hp⟩ := half a ha
  obtain ⟨q, hq⟩ := half b hb
  obtain ⟨m, rfl⟩ := hN
  have key : ((m + m : ℕ) : ℂ) * (ofRealVec a ⬝ᵥ ofIntVec n' - ofRealVec b ⬝ᵥ ofIntVec n) =
      ((∑ i, (m : ℤ) * p i * n' i - ∑ i, (m : ℤ) * q i * n i : ℤ) : ℂ) := by
    simp only [dotProduct, ofRealVec, ofIntVec, hp, hq]
    push_cast
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  rw [key, eC_int]

variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℝ}

theorem autFactor_pow_of_even (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) (hb : ∀ i, b i = 0 ∨ b i = 1 / 2)
    {N : ℕ} (hN : Even N) (n n' : Fin g → ℤ) (z : Fin g → ℂ) :
    autFactor a b τ n n' z ^ N =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) := by
  rw [autFactor, mul_pow, ← eC_nat_mul, ← eC_nat_mul, eC_even_mul_half_char_eq_one ha hb hN n n', _root_.one_mul]
  congr 1
  ring

theorem thetaLevelChar_eq_thetaLevel_of_even (ha : ∀ i, a i = 0 ∨ a i = 1 / 2)
    (hb : ∀ i, b i = 0 ∨ b i = 1 / 2) {N : ℕ} (hN : Even N) :
    thetaLevelChar a b N τ = thetaLevel N τ := by
  ext f
  rw [mem_thetaLevelChar, mem_thetaLevel]
  refine and_congr_right fun _ => forall_congr' fun n => forall_congr' fun n' => forall_congr' fun z => ?_
  rw [eC_even_mul_half_char_eq_one ha hb hN n n', _root_.one_mul]

private lemma exists_mem_open_ne_zero_of_differentiable {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (hf0 : f ≠ 0)
    {V : Set (Fin g → ℂ)} (hV : IsOpen V) (hVne : V.Nonempty) : ∃ z ∈ V, f z ≠ 0 := by
  by_contra h
  push Not at h
  have := SCV.eqOn_of_eqOn_open (f := f) (g := fun _ => 0) isOpen_univ isPreconnected_univ
    hf.differentiableOn (differentiable_const _).differentiableOn hV hVne (Set.subset_univ _) h
  exact hf0 (funext fun z => this (Set.mem_univ z))

theorem exists_mem_thetaLevelChar_apply_ne_zero (hτ : τ ∈ SiegelH (Fin g)) (a b : Fin g → ℝ)
    {k : ℕ} (hk : k ≠ 0) (z₀ : Fin g → ℂ) : ∃ F ∈ thetaLevelChar a b (k + 1) τ, F z₀ ≠ 0 := by
  set θ : (Fin g → ℂ) → ℂ := fun z => theta a b z τ with hθ
  have hθd : Differentiable ℂ θ := differentiable_theta hτ a b
  have hθ0 : θ ≠ 0 := theta_ne_zero hτ a b
  obtain ⟨q, hq⟩ : ∃ q, θ q ≠ 0 := by
    by_contra h
    push Not at h
    exact hθ0 (funext h)
  have hk' : (-(k : ℂ)) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hk)
  have hV : IsOpen {w : Fin g → ℂ | θ (z₀ + w) ≠ 0} :=
    isOpen_ne_fun (hθd.continuous.comp (continuous_const.add continuous_id)) continuous_const
  have hVne : ({w : Fin g → ℂ | θ (z₀ + w) ≠ 0}).Nonempty :=
    ⟨q - z₀, by simpa only [Set.mem_ofPred_eq, add_sub_cancel] using hq⟩
  have hhd : Differentiable ℂ (fun w : Fin g → ℂ => θ (z₀ + (-(k : ℂ)) • w)) :=
    hθd.comp (by fun_prop)
  have hh0 : (fun w : Fin g → ℂ => θ (z₀ + (-(k : ℂ)) • w)) ≠ 0 := by
    intro h0
    apply hq
    have := congrFun h0 ((-(k : ℂ))⁻¹ • (q - z₀))
    simpa only [smul_smul, mul_inv_cancel₀ hk', one_smul, add_sub_cancel, Pi.zero_apply] using this
  obtain ⟨w, hw1, hw2⟩ := exists_mem_open_ne_zero_of_differentiable hhd hh0 hV hVne
  refine ⟨fun z => ∏ i : Fin (k + 1), θ (z + if i = 0 then (-(k : ℂ)) • w else w), ?_, ?_⟩
  · have hsum : ∑ i ∈ (Finset.univ : Finset (Fin (k + 1))), ((fun _ => 1 : Fin (k + 1) → ℕ) i : ℂ) •
        (fun i : Fin (k + 1) => if i = 0 then (-(k : ℂ)) • w else w) i = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Nat.cast_one, one_smul, if_pos, Fin.succ_ne_zero, if_false, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ, neg_smul, neg_add_cancel]
    have := prod_translate_mem_thetaLevelChar (a := a) (b := b) (τ := τ)
      (Finset.univ : Finset (Fin (k + 1))) (d := fun _ => 1) (F := fun _ => θ)
      (fun _ _ => theta_mem_thetaLevelChar_one hτ) _ hsum
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, _root_.mul_one] using this
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    split_ifs
    · exact hw2
    · exact hw1

theorem exists_thetaBundle_holUnif :
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → SiegelSubDomainStatement → ThetaHoloStatement → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ N : ℕ, 3 ≤ N → ∀ (X : Over (Sp ℂ)) (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (D : (Fin g → Fin N) → X.left.Opens), (IsIntegral X.left ∧ IsProper X.hom ∧ Function.Surjective ex ∧ (∀ z z', ex z = ex z' ↔ z - z' ∈ periodLattice τ) ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (ex w).left U f) {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (ex w).left ⁻¹ᵁ U}) ∧ (∀ c, IsAffineOpen (D c) ∧ ringKrullDim Γ(X.left, D c) ≤ g ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0) ∧ ∃ r : (Fin g → Fin N) → Γ(X.left, D c), (∀ c' z, theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) ≠ 0 → valAt' (ex z).left (D c) (r c') = theta (fun i => ((c' i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ) / theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial (Fin g → Fin N) ℂ, f = MvPolynomial.eval₂ (RingHom.comp (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) ∧ (⨆ c, D c = ⊤)) → (∀ (d : ℕ) (p q : (Fin g → ℂ) → ℂ), (Differentiable ℂ p ∧ ∀ (n n' : Fin g → ℤ) z, p (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * p z) → (Differentiable ℂ q ∧ ∀ (n n' : Fin g → ℤ) z, q (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-((N * d : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * q z) → ∃ (U : X.left.Opens) (φ : Γ(X.left, U)), ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ U ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left U φ = p z / q z)) → Even N → ∀ [GrpObj X], (∀ z w, ex (z + w) = ex z * ex w) → ∀ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) → ∃ (L : LB X.left) (u : HolUnif X L g), L.IsLB ∧ u.ex = ex ∧ (∀ z, z ∈ u.Λ ↔ z ∈ periodLattice τ) ∧ (∀ (n n' : Fin g → ℤ) i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → u.fr i z = autFactor a b τ n n' z * u.fr i (z + τ *ᵥ ofIntVec n + ofIntVec n')) ∧ (∀ i, ∃ h F : (Fin g → ℂ) → ℂ, (Differentiable ℂ h ∧ ∀ (n n' : Fin g → ℤ) z, h (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * h z) ∧ Differentiable ℂ F ∧ (∀ (n n' : Fin g → ℤ) z, F (z + τ *ᵥ ofIntVec n + ofIntVec n') = autFactor a b τ n n' z * eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * F z) ∧ ∀ z, (⊤ ≤ (ex z).left ⁻¹ᵁ L.U i ↔ h z ≠ 0 ∧ F z ≠ 0) ∧ u.fr i z = h z / F z)) := by
  intro H1 _ _ _ H5 g τ hτ N hN3 X ex D hX hquot hNe _ hexadd a b ha hb
  obtain ⟨hInt, hProp, hsurj, hker, hhol, -, -⟩ := hX
  have : IsIntegral X.left := hInt
  have : IsProper X.hom := hProp
  have hN0 : N ≠ 0 := by omega
  have hext := H1 X inferInstance inferInstance
  have hlev : ∀ M, Even M → thetaLevelChar a b M τ = thetaLevel M τ :=
    fun M hM => thetaLevelChar_eq_thetaLevel_of_even ha hb hM
  have quot : ∀ p q : (Fin g → ℂ) → ℂ, p ∈ thetaLevelChar a b (N * (N + 2)) τ →
      q ∈ thetaLevelChar a b (N * (N + 2)) τ → ∃ (V : X.left.Opens) (φ : Γ(X.left, V)), ∀ z,
        (⊤ ≤ (ex z).left ⁻¹ᵁ V ↔ q z ≠ 0) ∧ (q z ≠ 0 → valAt' (ex z).left V φ = p z / q z) := by
    intro p q hp hq
    rw [hlev _ (hNe.mul_right _)] at hp hq
    exact hquot (N + 2) p q (mem_thetaLevel.mp hp) (mem_thetaLevel.mp hq)
  let κ : Type := {p : ((Fin g → ℂ) → ℂ) × ((Fin g → ℂ) → ℂ) //
    p.1 ∈ thetaLevel N τ ∧ p.2 ∈ thetaLevelChar a b (N + 1) τ}
  have hF : ∀ i : κ, i.1.2 ∈ thetaLevelChar a b (N + 1) τ := fun i => i.2.2
  have hh : ∀ i : κ, i.1.1 ∈ thetaLevelChar a b N τ := fun i => by
    rw [hlev N hNe]
    exact i.2.1
  have hchart : ∀ i : κ, ∃ V : X.left.Opens, ∀ z,
      (⊤ ≤ (ex z).left ⁻¹ᵁ V ↔ i.1.1 z ≠ 0 ∧ i.1.2 z ≠ 0) := by
    intro i
    have hq : i.1.1 * i.1.2 ^ N ∈ thetaLevelChar a b (N * (N + 2)) τ := by
      have e : N * (N + 2) = N + N * (N + 1) := by ring
      rw [e]
      exact mul_mem_thetaLevelChar (hh i) (pow_mem_thetaLevelChar (hF i) N)
    obtain ⟨V, _, hV⟩ := quot _ _ hq hq
    refine ⟨V, fun z => (hV z).1.trans ?_⟩
    simp only [Pi.mul_apply, Pi.pow_apply, ne_eq, mul_eq_zero, pow_eq_zero_iff hN0, not_or]
  choose V hV using hchart
  let fr : κ → (Fin g → ℂ) → ℂ := fun i z => i.1.1 z / i.1.2 z
  have hfr : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ V i → fr i z ≠ 0 :=
    fun i z hz => div_ne_zero ((hV i z).1 hz).1 ((hV i z).1 hz).2
  have pt : ∀ x : Sp ℂ ⟶ X.left, x ≫ X.hom = 𝟙 _ → ∃ z, (ex z).left = x := by
    intro x hx
    obtain ⟨z, hz⟩ := hsurj (Over.homMk x (by simpa using hx))
    exact ⟨z, by rw [hz]; rfl⟩
  have hcov : ⨆ i, V i = ⊤ := by
    refine ComplexPoints.iSup_eq_top_of_complexPoints X.hom V fun x hx => ?_
    obtain ⟨z, rfl⟩ := pt x hx
    obtain ⟨F, hFm, hFz⟩ := exists_mem_thetaLevelChar_apply_ne_zero hτ a b hN0 z
    obtain ⟨h, hhm, hhz⟩ := exists_mem_thetaLevelChar_apply_ne_zero hτ 0 0 (k := N - 1) (by omega) z
    rw [Nat.sub_add_cancel (by omega), thetaLevelChar_zero] at hhm
    exact ⟨⟨(h, F), hhm, hFm⟩, (hV _ z).2 ⟨hhz, hFz⟩⟩
  have hreg : ∀ i j : κ, ∃ φ : Γ(X.left, V i ⊓ V j), ∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ (V i ⊓ V j) →
      valAt' (ex z).left (V i ⊓ V j) φ = fr i z / fr j z := by
    intro i j
    have hp : i.1.1 * j.1.2 * i.1.2 ^ (N - 1) ∈ thetaLevelChar a b (N * (N + 2)) τ := by
      have e : N * (N + 2) = N + (N + 1) + (N - 1) * (N + 1) := by
        obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
        rw [hM, Nat.add_sub_cancel]
        ring
      rw [e]
      exact mul_mem_thetaLevelChar (mul_mem_thetaLevelChar (hh i) (hF j)) (pow_mem_thetaLevelChar (hF i) _)
    have hq : j.1.1 * i.1.2 ^ N ∈ thetaLevelChar a b (N * (N + 2)) τ := by
      have e : N * (N + 2) = N + N * (N + 1) := by ring
      rw [e]
      exact mul_mem_thetaLevelChar (hh j) (pow_mem_thetaLevelChar (hF i) N)
    obtain ⟨W, φ, hW⟩ := quot _ _ hp hq
    have hVW : V i ⊓ V j ≤ W := by
      refine ComplexPoints.opens_le_of_complexPoints X.hom _ _ fun x hx hxV => ?_
      obtain ⟨z, rfl⟩ := pt x hx
      have hi := (hV i z).1 (preimage_whole_of_le _ inf_le_left hxV)
      have hj := (hV j z).1 (preimage_whole_of_le _ inf_le_right hxV)
      refine (hW z).1.2 ?_
      simp only [Pi.mul_apply, Pi.pow_apply]
      exact mul_ne_zero hj.1 (pow_ne_zero _ hi.2)
    refine ⟨(X.left.presheaf.map (homOfLE hVW).op).hom φ, fun z hz => ?_⟩
    have hi := (hV i z).1 (preimage_whole_of_le _ inf_le_left hz)
    have hj := (hV j z).1 (preimage_whole_of_le _ inf_le_right hz)
    have hq0 : (j.1.1 * i.1.2 ^ N) z ≠ 0 := by
      simp only [Pi.mul_apply, Pi.pow_apply]
      exact mul_ne_zero hj.1 (pow_ne_zero _ hi.2)
    rw [valAt'_presheaf_map' _ hVW hz, (hW z).2 hq0]
    have hpow : i.1.2 z ^ N = i.1.2 z ^ (N - 1) * i.1.2 z := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    simp only [fr, Pi.mul_apply, Pi.pow_apply]
    rw [hpow]
    have h1 := hi.1
    have h2 := hi.2
    have h3 := hj.1
    have h4 := hj.2
    field_simp
  obtain ⟨tr, hLB, hcompat⟩ := exists_isLB_of_frames X ex hsurj hext V hcov fr hfr hreg
  have hex0 : ex 0 = 1 := by
    obtain ⟨z1, hz1⟩ := hsurj 1
    have := hexadd z1 0
    rw [add_zero, hz1, _root_.one_mul] at this
    exact this.symm
  let u : HolUnif X (LB.mk κ V tr) g :=
    { ex := ex
      ex_add := hexadd
      ex_onto := hsurj
      Λ := (periodLattice τ).toIntSubmodule
      ker := fun z => by
        rw [← hex0, hker, sub_zero]
        exact Iff.rfl
      discrete := (H5 g τ hτ).1
      full := (H5 g τ hτ).2.1
      hol := fun W f => by
        simpa only [Set.mem_univ, true_and] using hhol W f
      fr := fr
      fr_hol := fun i => by
        have dh := (mem_thetaLevel.mp i.2.1).1
        have dF := (mem_thetaLevelChar.mp i.2.2).1
        intro z hz
        have hd := (dh z).mul ((dF z).inv ((hV i z).1 hz).2)
        exact (hd.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun w => div_eq_mul_inv _ _)).differentiableWithinAt
      fr_ne := hfr
      fr_compat := hcompat }
  refine ⟨LB.mk κ V tr, u, hLB, rfl, fun z => Iff.rfl, ?_, ?_⟩
  · intro n n' i z hz
    have hi := (hV i z).1 hz
    have hA : autFactor a b τ n n' z ≠ 0 := by
      rw [autFactor]
      exact mul_ne_zero (eC_ne_zero _) (eC_ne_zero _)
    have h1 := (mem_thetaLevelChar_iff_autFactor.mp (hh i)).2 n n' z
    have h2 := (mem_thetaLevelChar_iff_autFactor.mp (hF i)).2 n n' z
    show i.1.1 z / i.1.2 z = autFactor a b τ n n' z *
      (i.1.1 (z + τ *ᵥ ofIntVec n + ofIntVec n') / i.1.2 (z + τ *ᵥ ofIntVec n + ofIntVec n'))
    rw [h1, h2, pow_succ]
    have h3 := hi.2
    have h4 := pow_ne_zero N hA
    field_simp
  · intro i
    refine ⟨i.1.1, i.1.2, mem_thetaLevel.mp i.2.1, (mem_thetaLevelChar.mp i.2.2).1,
      fun n n' z => ?_, fun z => ⟨hV i z, rfl⟩⟩
    rw [(mem_thetaLevelChar_iff_autFactor.mp i.2.2).2 n n' z, pow_succ', autFactor_pow_of_even ha hb hNe]

end GlobalTheory
