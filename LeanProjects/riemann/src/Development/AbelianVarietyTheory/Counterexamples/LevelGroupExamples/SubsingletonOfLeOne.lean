import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAddRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodFormAdditiveBalancedPosDefBoundedRank

noncomputable section

namespace GlobalTheory.PointLawsEdge

open Filter Topology Matrix in

theorem real_pos_of_int_ge {ι : Type} [Fintype ι] (M : ι → ι → ℝ) (hs : ∀ i k, M i k = M k i) {c : ℝ} (hc : 0 < c)
    (hM : ∀ z : ι → ℤ, z ≠ 0 → c ≤ ∑ i, ∑ k, (z i : ℝ) * z k * M i k) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ k, x i * x k * M i k := by
  classical
  set Q : (ι → ℝ) → ℝ := fun y => ∑ i, ∑ k, y i * y k * M i k with hQdef
  have hQc : Continuous Q := by simp only [hQdef]; fun_prop
  have hM0 : ∀ z : ι → ℤ, 0 ≤ Q fun i => z i := by
    intro z
    by_cases hz : z = 0
    · simp [hz, hQdef]
    · exact hc.le.trans (hM z hz)
  have hQ : ∀ q : ι → ℚ, 0 ≤ Q fun i => q i := by
    intro q
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
    choose z hz using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero d.2
    have hz' : ∀ i, (z i : ℝ) = ((d : ℤ) : ℝ) * (q i : ℝ) := by
      intro i
      have h := hz i
      simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul] at h
      have := congrArg (fun t : ℚ => (t : ℝ)) h
      simpa using this
    have h1 := hM0 z
    have h2 : (Q fun i => z i) = ((d : ℤ) : ℝ) ^ 2 * Q fun i => q i := by
      simp only [hQdef, Finset.mul_sum, hz']
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [h2] at h1
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h1
  have hR : ∀ y, 0 ≤ Q y := by
    intro y
    have hdr : DenseRange (Pi.map (fun (_ : ι) (q : ℚ) => (q : ℝ))) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    exact hdr.induction_on y (isClosed_le continuous_const hQc) fun q => hQ q
  have hform : ∀ y : ι → ℝ, star y ⬝ᵥ (Matrix.of M) *ᵥ y = Q y := by
    intro y
    simp only [hQdef, dotProduct, mulVec, Finset.mul_sum, star_trivial, of_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hpsd : (Matrix.of M).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun y => by rw [hform]; exact hR y⟩
    ext i k
    simp [hs i k]
  refine (hR x).lt_of_ne fun h0 => ?_
  have hker : (Matrix.of M) *ᵥ x = 0 := (hpsd.dotProduct_mulVec_zero_iff x).1 ((hform x).trans h0.symm)
  have hker' : x ᵥ* (Matrix.of M) = 0 := by
    ext k
    have := congrFun hker k
    simp only [mulVec, vecMul, dotProduct, of_apply, Pi.zero_apply] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i k, mul_comm]
  have hshift : ∀ (y : ι → ℝ) (t : ℝ), Q (y + t • x) = Q y := by
    intro y t
    rw [← hform, ← hform]
    simp only [star_trivial, mulVec_add, mulVec_smul, hker, smul_zero, add_zero, add_dotProduct, smul_dotProduct,
      dotProduct_mulVec x, hker', zero_dotProduct]
  let u : ℕ → ι → ℝ := fun n i => Int.fract ((n : ℝ) * x i)
  have hu : ∀ n, u n ∈ Set.Icc (0 : ι → ℝ) 1 := fun n =>
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hu
  have hd : Tendsto (fun k => u (φ (k + 1)) - u (φ k)) atTop (𝓝 0) := by
    have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    simpa using this
  have h1 : ∀ᶠ k in atTop, Q (u (φ (k + 1)) - u (φ k)) < c := by
    have := (hQc.tendsto 0).comp hd
    refine this.eventually (gt_mem_nhds ?_)
    simpa [hQdef] using hc
  have h2 : ∀ᶠ k in atTop, ‖u (φ (k + 1)) - u (φ k)‖ < ‖x‖ :=
    hd.norm.eventually (gt_mem_nhds (by simpa using hx))
  obtain ⟨k, h1, h2⟩ := (h1.and h2).exists
  let z : ι → ℤ := fun i => ⌊(φ k : ℝ) * x i⌋ - ⌊(φ (k + 1) : ℝ) * x i⌋
  have e : u (φ (k + 1)) - u (φ k) = (fun i => (z i : ℝ)) + ((φ (k + 1) : ℝ) - φ k) • x := by
    ext i
    simp only [u, z, Int.fract, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e] at h1 h2
  by_cases hz : z = 0
  · have h3 : (φ k : ℝ) + 1 ≤ φ (k + 1) := by exact_mod_cast hφ (Nat.lt_succ_self k)
    have e0 : (fun i => (z i : ℝ)) = 0 := by ext i; simp [hz]
    rw [e0, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at h2
    nlinarith [norm_nonneg x]
  · rw [hshift] at h1
    exact absurd (hM z hz) (not_le.2 h1)

theorem exists_radius {R C : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [NormedField C]
    [IsUltrametricDist C] (f : R →+* C) (hle : ∀ a, ‖f a‖ ≤ 1) (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, ‖f a‖ < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, ‖f a‖ ≤ ρ := by
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)
  have hb : ∀ s : Finset R, (∀ a ∈ s, ‖f a‖ < 1) → ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ a ∈ s, ‖f a‖ ≤ ρ := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨1 / 2, by norm_num, by norm_num, by simp⟩
    | insert a s _ ih =>
      intro h
      obtain ⟨ρ, h0, h1, h2⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
      refine ⟨max ρ ‖f a‖, lt_max_of_lt_left h0, max_lt h1 (h a (Finset.mem_insert_self _ _)), fun b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact le_max_right _ _
      · exact (h2 b hb).trans (le_max_left _ _)
  obtain ⟨ρ, h0, h1, h2⟩ := hb s fun a ha => hm a (hs ▸ Submodule.subset_span ha)
  refine ⟨ρ, h0, h1, fun a ha => ?_⟩
  rw [← hs] at ha
  induction ha using Submodule.span_induction with
  | mem a ha => exact h2 a ha
  | zero => simpa using h0.le
  | add a b _ _ ha hb => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  | smul r a _ ha =>
    rw [smul_eq_mul, map_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hle r)).trans ha

open IsLocalRing Matrix GlobalTheory.ToricRank in

theorem right_inverse_local {R : Type} [CommRing R] [IsLocalRing R] (e : ℕ) {m n : Type}
    [Fintype m] [DecidableEq m] [Fintype n] (C : Matrix m n R)
    (hC : ∀ u, u ᵥ* C.map (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) = 0 → u = 0) :
    ∃ D : Matrix n m R, C * D = 1 := by
  obtain ⟨s, hs, hs'⟩ : ∃ s : R, s ∉ maximalIdeal R ^ (e + 1) ∧
      ∀ a ∈ maximalIdeal R, s * a ∈ maximalIdeal R ^ (e + 1) := by
    by_contra h
    push Not at h
    have key : ∀ k : ℕ, ∃ s ∈ maximalIdeal R ^ k, s ∉ maximalIdeal R ^ (e + 1) := by
      intro k
      induction k with
      | zero => exact ⟨1, by simp, fun h1 =>
          (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (Ideal.pow_le_self (by omega) h1))⟩
      | succ k ih =>
        obtain ⟨s, h1, h2⟩ := ih
        obtain ⟨a, ha, ha'⟩ := h s h2
        exact ⟨s * a, by rw [pow_succ]; exact Ideal.mul_mem_mul h1 ha, ha'⟩
    obtain ⟨s, h1, h2⟩ := key (e + 1)
    exact h2 h1
  obtain ⟨c, P, hc, hP⟩ := exists_mul_eq_smul_one (ResidueField R) (C.map (residue R)) fun u hu => by
    choose w hw using fun i => residue_surjective (u i)
    have h₁ : ∀ j, (w ᵥ* C) j ∈ maximalIdeal R := fun j => by
      rw [← residue_eq_zero_iff, RingHom.map_vecMul]
      exact (congrArg (fun z => (z ᵥ* C.map (residue R)) j) (funext hw)).trans (congrFun hu j)
    have h₂ := hC (fun i => Ideal.Quotient.mk _ ((s • w) i)) (funext fun j => by
      refine ((Ideal.Quotient.mk _).map_vecMul C (s • w) j).symm.trans ?_
      rw [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, Matrix.smul_vecMul]
      exact hs' _ (h₁ j))
    funext i
    have h₃ : s * w i ∈ maximalIdeal R ^ (e + 1) := Ideal.Quotient.eq_zero_iff_mem.1 (congrFun h₂ i)
    rw [← hw, Pi.zero_apply, residue_eq_zero_iff]
    exact fun hu => hs ((Ideal.mul_unit_mem_iff_mem _ hu).1 h₃)
  choose Q hQ using fun i j => residue_surjective (P i j)
  have hu : IsUnit (C * Matrix.of Q).det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul,
      show (Matrix.of Q).map (residue R) = P from Matrix.ext hQ, hP, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  exact ⟨Matrix.of Q * (C * Matrix.of Q)⁻¹, by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]⟩

section Geometry

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.LieEigen Matrix
open Formalism.MainNotions.DIV.Cons GlobalTheory.ToricRank GlobalTheory.PeriodLaws
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)
open scoped CategoryTheory.Obj

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out in

theorem matrix_level_local {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oD : D.OAct O}
    {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct)
    {g r : ℕ} {v : Fin g → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {ρ : O →+* Module.End R (Fin g → R)} (hρ : ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ aG.act a)
    (b : Module.Basis (Fin r) ℤ D.toPre.X) (e : ℕ) :
    ∃ (C : Matrix (Fin r) (Fin g) R) (D' : Matrix (Fin g) (Fin r) R), C * D' = 1 ∧ ∀ a k j,
      (C * (LinearMap.toMatrix' (ρ a))ᵀ - (Matrix.of fun k j => (b.repr (star a • b j) k : R)) * C) k j ∈
        maximalIdeal R ^ (e + 1) := by
  have := U.smooth
  let f := Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))
  obtain ⟨v', ρ', hv', hρ', hM⟩ := exists_action_pullback hv hρ f
  let gc := U.gt e
  have := gc.i_hom
  obtain ⟨C₀, hC₀⟩ := exists_matrix_torus hv' b gc.i
  choose C hC using fun i j => Ideal.Quotient.mk_surjective (C₀ i j)
  have hC' : (Matrix.of C).map f = C₀ := Matrix.ext hC
  obtain ⟨D', hD'⟩ := right_inverse_local e (Matrix.of C) fun u hu => by
    let c := (Diag.dualBasis _ b).equivFun.symm u
    have hc : (fun k => c (b k)) = u := (Diag.dualBasis _ b).equivFun.apply_symm_apply u
    have h₁ : Diag.lieVec c ≫ gc.i = Diag.lieVec 0 ≫ gc.i := by
      rw [hC₀, hC₀, hc, ← hC', hu]
      exact congrArg (prodPts · v') (Matrix.zero_vecMul _).symm
    have h₂ := Diag.lieVec_injective (gc.isKernel.hom_ext h₁ (toUnit_unique _ _))
    rw [← hc, h₂]
    rfl
  refine ⟨Matrix.of C, D', hD', fun a k j => ?_⟩
  obtain ⟨t, ht, hi⟩ := hl.i_lin e a
  obtain rfl := ConstBasis.eq_diagMap (DistribSMul.toAddMonoidHom D.toPre.X (star a)) ht
  have h₁ := congrArg (Diag.lieVec (Diag.dualBasis _ b k) ≫ ·) hi
  rw [← Category.assoc, ← Category.assoc, Diag.lieVec_comp_diagMap, hC₀, hC₀] at h₁
  have h₂ := congrFun (prodPts_injective hv' ((hρ' a _).trans h₁)) j
  rw [hM, vecMul_vecMul] at h₂
  have e₁ : (fun k' => Diag.dualBasis (R ⧸ maximalIdeal R ^ (e + 1)) b k (b k')) = Pi.single k 1 := by
    ext k'
    simp [Diag.dualBasis_apply, Finsupp.single_apply, Pi.single_apply]
  rw [e₁, Matrix.single_one_vecMul] at h₂
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change (Matrix.map _ f) k j = (Matrix.map _ f) k j
  rw [Matrix.map_mul, Matrix.map_mul, hC']
  refine h₂.trans ?_
  simp [Matrix.mul_apply, vecMul, dotProduct, Diag.dualBasis_apply]

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out in

theorem finrank_le_local {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [IsDomain O] [StarRing O] [Module.Finite ℤ O]
    [Module O D.toPre.X] {oD : D.OAct O} {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct)
    {F : Type} [NontriviallyNormedField F] [IsAlgClosed F] [IsUltrametricDist F] (f : R →+* intO F)
    (hf : ∀ a ∈ maximalIdeal R, ‖((f a : intO F) : F)‖ < 1) {τ : O →+* F}
    (hτ : Function.Injective τ) {N : ℕ} (hN : LieMult aG (spMap ((intO F).subtype.comp f)) τ N) :
    Module.finrank O D.toPre.X ≤ N := by
  classical
  have := U.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis G U.smooth
  obtain ⟨ρ, hρ⟩ := exists_action hv aG
  obtain ⟨v', ρ', hv', hρ', hM⟩ := exists_action_pullback hv hρ ((intO F).subtype.comp f)
  have hk := isLinearPullback_pullback aG (spMap ((intO F).subtype.comp f))
  rw [← finrank_of_lieMult hk.1 hv' hk.2 hρ' hN]
  let V := intO F
  have : IsFractionRing V F := isFractionRing_intO
  obtain ⟨κ, h0, h1, h2⟩ := exists_radius ((intO F).subtype.comp f) (fun a => (f a).2) hf
  obtain ⟨π, hπ0, hπ1⟩ : ∃ π : V, κ ≤ ‖(π : F)‖ ∧ ‖(π : F)‖ < 1 := by
    obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one F
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hy0 h1
    have hn0 : n ≠ 0 := fun e => by rw [e, pow_zero] at hn; exact hn.not_gt hy1
    obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.pos_of_ne_zero hn0)
    rw [norm_pow] at hn hy1
    have hx1 : ‖x‖ < 1 := (pow_lt_one_iff_of_nonneg (norm_nonneg _) hn0).1 hy1
    exact ⟨⟨x, hx1.le⟩, (lt_of_pow_lt_pow_left₀ n (norm_nonneg _) hn).le, hx1⟩
  have hpow : ∀ n, ∀ a ∈ maximalIdeal R ^ n, π ^ n ∣ f a := by
    have hπ : π ≠ 0 := fun e => by
      rw [e] at hπ0
      exact absurd hπ0 (by simpa using h0)
    have hle : (maximalIdeal R).map f ≤ Ideal.span {π} := Ideal.map_le_iff_le_comap.2 fun a ha =>
      Ideal.mem_span_singleton.2 (dvd_of_norm_le hπ ((h2 a ha).trans hπ0))
    intro n a ha
    have := Ideal.pow_right_mono hle n (Ideal.map_pow f _ n ▸ Ideal.mem_map_of_mem f ha)
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  let τV : O →+* V := τ.codRestrict V fun a =>
    norm_le_one_of_integral (map_isIntegral_int τ (Algebra.IsIntegral.isIntegral a))
  let b := Module.finBasis ℤ D.toPre.X
  have : Module.Finite O D.toPre.X := .of_restrictScalars_finite ℤ _ _
  obtain ⟨φ⟩ := ConstBasis.nonempty_basis_eigenHom (X := D.toPre.X) (τ.comp (starRingEnd O))
    (hτ.comp star_injective)
  refine le_finrank_eigenSub (R := V) (V := V) π (fun h => ?_) (fun c hc => ?_) τV
    (fun a => (LinearMap.toMatrix' (ρ a))ᵀ.map f) ρ' hM star b (fun k => (φ k).1)
    (φ.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _))
    (fun k a x => ((φ k).2 _ x).trans (congrArg (τ · * _) (star_star a))) fun n => ?_
  · obtain ⟨w, hw⟩ := h.exists_right_inv
    have h₁ : ‖(π : F)‖ * ‖(w : F)‖ = 1 := by
      rw [← norm_mul]
      exact (congrArg (fun z : V => ‖(z : F)‖) hw).trans norm_one
    have h₂ : ‖(w : F)‖ ≤ 1 := w.2
    exact ((mul_le_of_le_one_right (norm_nonneg _) h₂).trans_lt hπ1).ne' h₁.symm
  · have hc' : 0 < ‖(c : F)‖ := norm_pos_iff.2 fun e => hc (Subtype.ext e)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hc' hπ1
    exact ⟨n, dvd_of_norm_le hc ((norm_pow _ n).trans_le hn.le)⟩
  · obtain ⟨C, D', hCD, hC⟩ := matrix_level_local U hl hv hρ b n
    refine ⟨C.map f, D'.map f, by rw [← Matrix.map_mul, hCD]; simp, fun a k j => ?_⟩
    have := hpow _ _ (hC a k j)
    simpa [Matrix.mul_apply, map_sum] using this

end Geometry

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem coord_ne_zero {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) (χ : A.Ylat) (r : A.R)
    (hr : PsiCoord A.U.D.toPre χ r) : ((intO ↥C.S).subtype.comp A.f) r ≠ 0 := by
  have hop : IsOpen (A.ι ⁻¹' abLocus Y.t.G) := by
    have : A.ι ⁻¹' abLocus Y.t.G = abLocus A.t.G :=
      Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 x
    rw [this]
    exact AbLocusOpen.isOpen_abLocus_local _ A.t.semi
  let z : Sp ↥C.S := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ↥C.S)
  have e : spMap ((intO ↥C.S).subtype.comp A.f) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _ := by
    refine Eq.trans ?_ P.ext
    rw [← A.fac, ← Category.assoc]
    exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO ↥C.S).subtype))
  have hz : spMap ((intO ↥C.S).subtype.comp A.f) z ∈ A.ι ⁻¹' abLocus Y.t.G := by
    have h1 : Y.jQ (P.y z) ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := Y.ab_gen ▸ Set.mem_range_self _
    have h2 := congrArg (fun g : Sp ↥C.S ⟶ Y.X => g z) e
    simp only [Scheme.Hom.comp_apply] at h2
    rw [Set.mem_preimage, h2]
    exact h1
  exact fun h0 => PsiCoordLocal.not_mem_of_coord hop hz (A.unitOn χ) hr h0

theorem betaAdd (Y : Model Xo c β) (p : ℕ) : Formalism.L2.Pj.BetaAdd Y p := fun _ _ A =>
  (GlobalTheory.BetaAdd.main A.R A.U.D _ _ p A.normal (fun a => (A.f a).2) (coord_ne_zero A)).1

theorem betaBal (Y : Model Xo c β) (p : ℕ) : BetaBal Y p (IsCMField.complexConj E) := fun _ _ A x x' hx a b => by
  have : x' = H.bar x := Subtype.ext (hx.trans (H.bar_eq x).symm)
  rw [this]
  exact PeriodBalance.betaAt_balanced E H A.R A.t A.U _ _ p A.normal (fun a => (A.f a).2) (coord_ne_zero A) x a b

theorem exists_lower {Y : Model Xo c β} {p : ℕ} (hp : 1 < p) {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ a : A.Ylat, a ≠ 0 → κ ≤ A.beta a a := by
  have := A.noeth
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨ρ, h0, h1, h2⟩ := exists_radius ((intO ↥C.S).subtype.comp A.f) (fun a => (A.f a).2) A.f_loc
  have hco := PsiCoordLocal.main A.R A.U.D A.normal
  have hneg := Real.logb_neg hp' h0 h1
  refine ⟨2 * -Real.logb p ρ, by linarith, fun a ha => ?_⟩
  rw [DatAt.beta, (GlobalTheory.BetaAdd.main A.R A.U.D _ _ p A.normal (fun a => (A.f a).2) (coord_ne_zero A)).2]
  obtain ⟨r₀, hr₀, -, hmem, -⟩ := (hco a).1
  have h : ∃ r, PsiCoord A.U.D.toPre a r := ⟨r₀, hr₀⟩
  obtain ⟨u, hu⟩ := (hco a).2.1 r₀ _ hr₀ h.choose_spec
  have hrm : h.choose ∈ maximalIdeal A.R := hu ▸ Ideal.mul_mem_left _ _ (hmem ha)
  have := Real.logb_le_logb_of_le hp' (norm_pos_iff.2 (coord_ne_zero A a _ h.choose_spec)) (h2 _ hrm)
  simp only [vPsiAt, dif_pos h]
  linarith

theorem betaPosDef (Y : Model Xo c β) {p : ℕ} (hp : 1 < p) : BetaPosDef Y p := fun C P A => by
  obtain ⟨κ, hκ, hlow⟩ := exists_lower hp A
  let b := Module.Free.chooseBasis ℤ A.Ylat
  refine ⟨_, inferInstance, b, real_pos_of_int_ge _ (fun i k => A.beta_symm _ _) hκ fun z hz => ?_⟩
  have hne : ∑ i, z i • b i ≠ 0 := fun h => hz (funext (Fintype.linearIndependent_iff.1 b.linearIndependent z h))
  refine (hlow _ hne).trans_eq ?_
  rw [← A.beLin_apply (betaAdd Y p)]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, DatAt.beLin_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem rank_le {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P) :
    ∃ ρ : ℕ, Module.finrank ℤ A.Ylat = 2 * (Module.finrank ℚ E / 2) * ρ ∧ ρ ≤ Dw.p ∧ ρ ≤ Dw.q := by
  let := H.starRing
  have := A.noeth
  let F : Type := ↥C.S
  obtain ⟨b, hb⟩ := Spec.map_surjective (P.y ≫ pullback.fst _ _ ≫ Xo.s)
  have hdet := (Y.oF.geom F P.y b.hom hb.symm).1
  have key : ∀ (τ : 𝓞 E →+* F) (n : ℕ), Function.Injective τ → LieMult Y.oF.t.act P.y τ n →
      Module.finrank (𝓞 E) A.U.D.toPre.X ≤ n := fun τ n hτ hn => by
    refine finrank_le_local A.U.U.toUnifPre A.U.lin A.f A.f_loc hτ ?_
    rw [LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ Y.m.cart Y.m.act] at hn
    rw [LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ A.m.cart A.m.act]
    have e : spMap ((intO F).subtype.comp A.f) ≫ A.ι = P.y ≫ Y.jQ ≫ pullback.fst _ _ := by
      refine Eq.trans ?_ P.ext
      rw [← A.fac, ← Category.assoc]
      exact congrArg (· ≫ A.ι) (Spec.map_comp (CommRingCat.ofHom A.f) (CommRingCat.ofHom (intO F).subtype))
    rw [e]
    exact hn
  let τ₀ : 𝓞 E →+* F := (IsAlgClosed.lift (R := ℚ) (S := E) (M := F)).toRingHom.comp (algebraMap _ E)
  have h₀ : Function.Injective τ₀ :=
    (IsAlgClosed.lift (R := ℚ) (S := E) (M := F)).injective.comp RingOfIntegers.coe_injective
  have h₁ : Function.Injective (τ₀.comp H.bar.toRingHom) := h₀.comp H.bar.injective
  have e₁ : τ₀.comp H.bar.toRingHom H.rt = -τ₀ H.rt := by
    rw [← map_neg, ← HostModel.bar_rt]; rfl
  have hsq : τ₀ H.rt ^ 2 = b.hom (baseKA l).ρ ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, (baseKA l).ρ_sq]; simp
  have hne : -τ₀ H.rt ≠ τ₀ H.rt := fun h => by
    have h2 : τ₀ H.rt ^ 2 = 0 := by rw [neg_eq_self.1 h]; simp
    rw [← map_pow, H.rt_sq] at h2
    exact H.d_prime.ne_zero (by simpa using h2)
  refine ⟨Module.finrank (𝓞 E) A.U.D.toPre.X, ?_, ?_⟩
  · have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    rw [ToricRank.finrank_int_eq E]
    congr 1
    omega
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact ⟨key _ _ h₀ ((hdet _).1 h), key _ _ h₁ ((hdet _).2 (by rw [e₁, ← h]; exact hne))⟩
    · have h' : -τ₀ H.rt = b.hom (baseKA l).ρ := by rw [h, neg_neg]
      exact ⟨key _ _ h₁ ((hdet _).1 (e₁.trans h')), key _ _ h₀ ((hdet _).2 (by rw [← h']; exact hne.symm))⟩

theorem ylRank (Y : Model Xo c β) (p : ℕ) : YlRank Y p (Dw.p + Dw.q) Dw.p ∧ YlRank Y p (Dw.p + Dw.q) Dw.q :=
  ⟨fun _ _ A => (rank_le A).imp fun _ h => ⟨h.1, fun _ _ => by omega⟩,
    fun _ _ A => (rank_le A).imp fun _ h => ⟨h.1, fun _ _ => by omega⟩⟩

theorem main (Y : Model Xo c β) {p : ℕ} (hp : 1 < p) :
    Formalism.L2.Pj.BetaAdd Y p ∧ BetaBal Y p (IsCMField.complexConj E) ∧ BetaPosDef Y p ∧
      YlRank Y p (Dw.p + Dw.q) Dw.p :=
  ⟨betaAdd Y p, betaBal Y p, betaPosDef Y hp, (ylRank Y p).1⟩

end GlobalTheory.PointLawsEdge
