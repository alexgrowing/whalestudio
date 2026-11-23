import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

noncomputable section

namespace GlobalTheory.ToricRank

section Algebra

open Matrix

theorem exists_mul_mul_eq_smul {V : Type} (F : Type) [CommRing V] [IsDomain V] [Field F] [Algebra V F]
    [IsFractionRing V F] {m n : Type} [Fintype m] [Fintype n] (B : Matrix m n V) :
    ∃ (c : V) (P : Matrix n m V), c ≠ 0 ∧ B * P * B = c • B := by
  classical
  let f := Matrix.toLin' (B.map (algebraMap V F))
  obtain ⟨g₁, h₁⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g₂, h₂⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have hf : f ∘ₗ (g₁ ∘ₗ g₂) ∘ₗ f = f := LinearMap.ext fun x => by
    have e₂ : g₂ (f x) = f.rangeRestrict x := LinearMap.congr_fun h₂ (f.rangeRestrict x)
    have e₁ := congrArg Subtype.val (LinearMap.congr_fun h₁ (f.rangeRestrict x))
    simp only [LinearMap.comp_apply, e₂]
    exact e₁
  have hm := congrArg LinearMap.toMatrix' hf
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at hm
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors V)
    (fun p : n × m => LinearMap.toMatrix' (g₁ ∘ₗ g₂) p.1 p.2)
  choose P hP using hc
  have hP' : (Matrix.of fun i j => P (i, j)).map (algebraMap V F) =
      algebraMap V F c • LinearMap.toMatrix' (g₁ ∘ₗ g₂) := by
    ext i j
    simpa [Algebra.smul_def] using hP (i, j)
  refine ⟨c, Matrix.of fun i j => P (i, j), nonZeroDivisors.coe_ne_zero c,
    Matrix.map_injective (IsFractionRing.injective V F) ?_⟩
  dsimp only
  rw [Matrix.map_mul, Matrix.map_mul, hP', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hm]
  ext i j
  simp

theorem exists_mul_eq_smul_one {V : Type} (F : Type) [CommRing V] [IsDomain V] [Field F] [Algebra V F]
    [IsFractionRing V F] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] (B : Matrix m n V)
    (hB : ∀ u, u ᵥ* B = 0 → u = 0) : ∃ (c : V) (P : Matrix n m V), c ≠ 0 ∧ B * P = c • 1 := by
  obtain ⟨c, P, hc, h⟩ := exists_mul_mul_eq_smul F B
  refine ⟨c, P, hc, sub_eq_zero.1 (Matrix.ext fun i => congrFun (hB _ ?_))⟩
  have : (B * P - c • (1 : Matrix m m V)) * B = 0 := by rw [Matrix.sub_mul, h, Matrix.smul_mul, Matrix.one_mul, sub_self]
  exact congrFun this i

theorem exists_solutions {V : Type} (F : Type) [CommRing V] [IsDomain V] [Field F] [Algebra V F]
    [IsFractionRing V F] (π : V) (hπ : ¬ IsUnit π) (hd : ∀ c : V, c ≠ 0 → ∃ n, c ∣ π ^ n)
    {s r g h : Type} [Fintype s] [DecidableEq s] [Fintype r] [DecidableEq r] [Fintype g] [Fintype h]
    (B : Matrix g h V) (Φ : Matrix s r V) (hΦ : ∀ u, u ᵥ* Φ = 0 → u = 0)
    (hC : ∀ n, ∃ (C : Matrix r g V) (D : Matrix g r V) (Z : Matrix s h V),
      C * D = 1 ∧ Φ * C * B = π ^ (n + 1) • Z) :
    ∃ (W : Matrix s g V) (N : Matrix g s V), W * B = 0 ∧ (W * N).det ≠ 0 := by
  obtain ⟨c, P, hc, hP⟩ := exists_mul_mul_eq_smul F B
  obtain ⟨d, Ψ, hd0, hΨ⟩ := exists_mul_eq_smul_one F Φ hΦ
  obtain ⟨n, y, hy⟩ := hd (c * d) (mul_ne_zero hc hd0)
  obtain ⟨C, D, Z, hCD, hZ⟩ := hC n
  refine ⟨c • (Φ * C) - Φ * C * B * P, D * Ψ, ?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.mul_assoc (Φ * C) B P, Matrix.mul_assoc (Φ * C) (B * P) B, hP, Matrix.smul_mul,
      Matrix.mul_smul, sub_self]
  · have e : (c • (Φ * C) - Φ * C * B * P) * (D * Ψ) = (c * d) • (1 - π • (y • (Z * P * (D * Ψ)))) := by
      rw [Matrix.sub_mul, hZ, Matrix.smul_mul, Matrix.mul_assoc Φ, ← Matrix.mul_assoc C, hCD, Matrix.one_mul, hΨ,
        Matrix.smul_mul, Matrix.smul_mul, smul_sub, smul_smul, smul_smul, smul_smul, pow_succ, hy]
      congr 2
      ring
    rw [e, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero hc hd0)) fun h0 => hπ ?_
    have h1 := (Ideal.Quotient.mk (Ideal.span {π})).map_det (1 - π • (y • (Z * P * (D * Ψ))))
    have h2 : (Ideal.Quotient.mk (Ideal.span {π})).mapMatrix (1 - π • (y • (Z * P * (D * Ψ)))) = 1 := by
      rw [map_sub, map_one, sub_eq_self]
      ext i j
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π))
    rw [h0, h2, map_zero, Matrix.det_one, eq_comm, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at h1
    exact isUnit_of_dvd_one h1

open IsLocalRing in

theorem exists_mul_eq_one {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (e : ℕ) {m n : Type}
    [Fintype m] [DecidableEq m] [Fintype n] (C : Matrix m n R)
    (hC : ∀ u, u ᵥ* C.map (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) = 0 → u = 0) :
    ∃ D : Matrix n m R, C * D = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm := hπ.maximalIdeal_eq
  obtain ⟨c, P, hc, hP⟩ := exists_mul_eq_smul_one (ResidueField R) (C.map (residue R)) fun u hu => by
    choose w hw using fun i => residue_surjective (u i)
    have h₁ : ∀ j, π ∣ (w ᵥ* C) j := fun j => by
      rw [← Ideal.mem_span_singleton, ← hm, ← residue_eq_zero_iff, RingHom.map_vecMul]
      exact (congrArg (fun z => (z ᵥ* C.map (residue R)) j) (funext hw)).trans (congrFun hu j)
    have h₂ := hC (fun i => Ideal.Quotient.mk _ ((π ^ e • w) i)) (funext fun j => by
      refine ((Ideal.Quotient.mk _).map_vecMul C (π ^ e • w) j).symm.trans ?_
      rw [Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
        Matrix.smul_vecMul, pow_succ]
      exact mul_dvd_mul_left _ (h₁ j))
    funext i
    have h₃ := Ideal.Quotient.eq_zero_iff_mem.1 (congrFun h₂ i)
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ] at h₃
    rw [← hw, Pi.zero_apply, residue_eq_zero_iff, hm, Ideal.mem_span_singleton]
    exact (mul_dvd_mul_iff_left (pow_ne_zero e hπ.ne_zero)).1 h₃
  choose Q hQ using fun i j => residue_surjective (P i j)
  have hu : IsUnit (C * Matrix.of Q).det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul,
      show (Matrix.of Q).map (residue R) = P from Matrix.ext hQ, hP, Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hc
  exact ⟨Matrix.of Q * (C * Matrix.of Q)⁻¹, by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]⟩

open NumberField TensorProduct in

theorem finrank_int_eq (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] :
    Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  rw [← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq,
    Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]

end Algebra

section Eigen

open Matrix GlobalTheory.EigenSplit

theorem le_finrank_eigenSub {R V F O X : Type} [CommRing R] [CommRing V] [IsDomain V] [Field F] [Algebra R V]
    [Algebra V F] [IsFractionRing V F] [CommRing O] [Module.Finite ℤ O] [AddCommGroup X] [Module O X] (π : R)
    (hπ : ¬ IsUnit (algebraMap R V π)) (hd : ∀ c : V, c ≠ 0 → ∃ n, c ∣ algebraMap R V π ^ n) (τ : O →+* V)
    {g r s : ℕ} (M : O → Matrix (Fin g) (Fin g) R) (ρ : O →+* Module.End F (Fin g → F))
    (hM : ∀ a w, ρ a w = w ᵥ* (M a).map ((algebraMap V F).comp (algebraMap R V))) (σ : O → O)
    (b : Module.Basis (Fin r) ℤ X) (φ : Fin s → (X →+ F)) (hφ : LinearIndependent F φ)
    (hφ' : ∀ k a x, φ k (σ a • x) = algebraMap V F (τ a) * φ k x)
    (hC : ∀ n, ∃ (C : Matrix (Fin r) (Fin g) R) (D : Matrix (Fin g) (Fin r) R), C * D = 1 ∧ ∀ a k j,
      π ^ (n + 1) ∣ (C * M a - (Matrix.of fun k j => (b.repr (σ a • b j) k : R)) * C) k j) :
    s ≤ Module.finrank F (eigenSub ρ ((algebraMap V F).comp τ)) := by
  classical
  have hinj := IsFractionRing.injective V F
  obtain ⟨d, hd'⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors V)
    (fun p : _ × _ => (φ p.1 (b p.2) : F))
  choose Φ₀ hΦ₀ using hd'
  let Φ : Matrix (Fin s) (Fin r) V := Matrix.of fun k j => Φ₀ (k, j)
  have hΦ : ∀ k j, algebraMap V F (Φ k j) = algebraMap V F d * φ k (b j) := fun k j =>
    (hΦ₀ (k, j)).trans (Algebra.smul_def _ _)
  clear_value Φ
  have hd0 : algebraMap V F d ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.coe_ne_zero d)
  obtain ⟨m, o, ho⟩ := Module.Finite.exists_fin (R := ℤ) (M := O)
  let B' : O → Matrix (Fin g) (Fin g) V := fun a => (M a).map (algebraMap R V) - τ a • 1
  let B : Matrix (Fin g) (Fin m × Fin g) V := Matrix.of fun i p => B' (o p.1) i p.2
  obtain ⟨W, N', hW, hN'⟩ := exists_solutions F (algebraMap R V π) hπ hd B Φ
    (fun u hu => by
      have h₁ : ∑ k, (algebraMap V F (u k) * algebraMap V F d) • φ k = 0 := by
        refine AddMonoidHom.toIntLinearMap_injective (b.ext fun j => ?_)
        have := congrArg (algebraMap V F) (congrFun hu j)
        simpa [vecMul, dotProduct, hΦ, mul_assoc] using this
      funext k
      have := Fintype.linearIndependent_iff.1 hφ _ h₁ k
      exact hinj ((mul_eq_zero.1 this).resolve_right hd0 |>.trans (map_zero _).symm))
    (fun n => by
      obtain ⟨C, D', hCD, hC⟩ := hC n
      have key : ∀ k p, algebraMap R V π ^ (n + 1) ∣ (Φ * C.map (algebraMap R V) * B) k p := fun k p => by
        have e₁ : Φ * (Matrix.of fun k j => (b.repr (σ (o p.1) • b j) k : R)).map (algebraMap R V) =
            τ (o p.1) • Φ := by
          ext k j
          refine hinj ?_
          have h₁ := hφ' k (o p.1) (b j)
          rw [← b.sum_repr (σ (o p.1) • b j), map_sum] at h₁
          simp only [Matrix.mul_apply, map_sum, map_mul, hΦ, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply,
            Matrix.of_apply, map_intCast, mul_assoc, ← Finset.mul_sum]
          rw [mul_left_comm]
          congr 1
          simpa [mul_comm] using h₁
        have e₂ : (Φ * C.map (algebraMap R V) * B) k p = (Φ * (C * M (o p.1) -
            (Matrix.of fun k j => (b.repr (σ (o p.1) • b j) k : R)) * C).map (algebraMap R V)) k p.2 := by
          change (Φ * C.map (algebraMap R V) * B' (o p.1)) k p.2 = _
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.mul_sub,
            ← Matrix.mul_assoc, ← Matrix.mul_assoc, e₁, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        rw [e₂, Matrix.mul_apply]
        refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _
        rw [← map_pow]
        exact map_dvd _ (hC (o p.1) i p.2)
      choose Z hZ using key
      exact ⟨C.map (algebraMap R V), D'.map (algebraMap R V), Matrix.of Z,
        by rw [← Matrix.map_mul, hCD, Matrix.map_one _ (map_zero _) (map_one _)], Matrix.ext hZ⟩)
  have mem : ∀ k, (W.map (algebraMap V F)) k ∈ eigenSub ρ ((algebraMap V F).comp τ) := fun k =>
    mem_eigenSub.2 fun a => by
    have ha : a ∈ Submodule.span ℤ (Set.range o) := ho ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, rfl⟩ := ha
      have h₁ : W k ᵥ* B' (o l) = 0 := funext fun j => congrFun (congrFun hW k) (l, j)
      rw [vecMul_sub, vecMul_smul, vecMul_one, sub_eq_zero] at h₁
      rw [hM]
      funext j
      have h₂ := congrArg (algebraMap V F) (congrFun h₁ j)
      rw [RingHom.map_vecMul] at h₂
      exact h₂.trans (map_mul _ _ _)
    | zero => simp
    | add a a' _ _ h h' => rw [map_add, map_add, LinearMap.add_apply, h, h', add_smul]
    | smul z a _ h => rw [map_zsmul, map_zsmul, LinearMap.smul_apply, h, smul_assoc]
  have li : LinearIndependent F (W.map (algebraMap V F)).row := by
    rw [← Matrix.vecMul_injective_iff]
    have hu : IsUnit (W.map (algebraMap V F) * N'.map (algebraMap V F)) := by
      rw [← Matrix.map_mul, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det]
      exact (map_ne_zero_iff _ hinj).2 hN'
    intro x y h
    refine Matrix.vecMul_injective_of_isUnit hu ?_
    dsimp only at h ⊢
    rw [← vecMul_vecMul, ← vecMul_vecMul, h]
  let w : Fin s → eigenSub ρ ((algebraMap V F).comp τ) := fun k => ⟨_, mem k⟩
  have li' : LinearIndependent F w := LinearIndependent.of_comp (Submodule.subtype _) li
  exact (Fintype.card_fin s).symm.trans_le li'.fintype_card_le_finrank

end Eigen

section Geometry

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre GlobalTheory.EigenSplit GlobalTheory.LieEigen Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)
open scoped CategoryTheory.Obj

theorem exists_action_pullback {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {act : OAct O G} {g : ℕ} {v : Fin g → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {ρ : O →+* Module.End R (Fin g → R)} (hρ : ∀ a c, prodPts (ρ a c) v = prodPts c v ≫ act.act a)
    {S : Type} [CommRing S] (f : R →+* S) :
    ∃ (v' : Fin g → (epsR S ⟶ (Over.pullback (spMap f)).obj G)) (ρ' : O →+* Module.End S (Fin g → S)),
      IsLieBasis v' ∧ (∀ a c, prodPts (ρ' a c) v' = prodPts c v' ≫ (act.pullback (spMap f) G).act a) ∧
      ∀ a w, ρ' a w = w ᵥ* (LinearMap.toMatrix' (ρ a))ᵀ.map f := by
  have hk := isLinearPullback_pullback act (spMap f)
  obtain ⟨v', hv', e⟩ := GlobalTheory.exists_isLieBasis_baseChange R S f _ _ _ hk.1 ‹_› g v hv
  obtain ⟨ρ', hρ'⟩ := exists_action hv' (act.pullback (spMap f) G)
  refine ⟨v', ρ', hv', hρ', fun x w => ?_⟩
  have : ρ' x = ((LinearMap.toMatrix' (ρ x))ᵀ.map f).vecMulLinear := (Pi.basisFun S (Fin g)).ext fun i => by
    have e₁ : Pi.basisFun S (Fin g) i = f ∘ Pi.single i 1 := by
      ext j; by_cases h : j = i <;> simp [h]
    rw [e₁, ← action_baseChange hk.1 hv' e hk.2 hρ hρ', ← e₁]
    ext j; simp
  rw [this]; rfl

theorem exists_matrix_torus {S X : Type} [CommRing S] [AddCommGroup X] {G : Over (Sp S)} [GrpObj G] [IsCommMonObj G]
    {g r : ℕ} {v : Fin g → (epsR S ⟶ G)} (hv : IsLieBasis v) (b : Module.Basis (Fin r) ℤ X)
    (i : splitTorus (Sp S) X ⟶ G) [IsMonHom i] :
    ∃ C : Matrix (Fin r) (Fin g) S, ∀ c : X →+ S, Diag.lieVec c ≫ i = prodPts ((fun k => c (b k)) ᵥ* C) v := by
  obtain ⟨C, hC, -⟩ := SqZero.existsUnique_lieMatrix i (Diag.isLieBasis_dualBasis (R := S) b).1 hv
  refine ⟨C, fun c => ?_⟩
  have e₀ : Diag.lieVec c = prodPts (fun k => c (b k)) fun k => Diag.lieVec (Diag.dualBasis S b k) :=
    (Chart.isLieComb_iff _ _ _).1 ((Diag.isLieComb_iff _ _ _).2
      (congrArg _ ((Diag.dualBasis S b).sum_repr c).symm))
  have e : Diag.lieVec c ≫ i = prodPts (fun k => c (b k)) fun k => Diag.lieVec (Diag.dualBasis S b k) ≫ i := by
    rw [e₀]
    refine (map_list_prod (IsMonHom.monoidHom i _) _).trans ?_
    rw [prodPts, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun k => Category.assoc _ _ i)
  rw [e, funext fun i => (Chart.isLieComb_iff _ _ _).1 (hC i), vecMul_eq_sum]
  exact prodPts_prodPts hv.1 _ fun i => C i

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out in

theorem exists_matrix_level {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
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
  obtain ⟨D', hD'⟩ := exists_mul_eq_one e (Matrix.of C) fun u hu => by
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

theorem finrank_le_of_lieMult {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {D : DegData R (maximalIdeal R)} {P : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre (maximalIdeal R) D P G) {O : Type} [CommRing O] [IsDomain O] [StarRing O] [Module.Finite ℤ O]
    [Module O D.toPre.X] {oD : D.OAct O} {oP : P.OAct O} {aG : OAct O G} (hl : U.OLinear O oD oP aG.toRingAct)
    {F : Type} [Field F] [Algebra R F] [FaithfulSMul R F] [Algebra.IsAlgebraic R F] {τ : O →+* F}
    (hτ : Function.Injective τ) {N : ℕ} (hN : LieMult aG (spMap (algebraMap R F)) τ N) :
    Module.finrank O D.toPre.X ≤ N := by
  classical
  have := U.smooth
  obtain ⟨g, v, hv⟩ := Chart.exists_isLieBasis G U.smooth
  obtain ⟨ρ, hρ⟩ := exists_action hv aG
  obtain ⟨v', ρ', hv', hρ', hM⟩ := exists_action_pullback hv hρ (algebraMap R F)
  have hk := isLinearPullback_pullback aG (spMap (algebraMap R F))
  rw [← finrank_of_lieMult hk.1 hv' hk.2 hρ' hN]
  let V := integralClosure R F
  have : IsFractionRing V F := integralClosure.isFractionRing_of_algebraic fun x hx =>
    (FaithfulSMul.algebraMap_eq_zero_iff R F).1 hx
  have : FaithfulSMul R V := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    FaithfulSMul.algebraMap_injective R F (congrArg Subtype.val h)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let τV : O →+* V := τ.codRestrict V fun a =>
    (map_isIntegral_int τ (Algebra.IsIntegral.isIntegral a)).tower_top
  let b := Module.finBasis ℤ D.toPre.X
  have : Module.Finite O D.toPre.X := .of_restrictScalars_finite ℤ _ _
  obtain ⟨φ⟩ := ConstBasis.nonempty_basis_eigenHom (X := D.toPre.X) (τ.comp (starRingEnd O))
    (hτ.comp star_injective)
  refine le_finrank_eigenSub (V := V) π (fun h => hπ.not_isUnit ((isUnit_map_iff _ _).1 h)) (fun c hc => ?_) τV
    (fun a => (LinearMap.toMatrix' (ρ a))ᵀ) ρ' hM star b (fun k => (φ k).1)
    (φ.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _))
    (fun k a x => ((φ k).2 _ x).trans (congrArg (τ · * _) (star_star a))) fun n => ?_
  · obtain ⟨x, hx, hc'⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) c).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hc)
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hπ
    exact ⟨n, hc'.trans (by rw [← map_pow]; exact map_dvd _ hn.dvd)⟩
  · obtain ⟨C, D', hCD, hC⟩ := exists_matrix_level U hl hv hρ b n
    refine ⟨C, D', hCD, fun a k j => Ideal.mem_span_singleton.1 ?_⟩
    rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
    exact hC a k j

end Geometry

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem rank_le_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] [IsDiscreteValuationRing R] (t : SAB H (Sp R)) (U : PELUnif (maximalIdeal R) t) (tK : SAB H (Sp (FractionRing R))) (_ : SABMap tK t (jK R)) (x : Sp (FractionRing R) ⟶ Xo.X) (_ : SABMap tK Xo.univ.t x), IsAdicComplete (maximalIdeal R) R → ∃ ρ : ℕ, Module.finrank ℤ U.D.toPre.X = 2 * (Module.finrank ℚ E / 2) * ρ ∧ ρ ≤ Dw.p ∧ ρ ≤ Dw.q := by
  intro E _ _ _ H Dw l Xo R _ _ _ _ _ t U tK m x m' _
  let := H.starRing
  let F := AlgebraicClosure (FractionRing R)
  have : FaithfulSMul R F := .trans R (FractionRing R) F
  have : Algebra.IsAlgebraic R F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing R)).2 inferInstance
  have : CharZero F := algebraRat.charZero F
  let y : Sp F ⟶ Sp (FractionRing R) := spMap (algebraMap (FractionRing R) F)
  obtain ⟨β, hβ⟩ := Spec.map_surjective ((y ≫ x) ≫ Xo.s)
  have hdet := (Xo.univ.geom F (y ≫ x) β.hom hβ.symm).1
  have key : ∀ (τ : 𝓞 E →+* F) (n : ℕ), Function.Injective τ → LieMult Xo.univ.t.act (y ≫ x) τ n →
      Module.finrank (𝓞 E) U.D.toPre.X ≤ n := fun τ n hτ hn => by
    refine finrank_le_of_lieMult U.U.toUnifPre U.lin hτ ?_
    rw [← LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ m'.cart m'.act,
      LiePull.lieMult_pull _ _ _ _ _ _ _ _ _ m.cart m.act] at hn
    convert hn using 1
    exact (congrArg Spec.map (by rw [IsScalarTower.algebraMap_eq R (FractionRing R) F]; rfl)).trans (Spec.map_comp _ _)
  let τ₀ : 𝓞 E →+* F := (IsAlgClosed.lift (R := ℚ) (S := E) (M := F)).toRingHom.comp (algebraMap _ E)
  have h₀ : Function.Injective τ₀ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := F)).injective.comp RingOfIntegers.coe_injective
  have h₁ : Function.Injective (τ₀.comp H.bar.toRingHom) := h₀.comp H.bar.injective
  have e₁ : τ₀.comp H.bar.toRingHom H.rt = -τ₀ H.rt := by
    rw [← map_neg, ← HostModel.bar_rt]; rfl
  have hsq : τ₀ H.rt ^ 2 = β.hom (baseKA l).ρ ^ 2 := by
    rw [← map_pow, ← map_pow, H.rt_sq, (baseKA l).ρ_sq]; simp
  have hne : -τ₀ H.rt ≠ τ₀ H.rt := fun h => by
    have h2 : τ₀ H.rt ^ 2 = 0 := by rw [neg_eq_self.1 h]; simp
    rw [← map_pow, H.rt_sq] at h2
    exact H.d_prime.ne_zero (by simpa using h2)
  refine ⟨Module.finrank (𝓞 E) U.D.toPre.X, ?_, ?_⟩
  · have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    rw [finrank_int_eq E]
    congr 1
    omega
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact ⟨key _ _ h₀ ((hdet _).1 h), key _ _ h₁ ((hdet _).2 (by rw [e₁, ← h]; exact hne))⟩
    · have h' : -τ₀ H.rt = β.hom (baseKA l).ρ := by rw [h, neg_neg]
      exact ⟨key _ _ h₁ ((hdet _).1 (e₁.trans h')), key _ _ h₀ ((hdet _).2 (by rw [← h']; exact hne.symm))⟩

end GlobalTheory.ToricRank
