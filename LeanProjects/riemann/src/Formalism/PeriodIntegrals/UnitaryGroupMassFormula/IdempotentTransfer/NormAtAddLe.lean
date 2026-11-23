import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.HarderNarasimhan.FinalCor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFormulaOfRankDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.CharacteristicPolynomialCompatibility

noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module NumberField

section Sandwich

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

lemma sandwich (Y : Module.End K W) (hY : Y ≠ 0) :
    ∃ (n : ℕ) (A B : Fin n → Module.End K W), ∑ i, A i * Y * B i = 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, Y v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hY (LinearMap.ext h)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K W, ψ (Y v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff K (Y v)).mp h)
  set φ : Module.Dual K W := (ψ (Y v))⁻¹ • ψ with hφdef
  have hφ : φ (Y v) = 1 := by
    rw [hφdef, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψ]
  let b := Module.finBasis K W
  refine ⟨Module.finrank K W, fun i => φ.smulRight (b i), fun i => (b.coord i).smulRight v, ?_⟩
  apply b.ext
  intro j
  rw [LinearMap.sum_apply]
  simp only [Module.End.mul_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, map_smul, Module.End.one_apply]
  rw [Finset.sum_eq_single j]
  · simp [hφ]
  · intro i _ hij
    simp [Finsupp.single_apply, Ne.symm hij]
  · simp

end Sandwich

section GroupAlg

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

open Classical in
lemma epsSum_eq (P : Pair K G) : epsSum P = ((Fintype.card P.H : ℕ) : K) • eps P := by
  have hc : ((Fintype.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eps_eq, smul_smul, mul_inv_cancel₀ hc, one_smul]

open Classical in
lemma eps_mul_epsSum (P : Pair K G) : eps P * epsSum P = epsSum P := by
  have hc : ((Fintype.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eps_eq, smul_mul_assoc, epsSum_sq, smul_smul, inv_mul_cancel₀ hc, one_smul]

lemma eS_in_ideal (T : GoodSet K G) (s : T.S) (P0 : Pair K G)
    (hY : (T.tau s).asAlgebraHom (eps P0) ≠ 0) :
    ∃ (n : ℕ) (a b : Fin n → MonoidAlgebra K G), ∑ i, a i * (eps P0 * (b i * eS T s)) = eS T s := by
  obtain ⟨n, A, B, h⟩ := sandwich _ hY
  choose a ha using fun i => T.irr s (A i)
  choose b hb using fun i => T.irr s (B i)
  refine ⟨n, a, b, ?_⟩
  have key : (∑ i, a i * eps P0 * b i) * eS T s = eS T s := by
    rw [mul_eS, map_sum]
    simp only [map_mul, ha, hb]
    rw [h, phiS_one]
  conv_rhs => rw [← key]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc]

lemma vanish {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) (P0 : Pair K G) (x : V)
    (h : ∀ g, ρ.asAlgebraHom (eps P0) (ρ g x) = 0) (c : MonoidAlgebra K G) :
    ρ.asAlgebraHom (eps P0 * c) x = 0 := by
  induction c using MonoidAlgebra.induction_on with
  | of g => rw [map_mul, Module.End.mul_apply, Representation.asAlgebraHom_of, h g]
  | add a b ha hb => rw [mul_add, map_add, LinearMap.add_apply, ha, hb, add_zero]
  | smul r a ha => rw [mul_smul_comm, map_smul, LinearMap.smul_apply, ha, smul_zero]

lemma exists_g (T : GoodSet K G) (P0 P : Pair K G) (hM : M1 T P0) {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (x : V) (hx : x ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T)))
    (hx0 : x ≠ 0) : ∃ g, ρ.asAlgebraHom (eps P0) (ρ g x) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hx0
  have hes : ∀ s, ρ.asAlgebraHom (eS T s) x = 0 := by
    intro s
    have hY : (T.tau s).asAlgebraHom (eps P0) ≠ 0 := by
      intro h0
      have := hM s
      rw [nS, h0, LinearMap.range_zero, finrank_bot] at this
      exact zero_ne_one this
    obtain ⟨n, a, b, hab⟩ := eS_in_ideal T s P0 hY
    rw [← hab, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, Module.End.mul_apply, vanish ρ P0 x hcon, map_zero]
  obtain ⟨z, rfl⟩ := hx
  have he : ρ.asAlgebraHom (eG T) (ρ.asAlgebraHom (eps P * eG T) z) = ρ.asAlgebraHom (eps P * eG T) z := by
    rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← eG_comm, mul_assoc, eG_idem]
  rw [← he, eG, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun s _ => hes s

open Classical in
lemma phi_apply {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) (P0 : Pair K G) (g : G)
    (y : V) :
    ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G g) y =
      ∑ h : P0.H, (((P0.chi h)⁻¹ : Kˣ) : K) • ρ (h : G) (ρ g y) := by
  rw [map_mul, Representation.asAlgebraHom_of, Module.End.mul_apply, epsSum, map_sum, LinearMap.sum_apply]
  simp only [map_smul, Representation.asAlgebraHom_of, LinearMap.smul_apply]

open Classical in
lemma chi_pow (P : Pair K G) (h : P.H) : ((((P.chi h)⁻¹ : Kˣ) : K)) ^ Fintype.card P.H = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← map_inv, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

end GroupAlg

section Norms

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

lemma fcoord_smul' (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  unfold Formalism.HermitianLatticesTheory.fcoord
  have h : Formalism.HermitianLatticesTheory.vecAt b v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, map_smul, smul_eq_mul, map_mul]
  rw [h, Matrix.mulVec_smul]

lemma normAt_smul' (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (c • x) = ‖v.embedding c‖ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  unfold Formalism.HermitianLatticesTheory.normAt
  rw [fcoord_smul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma normAt_add_le' (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + y) ≤ Formalism.HermitianLatticesTheory.normAt b X v x + Formalism.HermitianLatticesTheory.normAt b X v y := by
  have hc : ∀ u : ι → ℂ, Formalism.HermitianLatticesTheory.cnorm u = ‖(WithLp.equiv 2 (ι → ℂ)).symm u‖ := by
    intro u
    rw [EuclideanSpace.norm_eq]
    rfl
  have h : Formalism.HermitianLatticesTheory.fcoord b X v (x + y) = Formalism.HermitianLatticesTheory.fcoord b X v x + Formalism.HermitianLatticesTheory.fcoord b X v y := by
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  unfold Formalism.HermitianLatticesTheory.normAt
  rw [h, hc, hc, hc]
  exact norm_add_le ((WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v x))
    ((WithLp.equiv 2 (ι → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X v y))

lemma normAt_zero' (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) :
    Formalism.HermitianLatticesTheory.normAt b X v 0 = 0 := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.fcoord
  have h : Formalism.HermitianLatticesTheory.vecAt b v (0 : V) = 0 := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [h, Matrix.mulVec_zero]
  simp

lemma normAt_sum_le' {α : Type} (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (s : Finset α) (f : α → V) :
    Formalism.HermitianLatticesTheory.normAt b X v (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Formalism.HermitianLatticesTheory.normAt b X v (f i) := by
  exact Finset.le_sum_of_subadditive (Formalism.HermitianLatticesTheory.normAt b X v) (normAt_zero' b X v).le (normAt_add_le' b X v) s f

lemma realize_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (f : V → V) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ v x, Formalism.HermitianLatticesTheory.normAt b X v (f x) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v x) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X (f x)‖ ≤ C * ‖Formalism.HermitianLatticesTheory.realize b X x‖ := by
  have hsq : ‖Formalism.HermitianLatticesTheory.realize b X (f x)‖ ^ 2 ≤ (C * ‖Formalism.HermitianLatticesTheory.realize b X x‖) ^ 2 := by
    rw [mul_pow, Formalism.HN.PlaceOperatorNorms.norm_sq_realize, Formalism.HN.PlaceOperatorNorms.norm_sq_realize,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (h v x) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end Norms

theorem muPart : MuPart := by
  intro K _ _ _ _ G _ _ T P0 P hM A ρ hA hR
  classical
  have : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  set ρR := Formalism.HermitianLatticesTheory.realize A.b A.X with hρR
  set L1 := cut A ρ (eps P * eG T) A.L with hL1def
  set L0 := cut A ρ (eps P0 * eG T) A.L with hL0def
  have hfg : A.L.FG := hA.1.2.1
  have hnoeth : IsNoetherian (𝓞 K) A.L := isNoetherian_of_fg_of_noetherian A.L hfg
  have fg_of_le : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → N.FG := fun N hN => isNoetherian_submodule.mp hnoeth N hN
  have hL1 : L1 ≤ A.L := inf_le_left
  have hL0 : L0 ≤ A.L := inf_le_left
  have lat : ∀ N : Submodule (𝓞 K) A.V, N ≤ A.L → Formalism.HN.IsLat ρR N :=
    fun N hN => (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le N hN)).1
  have hL1ne : L1 ≠ ⊥ := by
    intro h
    have hr := rankPart K G T P0 P hM A ρ hA
    rw [← hL1def, h] at hr
    have h0 : rkL A (⊥ : Submodule (𝓞 K) A.V) = 0 := by
      simp [rkL, Formalism.HN.rkK]
    omega
  obtain ⟨hmax1, -, ⟨N, hNsat, hN0, hNslope⟩, -⟩ := Formalism.HN.muChar (𝓞 K) A.V _ ρR L1 (lat L1 hL1) hL1ne
  have hNL1 : N ≤ L1 := hNsat.1
  have hNL : N ≤ A.L := hNL1.trans hL1
  obtain ⟨x, hxN, hx0⟩ := (Submodule.ne_bot_iff N).mp hN0
  have hrkN : (Formalism.HN.rk ρR N : ℝ) ≠ 0 := by
    have hpl := (Formalism.HN.plLat K A.V A.ι A.b A.X hA.1.1 N (fg_of_le N hNL)).2.1
    have hspan : Submodule.span K (N : Set A.V) ≠ ⊥ := by
      intro h
      apply hx0
      have hmem := Submodule.subset_span (R := K) hxN
      rw [h] at hmem
      exact (Submodule.mem_bot K).mp hmem
    have hk : Formalism.HN.rkK N ≠ 0 := fun h => hspan (Submodule.finrank_eq_zero.mp h)
    have hq : Module.finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
    rw [hpl]
    exact_mod_cast mul_ne_zero hq hk
  have hminN : Formalism.HN.muMax ρR L1 ≤ Formalism.HN.muMin ρR N := by
    obtain ⟨-, hmin, -⟩ := Formalism.HN.muChar (𝓞 K) A.V _ ρR N (lat N hNL) hN0
    rw [hmin]
    intro N' hN'
    have h1 := (hmax1 (Formalism.HN.muMax ρR L1)).mp le_rfl N' (hN'.trans hNL1)
    have h2 : Formalism.HN.deg ρR N = Formalism.HN.muMax ρR L1 * Formalism.HN.rk ρR N := by
      rw [← hNslope]
      unfold Formalism.HN.slope Formalism.F.slope
      unfold Formalism.HN.deg Formalism.HN.rk at *
      field_simp
    rw [mul_sub]
    linarith
  have hxR : x ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T)) := (Submodule.mem_inf.mp (hNL1 hxN)).2
  obtain ⟨g, hg⟩ := exists_g T P0 P hM ρ x hxR hx0
  set φ : A.V →ₗ[K] A.V := ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G g) with hφdef
  have hcardK : ((Fintype.card P0.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hφx : φ x ≠ 0 := by
    rw [hφdef, epsSum_eq, smul_mul_assoc, map_smul, map_mul, LinearMap.smul_apply, Module.End.mul_apply,
      Representation.asAlgebraHom_of]
    exact smul_ne_zero hcardK hg
  have hmapL : ∀ y ∈ A.L, φ y ∈ A.L := by
    intro y hy
    rw [hφdef, phi_apply]
    refine A.L.sum_mem fun h _ => ?_
    have hint : IsIntegral ℤ ((((P0.chi h)⁻¹ : Kˣ) : K)) :=
      IsIntegral.of_pow Fintype.card_pos (by rw [chi_pow]; exact isIntegral_one)
    have hmem : ρ (h : G) (ρ g y) ∈ A.L := hA.2.1 _ _ (hA.2.1 _ _ hy)
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (((P0.chi h)⁻¹ : Kˣ) : K) := ⟨⟨_, hint⟩, rfl⟩
    rw [← hr, algebraMap_smul]
    exact A.L.smul_mem r hmem
  have hmapR : ∀ y ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eG T)),
      φ y ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eG T)) := by
    rintro y ⟨z, rfl⟩
    refine ⟨ρ.asAlgebraHom (epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T)) z, ?_⟩
    have alg : eps P0 * eG T * (epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T)) =
        epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T) := by
      calc eps P0 * eG T * (epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T))
          = eps P0 * (eG T * (epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T))) := by rw [mul_assoc]
        _ = eps P0 * ((epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T)) * eG T) := by rw [← eG_comm]
        _ = (eps P0 * epsSum P0) * (MonoidAlgebra.of K G g * (eps P * (eG T * eG T))) := by
          simp only [mul_assoc]
        _ = epsSum P0 * MonoidAlgebra.of K G g * (eps P * eG T) := by
          rw [eps_mul_epsSum, eG_idem]
          simp only [mul_assoc]
    rw [← Module.End.mul_apply, ← map_mul, alg, hφdef, map_mul, Module.End.mul_apply]
  have hmap : ∀ y : N, φ (y : A.V) ∈ L0 := fun y =>
    Submodule.mem_inf.mpr ⟨hmapL _ (hNL y.2), hmapR _ (Submodule.mem_inf.mp (hNL1 y.2)).2⟩
  let ψ : N →ₗ[𝓞 K] L0 := LinearMap.codRestrict L0 ((φ.restrictScalars (𝓞 K)).domRestrict N) hmap
  have hψ : ∀ y : N, ((ψ y : L0) : A.V) = φ y := fun y => rfl
  have hψ0 : ψ ≠ 0 := by
    intro h
    apply hφx
    have := congrArg (fun f : N →ₗ[𝓞 K] L0 => ((f ⟨x, hxN⟩ : L0) : A.V)) h
    simpa [hψ] using this
  set C : ℝ := (Fintype.card P0.H : ℝ) with hCdef
  have hC : 0 < C := by rw [hCdef]; exact_mod_cast Fintype.card_pos
  have hplace : ∀ v y, Formalism.HermitianLatticesTheory.normAt A.b A.X v (φ y) ≤ C * Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
    intro v y
    rw [hφdef, phi_apply]
    refine (normAt_sum_le' A.b A.X v _ _).trans (le_of_eq ?_)
    have hterm : ∀ h : P0.H, Formalism.HermitianLatticesTheory.normAt A.b A.X v ((((P0.chi h)⁻¹ : Kˣ) : K) • ρ (h : G) (ρ g y)) =
        Formalism.HermitianLatticesTheory.normAt A.b A.X v y := by
      intro h
      rw [normAt_smul', hA.2.2, hA.2.2]
      have hn : ‖v.embedding ((((P0.chi h)⁻¹ : Kˣ) : K))‖ = 1 :=
        Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, chi_pow, map_one]) Fintype.card_ne_zero
      rw [hn, one_mul]
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hCdef]
  have hbound : ∀ y : N, ‖ρR ((ψ y : L0) : A.V)‖ ≤ C * ‖ρR (y : A.V)‖ := by
    intro y
    rw [hψ]
    exact realize_le A.b A.X φ C hC.le hplace y
  obtain ⟨h1, -⟩ := Formalism.HN.slopeIneq (𝓞 K) A.V A.V _ _ ρR ρR N L0 (lat N hNL) (lat L0 hL0) ψ C hC hbound
  have key := (h1 hψ0).2
  have hlogC : Real.log C ≤ laG G := by
    unfold laG
    apply Real.log_le_log hC
    rw [hCdef]
    exact_mod_cast Fintype.card_subtype_le _
  have hla : 0 ≤ laG G := by
    unfold laG
    exact Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  unfold muMaxL Formalism.HN.muMaxDef
  linarith

end PI.Dv.Tr
