import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MajorantSquareBound
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

namespace UpperTheory.V.Loc

section Gen

variable {R K H : Type} [CommRing R] [CommRing K] [Group H] (f : R →+* K)

private theorem spl_rep (r : H →* M4 R) (g : H) : mapRep f r g = f.mapMatrix (r g) := rfl

private theorem spl_smul (a : R) (X : M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp

private theorem spl_adj (X : M4 R) : adj (f.mapMatrix X) = f.mapMatrix (adj X) := by
  ext i j
  simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul]

private theorem spl_gsp {ν : R} {X : M4 R} (h : IsGSp ν X) : IsGSp (f ν) (f.mapMatrix X) := by
  unfold IsGSp at *
  rw [spl_adj, ← map_mul, h, spl_smul, map_one]

private theorem spl_prj (c : Fin 4 → R) (X : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix X) i = f.mapMatrix (prj c X i) := by
  unfold prj
  have h : ∀ p : Polynomial R,
      Polynomial.aeval (f.mapMatrix X) (p.map f) = f.mapMatrix (Polynomial.aeval X p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, map_add, hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, spl_smul, map_one]
  rw [← h, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem spl_ord {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H} {r : H →* M4 R} (h : Ord I ps s₀ r) :
    Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) where
  charpoly := by
    rw [spl_rep, RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  stable g i j hij := by
    rw [spl_rep, spl_rep, spl_prj f (fun a => ps a s₀), spl_prj f (fun a => ps a s₀), ← map_mul, ← map_mul,
      h.stable g i j hij, map_zero]
  inert s hs i := by
    rw [spl_rep, spl_rep, spl_prj f (fun a => ps a s₀), ← map_one f.mapMatrix, ← spl_smul, ← map_sub, ← map_mul,
      ← map_mul, h.inert s hs i, map_zero]

private theorem spl_tr (c : Fin 4 → R) (X Y : M4 R) (i : Fin 4) :
    (prj (fun a => f (c a)) (f.mapMatrix X) i * f.mapMatrix Y).trace = f (prj c X i * Y).trace := by
  rw [spl_prj, ← map_mul, RingHom.mapMatrix_apply, AddMonoidHom.map_trace]

private theorem spl_tr_diag (c a : Fin 4 → R) (i : Fin 4) :
    (prj c (Matrix.diagonal c) i * Matrix.diagonal a).trace = (∏ j ∈ Finset.univ.erase i, (c i - c j)) * a i := by
  have h : prj c (Matrix.diagonal c) i = Matrix.diagonal fun b => ∏ j ∈ Finset.univ.erase i, (c b - c j) := by
    unfold prj
    have h1 := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom (n := Fin 4) (α := R) R) c
      (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (c j)))
    rw [Matrix.diagonalAlgHom_apply, Matrix.diagonalAlgHom_apply] at h1
    rw [h1]
    congr 1
    funext b
    simp [map_prod]
  rw [h, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Finset.sum_eq_single i]
  · intro b _ hb
    rw [Finset.prod_eq_zero (i := b) (by simp [hb]) (sub_self _), zero_mul]
  · simp

private theorem spl_adj_mul (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev] <;> ring

private theorem spl_adj_one : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

private theorem spl_conj {ν : R} {X : M4 R} (h : IsGSp ν X) (u v : M4 R) (hv : v * u = 1) :
    adj (u * X * v) * (adj v * v) * (u * X * v) = ν • (adj v * v) := by
  have h1 : adj u * adj v = 1 := by
    rw [← spl_adj_mul, hv, spl_adj_one]
  unfold IsGSp at h
  rw [spl_adj_mul, spl_adj_mul]
  calc _ = adj v * (adj X * (adj u * adj v) * (v * u) * X) * v := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, hv, Matrix.mul_one, Matrix.mul_one, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

private theorem spl_adj_unit (u : (M4 R)ˣ) : IsUnit (adj (u : M4 R)) :=
  IsUnit.of_mul_eq_one (adj ((u⁻¹ : (M4 R)ˣ) : M4 R)) (by rw [← spl_adj_mul, Units.inv_mul, spl_adj_one])

end Gen

section Fld

variable {K : Type} [Field K]

private theorem spl_gram {ν : K} {M A : M4 K} (hM : ∀ i j, j < i → M i j = 0) (h : adj M * A * M = ν • A)
    (hc : ∀ i j : Fin 4, j < i → M i.rev i.rev * M j j ≠ ν) : ∀ i j, j < i → A i j = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  have m10 := hM 1 0 (by decide)
  have m20 := hM 2 0 (by decide)
  have m30 := hM 3 0 (by decide)
  have m21 := hM 2 1 (by decide)
  have m31 := hM 3 1 (by decide)
  have m32 := hM 3 2 (by decide)
  have k : ∀ {a b x : K}, a ≠ b → a * x = b * x → x = 0 := fun hab hx => by
    by_contra h0
    exact hab (mul_right_cancel₀ h0 hx)
  have e30 := e 3 0
  have e20 := e 2 0
  have e10 := e 1 0
  have e31 := e 3 1
  have e21 := e 2 1
  have e32 := e 3 2
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, m10, m20, m30, m21, m31, m32] at e30 e20 e10 e31 e21 e32
  have a30 : A 3 0 = 0 := k (hc 3 0 (by decide)) (by show M 0 0 * M 0 0 * _ = _; linear_combination e30)
  rw [a30] at e20 e10 e31 e21 e32
  have a20 : A 2 0 = 0 := k (hc 2 0 (by decide)) (by show M 1 1 * M 0 0 * _ = _; linear_combination e20)
  have a31 : A 3 1 = 0 := k (hc 3 1 (by decide)) (by show M 0 0 * M 1 1 * _ = _; linear_combination e31)
  simp only [a20, a31] at e10 e21 e32
  have a10 : A 1 0 = 0 := k (hc 1 0 (by decide)) (by show M 2 2 * M 0 0 * _ = _; linear_combination e10)
  have a21 : A 2 1 = 0 := k (hc 2 1 (by decide)) (by show M 1 1 * M 1 1 * _ = _; linear_combination e21)
  have a32 : A 3 2 = 0 := k (hc 3 2 (by decide)) (by show M 0 0 * M 2 2 * _ = _; linear_combination e32)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

private theorem spl_dual {ν : K} {M A : M4 K} (hM : ∀ i j, j < i → M i j = 0) (hA : ∀ i j, j < i → A i j = 0)
    (hu : IsUnit A) (h : adj M * A * M = ν • A) (i : Fin 4) : M i.rev i.rev * M i i = ν := by
  have hA' : A.BlockTriangular id := fun i j h => hA i j h
  have hM' : M.BlockTriangular id := fun i j h => hM i j h
  have hN : (adj M).BlockTriangular id := fun i j h => by
    rw [adj_apply, hM j.rev i.rev (Fin.rev_lt_rev.2 h), smul_zero]
  have hd : ∀ {X Y : M4 K}, X.BlockTriangular id → Y.BlockTriangular id → (X * Y) i i = X i i * Y i i := by
    intro X Y hX hY
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hX h, zero_mul]
      · rw [hY h, mul_zero]
    · simp
  have h0 : A i i ≠ 0 := by
    have := ((Matrix.isUnit_iff_isUnit_det A).1 hu).ne_zero
    rw [Matrix.det_of_upperTriangular hA'] at this
    exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ _)
  have e := congrFun (congrFun h i) i
  have hs : ∀ i, sgn i * sgn i = 1 := by decide
  rw [hd (hN.mul hA') hM', hd hN hA', adj_apply, hs, one_smul, Matrix.smul_apply, smul_eq_mul] at e
  exact mul_right_cancel₀ h0 (by linear_combination e)

private theorem spl_int {B : Type} [CommRing B] [Algebra B K] (X : M4 B) (u : (M4 K)ˣ)
    (hM : ∀ i j, j < i → ((u : M4 K) * (algebraMap B K).mapMatrix X * (u⁻¹ : (M4 K)ˣ)) i j = 0) (i : Fin 4) :
    IsIntegral B (((u : M4 K) * (algebraMap B K).mapMatrix X * (u⁻¹ : (M4 K)ˣ)) i i) := by
  refine ⟨X.charpoly, X.charpoly_monic, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map, ← RingHom.mapMatrix_apply,
    ← Matrix.charpoly_units_conj u, ← Matrix.coe_units_inv, Matrix.charpoly_of_upperTriangular _ (fun i j h => hM i j h),
    Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

end Fld

private theorem spl_local (R S : Type) [CommRing R] [HenselianLocalRing R] [CommRing S] [IsDomain S] [Algebra R S]
    [Module.Finite R S] : IsLocalRing S := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal S
  obtain ⟨e, he, h⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian R q
  refine IsLocalRing.of_unique_max_ideal ⟨q, hq, fun n hn => (h n hn).1 ?_⟩
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 he with rfl | rfl
  · exact absurd q.zero_mem ((h q hq).2 rfl)
  · exact (Ideal.ne_top_iff_one n).1 hn.ne_top

private theorem spl_intOf {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
  exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

open Polynomial in
private theorem spl_norm_lt {l : ℕ} [Fact l.Prime] {O R : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing R] [IsLocalRing R] [Algebra O R]
    (y : R →ₐ[O] PadicAlgCl l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.NormLtOne.norm_lt_one y a ha

private theorem spl_near {l : ℕ} [Fact l.Prime] {O B : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing B] [IsDomain B] [HenselianLocalRing B]
    [Algebra O B] (x y : B →ₐ[O] PadicAlgCl l) (d : O) (hd : algebraMap O (PadicAlgCl l) d ≠ 0) (t : B) (ht : x t = 0)
    (v : FractionRing B) (hv : IsIntegral B v)
    (hvt : algebraMap B _ (algebraMap O B d) * v = algebraMap B _ t) (κ : PadicAlgCl l)
    (hκ : algebraMap O _ d * κ = y t) : ‖κ‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.MajorantSquareBound.spl_near x y d hd t ht v hv hvt κ hκ

private theorem spl_red {l : ℕ} [Fact l.Prime] {O B H : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing B] [IsDomain B] [HenselianLocalRing B]
    [Algebra O B] [Group H] (hO : Function.Injective (algebraMap O (PadicAlgCl l))) {I : Subgroup H}
    {ps : Fin 4 → H → O} {s₀ : H} (hinj : Function.Injective fun i => ps i s₀) {ρ : H →* M4 B}
    (hρ : Ord I (fun i g => algebraMap O B (ps i g)) s₀ ρ) (x : B →ₐ[O] O)
    (hx : ∀ g a b, x (ρ g a b) = Matrix.diagonal (fun i => ps i g) a b) (y : B →ₐ[O] PadicAlgCl l) (i : Fin 4) (g : H)
    (κ : PadicAlgCl l)
    (hκ : (∏ j ∈ Finset.univ.erase i, (algebraMap O _ (ps i s₀) - algebraMap O _ (ps j s₀))) * κ =
      (prj (fun a => algebraMap O _ (ps a s₀)) (mapRep (y : B →+* PadicAlgCl l) ρ s₀) i *
        mapRep (y : B →+* PadicAlgCl l) ρ g).trace) : ‖κ - algebraMap O _ (ps i g)‖ < 1 := by
  let d : O := ∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)
  let t : B := (prj (fun a => algebraMap O B (ps a s₀)) (ρ s₀) i * ρ g).trace
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 fun e => (Finset.mem_erase.1 hj).1 (hinj e).symm
  have hB : Function.Injective (algebraMap O B) := fun a b e => by simpa using congrArg x e
  have hxt : x t = d * ps i g := by
    have h1 := spl_tr (x : B →+* O) (fun a => algebraMap O B (ps a s₀)) (ρ s₀) (ρ g) i
    have h2 : ∀ g, (x : B →+* O).mapMatrix (ρ g) = Matrix.diagonal fun i => ps i g := fun g => Matrix.ext (hx g)
    simp only [h2, RingHom.coe_coe, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h1
    rw [spl_tr_diag] at h1
    exact h1.symm
  have hyt : algebraMap O _ d * κ = y t := by
    have h1 := spl_tr (y : B →+* PadicAlgCl l) (fun a => algebraMap O B (ps a s₀)) (ρ s₀) (ρ g) i
    simp only [RingHom.coe_coe, AlgHom.commutes] at h1
    rw [← h1, map_prod]
    simp only [map_sub]
    exact hκ
  obtain ⟨u, k, h1, h2, -, h4⟩ := ordFlag I (FractionRing B) _ s₀ _
    (fun a b e => hinj (hB (IsFractionRing.injective B (FractionRing B) e))) (spl_ord (algebraMap B (FractionRing B)) hρ)
  have hint : IsIntegral B (k i g : FractionRing B) := h2 g i ▸ spl_int (ρ g) u (h1 g) i
  have hk : algebraMap B (FractionRing B) (algebraMap O B d) * k i g = algebraMap B _ t := by
    rw [← spl_tr (algebraMap B (FractionRing B)), map_prod, map_prod]
    simp only [map_sub]
    exact h4 i g
  refine spl_near ((Algebra.ofId O _).comp x) y d ((map_ne_zero_iff _ hO).2 hd) (t - algebraMap O B (d * ps i g)) ?_
    (k i g - algebraMap B _ (algebraMap O B (ps i g))) (hint.sub isIntegral_algebraMap) ?_ _ ?_
  · rw [AlgHom.comp_apply, map_sub, hxt, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self, map_zero]
  · rw [mul_sub, hk, map_sub, map_mul, map_mul]
  · rw [mul_sub, hyt, map_sub, AlgHom.commutes, map_mul]

private theorem spl_cont {X R K : Type} [TopologicalSpace X] [CommRing R] [NormedRing K] (I : Ideal R) (y : R →+* K)
    {a : ℝ} (h1 : a < 1) (h0 : 0 ≤ a) (h : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n) {f : X → R} (hf : AdicCont I f) :
    Continuous fun g => y (f g) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε h1
  filter_upwards [(hf k).eventually_eq g] with g' hg'
  rw [dist_eq_norm, ← map_sub]
  exact (h k _ (Ideal.Quotient.eq.1 hg')).trans_lt hk

private theorem spl_bar {l : ℕ} [Fact l.Prime] (c : Coef l) {a b : c.O} {z : PadicAlgCl l} (ha : ‖z - a‖ < 1)
    (hb : ‖z - b‖ < 1) : residue c.O a = residue c.O b := by
  obtain ⟨-, t, -, -, ht⟩ := (coPt c c.O).1 (Algebra.ofId _ _)
  have h1 : ‖((a - b : c.O) : PadicAlgCl l)‖ < 1 := by
    have : ((a - b : c.O) : PadicAlgCl l) = (z - b) + -(z - a) := by push_cast; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hb (by rwa [norm_neg]))
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h2 : ‖(w : PadicAlgCl l)‖ ≤ 1 := by simpa using ht 0 w (by simp)
  have h3 : ‖((a - b : c.O) : PadicAlgCl l)‖ * ‖(w : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← MulMemClass.coe_mul, hw, OneMemClass.coe_one, norm_one]
  nlinarith [norm_nonneg ((a - b : c.O) : PadicAlgCl l), norm_nonneg (w : PadicAlgCl l)]

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.spPtL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (r : D.Gp l →* M4 (PadicAlgCl l)), PtOn D D.condL r → ∃ (h : (M4 (PadicAlgCl l))ˣ) (κ : Fin 4 → D.Gp l →* (PadicAlgCl l)ˣ), FlagIn r h κ ∧ (∀ i (s : D.Gp l), (s : G ℚ Ω) ∈ D.Ip l → (κ i s : PadicAlgCl l) = ((D.ps i s : c.Oˣ) : c.O)) ∧ (∀ i g, ‖(κ i g : PadicAlgCl l) - ((D.ps i g : c.Oˣ) : c.O)‖ < 1) ∧ (∀ g : D.Gp l, ((κ 0 g * κ 3 g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = ((D.th g : c.Oˣ) : c.O) ∧ ((κ 1 g * κ 2 g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = ((D.th g : c.Oˣ) : c.O)) ∧ (∀ i, Continuous fun g => (κ i g : PadicAlgCl l)) ∧ ∀ i j, i ≠ j → ∀ U : Subgroup (D.Gp l), IsOpen (U : Set (D.Gp l)) → (∃ g ∈ U, (g : G ℚ Ω) = D.sg l) → ∃ g ∈ U, (κ i g : PadicAlgCl l) ≠ (κ j g : PadicAlgCl l) * ((chiO ℚ Ω l c.O g : c.Oˣ) : c.O) := by
  intro Ω _ _ _ l _ c D hD r hr
  obtain ⟨R, _, _, _, ρ', y', ⟨B, _, _, _, _, ρ, hρ, ⟨x, hx⟩, y₀, rfl⟩, rfl⟩ := hr
  obtain ⟨-, hT, -, hwt, -, hrev, hinj, -⟩ := facts D hD
  let y : B →ₐ[c.O] PadicAlgCl l := y'.comp y₀
  have er : mapRep (y' : R →+* PadicAlgCl l) (ρ.map y₀).hom = mapRep (y : B →+* PadicAlgCl l) ρ.hom := rfl
  rw [er]
  have hy : ∀ a : c.O, (y : B →+* PadicAlgCl l) (algebraMap c.O B a) = algebraMap c.O _ a := fun a => y.commutes a
  have hO : Function.Injective (algebraMap c.O (PadicAlgCl l)) := Subtype.val_injective
  have hord := spl_ord (y : B →+* PadicAlgCl l) hρ.2
  simp only [hy] at hord
  have hgsp : ∀ g : D.Gp l, IsGSp (algebraMap c.O _ (D.th g)) (mapRep (y : B →+* PadicAlgCl l) ρ.hom g) := fun g => by
    have h := spl_gsp (y : B →+* PadicAlgCl l) (hρ.1 g)
    rwa [hy] at h
  obtain ⟨u, κ, h1, h2, h3, h4⟩ := ordFlag _ (PadicAlgCl l) _ D.s0 _ (fun a b e => hinj (hO e)) hord
  haveI : HenselianLocalRing B := GlobalTheory.henselianLocalRing_of_henselianRing B
  have hs0 : D.s0 ∈ (D.Ip l).subgroupOf (D.Gp l) := hD.decompSigma_mem.1.1
  have hred : ∀ i (g : D.Gp l), ‖(κ i g : PadicAlgCl l) - ((D.ps i g : c.Oˣ) : c.O)‖ < 1 := fun i g =>
    spl_red hO (ps := fun i (g : D.Gp l) => (D.ps i g : c.O)) hinj hρ.2 x hx y i g _ (h4 i g)
  have hdual : ∀ (g : D.Gp l) (i : Fin 4), (κ i.rev g : PadicAlgCl l) * κ i g = algebraMap c.O _ (D.th g) := by
    intro g i
    have hA := spl_gram (h1 D.s0) (spl_conj (hgsp D.s0) _ _ u.inv_mul) fun i j hij e => by
      rw [h2, h2, h3 _ _ hs0, h3 _ _ hs0, ← map_mul, ← hrev i, MonoidHom.mul_apply, mul_comm (D.ps i _), Units.val_mul] at e
      exact hij.ne (hinj ((Units.mul_right_inj _).1 (hO e)))
    rw [← h2, ← h2]
    exact spl_dual (h1 g) hA ((spl_adj_unit u⁻¹).mul (u⁻¹).isUnit) (spl_conj (hgsp g) _ _ u.inv_mul) i
  refine ⟨u⁻¹, κ, fun g => ⟨h1 g, h2 g⟩, fun i s hs => h3 i s hs, hred, fun g => ⟨hdual g 3, hdual g 2⟩, fun i => ?_,
    fun i j hij U hU ⟨g, hg, hgs⟩ => ?_⟩
  · obtain ⟨-, a, a1, a0, ha⟩ := (coPt c B).1 y
    have hc : Continuous fun g => mapRep (y : B →+* PadicAlgCl l) ρ.hom g :=
      continuous_matrix fun a b => spl_cont _ (y : B →+* PadicAlgCl l) a1 a0 ha (ρ.cont a b)
    simp only [← h2]
    exact ((continuous_const.matrix_mul hc).matrix_mul continuous_const).matrix_elem i i
  · by_contra hn
    push Not at hn
    have hlam : lamW i ≠ lamW j := by
      haveI : CompactSpace (D.Gp l) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
      haveI := Subgroup.quotient_finite_of_isOpen U hU
      haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      obtain ⟨n, hn0, -, hnU⟩ := U.exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero D.s0
      have e := hn _ hnU
      have hm : ((D.s0 ^ n : D.Gp l) : G ℚ Ω) ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker := pow_mem hD.decompSigma_mem n
      rw [h3 i _ hm.1.1, h3 j _ hm.1.1, hwt i _ hm, hwt j _ hm] at e
      have e1 : chiO ℚ Ω l c.O (D.s0 ^ n : D.Gp l) ^ D.wts4 i = chiO ℚ Ω l c.O (D.s0 ^ n : D.Gp l) ^ (D.wts4 j + 1) := by
        apply Units.ext
        apply hO
        rw [e, pow_succ, Units.val_mul, map_mul]
        rfl
      have hZ : Function.Injective (algebraMap ℤ_[l] c.O) :=
        Function.Injective.of_comp (f := algebraMap c.O (PadicAlgCl l)) (by
          rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l]]
          exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
      have hf : ¬ IsOfFinOrder (chiO ℚ Ω l c.O (D.s0 ^ n : D.Gp l)) := fun hf => hD.decompSigma_ord (by
        have h5 := ((Units.map_injective (f := (algebraMap ℤ_[l] c.O).toMonoidHom) hZ).isOfFinOrder_iff).1 hf
        rw [SubgroupClass.coe_pow, map_pow] at h5
        exact h5.of_pow hn0.ne')
      have e2 := injective_pow_iff_not_isOfFinOrder.2 hf e1
      have := hD.two_le
      fin_cases i <;> fin_cases j <;> simp [Raw.wts4, lamW] at e2 ⊢ <;> omega
    have e := hn g hg
    have e1 : chiO ℚ Ω l c.O g = 1 := by
      rw [hgs, chiO, MonoidHom.comp_apply, hD.sg_cyc, map_one]
    rw [e1, Units.val_one, OneMemClass.coe_one, mul_one] at e
    refine (hT l (Finset.mem_insert_self _ _)).2.2 i j hlam ?_
    rw [← hgs]
    exact spl_bar c (hred i g) (e ▸ hred j g)
