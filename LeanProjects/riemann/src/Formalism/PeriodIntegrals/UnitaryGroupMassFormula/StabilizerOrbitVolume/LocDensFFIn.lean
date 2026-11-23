import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFCnt

noncomputable section

namespace PI.VolStabSW.FFHS

open Module Polynomial

section matrix

variable {K : Type} [Field K] {σ : K →+* K}

theorem ffH_isHS (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) : IsHS σ (ffH σ J) where
  add_right x y z := by
    simp only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right c x y := by
    simp only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  herm x y := by
    simp only [ffH, map_sum, map_mul, hσ, hJ]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  nondeg x hx := by
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j0
      have := hx (Pi.single j0 1)
      simpa [ffH, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hinv : (fun i => σ (x i)) = 0 := by
      have := congrArg (fun v => Matrix.vecMul v J⁻¹) hv
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] using this
    funext i
    exact σ.injective (by simpa using congrFun hinv i)

theorem ffH_single {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  have hs : ∀ i' : Fin n, σ ((Pi.single i 1 : Fin n → K) i') = (Pi.single i 1 : Fin n → K) i' := by
    intro i'
    by_cases h : i' = i
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  simp only [PI.VolStabSW.ffH, hs]
  simp [Pi.single_apply]

end matrix

theorem card_isom {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} := by
  refine Nat.card_congr
    { toFun := fun φ => ⟨fun i => φ.1 (b i), fun i j => φ.2 (b i) (b j)⟩
      invFun := fun Y => ⟨b.constr K Y.1, fun x y => ?_⟩
      left_inv := fun φ => ?_
      right_inv := fun Y => ?_ }
  · have hs1 : IsSq σ (fun x y => hV (b.constr K Y.1 x) (b.constr K Y.1 y)) :=
      { add_right := fun x y z => by
          simp only [map_add]
          exact hsV.add_right _ _ _
        smul_right := fun c x y => by
          simp only [map_smul]
          exact hsV.smul_right _ _ _
        herm := fun x y => hsV.herm _ _ }
    exact hs1.ext_basis hsU b (fun i j => by simpa only [Basis.constr_basis] using Y.2 i j) x y
  · apply Subtype.ext
    exact b.ext fun i => by simp [Basis.constr_basis]
  · apply Subtype.ext
    funext i
    simp [Basis.constr_basis]

section field

variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]

private theorem card_le_natDegree_of_eval_eq_zero {L : Type} [Field L] (P : L[X]) (hP : P ≠ 0)
    (Z : Finset L) (hZ : ∀ z ∈ Z, P.eval z = 0) : Z.card ≤ P.natDegree := by
  have hsub : Z.val ⊆ P.roots := fun z hz =>
    (Polynomial.mem_roots hP).mpr (hZ z (Finset.mem_val.mp hz))
  exact (Multiset.card_le_card ((Multiset.le_iff_subset Z.nodup).mpr hsub)).trans
    (Polynomial.card_roots' P)

private theorem card_le_of_pow_eq_mul_add {L : Type} [Field L] (n : ℕ) (hn : 1 < n) (b c : L)
    (Z : Finset L) (hZ : ∀ z ∈ Z, z ^ n = b * z + c) : Z.card ≤ n := by
  have hlt : (C b * X + C c : L[X]).natDegree < (X ^ n : L[X]).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    exact lt_of_le_of_lt Polynomial.natDegree_linear_le hn
  have hdeg : (X ^ n - (C b * X + C c) : L[X]).natDegree = n := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hP0 : (X ^ n - (C b * X + C c) : L[X]) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have := card_le_natDegree_of_eval_eq_zero _ hP0 Z fun z hz => by simp [hZ z hz]
  rwa [hdeg] at this

private theorem exists_algebraMap_eq_of_frobenius_fixed (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  by_contra hne
  push_neg at hne
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hdS : d ∉ Finset.univ.image (algebraMap k K) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hne
  have hc := card_le_of_pow_eq_mul_add (Fintype.card k) hq 1 0
    (Finset.cons d (Finset.univ.image (algebraMap k K)) hdS) (by
      intro z hz
      rw [Finset.mem_cons] at hz
      rcases hz with h | hz
      · rw [h, hd, one_mul, add_zero]
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
        rw [← map_pow, FiniteField.pow_card, one_mul, add_zero])
  rw [Finset.card_cons, Finset.card_image_of_injective _ (algebraMap k K).injective,
    Finset.card_univ] at hc
  omega

theorem frob_of_ne (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  intro x
  haveI : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  by_cases hx : ∃ a : k, algebraMap k K a = x
  · obtain ⟨a, rfl⟩ := hx
    rw [AlgEquiv.commutes, ← map_pow, FiniteField.pow_card]
  push_neg at hx
  have hq : x ^ Fintype.card k ≠ x := fun h => by
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_frobenius_fixed x h
    exact hx a ha
  have hσx : σ x ≠ x := by
    intro hfix
    apply hne
    have hli : LinearIndependent k ![(1 : K), x] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        exact ⟨by simpa using hst, rfl⟩
      · exfalso
        have htK : algebraMap k K t ≠ 0 := (_root_.map_ne_zero _).mpr ht
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        apply hx (-s * t⁻¹)
        rw [map_mul, map_neg, map_inv₀, eq_comm, eq_mul_inv_iff_mul_eq₀ htK]
        linear_combination hst
    have hlin : σ.toLinearMap = LinearMap.id :=
      (basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])).ext fun i => by
        fin_cases i <;> simp [coe_basisOfLinearIndependentOfCardEqFinrank, hfix]
    ext y
    simpa using LinearMap.congr_fun hlin y
  have hint_r : IsIntegral k x := IsIntegral.of_finite k x
  have hP0 : (minpoly k x).map (algebraMap k K) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint_r)
  have hroot : ∀ y, Polynomial.aeval y (minpoly k x) = 0 →
      ((minpoly k x).map (algebraMap k K)).eval y = 0 := fun y hy => by
    rw [Polynomial.eval_map_algebraMap]
    exact hy
  have r1 := hroot x (minpoly.aeval k x)
  have r2 := hroot (σ x) (by
    rw [show σ x = (σ : K →ₐ[k] K) x from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval,
      map_zero])
  have r3 := hroot (x ^ Fintype.card k) (by
    rw [← Polynomial.expand_aeval, FiniteField.expand_card, map_pow, minpoly.aeval,
      zero_pow Fintype.card_ne_zero])
  by_contra hne3
  have hcard : ({x, σ x, x ^ Fintype.card k} : Finset K).card = 3 :=
    Finset.card_eq_three.mpr ⟨x, σ x, x ^ Fintype.card k, hσx.symm, hq.symm, hne3, rfl⟩
  have hle := card_le_natDegree_of_eval_eq_zero _ hP0 {x, σ x, x ^ Fintype.card k} (by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h <;> rw [h] <;> assumption)
  rw [hcard, Polynomial.natDegree_map] at hle
  have hdeg : (minpoly k x).natDegree ≤ finrank k K := minpoly.natDegree_le x
  omega

theorem card_norm_fiber (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hKcard' : Fintype.card K = Fintype.card k ^ finrank k K := Module.card_eq_pow_finrank
  have hKcard : Fintype.card K = Fintype.card k ^ 2 := by rw [hKcard', h2]
  have hσσ : ∀ t, σ (σ t) = t := by
    intro t
    rw [hfrob (σ t), hfrob t, ← pow_mul, ← sq, ← hKcard, FiniteField.pow_card]
  let c : K → ℕ := fun y => (Finset.univ.filter fun t : K => t * σ t = y).card
  let F : Finset K := Finset.univ.filter fun y : K => y ^ Fintype.card k = y
  have hsum : Fintype.card K = ∑ y ∈ F, c y := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (f := fun t => t * σ t) fun t _ => by
      simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hfrob, map_mul, hσσ, mul_comm]
  have hF : F.card ≤ Fintype.card k :=
    card_le_of_pow_eq_mul_add _ hq1 1 0 F fun z hz => by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [hz, one_mul, add_zero]
  have hfib : ∀ y, c y ≤ Fintype.card k + 1 := fun y =>
    card_le_of_pow_eq_mul_add _ (by omega) 0 y (Finset.univ.filter fun t : K => t * σ t = y)
      fun t ht => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        rw [pow_succ', ← hfrob, ht, zero_mul, zero_add]
  have hc0 : c 0 = 1 := by
    show (Finset.univ.filter fun t : K => t * σ t = 0).card = 1
    rw [Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext t
    simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  split_ifs with hd0
  · subst hd0
    exact hc0
  · have hdF : d ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hfrob, hd]
    have h0F : (0 : K) ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact zero_pow (by omega)
    refine le_antisymm (hfib d) ?_
    by_contra hlt
    push_neg at hlt
    have key : ∑ y ∈ F.erase 0, c y < ∑ _y ∈ F.erase 0, (Fintype.card k + 1) :=
      Finset.sum_lt_sum (fun y _ => hfib y) ⟨d, Finset.mem_erase.mpr ⟨hd0, hdF⟩, hlt⟩
    rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0F] at key
    have hs := Finset.add_sum_erase F c h0F
    rw [hc0] at hs
    have hn : 1 ≤ F.card := Finset.card_pos.mpr ⟨0, h0F⟩
    have h3 : (F.card - 1) * (Fintype.card k + 1) ≤
        (Fintype.card k - 1) * (Fintype.card k + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (Fintype.card k - 1) * (Fintype.card k + 1) + 1 = Fintype.card k ^ 2 := by
      obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel]
      ring
    omega

end field

theorem fFInert_holds : FFInert := by
  unfold PI.VolStabSW.FFInert
  intro k K _ _ _ _ σ hσ h2 hne h2k M a haM J hJ hdet T hT hTdet
  classical
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite K := Module.finite_of_finite k
  haveI : Fintype K := Fintype.ofFinite K
  have hfrob := frob_of_ne σ h2 hne
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have h2K : (2 : K) ≠ 0 := by
    have := (algebraMap k K).injective.ne h2k
    rwa [map_ofNat, map_zero] at this
  have hK' : Fintype.card K = Fintype.card k ^ Module.finrank k K := Module.card_eq_pow_finrank
  have hK : Fintype.card K = Nat.card k ^ 2 := by
    rw [hK', h2, Nat.card_eq_fintype_card]
  have hN : ∀ d, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Nat.card k + 1 := by
    intro d hd
    rw [Nat.card_eq_fintype_card (α := k)]
    exact card_norm_fiber σ hfrob h2 d hd
  have hq0 : 0 < Nat.card k := Nat.card_pos
  have hsV := ffH_isHS hσ' J hJ hdet
  have hsU := ffH_isHS hσ' T hT hTdet
  obtain ⟨f, horth, hnz⟩ := exists_orth h2K a (Fin a → K)
    (PI.VolStabSW.ffH (σ : K →+* K) T) hsU (Module.finrank_fin_fun K)
  have hli := linIndep_orth hsU.toIsSq f horth hnz
  have hsp : Submodule.span K (Set.range f) = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_fin_fun])
  let bf := Module.Basis.mk hli hsp.ge
  have hbf : ∀ i, bf i = f i := fun i => Module.Basis.mk_apply hli hsp.ge i
  have e1 : Nat.card {X : Fin a → Fin M → K // PI.VolStabSW.ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) J (Y i) (Y j) =
        PI.VolStabSW.ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i) (Pi.basisFun K (Fin a) j)} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun X => ?_)
    simp only [Pi.basisFun_apply, ffH_single]
    constructor
    · intro h i j
      exact congrFun (congrFun h i) j
    · intro h
      ext i j
      exact h i j
  have e2 := card_isom hsU.toIsSq
    hsV.toIsSq (Pi.basisFun K (Fin a))
  have e3 := card_isom hsU.toIsSq
    hsV.toIsSq bf
  have e4 : Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) J (Y i) (Y j) =
        PI.VolStabSW.ffH (σ : K →+* K) T (bf i) (bf j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) J (Y i) (Y j) =
        if i = j then PI.VolStabSW.ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    have hg : ∀ i j, PI.VolStabSW.ffH (σ : K →+* K) T (bf i) (bf j) =
        if i = j then PI.VolStabSW.ffH (σ : K →+* K) T (f i) (f i) else 0 := by
      intro i j
      simp only [hbf]
      split_ifs with hij
      · rw [hij]
      · exact horth i j hij
    refine Nat.card_congr (Equiv.subtypeEquivRight fun Y => ?_)
    simp only [hg]
  rw [e1, ← e2, e3, e4]
  exact card_diag (Nat.card k) hq0 hK hσ' h2K hN a M haM
    (Fin M → K) (PI.VolStabSW.ffH (σ : K →+* K) J) hsV (Module.finrank_fin_fun K)
    (fun i => PI.VolStabSW.ffH (σ : K →+* K) T (f i) (f i))
    (fun i => hsU.toIsSq.self_fixed (f i)) hnz

end PI.VolStabSW.FFHS
