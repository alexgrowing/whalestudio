import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RatNoetherFrame

section Normalization

variable {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R] {J : Type*} [Fintype J]

theorem exists_intOver_start (v : J → R) :
    ∃ r, ∃ L : Fin r → J → k, ∀ t, IntOver k (forms v L) (v t) := by
  classical
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j s => if s = e.symm j then 1 else 0, fun t => ?_⟩
  have hf : forms v (fun j s => if s = e.symm j then (1 : k) else 0) = fun j => v (e.symm j) := by
    funext j
    simp [forms, ite_smul]
  rw [hf]
  have : v t = (aeval (fun j => v (e.symm j)) : MvPolynomial (Fin _) k →ₐ[k] R) (X (e t)) := by
    simp
  rw [this]
  exact RingHom.isIntegralElem_map _

theorem algebraicIndependent_of_minimal [Infinite k] (hinj : Function.Injective (algebraMap k R))
    (v : J → R) : ∀ (r : ℕ) (L : Fin r → J → k), (∀ t, IntOver k (forms v L) (v t)) →
      (∀ r' < r, ∀ L' : Fin r' → J → k, ¬ ∀ t, IntOver k (forms v L') (v t)) →
      AlgebraicIndependent k (forms v L)
  | 0, _, _, _ => algebraicIndependent_empty_type_iff.mpr hinj
  | r + 1, L, hL, hmin => by
    by_contra hnot
    rw [algebraicIndependent_iff] at hnot
    push Not at hnot
    obtain ⟨F, hF, hF0⟩ := hnot
    obtain ⟨lam, h0⟩ := exists_isIntegralElem_linear (forms v L) F hF0 hF
    refine hmin r (Nat.lt_succ_self r) (fun i s => L i.succ s - lam i * L 0 s) fun t => ?_
    have hf : forms v (fun i s => L i.succ s - lam i * L 0 s) =
        fun i => forms v L i.succ - lam i • forms v L 0 := by
      funext i
      simp [forms, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
    rw [hf]
    exact intOver_trans (forms v L) lam h0 (hL t)

theorem exists_indep_normalization [Infinite k] (hinj : Function.Injective (algebraMap k R)) (v : J → R) :
    ∃ r, ∃ L : Fin r → J → k, AlgebraicIndependent k (forms v L) ∧ ∀ t, IntOver k (forms v L) (v t) := by
  classical
  have hex := exists_intOver_start (k := k) v
  obtain ⟨L, hL⟩ := Nat.find_spec hex
  exact ⟨_, L, algebraicIndependent_of_minimal hinj v _ L hL
    fun r' hr' L' hL' => Nat.find_min hex hr' ⟨L', hL'⟩, hL⟩

end Normalization

section Cone

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type}

theorem sum_smul_cone [Fintype J] (x : J → Ω) (c : J → ℚ) :
    ∑ t, c t • (Polynomial.C (x t) * Polynomial.X) =
      Polynomial.C (∑ t, (c t : Ω) * x t) * Polynomial.X := by
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Algebra.smul_def, Polynomial.algebraMap_apply, ← mul_assoc, ← map_mul]
  simp

theorem coneMap_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    coneMap ℚ x (MvPolynomial.map (Int.castRingHom ℚ) f) = coneMap ℤ x f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [coneMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, map_X, hp]; simp [coneMap]

theorem ker_coneMap_rat (x : J → Ω) :
    RingHom.ker (coneMap ℚ x) = (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨N, hN, g, hg⟩ := exists_int_mul_eq_qmap f
    have hg0 : g ∈ coordIdeal ℤ x := by
      rw [coordIdeal, RingHom.mem_ker, ← coneMap_map_int]
      change coneMap ℚ x (qmap g) = 0
      rw [← hg, map_mul, RingHom.mem_ker.mp hf, mul_zero]
    have hmem : (N : MvPolynomial J ℚ) * f ∈
        (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
      rw [hg]
      exact Ideal.mem_map_of_mem _ hg0
    have hu : IsUnit (N : MvPolynomial J ℚ) := by
      have h1 : (N : MvPolynomial J ℚ) = C (N : ℚ) := by simp
      rw [h1]
      exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hN)).map C
    have h2 := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : MvPolynomial J ℚ) hmem
    rwa [← mul_assoc, hu.val_inv_mul, one_mul] at h2
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, coneMap_map_int]
    exact RingHom.mem_ker.mp hg

theorem withBot_eq_of_add_one {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) :
    a = (n : WithBot ℕ∞) := by
  cases a with
  | bot =>
    rw [WithBot.bot_add] at h
    exact absurd h.symm (WithBot.natCast_ne_bot (n + 1))
  | coe b =>
    cases b with
    | top =>
      exfalso
      have h2 : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      have h3 : (⊤ + 1 : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := WithBot.coe_injective h2
      have h4 : ((n : ℕ∞) + 1) ≠ ⊤ := by exact_mod_cast ENat.natCast_ne_top (n + 1)
      exact h4 h3.symm
    | coe b =>
      have h1 : ((b + 1 : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have h2 : b + 1 = n + 1 := by exact_mod_cast h1
      have h3 : b = n := by omega
      subst h3
      rfl

theorem ringKrullDim_coneRing_rat {κ : Type} [Fintype κ] (x : Ix κ → Ω) (D : ℕ)
    (h : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) :
    ringKrullDim (coneMap ℚ x).range = ((D + 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, ⟨hprime, -, -⟩, hH, hdim⟩ := h
  have : (coordIdeal ℤ x).IsPrime := hprime
  have hch : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x → m = 0 := by
    intro m hm
    have hm' : m ∈ (coordIdeal ℤ x).comap (C : ℤ →+* MvPolynomial (Ix κ) ℤ) := hm
    have hm'' : m ∈ (⊥ : Ideal ℤ) := hH ▸ hm'
    exact (Ideal.mem_bot).mp hm''
  obtain ⟨-, -, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec (coordIdeal ℤ x) hch
  rw [Fintype.card_unit] at hdim
  rw [hdim] at hd
  have e1 := ((Ideal.quotEquivOfEq (ker_coneMap_rat x)).symm).trans
    (Ideal.quotientKerEquivRange (coneMap ℚ x)).toRingEquiv
  rw [← ringKrullDim_eq_of_ringEquiv e1]
  exact withBot_eq_of_add_one hd

theorem ringKrullDim_mvPolynomial_rat (r : ℕ) :
    ringKrullDim (MvPolynomial (Fin r) ℚ) = (r : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

theorem intOver_coneMap (x : J → Ω) {r : ℕ} (w : Fin r → Polynomial Ω)
    (hint : ∀ t, IntOver ℚ w (Polynomial.C (x t) * Polynomial.X)) (q : MvPolynomial J ℚ) :
    IntOver ℚ w (coneMap ℚ x q) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    have h1 : coneMap ℚ x (C a) = (aeval w : MvPolynomial (Fin r) ℚ →ₐ[ℚ] Polynomial Ω) (C a) := by
      simp [coneMap]
    rw [h1]
    exact RingHom.isIntegralElem_map _
  | add p q hp hq =>
    rw [map_add]
    exact RingHom.IsIntegralElem.add _ hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine RingHom.IsIntegralElem.mul _ hp ?_
    have h1 : coneMap ℚ x (X i) = Polynomial.C (x i) * Polynomial.X := by simp [coneMap]
    rw [h1]
    exact hint i

theorem rank_eq {κ : Type} [Fintype κ] (x : Ix κ → Ω) (D : ℕ)
    (h : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) {r : ℕ} (L : Fin r → Ix κ → ℚ)
    (hind : AlgebraicIndependent ℚ (forms (fun j => Polynomial.C (x j) * Polynomial.X) L))
    (hint : ∀ t, IntOver ℚ (forms (fun j => Polynomial.C (x j) * Polynomial.X) L)
      (Polynomial.C (x t) * Polynomial.X)) :
    r = D + 1 := by
  set w := forms (fun j => Polynomial.C (x j) * Polynomial.X) L with hw
  let ψ : MvPolynomial (Fin r) ℚ →ₐ[ℚ] MvPolynomial (Ix κ) ℚ := aeval fun k => ∑ t, L k t • X t
  let g : MvPolynomial (Fin r) ℚ →ₐ[ℚ] (coneMap ℚ x).range := (coneMap ℚ x).rangeRestrict.comp ψ
  have hval : ((coneMap ℚ x).range.val).comp g = aeval w := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [aeval_X]
    change coneMap ℚ x (ψ (X k)) = w k
    simp [ψ, hw, forms, coneMap]
  have hvalx : ∀ p, ((g p : (coneMap ℚ x).range) : Polynomial Ω) = aeval w p := fun p => by
    rw [← hval]
    rfl
  have hinj : Function.Injective g := by
    intro a b hab
    exact hind (by rw [← hvalx, ← hvalx, hab])
  have hcomp : ((coneMap ℚ x).range.val : (coneMap ℚ x).range →+* Polynomial Ω).comp
      (g : MvPolynomial (Fin r) ℚ →+* (coneMap ℚ x).range) =
      (aeval w : MvPolynomial (Fin r) ℚ →ₐ[ℚ] Polynomial Ω) :=
    RingHom.ext fun p => hvalx p
  have hintg : (g : MvPolynomial (Fin r) ℚ →+* (coneMap ℚ x).range).IsIntegral := by
    intro s
    obtain ⟨q, hq⟩ := s.2
    apply isIntegralElem_of_comp (g : MvPolynomial (Fin r) ℚ →+* (coneMap ℚ x).range)
      ((coneMap ℚ x).range.val : (coneMap ℚ x).range →+* Polynomial Ω) Subtype.val_injective
    rw [hcomp]
    change IntOver ℚ w (s : Polynomial Ω)
    rw [← hq]
    exact intOver_coneMap x w hint q
  have hdim := ringKrullDim_coneRing_rat x D h
  have h1 : (r : WithBot ℕ∞) ≤ ringKrullDim (coneMap ℚ x).range :=
    le_ringKrullDim_of_isIntegral _ hintg hinj r (ringKrullDim_mvPolynomial_rat r).ge
  have h2 : ringKrullDim (coneMap ℚ x).range ≤ (r : WithBot ℕ∞) := by
    let _ := (g : MvPolynomial (Fin r) ℚ →+* (coneMap ℚ x).range).toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin r) ℚ) (coneMap ℚ x).range := ⟨hintg⟩
    rw [← ringKrullDim_mvPolynomial_rat r]
    exact ringKrullDim_le_of_isIntegral'
  rw [hdim] at h1 h2
  have h3 : ((D + 1 : ℕ) : WithBot ℕ∞) = (r : WithBot ℕ∞) := le_antisymm h2 h1
  exact_mod_cast h3.symm

theorem exists_completion [Fintype J] {n : ℕ} (L : Fin n → J → ℚ) (hL : LinearIndependent ℚ L) :
    ∃ (B : Matrix J J ℚ) (e : Fin n → J), Function.Injective e ∧ IsInvMat B ∧ ∀ k, B (e k) = L k := by
  classical
  have hs := hL.linearIndepOn_id
  let b := Module.Basis.extend hs
  let σ := b.indexEquiv (Pi.basisFun ℚ J)
  have hsub : ∀ k, L k ∈ hs.extend (Set.subset_univ _) :=
    fun k => Module.Basis.subset_extend hs (Set.mem_range_self k)
  let B : Matrix J J ℚ := Matrix.of fun i => ((σ.symm i : hs.extend (Set.subset_univ _)) : J → ℚ)
  have hBrow : LinearIndependent ℚ (fun i => B i) := by
    have h1 := b.linearIndependent.comp σ.symm σ.symm.injective
    rw [Module.Basis.coe_extend] at h1
    exact h1
  have hdet : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det B).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hBrow)
  refine ⟨B, fun k => σ ⟨L k, hsub k⟩,
    fun a c hac => hL.injective (congrArg Subtype.val (σ.injective hac)),
    ⟨B⁻¹, fun v => ⟨?_, ?_⟩⟩, fun k => ?_⟩
  · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  · rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  · change ((σ.symm (σ ⟨L k, hsub k⟩) : hs.extend (Set.subset_univ _)) : J → ℚ) = L k
    rw [Equiv.symm_apply_apply]

end Cone

theorem proof : RatNoetherFrame.Statement := by
  intro D Ω _ _ κ _ x hx
  classical
  obtain ⟨r, L, hind, hint⟩ := exists_indep_normalization (k := ℚ) (R := Polynomial Ω)
    (algebraMap ℚ (Polynomial Ω)).injective (fun j : Ix κ => Polynomial.C (x j) * Polynomial.X)
  obtain rfl := rank_eq x D hx L hind hint
  set v : Ix κ → Polynomial Ω := fun j => Polynomial.C (x j) * Polynomial.X with hv
  have hlin : LinearIndependent ℚ L := by
    let φ : (Ix κ → ℚ) →ₗ[ℚ] Polynomial Ω :=
      { toFun := fun c => ∑ t, c t • v t
        map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
        map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }
    exact LinearIndependent.of_comp φ hind.linearIndependent
  obtain ⟨B, e, he, hB, hBe⟩ := exists_completion L hlin
  have hy : (fun k => Polynomial.C ((matAct B x ∘ e) k) * Polynomial.X) = forms v L := by
    funext k
    rw [forms, hv, sum_smul_cone]
    simp [matAct, hBe]
  refine ⟨B, e, hB, he, ?_, fun i => ?_⟩
  · rw [eq_bot_iff]
    intro p hp
    rw [Ideal.mem_bot]
    have hp0 : coneMap ℤ (matAct B x ∘ e) p = 0 := RingHom.mem_ker.mp hp
    have h2 := coneMap_map_int (matAct B x ∘ e) p
    rw [hp0, coneMap, hy] at h2
    have h3 : MvPolynomial.map (Int.castRingHom ℚ) p = 0 := hind (by rw [h2, map_zero])
    exact qmap_injective (by rw [qmap, h3, map_zero])
  · set A : MvPolynomial (Fin (D + 1)) ℚ →ₐ[ℚ] Polynomial Ω := aeval (forms v L) with hA
    have hS : coneRing ℚ (matAct B x ∘ e) = A.range := by
      rw [coneRing, coneMap, hy]
    rw [hS]
    have hvi : ∀ t, IsIntegral A.range (v t) := by
      intro t
      obtain ⟨p, hp, hpa⟩ := hint t
      refine ⟨p.map (A.rangeRestrict : MvPolynomial (Fin (D + 1)) ℚ →+* _), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hpa
    rw [show Polynomial.C (matAct B x i) * Polynomial.X = ∑ j, B i j • v j from
      (sum_smul_cone x (B i)).symm]
    refine IsIntegral.sum _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine IsIntegral.mul ?_ (hvi j)
    have hm : algebraMap ℚ (Polynomial Ω) (B i j) ∈ A.range :=
      Subalgebra.algebraMap_mem _ _
    exact isIntegral_algebraMap (R := A.range) (A := Polynomial Ω) (x := ⟨_, hm⟩)

end RatNoetherFrame

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
