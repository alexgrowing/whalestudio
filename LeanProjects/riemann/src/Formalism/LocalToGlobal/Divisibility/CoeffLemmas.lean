import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
import Formalism.LocalToGlobal.UnitaryNorms.PowValCast

open NumberField IntermediateField

noncomputable section

namespace Formalism.L2.DIV

open Formalism.L2.Host Formalism.DivisionValues

theorem sig0Conj : DistinguishedEmbeddingConjugation := by
  intro ι LL _ x
  show ι (CoF.val ι LL (star x)) = _
  rw [CoF.val_star, conjQb_spec]
  rfl

theorem conj_ne_of_sq_neg {w : ℂ} {r : ℝ} (hr : r < 0) (hw : w ^ 2 = (r : ℂ)) : starRingEnd ℂ w ≠ w := by
  intro h
  obtain ⟨t, rfl⟩ := Complex.conj_eq_iff_real.1 h
  have : t ^ 2 = r := by exact_mod_cast hw
  nlinarith [sq_nonneg t]

theorem exists_sqrt (m : ℤ) : ∃ x : Qb, x ∈ sqrts m := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (m : Qb) (n := 2) (by norm_num)
  exact ⟨x, hx⟩

theorem sqrts_sub (m : ℤ) : sqrts m ⊆ (sqQ m : Set Qb) := subset_adjoin ℚ _

theorem totComplex : TotComplex := by
  intro ι LL d hd hK
  refine ⟨fun v => ?_⟩
  rw [InfinitePlace.isComplex_iff]
  intro hreal
  obtain ⟨x, hx⟩ := exists_sqrt (-(d : ℤ))
  have hxL : x ∈ LL := hK (sqrts_sub _ hx)
  set y : CoF ι LL := CoF.mk ι LL x hxL with hy
  have hy2 : y ^ 2 = ((-(d : ℤ) : ℤ) : CoF ι LL) := by
    apply CoF.val_injective ι LL
    rw [map_pow, CoF.val_mk, map_intCast]
    exact hx
  have h2 : (v.embedding y) ^ 2 = ((-(d : ℝ) : ℝ) : ℂ) := by
    rw [← map_pow, hy2, map_intCast]; push_cast; ring
  have hneg : (-(d : ℝ)) < 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  exact conj_ne_of_sq_neg hneg h2 (RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hreal) y)

theorem isAlgebraicQb (LL : Fld) : Algebra.IsAlgebraic LL Qb := by
  have : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) LL

theorem exists_ext (ι : Qb →+* ℂ) (LL : Fld) (σ : CoF ι LL →+* ℂ) :
    ∃ τ : Qb →+* ℂ, ∀ x : CoF ι LL, τ (CoF.val ι LL x) = σ x := by
  have := isAlgebraicQb LL
  let f : LL →ₐ[ℚ] ℂ := RingHom.toRatAlgHom (R := LL) σ
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := LL) (M := ℂ) (E := Qb) f
  refine ⟨φ.toRingHom, fun x => ?_⟩
  exact DFunLike.congr_fun hφ x

theorem exists_aut (ι τ : Qb →+* ℂ) : ∃ σ : Qb ≃ₐ[ℚ] Qb, ∀ x, τ x = ι (σ x) := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (algC τ).trans (algC ι).symm) (fun r => by simp), fun x => ?_⟩
  have h : ((algC ι ((algC ι).symm (algC τ x)) : algebraicClosure ℚ ℂ) : ℂ) = τ x := by
    rw [RingEquiv.apply_symm_apply]; rfl
  exact h.symm

theorem cmQbIndep : CmQbIndep := by
  have key : ∀ ι ι' : Qb →+* ℂ, ∀ x ∈ cmQb ι, conjQb ι x = conjQb ι' x := by
    intro ι ι' x hx
    apply ι'.injective
    rw [conjQb_spec]
    exact hx ι'
  have le : ∀ ι ι' : Qb →+* ℂ, cmQb ι ≤ cmQb ι' := by
    intro ι ι' x hx τ
    rw [← key ι ι' x hx]
    exact hx τ
  exact fun ι ι' => ⟨le_antisymm (le ι ι') (le ι' ι), key ι ι'⟩

theorem conj_root (τ : Qb →+* ℂ) {N : ℕ} (hN : 0 < N) {z : Qb} (hz : z ∈ mus N) :
    starRingEnd ℂ (τ z) = τ z⁻¹ := by
  have h1 : (τ z) ^ N = 1 := by rw [← map_pow, show z ^ N = 1 from hz, map_one]
  rw [map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hN.ne')]

theorem cycLeCm : CycLeCm := by
  intro ι N hN
  rw [cycQ, adjoin_le_iff]
  intro z hz τ
  have hc : conjQb ι z = z⁻¹ := by
    apply ι.injective
    rw [conjQb_spec, conj_root ι hN hz]
  rw [hc, conj_root τ hN hz]

theorem conj_sqrt {w : ℂ} {r : ℝ} (hw : w ^ 2 = (r : ℂ)) :
    starRingEnd ℂ w = (if r < 0 then -1 else 1) * w := by
  have h2 : (starRingEnd ℂ w) ^ 2 = w ^ 2 := by rw [← map_pow, hw, Complex.conj_ofReal]
  split_ifs with hr
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exact absurd h (conj_ne_of_sq_neg hr hw)
    · rw [h]; ring
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · rw [h]; ring
    · have hre : w.re = 0 := by
        have := congrArg Complex.re h
        simp at this
        linarith
      have him : w.im = 0 := by
        have := congrArg Complex.re hw
        rw [sq, Complex.mul_re, hre, Complex.ofReal_re] at this
        have h0 : w.im * w.im ≤ 0 := by have := not_lt.1 hr; linarith
        nlinarith [mul_self_nonneg w.im]
      have hw0 : w = 0 := Complex.ext hre him
      rw [hw0]; simp

theorem sqLeCm : SqLeCm := by
  intro ι m
  rw [sqQ, adjoin_le_iff]
  intro x hx τ
  have hτ : ∀ τ : Qb →+* ℂ, (τ x) ^ 2 = ((m : ℝ) : ℂ) := by
    intro τ
    rw [← map_pow, show x ^ 2 = (m : Qb) from hx, map_intCast]; push_cast; rfl
  by_cases hm : (m : ℝ) < 0
  · have hc : conjQb ι x = -x := by
      apply ι.injective
      rw [conjQb_spec, conj_sqrt (hτ ι), if_pos hm, map_neg]; ring
    rw [hc, conj_sqrt (hτ τ), if_pos hm, map_neg]; ring
  · have hc : conjQb ι x = x := by
      apply ι.injective
      rw [conjQb_spec, conj_sqrt (hτ ι), if_neg hm]; ring
    rw [hc, conj_sqrt (hτ τ), if_neg hm]; ring

theorem tauStar : TauStar := by
  intro ι L LL _ h hL s x y hy
  apply CoF.val_injective ι LL
  rw [CoF.val_star, val_tauCo, val_tauCo]
  apply ι.injective
  rw [conjQb_spec]
  have h1 := hL x.2 (ι.comp (s.liftNormal Qb).toRingHom)
  have h2 : ∀ u : L, s.liftNormal Qb (u : Qb) = s u := fun u => AlgHom.liftNormal_commutes s Qb u
  have h3 : ι (s.liftNormal Qb (conjQb ι x)) = starRingEnd ℂ (ι (s.liftNormal Qb (x : Qb))) := h1
  rw [← hy, h2, h2] at h3
  exact h3.symm

theorem finite_pow_eq {n : ℕ} (hn : 0 < n) (a : Qb) : {z : Qb | z ^ n = a}.Finite := by
  classical
  refine (Polynomial.nthRoots n a).toFinset.finite_toSet.subset fun z hz => ?_
  simpa [Polynomial.mem_nthRoots hn] using hz

theorem isIntegralQb (x : Qb) : IsIntegral ℚ x := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral

theorem fin_adjoin {S : Set Qb} (hS : S.Finite) : FiniteDimensional ℚ (adjoin ℚ S) := by
  have : Finite S := hS
  exact finiteDimensional_adjoin fun x _ => isIntegralQb x

end Formalism.L2.DIV
