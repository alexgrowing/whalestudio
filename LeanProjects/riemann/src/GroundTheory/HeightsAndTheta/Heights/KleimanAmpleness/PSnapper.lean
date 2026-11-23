import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperDiffPolySt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperDevissageSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperHyperplaneSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSectionSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem eulerCharQuot_self {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubSystem k x E) : eulerCharQuot k F F = 0 := by
  unfold eulerCharQuot
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : ∀ I, Subsingleton (F.sub I ⧸ SubSystem.quotSub F F I) := fun I =>
    Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun y _ => y.2)
  have h2 : Subsingleton (Cech.Cochain (fun I => F.sub I ⧸ SubSystem.quotSub F F I) i) := by
    unfold Cech.Cochain; infer_instance
  have h3 : Subsingleton (SubSystem.quotH F F i) := by
    unfold SubSystem.quotH Cech.H
    infer_instance
  simp [Module.finrank_zero_of_subsingleton]

theorem subSystem_ext {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    {F G : SubSystem k x E} (h : ∀ I, F.sub I = G.sub I) : F = G := by
  obtain ⟨sF, mF⟩ := F
  obtain ⟨sG, mG⟩ := G
  have : sF = sG := funext h
  subst this
  rfl

theorem twist_idealSys_of_irrelevant (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) :
    (twistSys k x a).twist (idealSys x pp) = twistSys k x a := by
  refine subSystem_ext fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
    Submodule.subset_span ⟨X i, X i, 1, hpp i, X_mem_monos hi, isHomogeneous_X _ _,
      isHomogeneous_X _ _, by rw [aeval_X, div_self hxi]⟩
  have hle : (idealSys x pp).sub I ≤ 1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
    exact Submodule.mem_one.mpr ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine le_antisymm (Submodule.mul_le.mpr fun q hq y hy => ?_) fun y hy => by
    simpa using Submodule.mul_mem_mul h1 hy
  obtain ⟨q', rfl⟩ := Submodule.mem_one.mp (hle hq)
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ q' hy

theorem pieceChar_of_irrelevant (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) {t : ℕ}
    (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : pieceChar k pp a L n c = 0 := by
  unfold pieceChar
  rw [twist_idealSys_of_irrelevant pp hpp a]
  exact eulerCharQuot_self _

end Lemmas

section Dim

variable {R : Type*} [CommRing R]

theorem ringKrullDim_quotient_succ_le_of_lt {pp qq : Ideal R} [pp.IsPrime] (h : pp < qq) :
    ringKrullDim (R ⧸ qq) + 1 ≤ ringKrullDim (R ⧸ pp) := by
  obtain ⟨r, hrq, hrp⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk pp r ∈ nonZeroDivisors (R ⧸ pp) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  have hker : ∀ a ∈ Ideal.span {Ideal.Quotient.mk pp r}, Ideal.Quotient.factor h.le a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hrq, mul_zero]
  have := ringKrullDim_le_of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective _ hker (Ideal.Quotient.factor_surjective h.le))
  gcongr

end Dim

section Induction

variable {k : Type u} [Field k] {N : ℕ}

theorem one_le_ringKrullDim_of_relevant (pp : Ideal (Poly k N)) [pp.IsPrime]
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    1 ≤ ringKrullDim (Poly k N ⧸ pp) := by
  obtain ⟨i, hi⟩ := hrel
  have hle : pp ≤ RingHom.ker (constantCoeff : Poly k N →+* k) := by
    intro f hf
    rw [RingHom.mem_ker]
    by_contra h0
    have h1 := hh f hf 0
    rw [homogeneousComponent_zero] at h1
    have h0' : coeff 0 f ≠ 0 := by rwa [← constantCoeff_eq]
    have hu : IsUnit (C (coeff 0 f) : Poly k N) := (isUnit_iff_ne_zero.mpr h0').map C
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ h1 hu)
  have hlt : pp < RingHom.ker (constantCoeff : Poly k N →+* k) :=
    lt_of_le_of_ne hle fun h => hi (h ▸ by simp [RingHom.mem_ker])
  have hnt : Nontrivial (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) :=
    Ideal.Quotient.nontrivial_iff.mpr (RingHom.ker_ne_top _)
  calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
    _ ≤ ringKrullDim (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) + 1 :=
        by gcongr; exact ringKrullDim_nonneg_of_nontrivial
    _ ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_quotient_succ_le_of_lt hlt

theorem withBot_le_of_succ_le {d : WithBot ℕ∞} {D : ℕ} (h : d + 1 ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) :
    d ≤ (D : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    have h' : d + 1 ≤ (D : ℕ∞) + 1 := by exact_mod_cast h
    exact_mod_cast (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'

theorem isNumPolyLT_sum {t D r : ℕ} (g : Fin r → (Fin t → ℕ) → ℤ → ℚ) (h : ∀ m, IsNumPolyLT t D (g m)) :
    IsNumPolyLT t D (fun n c => ∑ m, g m n c) := by
  choose Q hQ hev using h
  refine ⟨∑ m, Q m, ?_, fun n c => by simp [hev, map_sum]⟩
  rcases Nat.eq_zero_or_pos D with hD | hD
  · left
    subst hD
    exact Finset.sum_eq_zero fun m _ => (hQ m).resolve_right (Nat.not_lt_zero _)
  · right
    refine lt_of_le_of_lt (totalDegree_finsetSum _ _) ?_
    rw [Finset.sup_lt_iff (by simpa using hD)]
    intro m _
    rcases hQ m with h0 | h0
    · rw [h0, totalDegree_zero]; exact hD
    · exact h0

theorem IsNumPolyLT.congr {t D : ℕ} {f g : (Fin t → ℕ) → ℤ → ℚ} (h : IsNumPolyLT t D f)
    (hfg : ∀ n c, f n c = g n c) : IsNumPolyLT t D g := by
  obtain ⟨Q, hQ, hev⟩ := h
  exact ⟨Q, hQ, fun n c => (hfg n c).symm.trans (hev n c)⟩

variable {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}

theorem pieceChar_isNumPolyLT (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) {t : ℕ} (L : Fin t → LineBundle k x) (D : ℕ) :
    ∀ (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
      primeOf (S := k) x ≤ pp → ringKrullDim (Poly k N ⧸ pp) ≤ (D : WithBot ℕ∞) →
      ∀ a : ℤ, IsNumPolyLT t D (fun n c => (pieceChar k pp a L n c : ℚ)) := by
  induction D with
  | zero =>
    intro pp hp hh _ hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have := (one_le_ringKrullDim_of_relevant pp hh hrel).trans hdim
      exact absurd this (by simp)
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩
  | succ D ih =>
    intro pp hp hh hle hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have key : ∀ (qq : Ideal (Poly k N)) (b : ℤ), qq.IsPrime →
          (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) → pp < qq →
          IsNumPolyLT t D (fun n c => (pieceChar k qq b L n c : ℚ)) := fun qq b hq hqh hlt =>
        ih qq hq hqh (hle.trans hlt.le)
          (withBot_le_of_succ_le ((ringKrullDim_quotient_succ_le_of_lt hlt).trans hdim)) b
      obtain ⟨i, hi⟩ := hrel
      obtain ⟨r, qq, b, hqq, heq⟩ := hH k Ω N x pp hp hh hle i hi a
      have h0 : IsNumPolyLT t D
          (fun n c => (pieceChar k pp a L n (c + 1) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        (isNumPolyLT_sum _ fun m => key (qq m) (b m) (hqq m).1 (hqq m).2.1
          (lt_of_le_of_ne (hqq m).2.2.1 fun h => hi (h ▸ (hqq m).2.2.2))).congr
          fun n c => by exact_mod_cast (heq t L n c).symm
      choose μ r' qq' b' hqq' heq' using fun j => hS k Ω N x pp hp hh hle ⟨i, hi⟩ t L j a
      have hj : ∀ j, IsNumPolyLT t D (fun n c =>
          (pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ j) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        fun j => (isNumPolyLT_sum _ fun m => key (qq' j m) (b' j m) (hqq' j m).1 (hqq' j m).2.1
          (hqq' j m).2.2).congr fun n c => by exact_mod_cast (heq' j n c).symm
      exact hP t D (fun n c => (pieceChar k pp a L n c : ℚ)) μ h0 hj
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩

end Induction

theorem Snapper.proof (hD : SnapperDevissage.Statement.{u, v, w}) (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) (hP : SnapperDiffPoly.Statement) : Snapper.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x e hZ E _ _ _ _ F hF t L
  obtain ⟨r, pp, a, hpp, heq⟩ := hD k Ω N x E F hF
  have hdim : ∀ m, ringKrullDim (Poly k N ⧸ pp m) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := fun m =>
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective (hpp m).2.2)).trans hZ.dim.le
  obtain ⟨Q, hQ, hev⟩ := isNumPolyLT_sum (fun m n c => (pieceChar k (pp m) (a m) L n c : ℚ))
    fun m => pieceChar_isNumPolyLT hH hS hP L (e + 1) (pp m) (hpp m).1 (hpp m).2.1 (hpp m).2.2 (hdim m) (a m)
  refine ⟨Q, ?_, fun n c => ?_⟩
  · rcases hQ with h0 | h0
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · omega
  · rw [heq t L n c, ← hev n c]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
