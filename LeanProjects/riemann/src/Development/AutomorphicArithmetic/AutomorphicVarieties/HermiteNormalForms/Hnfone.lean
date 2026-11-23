import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Scinv
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Hnfeq

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.hnfone :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (I : ℕ), 0 < I →
    ∃ S : Finset (Matrix (Fin N) (Fin N) (𝓞 L)), S.card ≤ I ^ (dd L N * N) ∧ ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 → nrmDet A = I →
      ∃ g : Gm L N, (g : Matrix (Fin N) (Fin N) (𝓞 L)) * A ∈ S := by
  classical
  intro L _ _ N I hI
  have hr0 : (I : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hI.ne'
  have hcardQ : Nat.card (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) = I ^ Module.finrank ℚ L := by
    have h1 := Ideal.absNorm_span_singleton (I : 𝓞 L)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    rw [h1, ← map_natCast (algebraMap ℤ (𝓞 L)) I, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank]
    simp
  haveI : Finite (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) :=
    Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact pow_ne_zero _ hI.ne')
  letI : Fintype (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) := Fintype.ofFinite _
  have hB : ∀ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ nrmDet A = I →
      ∃ B, A * B = (I : 𝓞 L) • 1 ∧ B * A = (I : 𝓞 L) • 1 := by
    intro A hA
    obtain ⟨_, B, h1, h2⟩ := scinv L N A hA.1
    rw [hA.2] at h1 h2
    exact ⟨B, h1, h2⟩
  let key : Matrix (Fin N) (Fin N) (𝓞 L) → Matrix (Fin N) (Fin N) (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) :=
    fun A => if h : A.det ≠ 0 ∧ nrmDet A = I then
      (Classical.choose (hB A h)).map (Ideal.Quotient.mk _) else 0
  let rep : Matrix (Fin N) (Fin N) (𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) → Matrix (Fin N) (Fin N) (𝓞 L) :=
    fun k => if h : ∃ A, (A.det ≠ 0 ∧ nrmDet A = I) ∧ key A = k then Classical.choose h else 0
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ]
    change Fintype.card (Fin N → Fin N → 𝓞 L ⧸ Ideal.span {(I : 𝓞 L)}) = _
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcardQ,
      dd, ← pow_mul, ← pow_mul, mul_assoc]
  · intro A hdet hnrm
    have hA : A.det ≠ 0 ∧ nrmDet A = I := ⟨hdet, hnrm⟩
    have hex : ∃ A', (A'.det ≠ 0 ∧ nrmDet A' = I) ∧ key A' = key A := ⟨A, hA, rfl⟩
    have hrep : rep (key A) = Classical.choose hex := dif_pos hex
    obtain ⟨hA'P, hA'k⟩ := Classical.choose_spec hex
    obtain ⟨h1, h2⟩ := Classical.choose_spec (hB A hA)
    obtain ⟨h1', h2'⟩ := Classical.choose_spec (hB _ hA'P)
    have hkk : (Classical.choose (hB _ hA'P)).map (Ideal.Quotient.mk (Ideal.span {(I : 𝓞 L)})) =
        (Classical.choose (hB A hA)).map (Ideal.Quotient.mk _) := by
      have keyeq : ∀ (M : Matrix (Fin N) (Fin N) (𝓞 L)) (h : M.det ≠ 0 ∧ nrmDet M = I),
          key M = (Classical.choose (hB M h)).map (Ideal.Quotient.mk _) := fun M h => dif_pos h
      exact (keyeq _ hA'P).symm.trans (hA'k.trans (keyeq A hA))
    have hent : ∀ i j, ∃ x, Classical.choose (hB A hA) i j - Classical.choose (hB _ hA'P) i j =
        (I : 𝓞 L) * x := by
      intro i j
      have h := congrFun (congrFun hkk i) j
      simp only [Matrix.map_apply] at h
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      exact ⟨-c, by rw [mul_neg, ← hc, neg_sub]⟩
    choose X hX using hent
    obtain ⟨g, hg⟩ := hnfeq (𝓞 L) N (I : 𝓞 L) hr0 A (Classical.choose hex) _ _ (Matrix.of X)
      h1 h2 h1' h2' (by ext i j; simp [hX])
    refine ⟨g, ?_⟩
    rw [hg, Finset.mem_image]
    exact ⟨key A, Finset.mem_univ _, hrep⟩
