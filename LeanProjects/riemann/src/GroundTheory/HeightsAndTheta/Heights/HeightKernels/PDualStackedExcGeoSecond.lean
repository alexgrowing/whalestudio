import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLinear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial

noncomputable section

namespace StackedExceptionalSecondGeometric

variable {T : Type} [Fintype T] {k : Type} [Field k]

theorem comap_linPrime {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    (linPrime α M).comap (C : ℤ →+* MRing (stackedBlocks T)) = RingHom.ker (Int.castRingHom k) := by
  ext z
  rw [Ideal.mem_comap, linPrime, RingHom.mem_ker, RingHom.mem_ker, linPointMap, coe_eval₂Hom, eval₂_C, eq_intCast,
    ← map_intCast (C : k →+* MvPolynomial (Option (Fin n)) k), C_eq_zero, eq_intCast]

theorem charOf_linPrime {n : ℕ} (α : T → k) (M : T → Fin n → k) : charOf (linPrime α M) = ringChar k := by
  have hker : RingHom.ker (Int.castRingHom k) = Ideal.span {((ringChar k : ℕ) : ℤ)} := by
    ext z
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, eq_intCast, CharP.intCast_eq_zero_iff k (ringChar k)]
  have key : ∀ I : Ideal ℤ, I = Ideal.span {((ringChar k : ℕ) : ℤ)} →
      (Submodule.IsPrincipal.generator I).natAbs = ringChar k := fun I hI => by
    have h := Ideal.span_singleton_eq_span_singleton.mp ((Ideal.span_singleton_generator I).trans hI)
    rw [Int.associated_iff_natAbs] at h
    rw [h, Int.natAbs_natCast]
  exact key _ ((comap_linPrime α M).trans hker)

omit [Fintype T] in

theorem exists_alpha_ne {α : T → k} (hα : Submodule.span ℤ (Set.range α) = ⊤) : ∃ s, α s ≠ 0 := by
  by_contra h
  push Not at h
  have hle : Submodule.span ℤ (Set.range α) ≤ ⊥ := Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; simp [h t])
  rw [hα, top_le_iff] at hle
  exact one_ne_zero ((Submodule.mem_bot ℤ).mp (hle ▸ Submodule.mem_top : (1 : k) ∈ (⊥ : Submodule ℤ k)))

theorem isRelevant_linPrime {n : ℕ} {α : T → k} {M : T → Fin (n + 1) → k}
    (hα : Submodule.span ℤ (Set.range α) = ⊤) (hM : LinFormsIndep M) : IsRelevant (linPrime α M) := by
  rintro (⟨⟩ | ⟨⟩)
  · obtain ⟨s, hs⟩ := exists_alpha_ne hα
    refine ⟨s, fun h => hs ?_⟩
    have h1 := LinPrimeExample.linPointMap_first α M s
    rw [graphFirst] at h1
    rw [linPrime, RingHom.mem_ker, h1] at h
    have h2 := congrArg (MvPolynomial.eval fun _ => (1 : k)) h
    simpa using h2
  · have hw : (Pi.single 0 1 : Fin (n + 1) → k) ≠ 0 := fun h0 => by
      simpa using congrFun h0 0
    obtain ⟨t, ht⟩ : ∃ t, ∑ j, M t j * (Pi.single 0 1 : Fin (n + 1) → k) j ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (hM _ h)
    refine ⟨t, fun h => ht ?_⟩
    have h1 := LinPrimeExample.linPointMap_second α M t
    rw [graphSecond] at h1
    rw [linPrime, RingHom.mem_ker, h1] at h
    have h2 := congrArg
      (MvPolynomial.eval fun o : Option (Fin (n + 1)) => o.elim (0 : k) fun j => (Pi.single 0 1 : Fin (n + 1) → k) j) h
    simpa using h2

theorem degSecond_inl : degSecond (Sum.inl ()) = 0 := by
  rw [degSecond, pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact Sum.inr_ne_inl hu)]
  rfl

theorem length_mul_log [Finite k] :
    ((Module.length ℤ k).toNat : ℝ) * Real.log (ringChar k) = Real.log (Nat.card k) := by
  set p := ringChar k with hp
  have : CharP k p := ringChar.charP k
  have := Fact.mk (CharP.char_is_prime k p)
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have : Fintype k := Fintype.ofFinite k
  have hlen : Module.length ℤ k = Module.finrank (ZMod p) k := by
    rw [Module.length_eq_of_surjective (R := ZMod p) ZMod.intCast_surjective, Module.length_eq_finrank]
  rw [hlen, ENat.toNat_natCast, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card,
    Nat.cast_pow, Real.log_pow]

theorem geoNum_linPrime (hCut : LinPrimeCut.Statement) (hBase : LinPrimeBase.Statement) :
    ∀ (n : ℕ) (α : T → k) (M : T → Fin (n + 1) → k), Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
      geoNum n (linPrime α M) (fun _ => degSecond) = ((Module.length ℤ k).toNat : ℤ)
  | 0, α, M, hα, hM => by
    have hrel := isRelevant_linPrime hα hM
    rw [geoNum, dif_pos hrel]
    obtain ⟨e⟩ := hBase T k α M hα hM (fun κ => (hrel κ).choose) (fun κ => (hrel κ).choose_spec)
    rw [e.toAddEquiv.toIntLinearEquiv.length_eq]
  | n + 1, α, M, hα, hM => by
    have hrel : ∀ κ, ∃ j, (X ⟨κ, j⟩ : MRing (stackedBlocks T)) ∉ linPrime α M := isRelevant_linPrime hα hM
    rw [geoNum]
    unfold IsRelevant
    rw [dif_pos hrel, Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_unique]
    rw [show degSecond (Sum.inl default) = 0 from degSecond_inl, show degSecond (Sum.inr default) = 1 from degSecond_inr,
      zero_mul, zero_add, one_mul]
    obtain ⟨M', hM', hsupp, hmult⟩ := hCut T k n α M hα hM ((hrel (Sum.inr ())).choose)
      (hrel (Sum.inr ())).choose_spec
    have hsupp' : divSupp (linPrime α M) (X ⟨Sum.inr default, (hrel (Sum.inr default)).choose⟩) =
        {linPrime α M'} := hsupp
    rw [hsupp', finsum_mem_singleton]
    have hmult' : multAt (linPrime α M ⊔ Ideal.span {(X ⟨Sum.inr default, (hrel (Sum.inr default)).choose⟩ :
        MRing (stackedBlocks T))}) (linPrime α M') = 1 := hmult
    rw [hmult', Nat.cast_one, one_mul]
    exact geoNum_linPrime hCut hBase n α M' hα hM'

end StackedExceptionalSecondGeometric

open StackedExceptionalSecondGeometric in

theorem DualStackedExcGeoSecond.proof (hLin : DualStackedExcLinear.Statement) (hCut : LinPrimeCut.Statement)
    (hBase : LinPrimeBase.Statement) : DualStackedExcGeoSecond.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab E hE
  obtain ⟨k, _, _, α, M, hα, hM, rfl, hcard⟩ := hLin K i F F' T b b' a hi hlt hcov hab E hE
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, geoNum_linPrime hCut hBase n α M hα hM, charOf_linPrime, ← hcard,
    ← Nat.card_eq_fintype_card, ← length_mul_log]
  push_cast
  rfl

end

end GroundTheory.Heights₂.Heights
