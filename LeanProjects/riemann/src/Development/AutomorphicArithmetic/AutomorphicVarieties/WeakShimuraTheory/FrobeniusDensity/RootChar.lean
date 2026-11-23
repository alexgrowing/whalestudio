import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.PrincZl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.DvrIntClosure
import Mathlib.NumberTheory.Padics.AddChar
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ReducedCoefficients
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

open Polynomial

private theorem rc_coef {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O :=
  _root_.UpperTheory.Reformulated.B.CoefficientRingContainingIntegers.rc_coef K

private theorem rc_root {κ : Type} [NormedField κ] [IsAlgClosed κ] (γ : κ) (hγ : ‖γ - 1‖ < 1) (n : ℕ) (hn : 0 < n) :
    ∃ b : κ, b ^ n = γ ∧ ‖b - 1‖ < 1 := by
  by_contra hc
  push Not at hc
  have hm : (X ^ n - C γ : κ[X]).Monic := monic_X_pow_sub_C γ hn.ne'
  have hs := (IsAlgClosed.splits (X ^ n - C γ : κ[X])).eq_prod_roots_of_monic hm
  have he := congrArg (fun p => ‖eval 1 p‖) hs
  simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C, eval_multiset_prod, Multiset.map_map] at he
  have h1 : 1 ≤ ‖(Multiset.map (eval 1 ∘ fun a => X - C a) (X ^ n - C γ : κ[X]).roots).prod‖ := by
    refine Multiset.prod_induction (fun x : κ => 1 ≤ ‖x‖) _ (fun a b ha hb => ?_) (by simp) ?_
    · rw [norm_mul]; exact one_le_mul_of_one_le_of_one_le ha hb
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
      have hb' : b ^ n = γ := by
        have := (mem_roots hm.ne_zero).1 hb
        simpa [sub_eq_zero] using this
      have := hc b hb'
      rw [norm_sub_rev] at this
      simpa using this
  rw [norm_sub_rev] at hγ
  linarith

private theorem rc_pow {κ : Type} [NormedField κ] [IsUltrametricDist κ] (b : κ) (hb : ‖b - 1‖ < 1) (k : ℕ) :
    ‖b ^ k - 1‖ ≤ ‖b - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : b ^ (k + 1) - 1 = (b ^ k - 1) * (b - 1) + ((b ^ k - 1) + (b - 1)) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih le_rfl)))
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ih.trans hb.le)

private theorem rc_char {l : ℕ} [Fact l.Prime] (b : PadicAlgCl l) (hb : ‖b - 1‖ < 1) :
    ∃ (κ : AddChar ℤ_[l] (PadicAlgCl l)) (c : Coef l), Continuous κ ∧ κ 1 = b ∧ ∀ x, κ x ∈ c.O ∧ ‖κ x - 1‖ < 1 := by
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] {b}
  haveI : FiniteDimensional ℚ_[l] K := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral b)
  obtain ⟨c, hc⟩ := rc_coef K
  haveI : CompleteSpace K := by
    have h : IsClosed (K.toSubmodule : Set (PadicAlgCl l)) := Submodule.closed_of_finiteDimensional _
    have h2 : IsComplete (K.toSubmodule : Set (PadicAlgCl l)) := Submodule.complete_of_finiteDimensional _
    exact h2.completeSpace_coe
  haveI : IsBoundedSMul ℤ_[l] K := by
    refine IsBoundedSMul.of_norm_smul_le fun r x => ?_
    show ‖((r • x : K) : PadicAlgCl l)‖ ≤ ‖r‖ * ‖(x : PadicAlgCl l)‖
    have : ((r • x : K) : PadicAlgCl l) = (r : ℚ_[l]) • (x : PadicAlgCl l) := rfl
    rw [this, norm_smul]
    rfl
  let b' : K := ⟨b, IntermediateField.mem_adjoin_simple_self _ b⟩
  have hb' : ‖b' - 1‖ < 1 := hb
  have ht := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hb'
  let κ₀ : AddChar ℤ_[l] K := PadicInt.addChar_of_value_at_one (b' - 1) ht
  have h0 : Continuous κ₀ := PadicInt.continuous_addChar_of_value_at_one ht
  have h1 : κ₀ 1 = b' := by
    rw [PadicInt.addChar_of_value_at_one_def]; ring
  let κ : AddChar ℤ_[l] (PadicAlgCl l) := (K.val : K →* PadicAlgCl l).compAddChar κ₀
  have hκ : ∀ x, κ x = (κ₀ x : PadicAlgCl l) := fun _ => rfl
  have hcont : Continuous κ := continuous_subtype_val.comp h0
  have hone : κ 1 = b := by rw [hκ, h1]
  have hle : ∀ x, ‖κ x - 1‖ ≤ ‖b - 1‖ := by
    intro x
    refine PadicInt.denseRange_natCast.induction_on x
      (isClosed_le (hcont.sub continuous_const).norm continuous_const) fun k => ?_
    rw [← nsmul_one, AddChar.map_nsmul_eq_pow, hone]
    exact rc_pow b hb k
  refine ⟨κ, c, hcont, hone, fun x => ⟨hc _ (κ₀ x).2 ?_, (hle x).trans_lt hb⟩⟩
  have : κ x = (κ x - 1) + 1 := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hle x).trans hb.le) (by simp))

private theorem rc_princ {l : ℕ} [Fact l.Prime] (u : ℤ_[l]ˣ) : u ∈ KStar.TotallyRealRoots.princ l 1 ↔ ‖(u : ℤ_[l]) - 1‖ < 1 := by
  rw [KStar.TotallyRealRoots.mem_princ, pow_one, PadicInt.norm_lt_one_iff_dvd]

private theorem rc_equiv {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) :
    Nonempty (KStar.TotallyRealRoots.princ l 1 ≃ₜ* Multiplicative ℤ_[l]) := by
  refine (princZl l (KStar.TotallyRealRoots.princ l 1) ?_ (by rw [qExp, if_neg hl]) ?_).1
  · apply Subgroup.isClosed_of_isOpen
    have : (KStar.TotallyRealRoots.princ l 1 : Set ℤ_[l]ˣ) = {u : ℤ_[l]ˣ | ‖(u : ℤ_[l]) - 1‖ < 1} := Set.ext rc_princ
    rw [this]
    exact isOpen_lt (Units.continuous_val.sub continuous_const).norm continuous_const
  · have hn : ‖(l : ℤ_[l])‖ < 1 := by rw [PadicInt.norm_lt_one_iff_dvd]
    have hu : IsUnit (1 - (l : ℤ_[l])) := (Units.oneSub _ hn).isUnit
    intro h
    have h1 : hu.unit ∈ KStar.TotallyRealRoots.princ l 1 := by
      rw [rc_princ]; simpa using hn
    rw [h, Subgroup.mem_bot] at h1
    have h2 := congrArg Units.val h1
    have h3 : (l : ℤ_[l]) = 0 := by simpa using h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h3)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.Tw.rootChar :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (π : Γ →* ℤ_[l]ˣ), Continuous π → (∀ s, ‖(π s : ℤ_[l]) - 1‖ < 1) → ∀ n : ℕ, 0 < n → ∃ (t : Γ →* Multiplicative ℤ_[l]) (β : Γ →* (PadicAlgCl l)ˣ) (c₁ : Coef l), Continuous t ∧ t.ker = π.ker ∧ t.ker ≤ β.ker ∧ Continuous β ∧ (∀ s, (β s : PadicAlgCl l) ∈ c₁.O ∧ ‖(β s : PadicAlgCl l) - 1‖ < 1) ∧ (∀ s, (β s : PadicAlgCl l) ^ n = algebraMap ℤ_[l] (PadicAlgCl l) (π s : ℤ_[l])) ∧ ∀ s s', π s * π s' = 1 → β s * β s' = 1 := by
  intro l _ hl Γ _ _ _ _ π hπ h1 n hn
  obtain ⟨e⟩ := rc_equiv hl
  let π' : Γ →* KStar.TotallyRealRoots.princ l 1 := π.codRestrict _ fun s => (rc_princ _).2 (h1 s)
  have hπ' : Continuous π' := hπ.subtype_mk _
  let t : Γ →* Multiplicative ℤ_[l] := (e.toMulEquiv : _ →* _).comp π'
  have ht : ∀ s, t s = e (π' s) := fun _ => rfl
  have htc : Continuous t := e.continuous.comp hπ'
  have hnorm : ∀ x : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) x‖ = ‖x‖ := fun x => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    rfl
  have hac : Continuous (algebraMap ℤ_[l] (PadicAlgCl l)) :=
    (AddMonoidHomClass.isometry_of_norm _ hnorm).continuous
  let κ₀ : AddChar ℤ_[l] (PadicAlgCl l) := AddChar.toMonoidHomEquiv.symm
    ((algebraMap ℤ_[l] (PadicAlgCl l) : ℤ_[l] →* _).comp ((Units.coeHom _).comp
      ((KStar.TotallyRealRoots.princ l 1).subtype.comp (e.toMulEquiv.symm : _ →* _))))
  have hκ₀ : ∀ x, κ₀ x = algebraMap ℤ_[l] (PadicAlgCl l) ((e.symm (Multiplicative.ofAdd x) : ℤ_[l]ˣ) : ℤ_[l]) :=
    fun _ => rfl
  have hc₀ : Continuous κ₀ :=
    hac.comp (Units.continuous_val.comp (continuous_subtype_val.comp (e.symm.continuous.comp continuous_ofAdd)))
  have hγ : ‖κ₀ 1 - 1‖ < 1 := by
    rw [hκ₀, ← map_one (algebraMap ℤ_[l] (PadicAlgCl l)), ← map_sub, hnorm]
    exact (rc_princ _).1 (e.symm _).2
  obtain ⟨b, hbn, hb⟩ := rc_root _ hγ n hn
  obtain ⟨κ, c, hκc, hκ1, hκ⟩ := rc_char b hb
  have heq : κ ^ n = κ₀ := by
    refine PadicInt.denseRange_natCast.addChar_eq_of_eval_one_eq ?_ hc₀ ?_
    · exact (hκc.pow n).congr fun x => (AddChar.pow_apply κ n x).symm
    · rw [AddChar.pow_apply, hκ1, hbn]
  let β : Γ →* (PadicAlgCl l)ˣ := (κ.toMonoidHom.comp t).toHomUnits
  have hβ : ∀ s, (β s : PadicAlgCl l) = κ (Multiplicative.toAdd (t s)) := fun _ => rfl
  have hβv : Continuous fun s => (β s : PadicAlgCl l) := hκc.comp (continuous_toAdd.comp htc)
  have hker : t.ker = π.ker := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ht, map_eq_one_iff e e.injective]
    exact Subtype.ext_iff
  have hle : t.ker ≤ β.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    ext
    rw [hβ, hs]
    simp
  refine ⟨t, β, c, htc, hker, hle, ?_, fun s => hκ _, fun s => ?_, fun s s' h => ?_⟩
  · refine Units.continuous_iff.2 ⟨hβv, ?_⟩
    exact (hβv.comp continuous_inv).congr fun s => by simp
  · rw [hβ, ← AddChar.pow_apply, heq, hκ₀, ofAdd_toAdd, ht, e.symm_apply_apply]
    rfl
  · rw [← map_mul] at h ⊢
    exact hle (hker ▸ h)
