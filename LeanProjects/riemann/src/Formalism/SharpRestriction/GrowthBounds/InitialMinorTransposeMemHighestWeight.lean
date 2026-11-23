import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DescendingProdEqFactorialChoose
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ExponentFactorialAddSingleOne
import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorLatticeScaling
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolynomialMemWeightSpaceIff
import Formalism.GrowthSums.FactorialBaseGrowth.Coarse
import Formalism.GrowthSums.FactorialBaseGrowth.Harmonic
import Formalism.GrowthSums.FactorialBaseGrowth.LogCoef
import Formalism.SharpRestriction.GrowthBounds.RootWeights.MahPadicGeOfDvd
import Formalism.SharpRestriction.GrowthBounds.RootWeights.BinomialExpansionCoeffZeroOfDeg
import Formalism.SharpRestriction.GrowthBounds.RootWeights.MemBoundedDegreeExponentsIff
import Formalism.SharpRestriction.GrowthBounds.CountingStatementReduction
import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FinalD
import Lemmata.MiscLemmasE.Imports

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.Joints.F6

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem c1 (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) :
    ∀ (S : Set ι) (a b : Fin n) (k : ℕ), a ≠ b →
        ((k.factorial : ℕ) : KK O) • divPow (KK O) LL S a b k = (glAct (KK O) LL S a b) ^ k := by
  intro S a b k hab
  rw [glAct_pow_eq_factorial_divPow LL S a b hab k, Nat.cast_smul_eq_nsmul]

theorem c2 (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) :
    ∀ (S : Set ι) (a b : Fin n) (F G : MvPolynomial (ι × Fin n) (KK O)),
        fock (glAct (KK O) LL S a b F) G = fock F (glAct (KK O) LL S b a G) := by
  intro S a b F G
  exact fock_form_contravariant LL S a b F G

theorem ellOf_le {K : Type} [Field K] [CharZero K] (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι)
    (d : ι → ℕ) : ellOf (glOps K n LL S) (Pol K n d) ≤ degIn d S := by
  have hwt : ∀ (mu : Fin n → ℤ), mu ∈ wtsOf (glOps K n LL S) (Pol K n d) →
      ∃ m : ι × Fin n →₀ ℕ, (∀ i, multideg m i = d i) ∧ wtS LL S m = mu := by
    intro mu hmu
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hmu
    obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.2 hx0
    refine ⟨m, ?_, weight_vector_monomial_weight LL S mu x hx.1 m hm⟩
    have h2 := (MvPolynomial.mem_restrictSupport_iff K).1 hx.2
    exact h2 (by simpa using hm)
  unfold ellOf
  apply csSup_le'
  rintro k ⟨mu, hmu, nu, hnu, a, b, hab, heq⟩
  obtain ⟨m, hm, rfl⟩ := hwt mu hmu
  obtain ⟨m', hm', rfl⟩ := hwt nu hnu
  have h1 := polynomial_weight_difference_le LL S d m m' hm hm' a a
  have h2 := congrFun heq a
  simp [rootW, hab] at h2
  omega

theorem c3 (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S0 : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (N : ℕ) (Ss : Fin N → Set ι) :
    ∀ (d : ι → ℕ) (i : Fin N), ellOf (glOps (KK O) n LL (Ss i)) (Pol (KK O) n d) ≤ degIn d (Ss i) := by
  intro d i
  have := dvr_fraction_field_char_zero hG.prime S0
  exact ellOf_le n ι LL (Ss i) d

theorem c8 (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S0 : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] (LL : Letters ι) (N : ℕ) (Ss : Fin N → Set ι) :
    ∀ (T : Finset (Fin N → Fin n → ℤ)) (d : ι → ℕ) (i : Fin N),
          (∀ t ∈ T, ellWt (t i) ≤ degIn d (Ss i)) →
          ((T.sup fun t =>
              N0 n * deF p n (ellOf (glOps (KK O) n LL (Ss i)) (Pol (KK O) n d) + ellWt (t i)) : ℕ) : ℝ) ≤
            (N0 n : ℝ) * Real.logb p (2 * (degIn d (Ss i) : ℝ) + n) := by
  intro T d i hT
  have hp1 : 1 < p := hG.prime.one_lt
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have h3 := c3 p n' O S0 hG n ι LL N Ss d i
  have hle : (T.sup fun t =>
      N0 n * deF p n (ellOf (glOps (KK O) n LL (Ss i)) (Pol (KK O) n d) + ellWt (t i))) ≤
      N0 n * Nat.log p (2 * degIn d (Ss i) + n) := by
    apply Finset.sup_le
    intro t ht
    apply Nat.mul_le_mul_left
    unfold deF
    apply Nat.log_mono_right
    have := hT t ht
    omega
  have hlog : (Nat.log p (2 * degIn d (Ss i) + n) : ℝ) ≤ Real.logb p (2 * (degIn d (Ss i) : ℝ) + n) := by
    have h := Real.natLog_le_logb (2 * degIn d (Ss i) + n) p
    push_cast at h
    exact h
  calc ((T.sup fun t =>
              N0 n * deF p n (ellOf (glOps (KK O) n LL (Ss i)) (Pol (KK O) n d) + ellWt (t i)) : ℕ) : ℝ)
      ≤ ((N0 n * Nat.log p (2 * degIn d (Ss i) + n) : ℕ) : ℝ) := by exact_mod_cast hle
    _ = (N0 n : ℝ) * (Nat.log p (2 * degIn d (Ss i) + n) : ℝ) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)

end Formalism.MainNotions.G.Joints.F6

end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G
open Classical

namespace Formalism.MainNotions.G.Joints.F7

open Formalism.MainNotions.G.Joints Formalism.MainNotions.G.GLWeightTheory

section Abstract

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem decSys_congr {W : I → Submodule K V} {e e' : I → Module.End K V} (h : DecSys W e)
    (h1 : ∀ mu, ∀ x ∈ W mu, e' mu x = x) (h2 : ∀ mu nu, nu ≠ mu → ∀ x ∈ W nu, e' mu x = 0) : e' = e := by
  funext mu
  refine LinearMap.ext fun x => ?_
  obtain ⟨T, hT⟩ := h.cover x
  have a : e' mu x = ∑ nu ∈ T, e' mu (e nu x) := by
    conv_lhs => rw [hT]
    rw [map_sum]
  rw [a]
  by_cases hmu : mu ∈ T
  · rw [Finset.sum_eq_single_of_mem mu hmu fun nu _ hne => h2 mu nu hne _ (h.mem nu x)]
    exact h1 mu _ (h.mem mu x)
  · rw [h.zero_of_not_mem hT hmu]
    exact Finset.sum_eq_zero fun nu hnu => h2 mu nu (fun hh => hmu (hh ▸ hnu)) _ (h.mem nu x)

theorem joint_top : ∀ {N : ℕ} (W : Fin N → I → Submodule K V) (e : Fin N → I → Module.End K V)
    (_ : ∀ i, DecSys (W i) (e i))
    (_ : ∀ i j, i ≠ j → ∀ mu nu, ∀ x ∈ W j nu, e i mu x ∈ W j nu),
    (⨆ t : Fin N → I, ⨅ i, W i (t i)) = ⊤
  | 0, W, e, h, hc => by
    refine eq_top_iff.2 ?_
    refine le_trans ?_ (le_iSup _ (fun i => i.elim0))
    simp
  | N + 1, W, e, h, hc => by
    have ih := joint_top (fun i => W i.succ) (fun i => e i.succ) (fun i => h i.succ)
      (fun i j hij => hc i.succ j.succ (by simpa using hij))
    refine eq_top_iff.2 fun x hx0 => ?_
    clear hx0
    have hx : x ∈ (⨆ t : Fin N → I, ⨅ i, W i.succ (t i)) := by rw [ih]; trivial
    induction hx using Submodule.iSup_induction' with
    | mem t y hy =>
      obtain ⟨T, hT⟩ := (h 0).cover y
      rw [hT]
      refine Submodule.sum_mem _ fun mu _ => ?_
      refine Submodule.mem_iSup_of_mem (Fin.cons mu t) ?_
      rw [Submodule.mem_iInf]
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using (h 0).mem mu y
      · simp only [Fin.cons_succ]
        exact hc 0 j.succ (Fin.succ_ne_zero j).symm mu (t j) y ((Submodule.mem_iInf _).1 hy j)
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb

theorem list_fix (l : List (Module.End K V)) (x : V) (h : ∀ A ∈ l, A x = x) : l.prod x = x := by
  induction l with
  | nil => rfl
  | cons A l ih =>
    rw [List.prod_cons, Module.End.mul_apply, ih (fun B hB => h B (List.mem_cons_of_mem _ hB))]
    exact h A List.mem_cons_self

theorem list_kill (l : List (Module.End K V)) (x : V) (h : ∀ A ∈ l, A x = x ∨ A x = 0) :
    (l.prod x = x ∨ l.prod x = 0) ∧ ((∃ A ∈ l, A x = 0) → l.prod x = 0) := by
  induction l with
  | nil => exact ⟨Or.inl rfl, fun ⟨A, hA, _⟩ => absurd hA (List.not_mem_nil)⟩
  | cons A l ih =>
    obtain ⟨i1, i2⟩ := ih (fun B hB => h B (List.mem_cons_of_mem _ hB))
    have hA := h A List.mem_cons_self
    rw [List.prod_cons, Module.End.mul_apply]
    refine ⟨?_, ?_⟩
    · rcases i1 with i1 | i1
      · rw [i1]; exact hA
      · rw [i1, map_zero]; exact Or.inr rfl
    · rintro ⟨B, hB, hB0⟩
      rcases List.mem_cons.1 hB with rfl | hB'
      · rcases i1 with i1 | i1
        · rw [i1]; exact hB0
        · rw [i1, map_zero]
      · rw [i2 ⟨B, hB', hB0⟩, map_zero]

theorem proj_eq_sum {N : ℕ} (W : Fin N → I → Submodule K V) (e : Fin N → I → Module.End K V)
    (h : ∀ i, DecSys (W i) (e i))
    (hc : ∀ i j, i ≠ j → ∀ mu nu, ∀ x ∈ W j nu, e i mu x ∈ W j nu)
    (T : Finset (Fin N → I)) (E : Module.End K V)
    (h1 : ∀ t ∈ T, ∀ x ∈ ⨅ i, W i (t i), E x = x) (h0 : ∀ t ∉ T, ∀ x ∈ ⨅ i, W i (t i), E x = 0) :
    E = ∑ t ∈ T, (List.ofFn fun i => e i (t i)).prod := by
  refine LinearMap.ext fun x => ?_
  have hx : x ∈ (⨆ t : Fin N → I, ⨅ i, W i (t i)) := by rw [joint_top W e h hc]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem t y hy =>
    have hy' : ∀ i, y ∈ W i (t i) := (Submodule.mem_iInf _).1 hy
    have hsame : (List.ofFn fun i => e i (t i)).prod y = y := by
      refine list_fix _ y fun A hA => ?_
      obtain ⟨i, rfl⟩ := (List.mem_ofFn).1 hA
      exact (h i).id_on _ y (hy' i)
    have hdiff : ∀ t' : Fin N → I, t' ≠ t → (List.ofFn fun i => e i (t' i)).prod y = 0 := by
      intro t' hne
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
      refine (list_kill _ y fun A hA => ?_).2 ⟨e i (t' i), (List.mem_ofFn).2 ⟨i, rfl⟩, ?_⟩
      · obtain ⟨k, rfl⟩ := (List.mem_ofFn).1 hA
        by_cases hk : t' k = t k
        · left; rw [hk]; exact (h k).id_on _ y (hy' k)
        · right; exact (h k).zero_on _ _ (Ne.symm hk) y (hy' k)
      · exact (h i).zero_on _ _ (Ne.symm hi) y (hy' i)
    rw [LinearMap.sum_apply]
    by_cases ht : t ∈ T
    · rw [h1 t ht y hy, Finset.sum_eq_single_of_mem t ht fun t' _ hne => hdiff t' hne, hsame]
    · rw [h0 t ht y hy]
      exact (Finset.sum_eq_zero fun t' ht' => hdiff t' (fun hh => ht (hh ▸ ht'))).symm
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, ha, hb]

end Abstract

section Pol

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} [NeZero n] (LL : Letters ι)

theorem sys_of (D : Formalism.BasicNotions.D7) (S : Set ι) (e : (Fin n → ℤ) → Module.End K (MvPolynomial (ι × Fin n) K))
    (he : ∀ lam, IsIsoProj (glOps K n LL S) lam (e lam)) : DecSys (isoSub (glOps K n LL S)) e := by
  obtain ⟨e0, s⟩ := isoDecomp (glOps K n LL S) D (weight_condition_from_integral_form D) (isGLRep_glOps K ι LL n S)
  have : e = e0 := decSys_congr s (fun mu => (he mu).1) (fun mu nu hne => (he mu).2 nu hne)
  rw [this]; exact s

theorem big_preserves {S S' : Set ι} (hs : S ⊆ S') (a b : Fin n) (mu : Fin n → ℤ) :
    ∀ x ∈ isoSub (glOps K n LL S) mu, glOps K n LL S' a b x ∈ isoSub (glOps K n LL S) mu := by
  intro x hx
  rw [gl_operator_union_add LL S S' hs a b, LinearMap.add_apply]
  refine Submodule.add_mem _ (isoSub_stab _ mu a b x hx) ?_
  refine isoSub_map_of_comm (glOps K n LL S) (glOps K n LL (S' \ S) a b) (fun c d y => ?_) mu x hx
  have h := congrArg (fun f : Module.End K (MvPolynomial (ι × Fin n) K) => f y)
    (disjoint_letters_commute (K := K) LL (S' \ S) S Set.disjoint_sdiff_left a b c d)
  simpa only [Module.End.mul_apply] using h

theorem comm_big (D : Formalism.BasicNotions.D7) {S S' : Set ι} (hs : S ⊆ S')
    (e : (Fin n → ℤ) → Module.End K (MvPolynomial (ι × Fin n) K))
    (he : ∀ lam, IsIsoProj (glOps K n LL S) lam (e lam)) (lam : Fin n → ℤ) (a b : Fin n)
    (x : MvPolynomial (ι × Fin n) K) :
    glOps K n LL S' a b (e lam x) = e lam (glOps K n LL S' a b x) :=
  (sys_of LL D S e he).comm_of_preserve (glOps K n LL S' a b) (fun mu => big_preserves LL hs a b mu) lam x

theorem cross_preserve (D : Formalism.BasicNotions.D7) {N : ℕ} (Ss : Fin N → Set ι) (hmono : Monotone Ss)
    (ee : Fin N → (Fin n → ℤ) → Module.End K (MvPolynomial (ι × Fin n) K))
    (hee : ∀ i lam, IsIsoProj (glOps K n LL (Ss i)) lam (ee i lam)) :
    ∀ i j, i ≠ j → ∀ mu nu, ∀ x ∈ isoSub (glOps K n LL (Ss j)) nu, ee i mu x ∈ isoSub (glOps K n LL (Ss j)) nu := by
  have key : ∀ i j, i < j → ∀ mu nu, ∀ x ∈ isoSub (glOps K n LL (Ss j)) nu,
      ee i mu x ∈ isoSub (glOps K n LL (Ss j)) nu := by
    intro i j hij mu nu x hx
    exact isoSub_map_of_comm (glOps K n LL (Ss j)) (ee i mu)
      (fun a b y => (comm_big LL D (hmono hij.le) (ee i) (hee i) mu a b y).symm) nu x hx
  intro i j hij mu nu x hx
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h mu nu x hx
  · have hc := (sys_of LL D (Ss i) (ee i) (hee i)).comm_of_preserve (ee j nu) (fun mu' => key j i h nu mu') mu x
    rw [(hee j nu).1 x hx] at hc
    rw [← hc]
    exact (sys_of LL D (Ss j) (ee j) (hee j)).mem nu _

theorem ellWt_le (D : Formalism.BasicNotions.D7) (S : Set ι) (e : (Fin n → ℤ) → Module.End K (MvPolynomial (ι × Fin n) K))
    (he : ∀ lam, IsIsoProj (glOps K n LL S) lam (e lam)) (d : ι → ℕ) (lam : Fin n → ℤ)
    (h : ∃ F ∈ Pol K n d, e lam F ≠ 0) : ellWt lam ≤ degIn d S := by
  obtain ⟨F, hF, hne⟩ := h
  have sys := sys_of LL D S e he
  have hy1 : e lam F ∈ Pol K n d := e_mem_Pol LL S sys d lam F hF
  have hy2 : e lam F ∈ isoSub (glOps K n LL S) lam := sys.mem lam F
  have hcomm : ∀ a b x, polProj K d (glOps K n LL S a b x) = glOps K n LL S a b (polProj K d x) :=
    fun a b x => polProj_glAct d LL S a b x

  have hex : ∃ v, IsHWV (glOps K n LL S) lam v ∧ polProj K d v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hz : ∀ x ∈ isoSub (glOps K n LL S) lam, polProj K d x = 0 := by
      intro x hx
      unfold isoSub at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨u, hu, v, hv, rfl⟩ := hy
        rw [umon_comm _ (polProj K d) hcomm u hu v, hcon v hv, map_zero]
      | zero => rw [map_zero]
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [map_smul, hy, smul_zero]
    exact hne (by rw [← polProj_of_mem d _ hy1]; exact hz _ hy2)
  obtain ⟨v, hv, hw0⟩ := hex
  have hwP : polProj K d v ∈ Pol K n d := polProj_mem d v
  have hwW : polProj K d v ∈ weightSp (glOps K n LL S) lam := by
    have hw := hv.2.1
    unfold weightSp at hw ⊢
    rw [Submodule.mem_iInf] at hw ⊢
    intro a
    have := hw a
    rw [LinearMap.mem_ker] at this ⊢
    have h2 : (glOps K n LL S a a - (lam a : K) • (1 : Module.End K (MvPolynomial (ι × Fin n) K))) (polProj K d v) =
        polProj K d ((glOps K n LL S a a - (lam a : K) • (1 : Module.End K (MvPolynomial (ι × Fin n) K))) v) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hcomm]
    rw [h2, this, map_zero]
  obtain ⟨m, hm⟩ : ∃ m, m ∈ (polProj K d v).support := by
    by_contra hcon
    push Not at hcon
    exact hw0 (MvPolynomial.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem hcon))
  have hwt : wtS LL S m = lam := weight_vector_monomial_weight LL S lam _ hwW m hm
  have hdeg : ∀ i, multideg m i = d i := by
    have := (MvPolynomial.mem_restrictSupport_iff K).1 hwP
    exact this (by simpa using hm)
  have hfin := polynomial_weight_difference_le LL S d m m hdeg hdeg 0 (lastIdx n)
  rw [hwt] at hfin
  unfold ellWt
  omega

end Pol

section Clauses

variable (D : Formalism.BasicNotions.D7) (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (S0 : UniformizedDVR p O) (hG : AdmissibleDVR p n' O) (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] (LL : Letters ι) (N : ℕ)
  (Ss : Fin N → Set ι) (hmono : Monotone Ss)
  (ee : Fin N → (Fin n → ℤ) → Module.End (KK O) (MvPolynomial (ι × Fin n) (KK O)))
  (hee : ∀ i lam, IsIsoProj (glOps (KK O) n LL (Ss i)) lam (ee i lam))

include D S0 hG hmono hee

theorem clause4 : ∀ i j : Fin N, i < j → ∀ lam a b,
    ee i lam * glAct (KK O) LL (Ss j) a b = glAct (KK O) LL (Ss j) a b * ee i lam := by
  have := dvr_fraction_field_char_zero hG.prime S0
  intro i j hij lam a b
  refine LinearMap.ext fun x => ?_
  exact (comm_big LL D (hmono hij.le) (ee i) (hee i) lam a b x).symm

theorem clause5 : ∀ (T : Finset (Fin N → Fin n → ℤ)) (e : Module.End (KK O) (MvPolynomial (ι × Fin n) (KK O))),
    (∀ t ∈ T, ∀ x ∈ Formalism.MainNotions.tableLineDegreeFive.jointComp (O := O) n LL Ss t, e x = x) →
    (∀ t ∉ T, ∀ x ∈ Formalism.MainNotions.tableLineDegreeFive.jointComp (O := O) n LL Ss t, e x = 0) →
    e = ∑ t ∈ T, (List.ofFn fun i => ee i (t i)).prod := by
  have := dvr_fraction_field_char_zero hG.prime S0
  intro T e h1 h0
  exact proj_eq_sum (fun i => isoSub (glOps (KK O) n LL (Ss i))) ee
    (fun i => sys_of LL D (Ss i) (ee i) (hee i)) (cross_preserve LL D Ss hmono ee hee) T e h1 h0

theorem clause6 : ∀ (d : ι → ℕ) (i : Fin N) (lam : Fin n → ℤ), (∃ F ∈ Pol (KK O) n d, ee i lam F ≠ 0) →
    ellWt lam ≤ degIn d (Ss i) := by
  have := dvr_fraction_field_char_zero hG.prime S0
  intro d i lam h
  exact ellWt_le LL D (Ss i) (ee i) (hee i) d lam h

end Clauses

end Formalism.MainNotions.G.Joints.F7

end

section

open Filter Topology Finset

namespace Formalism.MainNotions.G.Joints.F1

variable (p : ℕ) [Fact p.Prime]

noncomputable def L (u : ℚ_[p]) : ℚ_[p] := ∑' k : ℕ, (-1 : ℚ_[p]) ^ k * u ^ (k + 1) / ((k : ℚ_[p]) + 1)

lemma inv_norm_le (n : ℕ) (hn : n ≠ 0) : ‖(n : ℚ_[p])‖⁻¹ ≤ (n : ℝ) := by
  have h0 : (n : ℚ_[p]) ≠ 0 := by exact_mod_cast hn
  rw [Padic.norm_eq_zpow_neg_valuation h0, Padic.valuation_natCast, zpow_neg, inv_inv, zpow_natCast]
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd

lemma choose_tendsto (n : ℕ → ℕ) (hn : Tendsto (fun m => ((n m : ℚ_[p]) + 1)) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun m => ((n m).choose k : ℚ_[p])) atTop (𝓝 ((-1) ^ k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : ∀ m, ((n m).choose (k + 1) : ℚ_[p]) =
        ((n m : ℚ_[p]) + 1) * ((n m).choose k : ℚ_[p]) / ((k : ℚ_[p]) + 1) - ((n m).choose k : ℚ_[p]) := by
      intro m
      have hk : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have e1' : ((n m : ℚ_[p]) + 1) * ((n m).choose k : ℚ_[p]) =
          ((n m + 1).choose (k + 1) : ℚ_[p]) * ((k : ℚ_[p]) + 1) := by
        exact_mod_cast Nat.add_one_mul_choose_eq (n m) k
      have e2' : ((n m + 1).choose (k + 1) : ℚ_[p]) =
          ((n m).choose k : ℚ_[p]) + ((n m).choose (k + 1) : ℚ_[p]) := by
        exact_mod_cast Nat.choose_succ_succ (n m) k
      rw [e1', mul_div_assoc, div_self hk, mul_one, e2']; ring
    have h2 := ((hn.mul ih).div_const ((k : ℚ_[p]) + 1)).sub ih
    simp only [zero_mul, zero_div, zero_sub] at h2
    rw [pow_succ, mul_neg_one]
    exact h2.congr (fun m => (h1 m).symm)

lemma binom_id (u : ℚ_[p]) (n : ℕ) :
    ((1 + u) ^ (n + 1) - 1) / ((n : ℚ_[p]) + 1) =
      ∑' k : ℕ, (n.choose k : ℚ_[p]) * u ^ (k + 1) / ((k : ℚ_[p]) + 1) := by
  have hn : ((n : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [tsum_eq_sum (s := range (n + 1))]
  · rw [add_comm 1 u, add_pow, sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
    rw [sum_div]
    refine sum_congr rfl fun k _ => ?_
    have hk : ((k : ℚ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have e1' : ((n : ℚ_[p]) + 1) * (n.choose k : ℚ_[p]) =
        ((n + 1).choose (k + 1) : ℚ_[p]) * ((k : ℚ_[p]) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    rw [div_eq_div_iff hn hk]
    linear_combination (-(u ^ (k + 1))) * e1'
  · intro k hk
    have : n < k := by simpa using hk
    rw [Nat.choose_eq_zero_of_lt this]; simp

lemma tendsto_L (u : ℚ_[p]) (hu : ‖u‖ < 1) (n : ℕ → ℕ)
    (hn : Tendsto (fun m => ((n m : ℚ_[p]) + 1)) atTop (𝓝 0)) :
    Tendsto (fun m => ((1 + u) ^ (n m + 1) - 1) / ((n m : ℚ_[p]) + 1)) atTop (𝓝 (L p u)) := by
  simp only [binom_id]
  unfold L
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun k => ((k + 1 : ℕ) : ℝ) ^ 1 * ‖u‖ ^ (k + 1)) ?_ ?_ ?_
  · have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := ‖u‖) (by simpa using hu)
    exact (summable_nat_add_iff 1).2 this
  · intro k
    exact ((choose_tendsto p n hn k).mul_const _).div_const _
  · refine Eventually.of_forall fun m k => ?_
    rw [norm_div, norm_mul, norm_pow, div_eq_mul_inv]
    have h1 : ‖((n m).choose k : ℚ_[p])‖ ≤ 1 := by
      simpa using Padic.norm_int_le_one (p := p) ((n m).choose k : ℤ)
    have h2 : ‖(k : ℚ_[p]) + 1‖⁻¹ ≤ ((k + 1 : ℕ) : ℝ) := by
      have := inv_norm_le p (k + 1) (Nat.succ_ne_zero k)
      simpa using this
    calc _ ≤ 1 * ‖u‖ ^ (k + 1) * ((k + 1 : ℕ) : ℝ) := by gcongr
      _ = _ := by ring

lemma tendsto_p_pow : Tendsto (fun m : ℕ => (p : ℚ_[p]) ^ m) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one

lemma tendsto_quot (x : ℚ_[p]) (hx : ‖x - 1‖ < 1) :
    Tendsto (fun m : ℕ => (x ^ (p ^ m) - 1) / ((p : ℚ_[p]) ^ m)) atTop (𝓝 (L p (x - 1))) := by
  have hq : ∀ m : ℕ, p ^ m - 1 + 1 = p ^ m := fun m =>
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
  have hc : ∀ m : ℕ, (((p ^ m - 1 : ℕ) : ℚ_[p]) + 1) = (p : ℚ_[p]) ^ m := fun m => by
    have := congrArg (fun j : ℕ => (j : ℚ_[p])) (hq m)
    simpa using this
  have h := tendsto_L p (x - 1) hx (fun m => p ^ m - 1) (by simp only [hc]; exact tendsto_p_pow p)
  simp only [hc, hq, add_sub_cancel] at h
  exact h

lemma norm_mul_sub_one (x y : ℚ_[p]) (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) : ‖x * y - 1‖ < 1 := by
  have hy1 : ‖y‖ ≤ 1 := by
    have : y = (y - 1) + 1 := by ring
    rw [this]
    exact (Padic.nonarchimedean _ _).trans (max_le hy.le (by simp))
  have e : x * y - 1 = (x - 1) * y + (y - 1) := by ring
  rw [e]
  refine (Padic.nonarchimedean _ _).trans_lt (max_lt ?_ hy)
  rw [norm_mul]
  calc ‖x - 1‖ * ‖y‖ ≤ ‖x - 1‖ * 1 := by gcongr
    _ < 1 := by simpa using hx

theorem L_mul (x y : ℚ_[p]) (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    L p (x * y - 1) = L p (x - 1) + L p (y - 1) := by
  have hxy := tendsto_quot p (x * y) (norm_mul_sub_one p x y hx hy)
  have h1 := tendsto_quot p x hx
  have h2 := tendsto_quot p y hy
  have h3 := (((tendsto_p_pow p).mul h1).mul h2).add (h1.add h2)
  simp only [zero_mul, zero_add] at h3
  refine tendsto_nhds_unique hxy (h3.congr fun m => ?_)
  have hp : (p : ℚ_[p]) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [mul_pow]
  field_simp
  ring

lemma plog_eq (x : ℚ_[p]) : Formalism.MainNotions.tableLineDegreeFive.plog p x = L p (x - 1) := rfl

theorem plog_mul (x y : ℚ_[p]) (hx : ‖x - 1‖ < 1) (hy : ‖y - 1‖ < 1) :
    Formalism.MainNotions.tableLineDegreeFive.plog p (x * y) = Formalism.MainNotions.tableLineDegreeFive.plog p x + Formalism.MainNotions.tableLineDegreeFive.plog p y := by
  simpa only [plog_eq] using L_mul p x y hx hy

lemma plog_one : Formalism.MainNotions.tableLineDegreeFive.plog p 1 = 0 := by
  simp [Formalism.MainNotions.tableLineDegreeFive.plog]

lemma norm_prod_sub_one {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p]) (h : ∀ i ∈ s, ‖f i - 1‖ < 1) :
    ‖∏ i ∈ s, f i - 1‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact norm_mul_sub_one p _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem plog_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p]) (h : ∀ i ∈ s, ‖f i - 1‖ < 1) :
    Formalism.MainNotions.tableLineDegreeFive.plog p (∏ i ∈ s, f i) = ∑ i ∈ s, Formalism.MainNotions.tableLineDegreeFive.plog p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [plog_one]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, ‖f i - 1‖ < 1 := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      plog_mul p _ _ (h a (Finset.mem_insert_self a s)) (norm_prod_sub_one p s f hs), ih hs]

end Formalism.MainNotions.G.Joints.F1

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.F2

open Formalism.MainNotions.G Formalism.MainNotions.tableLineDegreeFive Finset

theorem coarse_unit_product_prime_power (p : ℕ) [hp : Fact p.Prime] (t : ℕ) (n : ℕ) :
    cUnit (p ^ (t + 1)) n =
      ∏ i ∈ Finset.range n, ∏ y ∈ Finset.Ico 1 (p ^ (t + 1)), (1 + ((p ^ (t + 1) : ℕ) : ℚ) * i / y) :=
  Formalism.GrowthSums.blockFactorialQuotientProd (p ^ (t + 1)) n (Nat.one_le_pow _ _ hp.1.pos)

theorem inv_norm_nat_le (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : m ≠ 0) : ‖(m : ℚ_[p])‖⁻¹ ≤ (m : ℝ) := by
  have h0 : ((m : ℚ)) ≠ 0 := by exact_mod_cast hm
  have h1 : ‖(m : ℚ_[p])‖ = ((p : ℝ) ^ (padicValNat p m))⁻¹ := by
    rw [show (m : ℚ_[p]) = ((m : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm,
      padicNorm.eq_zpow_of_nonzero h0, padicValRat.of_nat, zpow_neg, zpow_natCast, Rat.cast_inv, Rat.cast_pow,
      Rat.cast_natCast]
  rw [h1, inv_inv]
  have : p ^ padicValNat p m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) pow_padicValNat_dvd
  exact_mod_cast this

theorem summable_log (p : ℕ) [hp : Fact p.Prime] (u : ℚ_[p]) (hu : ‖u‖ < 1) :
    Summable fun k : ℕ => (-1 : ℚ_[p]) ^ k * u ^ (k + 1) / ((k : ℚ_[p]) + 1) := by
  have hs : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 1 * ‖u‖ ^ (k + 1) :=
    (summable_nat_add_iff 1).2 (summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖u‖) (by simpa using hu))
  refine Summable.of_norm_bounded hs fun k => ?_
  have hk := inv_norm_nat_le p (k + 1) (Nat.succ_ne_zero k)
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul, pow_one, div_eq_mul_inv,
    mul_comm]
  have e : ((k : ℚ_[p]) + 1) = ((k + 1 : ℕ) : ℚ_[p]) := by push_cast; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hk (by positivity)

theorem norm_quot_lt (p : ℕ) [hp : Fact p.Prime] (t i y : ℕ) (h1 : 1 ≤ y) (h2 : y < p ^ (t + 1)) :
    ‖((p ^ (t + 1) : ℕ) : ℚ_[p]) * (i : ℚ_[p]) / (y : ℚ_[p])‖ < 1 := by
  have hy : ¬ ‖((y : ℤ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((t + 1 : ℕ) : ℤ)) := by
    rw [Padic.norm_int_le_pow_iff_dvd]
    intro h
    have h' : p ^ (t + 1) ∣ y := by exact_mod_cast h
    have := Nat.le_of_dvd (by omega) h'
    omega
  have hy' : (p : ℝ) ^ (-((t + 1 : ℕ) : ℤ)) < ‖(y : ℚ_[p])‖ := by
    have := not_le.1 hy
    simpa using this
  have hP : ‖((p ^ (t + 1) : ℕ) : ℚ_[p])‖ = (p : ℝ) ^ (-((t + 1 : ℕ) : ℤ)) := by
    rw [Nat.cast_pow, Padic.norm_p_pow]
  have hi : ‖(i : ℚ_[p])‖ ≤ 1 := by
    have := Padic.norm_int_le_one (p := p) (i : ℤ)
    simpa using this
  have hpos : 0 < ‖(y : ℚ_[p])‖ := lt_of_le_of_lt (by positivity) hy'
  rw [norm_div, norm_mul, div_lt_one hpos, hP]
  calc (p : ℝ) ^ (-((t + 1 : ℕ) : ℤ)) * ‖(i : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((t + 1 : ℕ) : ℤ)) * 1 :=
        mul_le_mul_of_nonneg_left hi (by positivity)
    _ < ‖(y : ℚ_[p])‖ := by rw [mul_one]; exact hy'

theorem plog_one_add (p : ℕ) [Fact p.Prime] (u : ℚ_[p]) :
    plog p (1 + u) = ∑' k : ℕ, (-1 : ℚ_[p]) ^ k * u ^ (k + 1) / ((k : ℚ_[p]) + 1) := by
  simp only [plog, add_sub_cancel_left]

theorem term_collect (P n s : ℕ) :
    ∑ x ∈ Finset.range n ×ˢ Finset.Ico 1 P, (-1 : ℚ) ^ s * ((P : ℚ) * (x.1 : ℚ) / (x.2 : ℚ)) ^ (s + 1) / ((s : ℚ) + 1) =
      (-1 : ℚ) ^ s * (P : ℚ) ^ (s + 1) * harm P (s + 1) / ((s : ℚ) + 1) * powSum (s + 1) n := by
  rw [Finset.sum_product, harm, powSum]
  have : ∀ i ∈ Finset.range n, ∑ y ∈ Finset.Ico 1 P,
      (-1 : ℚ) ^ s * ((P : ℚ) * (i : ℚ) / (y : ℚ)) ^ (s + 1) / ((s : ℚ) + 1) =
      ((-1 : ℚ) ^ s * (P : ℚ) ^ (s + 1) * (∑ y ∈ Finset.Ico 1 P, ((y : ℚ) ^ (s + 1))⁻¹) / ((s : ℚ) + 1)) *
        (i : ℚ) ^ (s + 1) := by
    intro i _
    rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [div_pow, mul_pow, div_eq_mul_inv ((P : ℚ) ^ (s + 1) * (i : ℚ) ^ (s + 1))]
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]

theorem padic_log_unit_factor_series (p : ℕ) [hp : Fact p.Prime]
    (hprod : ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℚ_[p]), (∀ i ∈ s, ‖f i - 1‖ < 1) →
      plog p (∏ i ∈ s, f i) = ∑ i ∈ s, plog p (f i))
    (t : ℕ) (n : ℕ) :
    plog p (cUnit (p ^ (t + 1)) n : ℚ_[p]) =
      ∑' s : ℕ, (((-1 : ℚ) ^ s * ((p ^ (t + 1) : ℕ) : ℚ) ^ (s + 1) * harm (p ^ (t + 1)) (s + 1) / ((s : ℚ) + 1) *
        powSum (s + 1) n : ℚ) : ℚ_[p]) := by
  set P : ℕ := p ^ (t + 1) with hPdef
  set S : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.Ico 1 P with hS
  let u : ℕ × ℕ → ℚ_[p] := fun x => (P : ℚ_[p]) * (x.1 : ℚ_[p]) / (x.2 : ℚ_[p])
  have hu : ∀ x ∈ S, ‖u x‖ < 1 := by
    intro x hx
    rw [hS, Finset.mem_product, Finset.mem_Ico] at hx
    exact norm_quot_lt p t x.1 x.2 hx.2.1 hx.2.2
  have hc : ((cUnit P n : ℚ) : ℚ_[p]) = ∏ x ∈ S, (1 + u x) := by
    rw [hPdef, coarse_unit_product_prime_power p t n, ← hPdef, hS, Finset.prod_product]
    push_cast
    rfl
  rw [hc, hprod S (fun x => 1 + u x) (fun x hx => by simpa using hu x hx)]
  simp only [plog_one_add]
  rw [← Summable.tsum_finsetSum (fun x hx => summable_log p (u x) (hu x hx))]
  refine tsum_congr fun s => ?_
  rw [← term_collect P n s]
  push_cast
  rfl

end Formalism.MainNotions.G.Joints.F2

end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.Joints.F3

open Formalism.MainNotions.tableLineDegreeFive

theorem harm_eq (P s : ℕ) : harm P s = ∑ y ∈ Ico 1 P, 1 / (y : ℚ) ^ s := by
  unfold harm
  exact Finset.sum_congr rfl fun y _ => (one_div _).symm

theorem padic_val_harmonic_lower_bound (p : ℕ) [hp : Fact p.Prime] (_h5 : 5 ≤ p) (t : ℕ) :
    ∀ s : ℕ, 1 ≤ s → (s : ℤ) ≤ padicValRat p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * harm (p ^ (t + 1)) s) := by
  intro s _
  rw [harm_eq]
  exact Formalism.GrowthSums.padicValHarmonicPowerSum p t s hp.out

theorem power_sum_polynomial_exists : ∀ s : ℕ, ∃ f : Polynomial ℚ, f.natDegree = s + 1 ∧ ∀ n : ℕ, f.eval (n : ℚ) = powSum s n := by
  intro s
  exact Formalism.GrowthSums.powerSumPolynomial s

theorem padic_val_harmonic_term_bound (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p) (t : ℕ) :
    ∀ s : ℕ, 1 ≤ s → ((s : ℝ) + 1) / 4 ≤
      (padicValRat p ((-1 : ℚ) ^ (s - 1) * ((p ^ (t + 1) : ℕ) : ℚ) ^ s * harm (p ^ (t + 1)) s / s) : ℝ)
        - 1 / ((p : ℝ) - 1) := by
  intro s hs
  have h := Formalism.GrowthSums.padicValHarmonicPowerSumDivLowerBound p t s hp.out h5 hs
  rw [← harm_eq] at h
  rcases neg_one_pow_eq_or ℚ (s - 1) with h1 | h1
  · rw [h1, one_mul]; exact h
  · rw [h1]
    have : (-1 : ℚ) * ((p ^ (t + 1) : ℕ) : ℚ) ^ s * harm (p ^ (t + 1)) s / s
        = -(((p ^ (t + 1) : ℕ) : ℚ) ^ s * harm (p ^ (t + 1)) s / s) := by ring
    rw [this, padicValRat.neg]; exact h

end Formalism.MainNotions.G.Joints.F3

end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.Joints.F4

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.tableLineDegreeFive Formalism.MainNotions.G.GLWeightTheory

theorem mahlerCoef_eq_mah (f : ℕ → ℚ) (j : ℕ) : mahlerCoef f j = mah f j := by
  rw [mahlerCoef, mah, fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [zsmul_eq_mul]

theorem binomDecay_of_dec {p : ℕ} {f : ℕ → ℚ} (h : Dec p (1 / 4) 0 f) : BinomDecay p f := by
  intro j
  rw [mahlerCoef_eq_mah]
  have := h j
  rcases this with h0 | h1
  · exact Or.inl h0
  · refine Or.inr (le_trans (le_of_eq ?_) h1)
    ring

theorem binomial_decay_unit_factor (p : ℕ) [hp : Fact p.Prime] (_h5 : 5 ≤ p) (t : ℕ) :
    BinomDecay p (fun n => cUnit (p ^ (t + 1)) n) := by
  have := hDec_of hp.out (hdU_proved hp.out) ⟨t, 0, true, false⟩ (by simpa using Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero))
  rw [mah_unitFn_tf] at this
  exact binomDecay_of_dec this

theorem binomial_decay_unit_factor_inv (p : ℕ) [hp : Fact p.Prime] (_h5 : 5 ≤ p) (t : ℕ) :
    BinomDecay p (fun n => (cUnit (p ^ (t + 1)) n)⁻¹) := by
  have := hDec_of hp.out (hdU_proved hp.out) ⟨t, 0, true, true⟩ (by simpa using Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero))
  rw [mah_unitFn_tt] at this
  exact binomDecay_of_dec this

theorem binomial_decay_second_factor (p : ℕ) [hp : Fact p.Prime] (_h5 : 5 ≤ p) (t : ℕ) :
    ∀ rho : ℕ, rho < p ^ (t + 1) → BinomDecay p (fun n => dUnit (p ^ (t + 1)) n rho) ∧
      BinomDecay p (fun n => (dUnit (p ^ (t + 1)) n rho)⁻¹) := by
  intro rho hr
  have h1 := hDec_of hp.out (hdU_proved hp.out) ⟨t, rho, false, false⟩ hr
  have h2 := hDec_of hp.out (hdU_proved hp.out) ⟨t, rho, false, true⟩ hr
  rw [mah_unitFn_ff] at h1
  rw [mah_unitFn_ft] at h2
  exact ⟨binomDecay_of_dec h1, binomDecay_of_dec h2⟩

end Formalism.MainNotions.G.Joints.F4

end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.Joints.F5

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.tableLineDegreeFive

theorem mahlerCoef_eq_mah (f : ℕ → ℚ) (j : ℕ) : mahlerCoef f j = mah f j := by
  unfold mahlerCoef mah
  rw [fwdDiff_iter_eq_sum_shift]
  refine sum_congr rfl fun i _ => ?_
  simp [zsmul_eq_mul]

theorem dec_of_binomDecay {p : ℕ} {f : ℕ → ℚ} (h : BinomDecay p f) : Dec p (1 / 4) 0 f := by
  intro j
  have := h j
  rw [mahlerCoef_eq_mah] at this
  rcases this with h0 | h1
  · exact Or.inl h0
  · refine Or.inr ?_
    have e : (1 / 4 : ℝ) * (j : ℝ) + 0 = (j : ℝ) / 4 := by ring
    rw [e]; exact h1

theorem binomDecay_of_dec {p : ℕ} {f : ℕ → ℚ} (h : Dec p (1 / 4) 0 f) : BinomDecay p f := by
  intro j
  rw [mahlerCoef_eq_mah]
  rcases h j with h0 | h1
  · exact Or.inl h0
  · refine Or.inr ?_
    have e : (1 / 4 : ℝ) * (j : ℝ) + 0 = (j : ℝ) / 4 := by ring
    rw [← e]; exact h1

theorem binomial_basis_approximation (p : ℕ) [Fact p.Prime] :
    (∀ (K : ℕ) (f : Fin K → ℕ → ℚ), (∀ k, BinomDecay p (f k)) → ∀ c : ℕ,
      ∃ b : (Fin K → ℕ) → ℚ,
        (∀ J, b J ≠ 0 → ∑ k, J k ≤ 4 * c ∧ 0 ≤ padicValRat p (b J)) ∧
        ∀ n : Fin K → ℕ, VGe p (∏ k, f k (n k) -
          ∑ J ∈ Fintype.piFinset (fun _ : Fin K => Finset.range (4 * c + 1)),
            b J * ∏ k, ((n k).choose (J k) : ℚ)) c) := by
  classical
  intro K f hf c
  have hd : ∀ k, Dec p (1 / 4) 0 (f k) := fun k => dec_of_binomDecay (hf k)
  refine ⟨fun J => if ∑ k, J k ≤ 4 * c then ∏ k, mah (f k) (J k) else 0, ?_, ?_⟩
  · intro J hJ
    by_cases h : ∑ k, J k ≤ 4 * c
    · refine ⟨h, ?_⟩
      simp only [h, if_true] at hJ ⊢
      rcases asm_q_ge f hd J with h0 | h1
      · exact absurd h0 hJ
      · have h2 : (0 : ℝ) ≤ (padicValRat p (∏ k, mah (f k) (J k)) : ℝ) :=
          le_trans (by positivity) h1
        exact_mod_cast h2
    · simp [h] at hJ
  · intro n
    have h := asm_multi f hd c n
    have e : ∑ J ∈ Fintype.piFinset (fun _ : Fin K => Finset.range (4 * c + 1)),
        (if ∑ k, J k ≤ 4 * c then ∏ k, mah (f k) (J k) else 0) * ∏ k, ((n k).choose (J k) : ℚ) =
        ∑ j ∈ boundedDegreeExponents (Fin K) c, (∏ k, mah (f k) (j k)) * ∏ k, ((n k).choose (j k) : ℚ) := by
      have e0 : boundedDegreeExponents (Fin K) c =
          (Fintype.piFinset (fun _ : Fin K => Finset.range (4 * c + 1))).filter fun j => ∑ k, j k ≤ 4 * c := by
        ext J
        rw [mem_bounded_degree_exponents_iff]
        simp only [mem_filter, Fintype.mem_piFinset, mem_range]
        refine ⟨fun h => ⟨fun k => ?_, h⟩, fun h => h.2⟩
        have : J k ≤ ∑ k, J k := single_le_sum (f := J) (fun _ _ => Nat.zero_le _) (mem_univ k)
        omega
      rw [e0, sum_filter]
      refine sum_congr rfl fun J _ => ?_
      split_ifs <;> simp
    show VGe p (∏ k, f k (n k) - ∑ J ∈ Fintype.piFinset (fun _ : Fin K => Finset.range (4 * c + 1)),
        (if ∑ k, J k ≤ 4 * c then ∏ k, mah (f k) (J k) else 0) * ∏ k, ((n k).choose (J k) : ℚ)) c
    rw [e]
    exact h

end Formalism.MainNotions.G.Joints.F5

end

namespace Formalism.MainNotions.G.Joints

open Formalism.MainNotions.G

theorem joint_types_corollary_sentences (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.tableLineDegreeFive.FilteredProjectionCriterion D := by
  intro p n' O _ _ _ S hG n _ ι _ LL N Ss hmono
  exact ⟨F6.c1 O n ι LL, F6.c2 O n ι LL, F6.c3 p n' O S hG n ι LL N Ss, fun ee hee =>
    ⟨F7.clause4 D p n' O S hG n ι LL N Ss hmono ee hee, F7.clause5 D p n' O S hG n ι LL N Ss hmono ee hee,
      F7.clause6 D p n' O S hG n ι LL N Ss hmono ee hee, F6.c8 p n' O S hG n ι LL N Ss⟩⟩

end Formalism.MainNotions.G.Joints

namespace Formalism.MainNotions.G.Joints

open Formalism.MainNotions.G Formalism.MainNotions.tableLineDegreeFive

theorem coarse_units_lemma (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.tableLineDegreeFive.adm22 D := by
  intro p _ h5 t
  exact ⟨F2.coarse_unit_product_prime_power p t, F2.padic_log_unit_factor_series p (fun s f h => F1.plog_prod p s f h) t, F3.padic_val_harmonic_lower_bound p h5 t, F3.power_sum_polynomial_exists,
    F3.padic_val_harmonic_term_bound p h5 t, F4.binomial_decay_unit_factor p h5 t, F4.binomial_decay_unit_factor_inv p h5 t, F4.binomial_decay_second_factor p h5 t, F5.binomial_basis_approximation p⟩

end Formalism.MainNotions.G.Joints

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section GlobalTheory

variable {A A' : Type} [CommRing A] [CommRing A'] {n : ℕ}

def kr_blk (W : Fin n → A) (Dm : Matrix (Fin n) (Fin n) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => Fin.cases (motive := fun _ => A) (Fin.cases (motive := fun _ => A) 1 W j)
    (fun i' => Fin.cases (motive := fun _ => A) 0 (fun j' => Dm i' j') j) i

def kr_lowM (γ : A) (v : Fin n → A) (b' : Matrix (Fin n) (Fin n) A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => Fin.cases (motive := fun _ => A) (Fin.cases (motive := fun _ => A) γ (fun _ => 0) j)
    (fun i' => Fin.cases (motive := fun _ => A) (v i') (fun j' => b' i' j') j) i

variable (W : Fin n → A) (Dm : Matrix (Fin n) (Fin n) A) (γ : A) (v : Fin n → A) (b' : Matrix (Fin n) (Fin n) A)

@[simp] theorem blk_00 : kr_blk W Dm 0 0 = 1 := rfl
@[simp] theorem blk_0s (j : Fin n) : kr_blk W Dm 0 j.succ = W j := rfl
@[simp] theorem cornerScalarBlockMatrix_apply_succ_zero (i : Fin n) : kr_blk W Dm i.succ 0 = 0 := rfl
@[simp] theorem blk_ss (i j : Fin n) : kr_blk W Dm i.succ j.succ = Dm i j := rfl
@[simp] theorem lowM_00 : kr_lowM γ v b' 0 0 = γ := rfl
@[simp] theorem lowM_0s (j : Fin n) : kr_lowM γ v b' 0 j.succ = 0 := rfl
@[simp] theorem lowerMatrix_succ_zero (i : Fin n) : kr_lowM γ v b' i.succ 0 = v i := rfl
@[simp] theorem lowM_ss (i j : Fin n) : kr_lowM γ v b' i.succ j.succ = b' i j := rfl

end GlobalTheory

def kr_genD (O : Type) [CommRing O] (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1))) :=
  (genMat O (r + 1)).map ((C : GLCoord O (r + 1) →+* MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1))).comp
    (algebraMap (MvPolynomial (Fin (r + 1) × Fin (r + 1)) O) (GLCoord O (r + 1))))

section Eval

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]

theorem kr_evalG_algebraMap {n : ℕ} (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (aeval (fun x : Fin n × Fin n => g x.1 x.2) (genMat O n).det)) (c : O) :
    evalG (R := O) g hg (algebraMap O (GLCoord O n) c) = algebraMap O A c := by
  rw [IsScalarTower.algebraMap_apply O (MvPolynomial (Fin n × Fin n) O) (GLCoord O n), evalG_alg, AlgHom.commutes]

variable {r : ℕ}

def kr_resEv (W : Fin (r + 1) → A) (Dm : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (hD : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => Dm x.1 x.2) (genMat O (r + 1)).det)) :
    MvPolynomial (Fin (r + 1)) (GLCoord O (r + 1)) →ₐ[O] A :=
  { eval₂Hom (evalG (R := O) Dm hD) W with
    commutes' := fun c => by
      show eval₂Hom (evalG (R := O) Dm hD) W (algebraMap O _ c) = algebraMap O A c
      rw [MvPolynomial.algebraMap_apply, eval₂Hom_C, kr_evalG_algebraMap] }

def kr_cellW {n : ℕ} (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (γ : Aˣ) : Fin n → A :=
  fun j => ((γ⁻¹ : Aˣ) : A) * g 0 j.succ

def kr_cellD {n : ℕ} (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (γ : Aˣ) : Matrix (Fin n) (Fin n) A :=
  fun i j => g i.succ j.succ - g i.succ 0 * kr_cellW g γ j

end Eval

section Generic

variable (O : Type) [CommRing O] [IsDomain O] (n : ℕ)

theorem kr_genMat_det_ne : (genMat O n).det ≠ 0 := Matrix.det_mvPolynomialX_ne_zero (Fin n) O

instance kr_instDomGL : IsDomain (GLCoord O n) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (kr_genMat_det_ne O n))

theorem kr_GL_inj : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (kr_genMat_det_ne O n))

def kr_genG : Matrix (Fin n) (Fin n) (GLCoord O n) :=
  (genMat O n).map (algebraMap (MvPolynomial (Fin n × Fin n) O) (GLCoord O n))

def topLeftCoordinate : GLCoord O (n + 1) := algebraMap (MvPolynomial (Fin (n + 1) × Fin (n + 1)) O) (GLCoord O (n + 1)) (X (0, 0))

theorem corner_entry_ne_zero_alt : topLeftCoordinate O n ≠ 0 := by
  intro h
  exact X_ne_zero (R := O) _ (kr_GL_inj O (n + 1) (h.trans (map_zero _).symm))

abbrev kr_CA := Localization.Away (topLeftCoordinate O n)

instance kr_instDomCA : IsDomain (kr_CA O n) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (corner_entry_ne_zero_alt O n))

def kr_iotaA : GLCoord O (n + 1) →ₐ[O] kr_CA O n := IsScalarTower.toAlgHom O (GLCoord O (n + 1)) (kr_CA O n)

def kr_genA : Matrix (Fin (n + 1)) (Fin (n + 1)) (kr_CA O n) := (kr_genG O (n + 1)).map (kr_iotaA O n)

def kr_gam : (kr_CA O n)ˣ := (IsLocalization.Away.algebraMap_isUnit (S := kr_CA O n) (topLeftCoordinate O n)).unit

def kr_cW : Fin n → kr_CA O n := kr_cellW (kr_genA O n) (kr_gam O n)
def kr_cD : Matrix (Fin n) (Fin n) (kr_CA O n) := kr_cellD (kr_genA O n) (kr_gam O n)

end Generic

section Loc

variable {R : Type} [CommRing R] [IsDomain R]

theorem kr_away_pow_dvd (s q : R) (hq : Prime q) (hs : ¬ q ∣ s) (e : ℕ) (x : R)
    (h : algebraMap R (Localization.Away s) q ^ e ∣ algebraMap R (Localization.Away s) x) : q ^ e ∣ x := by
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ dvd_zero q)
  have hinj : Function.Injective (algebraMap R (Localization.Away s)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)
  obtain ⟨y, hy⟩ := h
  obtain ⟨⟨z, ⟨t, k, hk⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers s) y
  have hz' : y * algebraMap R (Localization.Away s) t = algebraMap R (Localization.Away s) z := hz
  have h1 : x * t = q ^ e * z := by
    apply hinj
    rw [map_mul, hy, mul_assoc, hz', map_mul, map_pow]
  have hk' : s ^ k = t := hk
  have ht : ¬ q ∣ t := by
    rw [← hk']
    exact fun hd => hs (hq.dvd_of_dvd_pow hd)
  exact hq.pow_dvd_of_dvd_mul_right e ht ⟨z, h1⟩

theorem kr_away_prime (s q : R) (hq : Prime q) (hs : ¬ q ∣ s) : Prime (algebraMap R (Localization.Away s) q) := by
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ dvd_zero q)
  have hinj : Function.Injective (algebraMap R (Localization.Away s)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hs0)
  have hdvd : ∀ x : R, algebraMap R (Localization.Away s) q ∣ algebraMap R (Localization.Away s) x → q ∣ x := by
    intro x hx
    have := kr_away_pow_dvd s q hq hs 1 x (by rwa [pow_one])
    rwa [pow_one] at this
  refine ⟨fun h0 => hq.ne_zero (hinj (h0.trans (map_zero _).symm)), fun hu => ?_, fun a b hab => ?_⟩
  · have h1 : algebraMap R (Localization.Away s) q ∣ algebraMap R (Localization.Away s) 1 := by
      rw [map_one]; exact hu.dvd
    exact hq.not_isUnit (isUnit_of_dvd_one (hdvd 1 h1))
  · obtain ⟨⟨a0, t1⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s) a
    obtain ⟨⟨b0, t2⟩, hb⟩ := IsLocalization.surj (Submonoid.powers s) b
    have ha' : a * algebraMap R (Localization.Away s) t1 = algebraMap R (Localization.Away s) a0 := ha
    have hb' : b * algebraMap R (Localization.Away s) t2 = algebraMap R (Localization.Away s) b0 := hb
    have hu1 : IsUnit (algebraMap R (Localization.Away s) (t1 : R)) := IsLocalization.map_units _ t1
    have hu2 : IsUnit (algebraMap R (Localization.Away s) (t2 : R)) := IsLocalization.map_units _ t2
    have h1 : algebraMap R (Localization.Away s) q ∣ algebraMap R (Localization.Away s) (a0 * b0) := by
      rw [map_mul, ← ha', ← hb']
      have : a * algebraMap R (Localization.Away s) (t1 : R) * (b * algebraMap R (Localization.Away s) (t2 : R)) =
          a * b * (algebraMap R (Localization.Away s) (t1 : R) * algebraMap R (Localization.Away s) (t2 : R)) := by ring
      rw [this]
      exact Dvd.dvd.mul_right hab _
    rcases hq.dvd_or_dvd (hdvd _ h1) with h | h
    · left
      have h2 : algebraMap R (Localization.Away s) q ∣ a * algebraMap R (Localization.Away s) (t1 : R) := by
        rw [ha']; exact map_dvd _ h
      exact (hu1.dvd_mul_right).1 h2
    · right
      have h2 : algebraMap R (Localization.Away s) q ∣ b * algebraMap R (Localization.Away s) (t2 : R) := by
        rw [hb']; exact map_dvd _ h
      exact (hu2.dvd_mul_right).1 h2

end Loc

section Primes

variable (O : Type) [CommRing O] [IsDomain O] (n : ℕ)

def kr_evOne : MvPolynomial (Fin n × Fin n) O →ₐ[O] O := aeval (fun x : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) O) x.1 x.2)

theorem kr_evOne_det : kr_evOne O n (genMat O n).det = 1 := by
  unfold kr_evOne
  rw [aeval_genMat_det, Matrix.det_one]

theorem kr_evOne_X (i j : Fin n) : kr_evOne O n (X (i, j)) = (1 : Matrix (Fin n) (Fin n) O) i j := by
  unfold kr_evOne
  rw [aeval_X]

theorem kr_not_dvd_det (q : MvPolynomial (Fin n × Fin n) O) (hq : ¬ IsUnit (kr_evOne O n q)) : ¬ q ∣ (genMat O n).det := by
  intro h
  have := map_dvd (kr_evOne O n) h
  rw [kr_evOne_det] at this
  exact hq (isUnit_of_dvd_one this)

end Primes

section Coeff

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] {r : ℕ}

def kr_cAlg (O : Type) [CommRing O] (A : Type) [CommRing A] [Algebra O A] (σ : Type) : A →ₐ[O] MvPolynomial σ A :=
  IsScalarTower.toAlgHom O A (MvPolynomial σ A)

end Coeff

theorem kr_HB_of_universal (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ)
    (f₁ : GLCoord O (r + 1))
    (hG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => G0 O (r + 1) x.1 x.2) (genMat O (r + 1)).det))
    (hBG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => (B0 O (r + 1) * G0 O (r + 1)) x.1 x.2)
      (genMat O (r + 1)).det))
    (hE : evalG (R := O) (B0 O (r + 1) * G0 O (r + 1)) hBG0 f₁ =
      (chiB c ka (fun i => (lower_triangular_base_diag_isUnit O (r + 1) i).unit) : UA O (r + 1)) * evalG (R := O) (G0 O (r + 1)) hG0 f₁) :
    f₁ ∈ HB O r c ka := by
  intro A _ _ b g u hg hbg hlow hdiag
  let U0 : Fin (r + 1) → (UA O (r + 1))ˣ := fun i => (lower_triangular_base_diag_isUnit O (r + 1) i).unit
  have hdetg : IsUnit g.det := by rwa [aeval_genMat_det] at hg
  have hbu : ∀ i, IsUnit (b i i) := fun i => by rw [hdiag i]; exact Units.isUnit _
  let φ := spec O (r + 1) b g hbu hdetg
  have hφB : (B0 O (r + 1)).map φ = b := by
    ext i j
    simp only [Matrix.map_apply, B0, uB]
    rw [spec_alg]
    split_ifs with h
    · rw [aeval_X]; rfl
    · rw [map_zero, hlow i j (not_le.mp h)]
  have hφG : (G0 O (r + 1)).map φ = g := by
    ext i j
    simp only [Matrix.map_apply, G0, uG]
    rw [spec_alg, aeval_X]; rfl
  have hφBG : (B0 O (r + 1) * G0 O (r + 1)).map φ = b * g := by
    rw [Matrix.map_mul, hφB, hφG]
  have hφU : (fun i => Units.map ((φ : UA O (r + 1) →+* A) : UA O (r + 1) →* A) (U0 i)) = u := by
    funext i
    apply Units.ext
    have : φ (B0 O (r + 1) i i) = b i i := by
      have := congrFun (congrFun hφB i) i
      simpa using this
    rw [← hdiag i, ← this]
    rfl
  have h1 := congrArg φ hE
  rw [map_mul, evalG_map φ _ hBG0 (by rw [hφBG]; exact hbg), evalG_map φ _ hG0 (by rw [hφG]; exact hg),
    evalG_congr hφBG _ hbg, evalG_congr hφG _ hg] at h1
  rw [h1]
  congr 1
  have h2 := chiB_map (φ : UA O (r + 1) →+* A) c ka U0
  rw [hφU] at h2
  exact h2

theorem kr_HB_of_smul (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) (a : O) (ha : a ≠ 0)
    (f₁ : GLCoord O (r + 1)) (hf : algebraMap O (GLCoord O (r + 1)) a * f₁ ∈ HB O r c ka) : f₁ ∈ HB O r c ka := by
  have hG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => G0 O (r + 1) x.1 x.2) (genMat O (r + 1)).det) := by
    rw [aeval_genMat_det]; exact base_matrix_det_isUnit O (r + 1)
  have hBG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => (B0 O (r + 1) * G0 O (r + 1)) x.1 x.2)
      (genMat O (r + 1)).det) := by
    rw [aeval_genMat_det, Matrix.det_mul]; exact (lower_triangular_base_det_isUnit O (r + 1)).mul (base_matrix_det_isUnit O (r + 1))
  refine kr_HB_of_universal O r c ka f₁ hG0 hBG0 ?_
  have hlow0 : ∀ i j, i < j → B0 O (r + 1) i j = 0 := by
    intro i j hij
    simp [B0, uB, not_le.mpr hij]
  have h0 := hf (UA O (r + 1)) (B0 O (r + 1)) (G0 O (r + 1)) (fun i => (lower_triangular_base_diag_isUnit O (r + 1) i).unit) hG0 hBG0 hlow0
    (fun i => rfl)
  rw [map_mul, map_mul, kr_evalG_algebraMap, kr_evalG_algebraMap] at h0
  have hne : algebraMap O (UA O (r + 1)) a ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply O (MvPolynomial (UV (r + 1)) O) (UA O (r + 1))]
    intro h
    have h1 := UA_inj O (r + 1) (h.trans (map_zero _).symm)
    rw [MvPolynomial.algebraMap_eq] at h1
    exact ha (C_injective _ _ (h1.trans C_0.symm))
  apply mul_left_cancel₀ hne
  rw [h0]; ring

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.GradedWeylDivisibility

def tr (R : Type) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n × Fin n) R := rename Prod.swap

abbrev io (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R →+* GLCoord R n :=
  algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)

theorem map_genMat_det {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) :
    MvPolynomial.map φ (genMat R n).det = (genMat S n).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [genMat]

def redG {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) : GLCoord R n →+* GLCoord S n :=
  IsLocalization.Away.lift (genMat R n).det (g := (io S n).comp (MvPolynomial.map φ))
    (by
      rw [RingHom.comp_apply, map_genMat_det]
      exact IsLocalization.Away.algebraMap_isUnit _)

def detU (R : Type) [CommRing R] (n : ℕ) : (GLCoord R n)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := GLCoord R n) (genMat R n).det).unit

def PolyHB : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (r : ℕ) (ν : Fin (r + 1) → ℕ)
    (P : MvPolynomial (Fin (r + 1) × Fin (r + 1)) R),
    io R (r + 1) P ∈ HB R r (ν 0) (fun i => ν i.succ) → tr R (r + 1) P ∈ dualWeyl R (r + 1) (r + 1) ν

def BideterminantInHighestWeight : Prop :=
  ∀ (R : Type) [CommRing R] (r K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r + 1)
    (I : ∀ k, Fin (sz k) → Fin (r + 1)),
    io R (r + 1) (tr R (r + 1) (bideterminant R sz hsz I)) ∈
      HB R r (shapeDeg (n := r + 1) sz 0) (fun i => shapeDeg (n := r + 1) sz i.succ)

def HBLin : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ),
    (0 : GLCoord R (r + 1)) ∈ HB R r c ka ∧
    (∀ f ∈ HB R r c ka, ∀ f' ∈ HB R r c ka, f + f' ∈ HB R r c ka) ∧
    (∀ (a : R), ∀ f ∈ HB R r c ka, algebraMap R (GLCoord R (r + 1)) a * f ∈ HB R r c ka)

def HBMul : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (c c' : ℤ) (ka ka' : Fin r → ℤ),
    ∀ f ∈ HB R r c ka, ∀ f' ∈ HB R r c' ka', f * f' ∈ HB R r (c + c') (ka + ka')

def HBDet : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ),
    (∀ N : ℤ, ((detU R (r + 1) ^ N : (GLCoord R (r + 1))ˣ) : GLCoord R (r + 1)) ∈ HB R r N (fun _ => N)) ∧
    g0r R r ∈ HB R r 1 (fun _ => 0)

def RedBasic : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ),
    (∀ P, redG φ n (io R n P) = io S n (MvPolynomial.map φ P)) ∧
    (∀ N : ℤ, redG φ n ((detU R n ^ N : (GLCoord R n)ˣ) : GLCoord R n) = ((detU S n ^ N : (GLCoord S n)ˣ) : GLCoord S n))

def RedHB : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (r : ℕ) (c : ℤ) (ka : Fin r → ℤ),
    ∀ f ∈ HB R r c ka, redG φ (r + 1) f ∈ HB S r c ka

def RedKer : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (w : O), Irreducible w → ∀ (n : ℕ)
    (x : GLCoord O n), redG (IsLocalRing.residue O) n x = 0 → ∃ y, x = algebraMap O (GLCoord O n) w * y

def TopRightDivisionDomain : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) (f : GLCoord R (r + 1)), 1 ≤ r →
    f ∈ HB R r c ka → g0r R r ∣ f → ∃ f₁ ∈ HB R r (c - 1) ka, f = g0r R r * f₁

def TopRightCancelConstant : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (r : ℕ) (a : R) (y : GLCoord R (r + 1)), 1 ≤ r → a ≠ 0 →
    g0r R r ∣ algebraMap R (GLCoord R (r + 1)) a * y → g0r R r ∣ y

def Lift : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ),
    ∀ k ∈ HB (IsLocalRing.ResidueField O) r c ka, ∃ f ∈ HB O r c ka, redG (IsLocalRing.residue O) (r + 1) f = k

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.GradedWeylDivisibility

theorem det_ne_zero_of_map_eq_one {B R : Type} [CommRing B] [CommRing R] [Nontrivial R] {n : ℕ} (g : Matrix (Fin n) (Fin n) B)
    (φ : B →+* R) (h : g.map φ = 1) : g.det ≠ 0 := by
  intro h0
  have h1 := congrArg φ h0
  rw [RingHom.map_det, RingHom.mapMatrix_apply, h, Matrix.det_one, map_zero] at h1
  exact one_ne_zero h1

theorem aeval_borel_mul_of_highest_weight {R B : Type} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B] (r : ℕ)
    (ν : Fin (r + 1) → ℕ) (P : MvPolynomial (Fin (r + 1) × Fin (r + 1)) R)
    (h : io R (r + 1) P ∈ HB R r (ν 0) (fun i => ν i.succ))
    (b g : Matrix (Fin (r + 1)) (Fin (r + 1)) B) (hb : ∀ i j, i < j → b i j = 0) (hd : ∀ i, b i i ≠ 0)
    (hg : g.det ≠ 0) :
    aeval (fun x : Fin (r + 1) × Fin (r + 1) => (b * g) x.1 x.2) P =
      (∏ i, b i i ^ ν i) * aeval (fun x : Fin (r + 1) × Fin (r + 1) => g x.1 x.2) P := by
  let A := FractionRing B
  let ι : B →ₐ[R] A := IsScalarTower.toAlgHom R B A
  have hι : Function.Injective ι := IsFractionRing.injective B A
  have hbdet : b.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular b (fun i j hij => hb i j hij)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd i
  have hdetmap : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) B, (M.map ι).det = ι M.det := by
    intro M
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
  have hmul : b.map ι * g.map ι = (b * g).map ι := (Matrix.map_mul).symm
  have hgU : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => (g.map ι) x.1 x.2) (genMat R (r + 1)).det) := by
    rw [aeval_genMat_det, hdetmap]
    exact isUnit_iff_ne_zero.2 (fun h0 => hg (hι (by rw [h0, map_zero])))
  have hbgU : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => (b.map ι * g.map ι) x.1 x.2)
      (genMat R (r + 1)).det) := by
    rw [aeval_genMat_det, hmul, hdetmap, Matrix.det_mul]
    exact isUnit_iff_ne_zero.2 (fun h0 => mul_ne_zero hbdet hg (hι (by rw [h0, map_zero])))
  let u : Fin (r + 1) → Aˣ := fun i => Units.mk0 (ι (b i i)) (fun h0 => hd i (hι (by rw [h0, map_zero])))
  have key := h A (b.map ι) (g.map ι) u hgU hbgU
    (fun i j hij => by rw [Matrix.map_apply, hb i j hij, map_zero]) (fun i => rfl)
  rw [evalG_alg, evalG_alg] at key
  have hchi : ((chiB (ν 0 : ℤ) (fun i => (ν i.succ : ℤ)) u : Aˣ) : A) = ι (∏ i, b i i ^ ν i) := by
    simp [chiB, u, Fin.prod_univ_succ]
  have e1 : (fun x : Fin (r + 1) × Fin (r + 1) => (b.map ι * g.map ι) x.1 x.2) =
      fun x => ι ((b * g) x.1 x.2) := by
    funext x; rw [hmul]; rfl
  have e2 : (fun x : Fin (r + 1) × Fin (r + 1) => (g.map ι) x.1 x.2) = fun x => ι (g x.1 x.2) := rfl
  rw [e1, e2, hchi, ← comp_aeval_apply, ← comp_aeval_apply, ← map_mul] at key
  exact hι key

theorem rename_eq_aeval_alt {R σ τ : Type} [CommRing R] (f : σ → τ) (P : MvPolynomial σ R) :
    rename f P = aeval (fun x => (X (f x) : MvPolynomial τ R)) P := by
  have h : (rename f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) = aeval (fun x => (X (f x) : MvPolynomial τ R)) := by
    ext x
    simp
  exact DFunLike.congr_fun h P

theorem column_addition_fixes_transpose {R : Type} [CommRing R] [IsDomain R] (r : ℕ)
    (ν : Fin (r + 1) → ℕ) (P : MvPolynomial (Fin (r + 1) × Fin (r + 1)) R)
    (h : io R (r + 1) P ∈ HB R r (ν 0) (fun i => ν i.succ)) (l j : Fin (r + 1)) (hlj : l < j) :
    colAddGen R (r := r + 1) l j (tr R (r + 1) P) = rename some (tr R (r + 1) P) := by
  classical
  let B := MvPolynomial (Option (Fin (r + 1) × Fin (r + 1))) R
  let g : Matrix (Fin (r + 1)) (Fin (r + 1)) B := fun i k => X (some (k, i))
  let b : Matrix (Fin (r + 1)) (Fin (r + 1)) B := fun i m =>
    (if i = m then 1 else 0) + (if i = j ∧ m = l then X none else 0)
  have hg : g.det ≠ 0 := by
    refine det_ne_zero_of_map_eq_one g ((aeval (fun o : Option (Fin (r + 1) × Fin (r + 1)) =>
      o.elim (0 : R) (fun v => if v.2 = v.1 then 1 else 0)) : B →ₐ[R] R) : B →+* R) ?_
    ext i k
    rw [Matrix.map_apply, Matrix.one_apply]
    show (aeval _ : B →ₐ[R] R) (X (some (k, i))) = _
    rw [aeval_X]
    rfl
  have hbb : ∀ i, b i i = 1 := by
    intro i
    have : ¬ (i = j ∧ i = l) := fun hh => hlj.ne (hh.2.symm.trans hh.1)
    simp [b, this]
  have key := aeval_borel_mul_of_highest_weight r ν P h b g
    (fun i m him => by
      have h1 : ¬ (i = j ∧ m = l) := fun hh => absurd (hh.1 ▸ hh.2 ▸ him) (not_lt.2 hlj.le)
      simp [b, him.ne, h1])
    (fun i => by rw [hbb]; exact one_ne_zero) hg
  simp only [hbb, one_pow, Finset.prod_const_one, one_mul] at key
  have hbg : ∀ i k, (b * g) i k = if i = j then X (some (k, i)) + X none * X (some (k, l)) else X (some (k, i)) := by
    intro i k
    rw [Matrix.mul_apply]
    by_cases hij : i = j
    · simp [b, g, hij, add_mul, Finset.sum_add_distrib]
    · simp [b, g, hij]
  simp only [colAddGen, tr, aeval_rename, rename_rename]
  have e1 : ((fun v : Fin (r + 1) × Fin (r + 1) =>
      if v.2 = j then (X (some v) + X none * X (some (v.1, l)) : B) else X (some v)) ∘ Prod.swap) =
      fun x => (b * g) x.1 x.2 := by
    funext x
    rw [hbg]
    rfl
  rw [e1, key, rename_eq_aeval_alt]
  rfl

theorem monomial_mapDomain_eq_prod {R σ τ : Type} [CommRing R] (f : σ → τ) (d : σ →₀ ℕ) :
    (monomial (d.mapDomain f) (1 : R)) = d.prod fun v k => (X (f v) : MvPolynomial τ R) ^ k := by
  rw [← rename_monomial, monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, rename_X]
  rfl

theorem column_weight_eq_mapDomain {m n : ℕ} (d : Fin m × Fin n →₀ ℕ) (t : Fin n) :
    Finsupp.weight (colW m n) d t = d.mapDomain Prod.snd t := by
  simp only [Finsupp.weight_apply, Finsupp.mapDomain, Finsupp.sum, Finset.sum_apply, Finsupp.coe_finsetSum,
    Pi.smul_apply, colW, Pi.single_apply, Finsupp.single_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : t = v.2
  · simp [h]
  · simp [h, Ne.symm h]

theorem isWeightedHomogeneous_of_column_scaling {R : Type} [CommRing R] {m n : ℕ} (Q : MvPolynomial (Fin m × Fin n) R) (ν : Fin n → ℕ)
    (key : aeval (fun v : Fin m × Fin n =>
        (X (Sum.inr v.2) * X (Sum.inl v) : MvPolynomial ((Fin m × Fin n) ⊕ Fin n) R)) Q =
      (∏ s, X (Sum.inr s) ^ ν s) * rename Sum.inl Q) :
    IsWeightedHomogeneous (colW m n) Q ν := by
  classical
  intro d0 hd0
  let E : (Fin m × Fin n →₀ ℕ) → ((Fin m × Fin n) ⊕ Fin n →₀ ℕ) := fun d =>
    d.mapDomain Sum.inl + d.mapDomain (Sum.inr ∘ Prod.snd)
  have hEl : ∀ d v, E d (Sum.inl v) = d v := by
    intro d v
    simp only [E, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective]
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), add_zero]
  have hEr : ∀ d s, E d (Sum.inr s) = d.mapDomain Prod.snd s := by
    intro d s
    simp only [E, Finsupp.add_apply]
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), Finsupp.mapDomain_comp,
      Finsupp.mapDomain_apply Sum.inr_injective, zero_add]
  have hmono : ∀ d (a : R), aeval (fun v : Fin m × Fin n =>
        (X (Sum.inr v.2) * X (Sum.inl v) : MvPolynomial ((Fin m × Fin n) ⊕ Fin n) R)) (monomial d a) =
      monomial (E d) a := by
    intro d a
    rw [aeval_monomial]
    have hs : (monomial (E d) (1 : R)) =
        monomial (d.mapDomain Sum.inl) 1 * monomial (d.mapDomain (Sum.inr ∘ Prod.snd)) 1 := by
      rw [monomial_mul, one_mul]
    have hp : (d.prod fun v k => (X (Sum.inr v.2) * X (Sum.inl v) :
        MvPolynomial ((Fin m × Fin n) ⊕ Fin n) R) ^ k) = monomial (E d) 1 := by
      rw [hs, monomial_mapDomain_eq_prod, monomial_mapDomain_eq_prod, ← Finsupp.prod_mul]
      refine Finsupp.prod_congr fun v _ => ?_
      rw [mul_pow, mul_comm]
      rfl
    rw [hp, algebraMap_eq, C_mul_monomial, mul_one]
  have hL : coeff (E d0) (aeval (fun v : Fin m × Fin n =>
        (X (Sum.inr v.2) * X (Sum.inl v) : MvPolynomial ((Fin m × Fin n) ⊕ Fin n) R)) Q) = coeff d0 Q := by
    conv_lhs => rw [Q.as_sum]
    rw [map_sum, coeff_sum]
    simp_rw [hmono, coeff_monomial]
    rw [Finset.sum_eq_single d0]
    · simp
    · intro d _ hne
      rw [if_neg]
      intro hE
      apply hne
      ext v
      rw [← hEl d v, hE, hEl]
    · intro hn
      simp [notMem_support_iff.1 hn]
  have hprod : (∏ s, X (Sum.inr s) ^ ν s : MvPolynomial ((Fin m × Fin n) ⊕ Fin n) R) =
      monomial ((Finsupp.equivFunOnFinite.symm ν).mapDomain Sum.inr) 1 := by
    rw [monomial_mapDomain_eq_prod, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp
  have hR : coeff (E d0) ((∏ s, X (Sum.inr s) ^ ν s) * rename Sum.inl Q :
      MvPolynomial ((Fin m × Fin n) ⊕ Fin n) R) ≠ 0 := by
    rw [← key, hL]; exact hd0
  rw [hprod, coeff_monomial_mul'] at hR
  split_ifs at hR with hle
  · rw [one_mul] at hR
    obtain ⟨u, hu, -⟩ := coeff_rename_ne_zero _ _ _ hR
    funext t
    rw [column_weight_eq_mapDomain, ← hEr]
    have h1 := DFunLike.congr_fun hu (Sum.inr t)
    have h2 := hle (Sum.inr t)
    rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp), Finsupp.tsub_apply,
      Finsupp.mapDomain_apply Sum.inr_injective] at h1
    rw [Finsupp.mapDomain_apply Sum.inr_injective] at h2
    have hν : (Finsupp.equivFunOnFinite.symm ν) t = ν t := rfl
    rw [hν] at h1 h2
    omega
  · exact absurd rfl hR

theorem weighted_homog_of_highest_weight {R : Type} [CommRing R] [IsDomain R] (r : ℕ)
    (ν : Fin (r + 1) → ℕ) (P : MvPolynomial (Fin (r + 1) × Fin (r + 1)) R)
    (h : io R (r + 1) P ∈ HB R r (ν 0) (fun i => ν i.succ)) :
    IsWeightedHomogeneous (colW (r + 1) (r + 1)) (tr R (r + 1) P) ν := by
  classical
  let B := MvPolynomial ((Fin (r + 1) × Fin (r + 1)) ⊕ Fin (r + 1)) R
  let g : Matrix (Fin (r + 1)) (Fin (r + 1)) B := fun i k => X (Sum.inl (k, i))
  let b : Matrix (Fin (r + 1)) (Fin (r + 1)) B := Matrix.diagonal fun i => X (Sum.inr i)
  have hg : g.det ≠ 0 := by
    refine det_ne_zero_of_map_eq_one g ((aeval (Sum.elim (fun v : Fin (r + 1) × Fin (r + 1) => if v.2 = v.1 then (1 : R) else 0)
      (fun _ => 0)) : B →ₐ[R] R) : B →+* R) ?_
    ext i k
    rw [Matrix.map_apply, Matrix.one_apply]
    show (aeval _ : B →ₐ[R] R) (X (Sum.inl (k, i))) = _
    rw [aeval_X]
    rfl
  have key := aeval_borel_mul_of_highest_weight r ν P h b g (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne)
    (fun i => by
      have hbi : b i i = X (Sum.inr i) := Matrix.diagonal_apply_eq _ i
      rw [hbi]; exact X_ne_zero _) hg
  apply isWeightedHomogeneous_of_column_scaling
  simp only [tr, aeval_rename, rename_rename]
  have e1 : ((fun v : Fin (r + 1) × Fin (r + 1) => (X (Sum.inr v.2) * X (Sum.inl v) : B)) ∘ Prod.swap) =
      fun x => (b * g) x.1 x.2 := by
    funext x
    show _ = (Matrix.diagonal (fun i => (X (Sum.inr i) : B)) * g) x.1 x.2
    rw [Matrix.diagonal_mul]
    rfl
  rw [e1, key, rename_eq_aeval_alt]
  simp only [b, Matrix.diagonal_apply_eq]
  rfl

theorem polyHB : PolyHB := by
  intro R _ _ r ν P h
  rw [dualWeyl, Submodule.mem_inf]
  refine ⟨(mem_weightedHomogeneousSubmodule R _ _ _).2 (weighted_homog_of_highest_weight r ν P h), ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  intro l j hlj
  exact column_addition_fixes_transpose r ν P h l j hlj

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.GradedWeylDivisibility

section Tools

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

theorem evaluation_algebraMap_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (aeval (fun x : Fin n × Fin n => g x.1 x.2) (genMat R n).det)) (a : R) :
    evalG (R := R) g hg (algebraMap R (GLCoord R n) a) = algebraMap R A a := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n), evalG_alg,
    MvPolynomial.algebraMap_eq, aeval_C]

theorem character_eq_prod_pow {r : ℕ} (w : Fin (r + 1) → ℤ) (u : Fin (r + 1) → Aˣ) :
    chiB (w 0) (fun i => w i.succ) u = ∏ i, u i ^ w i := by
  unfold chiB
  rw [Fin.prod_univ_succ]

theorem character_add_eq_mul {r : ℕ} (c c' : ℤ) (ka ka' : Fin r → ℤ) (u : Fin (r + 1) → Aˣ) :
    chiB (c + c') (ka + ka') u = chiB c ka u * chiB c' ka' u := by
  unfold chiB
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem evaluation_det_eq {n : ℕ} (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (aeval (fun x : Fin n × Fin n => g x.1 x.2) (genMat R n).det)) :
    evalG (R := R) g hg (detU R n : GLCoord R n) = g.det := by
  have h : ((detU R n : (GLCoord R n)ˣ) : GLCoord R n) =
      algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) (genMat R n).det := IsUnit.unit_spec _
  rw [h, evalG_alg, aeval_genMat_det]

theorem evaluation_det_zpow {n : ℕ} (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (aeval (fun x : Fin n × Fin n => g x.1 x.2) (genMat R n).det)) (N : ℤ) :
    evalG (R := R) g hg ((detU R n ^ N : (GLCoord R n)ˣ) : GLCoord R n) =
      ((Units.map (evalG (R := R) g hg : GLCoord R n →* A) (detU R n) ^ N : Aˣ) : A) := by
  rw [← map_zpow]
  rfl

theorem det_of_lower_triangular {n : ℕ} (b : Matrix (Fin n) (Fin n) A) (h1 : ∀ i j, i < j → b i j = 0) :
    b.det = ∏ i, b i i :=
  Matrix.det_of_isLowerTriangular b (fun i j hij => h1 i j (OrderDual.toDual_lt_toDual.mp hij))

theorem evaluation_initial_minor_eq {r s : ℕ} (hs : s ≤ r + 1) (I : Fin s → Fin (r + 1))
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) A)
    (hM : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => M x.1 x.2) (genMat R (r + 1)).det)) :
    evalG (R := R) M hM (io R (r + 1) (tr R (r + 1) (initMinor R I hs))) =
      (Matrix.of fun p q : Fin s => M (Fin.castLE hs q) (I p)).det := by
  rw [evalG_alg]
  unfold tr initMinor
  rw [aeval_rename, AlgHom.map_det]
  congr 1
  ext p q
  simp

theorem minor_triangular_mul {r s : ℕ} (hs : s ≤ r + 1) (I : Fin s → Fin (r + 1))
    (b g : Matrix (Fin (r + 1)) (Fin (r + 1)) A) (u : Fin (r + 1) → Aˣ)
    (h1 : ∀ i j, i < j → b i j = 0) (h2 : ∀ i, b i i = u i) :
    (Matrix.of fun p q : Fin s => (b * g) (Fin.castLE hs q) (I p)).det =
      (∏ q : Fin s, (u (Fin.castLE hs q) : A)) *
        (Matrix.of fun p q : Fin s => g (Fin.castLE hs q) (I p)).det := by
  have hmat : (Matrix.of fun p q : Fin s => (b * g) (Fin.castLE hs q) (I p)) =
      (Matrix.of fun p q : Fin s => g (Fin.castLE hs q) (I p)) *
        (Matrix.of fun q q' : Fin s => b (Fin.castLE hs q) (Fin.castLE hs q')).transpose := by
    ext p q
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ ?_ ?_
    · intro j hj
      have hlt : Fin.castLE hs q < j := by
        by_contra hlt
        apply hj
        have h3 : j.val ≤ q.val := not_lt.mp hlt
        exact ⟨⟨j.val, lt_of_le_of_lt h3 q.isLt⟩, Fin.ext rfl⟩
      rw [h1 _ _ hlt, zero_mul]
    · intro q'
      exact mul_comm _ _
  have hlow : (Matrix.of fun q q' : Fin s => b (Fin.castLE hs q) (Fin.castLE hs q')).det =
      ∏ q : Fin s, (u (Fin.castLE hs q) : A) := by
    rw [det_of_lower_triangular (Matrix.of fun q q' : Fin s => b (Fin.castLE hs q) (Fin.castLE hs q'))
      (fun i j hij => h1 (Fin.castLE hs i) (Fin.castLE hs j) hij)]
    exact Finset.prod_congr rfl fun q _ => h2 _
  rw [hmat, Matrix.det_mul, Matrix.det_transpose, hlow, mul_comm]

end Tools

theorem hbLin : HBLin := by
  intro R _ r c ka
  refine ⟨?_, ?_, ?_⟩
  · intro A _ _ b g u hg hbg _ _
    simp
  · intro f hf f' hf' A _ _ b g u hg hbg h1 h2
    rw [map_add, map_add, hf A b g u hg hbg h1 h2, hf' A b g u hg hbg h1 h2, mul_add]
  · intro a f hf A _ _ b g u hg hbg h1 h2
    rw [map_mul, map_mul, hf A b g u hg hbg h1 h2, evaluation_algebraMap_eq, evaluation_algebraMap_eq]
    ring

theorem hbMul : HBMul := by
  intro R _ r c c' ka ka' f hf f' hf' A _ _ b g u hg hbg h1 h2
  rw [map_mul, map_mul, hf A b g u hg hbg h1 h2, hf' A b g u hg hbg h1 h2, character_add_eq_mul, Units.val_mul]
  ring

theorem hbDet : HBDet := by
  intro R _ r
  refine ⟨?_, ?_⟩
  · intro N A _ _ b g u hg hbg h1 h2
    have hd : Units.map (evalG (R := R) (b * g) hbg : GLCoord R (r + 1) →* A) (detU R (r + 1)) =
        (∏ i, u i) * Units.map (evalG (R := R) g hg : GLCoord R (r + 1) →* A) (detU R (r + 1)) := by
      apply Units.ext
      rw [Units.val_mul, Units.coe_map, Units.coe_map, Units.coe_prod]
      show evalG (R := R) (b * g) hbg (detU R (r + 1) : GLCoord R (r + 1)) =
        (∏ i, (u i : A)) * evalG (R := R) g hg (detU R (r + 1) : GLCoord R (r + 1))
      rw [evaluation_det_eq, evaluation_det_eq, Matrix.det_mul, det_of_lower_triangular b h1]
      congr 1
      exact Finset.prod_congr rfl fun i _ => h2 i
    have hc : chiB N (fun _ => N) u = (∏ i, u i) ^ N := by
      unfold chiB
      rw [Finset.prod_zpow, ← mul_zpow, ← Fin.prod_univ_succ u]
    rw [evaluation_det_zpow, evaluation_det_zpow, hd, mul_zpow, Units.val_mul, hc]
  · intro A _ _ b g u hg hbg h1 h2
    rw [evaluation_generic_corner_entry, evaluation_generic_corner_entry, Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [h2 0]
      congr 1
      simp [chiB]
    · intro j _ hj
      rw [h1 0 j (Fin.pos_of_ne_zero hj), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

def initialMinorWeight (r s : ℕ) : Fin (r + 1) → ℤ := fun i => if i.val < s then 1 else 0

theorem initial_minor_transpose_mem_highest_weight (R : Type) [CommRing R] {r s : ℕ} (hs : s ≤ r + 1) (I : Fin s → Fin (r + 1)) :
    io R (r + 1) (tr R (r + 1) (initMinor R I hs)) ∈ HB R r (initialMinorWeight r s 0) (fun i => initialMinorWeight r s i.succ) := by
  intro A _ _ b g u hg hbg h1 h2
  rw [evaluation_initial_minor_eq, evaluation_initial_minor_eq, minor_triangular_mul hs I b g u h1 h2, character_eq_prod_pow]
  congr 1
  rw [Units.coe_prod]
  refine Fintype.prod_of_injective (Fin.castLE hs) (Fin.castLE_injective hs) _ _ ?_ ?_
  · intro j hj
    have hn : ¬ j.val < s := fun h => hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
    simp [initialMinorWeight, hn]
  · intro q
    simp [initialMinorWeight]

theorem one_mem_highest_weight (R : Type) [CommRing R] (r : ℕ) :
    (1 : GLCoord R (r + 1)) ∈ HB R r ((0 : Fin (r + 1) → ℤ) 0) (fun i => (0 : Fin (r + 1) → ℤ) i.succ) := by
  intro A _ _ b g u hg hbg _ _
  simp [chiB]

theorem prod_mem_highest_weight (R : Type) [CommRing R] (r : ℕ) {ι : Type} (s : Finset ι) (f : ι → GLCoord R (r + 1))
    (w : ι → Fin (r + 1) → ℤ) (h : ∀ k ∈ s, f k ∈ HB R r (w k 0) (fun i => w k i.succ)) :
    ∏ k ∈ s, f k ∈ HB R r ((∑ k ∈ s, w k) 0) (fun i => (∑ k ∈ s, w k) i.succ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact one_mem_highest_weight R r
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact hbMul R r _ _ _ _ _ (h a (Finset.mem_insert_self a s)) _
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem bidetHB : BideterminantInHighestWeight := by
  intro R _ r K sz hsz I
  have h := prod_mem_highest_weight R r Finset.univ
    (fun k : Fin K => io R (r + 1) (tr R (r + 1) (initMinor R (I k) (hsz k)))) (fun k => initialMinorWeight r (sz k))
    (fun k _ => initial_minor_transpose_mem_highest_weight R (hsz k) (I k))
  have hw : (∑ k : Fin K, initialMinorWeight r (sz k)) = fun t => ((shapeDeg (n := r + 1) sz t : ℕ) : ℤ) := by
    funext t
    rw [Finset.sum_apply, shapeDeg, Finset.card_filter]
    push_cast
    rfl
  rw [hw] at h
  unfold bideterminant
  rw [map_prod, map_prod]
  exact h

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.GradedWeylDivisibility

section Red

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)

theorem reduction_comm_inclusion (P : MvPolynomial (Fin n × Fin n) R) :
    redG φ n (io R n P) = io S n (MvPolynomial.map φ P) := by
  unfold redG
  exact IsLocalization.Away.lift_eq _ _ P

theorem reduction_det_unit :
    Units.map (redG φ n : GLCoord R n →* GLCoord S n) (detU R n) = detU S n := by
  apply Units.ext
  show redG φ n (io R n (genMat R n).det) = io S n (genMat S n).det
  rw [reduction_comm_inclusion, map_genMat_det]

theorem redBasic : RedBasic := by
  intro R S _ _ φ n
  refine ⟨reduction_comm_inclusion φ n, fun N => ?_⟩
  have h := congrArg Units.val (map_zpow (Units.map (redG φ n : GLCoord R n →* GLCoord S n)) (detU R n) N)
  rw [reduction_det_unit] at h
  exact h

theorem evaluation_reduction_eq {A : Type} [CommRing A] [Algebra S A] (g : Matrix (Fin n) (Fin n) A)
    (hg : IsUnit (aeval (R := S) (fun x : Fin n × Fin n => g x.1 x.2) (genMat S n).det)) :
    letI : Algebra R A := ((algebraMap S A).comp φ).toAlgebra
    ∀ (hg' : IsUnit (aeval (R := R) (fun x : Fin n × Fin n => g x.1 x.2) (genMat R n).det)) (f : GLCoord R n),
      evalG (R := S) g hg (redG φ n f) = evalG (R := R) g hg' f := by
  letI : Algebra R A := ((algebraMap S A).comp φ).toAlgebra
  intro hg' f
  have h : (evalG (R := S) g hg).comp (redG φ n) = evalG (R := R) g hg' := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat R n).det)
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply]
    have e1 : redG φ n (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n) P) =
        algebraMap (MvPolynomial (Fin n × Fin n) S) (GLCoord S n) (MvPolynomial.map φ P) := reduction_comm_inclusion φ n P
    rw [e1, evalG_alg, evalG_alg, aeval_def, aeval_def, eval₂_map]
    rfl
  exact RingHom.congr_fun h f

theorem redHB : RedHB := by
  intro R S _ _ φ r c ka f hf A _ _ b g u hg hbg hlow hdiag
  letI : Algebra R A := ((algebraMap S A).comp φ).toAlgebra
  have hg' : IsUnit (aeval (R := R) (fun x : Fin (r + 1) × Fin (r + 1) => g x.1 x.2) (genMat R (r + 1)).det) := by
    rw [aeval_genMat_det] at hg ⊢; exact hg
  have hbg' : IsUnit (aeval (R := R) (fun x : Fin (r + 1) × Fin (r + 1) => (b * g) x.1 x.2)
      (genMat R (r + 1)).det) := by
    rw [aeval_genMat_det] at hbg ⊢; exact hbg
  rw [evaluation_reduction_eq φ (r + 1) (b * g) hbg hbg' f, evaluation_reduction_eq φ (r + 1) g hg hg' f]
  exact hf A b g u hg' hbg' hlow hdiag

end Red

theorem genericMatrix_det_ne_zero (R : Type) [CommRing R] [IsDomain R] (n : ℕ) : (genMat R n).det ≠ 0 := by
  intro h
  have := kr_evOne_det R n
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem coordinate_inclusion_injective (R : Type) [CommRing R] [IsDomain R] (n : ℕ) : Function.Injective (io R n) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (genericMatrix_det_ne_zero R n))

theorem redKer : RedKer := by
  intro O _ _ _ w hw n x hx
  obtain ⟨⟨P, t⟩, h⟩ := IsLocalization.surj (Submonoid.powers (genMat O n).det) x
  have h' : x * io O n (t : MvPolynomial (Fin n × Fin n) O) = io O n P := h
  have h1 : io (IsLocalRing.ResidueField O) n (MvPolynomial.map (IsLocalRing.residue O) P) = 0 := by
    rw [← reduction_comm_inclusion, ← h', map_mul, hx, zero_mul]
  have h2 : MvPolynomial.map (IsLocalRing.residue O) P = 0 :=
    coordinate_inclusion_injective (IsLocalRing.ResidueField O) n (h1.trans (map_zero _).symm)
  have h3 : (C w : MvPolynomial (Fin n × Fin n) O) ∣ P := by
    rw [C_dvd_iff_dvd_coeff]
    intro m
    have h4 : IsLocalRing.residue O (coeff m P) = 0 := by
      rw [← coeff_map, h2, coeff_zero]
    rw [IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer w).1 hw,
      Ideal.mem_span_singleton] at h4
    exact h4
  obtain ⟨Q, rfl⟩ := h3
  have hu : IsUnit (io O n (t : MvPolynomial (Fin n × Fin n) O)) := IsLocalization.map_units _ t
  obtain ⟨v, hv⟩ := hu
  refine ⟨io O n Q * ((v⁻¹ : (GLCoord O n)ˣ) : GLCoord O n), ?_⟩
  have h5 : io O n (C w) = algebraMap O (GLCoord O n) w :=
    (IsScalarTower.algebraMap_apply O (MvPolynomial (Fin n × Fin n) O) (GLCoord O n) w).symm
  rw [← hv, map_mul, h5] at h'
  calc x = x * (v : GLCoord O n) * ((v⁻¹ : (GLCoord O n)ˣ) : GLCoord O n) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = algebraMap O (GLCoord O n) w * (io O n Q * ((v⁻¹ : (GLCoord O n)ˣ) : GLCoord O n)) := by
        rw [h', mul_assoc]

theorem kp1Dom : TopRightDivisionDomain := by
  intro O _ _ r c ka f _ hf hdvd
  obtain ⟨f₁, rfl⟩ := hdvd
  refine ⟨f₁, ?_, rfl⟩

  have hG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => G0 O (r + 1) x.1 x.2) (genMat O (r + 1)).det) := by
    rw [aeval_genMat_det]; exact base_matrix_det_isUnit O (r + 1)
  have hBG0 : IsUnit (aeval (fun x : Fin (r + 1) × Fin (r + 1) => (B0 O (r + 1) * G0 O (r + 1)) x.1 x.2)
      (genMat O (r + 1)).det) := by
    rw [aeval_genMat_det, Matrix.det_mul]; exact (lower_triangular_base_det_isUnit O (r + 1)).mul (base_matrix_det_isUnit O (r + 1))
  let U0 : Fin (r + 1) → (UA O (r + 1))ˣ := fun i => (lower_triangular_base_diag_isUnit O (r + 1) i).unit
  have hlow0 : ∀ i j, i < j → B0 O (r + 1) i j = 0 := by
    intro i j hij
    simp [B0, uB, not_le.mpr hij]
  have hU0 : ∀ i, B0 O (r + 1) i i = U0 i := fun i => rfl
  have h0 := hf (UA O (r + 1)) (B0 O (r + 1)) (G0 O (r + 1)) U0 hG0 hBG0 hlow0 hU0
  rw [map_mul, map_mul, evaluation_generic_corner_entry, evaluation_generic_corner_entry] at h0
  have hrow : (B0 O (r + 1) * G0 O (r + 1)) 0 (Fin.last r) = (U0 0 : UA O (r + 1)) * G0 O (r + 1) 0 (Fin.last r) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [hU0]
    · intro k _ hk
      rw [hlow0 0 k (Fin.pos_of_ne_zero hk), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hγ : G0 O (r + 1) 0 (Fin.last r) ≠ 0 := by
    have : G0 O (r + 1) 0 (Fin.last r) = algebraMap (MvPolynomial (UV (r + 1)) O) (UA O (r + 1))
        (X (Sum.inr (0, Fin.last r))) := rfl
    rw [this]
    intro h
    exact X_ne_zero (R := O) _ (UA_inj O (r + 1) (h.trans (map_zero _).symm))
  have hE : evalG (R := O) (B0 O (r + 1) * G0 O (r + 1)) hBG0 f₁ =
      (chiB (c - 1) ka U0 : UA O (r + 1)) * evalG (R := O) (G0 O (r + 1)) hG0 f₁ := by
    rw [hrow, chiB_succ] at h0
    have hne : (U0 0 : UA O (r + 1)) * G0 O (r + 1) 0 (Fin.last r) ≠ 0 := mul_ne_zero (U0 0).ne_zero hγ
    apply mul_left_cancel₀ hne
    rw [h0]; ring

  intro A _ _ b g u hg hbg hlow hdiag
  have hdetg : IsUnit g.det := by rwa [aeval_genMat_det] at hg
  have hbu : ∀ i, IsUnit (b i i) := fun i => by rw [hdiag i]; exact Units.isUnit _
  let φ := spec O (r + 1) b g hbu hdetg
  have hφB : (B0 O (r + 1)).map φ = b := by
    ext i j
    simp only [Matrix.map_apply, B0, uB]
    rw [spec_alg]
    split_ifs with h
    · rw [aeval_X]; rfl
    · rw [map_zero, hlow i j (not_le.mp h)]
  have hφG : (G0 O (r + 1)).map φ = g := by
    ext i j
    simp only [Matrix.map_apply, G0, uG]
    rw [spec_alg, aeval_X]; rfl
  have hφBG : (B0 O (r + 1) * G0 O (r + 1)).map φ = b * g := by
    rw [Matrix.map_mul, hφB, hφG]
  have hφU : (fun i => Units.map ((φ : UA O (r + 1) →+* A) : UA O (r + 1) →* A) (U0 i)) = u := by
    funext i
    apply Units.ext
    have : φ (B0 O (r + 1) i i) = b i i := by
      have := congrFun (congrFun hφB i) i
      simpa using this
    rw [← hdiag i, ← this]
    rfl
  have h1 := congrArg φ hE
  rw [map_mul, evalG_map φ _ hBG0 (by rw [hφBG]; exact hbg), evalG_map φ _ hG0 (by rw [hφG]; exact hg),
    evalG_congr hφBG _ hbg, evalG_congr hφG _ hg] at h1
  rw [h1]
  congr 1
  have h2 := chiB_map (φ : UA O (r + 1) →+* A) (c - 1) ka U0
  rw [hφU] at h2
  exact h2

theorem top_right_not_dvd_det (R : Type) [CommRing R] [IsDomain R] (r : ℕ) (hr : 1 ≤ r) :
    ¬ (X (0, Fin.last r) : MvPolynomial (Fin (r + 1) × Fin (r + 1)) R) ∣ (genMat R (r + 1)).det := by
  apply kr_not_dvd_det
  have h0 : (0 : Fin (r + 1)) ≠ Fin.last r := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [kr_evOne_X, Matrix.one_apply_ne h0]
  exact not_isUnit_zero

theorem g0rCancel : TopRightCancelConstant := by
  intro R _ _ r a y hr ha h
  have hnd := top_right_not_dvd_det R r hr
  have hp : Prime (g0r R r) := kr_away_prime _ (X (0, Fin.last r)) X_prime hnd
  rcases hp.dvd_or_dvd h with h1 | h1
  · exfalso
    have h2 : algebraMap R (GLCoord R (r + 1)) a =
        algebraMap (MvPolynomial (Fin (r + 1) × Fin (r + 1)) R) (GLCoord R (r + 1)) (C a) :=
      IsScalarTower.algebraMap_apply R (MvPolynomial (Fin (r + 1) × Fin (r + 1)) R) (GLCoord R (r + 1)) a
    rw [h2] at h1
    have h3 := kr_away_pow_dvd _ (X (0, Fin.last r)) X_prime hnd 1 (C a) (by rw [pow_one]; exact h1)
    rw [pow_one] at h3
    have h4 := map_dvd (constantCoeff (σ := Fin (r + 1) × Fin (r + 1)) (R := R)) h3
    rw [constantCoeff_X, constantCoeff_C, zero_dvd_iff] at h4
    exact ha h4
  · exact h1

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.GradedWeylDivisibility

theorem transpose_transpose_polynomial (R : Type) [CommRing R] (n : ℕ) (P : MvPolynomial (Fin n × Fin n) R) :
    tr R n (tr R n P) = P := by
  unfold tr
  rw [rename_rename, Prod.swap_swap_eq]
  simp

theorem map_transpose {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)
    (P : MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial.map φ (tr R n P) = tr S n (MvPolynomial.map φ P) := by
  unfold tr
  exact map_rename φ _ P

theorem map_bideterminant {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

theorem algebraMap_eq_inclusion_C (R : Type) [CommRing R] (n : ℕ) (a : R) :
    algebraMap R (GLCoord R n) a = io R n (C a) := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n), MvPolynomial.algebraMap_eq]

theorem detUnit_coe_eq_det_generic (R : Type) [CommRing R] (n : ℕ) :
    ((detU R n : (GLCoord R n)ˣ) : GLCoord R n) = io R n (genMat R n).det := rfl

theorem residue_span_lift_bideterminant (hB1 : BideterminantInHighestWeight) (hB2 : HBLin)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r : ℕ) (ν : Fin (r + 1) → ℕ)
    (Q : MvPolynomial (Fin (r + 1) × Fin (r + 1)) (IsLocalRing.ResidueField O))
    (hQ : Q ∈ Submodule.span (IsLocalRing.ResidueField O)
      {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ r + 1) (I : ∀ k, Fin (sz k) → Fin (r + 1)),
        shapeDeg sz = ν ∧ f = bideterminant (IsLocalRing.ResidueField O) sz hsz I}) :
    ∃ Q' : MvPolynomial (Fin (r + 1) × Fin (r + 1)) O,
      io O (r + 1) (tr O (r + 1) Q') ∈ HB O r (ν 0) (fun i => ν i.succ) ∧
        MvPolynomial.map (IsLocalRing.residue O) Q' = Q := by
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hν, rfl⟩ := hx
    subst hν
    exact ⟨bideterminant O sz hsz I, hB1 O r K sz hsz I, map_bideterminant _ sz hsz I⟩
  | zero =>
    refine ⟨0, ?_, map_zero _⟩
    rw [map_zero, map_zero]
    exact (hB2 O r _ _).1
  | add x y _ _ hx hy =>
    obtain ⟨x', hx1, hx2⟩ := hx
    obtain ⟨y', hy1, hy2⟩ := hy
    refine ⟨x' + y', ?_, by rw [map_add, hx2, hy2]⟩
    rw [map_add, map_add]
    exact (hB2 O r _ _).2.1 _ hx1 _ hy1
  | smul a x _ hx =>
    obtain ⟨x', hx1, hx2⟩ := hx
    obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
    refine ⟨C a' * x', ?_, by rw [map_mul, map_C, hx2, smul_eq_C_mul]⟩
    have : tr O (r + 1) (C a' * x') = C a' * tr O (r + 1) x' := by
      rw [map_mul]
      congr 1
      exact (tr O (r + 1)).commutes a'
    rw [this, map_mul, ← algebraMap_eq_inclusion_C]
    exact (hB2 O r _ _).2.2 a' _ hx1

theorem exists_shift_nonneg_weights {r : ℕ} (c : ℤ) (ka : Fin r → ℤ) : ∃ M : ℕ, 0 ≤ c + M ∧ ∀ i, 0 ≤ ka i + M := by
  refine ⟨c.natAbs + ∑ i, (ka i).natAbs, by omega, fun i => ?_⟩
  have h : (ka i).natAbs ≤ ∑ i, (ka i).natAbs :=
    Finset.single_le_sum (f := fun i => (ka i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem lift_of (hA : PolyHB) (hB1 : BideterminantInHighestWeight) (hB2 : HBLin) (hB3 : HBMul) (hB4 : HBDet) (hC1 : RedBasic) : Lift := by
  intro O _ _ _ r c ka k hk
  obtain ⟨N0, P, hP⟩ := IsLocalization.Away.surj (genMat (IsLocalRing.ResidueField O) (r + 1)).det k
  obtain ⟨M, hcM, hkM⟩ := exists_shift_nonneg_weights c ka
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = N0 + M := ⟨_, rfl⟩
  set F := IsLocalRing.ResidueField O with hF
  obtain ⟨P', hP'⟩ : ∃ P' : MvPolynomial (Fin (r + 1) × Fin (r + 1)) F, P' = P * (genMat F (r + 1)).det ^ M :=
    ⟨_, rfl⟩
  have hcN : 0 ≤ c + N := by omega
  have hkN : ∀ i, 0 ≤ ka i + N := by
    intro i
    have := hkM i
    omega
  set ν : Fin (r + 1) → ℕ := Fin.cons (c + N).toNat (fun i => (ka i + N).toNat) with hν
  have hν0 : ((ν 0 : ℕ) : ℤ) = c + N := by
    simp only [hν, Fin.cons_zero]
    exact Int.toNat_of_nonneg hcN
  have hνs : (fun i : Fin r => ((ν i.succ : ℕ) : ℤ)) = ka + fun _ => (N : ℤ) := by
    funext i
    simp only [hν, Fin.cons_succ, Pi.add_apply]
    exact Int.toNat_of_nonneg (hkN i)
  have hdetN : ((detU F (r + 1) ^ (N : ℤ) : (GLCoord F (r + 1))ˣ) : GLCoord F (r + 1)) =
      io F (r + 1) (genMat F (r + 1)).det ^ N := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, detUnit_coe_eq_det_generic]
  have hioP' : io F (r + 1) P' = k * ((detU F (r + 1) ^ (N : ℤ) : (GLCoord F (r + 1))ˣ) : GLCoord F (r + 1)) := by
    rw [hdetN, hP', map_mul, map_pow, ← hP, hN, pow_add, mul_assoc]
  have hmem : io F (r + 1) P' ∈ HB F r (ν 0) (fun i => ν i.succ) := by
    rw [hν0, hνs, hioP']
    exact hB3 F r c N ka (fun _ => (N : ℤ)) k hk _ ((hB4 F r).1 N)
  have hdw := hA F r ν P' hmem
  rw [standardMonomialSpanDomain F (r + 1) (r + 1) ν] at hdw
  obtain ⟨Q', hQ1, hQ2⟩ := residue_span_lift_bideterminant hB1 hB2 O r ν _ hdw
  refine ⟨io O (r + 1) (tr O (r + 1) Q') *
    ((detU O (r + 1) ^ (-(N : ℤ)) : (GLCoord O (r + 1))ˣ) : GLCoord O (r + 1)), ?_, ?_⟩
  · have h := hB3 O r (ν 0) (-(N : ℤ)) (fun i => ν i.succ) (fun _ => -(N : ℤ)) _ hQ1 _ ((hB4 O r).1 (-(N : ℤ)))
    have e1 : ((ν 0 : ℕ) : ℤ) + -(N : ℤ) = c := by rw [hν0]; ring
    have e2 : ((fun i : Fin r => ((ν i.succ : ℕ) : ℤ)) + fun _ => -(N : ℤ)) = ka := by
      rw [hνs]; funext i; simp
    rw [e1, e2] at h
    exact h
  · rw [map_mul, (hC1 O F (IsLocalRing.residue O) (r + 1)).1, (hC1 O F (IsLocalRing.residue O) (r + 1)).2,
      map_transpose, hQ2, transpose_transpose_polynomial, hioP', mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, mul_one]

theorem top_right_division_lift (hL : Lift) (hB2 : HBLin) (hB3 : HBMul) (hB4 : HBDet) (hC1 : RedBasic) (hC2 : RedHB)
    (hC3 : RedKer) (hC4 : TopRightDivisionDomain) (hC5 : TopRightCancelConstant)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) (hr : 1 ≤ r)
    (w : O) (hw : Irreducible w) :
    ∀ (m : ℕ) (f h : GLCoord O (r + 1)), f ∈ HB O r c ka →
      g0r O r ∣ f - algebraMap O (GLCoord O (r + 1)) (w ^ m) * h → ∃ f' ∈ HB O r c ka, g0r O r ∣ h - f' := by
  intro m
  induction m with
  | zero =>
    intro f h hf hd
    refine ⟨f, hf, ?_⟩
    have e : h - f = -(f - algebraMap O (GLCoord O (r + 1)) (w ^ 0) * h) := by
      rw [pow_zero, map_one, one_mul]; ring
    rw [e]
    exact (dvd_neg).2 hd
  | succ m ih =>
    intro f h hf hd
    obtain ⟨k, hk⟩ := hd
    have hρg : redG (IsLocalRing.residue O) (r + 1) (g0r O r) = g0r (IsLocalRing.ResidueField O) r := by
      unfold g0r
      rw [(hC1 O _ (IsLocalRing.residue O) (r + 1)).1, map_X]
    have hρw : redG (IsLocalRing.residue O) (r + 1) (algebraMap O (GLCoord O (r + 1)) w) = 0 := by
      rw [algebraMap_eq_inclusion_C, (hC1 O _ (IsLocalRing.residue O) (r + 1)).1, map_C]
      have : IsLocalRing.residue O w = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff]
        exact (IsLocalRing.mem_maximalIdeal w).2 hw.not_isUnit
      rw [this, C_0, map_zero]
    have h1 : redG (IsLocalRing.residue O) (r + 1) f =
        g0r (IsLocalRing.ResidueField O) r * redG (IsLocalRing.residue O) (r + 1) k := by
      have h2 := congrArg (redG (IsLocalRing.residue O) (r + 1)) hk
      rw [map_sub, map_mul, map_mul, pow_succ, map_mul, map_mul, hρw, mul_zero, zero_mul, sub_zero, hρg] at h2
      exact h2
    obtain ⟨k1, hk1, hk1e⟩ := hC4 (IsLocalRing.ResidueField O) r c ka _ hr
      (hC2 O _ (IsLocalRing.residue O) r c ka f hf) ⟨_, h1⟩
    obtain ⟨f1, hf1, hf1e⟩ := hL O r (c - 1) ka k1 hk1
    have hgf1 : g0r O r * f1 ∈ HB O r c ka := by
      have h3 := hB3 O r 1 (c - 1) (fun _ => 0) ka _ (hB4 O r).2 _ hf1
      have e1 : (1 : ℤ) + (c - 1) = c := by ring
      have e2 : ((fun _ : Fin r => (0 : ℤ)) + ka) = ka := by funext i; simp
      rw [e1, e2] at h3
      exact h3
    have hsub : f - g0r O r * f1 ∈ HB O r c ka := by
      have h4 := (hB2 O r c ka).2.1 _ hf _ ((hB2 O r c ka).2.2 (-1) _ hgf1)
      have e : f - g0r O r * f1 = f + algebraMap O (GLCoord O (r + 1)) (-1) * (g0r O r * f1) := by
        rw [map_neg, map_one]; ring
      rw [e]
      exact h4
    have hz : redG (IsLocalRing.residue O) (r + 1) (f - g0r O r * f1) = 0 := by
      rw [map_sub, map_mul, hρg, hf1e, ← hk1e, sub_self]
    obtain ⟨y, hy⟩ := hC3 O w hw (r + 1) _ hz
    have hyH : y ∈ HB O r c ka := kr_HB_of_smul O r c ka w hw.ne_zero y (hy ▸ hsub)
    apply ih y h hyH
    apply hC5 O r w _ hr hw.ne_zero
    refine ⟨k - f1, ?_⟩
    have e : algebraMap O (GLCoord O (r + 1)) w * (y - algebraMap O (GLCoord O (r + 1)) (w ^ m) * h) =
        (f - algebraMap O (GLCoord O (r + 1)) (w ^ (m + 1)) * h) - g0r O r * f1 := by
      rw [mul_sub, ← hy, pow_succ', map_mul]; ring
    rw [e, hk]; ring

theorem sizes_bound_of_log_estimates (D : Formalism.BasicNotions.D7) (hL : Lift) (hB2 : HBLin) (hB3 : HBMul) (hB4 : HBDet) (hC1 : RedBasic)
    (hC2 : RedHB) (hC3 : RedKer) (hC4 : TopRightDivisionDomain) (hC5 : TopRightCancelConstant) : Formalism.MainNotions.flipOneThree.adm5 D := by
  intro O _ _ _ r c ka f h a hr hf ha hd
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hw
  obtain ⟨f', hf', hd'⟩ := top_right_division_lift hL hB2 hB3 hB4 hC1 hC2 hC3 hC4 hC5 O r c ka hr w hw m f
    (algebraMap O (GLCoord O (r + 1)) (u : O) * h) hf (by
      have e : f - algebraMap O (GLCoord O (r + 1)) (w ^ m) * (algebraMap O (GLCoord O (r + 1)) (u : O) * h) =
          f - algebraMap O (GLCoord O (r + 1)) ((u : O) * w ^ m) * h := by
        rw [map_mul]; ring
      rw [e]; exact hd)
  refine ⟨algebraMap O (GLCoord O (r + 1)) ((u⁻¹ : Oˣ) : O) * f', (hB2 O r c ka).2.2 _ _ hf', ?_⟩
  have e : h - algebraMap O (GLCoord O (r + 1)) ((u⁻¹ : Oˣ) : O) * f' =
      algebraMap O (GLCoord O (r + 1)) ((u⁻¹ : Oˣ) : O) * (algebraMap O (GLCoord O (r + 1)) (u : O) * h - f') := by
    rw [mul_sub, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [e]
  exact Dvd.dvd.mul_left hd' _

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.GradedWeylDivisibility

def sC (k n : ℕ) (ν : Fin n → ℕ) : ℕ := Nat.card (ssIdx k n ν)

def BR : Prop :=
  ∀ (r : ℕ) (ν : Fin (r + 1) → ℕ),
    sC (r + 1) (r + 1) ν =
      ∑ μ ∈ Fintype.piFinset (fun t : Fin r => Finset.Icc (ν t.succ) (ν t.castSucc)), sC r r μ

def Shift : Prop :=
  ∀ (n : ℕ) (ν : Fin n → ℕ) (N : ℕ), sC n n (fun t => ν t + N) = sC n n ν

def Diff : Prop :=
  ∀ (r c : ℕ) (κ : Fin (r + 1) → ℕ), κ 0 ≤ c + 1 →
    sC (r + 2) (r + 2) (Fin.cons (c + 1) κ : Fin (r + 2) → ℕ) =
      sC (r + 2) (r + 2) (Fin.cons c κ : Fin (r + 2) → ℕ) +
        ∑ μ ∈ Fintype.piFinset (fun t : Fin r => Finset.Icc (κ t.succ) (κ t.castSucc)),
          sC (r + 1) (r + 1) (Fin.cons (c + 1) μ : Fin (r + 1) → ℕ)

def FinrankHB : Prop :=
  ∀ (K : Type) [Field K] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) (ν : Fin (r + 1) → ℕ) (N : ℤ),
    (ν 0 : ℤ) = c + N → (∀ i : Fin r, (ν i.succ : ℤ) = ka i + N) →
    Module.Finite K (Submodule.span K (HB K r c ka)) ∧
      Module.finrank K (Submodule.span K (HB K r c ka)) = sC (r + 1) (r + 1) ν

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open Formalism.GradedWeylDivisibility Finset

theorem sum_le_castSucc_eq {r : ℕ} (f : Fin (r + 1) → ℕ) (a : Fin r) :
    (∑ b : Fin (r + 1) with b ≤ a.castSucc, f b) = ∑ b : Fin r with b ≤ a, f b.castSucc := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  have h : ¬ (Fin.last r ≤ a.castSucc) := by
    rw [not_le]; exact Fin.castSucc_lt_last a
  simp [h, Fin.castSucc_le_castSucc_iff]

theorem sum_lt_castSucc_eq {r : ℕ} (f : Fin (r + 1) → ℕ) (a : Fin r) :
    (∑ b : Fin (r + 1) with b < a.castSucc, f b) = ∑ b : Fin r with b < a, f b.castSucc := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  have h : ¬ (Fin.last r < a.castSucc) := by
    rw [not_lt]; exact Fin.le_last _
  simp [h, Fin.castSucc_lt_castSucc_iff]

theorem sum_le_last_eq {r : ℕ} (f : Fin (r + 1) → ℕ) :
    (∑ b : Fin (r + 1) with b ≤ Fin.last r, f b) = ∑ b : Fin (r + 1), f b := by
  rw [Finset.filter_true_of_mem (fun b _ => Fin.le_last b)]

theorem sum_lt_last_eq_castSucc {r : ℕ} (f : Fin (r + 1) → ℕ) :
    (∑ b : Fin (r + 1) with b < Fin.last r, f b) = ∑ b : Fin r, f b.castSucc := by
  rw [Finset.sum_filter, Fin.sum_univ_castSucc]
  simp [Fin.castSucc_lt_last]

theorem interlaced_triangularity {k n : ℕ} (m : Fin k × Fin n →₀ ℕ) (hm : Interlaced m) :
    ∀ (i : ℕ) (a : Fin k) (t : Fin n), a.val = i → a.val < t.val →
      (∑ b : Fin k with b ≤ a, m (b, t)) = 0 := by
  intro i
  induction i with
  | zero =>
    intro a t ha hat
    have hl : t.val - 1 < n := by omega
    have h : (∑ b : Fin k with b ≤ a, m (b, t)) ≤ 0 + ∑ b : Fin k with b < a, m (b, (⟨t.val - 1, hl⟩ : Fin n)) :=
      hm ⟨t.val - 1, hl⟩ t (by simp only []; omega) a
    have he : (Finset.univ.filter fun b : Fin k => b < a) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ hb
      have : b.val < a.val := hb
      omega
    rw [he] at h
    simpa using h
  | succ i ih =>
    intro a t ha hat
    have hl : t.val - 1 < n := by omega
    have h : (∑ b : Fin k with b ≤ a, m (b, t)) ≤ 0 + ∑ b : Fin k with b < a, m (b, (⟨t.val - 1, hl⟩ : Fin n)) :=
      hm ⟨t.val - 1, hl⟩ t (by simp only []; omega) a
    have ha' : a.val - 1 < k := by omega
    have he : (Finset.univ.filter fun b : Fin k => b < a) =
        Finset.univ.filter fun b : Fin k => b ≤ (⟨a.val - 1, ha'⟩ : Fin k) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def]
      omega
    rw [he, ih ⟨a.val - 1, ha'⟩ ⟨t.val - 1, hl⟩ (by simp only []; omega) (by simp only []; omega)] at h
    simpa using h

def k5aMu {r : ℕ} (m : Fin (r + 1) × Fin (r + 1) →₀ ℕ) : Fin r → ℕ :=
  fun t => ∑ a : Fin r, m (a.castSucc, t.castSucc)

def k5aDown {r : ℕ} (m : Fin (r + 1) × Fin (r + 1) →₀ ℕ) : Fin r × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => m (x.1.castSucc, x.2.castSucc)

def k5aUpF {r : ℕ} (ν : Fin (r + 1) → ℕ) (μ : Fin r → ℕ) (m' : Fin r × Fin r →₀ ℕ) :
    Fin (r + 1) × Fin (r + 1) → ℕ :=
  fun x => Fin.lastCases (motive := fun _ => ℕ)
    (Fin.lastCases (motive := fun _ => ℕ) (ν (Fin.last r)) (fun t' => ν t'.castSucc - μ t') x.2)
    (fun a' => Fin.lastCases (motive := fun _ => ℕ) 0 (fun t' => m' (a', t')) x.2) x.1

def k5aUp {r : ℕ} (ν : Fin (r + 1) → ℕ) (μ : Fin r → ℕ) (m' : Fin r × Fin r →₀ ℕ) :
    Fin (r + 1) × Fin (r + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (k5aUpF ν μ m')

theorem k5aDown_apply {r : ℕ} (m : Fin (r + 1) × Fin (r + 1) →₀ ℕ) (a t : Fin r) :
    k5aDown m (a, t) = m (a.castSucc, t.castSucc) := by
  simp [k5aDown]

theorem k5aUp_ll {r : ℕ} (ν : Fin (r + 1) → ℕ) (μ : Fin r → ℕ) (m' : Fin r × Fin r →₀ ℕ) :
    k5aUp ν μ m' (Fin.last r, Fin.last r) = ν (Fin.last r) := by
  simp [k5aUp, k5aUpF]

theorem k5aUp_lc {r : ℕ} (ν : Fin (r + 1) → ℕ) (μ : Fin r → ℕ) (m' : Fin r × Fin r →₀ ℕ) (t : Fin r) :
    k5aUp ν μ m' (Fin.last r, t.castSucc) = ν t.castSucc - μ t := by
  simp [k5aUp, k5aUpF]

theorem k5aUp_cl {r : ℕ} (ν : Fin (r + 1) → ℕ) (μ : Fin r → ℕ) (m' : Fin r × Fin r →₀ ℕ) (a : Fin r) :
    k5aUp ν μ m' (a.castSucc, Fin.last r) = 0 := by
  simp [k5aUp, k5aUpF]

theorem k5aUp_cc {r : ℕ} (ν : Fin (r + 1) → ℕ) (μ : Fin r → ℕ) (m' : Fin r × Fin r →₀ ℕ) (a t : Fin r) :
    k5aUp ν μ m' (a.castSucc, t.castSucc) = m' (a, t) := by
  simp [k5aUp, k5aUpF]

theorem semistandard_column_sum_split {r : ℕ} {ν : Fin (r + 1) → ℕ} {m : Fin (r + 1) × Fin (r + 1) →₀ ℕ}
    (hm : m ∈ ssIdx (r + 1) (r + 1) ν) (t : Fin (r + 1)) :
    (∑ a : Fin r, m (a.castSucc, t)) + m (Fin.last r, t) = ν t := by
  rw [← hm.2 t, Fin.sum_univ_castSucc]

theorem semistandard_restrict_interlacing {r : ℕ} {ν : Fin (r + 1) → ℕ} {m : Fin (r + 1) × Fin (r + 1) →₀ ℕ}
    (hm : m ∈ ssIdx (r + 1) (r + 1) ν) :
    k5aMu m ∈ Fintype.piFinset (fun t : Fin r => Finset.Icc (ν t.succ) (ν t.castSucc)) ∧
      k5aDown m ∈ ssIdx r r (k5aMu m) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro t
    rw [Finset.mem_Icc]
    constructor
    · have h : (∑ b : Fin (r + 1) with b ≤ Fin.last r, m (b, t.succ)) ≤
          0 + ∑ b : Fin (r + 1) with b < Fin.last r, m (b, t.castSucc) :=
        hm.1 t.castSucc t.succ (by simp) (Fin.last r)
      rw [sum_le_last_eq (fun b => m (b, t.succ)), sum_lt_last_eq_castSucc (fun b => m (b, t.castSucc)),
        hm.2 t.succ, zero_add] at h
      exact h
    · have := semistandard_column_sum_split hm t.castSucc
      show (∑ a : Fin r, m (a.castSucc, t.castSucc)) ≤ ν t.castSucc
      omega
  · intro l j hj a
    have h : (∑ b : Fin (r + 1) with b ≤ a.castSucc, m (b, j.castSucc)) ≤
        0 + ∑ b : Fin (r + 1) with b < a.castSucc, m (b, l.castSucc) :=
      hm.1 l.castSucc j.castSucc (by simpa using hj) a.castSucc
    rw [sum_le_castSucc_eq (fun b => m (b, j.castSucc)), sum_lt_castSucc_eq (fun b => m (b, l.castSucc))] at h
    simpa only [k5aDown_apply] using h
  · intro t
    simp only [k5aDown_apply]
    rfl

theorem interlaced_up_mem {r : ℕ} {ν : Fin (r + 1) → ℕ} {μ : Fin r → ℕ} {m' : Fin r × Fin r →₀ ℕ}
    (hμ : μ ∈ Fintype.piFinset (fun t : Fin r => Finset.Icc (ν t.succ) (ν t.castSucc)))
    (hm' : m' ∈ ssIdx r r μ) : k5aUp ν μ m' ∈ ssIdx (r + 1) (r + 1) ν := by
  rw [Fintype.mem_piFinset] at hμ
  have hcol : ∀ t : Fin (r + 1), ∑ a : Fin (r + 1), k5aUp ν μ m' (a, t) = ν t := by
    intro t
    rw [Fin.sum_univ_castSucc]
    induction t using Fin.lastCases with
    | last => simp [k5aUp_cl, k5aUp_ll]
    | cast t' =>
      simp only [k5aUp_cc, k5aUp_lc]
      have h1 := hm'.2 t'
      have h2 := (Finset.mem_Icc.1 (hμ t')).2
      rw [h1]; omega
  refine ⟨?_, hcol⟩
  intro l j hj a
  have hl : l.val < r := by have := j.isLt; omega
  obtain ⟨l', rfl⟩ : ∃ l' : Fin r, l = l'.castSucc := ⟨⟨l.val, hl⟩, by ext; rfl⟩
  show (∑ b : Fin (r + 1) with b ≤ a, k5aUp ν μ m' (b, j)) ≤
    0 + ∑ b : Fin (r + 1) with b < a, k5aUp ν μ m' (b, l'.castSucc)
  induction a using Fin.lastCases with
  | last =>
    rw [sum_le_last_eq (fun b => k5aUp ν μ m' (b, j)),
      sum_lt_last_eq_castSucc (fun b => k5aUp ν μ m' (b, l'.castSucc)), hcol j, zero_add]
    simp only [k5aUp_cc]
    rw [hm'.2 l']
    have hj' : j = l'.succ := by ext; simpa using hj
    rw [hj']
    exact (Finset.mem_Icc.1 (hμ l')).1
  | cast a' =>
    rw [sum_le_castSucc_eq (fun b => k5aUp ν μ m' (b, j)),
      sum_lt_castSucc_eq (fun b => k5aUp ν μ m' (b, l'.castSucc))]
    simp only [k5aUp_cc]
    induction j using Fin.lastCases with
    | last => simp [k5aUp_cl]
    | cast j' =>
      simp only [k5aUp_cc]
      exact hm'.1 l' j' (by simpa using hj) a'

theorem interlaced_up_down_eq {r : ℕ} {ν : Fin (r + 1) → ℕ} {m : Fin (r + 1) × Fin (r + 1) →₀ ℕ}
    (hm : m ∈ ssIdx (r + 1) (r + 1) ν) : k5aUp ν (k5aMu m) (k5aDown m) = m := by
  have htri : ∀ a : Fin r, m (a.castSucc, Fin.last r) = 0 := by
    intro a
    have h := interlaced_triangularity m hm.1 _ a.castSucc (Fin.last r) rfl (by simp)
    rw [Finset.sum_eq_zero_iff] at h
    exact h a.castSucc (by simp)
  ext ⟨a, t⟩
  induction a using Fin.lastCases with
  | last =>
    induction t using Fin.lastCases with
    | last =>
      rw [k5aUp_ll]
      have := semistandard_column_sum_split hm (Fin.last r)
      simp only [htri, Finset.sum_const_zero, zero_add] at this
      exact this.symm
    | cast t' =>
      rw [k5aUp_lc]
      have := semistandard_column_sum_split hm t'.castSucc
      show ν t'.castSucc - (∑ a : Fin r, m (a.castSucc, t'.castSucc)) = _
      omega
  | cast a' =>
    induction t using Fin.lastCases with
    | last => rw [k5aUp_cl, htri]
    | cast t' => rw [k5aUp_cc, k5aDown_apply]

theorem semistandard_lift_restrict_weight {r : ℕ} (ν : Fin (r + 1) → ℕ) {μ : Fin r → ℕ} {m' : Fin r × Fin r →₀ ℕ}
    (hm' : m' ∈ ssIdx r r μ) : k5aMu (k5aUp ν μ m') = μ := by
  funext t
  show ∑ a : Fin r, k5aUp ν μ m' (a.castSucc, t.castSucc) = μ t
  simp only [k5aUp_cc]
  exact hm'.2 t

theorem interlaced_down_up_eq {r : ℕ} (ν : Fin (r + 1) → ℕ) (μ : Fin r → ℕ) (m' : Fin r × Fin r →₀ ℕ) :
    k5aDown (k5aUp ν μ m') = m' := by
  ext ⟨a, t⟩
  rw [k5aDown_apply, k5aUp_cc]

theorem straight_count_eq_card (k n : ℕ) (ν : Fin n → ℕ) : sC k n ν = (sSIdxFinite k n ν).toFinset.card := by
  rw [sC, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (sSIdxFinite k n ν)]

theorem br : BR := by
  intro r ν
  rw [straight_count_eq_card]
  simp_rw [straight_count_eq_card r r]
  rw [← Finset.card_sigma]
  refine Finset.card_nbij' (fun m => ⟨k5aMu m, k5aDown m⟩) (fun x => k5aUp ν x.1 x.2) ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hm
    have h := semistandard_restrict_interlacing hm
    rw [Finset.mem_coe, Finset.mem_sigma]
    exact ⟨h.1, (Set.Finite.mem_toFinset _).2 h.2⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_sigma] at hx
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact interlaced_up_mem hx.1 ((Set.Finite.mem_toFinset _).1 hx.2)
  · intro m hm
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hm
    exact interlaced_up_down_eq hm
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_sigma] at hx
    obtain ⟨μ, m'⟩ := x
    have h2 := (Set.Finite.mem_toFinset _).1 hx.2
    show (⟨k5aMu (k5aUp ν μ m'), k5aDown (k5aUp ν μ m')⟩ : Σ _ : Fin r → ℕ, (Fin r × Fin r →₀ ℕ)) = ⟨μ, m'⟩
    rw [semistandard_lift_restrict_weight ν h2, interlaced_down_up_eq]

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open Formalism.GradedWeylDivisibility

theorem straight_count_shift_eq (h : BR) : ∀ (n : ℕ) (ν : Fin n → ℕ), sC n n (fun t => ν t + 1) = sC n n ν := by
  intro n
  induction n with
  | zero =>
    intro ν
    congr 1
    funext t
    exact t.elim0
  | succ r ih =>
    intro ν
    rw [h r (fun t => ν t + 1), h r ν]
    symm
    refine Finset.sum_nbij' (fun μ t => μ t + 1) (fun μ t => μ t - 1) ?_ ?_ ?_ ?_ ?_
    · intro μ hμ
      simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hμ ⊢
      intro t
      have := hμ t
      omega
    · intro μ hμ
      simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hμ ⊢
      intro t
      have := hμ t
      omega
    · intro μ _
      funext t
      simp
    · intro μ hμ
      simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hμ
      funext t
      have := hμ t
      show μ t - 1 + 1 = μ t
      omega
    · intro μ _
      exact (ih μ).symm

theorem shift_of (h : BR) : Shift := by
  intro n ν N
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (fun t => ν t + (N + 1)) = fun t => (fun s => ν s + N) t + 1 := by
      funext t
      show ν t + (N + 1) = ν t + N + 1
      omega
    rw [e, straight_count_shift_eq h n (fun s => ν s + N), ih]

theorem sum_piFinset_cons {M : Type*} [AddCommMonoid M] (r : ℕ) (S : Fin (r + 1) → Finset ℕ)
    (F : (Fin (r + 1) → ℕ) → M) :
    ∑ μ ∈ Fintype.piFinset S, F μ =
      ∑ a ∈ S 0, ∑ μ' ∈ Fintype.piFinset (fun t : Fin r => S t.succ), F (Fin.cons a μ') := by
  first | exact Bl.SecondBlockLemmaF.goal1 .. | (apply Bl.SecondBlockLemmaF.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaF.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaF.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaF.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaF.goal1 <;> first | assumption | infer_instance)

theorem diff_of (h : BR) : Diff := by
  intro r c κ hκ
  have e1 : sC (r + 2) (r + 2) (Fin.cons (c + 1) κ : Fin (r + 2) → ℕ) = _ := h (r + 1) (Fin.cons (c + 1) κ)
  have e2 : sC (r + 2) (r + 2) (Fin.cons c κ : Fin (r + 2) → ℕ) = _ := h (r + 1) (Fin.cons c κ)
  rw [e1, e2, sum_piFinset_cons, sum_piFinset_cons]
  simp only [Fin.cons_succ, Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc]
  have hI : Finset.Icc (κ 0) (c + 1) = insert (c + 1) (Finset.Icc (κ 0) c) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hI, Finset.sum_insert (by simp), add_comm]

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.GradedWeylDivisibility

theorem mem_highest_weight_congr {R : Type} [CommRing R] {r : ℕ} {c c' : ℤ} {ka ka' : Fin r → ℤ} (hc : c = c')
    (hk : ka = ka') {f : GLCoord R (r + 1)} (h : f ∈ HB R r c ka) : f ∈ HB R r c' ka' := by
  subst hc hk; exact h

section

variable (K : Type) [Field K]

theorem coordinate_inclusion_injective_field (n : ℕ) : Function.Injective (io K n) := kr_GL_inj K n

theorem transpose_transpose_alt (n : ℕ) (P : MvPolynomial (Fin n × Fin n) K) : tr K n (tr K n P) = P := by
  simp [tr, rename_rename, Prod.swap_swap_eq]

def transposeInclusion (n : ℕ) : MvPolynomial (Fin n × Fin n) K →ₗ[K] GLCoord K n :=
  (IsScalarTower.toAlgHom K (MvPolynomial (Fin n × Fin n) K) (GLCoord K n)).toLinearMap ∘ₗ (tr K n).toLinearMap

theorem transposeInclusion_apply (n : ℕ) (P : MvPolynomial (Fin n × Fin n) K) : transposeInclusion K n P = io K n (tr K n P) := rfl

theorem polynomialInclusion_injective (n : ℕ) : Function.Injective (transposeInclusion K n) := by
  intro a b h
  have h1 : tr K n a = tr K n b := coordinate_inclusion_injective_field K n h
  have h2 := congrArg (tr K n) h1
  rwa [transpose_transpose_alt, transpose_transpose_alt] at h2

def dualWeylImage (n : ℕ) (ν : Fin n → ℕ) : Submodule K (GLCoord K n) := (dualWeyl K n n ν).map (transposeInclusion K n)

theorem dualWeyl_finrank (n : ℕ) (ν : Fin n → ℕ) :
    Module.Finite K (dualWeyl K n n ν) ∧ Module.finrank K (dualWeyl K n n ν) = sC n n ν := by
  obtain ⟨b, ⟨hli, hspan, -⟩, -⟩ := sSBasis K n n ν
  have : Finite (ssIdx n n ν) := (sSIdxFinite n n ν).to_subtype
  have : Fintype (ssIdx n n ν) := Fintype.ofFinite _
  rw [← hspan]
  refine ⟨FiniteDimensional.span_of_finite K (Set.finite_range b), ?_⟩
  rw [finrank_span_eq_card hli, sC, Nat.card_eq_fintype_card]

theorem dualWeylImage_finrank (n : ℕ) (ν : Fin n → ℕ) :
    Module.Finite K (dualWeylImage K n ν) ∧ Module.finrank K (dualWeylImage K n ν) = sC n n ν := by
  obtain ⟨h1, h2⟩ := dualWeyl_finrank K n ν
  have e := Submodule.equivMapOfInjective (transposeInclusion K n) (polynomialInclusion_injective K n) (dualWeyl K n n ν)
  unfold dualWeylImage
  exact ⟨Module.Finite.equiv e, by rw [← h2]; exact e.finrank_eq.symm⟩

theorem finrank_map_mul_unit {n : ℕ} (v : (GLCoord K n)ˣ) (S : Submodule K (GLCoord K n)) [Module.Finite K S] :
    Module.Finite K (S.map (LinearMap.mulLeft K (v : GLCoord K n))) ∧
      Module.finrank K (S.map (LinearMap.mulLeft K (v : GLCoord K n))) = Module.finrank K S := by
  have hinj : Function.Injective (LinearMap.mulLeft K (v : GLCoord K n)) := fun a b h =>
    (Units.mul_right_inj v).1 h
  have e := Submodule.equivMapOfInjective _ hinj S
  exact ⟨Module.Finite.equiv e, e.finrank_eq.symm⟩

theorem det_unit_natPow_eq (n M : ℕ) :
    ((detU K n ^ (M : ℤ) : (GLCoord K n)ˣ) : GLCoord K n) = io K n ((genMat K n).det ^ M) := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  rfl

def highestWeightSubmodule (hB2 : HBLin) (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) : Submodule K (GLCoord K (r + 1)) where
  carrier := HB K r c ka
  add_mem' := fun {a b} ha hb => (hB2 K r c ka).2.1 a ha b hb
  zero_mem' := (hB2 K r c ka).1
  smul_mem' := fun a f hf => by
    rw [Algebra.smul_def]
    exact (hB2 K r c ka).2.2 a f hf

theorem dualWeylImage_le_highest_weight (hB1 : BideterminantInHighestWeight) (hB2 : HBLin) (r : ℕ) (ν : Fin (r + 1) → ℕ) :
    ∀ x ∈ dualWeylImage K (r + 1) ν, x ∈ HB K r (ν 0) (fun i => ν i.succ) := by
  have key : dualWeyl K (r + 1) (r + 1) ν ≤
      (highestWeightSubmodule K hB2 r (ν 0) (fun i => ν i.succ)).comap (transposeInclusion K (r + 1)) := by
    rw [standardMonomialSpanDomain K (r + 1) (r + 1) ν, Submodule.span_le]
    rintro f ⟨Kk, sz, hsz, I, hshape, rfl⟩
    subst hshape
    exact hB1 K r Kk sz hsz I
  rintro x ⟨Q, hQ, rfl⟩
  exact key hQ

theorem polynomial_mem_weight_space (hA : PolyHB) (r : ℕ) (ν : Fin (r + 1) → ℕ) (P : MvPolynomial (Fin (r + 1) × Fin (r + 1)) K)
    (h : io K (r + 1) P ∈ HB K r (ν 0) (fun i => ν i.succ)) : io K (r + 1) P ∈ dualWeylImage K (r + 1) ν :=
  ⟨tr K (r + 1) P, hA K r ν P h, by rw [transposeInclusion_apply, transpose_transpose_alt]⟩

theorem det_pow_mul_mem_shift (hB3 : HBMul) (hB4 : HBDet) (r : ℕ) (c c' N : ℤ) (ka ka' : Fin r → ℤ)
    (h0 : c' = c + N) (hs : ∀ i, ka' i = ka i + N) (f : GLCoord K (r + 1)) (hf : f ∈ HB K r c ka) :
    ((detU K (r + 1) ^ N : (GLCoord K (r + 1))ˣ) : GLCoord K (r + 1)) * f ∈ HB K r c' ka' := by
  refine mem_highest_weight_congr ?_ ?_ (hB3 K r _ _ _ _ _ ((hB4 K r).1 N) _ hf)
  · rw [h0]; ring
  · funext i
    rw [hs i]
    simp [add_comm]

theorem dualWeylImage_det_shift (hA : PolyHB) (hB1 : BideterminantInHighestWeight) (hB2 : HBLin) (hB3 : HBMul) (hB4 : HBDet) (hS : Shift)
    (r : ℕ) (ν : Fin (r + 1) → ℕ) (M : ℕ) :
    (dualWeylImage K (r + 1) ν).map
        (LinearMap.mulLeft K ((detU K (r + 1) ^ (M : ℤ) : (GLCoord K (r + 1))ˣ) : GLCoord K (r + 1))) =
      dualWeylImage K (r + 1) (fun t => ν t + M) := by
  have := (dualWeylImage_finrank K (r + 1) ν).1
  have := (dualWeylImage_finrank K (r + 1) (fun t => ν t + M)).1
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := dualWeylImage_le_highest_weight K hB1 hB2 r ν x hx
    obtain ⟨Q, hQ, rfl⟩ := hx
    have hm := det_pow_mul_mem_shift K hB3 hB4 r (ν 0) ((fun t => ν t + M) 0 : ℕ) (M : ℤ) (fun i => ν i.succ)
      (fun i => ((fun t => ν t + M) i.succ : ℕ)) (by push_cast; ring) (fun i => by push_cast; ring) _ hx'
    rw [LinearMap.mulLeft_apply]
    rw [det_unit_natPow_eq, transposeInclusion_apply, ← map_mul] at hm ⊢
    exact polynomial_mem_weight_space K hA r _ _ hm
  · rw [(finrank_map_mul_unit K _ _).2, (dualWeylImage_finrank K _ ν).2, (dualWeylImage_finrank K _ _).2]
    exact (hS _ ν M).symm

theorem det_pow_mul_mem_dualWeyl (hA : PolyHB) (hB1 : BideterminantInHighestWeight) (hB2 : HBLin) (hB3 : HBMul) (hB4 : HBDet) (hS : Shift)
    (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) (ν : Fin (r + 1) → ℕ) (N : ℤ)
    (h0 : (ν 0 : ℤ) = c + N) (hs : ∀ i : Fin r, (ν i.succ : ℤ) = ka i + N)
    (f : GLCoord K (r + 1)) (hf : f ∈ HB K r c ka) :
    ((detU K (r + 1) ^ N : (GLCoord K (r + 1))ˣ) : GLCoord K (r + 1)) * f ∈ dualWeylImage K (r + 1) ν := by
  obtain ⟨M', P, hP⟩ := IsLocalization.Away.surj (genMat K (r + 1)).det f
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = N + N.natAbs := ⟨(N + N.natAbs).toNat, by omega⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = M' + N.natAbs := ⟨_, rfl⟩
  have hg := det_pow_mul_mem_shift K hB3 hB4 r c (ν 0) N ka (fun i => ν i.succ) h0 hs f hf
  have hgM := det_pow_mul_mem_shift K hB3 hB4 r (ν 0) ((fun t => ν t + M) 0 : ℕ) (M : ℤ) (fun i => ν i.succ)
      (fun i => ((fun t => ν t + M) i.succ : ℕ)) (by push_cast; ring) (fun i => by push_cast; ring) _ hg
  have hu : (detU K (r + 1) ^ (M : ℤ) * detU K (r + 1) ^ N : (GLCoord K (r + 1))ˣ) =
      detU K (r + 1) ^ (M' : ℤ) * detU K (r + 1) ^ (e : ℤ) := by
    rw [← zpow_add, ← zpow_add]
    congr 1
    omega
  have hpoly : ((detU K (r + 1) ^ (M : ℤ) : (GLCoord K (r + 1))ˣ) : GLCoord K (r + 1)) *
      (((detU K (r + 1) ^ N : (GLCoord K (r + 1))ˣ) : GLCoord K (r + 1)) * f) =
      io K (r + 1) (P * (genMat K (r + 1)).det ^ e) := by
    rw [← mul_assoc, ← Units.val_mul, hu, Units.val_mul, det_unit_natPow_eq, det_unit_natPow_eq, map_mul, ← hP, map_pow, map_pow]
    ring
  rw [hpoly] at hgM
  have hW := polynomial_mem_weight_space K hA r (fun t => ν t + M) _ hgM
  rw [← hpoly, ← dualWeylImage_det_shift K hA hB1 hB2 hB3 hB4 hS r ν M] at hW
  obtain ⟨y, hy, hyeq⟩ := hW
  have hy2 : y = ((detU K (r + 1) ^ N : (GLCoord K (r + 1))ˣ) : GLCoord K (r + 1)) * f :=
    (Units.mul_right_inj _).1 hyeq
  rwa [← hy2]

end

theorem finrankHB_of (hA : PolyHB) (hB1 : BideterminantInHighestWeight) (hB2 : HBLin) (hB3 : HBMul) (hB4 : HBDet) (hS : Shift) :
    FinrankHB := by
  intro K _ r c ka ν N h0 hs
  have e : Submodule.span K (HB K r c ka) = (dualWeylImage K (r + 1) ν).map
      (LinearMap.mulLeft K ((detU K (r + 1) ^ (-N) : (GLCoord K (r + 1))ˣ) : GLCoord K (r + 1))) := by
    have h1 : Submodule.span K (HB K r c ka) = highestWeightSubmodule K hB2 r c ka := Submodule.span_eq (highestWeightSubmodule K hB2 r c ka)
    rw [h1]
    apply le_antisymm
    · intro f hf
      refine ⟨_, det_pow_mul_mem_dualWeyl K hA hB1 hB2 hB3 hB4 hS r c ka ν N h0 hs f hf, ?_⟩
      rw [LinearMap.mulLeft_apply, ← mul_assoc, ← Units.val_mul, ← zpow_add]
      simp
    · rintro _ ⟨y, hy, rfl⟩
      have hy' := dualWeylImage_le_highest_weight K hB1 hB2 r ν y hy
      exact det_pow_mul_mem_shift K hB3 hB4 r (ν 0) c (-N) (fun i => ν i.succ) ka (by rw [h0]; ring)
        (fun i => by rw [hs i]; ring) y hy'
  have := (dualWeylImage_finrank K (r + 1) ν).1
  rw [e]
  exact ⟨(finrank_map_mul_unit K _ _).1, by rw [(finrank_map_mul_unit K _ _).2, (dualWeylImage_finrank K _ ν).2]⟩

end Formalism.MainNotions.G.Joints.KP

end

noncomputable section

namespace Formalism.MainNotions.G.Joints.KP

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction Formalism.GradedWeylDivisibility

theorem mem_span_highest_weight_iff (hB2 : HBLin) {K : Type} [Field K] {r : ℕ} {c : ℤ} {ka : Fin r → ℤ}
    {x : GLCoord K (r + 1)} : x ∈ Submodule.span K (HB K r c ka) ↔ x ∈ HB K r c ka := by
  obtain ⟨h0, hadd, hsm⟩ := hB2 K r c ka
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x h => exact h
    | zero => exact h0
    | add x y _ _ hx hy => exact hadd x hx y hy
    | smul a x _ hx => rw [Algebra.smul_def]; exact hsm a x hx
  · exact fun h => Submodule.subset_span h

theorem top_right_ne_zero (K : Type) [Field K] (r : ℕ) : g0r K r ≠ 0 := by
  intro h
  exact X_ne_zero (R := K) _ (kr_GL_inj K (r + 1) (h.trans (map_zero _).symm))

theorem finrank_quotient_add_eq (hC4 : TopRightDivisionDomain) (hB2 : HBLin) (hB3 : HBMul) (hB4 : HBDet)
    (K : Type) [Field K] (r : ℕ) (c : ℤ) (ka : Fin r → ℤ) (h1 : 1 ≤ r)
    (hfin : Module.Finite K (Submodule.span K (HB K r c ka))) :
    Module.finrank K (Submodule.span K ((Ideal.Quotient.mk (Ideal.span {g0r K r})) '' HB K r c ka)) +
      Module.finrank K (Submodule.span K (HB K r (c - 1) ka)) =
    Module.finrank K (Submodule.span K (HB K r c ka)) := by
  obtain ⟨H, hH⟩ : ∃ H, H = Submodule.span K (HB K r c ka) := ⟨_, rfl⟩
  obtain ⟨H1, hH1⟩ : ∃ H1, H1 = Submodule.span K (HB K r (c - 1) ka) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : GLCoord K (r + 1) →ₗ[K] (GLCoord K (r + 1) ⧸ Ideal.span {g0r K r}),
      ∀ x, L x = Ideal.Quotient.mk (Ideal.span {g0r K r}) x :=
    ⟨(Ideal.Quotient.mkₐ K (Ideal.span {g0r K r})).toLinearMap, fun _ => rfl⟩
  have hmap : Submodule.span K ((Ideal.Quotient.mk (Ideal.span {g0r K r})) '' HB K r c ka) = H.map L := by
    rw [hH, Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, hL]
  have hker : (LinearMap.ker (L.domRestrict H)).map H.subtype =
      H1.map (LinearMap.mulLeft K (g0r K r)) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.subtype_apply,
      LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨⟨y, hy⟩, hy0, rfl⟩
      have hd : g0r K r ∣ y := by
        have h0 : (Ideal.Quotient.mk (Ideal.span {g0r K r})) y = 0 := by rw [← hL]; exact hy0
        rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
      rw [hH] at hy
      obtain ⟨f1, hf1, e⟩ := hC4 K r c ka y h1 ((mem_span_highest_weight_iff hB2).1 hy) hd
      exact ⟨f1, by rw [hH1]; exact (mem_span_highest_weight_iff hB2).2 hf1, e.symm⟩
    · rintro ⟨f1, hf1, rfl⟩
      rw [hH1] at hf1
      have hm : g0r K r * f1 ∈ HB K r c ka := by
        have h2 := hB3 K r 1 (c - 1) (fun _ => 0) ka _ (hB4 K r).2 f1 ((mem_span_highest_weight_iff hB2).1 hf1)
        have e1 : (1 : ℤ) + (c - 1) = c := by ring
        have e2 : (fun _ => 0 : Fin r → ℤ) + ka = ka := by funext i; simp
        rwa [e1, e2] at h2
      refine ⟨⟨_, by rw [hH]; exact (mem_span_highest_weight_iff hB2).2 hm⟩, ?_, rfl⟩
      rw [hL, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact Dvd.intro _ rfl
  have : Module.Finite K H := by rw [hH]; exact hfin
  have hinj : Function.Injective (LinearMap.mulLeft K (g0r K r)) := by
    intro a b h
    have h' : g0r K r * a = g0r K r * b := h
    exact mul_left_cancel₀ (top_right_ne_zero K r) h'
  have hr := LinearMap.finrank_range_add_finrank_ker (L.domRestrict H)
  rw [LinearMap.range_domRestrict] at hr
  have e1 : Module.finrank K (LinearMap.ker (L.domRestrict H)) = Module.finrank K H1 := by
    rw [(Submodule.equivMapOfInjective H.subtype H.injective_subtype _).finrank_eq, hker,
      ← (Submodule.equivMapOfInjective _ hinj H1).finrank_eq]
  rw [hmap, ← hH, ← hH1, ← e1]
  exact hr

theorem exists_shift_nonneg {r : ℕ} (c : ℤ) (ka : Fin r → ℤ) : ∃ N : ℕ, 0 ≤ c - 1 + N ∧ ∀ i, 0 ≤ ka i + N := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, (ka i).natAbs := ⟨_, rfl⟩
  refine ⟨(c - 1).natAbs + S, by omega, fun i => ?_⟩
  have hi : (ka i).natAbs ≤ S := by
    rw [hS]
    exact Finset.single_le_sum (f := fun i => (ka i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem sum_finrank_shifted_eq (hF : FinrankHB) (K : Type) [Field K] (r : ℕ) (c : ℤ) (N : ℕ) (lo hi : Fin r → ℤ)
    (hlo : ∀ t, 0 ≤ lo t + N) (hhi : ∀ t, 0 ≤ hi t + N) (hcN : 0 ≤ c + N) :
    ∑ ka' ∈ Fintype.piFinset (fun i : Fin r => Finset.Icc (lo i) (hi i)),
        Module.finrank K (Submodule.span K (HB K r c ka')) =
      ∑ μ ∈ Fintype.piFinset (fun t : Fin r => Finset.Icc (lo t + N).toNat (hi t + N).toNat),
        sC (r + 1) (r + 1) (Fin.cons (c + N).toNat μ : Fin (r + 1) → ℕ) := by
  refine Finset.sum_bij' (fun ka' _ => fun t => (ka' t + N).toNat) (fun μ _ => fun t => (μ t : ℤ) - N)
    ?_ ?_ ?_ ?_ ?_
  · intro ka' h
    rw [Fintype.mem_piFinset] at h ⊢
    intro t
    have := h t
    rw [Finset.mem_Icc] at this ⊢
    have := hlo t
    have := hhi t
    omega
  · intro μ h
    rw [Fintype.mem_piFinset] at h ⊢
    intro t
    have := h t
    rw [Finset.mem_Icc] at this ⊢
    have := hlo t
    have := hhi t
    omega
  · intro ka' h
    rw [Fintype.mem_piFinset] at h
    funext t
    have := h t
    rw [Finset.mem_Icc] at this
    have := hlo t
    show (((ka' t + N).toNat : ℕ) : ℤ) - N = ka' t
    omega
  · intro μ h
    funext t
    show ((μ t : ℤ) - N + N).toNat = μ t
    omega
  · intro ka' h
    rw [Fintype.mem_piFinset] at h
    refine (hF K r c ka' _ N ?_ ?_).2
    · rw [Fin.cons_zero]; omega
    · intro i
      rw [Fin.cons_succ]
      have := h i
      rw [Finset.mem_Icc] at this
      have := hlo i
      omega

theorem restriction_dimension_of_division (D : Formalism.BasicNotions.D7) (hC4 : TopRightDivisionDomain) (hB2 : HBLin) (hB3 : HBMul) (hB4 : HBDet) (hF : FinrankHB)
    (hD : Diff) : Formalism.MainNotions.flipOneThree.adm6 D := by
  intro K _ _ r c ka h1 hc
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨N, hN1, hN2⟩ := exists_shift_nonneg c ka
  have hc' : ka 0 ≤ c := hc
  obtain ⟨κ, hκ⟩ : ∃ κ : Fin (r' + 1) → ℕ, ∀ i, κ i = (ka i + N).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℕ, c0 = (c - 1 + N).toNat := ⟨_, rfl⟩
  have hFc := hF K (r' + 1) c ka (Fin.cons (c0 + 1) κ) N (by rw [Fin.cons_zero]; omega)
    (by intro i; rw [Fin.cons_succ, hκ]; have := hN2 i; omega)
  have hFc1 := hF K (r' + 1) (c - 1) ka (Fin.cons c0 κ) N (by rw [Fin.cons_zero]; omega)
    (by intro i; rw [Fin.cons_succ, hκ]; have := hN2 i; omega)
  have hfirst := finrank_quotient_add_eq hC4 hB2 hB3 hB4 K (r' + 1) c ka h1 hFc.1
  refine ⟨hfirst, ?_⟩
  have hd := hD r' c0 κ (by rw [hκ]; have := hN2 0; omega)
  have hs := sum_finrank_shifted_eq hF K r' c N (fun i => ka i.succ) (fun i => ka i.castSucc) (fun t => hN2 _) (fun t => hN2 _)
    (by omega)
  have e0 : (c + N).toNat = c0 + 1 := by omega
  rw [e0] at hs
  simp only [← hκ] at hs
  have key := hfirst
  rw [hFc.2, hFc1.2] at key
  have key2 := Nat.add_right_cancel (key.trans (hd.trans (Nat.add_comm _ _)))
  exact key2.trans hs.symm

end Formalism.MainNotions.G.Joints.KP

end

namespace Formalism.MainNotions.G.Joints.KP

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem lattice_count_of_highest_weight (D : Formalism.BasicNotions.D7) (hA : PolyHB) (hB1 : BideterminantInHighestWeight) (hB2 : HBLin) (hB3 : HBMul) (hB4 : HBDet)
    (hC4 : TopRightDivisionDomain) : Formalism.MainNotions.flipOneThree.adm6 D :=
  restriction_dimension_of_division D hC4 hB2 hB3 hB4 (finrankHB_of hA hB1 hB2 hB3 hB4 (shift_of br)) (diff_of br)

end Formalism.MainNotions.G.Joints.KP

namespace Formalism.MainNotions.G.Joints

open KP

theorem kp_lift : Lift := lift_of polyHB bidetHB hbLin hbMul hbDet redBasic

theorem saturated_restriction_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.flipOneThree.adm5 D :=
  sizes_bound_of_log_estimates D kp_lift hbLin hbMul hbDet redBasic redHB redKer kp1Dom g0rCancel

end Formalism.MainNotions.G.Joints

namespace Formalism.MainNotions.G.Joints

open KP

theorem restriction_dimension_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.flipOneThree.adm6 D :=
  lattice_count_of_highest_weight D polyHB bidetHB hbLin hbMul hbDet kp1Dom

end Formalism.MainNotions.G.Joints
