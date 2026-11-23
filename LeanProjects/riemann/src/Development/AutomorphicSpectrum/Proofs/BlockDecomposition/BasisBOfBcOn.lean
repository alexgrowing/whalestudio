import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverFieldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZKApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPullBasisFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientFiltrationBijectiveOfCoverStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.BasisBase
universe w w'

theorem gr_decomp {K B : Type} [CommRing K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ)
    (S : GrSplit K γ m) :
    (∀ b : B, ∃ n : ∀ i, S.N i, b = ∑ i, S.ν i (n i)) ∧ ∀ n : ∀ i, S.N i, ∑ i, S.ν i (n i) = 0 → n = 0 := by
  have anti : ∀ {a b : ℕ}, a ≤ b → pdP γ b ≤ pdP γ a := fun h =>
    Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩
  constructor
  · have key : ∀ d, d ≤ m → ∀ x ∈ pdP γ (m - d), ∃ n : ∀ i, S.N i, x = ∑ i, S.ν i (n i) := by
      intro d
      induction d with
      | zero =>
        intro _ x hx
        rw [Nat.sub_zero, S.nil] at hx
        exact ⟨0, by simpa using Ideal.mem_bot.1 hx⟩
      | succ d ih =>
        intro hd x hx
        let i0 : Fin m := ⟨m - (d + 1), by omega⟩
        obtain ⟨n0, hn0⟩ := S.surj i0 x hx
        have e : (i0 : ℕ) + 1 = m - d := by simp only [i0]; omega
        rw [e] at hn0
        obtain ⟨n, hn⟩ := ih (by omega) _ hn0
        refine ⟨n + Pi.single i0 n0, ?_⟩
        have h1 : ∑ i, S.ν i ((Pi.single i0 n0 : ∀ i, S.N i) i) = S.ν i0 n0 := by
          rw [Finset.sum_eq_single i0]
          · simp
          · intro b _ hb
            simp [Pi.single_eq_of_ne hb]
          · simp
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib, h1, ← hn]
        ring
    intro b
    refine key m le_rfl b ?_
    have : pdP γ (m - m) = ⊤ := by
      rw [Nat.sub_self, Ideal.eq_top_iff_one]
      exact Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
    rw [this]; trivial
  · intro n hn
    have key : ∀ k, ∀ i : Fin m, (i : ℕ) < k → n i = 0 := by
      intro k
      induction k with
      | zero => intro i hi; omega
      | succ k ih =>
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact ih i h
        · have h2 : S.ν i (n i) = - ∑ b ∈ Finset.univ.erase i, S.ν b (n b) := by
            rw [eq_neg_iff_add_eq_zero, add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
            exact hn
          refine S.inj i _ ?_
          rw [h2]
          refine Ideal.neg_mem_iff _ |>.2 (Ideal.sum_mem _ fun b hb => ?_)
          have hbi : b ≠ i := Finset.ne_of_mem_erase hb
          rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hbi) with h3 | h3
          · rw [ih b (by omega), map_zero]
            exact Ideal.zero_mem _
          · exact anti (by omega) (S.mem b _)
    funext i
    exact key _ i (Nat.lt_succ_self _)

theorem tens_dual {K N V : Type*} {M : Type w} [Field K] [AddCommGroup N] [Module K N] [AddCommGroup V] [Module K V]
    [AddCommGroup M] [Module K M] (e : V →ₗ[K] M) (φ : V →ₗ[K] K) (h : ∀ x, e x = 0 → φ x = 0) {a : ℕ}
    (n : Fin a → N) (b : Fin a → V) (hz : ∑ t, n t ⊗ₜ[K] e (b t) = 0) : ∑ t, φ (b t) • n t = 0 := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend
    (((LinearMap.ker e).liftQ φ fun x hx => h x hx).comp e.quotKerEquivRange.symm.toLinearMap)
  have h1 : ∀ x, ψ (e x) = φ x := by
    intro x
    have := LinearMap.congr_fun hψ ⟨e x, LinearMap.mem_range_self e x⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this]
    have h2 : e.quotKerEquivRange.symm ⟨e x, LinearMap.mem_range_self e x⟩ = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp [h2]
  have := congrArg (fun z => TensorProduct.rid K N (LinearMap.lTensor N ψ z)) hz
  simpa [map_sum, h1] using this

theorem tens_span {K N V : Type*} {M : Type w} [Field K] [AddCommGroup N] [Module K N] [AddCommGroup V] [Module K V]
    [AddCommGroup M] [Module K M] (e : V →ₗ[K] M) (he : Function.Surjective e) {a : ℕ} (bs : Module.Basis (Fin a) K V)
    (z : N ⊗[K] M) : ∃ n : Fin a → N, z = ∑ t, n t ⊗ₜ[K] e (bs t) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul x y =>
    obtain ⟨v, rfl⟩ := he y
    refine ⟨fun t => bs.repr v t • x, ?_⟩
    conv_lhs => rw [← bs.sum_repr v]
    rw [map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨n', rfl⟩ := hy
    exact ⟨n + n', by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩

theorem core_expand {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} {γ : DividedPowers I} {m : ℕ}
    (S : GrSplit K γ m) {V : Type w'} [AddCommGroup V] [Module K V] {W : Type w'} {Y : Type w'} [AddCommGroup W] [Module B W]
    [AddCommGroup Y] {M : Fin m → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (e : ∀ i, V →ₗ[K] M i) (μ : V → W) (qo : W →+ Y) {f : ∀ i, S.N i → M i → Y}
    (G : (∀ i, S.N i ⊗[K] M i) ≃+ Y) (hG : ∀ i n x, G (Pi.single i (n ⊗ₜ x)) = f i n x)
    (hf : ∀ i n x, f i n (e i x) = qo (S.ν i n • μ x)) {a : ℕ} (b : Fin a → V) (n : ∀ i, Fin a → S.N i) :
    qo (∑ t, (∑ i, S.ν i (n i t)) • μ (b t)) = G fun i => ∑ t, n i t ⊗ₜ[K] e i (b t) := by
  have h1 : (fun i => ∑ t, n i t ⊗ₜ[K] e i (b t)) =
      ∑ t, ∑ i, (Pi.single i (n i t ⊗ₜ[K] e i (b t)) : ∀ i, S.N i ⊗[K] M i) := by
    funext i
    simp only [Finset.sum_apply, Pi.single_apply]
    simp
  rw [h1, map_sum]
  simp only [map_sum, hG, hf, Finset.sum_smul]

theorem dividedPowerFiltration_anti' {B : Type} [CommRing B] {I : Ideal B} (γ : DividedPowers I) {a b : ℕ} (h : a ≤ b) :
    pdP γ b ≤ pdP γ a :=
  Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩

theorem core_basis {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} {γ : DividedPowers I} {m : ℕ}
    (S : GrSplit K γ m) {V : Type w'} [AddCommGroup V] [Module K V] {W : Type w'} {Y : Type w'} [AddCommGroup W] [Module B W]
    [AddCommGroup Y] {M : Fin m → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (e : ∀ i, V →ₗ[K] M i) (μ : V → W) (qo : W →+ Y) {f : ∀ i, S.N i → M i → Y}
    (hT : Tens K f) (hf : ∀ i n x, f i n (e i x) = qo (S.ν i n • μ x)) {a : ℕ} (bs : Module.Basis (Fin a) K V)
    (he : ∀ i, Function.Bijective (e i)) (hq : Function.Bijective qo) (w : W) :
    ∃! g : Fin a → B, w = ∑ t, g t • μ (bs t) := by
  obtain ⟨G, hG⟩ := hT
  have uniq : ∀ g : Fin a → B, ∑ t, g t • μ (bs t) = 0 → g = 0 := by
    intro g hg0
    choose n hn using fun t => (gr_decomp γ m S).1 (g t)
    have h1 := core_expand S e μ qo G hG hf (⇑bs) (fun i t => n t i)
    have hsum : (∑ t, (∑ i, S.ν i (n t i)) • μ (bs t)) = 0 := by
      rw [← hg0]; exact Finset.sum_congr rfl fun t _ => by rw [← hn t]
    rw [hsum, map_zero] at h1
    have h2 : (fun i => ∑ t, n t i ⊗ₜ[K] e i (bs t)) = 0 := G.injective (by rw [← h1, map_zero])
    have h3 : ∀ i t', n t' i = 0 := by
      intro i t'
      have hz := congrFun h2 i
      have := tens_dual (e i) (bs.coord t') (fun x hx => by
        rw [(he i).1 (hx.trans (map_zero _).symm)]; simp) (fun t => n t i) (⇑bs) hz
      simpa [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] using this
    funext t
    rw [hn t]
    simp [h3]
  have ex : ∃ g : Fin a → B, w = ∑ t, g t • μ (bs t) := by
    have hz : ∀ i, ∃ n : Fin a → S.N i, G.symm (qo w) i = ∑ t, n t ⊗ₜ[K] e i (bs t) :=
      fun i => tens_span (e i) (he i).2 bs _
    choose n hn using hz
    refine ⟨fun t => ∑ i, S.ν i (n i t), hq.1 ?_⟩
    rw [core_expand S e μ qo G hG hf (⇑bs) n]
    have : (fun i => ∑ t, n i t ⊗ₜ[K] e i (bs t)) = G.symm (qo w) := funext fun i => (hn i).symm
    rw [this, G.apply_symm_apply]
  obtain ⟨g, hg⟩ := ex
  refine ⟨g, hg, fun g' hg' => ?_⟩
  have := uniq (g' - g) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hg, ← hg', sub_self])
  exact sub_eq_zero.1 this

theorem core_filt {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} {γ : DividedPowers I} {m : ℕ}
    (S : GrSplit K γ m) {V : Type w'} [AddCommGroup V] [Module K V] {W : Type w'} {Y : Type w'} [AddCommGroup W] [Module B W]
    [AddCommGroup Y] {M : Fin m → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (e : ∀ i, V →ₗ[K] M i) (μ : V → W) (qo : W →+ Y) {f : ∀ i, S.N i → M i → Y}
    (hT : Tens K f) (hf : ∀ i n x, f i n (e i x) = qo (S.ν i n • μ x)) {a : ℕ} (bs : Fin a → V)
    (φ : V →ₗ[K] K) (k : ℕ) (hk : ∀ i : Fin m, k ≤ (i : ℕ) ∨ ∀ x, e i x = 0 → φ x = 0)
    (g : Fin a → B) (hg : qo (∑ t, g t • μ (bs t)) = 0) :
    ∑ t, g t * algebraMap K B (φ (bs t)) ∈ pdP γ k := by
  obtain ⟨G, hG⟩ := hT
  choose n hn using fun t => (gr_decomp γ m S).1 (g t)
  have h1 := core_expand S e μ qo G hG hf bs (fun i t => n t i)
  have hsum : (∑ t, (∑ i, S.ν i (n t i)) • μ (bs t)) = ∑ t, g t • μ (bs t) :=
    Finset.sum_congr rfl fun t _ => by rw [← hn t]
  rw [hsum, hg] at h1
  have h2 : (fun i => ∑ t, n t i ⊗ₜ[K] e i (bs t)) = 0 := G.injective (by rw [← h1, map_zero])
  have key : ∑ t, g t * algebraMap K B (φ (bs t)) =
      ∑ i, ∑ t, S.ν i (n t i) * algebraMap K B (φ (bs t)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hn t, Finset.sum_mul]
  rw [key]
  refine Ideal.sum_mem _ fun i _ => ?_
  rcases hk i with hki | hki
  · exact Ideal.sum_mem _ fun t _ => Ideal.mul_mem_right _ _ (dividedPowerFiltration_anti' γ hki (S.mem i _))
  · have h4 := tens_dual (e i) φ hki (fun t => n t i) bs (congrFun h2 i)
    have h3 := congrArg (S.ν i) h4
    rw [map_sum, map_zero] at h3
    have h5 : ∑ t, S.ν i (n t i) * algebraMap K B (φ (bs t)) = 0 := by
      rw [← h3]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smul, Algebra.smul_def, mul_comm]
    rw [h5]
    exact Ideal.zero_mem _

theorem transport_gen {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}
    (a a' b : IdF A) (e : a = a') (ha : ∀ T, a.S T = ⊤) (ha' : ∀ T, a'.S T = ⊤) (j : ℕ) :
    ∃ E : CH.H (sq a b) j ≃+ CH.H (sq a' b) j, ∀ y, E ((toSq a b ha).pull j y) = (toSq a' b ha').pull j y := by
  subst e
  exact ⟨AddEquiv.refl _, fun _ => rfl⟩

theorem toSq_bij_bot' {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}
    (a₀ b : IdF A) (h0 : ∀ T, a₀.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (j : ℕ) :
    Function.Bijective ((toSq a₀ b h0).pull j) := by
  refine CrystallineSemistableComparison.P.mapH_bij (toSq a₀ b h0).hom (fun n => ⟨fun f f' h => ?_, fun y => ?_⟩) j
  · funext s
    have h1 := congrArg Subtype.val (congrFun h s)
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hb] at h2
    exact sub_eq_zero.1 h2
  · have hm : ∀ s : ComposableArrows C n, ∃ t : A.obj (s.obj (Fin.last n)),
        Ideal.Quotient.mk _ t = (show sqM a₀ b _ from y s).1 := fun s => Ideal.Quotient.mk_surjective _
    choose t ht using hm
    exact ⟨t, funext fun s => Subtype.ext (ht s)⟩

theorem zK_transport {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (Q : ObjectProperty (Thick (smFun X q))) (t u : ℤ) (ht : t ≤ 0) (j : ℕ) :
    ∃ E : HQ Q t u j ≃+ HQ Q 0 u j, ∀ x, E (zK q Q t u ht j x) = quoK q Q u j x := by
  have e : sFil Q t = sFil Q 0 := by
    have : thFil (smFun X q) t = thFil (smFun X q) 0 := by
      unfold thFil
      congr 1
      funext T
      rw [Int.toNat_of_nonpos ht]
      rfl
    simp only [sFil, this]
  obtain ⟨E, hE⟩ := transport_gen (sFil Q t) (sFil Q 0) (sFil Q u) e _ (fun T => T.obj.pdPow_zero) j
  exact ⟨E, fun x => hE _⟩

theorem quoM_bij {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (s : ℕ) (h : ∀ T, Q T → T.pdPow s = ⊥) (j : ℕ) :
    Function.Bijective (quoM Q s j) := by
  refine toSq_bij_bot' _ _ _ (fun T => ?_) j
  change T.obj.pdPow ((s : ℤ).toNat) = ⊥
  simpa using h _ T.property

theorem dividedPowerFiltration_dividedPowersBot_of_one_le' {K : Type} [Field K] {r : ℕ} (hr : 1 ≤ r) : pdP (dividedPowersBot K) r = ⊥ := by
  refine Ideal.span_eq_bot.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have h : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra h
    push Not at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by simpa using h)
    omega
  obtain ⟨p, hp, h0⟩ := h
  refine List.prod_eq_zero (List.mem_map.2 ⟨p, hp, ?_⟩)
  have e : p.2 = 0 := hl p hp
  rw [e]
  exact (dividedPowersBot K).dpow_eval_zero h0

theorem tfbase_K {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot K) 1 s where
  nil := dividedPowerFiltration_dividedPowersBot_of_one_le' hs
  tf r x h := by simpa using h
  dv n hn := ⟨0, (n : K)⁻¹, by
    have : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
    simp [this]⟩

theorem tfbase_B {K B : Type} [Field K] [CharZero K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) {s : ℕ}
    (h : pdP γ s = ⊥) : TFBase γ 1 s where
  nil := h
  tf r x hx := by simpa using hx
  dv n hn := ⟨0, algebraMap K B (n : K)⁻¹, by
    have : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [pow_zero, ← map_natCast (algebraMap K B) n, ← map_mul, mul_inv_cancel₀ this, map_one]⟩

theorem main : BcOn False → KH.KIso → BasisB := by
  intro hB hK K B _ _ _ _ I γ s m hm hms X q U hU 𝒱 h𝒱 j a bs
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hone : (1 : B) ∈ pdP γ 0 := Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
    rw [hm] at hone
    have hsub : Subsingleton B := subsingleton_of_zero_eq_one ((Ideal.mem_bot.1 hone).symm)
    have hW : ∀ w : HO (TS γ q 1 s 𝒱) j, w = 0 := fun w => by
      have : (1 : B) • w = (0 : B) • w := by rw [Subsingleton.elim (1 : B) 0]
      rwa [one_smul, zero_smul] at this
    refine ⟨fun w => ⟨fun _ => 0, ?_, fun y _ => Subsingleton.elim _ _⟩, fun r hr g hg c φ hφ => ?_⟩
    · exact (hW _).trans (hW _).symm
    · rw [Subsingleton.elim (∑ t, g t * algebraMap K B (φ (bs t))) 0]
      exact Ideal.zero_mem _
  obtain ⟨S⟩ := GlobalTheory.T.graded_splitting_over_field (K := K) γ m hm
  have hs : 1 ≤ s := hm0.trans_le hms
  have hsB : pdP γ s = ⊥ := le_bot_iff.1 (hm ▸ Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, hms.trans hr, hz⟩)
  have hO : TFBase (dividedPowersBot K) 1 s := tfbase_K hs
  have hA : TFBase γ 1 s := tfbase_B (K := K) γ hsB
  have hd : ∀ α, U.d α < s := fun α => by have := hU α; omega
  have LC := fun (i : Fin m) n r => GlobalTheory.T.scalar_multiplication_shifts_filtration (O := K) γ q 1 s 𝒱 i (S.ν i n) (S.mem i n) r
  have T := fun (r : ℕ) (hr : r ≤ s) => hB γ 1 s m hO hA S q 𝒱 (Or.inr ⟨not_false, ⟨U⟩, h𝒱⟩) 0 r (by positivity)
    (by exact_mod_cast hr) (fun i n => LC i n 0) (fun i n => LC i n r) j
  have hne : ∀ i : Fin m, (0 : ℤ) - (i : ℕ) ≤ 0 := fun i => by omega
  refine ⟨fun w => ?_, ?_⟩
  · refine core_basis S (fun i => zK q (TO q 1 s 𝒱) (0 - (i : ℕ)) (s - (i : ℕ)) (hne i) j) (muB γ q 1 s 𝒱 j)
      (quoM (TS γ q 1 s 𝒱) s j).toAddMonoidHom (T s le_rfl) (fun i n x => GlobalTheory.T.smooth_pull_basis_filtration γ q 1 s 𝒱 _ _ _ _ _ _ _ j x) bs
      (fun i => ?_) (quoM_bij _ s (fun T hT => hT.1.1) j) w
    obtain ⟨E, hE⟩ := zK_transport q (TO q 1 s 𝒱) (0 - (i : ℕ)) (s - (i : ℕ)) (hne i) j
    have hb : Function.Bijective (quoK q (KS q s 𝒱) ((s - (i : ℕ) : ℕ) : ℤ) j) :=
      GlobalTheory.T.quotient_filtration_bijective_of_cover hK q U s (s - i) (fun α => by have := hU α; have := i.2; omega) (by omega) 𝒱 h𝒱 j
    have e1 : (((s - (i : ℕ) : ℕ) : ℤ)) = (s : ℤ) - (i : ℕ) := by have := i.2; omega
    rw [e1] at hb
    have : E ∘ (zK q (TO q 1 s 𝒱) (0 - (i : ℕ)) (s - (i : ℕ)) (hne i) j) = quoK q (KS q s 𝒱) ((s : ℤ) - (i : ℕ)) j :=
      funext hE
    exact (Function.Bijective.of_comp_iff' E.bijective _).1 (this ▸ hb)
  · intro r hr g hg c φ hφ
    refine core_filt S (fun i => zK q (TO q 1 s 𝒱) (0 - (i : ℕ)) (r - (i : ℕ)) (hne i) j) (muB γ q 1 s 𝒱 j)
      (quoM (TS γ q 1 s 𝒱) r j).toAddMonoidHom (T r hr) (fun i n x => GlobalTheory.T.smooth_pull_basis_filtration γ q 1 s 𝒱 _ _ _ _ _ _ _ j x) bs φ (r - c)
      (fun i => ?_) g hg
    by_cases hi : r - c ≤ (i : ℕ)
    · exact Or.inl hi
    refine Or.inr fun x hx => hφ x ?_
    obtain ⟨E, hE⟩ := zK_transport q (TO q 1 s 𝒱) (0 - (i : ℕ)) (r - (i : ℕ)) (hne i) j
    have h0 : quoK q (KS q s 𝒱) ((r - (i : ℕ) : ℕ) : ℤ) j x = 0 := by
      have e1 : (((r - (i : ℕ) : ℕ) : ℤ)) = (r : ℤ) - (i : ℕ) := by omega
      rw [e1, ← hE x, hx, map_zero]
    have h1 := ((hK q U s hd 𝒱 h𝒱 j).2 (r - i) (by omega) x).2 h0
    exact GlobalTheory.LogCris.fil_anti _ _ (by omega) h1

theorem basisB_of_bcOn : BcOn False → KH.KIso → BasisB := main

end GlobalTheory.CompanionTheory.BasisBase
