import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenominatorOfSpan
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraLast
set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv.LeadForm
noncomputable section

theorem common_den {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (S : Submonoid R) (M : Submodule R V)
    (Y : Finset V) [DecidableEq V] (h : ∀ y ∈ Y, ∃ s ∈ S, s • y ∈ M) : ∃ s ∈ S, ∀ y ∈ Y, s • y ∈ M := by
  induction Y using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert a Y _ ih =>
    obtain ⟨s, hs, hsY⟩ := ih fun y hy => h y (Finset.mem_insert_of_mem hy)
    obtain ⟨u, hu, hua⟩ := h a (Finset.mem_insert_self _ _)
    refine ⟨s * u, mul_mem hs hu, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · rw [mul_smul]; exact M.smul_mem _ hua
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ (hsY y hy)

theorem den_of_span {K : Type} [Field K] [NumberField K] {i : ℕ} (P : Ideal (𝓞 K)) [P.IsPrime]
    (M : Submodule (𝓞 K) (Fin i → K)) (x : Fin i → K)
    (hx : x ∈ Submodule.span (Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors)
      (M : Set (Fin i → K))) : ∃ s ∈ P.primeCompl, s • x ∈ M :=
  _root_.UpperTheory.Reformulated.B.SpanDenominator.den_of_span P M x hx

theorem frame : ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (P : Ideal (𝓞 K)), P.IsMaximal → P ≠ ⊥ →
    ∀ L : Submodule (𝓞 K) (Fin i → K), L.FG →
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → Fin i → K) (s : 𝓞 K), s ∉ P ∧ (∀ j, p j ∈ L) ∧
      LinearIndependent K p ∧ ∀ v ∈ L, s • v ∈ Submodule.span (𝓞 K) (Set.range p) := by
  intro K _ _ i P hP h0 L hL
  classical
  haveI : P.IsPrime := hP.isPrime
  let A : Subalgebra (𝓞 K) K := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) h0 A
  let N : Submodule A (Fin i → K) := Submodule.span A (L : Set (Fin i → K))
  obtain ⟨G, hG⟩ := hL
  haveI : Module.Finite A N := by
    rw [Module.Finite.iff_fg]
    refine ⟨G, ?_⟩
    rw [show N = Submodule.span A (L : Set (Fin i → K)) from rfl, ← hG, Submodule.span_span_of_tower]
  haveI : Module.IsTorsionFree A N := inferInstance
  haveI : Module.Free A N := Module.free_of_finite_type_torsion_free'
  let q := Module.Free.chooseBasis A N
  let ι := Module.Free.ChooseBasisIndex A N
  obtain ⟨s₀, hs₀, hs₀q⟩ := common_den P.primeCompl L (Finset.univ.image fun j : ι => ((q j : N) : Fin i → K)) (by
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact den_of_span P L _ (q j).2)
  have hs₀0 : algebraMap (𝓞 K) K s₀ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (P.primeCompl_le_nonZeroDivisors hs₀)
  let p : ι → Fin i → K := fun j => s₀ • ((q j : N) : Fin i → K)
  have hpL : ∀ j, p j ∈ L := fun j => hs₀q _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hqA : LinearIndependent A (fun j => ((q j : N) : Fin i → K)) :=
    q.linearIndependent.map' N.subtype N.ker_subtype
  have hqK : LinearIndependent K (fun j => ((q j : N) : Fin i → K)) :=
    (LinearIndependent.iff_fractionRing A K).1 hqA
  have hpK : LinearIndependent K p := by
    have := hqK.units_smul (fun _ => Units.mk0 _ hs₀0)
    convert this using 1
    funext j
    simp [p, Units.smul_def, algebraMap_smul]
  set Q : Submodule (𝓞 K) (Fin i → K) := Submodule.span (𝓞 K) (Set.range p) with hQ
  have hNQ : ∀ x ∈ N, x ∈ Submodule.span A (Q : Set (Fin i → K)) := by
    intro x hx
    have hx' := q.sum_repr ⟨x, hx⟩
    have : x = ∑ j, (q.repr ⟨x, hx⟩ j) • ((q j : N) : Fin i → K) := by
      calc x = ((∑ j, q.repr ⟨x, hx⟩ j • q j : N) : Fin i → K) := by rw [hx']
        _ = _ := by rw [AddSubmonoidClass.coe_finset_sum]; rfl
    rw [this]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    have hu : (algebraMap (𝓞 K) K s₀)⁻¹ ∈ A := ⟨1, s₀, hs₀, by simp⟩
    have : ((q j : N) : Fin i → K) = (⟨_, hu⟩ : A) • p j := by
      rw [Subalgebra.smul_def]
      simp only [p]
      rw [← algebraMap_smul K s₀, smul_smul]
      simp [hs₀0]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))
  obtain ⟨s₁, hs₁, hs₁G⟩ := common_den P.primeCompl Q G (by
    intro y hy
    have hyL : y ∈ L := hG ▸ Submodule.subset_span hy
    exact den_of_span P Q y (hNQ y (Submodule.subset_span hyL)))
  refine ⟨ι, inferInstance, p, s₁, hs₁, hpL, hpK, fun v hv => ?_⟩
  rw [← hG] at hv
  induction hv using Submodule.span_induction with
  | mem y hy => exact hs₁G y hy
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact Q.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact Q.smul_mem a hy

def ev {T B : Type} [Fintype T] [CommRing B] (x y : T → B) : MRing (stackedBlocks T) →+* B :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl _, t⟩ => x t
    | ⟨.inr _, t⟩ => y t

theorem ev_map {T B B' : Type} [Fintype T] [CommRing B] [CommRing B'] (h : B →+* B') (x y : T → B)
    (f : MRing (stackedBlocks T)) : h (ev x y f) = ev (fun t => h (x t)) (fun t => h (y t)) f := by
  have : h.comp (ev x y) = ev (fun t => h (x t)) (fun t => h (y t)) := by
    refine MvPolynomial.ringHom_ext (by simp [ev]) ?_
    rintro ⟨⟨⟩ | ⟨⟩, t⟩ <;> simp [ev]
  exact congrArg (fun g => g f) this

theorem ev_scale {T B : Type} [Fintype T] [CommRing B] (p q : B) (x y : T → B) (d n : ℕ)
    (f : MRing (stackedBlocks T)) (hf : IsMultiHomog f (bidegree d n)) :
    ev (fun t => p * x t) (fun t => q * y t) f = p ^ d * q ^ n * ev x y f := by
  classical
  simp only [ev, coe_eval₂Hom]
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 := hf m hm (Sum.inl ())
  have h2 := hf m hm (Sum.inr ())
  simp only [bidegree, Sum.elim_inl, Sum.elim_inr] at h1 h2
  simp only [Fintype.prod_sigma, Fintype.prod_sum_type, Fintype.prod_unique]
  have h1' : ∑ t, m ⟨Sum.inl default, t⟩ = d := h1
  have h2' : ∑ t, m ⟨Sum.inr default, t⟩ = n := h2
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  erw [h1', h2']
  ring

theorem stackedFormEval_eq_ev {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    [Fintype T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) :
    stackedFormEval b b' = ev (fun t => ∑ j, C ((b' t : Fin i → K) j) * X j)
      (fun t => ∑ j, C ((b t : Fin i → K) j) * X j) := by
  refine MvPolynomial.ringHom_ext (by simp [ev, stackedFormEval]) ?_
  rintro ⟨⟨⟩ | ⟨⟩, t⟩ <;> simp [ev, stackedFormEval]

theorem linPointMap_eq_ev {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    linPointMap α M = ev (fun t => C (α t) * X none) (fun t => ∑ j, C (M t j) * X (some j)) := by
  refine MvPolynomial.ringHom_ext (by simp [ev, linPointMap]) ?_
  rintro ⟨⟨⟩ | ⟨⟩, t⟩ <;> simp [ev, linPointMap]

theorem subst_form {K : Type} [Field K] {i : ℕ} {ι : Type} [Fintype ι]
    (c : (Fin i → K) →ₗ[K] (ι → K)) (W : ι → MvPolynomial ι K) (v : Fin i → K) :
    aeval (fun l : Fin i => ∑ j, C (c (Pi.single l 1) j) * W j) (∑ l, C (v l) * X l : MvPolynomial (Fin i) K) =
      ∑ j, C (c v j) * W j := by
  have hv : v = ∑ l, v l • (Pi.single l 1 : Fin i → K) := by
    funext a
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [map_sum, map_mul, aeval_X, algHom_C, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_smul, algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem poly : ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (k : Type) [Field k] (α : T → k) (M : T → Fin i → k) (ρ : 𝓞 K →+* k)
    (ι : Type) [Fintype ι] [DecidableEq ι] (e : ι → Fin i → K) (j₀ : ι) (π S : 𝓞 K)
    (C D : T → ι → 𝓞 K) (lam : k) (N : ι → Fin i → k),
    LinearIndependent K e → π ≠ 0 → ρ π = 0 → ρ S ≠ 0 →
    (∀ t, algebraMap (𝓞 K) K S • (b' t : Fin i → K) = ∑ j, algebraMap (𝓞 K) K (C t j) • e j) →
    (∀ t, algebraMap (𝓞 K) K S • (b t : Fin i → K) =
      ∑ j, algebraMap (𝓞 K) K (D t j) • (if j = j₀ then algebraMap (𝓞 K) K π • e j else e j)) →
    (∀ t, ρ S * α t = ρ (C t j₀) * lam) →
    (∀ t, ρ S • M t = ∑ j, ρ (D t j) • N j) →
    ∀ (d n : ℕ) (f : MRing (stackedBlocks T)), IsMultiHomog f (bidegree d n) →
      stackedFormEval b b' f = 0 → linPointMap α M f = 0 := by
  intro K _ _ i F F' T _ _ b b' k _ α M ρ ι _ _ e j₀ π S Cc D lam N he hπ hρπ hS hC hD hα hM d n f hf h0
  classical
  set am := algebraMap (𝓞 K) K with ham
  have hinj : LinearMap.ker (Fintype.linearCombination K e) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun y hy => ?_
    have := Fintype.linearIndependent_iff.1 he y (by simpa [Fintype.linearCombination_apply] using hy)
    exact funext this
  obtain ⟨c, hc⟩ := (Fintype.linearCombination K e).exists_leftInverse_of_injective hinj
  have hcy : ∀ y : ι → K, c (∑ l, y l • e l) = y := by
    intro y
    have := LinearMap.congr_fun hc y
    simpa [Fintype.linearCombination_apply] using this
  let W : ι → MvPolynomial ι K := fun j => if j = j₀ then X j else C (am π) * X j
  let h1 : MvPolynomial (Fin i) K →+* MvPolynomial ι K :=
    (aeval (fun l : Fin i => ∑ j, C (c (Pi.single l 1) j) * W j) :
      MvPolynomial (Fin i) K →ₐ[K] MvPolynomial ι K).toRingHom
  let h2 : MvPolynomial ι (𝓞 K) →+* MvPolynomial ι K := map am
  let h3 : MvPolynomial ι (𝓞 K) →+* MvPolynomial ι k := map ρ
  let P : T → MvPolynomial ι (𝓞 K) := fun t => ∑ j, C (Cc t j) * (if j = j₀ then X j else C π * X j)
  let Q : T → MvPolynomial ι (𝓞 K) := fun t => ∑ j, C (D t j) * X j
  have hform : ∀ v : Fin i → K, h1 (∑ l, C (v l) * X l) = ∑ j, C (c v j) * W j := fun v => subst_form c W v
  have hscale : ∀ (s : K) (v : Fin i → K), (C s * ∑ l, C (v l) * X l : MvPolynomial (Fin i) K) =
      ∑ l, C ((s • v) l) * X l := by
    intro s v
    simp [Finset.mul_sum, mul_assoc]
  have hx : ∀ t, h1 (C (am S) * ∑ l, C ((b' t : Fin i → K) l) * X l) = 1 * h2 (P t) := by
    intro t
    rw [hscale, hform, hC t, hcy (fun l => am (Cc t l)), one_mul]
    simp only [h2, P, map_sum, map_mul, map_C]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀ <;> simp [W, hj]
  have hy : ∀ t, h1 (C (am S) * ∑ l, C ((b t : Fin i → K) l) * X l) = C (am π) * h2 (Q t) := by
    intro t
    have hv : ∑ l, am (D t l) • (if l = j₀ then am π • e l else e l) =
        ∑ l, (am (D t l) * (if l = j₀ then am π else 1)) • e l := by
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : l = j₀ <;> simp [h, smul_smul]
    rw [hscale, hform, hD t, hv, hcy (fun l => am (D t l) * (if l = j₀ then am π else 1))]
    simp only [h2, Q, map_sum, map_mul, map_C, Finset.mul_sum, map_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · simp only [W, hj, if_true, map_mul]; ring
    · simp only [W, hj, if_false, map_mul, map_one]; ring
  have hamπ : (C (am π) : MvPolynomial ι K) ≠ 0 := by
    rw [Ne, C_eq_zero]
    exact fun h => hπ ((map_eq_zero_iff am RingOfIntegers.coe_injective).1 h)
  have h2inj : Function.Injective h2 := map_injective _ RingOfIntegers.coe_injective
  rw [stackedFormEval_eq_ev] at h0
  have e1 := ev_scale (C (am S)) (C (am S)) (fun t => ∑ l, C ((b' t : Fin i → K) l) * X l)
    (fun t => ∑ l, C ((b t : Fin i → K) l) * X l) d n f hf
  rw [h0, mul_zero] at e1
  have e2 := congrArg h1 e1
  rw [ev_map, map_zero] at e2
  simp only [hx, hy] at e2
  rw [ev_scale 1 (C (am π)) (fun t => h2 (P t)) (fun t => h2 (Q t)) d n f hf, one_pow, one_mul] at e2
  have e3 : ev (fun t => h2 (P t)) (fun t => h2 (Q t)) f = 0 :=
    (mul_eq_zero.1 e2).resolve_left (pow_ne_zero _ hamπ)
  rw [← ev_map] at e3
  have e4 : ev P Q f = 0 := h2inj (by rw [e3, map_zero])
  have e5 := congrArg h3 e4
  rw [ev_map, map_zero] at e5
  have hP3 : ∀ t, h3 (P t) = X j₀ * C (ρ (Cc t j₀)) := by
    intro t
    simp only [h3, P, map_sum, map_mul, map_C]
    rw [Finset.sum_eq_single j₀]
    · simp [mul_comm]
    · intro j _ hj
      simp [hj, hρπ]
    · simp
  simp only [hP3] at e5
  have e5' : ev (fun t => X j₀ * (C (ρ (Cc t j₀)) : MvPolynomial ι k)) (fun t => 1 * h3 (Q t)) f = 0 := by
    simpa only [one_mul] using e5
  replace e5 := e5'
  rw [ev_scale (X j₀) 1 (fun t => C (ρ (Cc t j₀))) (fun t => h3 (Q t)) d n f hf, one_pow, mul_one] at e5
  have e6 : ev (fun t => (C (ρ (Cc t j₀)) : MvPolynomial ι k)) (fun t => h3 (Q t)) f = 0 :=
    (mul_eq_zero.1 e5).resolve_left (pow_ne_zero _ (X_ne_zero _))
  let h4 : MvPolynomial ι k →+* MvPolynomial (Option (Fin i)) k :=
    eval₂Hom C (fun j => ∑ l, C (N j l) * X (some l))
  have e7 := congrArg h4 e6
  rw [ev_map, map_zero] at e7
  have hC4 : ∀ t, h4 (C (ρ (Cc t j₀))) = C (ρ (Cc t j₀)) := fun t => by simp [h4]
  have hyq : ∀ t, h4 (h3 (Q t)) = C (ρ S) * ∑ l, C (M t l) * X (some l) := by
    intro t
    have hMl : ∀ l, ρ S * M t l = ∑ j, ρ (D t j) * N j l := by
      intro l
      have := congrFun (hM t) l
      simpa [Finset.sum_apply] using this
    simp only [h3, h4, Q, map_sum, map_mul, map_C, map_X, coe_eval₂Hom, eval₂_mul, eval₂_C, eval₂_X, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, ← C_mul, hMl, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [C_mul, mul_assoc]
  simp only [hC4, hyq] at e7
  have e8 := ev_scale (C lam * X none) 1 (fun t => (C (ρ (Cc t j₀)) : MvPolynomial (Option (Fin i)) k))
    (fun t => C (ρ S) * ∑ l, C (M t l) * X (some l)) d n f hf
  rw [e7, mul_zero] at e8
  have hxq : ∀ t, (C lam * X none : MvPolynomial (Option (Fin i)) k) * C (ρ (Cc t j₀)) =
      C (ρ S) * (C (α t) * X none) := by
    intro t
    rw [← mul_assoc, ← C_mul, hα t, C_mul]
    ring
  simp only [hxq, one_mul] at e8
  rw [ev_scale (C (ρ S)) (C (ρ S)) (fun t => C (α t) * X none) (fun t => ∑ l, C (M t l) * X (some l)) d n f hf] at e8
  rw [linPointMap_eq_ev]
  have hS' : (C (ρ S) : MvPolynomial (Option (Fin i)) k) ≠ 0 := by rwa [Ne, C_eq_zero]
  exact (mul_eq_zero.1 e8).resolve_left (mul_ne_zero (pow_ne_zero _ hS') (pow_ne_zero _ hS'))

theorem unif {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) (hP : P.IsMaximal) (h0 : P ≠ ⊥) :
    ∃ π : R, π ≠ 0 ∧ π ∈ P ∧ ∃ s : R, s ∉ P ∧ ∀ y ∈ P, ∃ c, s * y = π * c :=
  _root_.UpperTheory.Reformulated.B.Yde5.main P hP h0

theorem semi_sum {K : Type} [Field K] [NumberField K] {i : ℕ} {k W : Type} [Field k] [AddCommGroup W] [Module k W]
    (ρ : 𝓞 K →+* k) (Λ : Submodule ℤ (Fin i → K))
    (hΛ : ∀ (μ : 𝓞 K) v, v ∈ Λ → algebraMap (𝓞 K) K μ • v ∈ Λ) (τ : Λ →+ W)
    (hτ : ∀ (μ : 𝓞 K) (φ ψ : Λ), (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → τ ψ = ρ μ • τ φ)
    {ι : Type} [Fintype ι] (y : ι → 𝓞 K) (q : ι → Λ) (v : Λ)
    (hv : (v : Fin i → K) = ∑ j, algebraMap (𝓞 K) K (y j) • (q j : Fin i → K)) :
    τ v = ∑ j, ρ (y j) • τ (q j) := by
  have : v = ∑ j, (⟨algebraMap (𝓞 K) K (y j) • (q j : Fin i → K), hΛ _ _ (q j).2⟩ : Λ) := by
    apply Subtype.ext
    rw [hv]
    simp
  rw [this, map_sum]
  exact Finset.sum_congr rfl fun j _ => hτ _ _ _ rfl

theorem dual_stable {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) (μ : 𝓞 K)
    (v : Fin i → K) (hv : v ∈ dualLattice F) : algebraMap (𝓞 K) K μ • v ∈ dualLattice F := by
  intro x hx
  obtain ⟨c, hc⟩ := hv x hx
  refine ⟨μ * c, ?_⟩
  rw [smul_dotProduct, ← hc, map_mul, smul_eq_mul]

def dualO {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) : Submodule (𝓞 K) (Fin i → K) where
  carrier := dualLattice F
  add_mem' := (dualLattice F).add_mem
  zero_mem' := (dualLattice F).zero_mem
  smul_mem' := by
    intro μ φ hφ
    rw [← algebraMap_smul K μ φ]
    exact dual_stable F μ φ hφ

theorem dualO_fg {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) {T : Type} [Fintype T]
    (b : Module.Basis T ℤ (dualLattice F)) : (dualO F).FG := by
  have : dualO F = Submodule.span (𝓞 K) (Set.range fun t => (b t : Fin i → K)) := by
    apply le_antisymm
    · intro x hx
      have hx' := b.sum_repr ⟨x, hx⟩
      have hxs : x = ∑ t, (b.repr ⟨x, hx⟩ t) • (b t : Fin i → K) := by
        calc x = ((∑ t, b.repr ⟨x, hx⟩ t • b t : dualLattice F) : Fin i → K) := by rw [hx']
          _ = _ := by rw [AddSubmonoidClass.coe_finset_sum]; rfl
      rw [hxs]
      refine Submodule.sum_mem _ fun t _ => ?_
      have hm : (b t : Fin i → K) ∈ Submodule.span (𝓞 K) (Set.range fun t => (b t : Fin i → K)) :=
        Submodule.subset_span ⟨t, rfl⟩
      exact (Submodule.span (𝓞 K) (Set.range fun t => (b t : Fin i → K))).toAddSubgroup.zsmul_mem hm _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact (b t).2
  rw [this]
  exact Submodule.fg_span (Set.finite_range _)

theorem dualStackedExcLeadForm : GroundTheory.Heights₂.Heights.DualStackedExcLeadForm.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hstack k _ α M hres d n f hf h0
  classical
  obtain ⟨ρ, ρ', σ, hρs, hρ's, hσs, hker, hρ'l, hσl, hα, hM⟩ := hres
  set am := algebraMap (𝓞 K) K with ham
  let P : Ideal (𝓞 K) := RingHom.ker ρ
  have hP : P.IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hρs
  have h0P : P ≠ ⊥ := by
    intro h
    have hinj : Function.Injective ρ := (RingHom.injective_iff_ker_eq_bot ρ).2 h
    have e : 𝓞 K ≃+* k := RingEquiv.ofBijective ρ ⟨hinj, hρs⟩
    exact RingOfIntegers.not_isField K (e.toMulEquiv.isField (Field.toIsField k))
  obtain ⟨π, hπ0, hπP, s₁, hs₁, hs₁y⟩ := unif P hP h0P
  obtain ⟨ι, _, p, s, hs, hpL, hpK, hsp⟩ := frame K i P hP h0P (dualO F') (dualO_fg F' b')
  have hρπ : ρ π = 0 := hπP
  have hρs₁ : ρ s₁ ≠ 0 := hs₁
  have hρs0 : ρ s ≠ 0 := hs
  let pL : ι → dualLattice F' := fun j => ⟨p j, hpL j⟩
  have hcoordp : ∀ v : dualLattice F', ∃ y : ι → 𝓞 K,
      am s • (v : Fin i → K) = ∑ j, am (y j) • p j := by
    intro v
    have h1 := hsp v v.2
    obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 h1
    refine ⟨y, ?_⟩
    rw [ham, algebraMap_smul, ← hy]
    exact (Finset.sum_congr rfl fun j _ => (algebraMap_smul K (y j) (p j)).symm).symm ▸ rfl
  have hρ'sum := fun (y : ι → 𝓞 K) (q : ι → dualLattice F') (v : dualLattice F') hv =>
    semi_sum ρ (dualLattice F') (dual_stable F') ρ' hρ'l y q v hv
  have hsv : ∀ (μ : 𝓞 K) (v : dualLattice F'), ρ' ⟨am μ • (v : Fin i → K), dual_stable F' μ _ v.2⟩ = ρ μ * ρ' v :=
    fun μ v => hρ'l μ v _ rfl
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, ρ' (pL j₀) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨v₀, hv₀⟩ := hρ's 1
    obtain ⟨y₀, hy₀⟩ := hcoordp v₀
    have h1 := hρ'sum y₀ pL ⟨am s • (v₀ : Fin i → K), dual_stable F' s _ v₀.2⟩ hy₀
    rw [hsv, hv₀, mul_one] at h1
    apply hρs0
    rw [h1]
    simp [hcon]
  set lam := ρ' (pL j₀) with hlam
  choose c hc using fun j => hρs (ρ' (pL j) / lam)
  let cc : ι → 𝓞 K := fun j => if j = j₀ then 0 else c j
  let e : ι → Fin i → K := fun j => p j - am (cc j) • p j₀
  have hemem : ∀ j, e j ∈ dualLattice F' := fun j =>
    (dualLattice F').sub_mem (pL j).2 (dual_stable F' _ _ (pL j₀).2)
  let eL : ι → dualLattice F' := fun j => ⟨e j, hemem j⟩
  have he₀ : e j₀ = p j₀ := by simp [e, cc]
  have hρe₀ : ρ' (eL j₀) = lam := by
    rw [hlam]
    congr 1
    exact Subtype.ext he₀
  have hρe : ∀ j, j ≠ j₀ → ρ' (eL j) = 0 := by
    intro j hj
    have h1 : eL j = pL j - ⟨am (c j) • (pL j₀ : Fin i → K), dual_stable F' _ _ (pL j₀).2⟩ := by
      apply Subtype.ext
      simp [eL, e, cc, hj, pL]
    rw [h1, map_sub, hsv, hc, ← hlam]
    field_simp [hj₀]
    simp
  have hei : LinearIndependent K e := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    set A : K := ∑ l, g l * am (cc l) with hA
    have h1 : ∑ j, (g j - if j = j₀ then A else 0) • p j = 0 := by
      have : ∑ j, (g j - if j = j₀ then A else 0) • p j = ∑ j, g j • e j := by
        simp only [e, sub_smul, smul_sub, Finset.sum_sub_distrib, smul_smul, ite_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_smul, hA]
      rw [this, hg]
    have h2 := Fintype.linearIndependent_iff.1 hpK _ h1
    have h3 : ∀ j, j ≠ j₀ → g j = 0 := fun j hj => by simpa [hj] using h2 j
    have h4 : A = 0 := by
      rw [hA]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = j₀
      · simp [hl, cc]
      · simp [h3 l hl]
    intro j
    by_cases hj : j = j₀
    · subst hj
      simpa [h4] using h2 j
    · exact h3 j hj
  have hcoord : ∀ v : dualLattice F', ∃ y : ι → 𝓞 K,
      am s • (v : Fin i → K) = ∑ j, am (y j) • e j := by
    intro v
    obtain ⟨y, hy⟩ := hcoordp v
    refine ⟨fun j => y j + if j = j₀ then ∑ l, y l * cc l else 0, ?_⟩
    rw [hy]
    simp only [map_add, add_smul, Finset.sum_add_distrib, apply_ite am, map_zero, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, he₀]
    simp only [e, smul_sub, Finset.sum_sub_distrib, smul_smul, map_sum, map_mul, Finset.sum_smul]
    abel
  have hlmem : ∀ j, (if j = j₀ then am π • e j else e j) ∈ dualLattice F := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      simp only [if_true]
      have h2 := (hker ⟨am π • e j, dual_stable F' _ _ (hemem j)⟩).1 (by
        have := hsv π (eL j)
        rw [hρπ, zero_mul] at this
        exact this)
      exact h2
    · simp only [hj, if_false]
      exact (hker (eL j)).1 (hρe j hj)
  let lL : ι → dualLattice F := fun j => ⟨_, hlmem j⟩
  let N : ι → Fin i → k := fun j => σ (lL j)
  have hbmem : ∀ t, (b t : Fin i → K) ∈ dualLattice F' := fun t => by
    rw [hstack t]
    exact (dualLattice F').smul_mem _ (b' t).2
  let bL : T → dualLattice F' := fun t => ⟨b t, hbmem t⟩
  choose yC hyC using fun t => hcoord (b' t)
  choose yD hyD using fun t => hcoord (bL t)
  have hyD0 : ∀ t, yD t j₀ ∈ P := by
    intro t
    have h1 := hρ'sum (yD t) eL ⟨am s • ((bL t : dualLattice F') : Fin i → K), dual_stable F' s _ (bL t).2⟩ (hyD t)
    have hb0 : ρ' (bL t) = 0 := (hker (bL t)).2 (b t).2
    rw [hsv, hb0, mul_zero, Finset.sum_eq_single j₀ (fun j _ hj => by simp [hρe j hj]) (by simp), hρe₀] at h1
    have h2 : ρ (yD t j₀) * lam = 0 := h1.symm
    exact (mul_eq_zero.1 h2).resolve_right hj₀
  choose cD hcD using fun t => hs₁y (yD t j₀) (hyD0 t)
  refine poly K i F F' T b b' k α M ρ ι e j₀ π (s₁ * s) (fun t j => s₁ * yC t j)
    (fun t j => if j = j₀ then cD t else s₁ * yD t j) lam N hei hπ0 hρπ
    (by rw [map_mul]; exact mul_ne_zero hρs₁ hρs0) ?_ ?_ ?_ ?_ d n f hf h0
  · intro t
    rw [map_mul, mul_smul, hyC t, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_smul]
  · intro t
    have hbt : am s • (b t : Fin i → K) = ∑ j, am (yD t j) • e j := hyD t
    rw [map_mul, mul_smul, hbt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj
      simp only [if_true, smul_smul]
      rw [← map_mul, ← map_mul, hcD t, mul_comm π]
    · beta_reduce
      rw [if_neg hj, if_neg hj, map_mul, mul_smul]
  · intro t
    have hv : ((⟨am (s₁ * s) • (b' t : Fin i → K), dual_stable F' _ _ (b' t).2⟩ : dualLattice F') : Fin i → K) =
        ∑ j, am (s₁ * yC t j) • (eL j : Fin i → K) := by
      show am (s₁ * s) • (b' t : Fin i → K) = ∑ j, am (s₁ * yC t j) • e j
      rw [map_mul, mul_smul, hyC t, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_smul]
    have h1 := hρ'sum _ eL _ hv
    rw [hsv, ← hα t, Finset.sum_eq_single j₀ (fun j _ hj => by simp [hρe j hj]) (by simp), hρe₀] at h1
    exact h1
  · intro t
    have hv : ((⟨am (s₁ * s) • (b t : Fin i → K), dual_stable F _ _ (b t).2⟩ : dualLattice F) : Fin i → K) =
        ∑ j, am (if j = j₀ then cD t else s₁ * yD t j) • (lL j : Fin i → K) := by
      show am (s₁ * s) • (b t : Fin i → K) =
        ∑ j, am (if j = j₀ then cD t else s₁ * yD t j) • (if j = j₀ then am π • e j else e j)
      have hbt : am s • (b t : Fin i → K) = ∑ j, am (yD t j) • e j := hyD t
      rw [map_mul, mul_smul, hbt, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = j₀
      · subst hj
        simp only [if_true, smul_smul]
        rw [← map_mul, ← map_mul, hcD t, mul_comm π]
      · beta_reduce
        rw [if_neg hj, if_neg hj, map_mul, mul_smul]
    have h1 := semi_sum ρ (dualLattice F) (dual_stable F) σ hσl _ lL _ hv
    rw [hσl (s₁ * s) (b t) _ rfl, ← hM t] at h1
    exact h1

end
end GlobalTheory.CompanionTheory.Ar.Giv.LeadForm
