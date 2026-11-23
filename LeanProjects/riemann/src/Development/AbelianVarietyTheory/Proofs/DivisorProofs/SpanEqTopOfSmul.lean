import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvolEqOfFixed

open NumberField Module
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.ModularLattice

section Rank

variable {R F V : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F] [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]

theorem finrank_quot (M : Submodule R V) (hfg : M.FG)
    (hspan : Submodule.span F (M : Set V) = ⊤) (𝔭 : Ideal R) [h𝔭 : 𝔭.IsMaximal] :
    finrank (R ⧸ 𝔭) (M ⧸ (𝔭 • ⊤ : Submodule R M)) = finrank F V := by
  let : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  let Q := M ⧸ (𝔭 • ⊤ : Submodule R M)
  have : Module.Finite (R ⧸ 𝔭) Q := Module.Finite.of_restrictScalars_finite R _ _
  let b := Module.finBasis (R ⧸ 𝔭) Q
  choose x hx using fun i => Submodule.Quotient.mk_surjective _ (b i)
  have hli : LinearIndependent F (M.subtype ∘ x) := by
    refine Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial (S := R ⧸ 𝔭) F ?_ M.subtype
      M.injective_subtype (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ?_
    · rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]; exact h𝔭.ne_top
    · have : (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) ∘ x = b := by
        funext i; exact hx i
      rw [this]; exact b.linearIndependent
  have hsup : (⊤ : Submodule R M) ≤ Submodule.span R (Set.range x) ⊔ 𝔭 • ⊤ := by
    intro v _
    have hv : (Submodule.Quotient.mk v : Q) ∈ Submodule.span (R ⧸ 𝔭) (Set.range b) := b.mem_span _
    rw [← @Submodule.restrictScalars_mem R,
      Submodule.restrictScalars_span R (R ⧸ 𝔭) Ideal.Quotient.mk_surjective] at hv
    have hb : Set.range b = (Submodule.mkQ (𝔭 • ⊤ : Submodule R M)) '' Set.range x := by
      rw [← Set.range_comp]; congr 1; funext i; exact (hx i).symm
    rw [hb, ← Submodule.map_span] at hv
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 hv
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at e
    have : v = y - (y - v) := by abel
    rw [this]
    exact sub_mem (Submodule.mem_sup_left hy) (Submodule.mem_sup_right e)
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top (R := R) (M := M)) le_rfl hsup
  have hs𝔭 : s ∉ 𝔭 := fun h => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem h hs1; simpa using this))
  have hsv : ∀ v : M, s • v ∈ Submodule.span R (Set.range x) := fun v =>
    hs (Submodule.smul_mem_pointwise_smul v s ⊤ trivial)
  have hs0 : algebraMap R F s ≠ 0 := by
    intro h0
    have : s = 0 := (IsFractionRing.injective R F) (by rw [h0, map_zero])
    exact hs𝔭 (this ▸ 𝔭.zero_mem)
  have hsp : ⊤ ≤ Submodule.span F (Set.range (M.subtype ∘ x)) := by
    rw [← hspan, Submodule.span_le]
    intro v hv
    have h1 := hsv ⟨v, hv⟩
    have h2 : (s • v : V) ∈ Submodule.span F (Set.range (M.subtype ∘ x)) := by
      have h3 : M.subtype (s • ⟨v, hv⟩) ∈ (Submodule.span R (Set.range x)).map M.subtype :=
        Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact Submodule.span_le_restrictScalars R F _ h3
    have h4 : v = (algebraMap R F s)⁻¹ • (s • v) := by
      rw [← algebraMap_smul F s v, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [h4]
    exact Submodule.smul_mem _ _ h2
  have := finrank_eq_card_basis (Basis.mk hli hsp)
  simpa using this.symm

end Rank

section Lagrangian

variable {k : Type} [Field k] (τ : k →+* k) {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem exists_lagrangian (hτ : ∀ x, τ (τ x) = x) (hN : ∀ z, τ z = z → ∃ a, a * τ a = z)
    (hev : Even (finrank k V)) (f : V → V → k) (hadd : ∀ y x x', f y (x + x') = f y x + f y x')
    (hsm : ∀ y (a : k) x, f y (a • x) = a * f y x) (hsy : ∀ x y, f y x = τ (f x y))
    (hnd : ∀ x, (∀ y, f y x = 0) → x = 0) : ∃ U : Submodule k V, ∀ x, x ∈ U ↔ ∀ y ∈ U, f y x = 0 := by
  classical
  let φ : V → V →ₗ[k] k := fun y => { toFun := f y, map_add' := hadd y, map_smul' := hsm y }
  have hφ : ∀ y x, φ y x = f y x := fun _ _ => rfl
  have hadd' : ∀ y y' x, f (y + y') x = f y x + f y' x := by
    intro y y' x; rw [hsy x (y + y'), hadd, map_add, ← hsy, ← hsy]
  have hsm' : ∀ (a : k) y x, f (a • y) x = τ a * f y x := by
    intro a y x; rw [hsy x (a • y), hsm, map_mul, ← hsy]
  have hz : ∀ x y, f x y = 0 → f y x = 0 := fun x y h => by rw [hsy, h, map_zero]
  obtain ⟨U, hU, hmax⟩ := (set_has_maximal_iff_noetherian (R := k) (M := V)).2 inferInstance
    {U | ∀ x ∈ U, ∀ y ∈ U, f y x = 0} ⟨⊥, fun x hx y _ => by
      rw [(Submodule.mem_bot k).1 hx]; exact (φ y).map_zero⟩
  let P : Submodule k V := ⨅ y : U, LinearMap.ker (φ y)
  have hP : ∀ x, x ∈ P ↔ ∀ y ∈ U, f y x = 0 := by
    intro x; simp only [P, Submodule.mem_iInf, LinearMap.mem_ker, hφ, Subtype.forall]
  have hUP : U ≤ P := fun x hx => (hP x).2 (hU x hx)
  have hiso : ∀ x ∈ P, f x x = 0 → x ∈ U := by
    intro x hx hxx
    by_contra hxU
    refine hmax (U ⊔ k ∙ x) ?_ (lt_of_le_of_ne le_sup_left fun h => hxU ?_)
    · intro a ha b hb
      obtain ⟨u, hu, a', ha', rfl⟩ := Submodule.mem_sup.1 ha
      obtain ⟨u', hu', b', hb', rfl⟩ := Submodule.mem_sup.1 hb
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 ha'
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb'
      rw [hadd, hadd', hadd', hsm, hsm, hsm', hsm', hU u hu u' hu', (hP x).1 hx u' hu',
        hz _ _ ((hP x).1 hx u hu), hxx]
      ring
    · rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

  have hdim : finrank k P + finrank k U = finrank k V := by
    let b := Module.finBasis k U
    let ψ : V →ₗ[k] (Fin (finrank k U) → k) := LinearMap.pi fun i => φ (b i)
    have hker : LinearMap.ker ψ = P := by
      ext x
      rw [hP, LinearMap.mem_ker]
      constructor
      · intro h y hy
        have h1 : ∀ i, f (b i) x = 0 := fun i => congrFun h i
        have h2 : ∀ z ∈ Submodule.span k (Set.range b), f (z : U) x = 0 := by
          intro z hz'
          induction hz' using Submodule.span_induction with
          | mem z hz => obtain ⟨i, rfl⟩ := hz; exact h1 i
          | zero => exact hz _ _ (φ x).map_zero
          | add z w _ _ h1 h2 => rw [Submodule.coe_add, hadd', h1, h2, add_zero]
          | smul a z _ h1 => rw [Submodule.coe_smul, hsm', h1, mul_zero]
        exact h2 ⟨y, hy⟩ (b.mem_span _)
      · intro h; funext i; exact h _ (b i).2
    have hrange : LinearMap.range ψ = ⊤ := by
      by_contra hne
      obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
      apply hg0
      let a : Fin (finrank k U) → k := fun i => g (Pi.single i 1)
      have hga : ∀ v, g v = ∑ i, v i * a i := by
        intro v
        rw [LinearMap.pi_apply_eq_sum_univ g v]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_eq_mul]; congr 2; funext j; simp [Pi.single_apply, eq_comm]
      have h0 : ((∑ i, τ (a i) • b i : U) : V) = 0 := by
        apply hnd
        intro y
        have h1 : g (ψ y) = 0 := hg ⟨y, rfl⟩
        rw [hga] at h1
        rw [← hφ, Submodule.coe_sum, map_sum]
        have h2 := congrArg τ h1
        rw [map_sum, map_zero] at h2
        rw [← h2]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, hφ, hsm, map_mul, hsy (b i) y, mul_comm]; rfl
      have h1 := Fintype.linearIndependent_iff.1 b.linearIndependent _ (Subtype.ext h0)
      have h2 : ∀ i, a i = 0 := fun i => by rw [← hτ (a i), h1 i, map_zero]
      ext v
      simp [hga, h2]
    have := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hker, hrange, finrank_top, Module.finrank_fin_fun] at this
    omega
  refine ⟨U, fun x => ⟨fun hx => hU x hx, fun hx => ?_⟩⟩
  by_contra hxU
  have hxP := (hP x).2 hx
  have hxx : f x x ≠ 0 := fun h => hxU (hiso x hxP h)
  have hPe : P = U ⊔ k ∙ x := by
    refine le_antisymm (fun y hy => ?_) (sup_le hUP ((Submodule.span_singleton_le_iff_mem _ _).2 hxP))
    let y' := y - (f x y / f x x) • x
    have hy'P : y' ∈ P := P.sub_mem hy (P.smul_mem _ hxP)
    have hxy : f x y' = 0 := by
      rw [← hφ, map_sub, map_smul, hφ, hφ, smul_eq_mul, div_mul_cancel₀ _ hxx, sub_self]
    obtain ⟨a, ha⟩ := hN (-(f y' y') / f x x) (by rw [map_div₀, map_neg, ← hsy, ← hsy])
    have h1 : y' + a • x ∈ U := by
      refine hiso _ (P.add_mem hy'P (P.smul_mem _ hxP)) ?_
      rw [hadd, hadd', hadd', hsm, hsm, hsm', hsm', hxy, hz _ _ hxy, ← mul_assoc, ha,
        div_mul_cancel₀ _ hxx]
      ring
    have : y = (y' + a • x) + (f x y / f x x - a) • x := by
      simp only [y', sub_smul]; abel
    rw [this]
    exact Submodule.add_mem_sup h1 (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x))
  have hx0 : x ≠ 0 := fun h => hxU (h ▸ U.zero_mem)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (k ∙ x)
  have h2 : U ⊓ (k ∙ x) = ⊥ := ((Submodule.disjoint_span_singleton' hx0).2 hxU).eq_bot
  rw [h2, finrank_bot, finrank_span_singleton hx0, ← hPe] at h1
  obtain ⟨m, hm⟩ := hev
  omega

end Lagrangian

section Lattices

variable {E : Type} [Field E] [NumberField E]

abbrev conjO (σ : E →+* E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom σ

theorem map_algebraMap (σ : E →+* E) (o : 𝓞 E) :
    σ (algebraMap (𝓞 E) E o) = algebraMap (𝓞 E) E (conjO σ o) := rfl

theorem conjO_conjO {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) (o : 𝓞 E) : conjO σ (conjO σ o) = o :=
  RingOfIntegers.ext (hσ _)

theorem int_mul_mem (A : FractionalIdeal (𝓞 E)⁰ E) (o : 𝓞 E) {z : E} (hz : z ∈ A) : algebraMap (𝓞 E) E o * z ∈ A := by
  rw [← Algebra.smul_def]; exact A.coeToSubmodule.smul_mem o hz

theorem add_mem' (A : FractionalIdeal (𝓞 E)⁰ E) {z w : E} (hz : z ∈ A) (hw : w ∈ A) : z + w ∈ A :=
  A.coeToSubmodule.add_mem hz hw

theorem one_mem_mul_inv {b : FractionalIdeal (𝓞 E)⁰ E} (hb : b ≠ 0) : (1 : E) ∈ b * b⁻¹ := by
  rw [mul_inv_cancel₀ hb]; exact FractionalIdeal.one_mem_one _

theorem mul_inv_mem {A b : FractionalIdeal (𝓞 E)⁰ E} (hb : b ≠ 0) {z u : E} (hz : z ∈ A * b) (hu : u ∈ b⁻¹) :
    u * z ∈ A := by
  have := FractionalIdeal.mul_mem_mul hz hu
  rwa [mul_assoc, mul_inv_cancel₀ hb, mul_one, mul_comm] at this

theorem cancel_mem {A b : FractionalIdeal (𝓞 E)⁰ E} (hb : b ≠ 0) {z : E} (h : ∀ t ∈ b, t * z ∈ A * b) : z ∈ A := by
  have key : ∀ r ∈ b * b⁻¹, r * z ∈ A := by
    intro r hr
    refine FractionalIdeal.mul_induction_on (C := fun r => r * z ∈ A) hr (fun t ht u hu => ?_) (fun x y hx hy => ?_)
    · have := mul_inv_mem hb (h t ht) hu
      rwa [show u * (t * z) = t * u * z by ring] at this
    · rw [add_mul]; exact add_mem' A hx hy
  simpa using key 1 (one_mem_mul_inv hb)

theorem conj_mul_mem {σ : E →+* E} {A b : FractionalIdeal (𝓞 E)⁰ E} (hA : ∀ z ∈ A, σ z ∈ A) (hb : ∀ z ∈ b, σ z ∈ b) :
    ∀ z ∈ A * b, σ z ∈ A * b := by
  intro z hz
  refine FractionalIdeal.mul_induction_on (C := fun z => σ z ∈ A * b) hz (fun t ht u hu => ?_) (fun x y hx hy => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hA t ht) (hb u hu)
  · rw [map_add]; exact add_mem' _ hx hy

theorem conj_inv_mem {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {A : FractionalIdeal (𝓞 E)⁰ E} (hA0 : A ≠ 0)
    (hA : ∀ z ∈ A, σ z ∈ A) : ∀ z ∈ A⁻¹, σ z ∈ A⁻¹ := by
  intro z hz
  rw [FractionalIdeal.mem_inv_iff hA0] at hz ⊢
  intro y hy
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 (hz (σ y) (hA y hy))
  refine (FractionalIdeal.mem_one_iff _).2 ⟨conjO σ o, ?_⟩
  rw [← map_algebraMap, ho, map_mul, hσ]

variable {d : ℕ}

theorem mem_of_dual {h : (Fin d → E) → (Fin d → E) → E} (hsm : ∀ y (a : E) x, h y (a • x) = a * h y x)
    {A b : FractionalIdeal (𝓞 E)⁰ E} (hb : b ≠ 0) {L : Submodule (𝓞 E) (Fin d → E)}
    (hL : ∀ x, x ∈ L ↔ ∀ y ∈ L, h y x ∈ A) (N : Submodule (𝓞 E) (Fin d → E))
    (hN : ∀ t ∈ b, ∀ y ∈ L, t • y ∈ N) {x : Fin d → E} (hx : ∀ y ∈ L, h y x ∈ A * b) : x ∈ N := by
  have key : ∀ r ∈ b * b⁻¹, r • x ∈ N := by
    intro r hr
    refine FractionalIdeal.mul_induction_on (C := fun r => r • x ∈ N) hr (fun t ht u hu => ?_) (fun x y hx hy => ?_)
    · rw [mul_smul]
      refine hN t ht _ ((hL _).2 fun y hy => ?_)
      rw [hsm]; exact mul_inv_mem hb (hx y hy) hu
    · rw [add_smul]; exact N.add_mem hx hy
  simpa using key 1 (one_mem_mul_inv hb)

theorem span_eq_top_of_smul {L M : Submodule (𝓞 E) (Fin d → E)} (hL : Submodule.span E (L : Set (Fin d → E)) = ⊤)
    {t : E} (ht : t ≠ 0) (hM : ∀ y ∈ L, t • y ∈ M) : Submodule.span E (M : Set (Fin d → E)) = ⊤ := by
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro y hy
  have : y = t⁻¹ • t • y := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hM y hy))

def HasModular (h : (Fin d → E) → (Fin d → E) → E) (A : FractionalIdeal (𝓞 E)⁰ E) : Prop :=
  ∃ L : Submodule (𝓞 E) (Fin d → E), L.FG ∧ Submodule.span E (L : Set (Fin d → E)) = ⊤ ∧
    ∀ x, x ∈ L ↔ ∀ y ∈ L, h y x ∈ A

variable {σ : E →+* E} {h : (Fin d → E) → (Fin d → E) → E}

theorem HasModular.scale (hσ : ∀ x, σ (σ x) = x) (hadd : ∀ y x x', h y (x + x') = h y x + h y x')
    (hsm : ∀ y (a : E) x, h y (a • x) = a * h y x) (hsy : ∀ x y, h y x = σ (h x y))
    {A b b' : FractionalIdeal (𝓞 E)⁰ E} (hb : b ≠ 0) (hb' : ∀ z, z ∈ b' ↔ σ z ∈ b) (hA : HasModular h A) :
    HasModular h (A * b * b') := by
  obtain ⟨L, hfg, hsp, hL⟩ := hA
  have hadd' : ∀ y y' x, h (y + y') x = h y x + h y' x := by
    intro y y' x; rw [hsy x (y + y'), hadd, map_add, ← hsy, ← hsy]
  have hsm' : ∀ (a : E) y x, h (a • y) x = σ a * h y x := by
    intro a y x; rw [hsy x (a • y), hsm, map_mul, ← hsy]
  have h0 : ∀ y, h y 0 = 0 := fun y => by simpa using hsm y 0 0
  have h0' : ∀ x, h 0 x = 0 := fun x => by rw [hsy, h0, map_zero]
  obtain ⟨t₀, ht₀, ht₀b⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hb
  have ht₀E : algebraMap (𝓞 E) E t₀ ≠ 0 := fun e => ht₀ (RingOfIntegers.ext e)
  have hb'0 : b' ≠ 0 := by
    intro e
    have : σ (algebraMap (𝓞 E) E t₀) ∈ b' := (hb' _).2 (by rwa [hσ])
    rw [e, FractionalIdeal.mem_zero_iff] at this
    exact ht₀E (by rw [← hσ (algebraMap (𝓞 E) E t₀), this, map_zero])
  let μ : E →ₗ[𝓞 E] (Fin d → E) →ₗ[𝓞 E] (Fin d → E) :=
    LinearMap.mk₂ (𝓞 E) (fun t y => t • y) add_smul smul_assoc smul_add (fun c t y => smul_comm t c y)
  let M := Submodule.map₂ μ b.coeToSubmodule L
  have hM : ∀ t ∈ b, ∀ y ∈ L, t • y ∈ M := fun t ht y hy => Submodule.apply_mem_map₂ μ ht hy
  refine ⟨M, Submodule.FG.map₂ μ (FractionalIdeal.fg_of_isNoetherianRing le_rfl b) hfg,
    span_eq_top_of_smul hsp ht₀E (hM _ ht₀b), fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩⟩
  · simp only [M, Submodule.map₂_eq_span_image2] at hx hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨u, hu, y, hy, rfl⟩ := hy
        change h (u • y) (t • x) ∈ _
        rw [hsm, hsm', show t * (σ u * h y x) = h y x * t * σ u by ring]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mul_mem_mul ((hL x).1 hx y hy) ht)
          ((hb' _).2 (by rw [hσ]; exact hu))
      | zero => rw [h0']; exact FractionalIdeal.zero_mem _
      | add y y' _ _ h1 h2 => rw [hadd']; exact add_mem' _ h1 h2
      | smul o y _ h1 =>
        rw [← algebraMap_smul E o y, hsm', map_algebraMap]; exact int_mul_mem _ _ h1
    | zero => rw [h0]; exact FractionalIdeal.zero_mem _
    | add x x' _ _ h1 h2 => rw [hadd]; exact add_mem' _ h1 h2
    | smul o x _ h1 => rw [← algebraMap_smul E o x, hsm]; exact int_mul_mem _ _ h1
  · refine mem_of_dual hsm hb hL M hM fun y hy => cancel_mem hb'0 fun t ht => ?_
    have := hx _ (hM _ ((hb' t).1 ht) y hy)
    rwa [hsm', hσ] at this

theorem exists_multiplier (hσ : ∀ x, σ (σ x) = x) {A : FractionalIdeal (𝓞 E)⁰ E} (hA0 : A ≠ 0)
    (hA : ∀ z ∈ A, σ z ∈ A) (p : Ideal (𝓞 E)) (hp : p.IsMaximal) (θ : 𝓞 E) (hθ : conjO σ θ - θ ∉ p) :
    ∃ s : E, σ s = s ∧ s ∈ A⁻¹ ∧ ∃ z ∈ A, ∃ a : 𝓞 E, a ∉ p ∧ algebraMap (𝓞 E) E a = s * z := by
  have hint : ∀ s ∈ A⁻¹, ∀ z ∈ A, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = s * z := fun s hs z hz =>
    (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hA0).1 hs z hz)
  obtain ⟨s, hs, z, hz, hsz⟩ : ∃ s ∈ A⁻¹, ∃ z ∈ A, s * z ∉ (p : FractionalIdeal (𝓞 E)⁰ E) := by
    by_contra hcon
    push Not at hcon
    have hle : A⁻¹ * A ≤ (p : FractionalIdeal (𝓞 E)⁰ E) := FractionalIdeal.mul_le.2 hcon
    rw [inv_mul_cancel₀ hA0] at hle
    obtain ⟨x, hx, hx1⟩ := (FractionalIdeal.mem_coeIdeal _).1 (hle (FractionalIdeal.one_mem_one _))
    have : x = 1 := RingOfIntegers.ext hx1
    exact hp.ne_top ((Ideal.eq_top_iff_one _).2 (this ▸ hx))
  have hs' := conj_inv_mem hσ hA0 hA s hs
  obtain ⟨a, ha⟩ := hint s hs z hz
  obtain ⟨a', ha'⟩ := hint _ hs' z hz
  have hap : a ∉ p := fun e => hsz ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, e, ha⟩)
  have key : ∀ t : 𝓞 E, t * a + conjO σ t * a' ∉ p →
      ∃ s : E, σ s = s ∧ s ∈ A⁻¹ ∧ ∃ z ∈ A, ∃ a : 𝓞 E, a ∉ p ∧ algebraMap (𝓞 E) E a = s * z := by
    intro t ht
    refine ⟨algebraMap (𝓞 E) E t * s + σ (algebraMap (𝓞 E) E t * s), by rw [map_add, hσ, add_comm], ?_, z, hz, _, ht, ?_⟩
    · refine add_mem' _ (int_mul_mem _ _ hs) ?_
      rw [map_mul, map_algebraMap]; exact int_mul_mem _ _ hs'
    · rw [map_add, map_mul, map_mul, map_mul, ha, ha', map_algebraMap]; ring
  by_cases h1 : 1 * a + conjO σ 1 * a' ∈ p
  · refine key θ fun h2 => ?_
    have h3 : (conjO σ θ - θ) * a ∈ p := by
      have := p.sub_mem (p.mul_mem_left (conjO σ θ) h1) h2
      rw [map_one] at this
      convert this using 1; ring
    exact (hp.isPrime.mem_or_mem h3).elim hθ hap
  · exact key 1 h1

theorem HasModular.inert (hσ : ∀ x, σ (σ x) = x) (hadd : ∀ y x x', h y (x + x') = h y x + h y x')
    (hsm : ∀ y (a : E) x, h y (a • x) = a * h y x) (hsy : ∀ x y, h y x = σ (h x y)) (hd : Even d)
    {A : FractionalIdeal (𝓞 E)⁰ E} (hA0 : A ≠ 0) (hAσ : ∀ z ∈ A, σ z ∈ A) (p : Ideal (𝓞 E)) (hp : p.IsMaximal)
    (hp0 : p ≠ ⊥) (hpσ : ∀ o ∈ p, conjO σ o ∈ p) (θ : 𝓞 E) (hθ : conjO σ θ - θ ∉ p) (hA : HasModular h A) :
    HasModular h (A * (p : FractionalIdeal (𝓞 E)⁰ E)) := by
  obtain ⟨L, hfg, hsp, hL⟩ := hA
  have hsm' : ∀ (a : E) y x, h (a • y) x = σ a * h y x := by
    intro a y x; rw [hsy x (a • y), hsm, map_mul, ← hsy]
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective _ _
  have hP0 : (p : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hp0
  obtain ⟨s, hsσ, hs, z₀, hz₀, a₀, ha₀p, ha₀⟩ := exists_multiplier hσ hA0 hAσ p hp θ hθ
  have hint : ∀ z ∈ A, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = s * z := fun z hz =>
    (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hA0).1 hs z hz)
  have hiff : ∀ z ∈ A, ∀ a : 𝓞 E, algebraMap (𝓞 E) E a = s * z →
      (a ∈ p ↔ z ∈ A * (p : FractionalIdeal (𝓞 E)⁰ E)) := by
    intro z hz a ha
    constructor
    · intro hap
      obtain ⟨y, i, hi, e⟩ := hp.exists_inv ha₀p
      have e' := congrArg (algebraMap (𝓞 E) E) e
      rw [map_add, map_mul, map_one, ha₀] at e'
      have : z = algebraMap (𝓞 E) E y * (z₀ * algebraMap (𝓞 E) E a) + z * algebraMap (𝓞 E) E i := by
        rw [ha]; linear_combination (-z) * e'
      rw [this]
      exact add_mem' _ (int_mul_mem _ _ (FractionalIdeal.mul_mem_mul hz₀ (FractionalIdeal.mem_coeIdeal_of_mem _ hap)))
        (FractionalIdeal.mul_mem_mul hz (FractionalIdeal.mem_coeIdeal_of_mem _ hi))
    · intro hz'
      rw [mul_comm] at hz'
      have := mul_inv_mem hA0 hz' hs
      obtain ⟨c, hc, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 this
      rwa [hinj (ha.trans e.symm)]
  have hLL : ∀ y x : L, h y x ∈ A := fun y x => (hL x).1 x.2 y y.2
  choose g hg using fun y x : L => hint _ (hLL y x)
  have gadd : ∀ y x x', g y (x + x') = g y x + g y x' := fun y x x' => hinj (by
    rw [map_add, hg, hg, hg, Submodule.coe_add, hadd, mul_add])
  have gsm : ∀ y (o : 𝓞 E) x, g y (o • x) = o * g y x := fun y o x => hinj (by
    rw [map_mul, hg, hg, Submodule.coe_smul, ← algebraMap_smul E o, hsm]; ring)
  have gsy : ∀ x y, g y x = conjO σ (g x y) := fun x y => hinj (by
    rw [← map_algebraMap, hg, hg, map_mul, hsσ, ← hsy])
  let G : L → L →ₗ[𝓞 E] 𝓞 E := fun y => { toFun := g y, map_add' := gadd y, map_smul' := gsm y }
  have gp : ∀ y x, x ∈ (p • ⊤ : Submodule (𝓞 E) L) → g y x ∈ p := by
    intro y x hx
    refine Submodule.smul_induction_on (p := fun x => g y x ∈ p) hx (fun r hr n _ => ?_) (fun u v hu hv => ?_)
    · rw [gsm]; exact p.mul_mem_right _ hr
    · rw [gadd]; exact p.add_mem hu hv
  letI : Field (𝓞 E ⧸ p) := Ideal.Quotient.field p
  haveI : Finite (𝓞 E ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hp0
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  let Q := L ⧸ (p • ⊤ : Submodule (𝓞 E) L)
  haveI : Module.Finite (𝓞 E ⧸ p) Q := Module.Finite.of_restrictScalars_finite (𝓞 E) _ _
  let τ : 𝓞 E ⧸ p →+* 𝓞 E ⧸ p := Ideal.quotientMap p (conjO σ) hpσ
  have hτ : ∀ o, τ (Ideal.Quotient.mk p o) = Ideal.Quotient.mk p (conjO σ o) := fun o => rfl
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hτ, hτ, conjO_conjO hσ]
  let π : L →ₗ[𝓞 E] Q := Submodule.mkQ _
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  choose sec hsec using hπ
  have hπ : ∀ v, ∃ x, π x = v := fun v => ⟨sec v, hsec v⟩
  let f : Q → Q → 𝓞 E ⧸ p := fun v w => Ideal.Quotient.mk p (g (sec v) (sec w))
  have hcl : ∀ y x x', π x = π x' → Ideal.Quotient.mk p (g y x) = Ideal.Quotient.mk p (g y x') := by
    intro y x x' e
    rw [Ideal.Quotient.eq]
    have := gp y _ ((Submodule.Quotient.eq _).1 e)
    rwa [show g y (x - x') = g y x - g y x' from (G y).map_sub x x'] at this
  have hf : ∀ y x, f (π y) (π x) = Ideal.Quotient.mk p (g y x) := by
    intro y x
    simp only [f]
    rw [hcl _ _ _ (hsec _), gsy, ← hτ, hcl _ _ _ (hsec _), hτ, ← gsy]
  have hf0 : ∀ y x : L, f (π y) (π x) = 0 ↔ h y x ∈ A * (p : FractionalIdeal (𝓞 E)⁰ E) := by
    intro y x
    rw [hf, Ideal.Quotient.eq_zero_iff_mem, hiff _ (hLL y x) _ (hg y x)]
  obtain ⟨U, hU⟩ := exists_lagrangian τ hττ
    (GlobalTheory.exists_mul_invol_eq_of_fixed _ τ hττ ⟨Ideal.Quotient.mk p θ, by
      rw [hτ]; exact fun e => hθ (Ideal.Quotient.eq.1 e)⟩)
    (V := Q) (by rw [finrank_quot L hfg hsp p, Module.finrank_fin_fun]; exact hd) f
    (by
      intro y x x'
      obtain ⟨y, rfl⟩ := hπ y; obtain ⟨x, rfl⟩ := hπ x; obtain ⟨x', rfl⟩ := hπ x'
      rw [← map_add, hf, hf, hf, gadd, map_add])
    (by
      intro y a x
      obtain ⟨y, rfl⟩ := hπ y; obtain ⟨x, rfl⟩ := hπ x; obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      have : Ideal.Quotient.mk p a • π x = π (a • x) := rfl
      rw [this, hf, hf, gsm, map_mul])
    (by
      intro x y
      obtain ⟨y, rfl⟩ := hπ y; obtain ⟨x, rfl⟩ := hπ x
      rw [hf, hf, hτ, ← gsy])
    (by
      intro x hx
      obtain ⟨x, rfl⟩ := hπ x
      have := mem_of_dual hsm hP0 hL ((p • ⊤ : Submodule (𝓞 E) L).map L.subtype) (fun t ht y hy => by
        obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ht
        exact ⟨c • ⟨y, hy⟩, Submodule.smul_mem_smul hc trivial, (algebraMap_smul E c y).symm⟩)
        (x := x) (fun y hy => (hf0 ⟨y, hy⟩ x).1 (hx _))
      obtain ⟨x', hx', e⟩ := this
      rw [← Subtype.ext e]
      exact (Submodule.Quotient.mk_eq_zero _).2 hx')
  let M : Submodule (𝓞 E) (Fin d → E) := ((U.restrictScalars (𝓞 E)).comap π).map L.subtype
  have hM : ∀ x : L, (x : Fin d → E) ∈ M ↔ π x ∈ U := fun x =>
    ⟨fun ⟨x', hx', e⟩ => Subtype.ext e ▸ hx', fun hx => ⟨x, hx, rfl⟩⟩
  have hML : M ≤ L := Submodule.map_subtype_le _ _
  have hpM : ∀ c ∈ p, ∀ y ∈ L, algebraMap (𝓞 E) E c • y ∈ M := by
    intro c hc y hy
    rw [algebraMap_smul]
    refine (hM (c • ⟨y, hy⟩)).2 ?_
    have : π (c • ⟨y, hy⟩) = 0 := (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hc trivial)
    rw [this]; exact U.zero_mem
  obtain ⟨c₀, hc₀, hc₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  refine ⟨M, Submodule.FG.map _ (IsNoetherian.noetherian _),
    span_eq_top_of_smul hsp (fun e => hc₀0 (hinj (e.trans (map_zero _).symm))) (hpM c₀ hc₀),
    fun x => ⟨fun hx y hy => ?_, fun hx => ?_⟩⟩
  · exact (hf0 ⟨y, hML hy⟩ ⟨x, hML hx⟩).1 ((hU _).1 ((hM ⟨x, hML hx⟩).1 hx) _ ((hM ⟨y, hML hy⟩).1 hy))
  · have hxL : x ∈ L := by
      refine (hL x).2 fun y hy => cancel_mem hP0 fun t ht => ?_
      obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ht
      have := hx _ (hpM _ (hpσ c hc) y hy)
      rwa [hsm', map_algebraMap, conjO_conjO hσ] at this
    refine (hM ⟨x, hxL⟩).2 ((hU _).2 fun u hu => ?_)
    obtain ⟨y, rfl⟩ := hπ u
    exact (hf0 y ⟨x, hxL⟩).2 (hx y ((hM y).2 hu))

theorem HasModular.mul_ideal (hσ : ∀ x, σ (σ x) = x) (hadd : ∀ y x x', h y (x + x') = h y x + h y x')
    (hsm : ∀ y (a : E) x, h y (a • x) = a * h y x) (hsy : ∀ x y, h y x = σ (h x y)) (hd : Even d)
    (hun : ∀ p : Ideal (𝓞 E), p.IsMaximal → ∃ θ, conjO σ θ - θ ∉ p) (I : Ideal (𝓞 E)) :
    I ≠ ⊥ → (∀ o ∈ I, conjO σ o ∈ I) → ∀ A : FractionalIdeal (𝓞 E)⁰ E, A ≠ 0 → (∀ z ∈ A, σ z ∈ A) →
      HasModular h A → HasModular h (A * (I : FractionalIdeal (𝓞 E)⁰ E)) := by
  induction I using IsNoetherian.induction with
  | hgt I ih =>
  intro hI0 hIσ A hA0 hAσ hA
  have hcoe : ∀ J : Ideal (𝓞 E), (∀ o ∈ J, conjO σ o ∈ J) →
      ∀ z ∈ (J : FractionalIdeal (𝓞 E)⁰ E), σ z ∈ (J : FractionalIdeal (𝓞 E)⁰ E) := by
    intro J hJ z hz
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    exact FractionalIdeal.mem_coeIdeal_of_mem _ (hJ c hc)
  have step : ∀ P : Ideal (𝓞 E), P ≠ ⊤ → (∀ o ∈ P, conjO σ o ∈ P) → I ≤ P →
      HasModular h (A * (P : FractionalIdeal (𝓞 E)⁰ E)) → HasModular h (A * (I : FractionalIdeal (𝓞 E)⁰ E)) := by
    intro P hPt hPσ hIP hAP
    obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 hIP
    have hP0 : P ≠ ⊥ := left_ne_zero_of_mul hI0
    have hJ0 : J ≠ ⊥ := right_ne_zero_of_mul hI0
    have hP0' : (P : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hP0
    have hlt : P * J < J := by
      refine lt_of_le_of_ne Ideal.mul_le_right fun e => hPt ?_
      have : P * J = 1 * J := by rw [one_mul]; exact e
      rw [mul_right_cancel₀ hJ0 this, Ideal.one_eq_top]
    have hJσ : ∀ o ∈ J, conjO σ o ∈ J := by
      intro o ho
      have : algebraMap (𝓞 E) E (conjO σ o) ∈ (J : FractionalIdeal (𝓞 E)⁰ E) := by
        refine cancel_mem hP0' fun t ht => ?_
        have h1 := FractionalIdeal.mul_mem_mul (hcoe P hPσ t ht) (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ ho)
        rw [← FractionalIdeal.coeIdeal_mul] at h1
        have h2 := hcoe _ hIσ _ h1
        rwa [map_mul, hσ, FractionalIdeal.coeIdeal_mul, mul_comm (P : FractionalIdeal (𝓞 E)⁰ E)] at h2
      obtain ⟨c, hc, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 this
      rwa [← IsFractionRing.injective (𝓞 E) E e]
    rw [FractionalIdeal.coeIdeal_mul, ← mul_assoc]
    exact ih J hlt hJ0 hJσ _ (mul_ne_zero hA0 hP0') (conj_mul_mem hAσ (hcoe P hPσ)) hAP
  by_cases hIt : I = ⊤
  · rw [hIt, FractionalIdeal.coeIdeal_top, mul_one]; exact hA
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hIt
  have hp0 : p ≠ ⊥ := fun e => hI0 (le_bot_iff.1 (e ▸ hIp))
  by_cases hpσ : ∀ o ∈ p, conjO σ o ∈ p
  · obtain ⟨θ, hθ⟩ := hun p hp
    exact step p hp.ne_top hpσ hIp (hA.inert hσ hadd hsm hsy hd hA0 hAσ p hp hp0 hpσ θ hθ)
  · let q : Ideal (𝓞 E) := p.comap (conjO σ)
    have hq : ∀ o, o ∈ q ↔ conjO σ o ∈ p := fun o => Iff.rfl
    have hpq : p ⊔ q = ⊤ := by
      refine hp.out.2 _ (lt_of_le_of_ne le_sup_left fun e => hpσ fun o ho => ?_)
      rw [e]
      exact Ideal.mem_sup_right ((hq _).2 (by rwa [conjO_conjO hσ]))
    have hinf : p * q = p ⊓ q := Ideal.mul_eq_inf_of_coprime hpq
    refine step (p * q) (fun e => hp.ne_top (top_le_iff.1 (e ▸ Ideal.mul_le_left))) ?_ ?_ ?_
    · intro o ho
      rw [hinf] at ho ⊢
      exact ⟨ho.2, (hq _).2 (by rw [conjO_conjO hσ]; exact ho.1)⟩
    · rw [hinf]; exact fun o ho => ⟨hIp ho, hIp (hIσ o ho)⟩
    · rw [FractionalIdeal.coeIdeal_mul, ← mul_assoc]
      refine hA.scale hσ hadd hsm hsy (FractionalIdeal.coeIdeal_ne_zero.2 hp0) fun z => ⟨fun hz => ?_, fun hz => ?_⟩
      · obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
        exact FractionalIdeal.mem_coeIdeal_of_mem _ ((hq c).1 hc)
      · obtain ⟨c, hc, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
        refine (FractionalIdeal.mem_coeIdeal _).2 ⟨conjO σ c, (hq _).2 (by rwa [conjO_conjO hσ]), ?_⟩
        rw [← map_algebraMap, e, hσ]

theorem HasModular.one (hσ : ∀ x, σ (σ x) = x) (hadd : ∀ y x x', h y (x + x') = h y x + h y x')
    (hsm : ∀ y (a : E) x, h y (a • x) = a * h y x) (hsy : ∀ x y, h y x = σ (h x y)) (hd : Even d)
    (hun : ∀ p : Ideal (𝓞 E), p.IsMaximal → ∃ θ, conjO σ θ - θ ∉ p) {A : FractionalIdeal (𝓞 E)⁰ E} (hA0 : A ≠ 0)
    (hAσ : ∀ z ∈ A, σ z ∈ A) (hA : HasModular h A) : HasModular h 1 := by
  obtain ⟨a, ha0, haA⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hA0
  set e := algebraMap (𝓞 E) E a with he
  have he0 : e ≠ 0 := fun h => ha0 (RingOfIntegers.ext h)
  have hσe0 : σ e ≠ 0 := fun h => he0 (by rw [← hσ e, h, map_zero])
  let b := FractionalIdeal.spanSingleton (𝓞 E)⁰ e⁻¹
  let b' := FractionalIdeal.spanSingleton (𝓞 E)⁰ (σ e)⁻¹
  have hb : b ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 (inv_ne_zero he0)
  have hb' : b' ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 (inv_ne_zero hσe0)
  have h1 : ∀ z ∈ b, σ z ∈ b' := by
    intro z hz
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hz
    rw [Algebra.smul_def, map_mul, map_algebraMap, map_inv₀]
    exact int_mul_mem _ _ (FractionalIdeal.mem_spanSingleton_self _ _)
  have h2 : ∀ z ∈ b', σ z ∈ b := by
    intro z hz
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hz
    rw [Algebra.smul_def, map_mul, map_algebraMap, map_inv₀, hσ]
    exact int_mul_mem _ _ (FractionalIdeal.mem_spanSingleton_self _ _)
  have hB := hA.scale hσ hadd hsm hsy hb (b' := b') fun z => ⟨h2 z, fun hz => hσ z ▸ h1 _ hz⟩
  have hbb : ∀ z ∈ b * b', σ z ∈ b * b' := by
    intro z hz
    refine FractionalIdeal.mul_induction_on (C := fun z => σ z ∈ b * b') hz (fun t ht u hu => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, mul_comm (σ t)]; exact FractionalIdeal.mul_mem_mul (h2 u hu) (h1 t ht)
    · rw [map_add]; exact add_mem' _ hx hy
  have hB0 : A * b * b' ≠ 0 := mul_ne_zero (mul_ne_zero hA0 hb) hb'
  have hBσ : ∀ z ∈ A * b * b', σ z ∈ A * b * b' := by
    rw [mul_assoc]; exact conj_mul_mem hAσ hbb
  have hB1 : (1 : E) ∈ A * b * b' := by
    have := FractionalIdeal.mul_mem_mul (FractionalIdeal.mul_mem_mul (int_mul_mem A (conjO σ a) haA)
      (FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰ e⁻¹)) (FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰ (σ e)⁻¹)
    rwa [← map_algebraMap, ← he, show σ e * e * e⁻¹ * (σ e)⁻¹ = 1 by field_simp] at this
  have hle : (A * b * b')⁻¹ ≤ 1 := by
    intro z hz
    simpa using (FractionalIdeal.mem_inv_iff hB0).1 hz 1 hB1
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have := HasModular.mul_ideal hσ hadd hsm hsy hd hun I
    (FractionalIdeal.coeIdeal_ne_zero.1 (hI ▸ inv_ne_zero hB0)) (by
      intro o ho
      have h3 := FractionalIdeal.mem_coeIdeal_of_mem (𝓞 E)⁰ (P := E) ho
      rw [hI] at h3
      have h4 := conj_inv_mem hσ hB0 hBσ _ h3
      rw [← hI] at h4
      obtain ⟨c, hc, e⟩ := (FractionalIdeal.mem_coeIdeal _).1 h4
      rw [map_algebraMap] at e
      rwa [← IsFractionRing.injective (𝓞 E) E e]) _ hB0 hBσ hB
  rwa [hI, mul_inv_cancel₀ hB0] at this

end Lattices

end GlobalTheory.ModularLattice
