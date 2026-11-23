import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SigmaCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMulDvdUnif

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def cnt (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (n : 𝓞 F)
    (Ω : Set V) : ℕ :=
  Nat.card {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
    ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω}

def fixS (x : V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g x = x}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a (b x) = x
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    change a.symm x = x
    rw [LinearEquiv.symm_apply_eq]
    exact ha.symm

theorem mem_fixS {x : V} {g : V ≃ₗ[K] V} : g ∈ fixS x ↔ g x = x := Iff.rfl

def tube (D : Subgroup (V ≃ₗ[K] V)) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (J : ℕ) (x : V) :
    Set V :=
  {y | ∃ g ∈ D, y - g x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V)}

theorem finite_quot {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Finite (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))) := by
  have : Module.Finite (𝓞 K) ↥A₀ := Module.Finite.iff_fg.2 hA₀.fg
  have : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := idealPowerSpanBounds.finite_quot h𝔭 k
  have : Module.Finite (𝓞 K ⧸ extP K 𝔭 ^ k)
      (↥A₀ ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A₀)) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) _ _
  have : Finite (↥A₀ ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A₀)) :=
    Module.finite_of_finite (𝓞 K ⧸ extP K 𝔭 ^ k)
  exact Finite.of_equiv _ (localizedQuotients.quotLocF h𝔭 A₀ k).toEquiv

theorem cnt_congr (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (n : 𝓞 F) {Ω Ω' : Set V}
    (hΩ : ∀ y ∈ A, CongrP 𝔭 k (h y y) (algebraMap F K (n : F)) → (y ∈ Ω ↔ y ∈ Ω')) :
    cnt h A 𝔭 k n Ω = cnt h A 𝔭 k n Ω' := by
  unfold cnt
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    exists_congr fun y => and_congr_right fun _ => and_congr_right fun hc => hΩ y y.2 hc)

theorem cnt_eq_nkCount (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (n : 𝓞 F) {Ω : Set V}
    (hΩ : ∀ y ∈ A, CongrP 𝔭 k (h y y) (algebraMap F K (n : F)) → y ∈ Ω) :
    cnt h A 𝔭 k n Ω = nkCount h A 𝔭 k n := by
  unfold cnt nkCount
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x =>
    exists_congr fun y => and_congr_right fun _ => ⟨fun h => h.1, fun hc => ⟨hc, hΩ y y.2 hc⟩⟩)

theorem cnt_biUnion (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (n : 𝓞 F) (hfin : Finite (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)))
    {ι : Type*} (s : Finset ι) (Ω : ι → Set V)
    (hst : ∀ i ∈ s, ∀ y ∈ Ω i, ∀ z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V), y + z ∈ Ω i)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ω i) (Ω j)) :
    cnt h A 𝔭 k n (⋃ i ∈ s, Ω i) = ∑ i ∈ s, cnt h A 𝔭 k n (Ω i) := by
  classical
  have := Fintype.ofFinite (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A))
  unfold cnt
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_biUnion]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨y, e, hc, i, hi, hy⟩
      exact ⟨i, hi, y, e, hc, hy⟩
    · rintro ⟨i, hi, y, e, hc, hy⟩
      exact ⟨y, e, hc, i, hi, hy⟩
  · intro i hi j hj hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    obtain ⟨y, e, -, hy⟩ := hx
    obtain ⟨y', e', -, hy'⟩ := hx'
    have h1 : y' - y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
      rw [← Submodule.Quotient.eq, e, e']
    rw [Submodule.mem_smul_top_iff] at h1
    have h2 := hst i hi y hy _ h1
    have h3 : (y : V) + ((y' - y : ↥A) : V) = y' := by
      simp
    rw [h3] at h2
    exact Set.disjoint_left.1 (hdis i hi j hj hij) h2 hy'

theorem cnt_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (n : 𝓞 F) (Ω : Set V) :
    cnt h (Formalism.HermitianLatticesTheory.gmap g A) 𝔭 k n (g '' Ω) = cnt h A 𝔭 k n Ω := by
  let e : ↥A ≃ₗ[𝓞 K] ↥(Formalism.HermitianLatticesTheory.gmap g A) := (g.restrictScalars (𝓞 K)).submoduleMap A
  have he : ∀ y : ↥A, ((e y : ↥(Formalism.HermitianLatticesTheory.gmap g A)) : V) = g y := fun y => rfl
  have hmap : ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A).map (e : ↥A →ₗ[𝓞 K] ↥(Formalism.HermitianLatticesTheory.gmap g A)) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(Formalism.HermitianLatticesTheory.gmap g A)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let E := Submodule.Quotient.equiv _ _ e hmap
  have hE : ∀ y : ↥A, E (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e y) := fun y => rfl
  refine (Nat.card_congr (Equiv.subtypeEquiv E.toEquiv fun x => ?_)).symm
  constructor
  · rintro ⟨y, rfl, hc, hy⟩
    refine ⟨e y, (hE y).symm, ?_, y, hy, (he y).symm⟩
    rw [he, hg]
    exact hc
  · rintro ⟨y', e', hc, w, hw, hwy⟩
    obtain ⟨y, rfl⟩ := e.surjective y'
    refine ⟨y, E.injective ?_, ?_, ?_⟩
    · rw [hE]; exact e'
    · rw [he, hg] at hc
      exact hc
    · rw [he] at hwy
      rw [← g.injective hwy]
      exact hw

theorem form_right_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {A : Submodule (𝓞 K) V} (hA : locF 𝔭 A = A) (hAi : IsIntegralAt 𝔭 h A) {k : ℕ} {y z : V}
    (hy : y ∈ A) (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) : h y z ∈ D2.pK K 𝔭 k := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  rw [← hA] at hz
  obtain ⟨w, hw, rfl⟩ := (D2.mem_smul_iff_unif h𝔭 hπ hπ' A).1 hz
  rw [hA] at hw
  rw [map_smul, smul_eq_mul]
  have h1 := hAi y hy w hw
  rw [D2.locF_one_eq] at h1
  simpa using D2.mul_mem_pK h𝔭 (D2.unif_pow_mem_pK (K := K) hπ k) h1

theorem form_left_mem (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {A : Submodule (𝓞 K) V} (hA : locF 𝔭 A = A) (hAi : IsIntegralAt 𝔭 h A)
    {k : ℕ} {y z : V} (hy : y ∈ A) (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) :
    h z y ∈ D2.pK K 𝔭 k := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  rw [← hA] at hz
  obtain ⟨w, hw, rfl⟩ := (D2.mem_smul_iff_unif h𝔭 hπ hπ' A).1 hz
  rw [hA] at hw
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_pow,
    MeanB.star_algebraMap hF]
  have h1 := hAi w hw y hy
  rw [D2.locF_one_eq] at h1
  simpa using D2.mul_mem_pK h𝔭 (D2.unif_pow_mem_pK (K := K) hπ k) h1

theorem congrP_add_of_mem (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {A : Submodule (𝓞 K) V} (hA : locF 𝔭 A = A) (hAi : IsIntegralAt 𝔭 h A)
    {k : ℕ} {y z : V} (hy : y ∈ A) (hz : z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V)) {c : K}
    (hc : CongrP 𝔭 k (h y y) c) : CongrP 𝔭 k (h (y + z) (y + z)) c := by
  rw [D2.congrP_algebraMap_iff_sub_mem h𝔭] at hc ⊢
  have hzA : z ∈ A := Submodule.smul_le_right hz
  have e : h (y + z) (y + z) - c = (h y y - c) + h y z + h z y + h z z := by
    simp only [map_add, LinearMap.add_apply]
    ring
  rw [e]
  exact add_mem (add_mem (add_mem hc (form_right_mem h𝔭 hA hAi hy hz))
    (form_left_mem hF h𝔭 hA hAi hy hz)) (form_right_mem h𝔭 hA hAi hzA hz)

theorem cnt_sub (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {A B : Submodule (𝓞 K) V} (hA : locF 𝔭 A = A) (hB : locF 𝔭 B = B)
    (hAi : IsIntegralAt 𝔭 h A) (hBA : B ≤ A) {k : ℕ}
    (hk : ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V) ≤ B)
    (hfin : Finite (↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B))) (n : 𝓞 F) {Ω : Set V}
    (hΩB : Ω ⊆ B) (hΩ : ∀ y ∈ Ω, ∀ z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V), y + z ∈ Ω) :
    cnt h B 𝔭 k n Ω = Nat.card (↥A ⧸ B.submoduleOf A) * cnt h A 𝔭 k n Ω := by
  obtain ⟨π, hπ, hπ'⟩ := D2.exists_unif h𝔭
  obtain ⟨c, hc⟩ : ∃ c : K, c = algebraMap F K (π : F) ^ k := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by rw [hc]; exact pow_ne_zero _ (D2.unif_ne_zero hπ')
  have memA : ∀ x : V, x ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V) ↔ ∃ y ∈ A, x = c • y := by
    intro x
    have := D2.mem_smul_iff_unif h𝔭 hπ hπ' A (k := k) (x := x)
    rwa [hA, ← hc] at this
  have memB : ∀ x : V, x ∈ ((extP K 𝔭) ^ k • B : Submodule (𝓞 K) V) ↔ ∃ y ∈ B, x = c • y := by
    intro x
    have := D2.mem_smul_iff_unif h𝔭 hπ hπ' B (k := k) (x := x)
    rwa [hB, ← hc] at this
  let m : ↥A →ₗ[𝓞 K] ↥B := LinearMap.codRestrict B
    (((LinearMap.lsmul K V c).restrictScalars (𝓞 K)).comp A.subtype)
    (fun a => hk ((memA _).2 ⟨a, a.2, rfl⟩))
  have hm : ∀ a : ↥A, ((m a : ↥B) : V) = c • (a : V) := fun a => rfl
  let ψ : ↥A →ₗ[𝓞 K] (↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B)) :=
    (Submodule.mkQ _).comp m
  have hψ : ∀ a : ↥A, ψ a = Submodule.Quotient.mk (m a) := fun a => rfl
  have hker : LinearMap.ker ψ = B.submoduleOf A := by
    ext a
    rw [LinearMap.mem_ker, hψ, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, hm, memB]
    change _ ↔ (a : V) ∈ B
    constructor
    · rintro ⟨y, hy, e⟩
      rw [smul_right_injective V hc0 e]
      exact hy
    · intro ha
      exact ⟨a, ha, rfl⟩
  let ψb : (↥A ⧸ B.submoduleOf A) →ₗ[𝓞 K] (↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B)) :=
    Submodule.liftQ _ ψ hker.ge
  have hψb : ∀ a : ↥A, ψb (Submodule.Quotient.mk a) = Submodule.Quotient.mk (m a) := fun a => rfl
  have ψb_inj : Function.Injective ψb := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  let φ : (↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B)) →ₗ[𝓞 K]
      (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
    Submodule.mapQ _ _ (Submodule.inclusion hBA) (by
      intro y hy
      rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
      rw [Submodule.mem_smul_top_iff] at hy
      exact Submodule.smul_mono le_rfl hBA hy)
  have hφ : ∀ y : ↥B, φ (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (Submodule.inclusion hBA y) := fun y => rfl
  have hφψ : ∀ q, φ (ψb q) = 0 := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hψb, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff]
    exact (memA _).2 ⟨a, a.2, rfl⟩
  choose y0 hy0 using fun x : {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
    ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} => x.2
  let yB : {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
    ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} → ↥B :=
    fun x => ⟨y0 x, hΩB (hy0 x).2.2⟩
  have hφy : ∀ x, φ (Submodule.Quotient.mk (yB x)) = x.1 := fun x => (hy0 x).1
  let Fn : (↥A ⧸ B.submoduleOf A) × {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
    ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} →
      {x : ↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B) //
    ∃ y : ↥B, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} :=
    fun p => ⟨Submodule.Quotient.mk (yB p.2) + ψb p.1, by
      obtain ⟨q, x⟩ := p
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hz : c • (a : V) ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V) := (memA _).2 ⟨a, a.2, rfl⟩
      exact ⟨yB x + m a, rfl, congrP_add_of_mem hF h𝔭 hA hAi (y0 x).2 hz (hy0 x).2.1,
        hΩ _ (hy0 x).2.2 _ hz⟩⟩
  have hFn : ∀ p, (Fn p).1 = Submodule.Quotient.mk (yB p.2) + ψb p.1 := fun p => rfl
  have hbij : Function.Bijective Fn := by
    constructor
    · rintro ⟨q, x⟩ ⟨q', x'⟩ e
      have e1 := congrArg Subtype.val e
      rw [hFn, hFn] at e1
      have e2 := congrArg φ e1
      simp only [map_add, hφψ, hφy, add_zero] at e2
      have e3 : x = x' := Subtype.ext e2
      subst e3
      have e4 : q = q' := ψb_inj (add_left_cancel e1)
      rw [e4]
    · rintro ⟨_, y, rfl, hcy, hyΩ⟩
      let x : {x : ↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) //
        ∃ y : ↥A, Submodule.Quotient.mk y = x ∧
        CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F)) ∧ (y : V) ∈ Ω} :=
        ⟨Submodule.Quotient.mk (Submodule.inclusion hBA y), _, rfl, hcy, hyΩ⟩
      have h1 : Submodule.inclusion hBA y - y0 x ∈
          ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
        rw [← Submodule.Quotient.eq]
        exact (hy0 x).1.symm
      rw [Submodule.mem_smul_top_iff, memA] at h1
      obtain ⟨a, ha, e⟩ := h1
      refine ⟨(Submodule.Quotient.mk ⟨a, ha⟩, x), Subtype.ext ?_⟩
      rw [hFn, hψb, ← Submodule.Quotient.mk_add]
      congr 1
      apply Subtype.ext
      change ((y0 x : ↥A) : V) + c • a = y
      rw [← e]
      change ((y0 x : ↥A) : V) + ((y : V) - (y0 x : ↥A)) = y
      abel
  exact (Nat.card_congr (Equiv.ofBijective Fn hbij)).symm.trans (Nat.card_prod _ _)

end Formalism.HermitianLattices.Ext.L3.LIOrb
