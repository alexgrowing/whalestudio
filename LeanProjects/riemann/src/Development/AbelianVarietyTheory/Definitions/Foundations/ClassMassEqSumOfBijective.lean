import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit

noncomputable section

open Formalism.UG

namespace GlobalTheory.Mass

section Abstract

variable {G : Type} [Group G]

def stabOrder (Γ K : Subgroup G) : ClassSet Γ K → ℕ :=
  Quotient.lift (fun g => Nat.card (stabAt Γ K g)) fun a b h => by
    obtain ⟨γ, hγ, k, hk, rfl⟩ := DoubleCoset.rel_iff.1 h
    exact (Formalism.UG.P.card_stabAt_mul Γ K a ⟨γ, hγ⟩ ⟨k, hk⟩).symm

@[simp] theorem stabOrder_mk (Γ K : Subgroup G) (g : G) :
    stabOrder Γ K (DoubleCoset.mk Γ K g) = Nat.card (stabAt Γ K g) := rfl

def FiniteClasses (Γ K : Subgroup G) : Prop :=
  Finite (ClassSet Γ K) ∧ ∀ g : G, Finite (stabAt Γ K g)

def classMass (Γ K : Subgroup G) : ℝ := ∑ᶠ c : ClassSet Γ K, ((stabOrder Γ K c : ℝ))⁻¹

variable {Γ K K' : Subgroup G}

theorem one_mem_stabAt (Γ K : Subgroup G) (g : G) : (1 : Γ) ∈ stabAt Γ K g := by simp [stabAt]

theorem FiniteClasses.stabOrder_pos (h : FiniteClasses Γ K) (c : ClassSet Γ K) : 0 < stabOrder Γ K c := by
  induction c using Quotient.inductionOn' with
  | h g =>
    haveI := h.2 g
    haveI : Nonempty (stabAt Γ K g) := ⟨⟨1, one_mem_stabAt Γ K g⟩⟩
    exact Nat.card_pos (α := stabAt Γ K g)

theorem classMass_eq_sum [Fintype (ClassSet Γ K)] :
    classMass Γ K = ∑ c : ClassSet Γ K, ((stabOrder Γ K c : ℝ))⁻¹ := finsum_eq_sum_of_fintype _

theorem classMass_eq_sum_of_bijective {ι : Type*} [Fintype ι] (g : ι → G)
    (hg : Function.Bijective fun i => (DoubleCoset.mk Γ K (g i) : ClassSet Γ K)) :
    classMass Γ K = ∑ i, ((Nat.card (stabAt Γ K (g i)) : ℝ))⁻¹ := by
  rw [classMass, ← finsum_comp _ hg, finsum_eq_sum_of_fintype]
  rfl

theorem classMass_eq_finsum_out (Γ K : Subgroup G) :
    classMass Γ K = ∑ᶠ c : ClassSet Γ K, ((Nat.card (stabAt Γ K c.out) : ℝ))⁻¹ := by
  refine finsum_congr fun c => ?_
  rw [← stabOrder_mk, DoubleCoset.out_eq']

theorem FiniteClasses.inv_card_le (h : FiniteClasses Γ K) (g : G) :
    ((Nat.card (stabAt Γ K g) : ℝ))⁻¹ ≤ classMass Γ K := by
  haveI := h.1
  haveI := Fintype.ofFinite (ClassSet Γ K)
  rw [classMass_eq_sum, ← stabOrder_mk]
  exact Finset.single_le_sum (f := fun c => ((stabOrder Γ K c : ℝ))⁻¹) (fun _ _ => by positivity)
    (Finset.mem_univ _)

theorem FiniteClasses.classMass_pos (h : FiniteClasses Γ K) : 0 < classMass Γ K :=
  lt_of_lt_of_le (inv_pos.2 (by exact_mod_cast h.stabOrder_pos (DoubleCoset.mk Γ K 1))) (h.inv_card_le 1)

theorem classMass_of_isNeat [Finite (ClassSet Γ K)] (h : IsNeat Γ K) :
    classMass Γ K = Nat.card (ClassSet Γ K) := by
  haveI := Fintype.ofFinite (ClassSet Γ K)
  have : ∀ c, stabOrder Γ K c = 1 := fun c => by
    induction c using Quotient.inductionOn' with
    | h g => change Nat.card (stabAt Γ K g) = 1; rw [h g]; simp
  simp [classMass_eq_sum, this]

theorem FiniteClasses.of_le (h : FiniteClasses Γ K) (hle : K' ≤ K) (hi : K'.relIndex K ≠ 0) :
    FiniteClasses Γ K' := by
  haveI := h.1
  haveI : Finite (K ⧸ K'.subgroupOf K) := Nat.finite_of_card_ne_zero hi
  refine ⟨Finite.of_surjective (fun p : ClassSet Γ K × (K ⧸ K'.subgroupOf K) =>
    (DoubleCoset.mk Γ K' (p.1.out * (p.2.out : K)) : ClassSet Γ K')) fun c => ?_, fun g => ?_⟩
  · induction c using Quotient.inductionOn' with
    | h g =>
      obtain ⟨γ, k, hγ, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
      obtain ⟨k', e'⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K) (⟨k, hk⟩ : K)⁻¹
      refine ⟨(DoubleCoset.mk Γ K g, QuotientGroup.mk (⟨k, hk⟩ : K)⁻¹), ?_⟩
      refine ((DoubleCoset.eq Γ K' _ _).2 ⟨γ, hγ, (k' : K), k'.2, ?_⟩).symm
      simp only [e, e', Subgroup.coe_mul, Subgroup.coe_inv]
      group
  · haveI := h.2 g
    exact Finite.of_injective (fun x : stabAt Γ K' g => (⟨x.1, hle x.2⟩ : stabAt Γ K g))
      fun x y e => Subtype.ext (congrArg (fun z : stabAt Γ K g => z.1) e)

theorem FiniteClasses.of_ge (h : FiniteClasses Γ K') (hle : K' ≤ K) (hi : K'.relIndex K ≠ 0) :
    FiniteClasses Γ K := by
  haveI := h.1
  haveI : Finite (K ⧸ K'.subgroupOf K) := Nat.finite_of_card_ne_zero hi
  refine ⟨Finite.of_surjective (fun c : ClassSet Γ K' => (DoubleCoset.mk Γ K c.out : ClassSet Γ K)) fun c => ?_,
    fun g => ?_⟩
  · induction c using Quotient.inductionOn' with
    | h g =>
      obtain ⟨γ, k, hγ, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K' g
      exact ⟨DoubleCoset.mk Γ K' g, ((DoubleCoset.eq Γ K _ _).2 ⟨γ, hγ, k, hle hk, e⟩).symm⟩
  · haveI := h.2 g
    let f : stabAt Γ K g → K ⧸ K'.subgroupOf K := fun x => QuotientGroup.mk ⟨_, x.2⟩
    let s : (K ⧸ K'.subgroupOf K) → stabAt Γ K g := fun q =>
      Classical.epsilon (h := ⟨⟨1, one_mem_stabAt Γ K g⟩⟩) fun x => f x = q
    have hs : ∀ x, f (s (f x)) = f x := fun x => Classical.epsilon_spec (p := fun y => f y = f x) ⟨x, rfl⟩
    have hm : ∀ x : stabAt Γ K g, (s (f x)).1⁻¹ * x.1 ∈ stabAt Γ K' g := fun x => by
      have h1 : (g⁻¹ * ((s (f x)).1 : G) * g)⁻¹ * (g⁻¹ * (x.1 : G) * g) ∈ K' :=
        (QuotientGroup.eq (s := K'.subgroupOf K)).1 (hs x)
      change g⁻¹ * (((s (f x)).1 : G)⁻¹ * (x.1 : G)) * g ∈ K'
      convert h1 using 1
      group
    refine Finite.of_injective (fun x => (f x, (⟨_, hm x⟩ : stabAt Γ K' g))) fun x y e => ?_
    have e1 : f x = f y := congrArg Prod.fst e
    have e2 : (s (f x)).1⁻¹ * x.1 = (s (f y)).1⁻¹ * y.1 := congrArg (fun p => p.2.1) e
    rw [e1] at e2
    exact Subtype.ext (mul_left_cancel e2)

theorem relIndex_ne_zero_of_isOpen [TopologicalSpace G] [IsTopologicalGroup G] (hK : IsCompact (K : Set G))
    (hK' : IsOpen (K' : Set G)) : K'.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI := Subgroup.quotient_finite_of_isOpen (K'.subgroupOf K) (hK'.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem FiniteClasses.of_isCompact_isOpen [TopologicalSpace G] [IsTopologicalGroup G] (h : FiniteClasses Γ K)
    (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) (hc' : IsCompact (K' : Set G))
    (ho' : IsOpen (K' : Set G)) : FiniteClasses Γ K' := by
  refine (h.of_le (K' := K' ⊓ K) inf_le_right ?_).of_ge inf_le_left ?_
  · rw [Subgroup.inf_relIndex_right]; exact relIndex_ne_zero_of_isOpen hc ho'
  · rw [Subgroup.inf_relIndex_left]; exact relIndex_ne_zero_of_isOpen hc' ho

section Transport

variable {G' : Type} [Group G'] (π : G →* G') (Γ : Subgroup G) (L : Subgroup G')

theorem bijective_classMap (hπ : Function.Surjective π) :
    Function.Bijective fun c : ClassSet Γ (L.comap π) =>
      (DoubleCoset.mk (Γ.map π) L (π c.out) : ClassSet (Γ.map π) L) := by
  constructor
  · intro c d e
    obtain ⟨_, ⟨γ, hγ, rfl⟩, k, hk, e'⟩ := (DoubleCoset.eq _ _ _ _).1 e
    rw [← DoubleCoset.out_eq' _ _ c, ← DoubleCoset.out_eq' _ _ d]
    refine (DoubleCoset.eq _ _ _ _).2 ⟨γ, hγ, (γ * c.out)⁻¹ * d.out, ?_, by group⟩
    rw [Subgroup.mem_comap, map_mul, e', map_inv, map_mul, inv_mul_cancel_left]
    exact hk
  · intro c
    induction c using Quotient.inductionOn' with
    | h g' =>
      obtain ⟨g, rfl⟩ := hπ g'
      obtain ⟨γ, k, hγ, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ (L.comap π) g
      refine ⟨DoubleCoset.mk Γ (L.comap π) g, ((DoubleCoset.eq (Γ.map π) L _ _).2
        ⟨π γ, ⟨γ, hγ, rfl⟩, π k, hk, ?_⟩).symm⟩
      rw [e, map_mul, map_mul]

theorem nonempty_stabAt_equiv (hΓ : Set.InjOn π Γ) (g : G) :
    Nonempty (stabAt Γ (L.comap π) g ≃ stabAt (Γ.map π) L (π g)) := by
  refine ⟨Equiv.ofBijective (fun x => ⟨⟨π x.1, x.1, x.1.2, rfl⟩, ?_⟩) ⟨fun x y e => ?_, ?_⟩⟩
  · have h : π (g⁻¹ * x.1 * g) ∈ L := x.2
    rwa [map_mul, map_mul, map_inv] at h
  · exact Subtype.ext (Subtype.ext (hΓ x.1.2 y.1.2 (congrArg (fun z => z.1.1) e)))
  · rintro ⟨⟨_, γ, hγ, rfl⟩, h⟩
    refine ⟨⟨⟨γ, hγ⟩, ?_⟩, rfl⟩
    change π (g⁻¹ * γ * g) ∈ L
    rw [map_mul, map_mul, map_inv]
    exact h

theorem classMass_comap (hπ : Function.Surjective π) (hΓ : Set.InjOn π Γ) :
    classMass Γ (L.comap π) = classMass (Γ.map π) L := by
  rw [classMass_eq_finsum_out, classMass, ← finsum_comp _ (bijective_classMap π Γ L hπ)]
  refine finsum_congr fun c => ?_
  obtain ⟨e⟩ := nonempty_stabAt_equiv π Γ L hΓ c.out
  rw [stabOrder_mk, Nat.card_congr e]

theorem finiteClasses_comap (hπ : Function.Surjective π) (hΓ : Set.InjOn π Γ) :
    FiniteClasses Γ (L.comap π) ↔ FiniteClasses (Γ.map π) L := by
  refine and_congr (bijective_classMap π Γ L hπ).finite_iff ⟨fun h g' => ?_, fun h g => ?_⟩
  · obtain ⟨g, rfl⟩ := hπ g'
    obtain ⟨e⟩ := nonempty_stabAt_equiv π Γ L hΓ g
    exact e.finite_iff.1 (h g)
  · obtain ⟨e⟩ := nonempty_stabAt_equiv π Γ L hΓ g
    exact e.finite_iff.2 (h _)

end Transport

open MeasureTheory in

theorem FiniteClasses.measure_toReal [MeasurableSpace G] [MeasurableMul G] [Countable Γ] (h : FiniteClasses Γ K)
    (μ : Measure G) [μ.IsMulLeftInvariant] (hK : MeasurableSet (K : Set G)) (hK1 : μ K = 1) {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : (μ 𝓕).toReal = classMass Γ K := by
  haveI := h.1
  haveI := Fintype.ofFinite (ClassSet Γ K)
  have e : ∀ g, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.stab Γ K g = stabAt Γ K g := fun g => by
    ext γ; simp only [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.stab, stabAt, mul_assoc]
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measure_fd_toReal μ hK hK1 (fun c : ClassSet Γ K => c.out) ?_ ?_ ?_ h𝓕,
    classMass_eq_finsum_out, finsum_eq_sum_of_fintype]
  · simp only [e]
  · intro x
    obtain ⟨γ, hγ, k, hk, e⟩ := (DoubleCoset.eq Γ K _ x).1 (DoubleCoset.out_eq' Γ K (DoubleCoset.mk Γ K x))
    exact ⟨_, ⟨γ, hγ⟩, ⟨k, hk⟩, e⟩
  · intro i j γ γ' k k' e
    rw [← DoubleCoset.out_eq' _ _ i, ← DoubleCoset.out_eq' _ _ j]
    refine (DoubleCoset.eq _ _ _ _).2 ⟨(γ'⁻¹ * γ : Γ), (γ'⁻¹ * γ).2, (k * k'⁻¹ : K), (k * k'⁻¹).2, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc, mul_assoc, ← mul_assoc (γ : G), ← mul_assoc, ← mul_assoc,
      mul_assoc _ _ (k : G), e]
    simp [mul_assoc]
  · intro i
    rw [e]
    exact h.2 _

end Abstract

section Unitary

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix

section Swap

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def ratIn : Subgroup (HA R σ J) := HFinIn R σ J

def swapTens (F E R : Type) [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] : R ⊗[F] E ≃+* E ⊗[F] R := (Algebra.TensorProduct.comm F R E).toRingEquiv

theorem swapTens_sig (x : R ⊗[F] E) :
    swapTens F E R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x) = Formalism.UG.sigR σ R (swapTens F E R x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x => rfl

theorem exists_swapPts : ∃ e : HA R σ J ≃* UPts σ J R,
    ∀ g, (e g : GL (Fin M) (E ⊗[F] R)) = bc (swapTens F E R : R ⊗[F] E →+* E ⊗[F] R) (HA.mat R σ J g) :=
  Formalism.UG.Final.UJTransport _ _ (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) (Formalism.UG.sigR σ R) (swapTens F E R)
    (RingHom.ext (swapTens_sig R σ)) (JR R J)

def swapPts : HA R σ J ≃* UPts σ J R := (exists_swapPts R σ J).choose

theorem coe_swapPts (g : HA R σ J) :
    (swapPts R σ J g : GL (Fin M) (E ⊗[F] R)) = bc (swapTens F E R : R ⊗[F] E →+* E ⊗[F] R) (HA.mat R σ J g) :=
  (exists_swapPts R σ J).choose_spec g

theorem map_swapPts_rat :
    (ratIn R σ J).map (swapPts R σ J : HA R σ J →* UPts σ J R) =
      (ratPts σ J R).subgroupOf (UPts σ J R) := by
  have key : ∀ u : GL (Fin M) E, bc (swapTens F E R : R ⊗[F] E →+* E ⊗[F] R) (bc (inclR R) u) =
      bc (inclE (F := F) R) u := fun u => Units.ext rfl
  ext x
  obtain ⟨g, rfl⟩ := (swapPts R σ J).surjective x
  constructor
  · rintro ⟨g', ⟨u, hu, e⟩, e'⟩
    refine ⟨u, hu, ?_⟩
    have e'' : swapPts R σ J g' = swapPts R σ J g := e'
    change _ = ((swapPts R σ J g : UPts σ J R) : GL (Fin M) (E ⊗[F] R))
    rw [← e'', coe_swapPts, ← key, e]
    rfl
  · rintro ⟨u, hu, e⟩
    refine ⟨g, ⟨u, hu, ?_⟩, rfl⟩
    have e' : bc (inclE (F := F) R) u = ((swapPts R σ J g : UPts σ J R) : GL (Fin M) (E ⊗[F] R)) := e
    rw [coe_swapPts, ← key] at e'
    exact Units.ext (Matrix.map_injective (swapTens F E R).injective (congrArg Units.val e'))

end Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def unitaryMass (K : Subgroup (HA (Af F) σ J)) : ℝ :=
  classMass (ratIn (Af F) σ J) K

omit [NumberField E] in

theorem unitaryMass_comap_swapPts (L : Subgroup (UPts σ J (Af F))) :
    unitaryMass σ J (L.comap (swapPts (Af F) σ J : HA (Af F) σ J →* UPts σ J (Af F))) =
      classMass ((ratPts σ J (Af F)).subgroupOf (UPts σ J (Af F))) L := by
  rw [unitaryMass, classMass_comap _ _ _ (swapPts (Af F) σ J).surjective (swapPts (Af F) σ J).injective.injOn,
    map_swapPts_rat]

def intTens (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (Af F ⊗[F] E) :=
  (tensInt (F := F) (Af F) (intOE E) (intAd F)).comap (swapTens F E (Af F) : Af F ⊗[F] E →+* E ⊗[F] Af F)

def stdLevel : Subgroup (HA (Af F) σ J) :=
  ((levelAf σ J).subgroupOf (UPts σ J (Af F))).comap (swapPts (Af F) σ J : HA (Af F) σ J →* UPts σ J (Af F))

theorem mem_stabGL_stdLat {A : Type} [CommRing A] (S : Subring A) {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n A) : g ∈ stabGL (stdLat (n := n) (A := A) S) ↔ ∀ i j, g.1 i j ∈ S ∧ (g⁻¹).1 i j ∈ S := by
  have hm : ∀ x : n → A, x ∈ stdLat (n := n) (A := A) S ↔ ∀ i, x i ∈ S := fun x =>
    ⟨fun h i => by obtain ⟨s, hs⟩ := h i trivial; exact hs ▸ s.2, fun h i _ => ⟨⟨x i, h i⟩, rfl⟩⟩
  have h1 : ∀ g ∈ stabGL (stdLat (n := n) (A := A) S), ∀ i j, g.1 i j ∈ S := fun g hg i j => by
    have := (hm _).1 ((hg (Pi.single j 1)).1 ((hm _).2 fun k => by
      rw [Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _])) i
    simpa using this
  have h2 : ∀ m : Matrix n n A, (∀ i j, m i j ∈ S) → ∀ x ∈ stdLat (n := n) (A := A) S,
      m *ᵥ x ∈ stdLat (n := n) (A := A) S := fun m h x hx =>
    (hm _).2 fun i => sum_mem fun j _ => mul_mem (h i j) ((hm _).1 hx j)
  refine ⟨fun h i j => ⟨h1 g h i j, h1 _ (inv_mem h) i j⟩, fun h x => ⟨h2 _ (fun i j => (h i j).1) x, fun hx => ?_⟩⟩
  have := h2 _ (fun i j => (h i j).2) _ hx
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem mem_stdLevel (g : HA (Af F) σ J) : g ∈ stdLevel σ J ↔
    ∀ i j, (HA.mat (Af F) σ J g).1 i j ∈ intTens F E ∧ ((HA.mat (Af F) σ J g)⁻¹).1 i j ∈ intTens F E := by
  have : g ∈ stdLevel σ J ↔ (swapPts (Af F) σ J g : GL (Fin M) (E ⊗[F] Af F)) ∈
      stabGL (stdLat (n := Fin M) (A := E ⊗[F] Af F) (tensInt (F := F) (Af F) (intOE E) (intAd F))) :=
    ⟨fun h => h.2, fun h => ⟨(swapPts (Af F) σ J g).2, h⟩⟩
  rw [this, mem_stabGL_stdLat, coe_swapPts]
  rfl

theorem intTens_open_compact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsOpen (intTens F E : Set (Af F ⊗[F] E)) ∧
      ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧ ∀ w ∈ intTens F E, w ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  let L : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have h1 : (fun _ => 1 : Fin 1 → E) ∈ L := Submodule.subset_span rfl
  have hsp : Submodule.span E (L : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have : v = v 0 • (fun _ => 1 : Fin 1 → E) := by funext i; simp [Subsingleton.elim i 0]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  constructor
  · have ho := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 1 L hsp).1 1 one_pos
    have hc : Continuous fun w : Af F ⊗[F] E => (fun _ => w : Fin 1 → Af F ⊗[F] E) :=
      continuous_pi fun _ => continuous_id
    refine (intTens F E).toAddSubgroup.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset
      ((ho.preimage hc).mem_nhds ⟨0, zero_mem _, by rw [smul_zero]; rfl⟩) ?_)
    rintro w ⟨y, hy, e⟩
    have hw : w = y 0 := by simpa using congrFun e 0
    rw [hw]
    clear e hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      change ((c • (fun _ => 1 : Fin 1 → E)) 0) ⊗ₜ[F] a ∈ tensInt (F := F) (Af F) (intOE E) (intAd F)
      have : ((c • (fun _ => 1 : Fin 1 → E)) 0) ⊗ₜ[F] a =
          (algebraMap (𝓞 E) E c ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
      rw [this]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat F E L (Submodule.fg_span_singleton _)
    refine ⟨(fun y => y 0) '' C, hC.image (continuous_apply 0), fun w hw => ?_⟩
    have gen : ∀ t : Af F ⊗[F] E, (∀ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∀ x ∈ L,
        t • (fun i => a ⊗ₜ[F] x i) ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin 1 → E))) →
        ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin 1 → E)), t • y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin 1 → E)) := by
      intro t ht y hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz => obtain ⟨a, ha, x, hx, rfl⟩ := hz; exact ht a ha x hx
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [smul_neg]; exact neg_mem hx
    have key : ∀ t ∈ tensInt (F := F) (Af F) (intOE E) (intAd F),
        ∀ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin 1 → E)),
          (swapTens F E (Af F)).symm t • y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin 1 → E)) := by
      intro t ht
      induction ht using Subring.closure_induction with
      | mem z hz =>
        rcases hz with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩
        · refine gen _ fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, c • x, L.smul_mem c hx, ?_⟩
          funext i
          change ((1 : Af F) ⊗ₜ[F] algebraMap (𝓞 E) E c) * (a ⊗ₜ[F] x i) = _
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Pi.smul_apply, Algebra.smul_def]
        · refine gen _ fun a ha x hx => AddSubgroup.subset_closure
            ⟨b * a, fun v => by rw [map_mul]; exact mul_mem (b.2 v) (ha v), x, hx, ?_⟩
          funext i
          change ((b : Af F) ⊗ₜ[F] (1 : E)) * (a ⊗ₜ[F] x i) = _
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero => intro y _; rw [map_zero, zero_smul]; exact zero_mem _
      | one => intro y hy; rwa [map_one, one_smul]
      | add a b _ _ ha hb => intro y hy; rw [map_add, add_smul]; exact add_mem (ha y hy) (hb y hy)
      | neg a _ ha => intro y hy; rw [map_neg, neg_smul]; exact neg_mem (ha y hy)
      | mul a b _ _ ha hb => intro y hy; rw [map_mul, mul_smul]; exact ha _ (hb y hy)
    have h0 := key _ hw _ (AddSubgroup.subset_closure
      ⟨1, fun v => by rw [map_one]; exact one_mem _, _, h1, rfl⟩)
    refine ⟨_, hLC _ h0, ?_⟩
    change (swapTens F E (Af F)).symm (swapTens F E (Af F) w) * ((1 : Af F) ⊗ₜ[F] (1 : E)) = w
    rw [RingEquiv.symm_apply_apply, ← Algebra.TensorProduct.one_def, mul_one]

theorem topGroup_fin : IsTopologicalGroup (HA (Af F) σ J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (Af F) σ J))

theorem isOpen_stdLevel : IsOpen (stdLevel σ J : Set (HA (Af F) σ J)) := by
  have hm : Continuous (HA.mat (Af F) σ J) := continuous_subtype_val
  have : (stdLevel σ J : Set (HA (Af F) σ J)) = ⋂ i, ⋂ j,
      ((fun g => (HA.mat (Af F) σ J g).1 i j) ⁻¹' (intTens F E) ∩
        (fun g => ((HA.mat (Af F) σ J g)⁻¹).1 i j) ⁻¹' (intTens F E)) := by
    ext g
    simp only [SetLike.mem_coe, mem_stdLevel, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact (intTens_open_compact F E).1.preimage ((Units.continuous_val.comp hm).matrix_elem i j)
  · exact (intTens_open_compact F E).1.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)

theorem isCompact_stdLevel (hJ : J.det ≠ 0) : IsCompact (stdLevel σ J : Set (HA (Af F) σ J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := topGroup_fin σ J
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨C, hC, hCe⟩ := (intTens_open_compact F E).2
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (Af F) σ J hJ C hC
  exact hK.of_isClosed_subset ((stdLevel σ J).isClosed_of_isOpen (isOpen_stdLevel σ J))
    fun g hg => hKe g fun i j => hCe _ ((mem_stdLevel σ J g).1 hg i j).1

variable {σ J}

theorem finiteClasses_unitary (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hd : IsTotDef σ J)
    {K : Subgroup (HA (Af F) σ J)} (hc : IsCompact (K : Set (HA (Af F) σ J)))
    (ho : IsOpen (K : Set (HA (Af F) σ J))) :
    FiniteClasses (ratIn (Af F) σ J) K := by
  haveI := topGroup_fin σ J
  have hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ :=
    fun τ => RingHom.ext (hσ.2.2.2 τ)
  have hH : IsHerm (σ : E →+* E) J := Matrix.ext fun i j => hJ.1 i j
  refine FiniteClasses.of_isCompact_isOpen (K := stdLevel σ J) ?_ (isCompact_stdLevel σ J hJ.2)
    (isOpen_stdLevel σ J) hc ho
  rw [stdLevel, finiteClasses_comap _ _ _ (swapPts (Af F) σ J).surjective (swapPts (Af F) σ J).injective.injOn,
    map_swapPts_rat]
  exact ⟨Formalism.UG.Final.ClassSetFinite F E _ σ J hτ hH hJ.2.isUnit hd,
    Formalism.UG.Final.AdelicStabFinite F E _ σ J hτ hH hJ.2.isUnit hd⟩

theorem finiteClasses_lattice (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hd : IsTotDef σ J)
    (Λ : Submodule (𝓞 E) (Fin M → E)) (hΛ : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin M → E)) = ⊤) :
    FiniteClasses (ratIn (Af F) σ J) (((levelAfL σ J Λ).subgroupOf (UPts σ J (Af F))).comap
      (swapPts (Af F) σ J : HA (Af F) σ J →* UPts σ J (Af F))) := by
  have hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ :=
    fun τ => RingHom.ext (hσ.2.2.2 τ)
  have hH : IsHerm (σ : E →+* E) J := Matrix.ext fun i j => hJ.1 i j
  rw [finiteClasses_comap _ _ _ (swapPts (Af F) σ J).surjective (swapPts (Af F) σ J).injective.injOn,
    map_swapPts_rat]
  exact ⟨Formalism.UG.Final.ClassSetFiniteL F E _ σ J hτ hH hJ.2.isUnit hd Λ hΛ hsp,
    Formalism.UG.Final.AdelicStabFiniteL F E _ σ J hτ hH hJ.2.isUnit hd Λ hΛ hsp⟩

theorem unitaryMass_pos (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hd : IsTotDef σ J)
    {K : Subgroup (HA (Af F) σ J)} (hc : IsCompact (K : Set (HA (Af F) σ J)))
    (ho : IsOpen (K : Set (HA (Af F) σ J))) : 0 < unitaryMass σ J K :=
  (finiteClasses_unitary hσ hJ hd hc ho).classMass_pos

end Unitary

section Adelic

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def IsFinProj (π : HA (AF F) σ J →* HA (Af F) σ J) : Prop :=
  ∀ g, HA.mat (Af F) σ J (π g) =
    bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (HA.mat (AF F) σ J g)

theorem parts_spec :
    (∀ g : GL (Fin M) (AF F ⊗[F] E), g ∈ HR (AF F) σ J ↔
      bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J ∧
      bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g ∈ HR (Af F) σ J) ∧
    ∀ (a : GL (Fin M) (Ainf F ⊗[F] E)) (b : GL (Fin M) (Af F ⊗[F] E)), ∃ g : GL (Fin M) (AF F ⊗[F] E),
      bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g = a ∧
      bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hi : ∀ x y : AF F ⊗[F] E, (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom y →
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom x =
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom y → x = y := fun x y h1 h2 =>
    e.injective (Prod.ext (((he x).1.trans h1).trans (he y).1.symm) (((he x).2.trans h2).trans (he y).2.symm))
  refine ⟨fun g => ?_, GlobalTheory.UnitarySplit.gl_glue _ _ hi fun a b => ?_⟩
  · have := GlobalTheory.UnitarySplit.mem_iff _ _ hi (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) (GlobalTheory.UnitarySplit.map_sig _ _) (GlobalTheory.UnitarySplit.map_sig _ _) (JR _ J) g
    rwa [GlobalTheory.UnitarySplit.map_JR, GlobalTheory.UnitarySplit.map_JR] at this
  · refine ⟨e.symm (a, b), (he _).1.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem existsUnique_isFinProj : ∃! π, IsFinProj σ J π := by
  refine ⟨((bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom).comp
    (HR (AF F) σ J).subtype).codRestrict (HR (Af F) σ J) fun g => (((parts_spec σ J).1 _).1 g.2).2,
    fun _ => rfl, fun π h => MonoidHom.ext fun g => Subtype.ext (h g)⟩

variable {σ J} {π : HA (AF F) σ J →* HA (Af F) σ J}

theorem IsFinProj.surjective (h : IsFinProj σ J π) : Function.Surjective π := fun b => by
  obtain ⟨g, h1, h2⟩ := (parts_spec σ J).2 1 (HA.mat (Af F) σ J b)
  refine ⟨⟨g, ((parts_spec σ J).1 g).2 ⟨h1 ▸ one_mem _, h2 ▸ b.2⟩⟩, Subtype.ext ((h _).trans h2)⟩

omit [NumberField E] in

theorem IsFinProj.injOn (h : IsFinProj σ J π) : Set.InjOn π (ratIn (AF F) σ J) := by
  haveI : Nontrivial (Af F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
    exact (Formalism.UG.evalV F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (Af F ⊗[F] E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := Af F) (B := E)
      (algebraMap F E).injective).nontrivial
  rintro x ⟨u, -, hu⟩ y ⟨v, -, hv⟩ e
  have e1 : bc (inclR (F := F) (Af F)) u = bc (inclR (F := F) (Af F)) v := by
    have hx := h x
    have hy := h y
    rw [e, hy] at hx
    change bc _ ((HR (AF F) σ J).subtype y) = bc _ ((HR (AF F) σ J).subtype x) at hx
    rw [← hu, ← hv] at hx
    exact hx.symm
  have e2 : u = v := Units.ext (Matrix.map_injective (inclR (F := F) (E := E) (Af F)).injective (congrArg Units.val e1 :
    (u : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (Af F)) = (v : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (Af F))))
  exact Subtype.ext (hu.symm.trans (e2 ▸ hv))

theorem IsFinProj.map_ratIn (h : IsFinProj σ J π) : (ratIn (AF F) σ J).map π = ratIn (Af F) σ J := by
  ext b
  constructor
  · rintro ⟨x, ⟨u, hu, e⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    have hx := h x
    change _ = bc _ ((HR (AF F) σ J).subtype x) at hx
    rw [← e] at hx
    exact hx.symm
  · rintro ⟨u, hu, e⟩
    have hm : bc (inclR (F := F) (AF F)) u ∈ HR (AF F) σ J :=
      Formalism.UG.Final.BCMem _ _ (Fin M) (σ : E →+* E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (inclR (AF F))
        (RingHom.ext fun _ => rfl) J u hu
    exact ⟨⟨_, hm⟩, ⟨u, hu, rfl⟩, Subtype.ext ((h _).trans e)⟩

theorem IsFinProj.continuous (h : IsFinProj σ J π) : Continuous π := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have hq : Continuous (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom :=
    (continuous_snd.comp hc).congr fun z => (he z).2
  have hm : Continuous (HA.mat (AF F) σ J) := continuous_subtype_val
  refine continuous_induced_rng.2 ?_
  change Continuous fun g => HA.mat (Af F) σ J (π g)
  simp only [h _]
  exact Units.continuous_iff.2 ⟨(Units.continuous_val.comp hm).matrix_map hq,
    (Units.continuous_coe_inv.comp hm).matrix_map hq⟩

theorem IsFinProj.unitaryMass_eq (h : IsFinProj σ J π) (K : Subgroup (HA (Af F) σ J)) :
    unitaryMass σ J K = classMass (ratIn (AF F) σ J) (K.comap π) := by
  rw [classMass_comap π _ K h.surjective h.injOn, h.map_ratIn, unitaryMass]

theorem IsFinProj.measure_toReal (h : IsFinProj σ J π) (hσ : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hd : IsTotDef σ J) {K : Subgroup (HA (Af F) σ J)} (hc : IsCompact (K : Set (HA (Af F) σ J)))
    (ho : IsOpen (K : Set (HA (Af F) σ J))) (μ : Measure (HA (AF F) σ J)) [μ.IsMulLeftInvariant]
    (hK1 : μ (K.comap π) = 1) {𝓕 : Set (HA (AF F) σ J)} (h𝓕 : IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) :
    (μ 𝓕).toReal = unitaryMass σ J K := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA σ J
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  haveI : Countable (ratIn (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma σ J
  have hf : FiniteClasses (ratIn (AF F) σ J) (K.comap π) := by
    rw [finiteClasses_comap π _ K h.surjective h.injOn, h.map_ratIn]
    exact finiteClasses_unitary hσ hJ hd hc ho
  rw [h.unitaryMass_eq]
  exact hf.measure_toReal μ (ho.preimage h.continuous).measurableSet hK1 h𝓕

end Adelic

theorem classMass_top_top (G : Type) [Group G] :
    classMass (⊤ : Subgroup G) ⊤ = ((Nat.card G : ℝ))⁻¹ := by
  rw [classMass_eq_sum_of_bijective (ι := Unit) (fun _ => 1) ⟨fun _ _ _ => rfl, fun c => ?_⟩]
  · have : stabAt (⊤ : Subgroup G) ⊤ 1 = Set.univ := Set.eq_univ_of_forall fun _ => Subgroup.mem_top _
    simp [this]
  · induction c using Quotient.inductionOn' with
    | h g => exact ⟨(), (DoubleCoset.eq ⊤ ⊤ _ _).2 ⟨g, trivial, 1, trivial, by simp⟩⟩

theorem classMass_bot {G : Type} [Group G] (K : Subgroup G) [K.FiniteIndex] :
    classMass (⊥ : Subgroup G) K = K.index := by
  have e : ClassSet (⊥ : Subgroup G) K = (G ⧸ K) := DoubleCoset.left_bot_eq_left_quot K
  haveI : Finite (ClassSet (⊥ : Subgroup G) K) := by rw [e]; infer_instance
  rw [classMass_of_isNeat fun g => Set.eq_singleton_iff_unique_mem.2
    ⟨one_mem_stabAt _ _ _, fun _ _ => Subsingleton.elim _ _⟩, e]
  rfl

theorem finiteClasses_of_finite {G : Type} [Group G] [Finite G] (Γ K : Subgroup G) : FiniteClasses Γ K :=
  ⟨Quotient.finite _, fun _ => inferInstance⟩

example : classMass (⊤ : Subgroup (Equiv.Perm (Fin 3))) ⊤ = 1 / 6 := by
  rw [classMass_top_top, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]

example : classMass (⊥ : Subgroup (Equiv.Perm (Fin 3))) ⊥ = 6 := by
  rw [classMass_bot, Subgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]

example : ¬ FiniteClasses (⊤ : Subgroup (Multiplicative ℤ)) ⊤ := fun h => by
  haveI := h.2 1
  exact not_finite_iff_infinite.2 inferInstance (Finite.of_injective
    (fun n : Multiplicative ℤ => (⟨⟨n, trivial⟩, Subgroup.mem_top _⟩ : stabAt (⊤ : Subgroup (Multiplicative ℤ)) ⊤ 1))
    fun x y e => congrArg (fun z => z.1.1) e)

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

example {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 0) (Fin 0) E) : unitaryMass σ J ⊤ = 1 := by
  haveI : Subsingleton (HA (Af F) σ J) := ⟨fun x y => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  rw [unitaryMass, Subsingleton.elim (ratIn (Af F) σ J) ⊥, classMass_bot]
  simp

end GlobalTheory.Mass
