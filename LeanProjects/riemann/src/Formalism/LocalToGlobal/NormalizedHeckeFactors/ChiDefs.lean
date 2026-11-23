import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.L2.NC

section hecke

variable {E : Type} [Field E] [NumberField E]

@[ext]
structure HC (E : Type) [Field E] [NumberField E] where
  χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ
  cont : Continuous χ
  triv : ∀ a : Eˣ, χ (Units.map (algebraMap E (AdeleRing (𝓞 E) E)).toMonoidHom a) = 1

instance : Mul (HC E) where
  mul χ ψ := ⟨χ.χ * ψ.χ, χ.cont.mul ψ.cont, fun a => by rw [MonoidHom.mul_apply, χ.triv a, ψ.triv a, one_mul]⟩

instance : Inv (HC E) where
  inv χ := ⟨χ.χ⁻¹, χ.cont.inv, fun a => by rw [MonoidHom.inv_apply, χ.triv a, inv_one]⟩

instance : One (HC E) where
  one := ⟨1, continuous_const, fun _ => rfl⟩

@[simp] theorem HC.mul_χ (χ ψ : HC E) : (χ * ψ).χ = χ.χ * ψ.χ := rfl
@[simp] theorem HC.inv_χ (χ : HC E) : (χ⁻¹).χ = χ.χ⁻¹ := rfl
@[simp] theorem HC.one_χ : (1 : HC E).χ = 1 := rfl

open scoped Classical in

def locM (P : HeightOneSpectrum (𝓞 E)) : P.adicCompletion E →* AdeleRing (𝓞 E) E where
  toFun x := ((1 : InfiniteAdeleRing E),
    (RestrictedProduct.mulSingle (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletionIntegers E) P x :
      FiniteAdeleRing (𝓞 E) E))
  map_one' := by
    show ((1 : InfiniteAdeleRing E), _) = ((1 : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
    rw [RestrictedProduct.mulSingle_one]
    rfl
  map_mul' x y := by
    show ((1 : InfiniteAdeleRing E), _) = ((1 : InfiniteAdeleRing E) * 1, _ * _)
    rw [RestrictedProduct.mulSingle_mul, mul_one]
    rfl

def HC.At (χ : HC E) (P : HeightOneSpectrum (𝓞 E)) (α : ℂ) : Prop :=
  (∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.χ (Units.map (locM P) u) = 1) ∧
    ∀ ϖ : (P.adicCompletion E)ˣ, Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ) →
      ((χ.χ (Units.map (locM P) ϖ) : ℂˣ) : ℂ) = α

theorem HC.At.mul {χ ψ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a b : ℂ} (h : χ.At P a) (h' : ψ.At P b) :
    (χ * ψ).At P (a * b) := by
  refine ⟨fun u hu => ?_, fun ϖ hϖ => ?_⟩
  · simp [h.1 u hu, h'.1 u hu]
  · simp [← h.2 ϖ hϖ, ← h'.2 ϖ hϖ]

theorem HC.At.inv {χ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a : ℂ} (h : χ.At P a) : (χ⁻¹).At P a⁻¹ := by
  refine ⟨fun u hu => ?_, fun ϖ hϖ => ?_⟩
  · simp [h.1 u hu]
  · simp [← h.2 ϖ hϖ]

theorem exists_unif (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ϖ : (P.adicCompletion E)ˣ, Valued.v (ϖ : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer E
  have hv : Valued.v (π : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    rw [P.valuedAdicCompletion_eq_valuation' π, hπ]
  have h0 : (π : P.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  exact ⟨Units.mk0 _ h0, hv⟩

theorem HC.At.unique {χ : HC E} {P : HeightOneSpectrum (𝓞 E)} {a b : ℂ} (ha : χ.At P a) (hb : χ.At P b) : a = b := by
  obtain ⟨ϖ, hϖ⟩ := exists_unif P
  rw [← ha.2 ϖ hϖ, ← hb.2 ϖ hϖ]

open scoped Classical in

def locInf (v : InfinitePlace E) : v.Completion →* AdeleRing (𝓞 E) E where
  toFun x := ((Pi.mulSingle v x : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
  map_one' := by
    show ((Pi.mulSingle v (1 : v.Completion) : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E)) =
      ((1 : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E))
    rw [Pi.mulSingle_one]
    rfl
  map_mul' x y := by
    show ((Pi.mulSingle v (x * y) : InfiniteAdeleRing E), (1 : FiniteAdeleRing (𝓞 E) E)) =
      ((Pi.mulSingle v x : InfiniteAdeleRing E) * Pi.mulSingle v y, (1 : FiniteAdeleRing (𝓞 E) E) * 1)
    rw [Pi.mulSingle_mul, mul_one]

def HC.Unr (χ : HC E) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ u : (P.adicCompletion E)ˣ, Valued.v (u : P.adicCompletion E) = 1 → χ.χ (Units.map (locM P) u) = 1

def HC.IsUnitArg (χ : HC E) (τ : E →+* ℂ) : Prop :=
  ∀ f : (InfinitePlace.mk τ).Completion →+* ℂ, Continuous f → (∀ x : E, f (x : (InfinitePlace.mk τ).Completion) = τ x) →
    ∀ z : ((InfinitePlace.mk τ).Completion)ˣ,
      ((χ.χ (Units.map (locInf (InfinitePlace.mk τ)) z) : ℂˣ) : ℂ) = f z / (‖f z‖ : ℂ)

def HC.FinOrd (χ : HC E) : Prop := ∃ n : ℕ, 0 < n ∧ ∀ x, χ.χ x ^ n = 1

end hecke

section read

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def Read {A K L : Type} [CommRing A] [CommRing K] [CommRing L] (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω)
    (φ : G E Ω →* Aˣ) (rd : A →+* K) (eL : L →+* K) (embC : L →+* ℂ) (χ : HC E) (w : ℤ) : Prop :=
  ∃ B : Finset (HeightOneSpectrum (𝓞 E)), ∀ P ∉ B, ∃ α : ℂ, χ.At P α ∧ ∃ x : L,
    embC x = α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ w ∧
    ∀ σ : G E Ω, IsFrob (F := E) (pl P) (normV P) σ → rd (φ σ : A) = eL x

abbrev ReadC {A : Type} [CommRing A] (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (φ : G E Ω →* Aˣ)
    (rd : A →+* ℂ) (χ : HC E) (w : ℤ) : Prop :=
  Read pl φ rd (RingHom.id ℂ) (RingHom.id ℂ) χ w

variable (E Ω) in

def cycU (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] : G E Ω →* Oˣ :=
  (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ E Ω l)

def CycFrob (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ P.asIdeal → ∀ σ : G E Ω, IsFrob (F := E) (pl P) (normV P) σ →
    ((cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (normV P : ℤ_[l])

theorem normV_ne_zero (P : HeightOneSpectrum (𝓞 E)) : normV P ≠ 0 := by
  have h : normV P = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [h]
  exact fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem finite_placesOver (l : ℕ) [Fact l.Prime] :
    {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem Read.frob_eq {A K L : Type} [CommRing A] [CommRing K] [CommRing L]
    {pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω} {φ φ' : G E Ω →* Aˣ} {rd : A →+* K} {eL : L →+* K}
    {embC : L →+* ℂ} {χ : HC E} {w : ℤ} (h : Read pl φ rd eL embC χ w) (h' : Read pl φ' rd eL embC χ w)
    (hC : Function.Injective embC) :
    ∃ B : Finset (HeightOneSpectrum (𝓞 E)), ∀ P ∉ B, ∀ σ : G E Ω, IsFrob (F := E) (pl P) (normV P) σ →
      rd (φ σ : A) = rd (φ' σ : A) := by
  classical
  obtain ⟨B, hB⟩ := h
  obtain ⟨B', hB'⟩ := h'
  refine ⟨B ∪ B', fun P hP σ hσ => ?_⟩
  obtain ⟨α, hα, x, hx, hs⟩ := hB P (fun h => hP (Finset.mem_union_left _ h))
  obtain ⟨α', hα', x', hx', hs'⟩ := hB' P (fun h => hP (Finset.mem_union_right _ h))
  have e : α = α' := hα.unique hα'
  have ex : x = x' := hC (by rw [hx, hx', e])
  rw [hs σ hσ, hs' σ hσ, ex]

theorem val_root_one (A : ValuationSubring Ω) {x : Ω} {N : ℕ} (hN : N ≠ 0) (hx : x ^ N = 1) : A.valuation x = 1 := by
  have h := congrArg A.valuation hx
  rw [map_pow, map_one] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le h1 hN).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hN).ne'

theorem cycFrob_holds [IsAlgClosed Ω] [CharZero Ω] (pl : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω)
    (hpl : ∀ P, IsPlaceOver (pl P) P) (l : ℕ) [Fact l.Prime] : CycFrob pl l := by
  intro P hl σ hσ
  have hlp : 0 < l := (Fact.out : l.Prime).pos
  have hvl : (pl P).valuation (l : Ω) = 1 := by
    have h1 : (pl P).valuation (l : Ω) ≤ 1 := by
      have := (pl P).valuation_le_one (l : pl P)
      simpa using this
    have h2 : ¬ (pl P).valuation (l : Ω) < 1 := by
      intro h
      apply hl
      refine (hpl P (l : 𝓞 E)).1 ?_
      simpa using h
    exact le_antisymm h1 (not_lt.1 h2)
  rw [← PadicInt.ext_of_toZModPow]
  intro n
  rw [map_natCast]
  have hN : l ^ n ≠ 0 := pow_ne_zero _ hlp.ne'
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hspec : σ ζ = ζ ^ (((cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow n).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G E Ω) Ω σ) ζ hζ.pow_eq_one
  set a := (((cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow n).val with ha
  set q := normV P
  have hz1 : (pl P).valuation ζ = 1 := val_root_one (pl P) hN hζ.pow_eq_one
  have hfrob := hσ.2 ζ hz1.le
  rw [hspec] at hfrob
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN
  have hζq : ζ ^ q ≠ 0 := pow_ne_zero _ hζ0
  have key : ζ ^ a = ζ ^ q := by
    by_contra hne
    set η := ζ ^ a * (ζ ^ q)⁻¹ with hη
    have hη1 : η ≠ 1 := fun h => hne ((mul_inv_eq_one₀ hζq).1 h)
    have hηN : η ^ (l ^ n) = 1 := by
      rw [hη, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a, mul_comm q, pow_mul, pow_mul, hζ.pow_eq_one,
        one_pow, one_pow, inv_one, mul_one]
    have hvη1 : (pl P).valuation η = 1 := val_root_one (pl P) hN hηN
    have hvη : (pl P).valuation (η - 1) < 1 := by
      have e : η - 1 = (ζ ^ a - ζ ^ q) * (ζ ^ q)⁻¹ := by
        rw [hη, sub_mul, mul_inv_cancel₀ hζq]
      have hq1 : (pl P).valuation (ζ ^ q) = 1 := by rw [map_pow, hz1, one_pow]
      rw [e, map_mul, map_inv₀, hq1, inv_one, mul_one]
      exact hfrob
    have hsum : ∑ i ∈ Finset.range (l ^ n), η ^ i = 0 := by
      rw [geom_sum_eq hη1, hηN, sub_self, zero_div]
    have hNsum : ((l ^ n : ℕ) : Ω) = ∑ i ∈ Finset.range (l ^ n), (1 - η ^ i) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero]
      simp
    have hlt : (pl P).valuation ((l ^ n : ℕ) : Ω) < 1 := by
      rw [hNsum]
      refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
      have e : 1 - η ^ i = -((∑ j ∈ Finset.range i, η ^ j) * (η - 1)) := by
        rw [geom_sum_mul]
        ring
      have hs : (pl P).valuation (∑ j ∈ Finset.range i, η ^ j) ≤ 1 :=
        Valuation.map_sum_le _ fun j _ => by rw [map_pow, hvη1, one_pow]
      rw [e, Valuation.map_neg, map_mul]
      calc (pl P).valuation (∑ j ∈ Finset.range i, η ^ j) * (pl P).valuation (η - 1)
          ≤ 1 * (pl P).valuation (η - 1) := mul_le_mul' hs le_rfl
        _ < 1 := by rw [one_mul]; exact hvη
    rw [Nat.cast_pow, map_pow, hvl, one_pow] at hlt
    exact lt_irrefl _ hlt
  have hdvd : ((l ^ n : ℕ) : ℤ) ∣ (q : ℤ) - (a : ℤ) := by
    have h1 : ζ ^ ((q : ℤ) - (a : ℤ)) = 1 := by
      rw [zpow_sub₀ hζ0, zpow_natCast, zpow_natCast, ← key, div_self (pow_ne_zero _ hζ0)]
    exact (hζ.zpow_eq_one_iff_dvd _).1 h1
  rw [← ZMod.natCast_zmod_val (((cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]).toZModPow n), ← ha]
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (a : ℤ) (q : ℤ) (l ^ n)).2 hdvd
  exact_mod_cast h2

end read

section rcg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

def UnrOut {A : Type} [Group A] (φ : G E Ω →* A) (Q : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := E) A, φ σ = 1

def IsRcgChar (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) {A : Type} [CommGroup A]
    (φ : G E Ω →* A) : Prop :=
  Finite A ∧ (∀ x : A, ∃ n : ℕ, x ^ (l ^ n) = 1) ∧ IsOpen (φ.ker : Set (G E Ω)) ∧ AntiHom c φ ∧ UnrOut φ Q

def rcgKer (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : Subgroup (G E Ω) where
  carrier := {g | ∀ (A : Type) [CommGroup A] (φ : G E Ω →* A), IsRcgChar c l Q φ → φ g = 1}
  one_mem' := fun A _ φ _ => map_one φ
  mul_mem' := fun {a b} ha hb A _ φ h => by rw [map_mul, ha A φ h, hb A φ h, one_mul]
  inv_mem' := fun {a} ha A _ φ h => by rw [map_inv, ha A φ h, inv_one]

theorem mem_rcgKer {c : Ω ≃+* Ω} {l : ℕ} {Q : Set (HeightOneSpectrum (𝓞 E))} {g : G E Ω} :
    g ∈ rcgKer c l Q ↔ ∀ (A : Type) [CommGroup A] (φ : G E Ω →* A), IsRcgChar c l Q φ → φ g = 1 := Iff.rfl

instance rcgKer_normal (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : (rcgKer c l Q).Normal where
  conj_mem g hg h A _ φ hφ := by
    rw [map_mul, map_mul, hg A φ hφ, mul_one, map_inv, mul_inv_cancel]

abbrev RCGGal (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  G E Ω ⧸ rcgKer c l Q

def artGal (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : G E Ω →* RCGGal c l Q :=
  QuotientGroup.mk' _

def RcgOpen (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ [IsAlgClosure E Ω], 0 < l → Q.Finite → (∀ v ∈ Q, ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) →
    IsOpen ((rcgKer c l Q : Subgroup (G E Ω)) : Set (G E Ω))

instance rcgGal_comm (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : CommGroup (RCGGal c l Q) :=
  { (inferInstance : Group (RCGGal c l Q)) with
    mul_comm := fun x y => by
      induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      refine mem_rcgKer.2 fun A _ φ _ => ?_
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (φ b) (φ a), inv_mul_cancel] }

theorem artGal_surj (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) :
    Function.Surjective (artGal c l Q) := QuotientGroup.mk'_surjective _

theorem artGal_ker (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) :
    (artGal c l Q).ker = rcgKer c l Q := QuotientGroup.ker_mk' _

theorem artGal_anti (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : AntiHom c (artGal c l Q) := by
  intro g g' h
  show (QuotientGroup.mk g' : RCGGal c l Q) = (QuotientGroup.mk g)⁻¹
  rw [← QuotientGroup.mk_inv, QuotientGroup.eq]
  refine mem_rcgKer.2 fun A _ φ hφ => ?_
  rw [map_mul, map_inv, map_inv, hφ.2.2.2.1 g g' h, inv_inv, mul_inv_cancel]

theorem artGal_unr (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) : UnrOut (artGal c l Q) Q := by
  intro v hv A hA σ hσ
  show (QuotientGroup.mk σ : RCGGal c l Q) = 1
  rw [QuotientGroup.eq_one_iff]
  exact mem_rcgKer.2 fun _ _ φ hφ => hφ.2.2.2.2 v hv A hA σ hσ

theorem artGal_univ (c : Ω ≃+* Ω) (l : ℕ) (Q : Set (HeightOneSpectrum (𝓞 E))) {A : Type} [CommGroup A]
    (φ : G E Ω →* A) (hφ : IsRcgChar c l Q φ) : ∃ f : RCGGal c l Q →* A, f.comp (artGal c l Q) = φ :=
  ⟨QuotientGroup.lift _ φ fun g hg => (mem_rcgKer.1 hg) A φ hφ, by ext g; rfl⟩

theorem rcgKer_mono (c : Ω ≃+* Ω) (l : ℕ) {Q Q' : Set (HeightOneSpectrum (𝓞 E))} (h : Q' ⊆ Q) :
    rcgKer c l Q ≤ rcgKer c l Q' := fun _ hg =>
  mem_rcgKer.2 fun A _ φ hφ => (mem_rcgKer.1 hg) A φ
    ⟨hφ.1, hφ.2.1, hφ.2.2.1, hφ.2.2.2.1, fun v hv => hφ.2.2.2.2 v (fun h' => hv (h h'))⟩

def resGal (c : Ω ≃+* Ω) (l : ℕ) {Q Q' : Set (HeightOneSpectrum (𝓞 E))} (h : Q' ⊆ Q) :
    RCGGal c l Q →* RCGGal c l Q' :=
  QuotientGroup.map _ _ (MonoidHom.id _) (fun _ hg => rcgKer_mono c l h hg)

theorem resGal_art (c : Ω ≃+* Ω) (l : ℕ) {Q Q' : Set (HeightOneSpectrum (𝓞 E))} (h : Q' ⊆ Q) :
    (resGal c l h).comp (artGal c l Q) = artGal c l Q' := by
  ext g
  rfl

theorem rcgGal_finite [IsTopologicalGroup (G E Ω)] [CompactSpace (G E Ω)] (c : Ω ≃+* Ω) (l : ℕ)
    (Q : Set (HeightOneSpectrum (𝓞 E))) (hO : IsOpen ((rcgKer c l Q : Subgroup (G E Ω)) : Set (G E Ω))) : Finite (RCGGal c l Q) :=
  Subgroup.quotient_finite_of_isOpen _ hO

theorem rcgGal_lpow [IsTopologicalGroup (G E Ω)] [CompactSpace (G E Ω)] (c : Ω ≃+* Ω) (l : ℕ)
    (Q : Set (HeightOneSpectrum (𝓞 E))) (hO : IsOpen ((rcgKer c l Q : Subgroup (G E Ω)) : Set (G E Ω))) (x : RCGGal c l Q) : ∃ n : ℕ, x ^ (l ^ n) = 1 := by
  induction x using QuotientGroup.induction_on with | H g => ?_
  let ι := Σ (A : Type) (_ : CommGroup A), {φ : G E Ω →* A // IsRcgChar c l Q φ}
  let U : ι → Set (G E Ω) := fun p => by
    let _ := p.2.1
    exact {h | p.2.2.1 h ≠ 1}
  have hUo : ∀ p, IsOpen (U p) := by
    intro p
    let _ := p.2.1
    have hk : IsClosed ((p.2.2.1.ker : Subgroup (G E Ω)) : Set (G E Ω)) :=
      Subgroup.isClosed_of_isOpen _ p.2.2.2.2.2.1
    exact hk.isOpen_compl
  have hK : IsCompact ((rcgKer c l Q : Set (G E Ω))ᶜ) := hO.isClosed_compl.isCompact
  have hcov : (rcgKer c l Q : Set (G E Ω))ᶜ ⊆ ⋃ p, U p := by
    intro h hh
    have hn : ¬ ∀ (A : Type) [CommGroup A] (φ : G E Ω →* A), IsRcgChar c l Q φ → φ h = 1 := hh
    push Not at hn
    obtain ⟨A, inst, φ, hφ, hne⟩ := hn
    exact Set.mem_iUnion.2 ⟨⟨A, inst, φ, hφ⟩, hne⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo hcov
  have hord : ∀ p : ι, ∃ n : ℕ, (by letI := p.2.1; exact p.2.2.1 g ^ (l ^ n) = 1) := by
    intro p
    let _ := p.2.1
    exact p.2.2.2.2.1 (p.2.2.1 g)
  choose nf hnf using hord
  refine ⟨∑ p ∈ t, nf p, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  by_contra hnot
  obtain ⟨p, hp, hmem⟩ := Set.mem_iUnion₂.1 (ht hnot)
  let _ := p.2.1
  apply hmem
  show p.2.2.1 (g ^ (l ^ (∑ p ∈ t, nf p))) = 1
  obtain ⟨k, hk⟩ := pow_dvd_pow l (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp : nf p ≤ ∑ p ∈ t, nf p)
  rw [map_pow, hk, pow_mul, hnf p, one_pow]

end rcg

end Formalism.L2.NC
