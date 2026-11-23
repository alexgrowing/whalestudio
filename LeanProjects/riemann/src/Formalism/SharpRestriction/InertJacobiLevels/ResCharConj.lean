import Formalism.SharpRestriction.InertJacobiLevels.ExtraVal

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain IsLocalRing

variable (D : D7) (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0)

def toLL0 : D.what₂.LL →+* ↥D.LL0 := (RingHom.id D.what₂.LL).codRestrict D.LL0 hLL0

def phiO : 𝓞 ↥D.LL0 →+* 𝓞 D.what₂.LL := RingOfIntegers.mapRingHom (algebraMap ↥D.LL0 D.what₂.LL)

def psiO : 𝓞 D.what₂.LL →+* 𝓞 ↥D.LL0 := RingOfIntegers.mapRingHom (toLL0 D hLL0)

theorem phi_psi (x : 𝓞 D.what₂.LL) : phiO D (psiO D hLL0 x) = x := RingOfIntegers.ext rfl

def plLL0 (P : HeightOneSpectrum (𝓞 D.what₂.LL)) : HeightOneSpectrum (𝓞 ↥D.LL0) where
  asIdeal := P.asIdeal.comap (phiO D)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : psiO D hLL0 x ∈ P.asIdeal.comap (phiO D) := by
      rw [Ideal.mem_comap, phi_psi]; exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← phi_psi D hLL0 x, h1, map_zero]

theorem cover_at (hc : NTw.TwCover D.ntw) (w : D.what₂.places.Pl) : ∃ i, D.ntw.l i = D.what₂.places.resChar w ∧
    ∀ x : 𝓞 ↥D.LL0, x ∈ (plLL0 D hLL0 (D.plEq w)).asIdeal ↔
      ∃ y ∈ maximalIdeal (D.ntw.O0 i),
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0) :=
  hc _ (D.what₂.places.resChar_prime w) (plLL0 D hLL0 (D.plEq w)) (by
    show phiO D _ ∈ (D.plEq w).asIdeal
    rw [map_natCast]
    exact resChar_mem D w)

def gOk (i : D.ntw.Tw) (k : ℕ) : D.ntw.O0 i →+* D.ntw.Ok i k :=
  (algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))

theorem gOk_inj (i : D.ntw.Tw) (k : ℕ) : Function.Injective (gOk D i k) :=
  (D.ntw.Ok_inj i k).comp (D.ntw.O_inj i)

theorem gOkF_inj (i : D.ntw.Tw) (k : ℕ) : Function.Injective
    ((algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k))).comp (gOk D i k)) :=
  (IsFractionRing.injective _ _).comp (gOk_inj D i k)

def iotaOk (i : D.ntw.Tw) (k : ℕ) : FractionRing (D.ntw.O0 i) →+* FractionRing (D.ntw.Ok i k) :=
  IsFractionRing.lift (gOkF_inj D i k)

theorem iotaOk_alg (i : D.ntw.Tw) (k : ℕ) (y : D.ntw.O0 i) :
    iotaOk D i k (algebraMap _ _ y) = algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k)) (gOk D i k y) :=
  IsFractionRing.lift_algebraMap (gOkF_inj D i k) y

theorem l_ne_zero (i : D.ntw.Tw) : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := by
  intro h
  have h1 : D.ntw.emb0 i ((D.ntw.l i : ℕ) : ↥D.LL0) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))), h, map_zero]
  have h2 := (map_eq_zero (D.ntw.emb0 i)).1 h1
  have h3 : (D.ntw.l i : ℕ) = 0 := by exact_mod_cast h2
  exact (Fact.out : (D.ntw.l i).Prime).ne_zero h3

theorem gOk_local (i : D.ntw.Tw) (k : ℕ) (y : D.ntw.O0 i) (hy : y ∈ maximalIdeal (D.ntw.O0 i)) :
    gOk D i k y ∈ maximalIdeal (D.ntw.Ok i k) := by
  have h1 := map_mem_maximalIdeal (algebraMap (D.ntw.O0 i) (D.ntw.O i)) (D.ntw.l i) (l_ne_zero D i) (D.ntw.O_l i) y hy
  have := D.ntw.Ok_fin i k
  have hint : (algebraMap (D.ntw.O i) (D.ntw.Ok i k)).IsIntegral :=
    algebraMap_isIntegral_iff.mpr inferInstance
  have hloc := hint.isLocalHom (D.ntw.Ok_inj i k)
  rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
  exact fun h => h1 (hloc.map_nonunit _ h)

def embAt (i : D.ntw.Tw) : D.what₂.LL →+* FractionRing (D.ntw.Ok i 1) :=
  (iotaOk D i 1).comp ((D.ntw.emb0 i).comp (toLL0 D hLL0))

theorem embAt_w (w : D.what₂.places.Pl) (i : D.ntw.Tw)
    (hi : ∀ x : 𝓞 ↥D.LL0, x ∈ (plLL0 D hLL0 (D.plEq w)).asIdeal ↔
      ∃ y ∈ maximalIdeal (D.ntw.O0 i),
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔
      embAt D hLL0 i x ∈ (algebraMap (D.ntw.Ok i 1) (FractionRing (D.ntw.Ok i 1))).range := by
  rw [val_nonneg_iff]
  refine val_le_one_iff (D.plEq w) (IsFractionRing.injective _ _) (embAt D hLL0 i) ?_ ?_ x
  · intro a ha
    have h1 : psiO D hLL0 a ∈ (plLL0 D hLL0 (D.plEq w)).asIdeal := by
      show phiO D (psiO D hLL0 a) ∈ (D.plEq w).asIdeal
      rw [phi_psi]; exact ha
    obtain ⟨y, hy, hy'⟩ := (hi _).1 h1
    refine ⟨gOk D i 1 y, gOk_local D i 1 y hy, ?_⟩
    rw [← iotaOk_alg, hy']
    rfl
  · intro a ha
    have h1 : psiO D hLL0 a ∉ (plLL0 D hLL0 (D.plEq w)).asIdeal := by
      show ¬ phiO D (psiO D hLL0 a) ∈ (D.plEq w).asIdeal
      rw [phi_psi]; exact ha
    have hint : IsIntegral (D.ntw.O0 i) (D.ntw.emb0 i ((psiO D hLL0 a : 𝓞 ↥D.LL0) : ↥D.LL0)) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom (D.ntw.O0 i)) (D.ntw.emb0 i) (RingHom.ext_int _ _)
        (RingOfIntegers.isIntegral_coe (psiO D hLL0 a))
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hu : IsUnit y := by
      by_contra hn
      exact h1 ((hi _).2 ⟨y, (mem_maximalIdeal y).2 hn, hy⟩)
    refine ⟨(hu.map (gOk D i 1)).unit, ?_⟩
    rw [IsUnit.unit_spec, ← iotaOk_alg, hy]
    rfl

def embAtB (i : D.ntw.Tw) : D.what₂.LL →+* FractionRing (D.ntw.Ok i 1) :=
  (iotaOk D i 1).comp ((D.ntw.emb0b i).comp (toLL0 D hLL0))

theorem embAtB_eq (i : D.ntw.Tw) (x : D.what₂.LL) : embAtB D hLL0 i x = embAt D hLL0 i (star x) :=
  congrArg (iotaOk D i 1) (D.ntw.restX_coefficientEmbedding_conj i (toLL0 D hLL0 x) (toLL0 D hLL0 (star x)) rfl)

def repW (w : D.what₂.places.Pl) : D.what₂.places.Pl :=
  @Classical.epsilon _ ⟨w⟩ (fun v => v = w ∨ v = D.what₂.places.conj w)

theorem repW_spec (w : D.what₂.places.Pl) : repW D w = w ∨ repW D w = D.what₂.places.conj w :=
  @Classical.epsilon_spec _ (fun v => v = w ∨ v = D.what₂.places.conj w) ⟨w, Or.inl rfl⟩

theorem repW_conj (w : D.what₂.places.Pl) : repW D (D.what₂.places.conj w) = repW D w := by
  unfold repW
  congr 1
  funext v
  rw [D.what₂.places.conj_conj]
  exact propext or_comm

theorem resChar_conj' (w : D.what₂.places.Pl) :
    D.what₂.places.resChar (D.what₂.places.conj w) = D.what₂.places.resChar w := by
  have hp := D.what₂.places.resChar_prime w
  have hq := D.what₂.places.resChar_prime (D.what₂.places.conj w)

  have h1 : (0 : WithTop ℤ) < D.what₂.places.val (D.what₂.places.conj w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.conj_val, star_natCast, D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have h2 : (0 : WithTop ℤ) < D.what₂.places.val (D.what₂.places.conj w)
      ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar]
    exact_mod_cast D.what₂.places.ramIdx_pos _
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  have h3 : (1 : D.what₂.LL) = (a : D.what₂.LL) * ((D.what₂.places.resChar (D.what₂.places.conj w) : ℕ) : D.what₂.LL) +
      (b : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    have := congrArg (fun z : ℤ => (z : D.what₂.LL)) hab
    push_cast at this
    exact this.symm
  have hint : ∀ z : ℤ, (0 : WithTop ℤ) ≤ D.what₂.places.val (D.what₂.places.conj w) (z : D.what₂.LL) := fun z => by
    rw [val_nonneg_iff]
    have := (D.plEq (D.what₂.places.conj w)).valuation_le_one (K := D.what₂.LL) (z : 𝓞 D.what₂.LL)
    simpa using this
  have h4 : (0 : WithTop ℤ) < D.what₂.places.val (D.what₂.places.conj w) (1 : D.what₂.LL) := by
    rw [h3]
    refine lt_of_lt_of_le ?_ (AddValuation.map_add _ _ _)
    rw [lt_min_iff, AddValuation.map_mul, AddValuation.map_mul]
    exact ⟨lt_of_lt_of_le h2 (le_add_of_nonneg_left (hint a)), lt_of_lt_of_le h1 (le_add_of_nonneg_left (hint b))⟩
  rw [AddValuation.map_one] at h4
  exact lt_irrefl _ h4

open Classical in

def nchEmbOf (hc : NTw.TwCover D.ntw) : NChEmb D where
  twI := fun w => (cover_at D hLL0 hc (repW D w)).choose
  twI_l := fun w => by
    rw [(cover_at D hLL0 hc (repW D w)).choose_spec.1]
    rcases repW_spec D w with h | h
    · rw [h]
    · rw [h, resChar_conj']
  sd := fun w => decide (repW D w = w)
  embW := fun w => if repW D w = w then embAt D hLL0 _ else embAtB D hLL0 _
  embW_w := fun w x => by
    by_cases h : repW D w = w
    · rw [if_pos h]
      have := embAt_w D hLL0 (repW D w) _ (cover_at D hLL0 hc (repW D w)).choose_spec.2 x
      have e : D.what₂.places.val (repW D w) x = D.what₂.places.val w x := by rw [h]
      rw [e] at this
      exact this
    · rw [if_neg h, embAtB_eq]
      have h' : repW D w = D.what₂.places.conj w := (repW_spec D w).resolve_left h
      have := embAt_w D hLL0 (repW D w) _ (cover_at D hLL0 hc (repW D w)).choose_spec.2 (star x)
      have e : D.what₂.places.val (repW D w) (star x) = D.what₂.places.val w x := by
        rw [h', D.conj_val, star_star]
      rw [e] at this
      exact this

end Formalism.MainNotions.Inhab

end
