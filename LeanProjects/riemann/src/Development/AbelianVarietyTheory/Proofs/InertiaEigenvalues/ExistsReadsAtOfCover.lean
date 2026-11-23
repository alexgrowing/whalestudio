import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivMapLattice

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

variable (D : D7)

theorem val_nonneg_iff (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := by simpa using hx
  rw [D.val_eq w x hx, vAdd, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.log_exp]
  norm_cast
  exact neg_nonneg

theorem val_pos_iff (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 < D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x < 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := by simpa using hx
  rw [D.val_eq w x hx, vAdd, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.log_exp]
  norm_cast
  exact neg_pos

theorem val_pos_iff_mem (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0) :
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔
      algebraMap (𝓞 ↥D.LL0) (𝓞 D.what₂.LL) x ∈ (D.plEq w).asIdeal := by
  rw [val_pos_iff, ← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL)]
  rfl

theorem val_resChar_pos (w : D.what₂.places.Pl) :
    0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
  rw [D.what₂.places.val_resChar]
  exact_mod_cast D.what₂.places.ramIdx_pos w

theorem eq_resChar_of_pos (w : D.what₂.places.Pl) {p : ℕ} (hp : p.Prime)
    (h : 0 < D.what₂.places.val w ((p : ℕ) : D.what₂.LL)) : p = D.what₂.places.resChar w := by
  by_contra hne
  have h1 := (val_pos_iff_mem D w (p : 𝓞 ↥D.LL0)).1 (by simpa using h)
  have h2 := (val_pos_iff_mem D w (D.what₂.places.resChar w : 𝓞 ↥D.LL0)).1 (by simpa using val_resChar_pos D w)
  rw [map_natCast] at h1 h2
  have h3 : IsCoprime ((p : ℕ) : 𝓞 D.what₂.LL) ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp (D.what₂.places.resChar_prime w)).2 hne)
  obtain ⟨a, b, hab⟩ := h3
  exact (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem exists_star_int (hG : IsGalois ℚ ↥D.LL0) (x : 𝓞 ↥D.LL0) :
    ∃ y : 𝓞 ↥D.LL0, ((y : ↥D.LL0) : D.what₂.LL) = star ((x : ↥D.LL0) : D.what₂.LL) := by
  let s : D.what₂.LL →ₐ[ℚ] D.what₂.LL := (starRingEnd D.what₂.LL).toRatAlgHom
  have h1 : star ((x : ↥D.LL0) : D.what₂.LL) ∈ D.LL0 :=
    (IntermediateField.normal_iff_forall_map_le.1 hG.to_normal s) ⟨_, (x : ↥D.LL0).2, rfl⟩
  have h2 : IsIntegral ℤ (star ((x : ↥D.LL0) : D.what₂.LL)) :=
    IsIntegral.map_of_comp_eq (RingHom.id ℤ) ((starRingEnd D.what₂.LL).comp (algebraMap ↥D.LL0 D.what₂.LL))
      (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe x)
  exact ⟨⟨⟨_, h1⟩, (isIntegral_algebraMap_iff (algebraMap ↥D.LL0 D.what₂.LL).injective).1 h2⟩, rfl⟩

theorem exists_star (hG : IsGalois ℚ ↥D.LL0) (x : ↥D.LL0) : ∃ y : ↥D.LL0, (y : D.what₂.LL) = star (x : D.what₂.LL) :=
  ⟨⟨_, (IntermediateField.normal_iff_forall_map_le.1 hG.to_normal (starRingEnd D.what₂.LL).toRatAlgHom)
    ⟨_, x.2, rfl⟩⟩, rfl⟩

def OverOne (w w' : D.what₂.places.Pl) : Prop :=
  ∀ x : 𝓞 ↥D.LL0, 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔
    0 < D.what₂.places.val w' ((x : ↥D.LL0) : D.what₂.LL)

def OverOnePair (w w' : D.what₂.places.Pl) : Prop := OverOne D w w' ∨ OverOne D (D.what₂.places.conj w) w'

variable {D}

theorem OverOne.conj (hG : IsGalois ℚ ↥D.LL0) {w w' : D.what₂.places.Pl} (h : OverOne D w w') :
    OverOne D (D.what₂.places.conj w) (D.what₂.places.conj w') := fun x => by
  obtain ⟨y, hy⟩ := exists_star_int D hG x
  rw [D.conj_val, D.conj_val, ← hy]
  exact h y

theorem overOnePair_refl (w : D.what₂.places.Pl) : OverOnePair D w w := Or.inl fun _ => Iff.rfl

theorem overOnePair_conj (w : D.what₂.places.Pl) : OverOnePair D w (D.what₂.places.conj w) := Or.inr fun _ => Iff.rfl

theorem OverOnePair.symm (hG : IsGalois ℚ ↥D.LL0) {w w' : D.what₂.places.Pl} (h : OverOnePair D w w') :
    OverOnePair D w' w := by
  rcases h with h | h
  · exact Or.inl fun x => (h x).symm
  · have h1 := h.conj hG
    rw [D.what₂.places.conj_conj] at h1
    exact Or.inr fun x => (h1 x).symm

theorem OverOnePair.trans (hG : IsGalois ℚ ↥D.LL0) {w w' w'' : D.what₂.places.Pl} (h : OverOnePair D w w')
    (h' : OverOnePair D w' w'') : OverOnePair D w w'' := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl fun x => (h x).trans (h' x)
  · exact Or.inr fun x => (h.conj hG x).trans (h' x)
  · exact Or.inr fun x => (h x).trans (h' x)
  · have h1 := h.conj hG
    rw [D.what₂.places.conj_conj] at h1
    exact Or.inl fun x => (h1 x).trans (h' x)

def sideEmb (i : D.ntw.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (D.ntw.O0 i) :=
  if b then D.ntw.emb0 i else D.ntw.emb0b i

def ReadsAt (i : D.ntw.Tw) (b : Bool) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : 𝓞 ↥D.LL0, (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = sideEmb i b (x : ↥D.LL0)) ↔
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)

theorem sideEmb_not (i : D.ntw.Tw) (b : Bool) {x y : ↥D.LL0} (h : (y : D.what₂.LL) = star (x : D.what₂.LL)) :
    sideEmb i (!b) x = sideEmb i b y := by
  cases b
  · exact (D.ntw.restX_coefficientEmbedding_conj i y x (by rw [h, star_star])).symm
  · exact D.ntw.restX_coefficientEmbedding_conj i x y h

theorem ReadsAt.conj (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl} (h : ReadsAt i b w) :
    ReadsAt i (!b) (D.what₂.places.conj w) := fun x => by
  obtain ⟨y, hy⟩ := exists_star_int D hG x
  rw [sideEmb_not i b hy, D.conj_val, ← hy]
  exact h y

theorem ReadsAt.of_overOne {i : D.ntw.Tw} {b : Bool} {w w' : D.what₂.places.Pl} (h : ReadsAt i b w) (h' : OverOne D w w') :
    ReadsAt i b w' := fun x => (h x).trans (h' x)

theorem ReadsAt.overOnePair (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b b' : Bool} {w w' : D.what₂.places.Pl}
    (h : ReadsAt i b w) (h' : ReadsAt i b' w') : OverOnePair D w w' := by
  by_cases hb : b' = b
  · subst hb
    exact Or.inl fun x => (h x).symm.trans (h' x)
  · obtain rfl : b' = !b := by revert hb; cases b <;> cases b' <;> simp
    exact Or.inr fun x => (h.conj hG x).symm.trans (h' x)

theorem l_mem_max (i : D.ntw.Tw) : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := fun hu =>
  D.ntw.O_l i (by simpa using hu.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)))

theorem ReadsAt.l_eq {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl} (h : ReadsAt i b w) :
    D.ntw.l i = D.what₂.places.resChar w :=
  eq_resChar_of_pos D w (D.ntw.lPrime i).out
    (by simpa using (h (D.ntw.l i : 𝓞 ↥D.LL0)).1 ⟨_, l_mem_max i, by simp⟩)

theorem ReadsAt.inW1 (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl} (h : ReadsAt i b w)
    (hw : TwistedAt D w) : D.ntw.NonzeroIndexPlace i := by
  cases b
  · exact ⟨_, (twistedAt_conj D w).2 hw, h.conj hG⟩
  · exact ⟨w, hw, h⟩

def below (w : D.what₂.places.Pl) : HeightOneSpectrum (𝓞 ↥D.LL0) := (D.plEq w).under (𝓞 ↥D.LL0)

theorem mem_below (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0) :
    x ∈ (below w).asIdeal ↔ 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) := (val_pos_iff_mem D w x).symm

theorem resChar_mem_below (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : 𝓞 ↥D.LL0) ∈ (below w).asIdeal :=
  (mem_below w _).2 (by simpa using val_resChar_pos D w)

theorem exists_readsAt_of_pair (hc : TwCoverPair D) {w : D.what₂.places.Pl} (hw : TwistedAt D w) :
    ∃ i b, ReadsAt i b w := by
  obtain ⟨i, -, h | h⟩ := hc _ (D.what₂.places.resChar_prime w) (below w) (resChar_mem_below w) ⟨w, hw, mem_below w⟩
  · exact ⟨i, true, fun x => (h x).symm.trans (mem_below w x)⟩
  · exact ⟨i, false, fun x => (h x).symm.trans (mem_below w x)⟩

theorem exists_readsAt_of_cover (hc : D.ntw.TwCover) (w : D.what₂.places.Pl) : ∃ i b, ReadsAt i b w := by
  obtain ⟨i, -, h⟩ := hc _ (D.what₂.places.resChar_prime w) (below w) (resChar_mem_below w)
  exact ⟨i, true, fun x => (h x).symm.trans (mem_below w x)⟩

theorem exists_orbitRep : ∃ o : D.what₂.places.Pl → D.what₂.places.Pl,
    ∀ w, (o w = w ∨ o w = D.what₂.places.conj w) ∧ o (D.what₂.places.conj w) = o w := by
  refine ⟨fun w => @Classical.epsilon _ ⟨w⟩ fun v => v = w ∨ v = D.what₂.places.conj w, fun w => ⟨?_, ?_⟩⟩
  · exact Classical.epsilon_spec (p := fun v => v = w ∨ v = D.what₂.places.conj w) ⟨w, Or.inl rfl⟩
  · simp only [D.what₂.places.conj_conj, or_comm]

theorem exists_settings (hG : IsGalois ℚ ↥D.LL0) (hc : TwCoverPair D) (i₀ : D.ntw.Tw) :
    ∃ (twI : D.what₂.places.Pl → D.ntw.Tw) (sd : D.what₂.places.Pl → Bool),
      (∀ w, TwistedAt D w → ReadsAt (twI w) (sd w) w ∧
        (D.what₂.places.conj w ≠ w → sd (D.what₂.places.conj w) = !sd w)) ∧
      ∀ w w', OverOnePair D w w' → twI w' = twI w := by
  classical
  haveI : Nonempty D.ntw.Tw := ⟨i₀⟩
  let twI : D.what₂.places.Pl → D.ntw.Tw := fun w => Classical.epsilon fun i => ∃ v b, OverOnePair D w v ∧ ReadsAt i b v
  have h1 : ∀ w w', OverOnePair D w w' → twI w' = twI w := fun w w' h => by
    refine congrArg Classical.epsilon (funext fun i => propext ⟨?_, ?_⟩)
    · rintro ⟨v, b, hv, hb⟩
      exact ⟨v, b, h.trans hG hv, hb⟩
    · rintro ⟨v, b, hv, hb⟩
      exact ⟨v, b, (h.symm hG).trans hG hv, hb⟩
  have h2 : ∀ w, ∃ b, TwistedAt D w → ReadsAt (twI w) b w := fun w => by
    by_cases hw : TwistedAt D w
    · obtain ⟨i, b, hi⟩ := exists_readsAt_of_pair hc hw
      obtain ⟨v, b', hv, hb⟩ := Classical.epsilon_spec (p := fun i => ∃ v b, OverOnePair D w v ∧ ReadsAt i b v)
        ⟨i, w, b, overOnePair_refl w, hi⟩
      rcases hv.symm hG with hv | hv
      · exact ⟨b', fun _ => hb.of_overOne hv⟩
      · exact ⟨!b', fun _ => (hb.conj hG).of_overOne hv⟩
    · exact ⟨true, fun h => absurd h hw⟩
  choose s hs using h2
  obtain ⟨o, ho⟩ := exists_orbitRep (D := D)
  refine ⟨twI, fun w => if o w = w then s w else !s (D.what₂.places.conj w), fun w hw => ⟨?_, fun hne => ?_⟩, h1⟩
  · by_cases h : o w = w
    · simpa only [h, if_true] using hs w hw
    · have h3 := (hs _ ((twistedAt_conj D w).2 hw)).conj hG
      rw [D.what₂.places.conj_conj, h1 w _ (overOnePair_conj w)] at h3
      simpa only [h, if_false] using h3
  · simp only [(ho w).2, D.what₂.places.conj_conj]
    rcases (ho w).1 with h | h
    · rw [if_neg (by rw [h]; exact hne.symm), if_pos h]
    · rw [if_pos h, if_neg (by rw [h]; exact hne), Bool.not_not]

theorem isLocalHom_phiK (i : D.ntw.Tw) (k : ℕ) : IsLocalHom (BlochKatoReduction.Gen.phiK D.ntw i k) := by
  haveI := D.ntw.Ok_fin i k
  haveI : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i k)
  haveI : IsLocalHom (algebraMap (D.ntw.O0 i) (D.ntw.O i)) := by
    refine ⟨fun y hy => ?_⟩
    by_contra hu
    haveI : CharZero (FractionRing (D.ntw.O0 i)) := (RingHom.charZero_iff (D.ntw.emb0 i).injective).1 inferInstance
    have hl : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := fun h => by
      have := congrArg (algebraMap _ (FractionRing (D.ntw.O0 i))) h
      rw [map_natCast, map_zero] at this
      exact (D.ntw.lPrime i).out.ne_zero (Nat.cast_eq_zero.1 this)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (D.ntw.O0 i)
    obtain ⟨n, u, hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
    have hy' : y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := hu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hy'
    obtain ⟨a, rfl⟩ := hy'
    rw [map_mul] at hy
    refine D.ntw.O_l i ?_
    rw [← map_natCast (algebraMap (D.ntw.O0 i) (D.ntw.O i)), hu', map_mul, map_pow]
    exact (u.isUnit.map _).mul ((isUnit_of_mul_isUnit_left hy).pow n)
  unfold BlochKatoReduction.Gen.phiK
  infer_instance

structure Reading (i : D.ntw.Tw) (k : ℕ) (b : Bool) (w : D.what₂.places.Pl) : Type 1 where
  Oe : Type
  [cr : CommRing Oe]
  [dom : IsDomain Oe]
  [dvr : IsDiscreteValuationRing Oe]
  [alg : Algebra (D.ntw.Ok i k) Oe]
  inj : Function.Injective (algebraMap (D.ntw.Ok i k) Oe)
  fin : Module.Finite (D.ntw.Ok i k) Oe
  loc : IsLocalHom (algebraMap (D.ntw.Ok i k) Oe)
  emb : D.what₂.LL →+* FractionRing Oe
  emb_w : ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ emb x ∈ (algebraMap Oe (FractionRing Oe)).range
  emb_side : ∀ (x : ↥D.LL0) (y z : D.ntw.O0 i),
    sideEmb i b x * algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z =
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y →
    emb (x : D.what₂.LL) * algebraMap Oe (FractionRing Oe) (algebraMap (D.ntw.Ok i k) Oe (BlochKatoReduction.Gen.phiK D.ntw i k z)) =
      algebraMap Oe (FractionRing Oe) (algebraMap (D.ntw.Ok i k) Oe (BlochKatoReduction.Gen.phiK D.ntw i k y))

attribute [instance] Reading.cr Reading.dom Reading.dvr Reading.alg

theorem ReadsAt.nonempty_reading {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl} (h : ReadsAt i b w) (k : ℕ) :
    Nonempty (Reading i k b w) := by
  haveI := D.ntw.Ok_fin i k
  haveI := D.ntw.O_complete i
  haveI := FormalIsogeny.isAdicComplete_maximalIdeal_of_finite (D.ntw.O i) (D.ntw.Ok i k)
  haveI := isLocalHom_phiK i k
  have hinj : Function.Injective (BlochKatoReduction.Gen.phiK D.ntw i k) := (D.ntw.Ok_inj i k).comp (D.ntw.O_inj i)
  let m : FractionRing (D.ntw.O0 i) →+* FractionRing (D.ntw.Ok i k) := IsFractionRing.map hinj
  have hm : ∀ y, m (algebraMap _ _ y) = algebraMap _ _ (BlochKatoReduction.Gen.phiK D.ntw i k y) := fun y => by
    simp [m, IsFractionRing.map]
  obtain ⟨O, _, _, _, _, e, h1, h2, h3, h4, h5⟩ := exists_coeff_ext D.what₂.LL D.LL0 (D.ntw.Ok i k)
    (m.comp (sideEmb i b)) (D.plEq w) fun x => by
      rw [← val_pos_iff_mem, ← h x]
      obtain ⟨φ, hφ⟩ := exists_intMap (sideEmb i b)
      constructor
      · rintro ⟨y, hy, hy'⟩
        exact ⟨_, map_nonunit (BlochKatoReduction.Gen.phiK D.ntw i k) y hy, by rw [← hm, hy']; rfl⟩
      · rintro ⟨y, hy, hy'⟩
        refine ⟨φ x, fun hu => hy ?_, hφ x⟩
        have : y = BlochKatoReduction.Gen.phiK D.ntw i k (φ x) :=
          IsFractionRing.injective _ (FractionRing (D.ntw.Ok i k)) (by rw [hy', ← hm, hφ]; rfl)
        exact this ▸ hu.map _
  refine ⟨{ Oe := O, inj := h1, fin := h2, loc := h3, emb := e
            emb_w := fun x => (val_nonneg_iff D w x).trans (h4 x)
            emb_side := fun x y z hxy => h5 x _ _ ?_ }⟩
  rw [← hm, ← hm, ← hxy, map_mul]
  rfl

def Reading.conj (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} (ρ : Reading i k b w) :
    Reading i k (!b) (D.what₂.places.conj w) where
  Oe := ρ.Oe
  inj := ρ.inj
  fin := ρ.fin
  loc := ρ.loc
  emb := ρ.emb.comp (starRingEnd D.what₂.LL)
  emb_w x := by rw [D.conj_val]; exact ρ.emb_w _
  emb_side x y z h := by
    obtain ⟨x', hx'⟩ := exists_star D hG x
    rw [sideEmb_not i b hx'] at h
    have h1 := ρ.emb_side x' y z h
    rw [hx'] at h1
    exact h1

theorem star_root {x : (D.what₂.LL)ˣ} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1) :
    star (x : D.what₂.LL) = ((x⁻¹ : (D.what₂.LL)ˣ) : D.what₂.LL) := by
  apply D.what₂.embLL.injective
  have h1 : ‖D.what₂.embLL (x : D.what₂.LL)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]) hn.ne'
  rw [D.starLL_cx, Units.val_inv_eq_inv_val, map_inv₀, Complex.inv_eq_conj h1]

end GlobalTheory.TwistChoice

end
