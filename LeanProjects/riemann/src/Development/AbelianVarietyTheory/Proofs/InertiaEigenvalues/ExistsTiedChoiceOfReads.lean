import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeSame

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

def TwistedPairSettingHyps (D : D7) : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i

def FullRank (D : D7) (E : IntegralHeckeForms.XD D) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b)

variable {D : D7}

theorem exists_inputs (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) (hR : FullRank D E) (hT : IntegralHeckeForms.adm7 D E) :
    ∃ S, ∀ i, D.ntw.NonzeroIndexPlace i → TwIn.Ok ⟨E, N0, S⟩ i := by
  have h : ∀ i j b, ∃ S : Finset (D.nexp.Dat i j b), D.ntw.NonzeroIndexPlace i → j ∈ Finset.Icc 1 D.R.m →
      IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) S := fun i j b => by
    by_cases h : D.ntw.NonzeroIndexPlace i ∧ j ∈ Finset.Icc 1 D.R.m
    · obtain ⟨S, hS⟩ := exists_basisOf D.nexp i j b _ (th_fg D.nexp E hT i h.1 j h.2 b)
      exact ⟨S, fun _ _ => hS⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose S hS using h
  exact ⟨S, fun i hi => ⟨hR i hi, fun j hj b => hS i j b hi hj⟩⟩

abbrev TwPl (D : D7) : Type := {w : D.what₂.places.Pl // TwistedAt D w}

def TwPl.conj (w : TwPl D) : TwPl D := ⟨D.what₂.places.conj w.1, (twistedAt_conj D w.1).2 w.2⟩

def GoodPack (I : TwIn D) (p : TwPack D) : Prop :=
  I.Ok p.1 ∧ IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 p.1 (twEps D p.1) (I.S p.1) (AvRec D) p.2.1 p.2.2.1 p.2.2.2

def GoodData (I : TwIn D) (t : TwPl D → TwPack D) (sd : D.what₂.places.Pl → Bool) : Prop :=
  ∀ w : TwPl D, ReadsAt (t w).1 (sd w.1) w.1 ∧ t w.conj = t w ∧
    (D.what₂.places.conj w.1 ≠ w.1 → sd (D.what₂.places.conj w.1) = !sd w.1) ∧ GoodPack I (t w)

def Apart (Q Q' : Finset (PlE D.host)) : Prop :=
  ∀ P ∈ Q, ∀ P' ∈ Q', ∀ p : ℕ, p.Prime → ¬ (P ∈ placesOver D.host.E p ∧ P' ∈ placesOver D.host.E p)

def ExistsData (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∃ S, ∀ A : D.ntw.Tw → Finset (PlE D.host), ∃ (t : TwPl D → TwPack D) (sd : D.what₂.places.Pl → Bool),
    GoodData ⟨E, N0, S⟩ t sd ∧ (∀ w, Disjoint (t w).2.1 (A (t w).1)) ∧
    (∀ w w' : TwPl D, OverOnePair D w.1 w'.1 → t w' = t w) ∧
    ({w | TwistedAt D w}.Finite → ∀ w w' : TwPl D, ¬ OverOnePair D w.1 w'.1 → Apart (t w).2.1 (t w').2.1)

theorem Apart.symm {Q Q' : Finset (PlE D.host)} (h : Apart Q Q') : Apart Q' Q :=
  fun P hP P' hP' p hp hh => h P' hP' P hP p hp hh.symm

theorem exists_finset_apart (B : Finset (PlE D.host)) :
    ∃ B' : Finset (PlE D.host), ∀ Q, Disjoint Q B' → Apart Q B := by
  have h : (⋃ P' ∈ (B : Set (PlE D.host)), placesOver D.host.E (Ideal.absNorm P'.asIdeal)).Finite :=
    B.finite_toSet.biUnion fun P' _ => placesOver_finite_av _ _ (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P'.ne_bot)
  refine ⟨h.toFinset, fun Q hQ P hP P' hP' p hp hh => Finset.disjoint_left.1 hQ hP ?_⟩
  rw [Set.Finite.mem_toFinset]
  refine Set.mem_biUnion hP' ?_
  have h1 : Ideal.absNorm P'.asIdeal ∣ p ^ Module.finrank ℤ (𝓞 D.host.E) := by
    have h2 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hh.2)
    rwa [Ideal.absNorm_span_natCast] at h2
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow hp).1 h1
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact P'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 hn)
  show ((Ideal.absNorm P'.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  rw [hn, Nat.cast_pow]
  exact Ideal.pow_mem_of_mem _ hh.1 _ (Nat.pos_of_ne_zero hn0)

theorem exists_apart_choice {ι : Type} {Z : ι → Type} (c : ∀ i, Z i → Finset (PlE D.host)) (P : ∀ i, Z i → Prop)
    (h : ∀ i (B : Finset (PlE D.host)), ∃ z, P i z ∧ Apart (c i z) B) (T : Finset ι) :
    ∃ f : ∀ i, Z i, (∀ i, P i (f i)) ∧ ∀ i ∈ T, ∀ i' ∈ T, i ≠ i' → Apart (c i (f i)) (c i' (f i')) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    choose f hf using fun i => h i ∅
    exact ⟨f, fun i => (hf i).1, by simp⟩
  | insert a T ha ih =>
    obtain ⟨f, hf, hf'⟩ := ih
    obtain ⟨z, hz, hz'⟩ := h a (T.biUnion fun i => c i (f i))
    have key : ∀ i ∈ T, Apart (c a (Function.update f a z a)) (c i (Function.update f a z i)) := fun i hi => by
      rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hi)]
      exact fun P hP P' hP' => hz' P hP P' (Finset.mem_biUnion.2 ⟨i, hi, hP'⟩)
    refine ⟨Function.update f a z, fun i => ?_, fun i hi i' hi' hne => ?_⟩
    · by_cases hi : i = a
      · subst hi; rwa [Function.update_self]
      · rw [Function.update_of_ne hi]; exact hf i
    · rcases Finset.mem_insert.1 hi with h1 | h1 <;> rcases Finset.mem_insert.1 hi' with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · subst h1; exact key i' h2
      · subst h2; exact (key i h1).symm
      · rw [Function.update_of_ne (by rintro rfl; exact ha h1), Function.update_of_ne (by rintro rfl; exact ha h2)]
        exact hf' i h1 i' h2 hne

open Classical in
theorem goodTw_union {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ} {i : D.ntw.Tw} {e : ℝ} {S} {A B Q : Finset (PlE D.host)} {k : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} (h : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S (A ∪ B) Q k ψ) :
    IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S A Q k ψ ∧ Disjoint Q B := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨⟨⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.1, h2.2.2.1⟩, h3⟩, h4⟩, h2.2.2.2⟩

theorem existsData (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) (hconds : IntegralHeckeForms.aux₃ D (BlochKatoReduction.bk0 D) E N0) (hS : TwistedPairSettingHyps D)
    (hR : FullRank D E) (hT : IntegralHeckeForms.adm7 D E) (hc : TwCoverPair D) (hG : IsGalois ℚ ↥D.LL0) : ExistsData D E N0 := by
  classical
  obtain ⟨S, hI⟩ := exists_inputs E N0 hR hT
  refine ⟨S, fun A => ?_⟩
  rcases isEmpty_or_nonempty (TwPl D) with he | ⟨⟨w₀⟩⟩
  · exact ⟨he.elim, fun _ => true, he.elim, he.elim, he.elim, fun _ => he.elim⟩
  obtain ⟨i₀, -⟩ := exists_readsAt_of_pair hc w₀.2
  obtain ⟨twI, sd, h1, h2⟩ := exists_settings hG hc i₀
  let T : Finset D.ntw.Tw := if h : {w | TwistedAt D w}.Finite then h.toFinset.image twI else ∅
  obtain ⟨f, hf, hf'⟩ := exists_apart_choice (D := D)
    (Z := fun i => Σ (Q : Finset (PlE D.host)) (k : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (fun _ z => z.1)
    (fun i z => D.ntw.NonzeroIndexPlace i → GoodPack ⟨E, N0, S⟩ ⟨i, z⟩ ∧ Disjoint z.1 (A i)) (fun i B => by
      by_cases hi : D.ntw.NonzeroIndexPlace i
      · obtain ⟨B', hB'⟩ := exists_finset_apart B
        obtain ⟨Q, k, ψ, h⟩ := hconds i hi (hS i hi) _ (twEps_pos D i) (hI i hi).1 _ (hI i hi).2 (AvRec D ∪ (A i ∪ B'))
        obtain ⟨h3, h4⟩ := goodTw_union h
        rw [Finset.disjoint_union_right] at h4
        exact ⟨⟨Q, k, ψ⟩, fun _ => ⟨⟨hI i hi, h3⟩, h4.1⟩, hB' Q h4.2⟩
      · exact ⟨⟨∅, 0, 1⟩, fun h => absurd h hi, fun P hP => by simp at hP⟩) T
  have h3 : ∀ w w' : TwPl D, OverOnePair D w.1 w'.1 →
      (⟨twI w'.1, f (twI w'.1)⟩ : TwPack D) = ⟨twI w.1, f (twI w.1)⟩ := fun w w' h =>
    congrArg (fun i => (⟨i, f i⟩ : TwPack D)) (h2 _ _ h)
  have h4 := fun w : TwPl D => hf _ ((h1 w.1 w.2).1.inW1 hG w.2)
  refine ⟨fun w => ⟨twI w.1, f (twI w.1)⟩, sd,
    fun w => ⟨(h1 w.1 w.2).1, h3 w w.conj (overOnePair_conj w.1), (h1 w.1 w.2).2, (h4 w).1⟩, fun w => (h4 w).2, h3,
    fun hfin w w' hne => ?_⟩
  have hT' : ∀ v : TwPl D, twI v.1 ∈ T := fun v => by
    simp only [T, dif_pos hfin]
    exact Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 v.2)
  refine hf' _ (hT' w) _ (hT' w') fun heq => hne ?_
  exact (h1 w.1 w.2).1.overOnePair hG (heq ▸ (h1 w'.1 w'.2).1)

def Reading.Pulls {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} (ρ : Reading i k b w)
    {Q : Finset (PlE D.host)} (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap ρ.Oe (FractionRing ρ.Oe)
    (algebraMap (D.ntw.Ok i k) ρ.Oe ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))

def HasReading (p : TwPack D) (b : Bool) (w : D.what₂.places.Pl) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∃ ρ : Reading p.1 p.2.2.1 b w, ρ.Pulls (BlochKatoReduction.Gen.psiAt b p.2.2.2) ψ₀

def ValuesIn (p : TwPack D) : Prop :=
  ∃ n : ℕ, 0 < n ∧ (∃ z : D.what₂.LL, IsPrimitiveRoot z n) ∧ ∀ δ, p.2.2.2 δ ^ n = 1

def IsCharOf (t : TwPl D → TwPack D) (sd : D.what₂.places.Pl → Bool)
    (ψ₀ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) : Prop :=
  (∀ w, ψ₀ (D.what₂.places.conj w) = ψ₀ w) ∧ (∀ w, ¬ TwistedAt D w → ψ₀ w = 1) ∧
    ∀ w : TwPl D, HasReading (t w) (sd w.1) w.1 (ψ₀ w.1)

theorem psiAt_not {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (x : Γ) :
    BlochKatoReduction.Gen.psiAt (!b) ψ x = (BlochKatoReduction.Gen.psiAt b ψ x)⁻¹ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

theorem psiAt_pow {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) {n : ℕ} (h : ∀ x, ψ x ^ n = 1) (x : Γ) :
    BlochKatoReduction.Gen.psiAt b ψ x ^ n = 1 := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt, h]

theorem pull_inv {L K A B Δ : Type} [Field L] [Field K] [CommRing A] [CommRing B] [Group Δ] [Fintype Δ] (e : L →+* K)
    (m : A →+* B) (m' : B →+* K) (χ : Δ →* Aˣ) (x : Lˣ) (δ : Δ) (h : e (x : L) = m' (m (χ δ : A))) :
    x ^ Fintype.card Δ = 1 ∧ e ((x⁻¹ : Lˣ) : L) = m' (m (((χ δ)⁻¹ : Aˣ) : A)) := by
  constructor
  · apply Units.ext
    apply e.injective
    rw [Units.val_pow_eq_pow_val, map_pow e, h, ← map_pow m', ← map_pow m, ← Units.val_pow_eq_pow_val, ← map_pow χ,
      pow_card_eq_one]
    simp
  · rw [Units.val_inv_eq_inv_val, map_inv₀, h]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem exists_pull {L K A B Γ Δ : Type} [Field L] [Field K] [CommRing A] [CommRing B] [Group Γ] [Group Δ] (e : L →+* K)
    (m : A →+* B) (m' : B →+* K) (χ : Δ →* Aˣ) (a : Γ →* Δ) {n : ℕ} (hn : 0 < n) {z : L} (hz : IsPrimitiveRoot z n)
    (h : ∀ δ, χ δ ^ n = 1) : ∃ ψ : Γ →* Lˣ, ∀ g, e (ψ g : L) = m' (m (χ (a g) : A)) :=
  exists_char_descent e hn hz ((Units.map (m'.comp m).toMonoidHom).comp (χ.comp a)) fun g => by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_pow, h, map_one]

theorem Reading.Pulls.conj (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} {ρ : Reading i k b w}
    {Q : Finset (PlE D.host)} {ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (hρ : ρ.Pulls ψ ψ₀) (h : ∀ x, ψ' x = (ψ x)⁻¹) : (ρ.conj hG).Pulls ψ' ψ₀ := by
  intro g
  have h0 := pull_inv ρ.emb (algebraMap (D.ntw.Ok i k) ρ.Oe) (algebraMap ρ.Oe (FractionRing ρ.Oe)) ψ (ψ₀ g) (D.ntw.art i Q g) (hρ g)
  have h2 := h0.2
  rw [← star_root Fintype.card_pos h0.1, ← h] at h2
  exact h2

theorem HasReading.conj (hG : IsGalois ℚ ↥D.LL0) {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} (h : HasReading p b w ψ₀) :
    HasReading p (!b) (D.what₂.places.conj w) ψ₀ :=
  let ⟨ρ, hρ⟩ := h
  ⟨ρ.conj hG, hρ.conj hG (psiAt_not b _)⟩

theorem psiAt_one {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (x : Γ) : BlochKatoReduction.Gen.psiAt b (1 : Γ →* A) x = 1 := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

theorem Reading.pulls_one {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} (ρ : Reading i k b w)
    {Q : Finset (PlE D.host)} {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} (h : ∀ x, ψ x = 1) : ρ.Pulls ψ 1 := fun g => by
  rw [h, MonoidHom.one_apply, Units.val_one, Units.val_one, map_one ρ.emb, map_one (algebraMap _ ρ.Oe),
    map_one (algebraMap ρ.Oe _)]

theorem exists_hasReading {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl} (h : ReadsAt p.1 b w) (hv : ValuesIn p) :
    ∃ ψ₀, HasReading p b w ψ₀ := by
  obtain ⟨ρ⟩ := h.nonempty_reading p.2.2.1
  obtain ⟨n, hn, ⟨z, hz⟩, hψ⟩ := hv
  obtain ⟨ψ₀, h₀⟩ := exists_pull ρ.emb (algebraMap (D.ntw.Ok p.1 p.2.2.1) ρ.Oe) (algebraMap ρ.Oe (FractionRing ρ.Oe))
    (BlochKatoReduction.Gen.psiAt b p.2.2.2) (D.ntw.art p.1 p.2.1) hn hz (psiAt_pow b _ hψ)
  exact ⟨ψ₀, ρ, h₀⟩

theorem exists_isCharOf (hG : IsGalois ℚ ↥D.LL0) {I : TwIn D} {t : TwPl D → TwPack D} {sd : D.what₂.places.Pl → Bool}
    (h : GoodData I t sd) (hv : ∀ w, ValuesIn (t w)) : ∃ ψ₀, IsCharOf t sd ψ₀ := by
  have h1 : ∀ w, ∃ ψ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ,
      (∀ hw : TwistedAt D w, HasReading (t ⟨w, hw⟩) (sd w) w ψ) ∧ (¬ TwistedAt D w → ψ = 1) := fun w => by
    by_cases hw : TwistedAt D w
    · obtain ⟨ψ, hψ⟩ := exists_hasReading (h ⟨w, hw⟩).1 (hv _)
      exact ⟨ψ, fun _ => hψ, fun h => absurd hw h⟩
    · exact ⟨1, fun h => absurd h hw, fun _ => rfl⟩
  choose ψ hψ hψ' using h1
  obtain ⟨o, ho⟩ := exists_orbitRep (D := D)
  refine ⟨fun w => ψ (o w), fun w => by simp only [(ho w).2], fun w hw => hψ' _ ?_, fun w => ?_⟩
  · rcases (ho w).1 with h2 | h2 <;> rw [h2]
    · exact hw
    · rwa [twistedAt_conj]
  · show HasReading (t w) (sd w.1) w.1 (ψ (o w.1))
    by_cases h2 : o w.1 = w.1
    · rw [h2]; exact hψ w.1 w.2
    · have h3 := (ho w.1).1.resolve_left h2
      have h4 : HasReading (t w.conj) (!sd (D.what₂.places.conj w.1)) (D.what₂.places.conj (D.what₂.places.conj w.1))
        (ψ (D.what₂.places.conj w.1)) := (hψ _ w.conj.2).conj hG
      rw [(h w).2.1, (h w).2.2.1 (h3 ▸ h2), Bool.not_not, D.what₂.places.conj_conj] at h4
      rwa [h3]

def RankEq (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (w : D.what₂.places.Pl) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → Module.finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) =
    Module.finrank (FractionRing (D.ntw.Ok i k)) (D.nexp.MtV i j b k Q (ψ.comp (D.ntw.art i Q)))

def RankTie (p : TwPack D) (b : Bool) (w : D.what₂.places.Pl) : Prop :=
  RankEq p.1 b p.2.1 p.2.2.1 (BlochKatoReduction.Gen.psiAt b p.2.2.2) w

theorem exists_formsIso {Oe : Type} [CommRing Oe] [IsDomain Oe] [IsDiscreteValuationRing Oe] {A : Type} [CommRing A] [IsDomain A] [Algebra A Oe]
    (hinj : Function.Injective (algebraMap A Oe)) {V : Type} [AddCommGroup V] [Module (FractionRing A) V] [Module A V]
    [IsScalarTower A (FractionRing A) V] (Λ : Submodule A V) (hfg : Λ.FG)
    (hspan : Submodule.span (FractionRing A) (Λ : Set V) = ⊤) (e : D.what₂.LL →+* FractionRing Oe) (μ : D.what₂.Tup) (j : ℕ) (c : Prop)
    (h : c → Module.finrank D.what₂.LL (D.what₂.MtL μ j) = Module.finrank (FractionRing A) V) :
    ∃ f : D.what₂.MtL μ j →ₛₗ[e] FractionRing Oe ⊗[A] V, c →
      (∀ (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j)) D.what₂.LL (D.what₂.MtL μ j)),
        LinearIndependent (FractionRing Oe) (fun a => f (b a)) ∧
          Submodule.span (FractionRing Oe) (Set.range fun a => f (b a)) = ⊤) ∧
      Submodule.span Oe (f '' {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).gen}) =
        Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V)) := by
  by_cases hj : c
  · obtain ⟨h1, h2, h3⟩ := form_gen (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _)
      (D.what₂.jMt_basis _ j _) _ (D.what₂.MtLat μ j).span_top (D.what₂.MtLat_sub _ j)
    obtain ⟨h4, h5⟩ := baseChange_lattice hinj Λ hfg hspan
    obtain ⟨f, hf⟩ := exists_semilinear e _ h2 h3
      (Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V))) ((h hj).trans h4.symm)
    exact ⟨f, fun _ => ⟨fun b => hf.1 _ b, hf.2⟩⟩
  · exact ⟨0, fun h1 => absurd h1 hj⟩

section ChoiceOf

variable (twI : D.what₂.places.Pl → D.ntw.Tw) (b : D.what₂.places.Pl → Bool) (Q : D.what₂.places.Pl → Finset (PlE D.host))
  (k : D.what₂.places.Pl → ℕ) (ψ : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k w))ˣ)
  (hr : ∀ w, ReadsAt (twI w) (b w) w) (ρ : ∀ w, Reading (twI w) (k w) (b w) w)
  (h : ∀ w, TwistedAt D w → RankEq (twI w) (b w) (Q w) (k w) (ψ w) w)

def choiceOf : NChoice D :=
  let H := fun w j => exists_formsIso (ρ w).inj _
    (D.nexp.MtLat_fg (twI w) j (b w) (k w) (Q w) ((ψ w).comp (D.ntw.art (twI w) (Q w))))
    (D.nexp.MtLat_span _ _ _ _ _ _) (ρ w).emb (D.what₂.muTw w) j (TwistedAt D w ∧ 1 ≤ j ∧ j ≤ D.R.m)
    fun c => h w c.1 j c.2.1 c.2.2
  { twI := twI
    twI_l := fun w => (hr w).l_eq
    sd := b
    Q := Q
    k' := k
    psi' := ψ
    Oe := fun w => (ρ w).Oe
    algOOe := fun w => ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
      (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
    towOe := fun w =>
      letI := ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
        (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Oe_inj := fun w => (ρ w).inj
    Oe_fin := fun w => (ρ w).fin
    Oe_loc := fun w => (ρ w).loc
    embW := fun w => (ρ w).emb
    embW_w := fun w => (ρ w).emb_w
    eMt := fun w j => (H w j).choose
    eMt_basis := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).1
    eMt_lat := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).2 }

end ChoiceOf

def choiceOfPack (p : D.what₂.places.Pl → TwPack D) (b : D.what₂.places.Pl → Bool) (hr : ∀ w, ReadsAt (p w).1 (b w) w)
    (ρ : ∀ w, Reading (p w).1 (p w).2.2.1 (b w) w) (h : ∀ w, TwistedAt D w → RankTie (p w) (b w) w) : NChoice D :=
  choiceOf (fun w => (p w).1) b (fun w => (p w).2.1) (fun w => (p w).2.2.1) (fun w => BlochKatoReduction.Gen.psiAt (b w) (p w).2.2.2) hr ρ h

theorem pack_choiceOf (p : D.what₂.places.Pl → TwPack D) (b : D.what₂.places.Pl → Bool) (hr : ∀ w, ReadsAt (p w).1 (b w) w)
    (ρ : ∀ w, Reading (p w).1 (p w).2.2.1 (b w) w) (h : ∀ w, TwistedAt D w → RankTie (p w) (b w) w)
    (w : D.what₂.places.Pl) : NChoicePack (choiceOfPack p b hr ρ h) w = p w :=
  congrArg (fun ψ => (⟨(p w).1, (p w).2.1, (p w).2.2.1, ψ⟩ : TwPack D)) (psiAt_psiAt (b w) (p w).2.2.2)

def Records (C : NChoice D) (t : TwPl D → TwPack D) (sd : D.what₂.places.Pl → Bool) : Prop :=
  ∀ w : TwPl D, NChoicePack C w.1 = t w ∧ C.sd w.1 = sd w.1

theorem Records.good {C : NChoice D} {I : TwIn D} {t : TwPl D → TwPack D} {sd : D.what₂.places.Pl → Bool}
    (hC : Records C t sd) (h : GoodData I t sd) : TwConjAt D C ∧ TwGoodAt D C I := by
  refine ⟨fun w hw => ⟨?_, fun hne => ?_⟩, fun w hw => ?_⟩
  · exact (hC (TwPl.conj ⟨w, hw⟩)).1.trans ((h ⟨w, hw⟩).2.1.trans (hC ⟨w, hw⟩).1.symm)
  · exact (hC (TwPl.conj ⟨w, hw⟩)).2.trans (((h ⟨w, hw⟩).2.2.1 hne).trans (congrArg _ (hC ⟨w, hw⟩).2.symm))
  · have h1 := (h ⟨w, hw⟩).2.2.2
    rw [← (hC ⟨w, hw⟩).1] at h1
    exact h1

def LocsCarry (t : TwPl D → TwPack D) (sd : D.what₂.places.Pl → Bool)
    (ψ₀ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)) : Prop :=
  ∀ a : D.nd.Loc, D.ntw.twOf a = (t ⟨D.nd.w a, D.nd.w_tw a⟩).1 ∧ D.ntw.twSide a = sd (D.nd.w a) ∧
    D.nd.Q a = (t ⟨D.nd.w a, D.nd.w_tw a⟩).2.1 ∧
    ∀ g, D.nd.embK a ((ψ₀ (D.nd.w a) g : (D.what₂.LL)ˣ) : D.what₂.LL) =
      algebraMap (D.nd.O a) (FractionRing (D.nd.O a)) ((D.ntw.psiL a g : (D.nd.O a)ˣ) : D.nd.O a)

def ReadElsewhere (D : D7) : Prop := ∀ w, ¬ TwistedAt D w → ∃ i b, ReadsAt (D := D) i b w

theorem readElsewhere_of_cover (h : D.ntw.TwCover) : ReadElsewhere D := fun w _ => exists_readsAt_of_cover h w

theorem exists_choice (hc : ReadElsewhere D) {I : TwIn D} {t : TwPl D → TwPack D} {sd : D.what₂.places.Pl → Bool}
    (h : GoodData I t sd) (hr : ∀ w, RankTie (t w) (sd w.1) w.1) : ∃ C : NChoice D, Records C t sd := by
  have h1 : ∀ w, ∃ (p : TwPack D) (b : Bool), ReadsAt p.1 b w ∧ ∀ hw : TwistedAt D w, p = t ⟨w, hw⟩ ∧ b = sd w := fun w => by
    by_cases hw : TwistedAt D w
    · exact ⟨t ⟨w, hw⟩, sd w, (h ⟨w, hw⟩).1, fun _ => ⟨rfl, rfl⟩⟩
    · obtain ⟨i, b, hi⟩ := hc w hw
      exact ⟨⟨i, ∅, 0, 1⟩, b, hi, fun h => absurd h hw⟩
  choose p b hp hp' using h1
  refine ⟨choiceOfPack p b hp (fun w => ((hp w).nonempty_reading _).some) fun w hw => ?_,
    fun w => ⟨(pack_choiceOf _ _ _ _ _ _).trans (hp' w.1 w.2).1, (hp' w.1 w.2).2⟩⟩
  rw [(hp' w hw).1, (hp' w hw).2]
  exact hr ⟨w, hw⟩

theorem exists_tied_choice_of_reads (hc : ReadElsewhere D) {t : TwPl D → TwPack D} {sd : D.what₂.places.Pl → Bool}
    (h : ∀ w : TwPl D, ReadsAt (t w).1 (sd w.1) w.1) (hr : ∀ w, RankTie (t w) (sd w.1) w.1)
    {ψ₀ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)} (hψ : IsCharOf t sd ψ₀) (hl : LocsCarry t sd ψ₀) :
    ∃ C : NChoice D, NChTie D C ∧ Records C t sd := by
  have h1 : ∀ w, ∃ (p : TwPack D) (b : Bool), (ReadsAt p.1 b w ∧ ∀ hw : TwistedAt D w, p = t ⟨w, hw⟩ ∧ b = sd w) ∧
      HasReading p b w (ψ₀ w) := fun w => by
    by_cases hw : TwistedAt D w
    · exact ⟨t ⟨w, hw⟩, sd w, ⟨h ⟨w, hw⟩, fun _ => ⟨rfl, rfl⟩⟩, hψ.2.2 ⟨w, hw⟩⟩
    · obtain ⟨i, b, hi⟩ := hc w hw
      obtain ⟨ρ⟩ := hi.nonempty_reading 0
      rw [hψ.2.1 w hw]
      exact ⟨⟨i, ∅, 0, 1⟩, b, ⟨hi, fun h => absurd h hw⟩, ρ, ρ.pulls_one (psiAt_one b)⟩
  choose p b hp ρ hρ using h1
  have h2 : ∀ w, TwistedAt D w → RankTie (p w) (b w) w := fun w hw => by
    rw [((hp w).2 hw).1, ((hp w).2 hw).2]
    exact hr ⟨w, hw⟩
  refine ⟨choiceOfPack p b (fun w => (hp w).1) ρ h2, ⟨fun a => ?_, fun a => ?_, fun a => ?_,
      ⟨ψ₀, hψ.1, hρ, fun a => (hl a).2.2.2⟩, fun w x y z _ hx => (ρ w).emb_side x y z hx⟩,
    fun w => ⟨(pack_choiceOf _ _ _ _ _ _).trans ((hp w.1).2 w.2).1, ((hp w.1).2 w.2).2⟩⟩
  · exact (hl a).1.trans (congrArg Sigma.fst ((hp _).2 (D.nd.w_tw a)).1.symm)
  · exact (hl a).2.1.trans ((hp _).2 (D.nd.w_tw a)).2.symm
  · exact (hl a).2.2.1.trans (congrArg (fun q : TwPack D => q.2.1) ((hp _).2 (D.nd.w_tw a)).1.symm)

theorem exists_tied_choice (hc : ReadElsewhere D) {I : TwIn D} {t : TwPl D → TwPack D} {sd : D.what₂.places.Pl → Bool}
    (h : GoodData I t sd) (hr : ∀ w, RankTie (t w) (sd w.1) w.1)
    {ψ₀ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)} (hψ : IsCharOf t sd ψ₀) (hl : LocsCarry t sd ψ₀) :
    ∃ C : NChoice D, NChTie D C ∧ Records C t sd :=
  exists_tied_choice_of_reads hc (fun w => (h w).1) hr hψ hl

def BuildsChoice (D : D7) : Prop :=
  ∀ (I : TwIn D) (t : TwPl D → TwPack D) (sd : D.what₂.places.Pl → Bool), GoodData I t sd →
    ((∀ w, ValuesIn (t w)) → ∃ ψ₀, IsCharOf t sd ψ₀) ∧
    (ReadElsewhere D → (∀ w, RankTie (t w) (sd w.1) w.1) →
      (∃ C : NChoice D, Records C t sd ∧ TwConjAt D C ∧ TwGoodAt D C I) ∧
      ∀ ψ₀, IsCharOf t sd ψ₀ → LocsCarry t sd ψ₀ →
        ∃ C : NChoice D, NChTie D C ∧ Records C t sd ∧ TwConjAt D C ∧ TwGoodAt D C I)

theorem buildsChoice (hG : IsGalois ℚ ↥D.LL0) : BuildsChoice D := fun _ _ _ h =>
  ⟨exists_isCharOf hG h, fun hc hr =>
    ⟨let ⟨C, hC⟩ := exists_choice hc h hr; ⟨C, hC, hC.good h⟩, fun _ hψ hl =>
      let ⟨C, h1, hC⟩ := exists_tied_choice hc h hr hψ hl; ⟨C, h1, hC, hC.good h⟩⟩⟩

theorem readsAt_of_tie {C : NChoice D} (h : NChTie D C) (w : D.what₂.places.Pl) : ReadsAt (C.twI w) (C.sd w) w := by
  intro x
  obtain ⟨φ, hφ⟩ := exists_intMap (sideEmb (C.twI w) (C.sd w))
  haveI := isLocalHom_phiK (C.twI w) (C.k' w)
  haveI := C.Oe_loc w
  have h1 : C.embW w ((x : ↥D.LL0) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w))
      (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    have h2 := h.embedding_baseField_condition w x (φ x) 1 one_ne_zero (by rw [map_one, mul_one, hφ]; rfl)
    simp only [map_one, mul_one] at h2
    exact h2
  have h2 : (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (C.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y = sideEmb (C.twI w) (C.sd w) (x : ↥D.LL0)) ↔
      ¬ IsUnit (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    rw [isUnit_map_iff, isUnit_map_iff]
    exact ⟨fun ⟨y, hy, hy'⟩ => IsFractionRing.injective _ (FractionRing _) (hy'.trans (hφ x).symm) ▸ hy,
      fun hu => ⟨_, hu, hφ x⟩⟩
  rw [h2]
  generalize algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x)) = u at h1
  generalize ((x : ↥D.LL0) : D.what₂.LL) = x' at h1
  by_cases hx : x' = 0
  · subst hx
    rw [map_zero, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h1
    simp [h1]
  have h3 : 0 < D.what₂.places.val w x' ↔ ¬ 0 ≤ D.what₂.places.val w x'⁻¹ := by
    rw [val_pos_iff, val_nonneg_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 (by simpa using hx))]
  have hu : algebraMap (C.Oe w) (FractionRing (C.Oe w)) u ≠ 0 := h1 ▸ (map_ne_zero _).2 hx
  rw [h3, C.embW_w, map_inv₀, h1, not_iff_not]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v⁻¹ : (C.Oe w)ˣ), eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])⟩
  · rintro ⟨v, hv⟩
    exact IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing (C.Oe w))
      (by rw [map_mul, hv, mul_inv_cancel₀ hu, map_one]))

theorem readElsewhere_of_tie {C : NChoice D} (h : NChTie D C) : ReadElsewhere D := fun w _ => ⟨_, _, readsAt_of_tie h w⟩

theorem rankTie_of_choice (C : NChoice D) (w : TwPl D) : RankTie (NChoicePack C w.1) (C.sd w.1) w.1 := by
  intro j h1 h2
  show _ = Module.finrank (FractionRing (D.ntw.Ok (C.twI w.1) (C.k' w.1))) (D.nexp.MtV (C.twI w.1) j (C.sd w.1) (C.k' w.1)
    (C.Q w.1) ((BlochKatoReduction.Gen.psiAt (C.sd w.1) (BlochKatoReduction.Gen.psiAt (C.sd w.1) (C.psi' w.1))).comp (D.ntw.art (C.twI w.1) (C.Q w.1))))
  rw [psiAt_psiAt, ← (baseChange_lattice (C.Oe_inj w.1) _ (D.nexp.MtLat_fg _ _ _ _ _ _) (D.nexp.MtLat_span _ _ _ _ _ _)).1]
  obtain ⟨h3, h4⟩ := C.eMt_basis w.1 j w.2 h1 h2 (Module.Free.chooseBasis _ _)
  rw [Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis _ _),
    Module.finrank_eq_nat_card_basis (Module.Basis.mk h3 h4.ge)]

theorem tied_unique {C C' : NChoice D} (h : NChTie D C) (h' : NChTie D C') (a : D.nd.Loc) :
    C.twI (D.nd.w a) = C'.twI (D.nd.w a) ∧ C.sd (D.nd.w a) = C'.sd (D.nd.w a) ∧ C.Q (D.nd.w a) = C'.Q (D.nd.w a) :=
  ⟨(h.twOf_eq a).symm.trans (h'.twOf_eq a), (h.twSide_eq a).symm.trans (h'.twSide_eq a), (h.Q_eq a).symm.trans (h'.Q_eq a)⟩

def MadeByExport (C : NChoice D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  TwConjAt D C ∧ ∃ S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b),
    (∀ w, TwistedAt D w → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      (∃ S', IntegralHeckeForms.BasisOf D.nexp (C.twI w) j b (IntegralHeckeForms.SgJ D.nexp E (C.twI w) j b) S') →
      IntegralHeckeForms.BasisOf D.nexp (C.twI w) j b (IntegralHeckeForms.SgJ D.nexp E (C.twI w) j b) (S (C.twI w) j b)) ∧
    ∀ w, TwistedAt D w → (∃ Q k ψ, TwGoodOne D ⟨E, N0, S⟩ (C.twI w) (C.sd w) Q k ψ) →
      TwGoodOne D ⟨E, N0, S⟩ (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

theorem good_of_madeByExport {C : NChoice D} {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ} (hconds : IntegralHeckeForms.aux₃ D (BlochKatoReduction.bk0 D) E N0)
    (hS : TwistedPairSettingHyps D) (hR : FullRank D E) (hT : IntegralHeckeForms.adm7 D E) (hG : IsGalois ℚ ↥D.LL0) (ht : NChTie D C)
    (h : MadeByExport C E N0) : TwConjAt D C ∧ ∃ S, TwGoodAt D C ⟨E, N0, S⟩ := by
  obtain ⟨h1, S, h2, h3⟩ := h
  have hW := fun w hw => (readsAt_of_tie ht w).inW1 hG hw
  have hI : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → TwIn.Ok ⟨E, N0, S⟩ (C.twI w) := fun w hw =>
    ⟨hR _ (hW w hw), fun j hj b => h2 w hw j hj b (exists_basisOf D.nexp _ j b _ (th_fg D.nexp E hT _ (hW w hw) j hj b))⟩
  obtain ⟨Q, k, ψ, h4, -⟩ := exists_good_of_conditions D ⟨E, N0, S⟩ C.twI C.sd hconds (fun w hw => hS _ (hW w hw)) hI hW
  exact ⟨h1, S, fun w hw => ⟨hI w hw, h3 w hw ⟨_, _, _, h4 w hw⟩⟩⟩

theorem madeByExport_of_good {C : NChoice D} {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ} {S} (h : TwConjAt D C)
    (h' : TwGoodAt D C ⟨E, N0, S⟩) : MadeByExport C E N0 :=
  ⟨h, S, fun w hw j hj b _ => (h' w hw).1.2 j hj b, fun w hw _ => (h' w hw).2⟩

theorem goodData_of_tied {C : NChoice D} {I : TwIn D} (ht : NChTie D C) (h : TwConjAt D C) (h' : TwGoodAt D C I) :
    GoodData I (fun w => NChoicePack C w.1) C.sd ∧ Records C (fun w => NChoicePack C w.1) C.sd ∧ ReadElsewhere D ∧
      ∀ w : TwPl D, RankTie (NChoicePack C w.1) (C.sd w.1) w.1 :=
  ⟨fun w => ⟨readsAt_of_tie ht w.1, (h w.1 w.2).1, (h w.1 w.2).2, h' w.1 w.2⟩, fun _ => ⟨rfl, rfl⟩,
    readElsewhere_of_tie ht, rankTie_of_choice C⟩

def InputsAt (D : D7) (E : IntegralHeckeForms.XD D) : Prop :=
  (∀ N0, IntegralHeckeForms.adm8 D N0 → IntegralHeckeForms.aux₃ D (BlochKatoReduction.bk0 D) E N0) ∧ TwistedPairSettingHyps D ∧ FullRank D E ∧ IntegralHeckeForms.adm7 D E

def FamInputs {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), InputsAt (Fm.D x i) (twE Fm x hx i)

def FamExists {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    (∀ N0, IntegralHeckeForms.adm8 (Fm.D x i) N0 → ExistsData (Fm.D x i) (twE Fm x hx i) N0) ∧ BuildsChoice (Fm.D x i)

def FamMade {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ N0, IntegralHeckeForms.adm8 (Fm.D x i) N0 ∧ MadeByExport (Fm.ex x hx i).nch (twE Fm x hx i) N0

theorem famExists {eps : ℝ} {Fm : FamP eps} (h : FamInputs Fm) : FamExists Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨x0, fun x hx0 hx i => ⟨fun N0 hN => ?_, buildsChoice (Fm.ties x i).baseField_isGalois⟩⟩
  obtain ⟨h1, h2, h3, h4⟩ := h x hx0 hx i
  exact existsData _ N0 (h1 N0 hN) h2 h3 h4 (Fm.ties x i).tw_cover (Fm.ties x i).baseField_isGalois

theorem twGood_of_made {eps : ℝ} {Fm : FamP eps} (h : FamInputs Fm) (hm : FamMade Fm) : TwGood Fm := by
  obtain ⟨x0, h⟩ := h
  obtain ⟨x1, hm⟩ := hm
  refine ⟨max x0 x1, fun x hx0 hx i => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h x (le_of_max_le_left hx0) hx i
  obtain ⟨N0, hN, h5⟩ := hm x (le_of_max_le_right hx0) hx i
  obtain ⟨h6, S, h7⟩ := good_of_madeByExport (h1 N0 hN) h2 h3 h4 (Fm.ties x i).baseField_isGalois (Fm.ex x hx i).nch_tie h5
  exact ⟨h6, N0, S, h7⟩

def PrimeTo (A : Finset ℕ) (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ p ∈ A, p.Prime → P ∉ placesOver D.host.E p

def SamePlace (i : D.ntw.Tw) (b : Bool) (i' : D.ntw.Tw) (b' : Bool) : Prop :=
  ∀ x : 𝓞 ↥D.LL0, (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = sideEmb i b (x : ↥D.LL0)) ↔
    ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i'),
      algebraMap (D.ntw.O0 i') (FractionRing (D.ntw.O0 i')) y = sideEmb i' b' (x : ↥D.LL0)

theorem ReadsAt.samePlace {i i' : D.ntw.Tw} {b b' : Bool} {w : D.what₂.places.Pl} (h : ReadsAt i b w) (h' : ReadsAt i' b' w) :
    SamePlace i b i' b' := fun x => (h x).trans (h' x).symm

theorem SamePlace.readsAt {i i' : D.ntw.Tw} {b b' : Bool} {w : D.what₂.places.Pl} (h : SamePlace i b i' b') (h' : ReadsAt i b w) :
    ReadsAt i' b' w := fun x => (h x).symm.trans (h' x)

theorem ReadsAt.side (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl} (h : ReadsAt i b w) (b' : Bool) :
    ∃ v, OverOnePair D w v ∧ ReadsAt i b' v := by
  by_cases hb : b' = b
  · exact ⟨w, overOnePair_refl w, hb ▸ h⟩
  · obtain rfl : b' = !b := by revert hb; cases b <;> cases b' <;> simp
    exact ⟨_, overOnePair_conj w, h.conj hG⟩

theorem ReadsAt.of_pair (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b : Bool} {v w : D.what₂.places.Pl} (h : ReadsAt i b v)
    (h' : OverOnePair D v w) : ∃ b', ReadsAt i b' w := by
  rcases h' with h' | h'
  · exact ⟨b, h.of_overOne h'⟩
  · exact ⟨!b, (h.conj hG).of_overOne h'⟩

def Shaped (A : Finset ℕ) (U : Finset (TwPack D)) : Prop :=
  (∀ p ∈ U, D.ntw.NonzeroIndexPlace p.1 ∧ BlochKatoReduction.Gen.PsiOk p.1 (AvRec D) p.2.1 p.2.2.1 p.2.2.2 ∧ PrimeTo A p.2.1) ∧
  (∀ w, TwistedAt D w → ∃ p ∈ U, ∃ b, ReadsAt p.1 b w) ∧
  (∀ p ∈ U, ∀ p' ∈ U, ∀ b b', SamePlace p.1 b p'.1 b' → p = p') ∧
  ∀ p ∈ U, ∀ p' ∈ U, p ≠ p' → Apart p.2.1 p'.2.1

abbrev Pass (D : D7) : Type := (∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)) × Finset (TwPack D)

def FirstPass (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) (A : Finset ℕ) (x : Pass D) : Prop :=
  Shaped A x.2 ∧ ∀ p ∈ x.2, GoodPack ⟨E, N0, x.1⟩ p

def firstPass (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) (A : Finset ℕ) : Pass D :=
  @Classical.epsilon _ ⟨(fun _ _ _ => ∅, ∅)⟩ (FirstPass D E N0 A)

def FirstInputs (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  IntegralHeckeForms.aux₃ D (BlochKatoReduction.bk0 D) E N0 ∧ TwistedPairSettingHyps D ∧ FullRank D E ∧ IntegralHeckeForms.adm7 D E ∧ TwCoverPair D ∧ IsGalois ℚ ↥D.LL0 ∧
    {w | TwistedAt D w}.Finite

theorem GoodPack.psiOk {I : TwIn D} {p : TwPack D} (h : GoodPack I p) :
    BlochKatoReduction.Gen.PsiOk p.1 (AvRec D) p.2.1 p.2.2.1 p.2.2.2 := by
  classical
  obtain ⟨-, ⟨h1, h2, h3⟩, -⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.2⟩, h3⟩

theorem firstPass_spec {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ} (h : FirstInputs D E N0) (A : Finset ℕ) :
    FirstPass D E N0 A (firstPass D E N0 A) := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, hG, hfin⟩ := h
  refine Classical.epsilon_spec (p := FirstPass D E N0 A) ?_
  obtain ⟨S, hS⟩ := existsData E N0 h1 h2 h3 h4 h5 hG
  have hA : (⋃ p ∈ A.filter Nat.Prime, placesOver D.host.E p).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => placesOver_finite_av _ p (Finset.mem_filter.1 hp).2.ne_zero
  obtain ⟨t, sd, hg, hd, hp, ha⟩ := hS fun _ => hA.toFinset
  haveI : Fintype (TwPl D) := hfin.fintype
  have hm : ∀ p, p ∈ Finset.univ.image t → ∃ w, t w = p := fun p hp => by simpa using hp
  refine ⟨(S, Finset.univ.image t), ⟨fun p hp => ?_, fun w hw => ?_, fun p hp' p' hp'' b b' hs => ?_,
    fun p hp' p' hp'' hne => ?_⟩, fun p hp => ?_⟩
  · obtain ⟨w, rfl⟩ := hm p hp
    refine ⟨(hg w).1.inW1 hG w.2, (hg w).2.2.2.psiOk, fun P hP q hq hq' hPq => Finset.disjoint_left.1 (hd w) hP ?_⟩
    rw [Set.Finite.mem_toFinset]
    exact Set.mem_biUnion (Finset.mem_filter.2 ⟨hq, hq'⟩) hPq
  · exact ⟨t ⟨w, hw⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), _, (hg ⟨w, hw⟩).1⟩
  · obtain ⟨w, rfl⟩ := hm p hp'
    obtain ⟨w', rfl⟩ := hm p' hp''
    obtain ⟨v, hv, hv'⟩ := (hg w).1.side hG b
    exact (hp w w' (hv.trans hG ((hs.readsAt hv').overOnePair hG (hg w').1))).symm
  · obtain ⟨w, rfl⟩ := hm p hp'
    obtain ⟨w', rfl⟩ := hm p' hp''
    exact ha hfin w w' fun h => hne (hp w w' h).symm
  · obtain ⟨w, rfl⟩ := hm p hp
    exact (hg w).2.2.2

def Follows (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) (D : D7) (E : IntegralHeckeForms.XD D) : Prop :=
  SameExport D₀ D ∧ HEq E₀.Dat0 E.Dat0 ∧
  (∃ φ : ↥D₀.LL0 ≃+* ↥D.LL0, ∀ (i₀ : D₀.ntw.Tw) (i : D.ntw.Tw), HEq i₀ i → ∀ b x, HEq (sideEmb i₀ b x) (sideEmb i b (φ x))) ∧
  ∀ (i₀ : D₀.ntw.Tw) (i : D.ntw.Tw), HEq i₀ i → (D₀.ntw.NonzeroIndexPlace i₀ ↔ D.ntw.NonzeroIndexPlace i)

theorem exists_heq {α β : Type} (h : α = β) (a : α) : ∃ b : β, HEq a b := ⟨cast h a, (cast_heq h a).symm⟩

theorem exists_heq' {α β : Type} (h : α = β) (b : β) : ∃ a : α, HEq a b := ⟨cast h.symm b, cast_heq _ b⟩

variable {D₀ D₁ : D7} {E₀ : IntegralHeckeForms.XD D₀} {E₁ : IntegralHeckeForms.XD D₁} {E : IntegralHeckeForms.XD D}

theorem Follows.refl (D : D7) (E : IntegralHeckeForms.XD D) : Follows D E D E :=
  ⟨.refl D, HEq.rfl, ⟨RingEquiv.refl _, fun _ _ h _ _ => by rw [eq_of_heq h]; rfl⟩, fun _ _ h => by rw [eq_of_heq h]⟩

theorem Follows.trans (h : Follows D₀ E₀ D₁ E₁) (h' : Follows D₁ E₁ D E) : Follows D₀ E₀ D E := by
  obtain ⟨h1, h2, ⟨φ, h3⟩, h4⟩ := h
  obtain ⟨h1', h2', ⟨φ', h3'⟩, h4'⟩ := h'
  have ht := (same_basic h1.gal h1.set h1.frm).1
  refine ⟨h1.trans h1', h2.trans h2', ⟨φ.trans φ', fun i₀ i hi b x => ?_⟩, fun i₀ i hi => ?_⟩ <;>
    obtain ⟨i₁, h₁⟩ := exists_heq ht i₀
  · exact (h3 i₀ i₁ h₁ b x).trans (h3' i₁ i (h₁.symm.trans hi) b (φ x))
  · exact (h4 i₀ i₁ h₁).trans (h4' i₁ i (h₁.symm.trans hi))

theorem follows_of_sameField (h : SameExport D₁ D) (h' : SameField D₁ D) (hE : HEq E₁.Dat0 E.Dat0) : Follows D₁ E₁ D E := by
  obtain ⟨h1, -, h2, -, h3⟩ := h'.basic h.gal h.set
  refine ⟨h, hE, h2, fun i₁ i hi => ⟨?_, ?_⟩⟩
  · rintro ⟨w₁, h4, h5⟩
    obtain ⟨w, hw⟩ := exists_heq h1 w₁
    exact ⟨w, (h'.tw _ _ hw).1 h4, ((h3 _ _ hw).2.1 _ _ hi true).1 h5⟩
  · rintro ⟨w, h4, h5⟩
    obtain ⟨w₁, hw⟩ := exists_heq' h1 w
    exact ⟨w₁, (h'.tw _ _ hw).2 h4, ((h3 _ _ hw).2.1 _ _ hi true).2 h5⟩

theorem Follows.samePlace (h : Follows D₀ E₀ D E) {i₀ j₀ : D₀.ntw.Tw} {i j : D.ntw.Tw} (hi : HEq i₀ i) (hj : HEq j₀ j)
    (b b' : Bool) : SamePlace i₀ b j₀ b' ↔ SamePlace i b j b' := by
  obtain ⟨h1, -, ⟨φ, h3⟩, -⟩ := h
  have h2 := (same_basic h1.gal h1.set h1.frm).2.2.2.2
  have h4 := fun x : 𝓞 ↥D₀.LL0 => (h2 _ _ hi).2.2 _ _ (h3 _ _ hi b (x : ↥D₀.LL0))
  have h5 := fun x : 𝓞 ↥D₀.LL0 => (h2 _ _ hj).2.2 _ _ (h3 _ _ hj b' (x : ↥D₀.LL0))
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨x₀, rfl⟩ := (RingOfIntegers.mapRingEquiv φ).surjective x
    exact (h4 x₀).symm.trans ((h x₀).trans (h5 x₀))
  · exact (h4 x).trans ((h (RingOfIntegers.mapRingEquiv φ x)).trans (h5 x).symm)

theorem Follows.fst_heq (h : Follows D₀ E₀ D E) {p₀ : TwPack D₀} {p : TwPack D} (hp : HEq p₀ p) : HEq p₀.1 p.1 :=
  ((same_basic h.1.gal h.1.set h.1.frm).2.2.2.1 p₀ p hp).1

theorem Follows.exists_good (h : Follows D₀ E₀ D E) (N₀ : D₀.ntw.Tw → ℕ) (S₀) :
    ∃ N S, ∀ (p₀ : TwPack D₀) (p : TwPack D), HEq p₀ p → GoodPack ⟨E₀, N₀, S₀⟩ p₀ → GoodPack ⟨E, N, S⟩ p := by
  obtain ⟨h1, -, h2, -⟩ := same_basic h.1.gal h.1.set h.1.frm
  obtain ⟨N, hN⟩ := exists_heq (congrArg (· → ℕ) h1) N₀
  obtain ⟨S, hS⟩ := exists_heq h2 S₀
  exact ⟨N, S, fun p₀ p hp hg => h.1.good (I := ⟨E₀, N₀, S₀⟩) (I' := ⟨E, N, S⟩) h.2.1 hN hS hp hg⟩

def MadeFrom (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) (N₀ : D₀.ntw.Tw → ℕ) (A : Finset ℕ) (D : D7) (C : NChoice D) (E : IntegralHeckeForms.XD D) : Prop :=
  Follows D₀ E₀ D E ∧ ∀ w, TwistedAt D w → (∃ p ∈ (firstPass D₀ E₀ N₀ A).2, HEq p (NChoicePack C w)) ∧
    (D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w)

theorem good_of_madeFrom {N₀ : D₀.ntw.Tw → ℕ} {A : Finset ℕ} {C : NChoice D} (hI : FirstInputs D₀ E₀ N₀)
    (h : MadeFrom D₀ E₀ N₀ A D C E) (ht : NChTie D C) (hG : IsGalois ℚ ↥D.LL0) :
    TwConjAt D C ∧ ∃ N S, TwGoodAt D C ⟨E, N, S⟩ := by
  obtain ⟨hs, hg⟩ := firstPass_spec hI A
  obtain ⟨N, S, hN⟩ := h.1.exists_good N₀ (firstPass D₀ E₀ N₀ A).1
  refine ⟨fun w hw => ⟨?_, (h.2 w hw).2⟩, N, S, fun w hw => ?_⟩
  · obtain ⟨p, hp, h1⟩ := (h.2 w hw).1
    obtain ⟨p', hp', h2⟩ := (h.2 _ ((twistedAt_conj D w).2 hw)).1
    have h3 := hs.2.2.1 p hp p' hp' _ _ ((h.1.samePlace (h.1.fst_heq h1) (h.1.fst_heq h2) _ _).2
      (((readsAt_of_tie ht w).conj hG).samePlace (readsAt_of_tie ht _)))
    exact eq_of_heq (h2.symm.trans (h3 ▸ h1))
  · obtain ⟨p, hp, h1⟩ := (h.2 w hw).1
    exact hN p _ h1 (hg p hp)

def SidesOk (t : TwPl D → TwPack D) (sd : D.what₂.places.Pl → Bool) : Prop :=
  ∀ w : TwPl D, ReadsAt (t w).1 (sd w.1) w.1 ∧ t w.conj = t w ∧
    (D.what₂.places.conj w.1 ≠ w.1 → sd (D.what₂.places.conj w.1) = !sd w.1)

def Rebuild (𝒬 : ∀ D : D7, IntegralHeckeForms.XD D → Prop) (D₁ : D7) (E₁ : IntegralHeckeForms.XD D₁) (V : Set (TwPack D₁)) : Prop :=
  ∀ t₁ sd₁ ψ₁, (∀ w, t₁ w ∈ V) → SidesOk t₁ sd₁ → IsCharOf t₁ sd₁ ψ₁ →
    ∃ (D : D7) (E : IntegralHeckeForms.XD D) (t : TwPl D → TwPack D) (sd : D.what₂.places.Pl → Bool)
      (ψ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)),
      𝒬 D E ∧ SameExport D₁ D ∧ SameField D₁ D ∧ HEq E₁.Dat0 E.Dat0 ∧
      (∀ (w₁ : TwPl D₁) (w : TwPl D), HEq w₁.1 w.1 → HEq (t₁ w₁) (t w) ∧ sd₁ w₁.1 = sd w.1) ∧ HEq ψ₁ ψ ∧
      (∀ w, RankTie (t w) (sd w.1) w.1) ∧ LocsCarry t sd ψ

def RebuildTied (𝒬 : ∀ D : D7, NChoice D → IntegralHeckeForms.XD D → Prop) (D₁ : D7) (E₁ : IntegralHeckeForms.XD D₁) (V : Set (TwPack D₁)) : Prop :=
  ∀ t₁ sd₁ ψ₁, (∀ w, t₁ w ∈ V) → SidesOk t₁ sd₁ → IsCharOf t₁ sd₁ ψ₁ →
    ∃ (D : D7) (C : NChoice D) (E : IntegralHeckeForms.XD D), 𝒬 D C E ∧ SameExport D₁ D ∧ SameField D₁ D ∧ HEq E₁.Dat0 E.Dat0 ∧ NChTie D C ∧
      ∀ (w₁ : TwPl D₁) (w : D.what₂.places.Pl), HEq w₁.1 w → HEq (t₁ w₁) (NChoicePack C w) ∧ sd₁ w₁.1 = C.sd w

theorem Rebuild.tied {𝒬 : ∀ D : D7, IntegralHeckeForms.XD D → Prop} {V : Set (TwPack D₁)} (h : Rebuild 𝒬 D₁ E₁ V) (hc : ReadElsewhere D₁) :
    RebuildTied (fun D _ E => 𝒬 D E) D₁ E₁ V := by
  intro t₁ sd₁ ψ₁ hV hs hψ
  obtain ⟨D, E, t, sd, ψ, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h t₁ sd₁ ψ₁ hV hs hψ
  obtain ⟨e1, -, -, e2, e3⟩ := h3.basic h2.gal h2.set
  obtain ⟨f1, -, -, f2, -⟩ := same_basic h2.gal h2.set h2.frm
  have key : ∀ w : TwPl D, ∃ w₁ : TwPl D₁, HEq w₁.1 w.1 := fun w =>
    let ⟨w₁, hw⟩ := exists_heq' e1 w.1
    ⟨⟨w₁, (h3.tw _ _ hw).2 w.2⟩, hw⟩
  obtain ⟨C, hC, hC'⟩ := exists_tied_choice_of_reads (t := t) (sd := sd) (ψ₀ := ψ)
    (fun w hw => by
      obtain ⟨w₁, h₁⟩ := exists_heq' e1 w
      obtain ⟨i₁, b, hi⟩ := hc w₁ fun h => hw ((h3.tw _ _ h₁).1 h)
      obtain ⟨i, hi'⟩ := exists_heq f1 i₁
      exact ⟨i, b, ((e3 _ _ h₁).2.1 _ _ hi' b).1 hi⟩)
    (fun w => by
      obtain ⟨w₁, h₁⟩ := key w
      rw [← (h5 w₁ w h₁).2]
      exact ((e3 _ _ h₁).2.1 _ _ (f2 _ _ (h5 w₁ w h₁).1).1 _).1 (hs w₁).1)
    h7 ⟨(e2 _ _ h6).1 hψ.1, fun w hw => by
      obtain ⟨w₁, h₁⟩ := exists_heq' e1 w
      exact ((e2 _ _ h6).2 _ _ h₁).2 (hψ.2.1 w₁ fun h => hw ((h3.tw _ _ h₁).1 h)), fun w => by
      obtain ⟨w₁, h₁⟩ := key w
      rw [← (h5 w₁ w h₁).2]
      exact (e3 _ _ h₁).2.2 _ _ (h5 w₁ w h₁).1 _ _ _ ((e2 _ _ h6).2 _ _ h₁).1 (hψ.2.2 w₁)⟩ h8
  refine ⟨D, C, E, h1, h2, h3, h4, hC, fun w₁ w hw => ?_⟩
  have hw' : TwistedAt D w := (h3.tw _ _ hw).1 w₁.2
  exact ⟨(h5 w₁ ⟨w, hw'⟩ hw).1.trans (heq_of_eq (hC' ⟨w, hw'⟩).1.symm), (h5 w₁ ⟨w, hw'⟩ hw).2.trans (hC' ⟨w, hw'⟩).2.symm⟩

def TwoSteps (𝓡 : ∀ D₁ : D7, IntegralHeckeForms.XD D₁ → Set (TwPack D₁) → Prop) (A : Finset ℕ) (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) : Prop :=
  ∀ U : Finset (TwPack D₀), Shaped A U → ∃ (D₁ : D7) (E₁ : IntegralHeckeForms.XD D₁), Follows D₀ E₀ D₁ E₁ ∧ IsGalois ℚ ↥D₁.LL0 ∧
    TwCoverPair D₁ ∧ (∀ p ∈ U, ∃ z : D₁.what₂.LL, IsPrimitiveRoot z (D₀.ntw.l p.1 ^ p.2.2.1)) ∧
    𝓡 D₁ E₁ {p₁ | ∃ p ∈ U, HEq p p₁}

theorem TwoSteps.mono {𝓡 𝓡' : ∀ D₁ : D7, IntegralHeckeForms.XD D₁ → Set (TwPack D₁) → Prop} {A : Finset ℕ} (h : TwoSteps 𝓡 A D₀ E₀)
    (h' : ∀ D₁ E₁ V, 𝓡 D₁ E₁ V → 𝓡' D₁ E₁ V) : TwoSteps 𝓡' A D₀ E₀ := fun U hU =>
  let ⟨D₁, E₁, h1, h2, h3, h4, h5⟩ := h U hU
  ⟨D₁, E₁, h1, h2, h3, h4, h' _ _ _ h5⟩

theorem twoSteps_of_untwisted (A : Finset ℕ) (E : IntegralHeckeForms.XD D) (h : ∀ w, ¬ TwistedAt D w) (hG : IsGalois ℚ ↥D.LL0)
    (hc : ReadElsewhere D) : TwoSteps (fun D₁ E₁ V => ReadElsewhere D₁ ∧ Rebuild (fun D' _ => D' = D) D₁ E₁ V) A D E := fun U hU =>
  ⟨D, E, .refl D E, hG, fun _ _ _ _ ⟨w, hw, _⟩ => absurd hw (h w), fun p hp => let ⟨w, hw, _⟩ := (hU.1 p hp).1; absurd hw (h w), hc,
    fun t sd ψ _ _ _ => ⟨D, E, t, sd, ψ, rfl, .refl D, .refl D, HEq.rfl, fun w => absurd w.2 (h _), HEq.rfl,
      fun w => absurd w.2 (h _), fun a => absurd (D.nd.w_tw a) (h _)⟩⟩

theorem rebuilt_self {C : NChoice D} (E : IntegralHeckeForms.XD D) (ht : NChTie D C) {t : TwPl D → TwPack D} {sd : D.what₂.places.Pl → Bool}
    (h : Records C t sd) : SameExport D D ∧ SameField D D ∧ HEq E.Dat0 E.Dat0 ∧ NChTie D C ∧
      ∀ (w₁ : TwPl D) (w : D.what₂.places.Pl), HEq w₁.1 w → HEq (t w₁) (NChoicePack C w) ∧ sd w₁.1 = C.sd w :=
  ⟨.refl D, .refl D, HEq.rfl, ht, fun w₁ _ hw => eq_of_heq hw ▸ ⟨heq_of_eq (h w₁).1.symm, (h w₁).2.symm⟩⟩

theorem exists_sides (hG : IsGalois ℚ ↥D.LL0) (t : TwPl D → TwPack D) (h : ∀ w, ∃ b, ReadsAt (t w).1 b w.1)
    (hc : ∀ w : TwPl D, t w.conj = t w) : ∃ sd, SidesOk t sd := by
  classical
  have h1 : ∀ w, ∃ b, ∀ hw : TwistedAt D w, ReadsAt (t ⟨w, hw⟩).1 b w := fun w => by
    by_cases hw : TwistedAt D w
    · obtain ⟨b, hb⟩ := h ⟨w, hw⟩
      exact ⟨b, fun _ => hb⟩
    · exact ⟨true, fun h => absurd h hw⟩
  choose s hs using h1
  obtain ⟨o, ho⟩ := exists_orbitRep (D := D)
  refine ⟨fun w => if o w = w then s w else !s (D.what₂.places.conj w), fun w => ⟨?_, hc w, fun hne => ?_⟩⟩
  · by_cases h2 : o w.1 = w.1
    · simpa only [h2, if_true] using hs w.1 w.2
    · have h3 : ReadsAt (t w.conj).1 (!s (D.what₂.places.conj w.1)) (D.what₂.places.conj (D.what₂.places.conj w.1)) :=
        (hs _ w.conj.2).conj hG
      rw [D.what₂.places.conj_conj, hc w] at h3
      simpa only [h2, if_false] using h3
  · simp only [(ho w.1).2, D.what₂.places.conj_conj]
    rcases (ho w.1).1 with h | h
    · rw [if_neg (by rw [h]; exact hne.symm), if_pos h]
    · rw [if_pos h, if_neg (by rw [h]; exact hne), Bool.not_not]

theorem Follows.exists_spread (h : Follows D₀ E₀ D E) (hG : IsGalois ℚ ↥D.LL0) (hc : TwCoverPair D) {A : Finset ℕ}
    {U : Finset (TwPack D₀)} (hU : Shaped A U) :
    ∃ (t : TwPl D → TwPack D) (sd : D.what₂.places.Pl → Bool), (∀ w, ∃ p ∈ U, HEq p (t w)) ∧ SidesOk t sd := by
  obtain ⟨f1, f2, -⟩ := same_basic h.1.gal h.1.set h.1.frm
  have h1 : ∀ w : TwPl D, ∃ q : TwPack D, (∃ p ∈ U, HEq p q) ∧ ∃ b, ReadsAt q.1 b w.1 := fun w => by
    obtain ⟨i, b, hi⟩ := exists_readsAt_of_pair hc w.2
    obtain ⟨i₀, h₀⟩ := exists_heq' f1 i
    obtain ⟨w₀, hw₀, h2⟩ := (h.2.2.2 _ _ h₀).2 (hi.inW1 hG w.2)
    obtain ⟨p, hp, b₀, h3⟩ := hU.2.1 w₀ hw₀
    obtain ⟨q, hq⟩ := exists_heq (α := TwPack D₀) (β := TwPack D) f2 p
    obtain ⟨v, hv, h4⟩ := hi.side hG true
    have h5 : SamePlace i true q.1 b₀ := (h.samePlace h₀ (h.fst_heq hq) _ _).1 (ReadsAt.samePlace (b := true) h2 h3)
    exact ⟨q, ⟨p, hp, hq⟩, (h5.readsAt h4).of_pair hG (hv.symm hG)⟩
  choose t ht ht' using h1
  refine (exists_sides hG t ht' fun w => ?_).elim fun sd hs => ⟨t, sd, ht, hs⟩
  obtain ⟨p, hp, h1⟩ := ht w
  obtain ⟨p', hp', h2⟩ := ht w.conj
  obtain ⟨b, hb⟩ := ht' w
  obtain ⟨b', hb'⟩ := ht' w.conj
  have h3 := hU.2.2.1 p hp p' hp' _ _ ((h.samePlace (h.fst_heq h1) (h.fst_heq h2) _ _).2 ((hb.conj hG).samePlace hb'))
  exact eq_of_heq (h2.symm.trans (h3 ▸ h1))

theorem pow_eq_one_of_mem_zpowers {R : Type} [CommRing R] {z x : Rˣ} {n : ℕ} (hz : IsPrimitiveRoot (z : R) n)
    (hx : x ∈ Subgroup.zpowers z) : x ^ n = 1 := by
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h1 : z ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hz.pow_eq_one, Units.val_one])
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]

theorem valuesIn_of_psiOk {p : TwPack D} {B : Finset (PlE D.host)} (h : BlochKatoReduction.Gen.PsiOk p.1 B p.2.1 p.2.2.1 p.2.2.2)
    (hz : ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l p.1 ^ p.2.2.1)) : ValuesIn p := by
  obtain ⟨i, Q, k, ψ⟩ := p
  obtain ⟨-, -, -, -, -, h1, -⟩ := h
  refine ⟨D.ntw.l i ^ k, pow_pos (D.ntw.lPrime i).out.pos _, hz, fun δ => ?_⟩
  obtain ⟨g, hg⟩ := D.ntw.art_surj i Q δ
  have h2 : ψ δ ∈ Subgroup.zpowers (D.ntw.zk i k) := by
    rw [← hg]
    exact h1 g
  exact pow_eq_one_of_mem_zpowers (D.ntw.zk_prim i k) h2

theorem exists_madeFrom {𝒬 : ∀ D : D7, NChoice D → IntegralHeckeForms.XD D → Prop} {N₀ : D₀.ntw.Tw → ℕ} {A : Finset ℕ}
    (hI : FirstInputs D₀ E₀ N₀) (h : TwoSteps (RebuildTied 𝒬) A D₀ E₀) :
    ∃ (D : D7) (C : NChoice D) (E : IntegralHeckeForms.XD D), 𝒬 D C E ∧ NChTie D C ∧ IsGalois ℚ ↥D.LL0 ∧ MadeFrom D₀ E₀ N₀ A D C E := by
  obtain ⟨hs, hg⟩ := firstPass_spec hI A
  obtain ⟨D₁, E₁, h1, hG, hc, hz, hR⟩ := h _ hs
  obtain ⟨t, sd, ht, hsd⟩ := h1.exists_spread hG hc hs
  obtain ⟨N, S, hN⟩ := h1.exists_good N₀ (firstPass D₀ E₀ N₀ A).1
  have hgood : GoodData ⟨E₁, N, S⟩ t sd := fun w =>
    let ⟨p, hp, h2⟩ := ht w
    ⟨(hsd w).1, (hsd w).2.1, (hsd w).2.2, hN p _ h2 (hg p hp)⟩
  obtain ⟨ψ, hψ⟩ := exists_isCharOf hG hgood fun w => by
    obtain ⟨p, hp, h2⟩ := ht w
    obtain ⟨-, -, -, f1, f2⟩ := same_basic h1.1.gal h1.1.set h1.1.frm
    refine valuesIn_of_psiOk (hgood w).2.2.2.psiOk ?_
    rw [← (f1 _ _ h2).2.2.1, ← (f2 _ _ (f1 _ _ h2).1).1]
    exact hz p hp
  obtain ⟨D, C, E, h2, h3, h4, h5, h6, h7⟩ := hR t sd ψ ht hsd hψ
  obtain ⟨e1, e2, -, -, e3⟩ := h4.basic h3.gal h3.set
  refine ⟨D, C, E, h2, h6, e2 hG, h1.trans (follows_of_sameField h3 h4 h5), fun w hw => ?_⟩
  obtain ⟨w₁, h₁⟩ := exists_heq' e1 w
  have hw₁ := (h4.tw _ _ h₁).2 hw
  obtain ⟨p, hp, h8⟩ := ht ⟨w₁, hw₁⟩
  refine ⟨⟨p, hp, h8.trans (h7 ⟨w₁, hw₁⟩ w h₁).1⟩, fun hne => ?_⟩
  rw [← (h7 ⟨w₁, hw₁⟩ w h₁).2, ← (h7 (TwPl.conj ⟨w₁, hw₁⟩) _ (e3 _ _ h₁).1).2]
  exact (hsd ⟨w₁, hw₁⟩).2.2 fun h => hne (eq_of_heq ((e3 _ _ h₁).1.symm.trans ((heq_of_eq h).trans h₁)))

def FamBuilt {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ∃ (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) (N₀ : D₀.ntw.Tw → ℕ) (A : Finset ℕ),
    FirstInputs D₀ E₀ N₀ ∧ MadeFrom D₀ E₀ N₀ A (Fm.D x i) (Fm.ex x hx i).nch (twE Fm x hx i)

theorem FamBuilt.twGood {eps : ℝ} {Fm : FamP eps} (h : FamBuilt Fm) : TwGood Fm := by
  obtain ⟨x0, h⟩ := h
  refine ⟨x0, fun x hx0 hx i => ?_⟩
  obtain ⟨D₀, E₀, N₀, A, h1, h2⟩ := h x hx0 hx i
  exact good_of_madeFrom h1 h2 (Fm.ex x hx i).nch_tie (Fm.ties x i).baseField_isGalois

def Assembles (𝒞 : FamClass) (eps x0 : ℝ) (J : ℝ → Type) (𝒬 : ∀ x, J x → ∀ D : D7, NChoice D → IntegralHeckeForms.XD D → Prop) : Prop :=
  ∀ s : ∀ x, x0 ≤ x → J x → Σ D : D7, NChoice D × IntegralHeckeForms.XD D,
    (∀ x h j, 𝒬 x j (s x h j).1 (s x h j).2.1 (s x h j).2.2 ∧ NChTie (s x h j).1 (s x h j).2.1) →
    ∃ Fm : FamP eps, 𝒞 Fm ∧ ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), ∃ h j,
      s x h j = ⟨Fm.D x i, (Fm.ex x hx i).nch, twE Fm x hx i⟩

theorem exists_famBuilt {𝒞 : FamClass} {eps x0 : ℝ} {J : ℝ → Type} {𝒬 : ∀ x, J x → ∀ D : D7, NChoice D → IntegralHeckeForms.XD D → Prop}
    (h : ∀ x, x0 ≤ x → ∀ j, ∃ (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) (N₀ : D₀.ntw.Tw → ℕ) (A : Finset ℕ),
      FirstInputs D₀ E₀ N₀ ∧ TwoSteps (RebuildTied (𝒬 x j)) A D₀ E₀) (h' : Assembles 𝒞 eps x0 J 𝒬) :
    ∃ Fm : FamP eps, 𝒞 Fm ∧ FamBuilt Fm := by
  have h1 : ∀ x, x0 ≤ x → ∀ j, ∃ s : Σ D : D7, NChoice D × IntegralHeckeForms.XD D, (𝒬 x j s.1 s.2.1 s.2.2 ∧ NChTie s.1 s.2.1) ∧
      ∃ (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) (N₀ : D₀.ntw.Tw → ℕ) (A : Finset ℕ),
        FirstInputs D₀ E₀ N₀ ∧ MadeFrom D₀ E₀ N₀ A s.1 s.2.1 s.2.2 := fun x hx j => by
    obtain ⟨D₀, E₀, N₀, A, h2, h3⟩ := h x hx j
    obtain ⟨D, C, E, h4, h5, -, h6⟩ := exists_madeFrom h2 h3
    exact ⟨⟨D, C, E⟩, ⟨h4, h5⟩, D₀, E₀, N₀, A, h2, h6⟩
  choose s hs hs' using h1
  obtain ⟨Fm, h2, x1, h3⟩ := h' s hs
  refine ⟨Fm, h2, x1, fun x hx1 hx i => ?_⟩
  obtain ⟨h4, j, h5⟩ := h3 x hx1 hx i
  have h6 := hs' x h4 j
  rw [h5] at h6
  exact h6

theorem twists_good :
    (∀ (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) (N₀ : D₀.ntw.Tw → ℕ) (A : Finset ℕ) (𝒬 : ∀ D : D7, IntegralHeckeForms.XD D → Prop),
      FirstInputs D₀ E₀ N₀ → TwoSteps (fun D₁ E₁ V => ReadElsewhere D₁ ∧ Rebuild 𝒬 D₁ E₁ V) A D₀ E₀ →
      ∃ (D : D7) (C : NChoice D) (E : IntegralHeckeForms.XD D), 𝒬 D E ∧ NChTie D C ∧ MadeFrom D₀ E₀ N₀ A D C E ∧
        TwConjAt D C ∧ ∃ N S, TwGoodAt D C ⟨E, N, S⟩) ∧
    (∀ (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) (N₀ : D₀.ntw.Tw → ℕ) (A : Finset ℕ) (𝒬 : ∀ D : D7, NChoice D → IntegralHeckeForms.XD D → Prop),
      FirstInputs D₀ E₀ N₀ → TwoSteps (RebuildTied 𝒬) A D₀ E₀ →
      ∃ (D : D7) (C : NChoice D) (E : IntegralHeckeForms.XD D), 𝒬 D C E ∧ NChTie D C ∧ MadeFrom D₀ E₀ N₀ A D C E ∧
        TwConjAt D C ∧ ∃ N S, TwGoodAt D C ⟨E, N, S⟩) ∧
    (∀ (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) (N₀ : D₀.ntw.Tw → ℕ) (A : Finset ℕ) (D : D7) (C : NChoice D) (E : IntegralHeckeForms.XD D),
      FirstInputs D₀ E₀ N₀ → MadeFrom D₀ E₀ N₀ A D C E → NChTie D C → IsGalois ℚ ↥D.LL0 →
      TwConjAt D C ∧ ∃ N S, TwGoodAt D C ⟨E, N, S⟩) ∧
    (∀ (eps : ℝ) (Fm : FamP eps), FamBuilt Fm → TwGood Fm) ∧
    (∀ 𝒞 : FamClass, Closed 𝒞 (fun Fm _ => FamBuilt Fm) → Closed 𝒞 fun Fm _ => TwGood Fm) ∧
    ∀ (𝒞 : FamClass) (eps x0 : ℝ) (J : ℝ → Type) (𝒬 : ∀ x, J x → ∀ D : D7, NChoice D → IntegralHeckeForms.XD D → Prop),
      (∀ x, x0 ≤ x → ∀ j, ∃ (D₀ : D7) (E₀ : IntegralHeckeForms.XD D₀) (N₀ : D₀.ntw.Tw → ℕ) (A : Finset ℕ),
        FirstInputs D₀ E₀ N₀ ∧ TwoSteps (RebuildTied (𝒬 x j)) A D₀ E₀) → Assembles 𝒞 eps x0 J 𝒬 →
      ∃ Fm : FamP eps, 𝒞 Fm ∧ FamBuilt Fm ∧ TwGood Fm := by
  refine ⟨fun D₀ E₀ N₀ A 𝒬 h1 h2 => ?_, fun D₀ E₀ N₀ A 𝒬 h1 h2 => ?_, fun _ _ _ _ _ _ _ => good_of_madeFrom,
    fun _ _ => FamBuilt.twGood, fun _ h => h.imp fun _ _ _ => FamBuilt.twGood, fun _ _ _ _ _ h h' => ?_⟩
  · obtain ⟨D, C, E, h3, h4, h5, h6⟩ := exists_madeFrom h1 (h2.mono fun _ _ _ h => h.2.tied h.1)
    exact ⟨D, C, E, h3, h4, h6, good_of_madeFrom h1 h6 h4 h5⟩
  · obtain ⟨D, C, E, h3, h4, h5, h6⟩ := exists_madeFrom h1 h2
    exact ⟨D, C, E, h3, h4, h6, good_of_madeFrom h1 h6 h4 h5⟩
  · obtain ⟨Fm, h1, h2⟩ := exists_famBuilt h h'
    exact ⟨Fm, h1, h2, h2.twGood⟩

end GlobalTheory.TwistChoice

end
