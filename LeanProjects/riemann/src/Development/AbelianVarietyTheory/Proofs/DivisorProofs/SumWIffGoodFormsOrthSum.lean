import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodReductionModelReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 IsGenericPsi mem_primesOf)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.SumWCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def cj (E : Type) [Field E] [StarRing E] : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)

theorem cj_coe (x : 𝓞 E) : ((cj E x : 𝓞 E) : E) = star (x : E) := rfl

theorem cj_cj (x : 𝓞 E) : cj E (cj E x) = x := RingOfIntegers.ext (star_star (x : E))

theorem coe_algMap (x : 𝓞 F) : ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = algebraMap F E (x : F) := rfl

theorem cj_algMap (hc : CMData F E) (x : 𝓞 F) : cj E (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
  RingOfIntegers.ext ((hc.fixed _).2 ⟨x, rfl⟩)

theorem exists_norm (hc : CMData F E) (y : 𝓞 E) : ∃ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) x = y * cj E y := by
  obtain ⟨a, ha⟩ := (hc.fixed ((y * cj E y : 𝓞 E) : E)).1 (by
    rw [← cj_coe, map_mul, cj_cj, mul_comm])
  have hi : IsIntegral ℤ a := by
    have h1 : IsIntegral ℤ (algebraMap F E a) := by rw [ha]; exact (y * cj E y).isIntegral_coe
    exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 h1
  exact ⟨⟨a, hi⟩, RingOfIntegers.ext ha⟩

theorem existsUnique_place (hc : CMData F E) {g : ℕ} {p : 𝓞 E} (hn : (p : E) * star (p : E) = (g : E))
    (hs : ∀ w : Pl E, p ∈ w.asIdeal → ∀ c : 𝓞 E, (c : E) = star (p : E) → c ∉ w.asIdeal)
    (v : HeightOneSpectrum (𝓞 F)) (hv : (g : 𝓞 F) ∈ v.asIdeal) :
    ∃! w : Pl E, p ∈ w.asIdeal ∧ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
  have hn' : p * cj E p = (g : 𝓞 E) := RingOfIntegers.ext (by simpa [cj_coe] using hn)
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := fun a b h =>
    RingOfIntegers.ext ((algebraMap F E).injective (by rw [← coe_algMap, ← coe_algMap, h]))
  have hle : ∀ w w' : Pl E, (p ∈ w.asIdeal ∧ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) →
      (p ∈ w'.asIdeal ∧ w'.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal) → w.asIdeal ≤ w'.asIdeal := by
    intro w w' h h'
    have key : ∀ y ∈ w.asIdeal, y ∉ w'.asIdeal → cj E y ∈ w'.asIdeal := by
      intro y hy hy'
      obtain ⟨x, hx⟩ := exists_norm hc y
      have h1 : x ∈ v.asIdeal := by
        rw [← h.2, Ideal.mem_comap, hx]; exact w.asIdeal.mul_mem_right _ hy
      rw [← h'.2, Ideal.mem_comap, hx] at h1
      exact (w'.isPrime.mem_or_mem h1).resolve_left hy'
    intro y hy
    by_contra hy'
    have h1 := key y hy hy'
    have h2 := key (y + p) (w.asIdeal.add_mem hy h.1) (fun h3 => hy' (by simpa using w'.asIdeal.sub_mem h3 h'.1))
    rw [map_add] at h2
    exact hs w' h'.1 (cj E p) (cj_coe p) (by simpa using w'.asIdeal.sub_mem h2 h1)
  have hex : ∃ w : Pl E, p ∈ w.asIdeal ∧ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
    haveI := v.isPrime
    obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) v.asIdeal ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot, map_eq_zero_iff _ hinj] at hx
      rw [hx]; exact zero_mem _)
    have hne : ∀ Q : Ideal (𝓞 E), Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal → Q ≠ ⊥ := by
      rintro Q hQ rfl
      exact v.ne_bot (by rw [← hQ, Ideal.comap_bot_of_injective _ hinj])
    have hg : p * cj E p ∈ Q := by
      rw [← hQv, Ideal.mem_comap, map_natCast] at hv
      rwa [hn']
    rcases hQ.mem_or_mem hg with h | h
    · exact ⟨⟨Q, hQ, hne Q hQv⟩, h, hQv⟩
    · have hQ' : (Q.comap (cj E)).comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal := by
        rw [← hQv]; ext x; simp only [Ideal.mem_comap, cj_algMap hc]
      exact ⟨⟨Q.comap (cj E), Ideal.comap_isPrime _ _, hne _ hQ'⟩, h, hQ'⟩
  obtain ⟨w, hw⟩ := hex
  exact ⟨w, hw, fun w' hw' => HeightOneSpectrum.ext (le_antisymm (hle _ _ hw' hw) (hle _ _ hw hw'))⟩

end Places

variable {D : D7}

theorem idx_eq {i k : Fin 2} (h : D.host.g i = D.host.g k) : i = k := by
  have := D.host.g_ne
  fin_cases i <;> fin_cases k <;> first | rfl | exact absurd h this | exact absurd h.symm this

theorem pb_ne_zero {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) (i : Fin 2) : pb i ≠ 0 := by
  intro h0
  have := h.norm i
  rw [h0] at this
  exact (h.prime i).ne_zero (by exact_mod_cast (by simpa using this.symm : ((D.host.g i : ℕ) : D.host.E) = 0))

theorem mem_typePl {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) (w : Pl D.host.E) :
    w ∈ GoodIdempotentBadPlaces.typePl pb ↔ ∃ i, pb i ∈ w.asIdeal := by
  rw [mem_primesOf]
  constructor
  · rintro ⟨-, h1⟩
    rcases w.isPrime.mem_or_mem h1 with h2 | h2
    exacts [⟨0, h2⟩, ⟨1, h2⟩]
  · rintro ⟨i, hi⟩
    refine ⟨mul_ne_zero (pb_ne_zero h 0) (pb_ne_zero h 1), ?_⟩
    fin_cases i
    exacts [w.asIdeal.mul_mem_right _ hi, w.asIdeal.mul_mem_left _ hi]

theorem exists_placeMatch {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) :
    ∃ pl : LevelCuspCharacters.Sq D.host ≃ ↥(GoodIdempotentBadPlaces.typePl pb), GoodReductionModelReading.IsPlaceMatch pl ∧
      Nonempty (∀ v : LevelCuspCharacters.Sq D.host, kP (pl v).1 ≃+* ZMod (D.host.g v.1)) := by
  have hu := fun v : LevelCuspCharacters.Sq D.host => existsUnique_place D.sp.cm (h.norm v.1) (h.split v.1) v.2.1 v.2.2
  choose w hw hw' using hu
  let f : LevelCuspCharacters.Sq D.host → ↥(GoodIdempotentBadPlaces.typePl pb) := fun v => ⟨w v, (mem_typePl h _).2 ⟨v.1, (hw v).1⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, v⟩ ⟨k, v'⟩ e
      have e' : w ⟨i, v⟩ = w ⟨k, v'⟩ := congrArg Subtype.val e
      have h1 := h.deg1 i _ (hw ⟨i, v⟩).1
      have h2 := h.deg1 k _ (hw ⟨k, v'⟩).1
      rw [e', h2] at h1
      obtain rfl := idx_eq h1
      have h3 := (hw ⟨k, v⟩).2
      rw [e', (hw ⟨k, v'⟩).2] at h3
      have : v = v' := Subtype.ext (HeightOneSpectrum.ext h3.symm)
      rw [this]
    · rintro ⟨u, hu⟩
      obtain ⟨i, hi⟩ := (mem_typePl h u).1 hu
      have hg : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal := by
        have : pb i * cj _ (pb i) = (D.host.g i : 𝓞 D.host.E) :=
          RingOfIntegers.ext (by simpa [cj_coe] using h.norm i)
        rw [← this]; exact u.asIdeal.mul_mem_right _ hi
      have hg' : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ u.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
        rwa [Ideal.mem_comap, map_natCast]
      haveI := u.isPrime
      let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨u.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)),
        Ideal.comap_isPrime _ _, fun h0 => by
          rw [h0, Ideal.mem_bot] at hg'
          exact (h.prime i).ne_zero (by exact_mod_cast hg')⟩
      exact ⟨⟨i, v, hg'⟩, Subtype.ext (hw' ⟨i, v, hg'⟩ u ⟨hi, rfl⟩).symm⟩
  refine ⟨Equiv.ofBijective f hf, fun v x y hxy => ?_,
    ⟨fun v => (GoodIdempotentBadPlaces.resIso h ⟨v.1, f v, (hw v).1⟩).symm⟩⟩
  have : y = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := RingOfIntegers.ext hxy
  rw [← (hw v).2, Ideal.mem_comap, this]
  rfl

theorem goodAt_comp {p : ℕ} [Fact p.Prime] {K : Type} [Field K] {r : ℕ} {ι κ J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ))
    (e : ι → κ) (he : Function.Surjective e) (s : κ → LevelCuspCharacters.SSParam p K r) :
    LevelCuspCharacters.GoodAt χ (fun v => s (e v)) ↔ LevelCuspCharacters.GoodAt χ s := by
  simp only [LevelCuspCharacters.GoodAt, he.forall, he.exists]

theorem coeff_centralIdem {G : Type} [Group G] [Finite G] (τ : G → ℂ) (x : G) :
    (LevelCuspCharacters.centralIdem τ).coeff x = τ 1 / (Nat.card G : ℂ) * τ x⁻¹ := by
  classical
  unfold LevelCuspCharacters.centralIdem
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem coeff_sum_centralIdem {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G'] (φ : G' ≃* G)
    {A : Set (G → ℂ)} (hA : A.Finite) {B : Set (G' → ℂ)} (hB : B.Finite) (h : B = (fun τ => τ ∘ φ) '' A) (x : G') :
    (∑ τ ∈ hA.toFinset, LevelCuspCharacters.centralIdem τ).coeff (φ x) = (∑ τ ∈ hB.toFinset, LevelCuspCharacters.centralIdem τ).coeff x := by
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply, coeff_centralIdem]
  refine Finset.sum_bij (fun τ _ => τ ∘ φ) ?_ ?_ ?_ ?_
  · intro τ hτ
    rw [Set.Finite.mem_toFinset] at hτ ⊢
    rw [h]; exact ⟨τ, hτ, rfl⟩
  · intro τ _ τ' _ e
    exact φ.surjective.injective_comp_right e
  · intro τ hτ
    rw [Set.Finite.mem_toFinset, h] at hτ
    obtain ⟨σ, hσ, rfl⟩ := hτ
    exact ⟨σ, hA.mem_toFinset.2 hσ, rfl⟩
  · intro τ _
    simp [Nat.card_congr φ.toEquiv]

section Match

variable {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) (pl : LevelCuspCharacters.Sq D.host ≃ ↥(GoodIdempotentBadPlaces.typePl pb))
  (red : ∀ v : LevelCuspCharacters.Sq D.host, kP (pl v).1 ≃+* ZMod (D.host.g v.1))

include h red in
theorem idx_of_mem (v : LevelCuspCharacters.Sq D.host) {k : Fin 2} (hk : pb k ∈ (pl v).1.asIdeal) : v.1 = k := by
  have h1 := h.deg1 k _ hk
  rw [Nat.card_congr (red v).toEquiv, Nat.card_zmod] at h1
  exact idx_eq h1

include h red in
theorem pb_mem (v : LevelCuspCharacters.Sq D.host) : pb v.1 ∈ (pl v).1.asIdeal := by
  obtain ⟨k, hk⟩ := (mem_typePl h _).1 (pl v).2
  rwa [idx_of_mem h pl red v hk]

def plEquiv (i : Fin 2) : LevelCuspCharacters.PlOver D.host i ≃ GoodIdempotentBadPlaces.PlOf pb i :=
  Equiv.ofBijective (fun v => ⟨pl ⟨i, v⟩, pb_mem h pl red ⟨i, v⟩⟩) (by
    constructor
    · intro v v' e
      have := pl.injective (congrArg Subtype.val e)
      exact eq_of_heq (Sigma.mk.inj this).2
    · rintro ⟨u, hu⟩
      obtain ⟨⟨k, v⟩, rfl⟩ := pl.surjective u
      obtain rfl : k = i := idx_of_mem h pl red ⟨k, v⟩ hu
      exact ⟨v, rfl⟩)

theorem reduction_reading_apply (x : G0 (GoodIdempotentBadPlaces.typePl pb) D.R.r) (v : LevelCuspCharacters.Sq D.host) :
    GoodReductionModelReading.readG0 pl red rfl x v = Matrix.GeneralLinearGroup.map (red v).toRingHom (x (pl v)) := by
  ext a b
  rfl

theorem compAt_eq (x : G0 (GoodIdempotentBadPlaces.typePl pb) D.R.r) (v : LevelCuspCharacters.Sq D.host) :
    GoodIdempotentBadPlaces.compAt h x ⟨v.1, plEquiv h pl red v.1 v.2⟩ = GoodReductionModelReading.readG0 pl red rfl x v := by
  have e : GoodIdempotentBadPlaces.resIso h ⟨v.1, plEquiv h pl red v.1 v.2⟩ = (red v).symm := Subsingleton.elim _ _
  rw [reduction_reading_apply, GoodIdempotentBadPlaces.compAt, e]
  rfl

def groupIso : G0 (GoodIdempotentBadPlaces.typePl pb) D.R.r ≃* LevelCuspCharacters.LevelGroup D.host :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (GoodReductionModelReading.readG0 pl red rfl) fun x y => by
      funext v; simp only [reduction_reading_apply, Pi.mul_apply, map_mul]) (by
    constructor
    · intro x y e
      funext u
      obtain ⟨v, rfl⟩ := pl.surjective u
      have := congrFun e v
      simp only [MonoidHom.mk'_apply, reduction_reading_apply] at this
      ext a b
      exact (red v).injective (congrArg (fun m : GL (Fin D.R.r) (ZMod (D.host.g v.1)) => m.1 a b) this)
    · intro y
      refine ⟨pl.piCongrLeft (fun u => GL (Fin D.R.r) (kP u.1))
        (fun v => Matrix.GeneralLinearGroup.map (red v).symm.toRingHom (y v)), ?_⟩
      funext v
      simp only [MonoidHom.mk'_apply, reduction_reading_apply, Equiv.piCongrLeft_apply_apply]
      ext a b
      exact (red v).apply_symm_apply _)

theorem tupleChar_eq (s : ∀ u : GoodIdempotentBadPlaces.PlAll pb, LevelCuspCharacters.SSParam (D.host.g u.1) ℂ D.R.r) :
    GoodIdempotentBadPlaces.tupleChar h s =
      LevelCuspCharacters.tupleChar (fun v : LevelCuspCharacters.Sq D.host => s ⟨v.1, plEquiv h pl red v.1 v.2⟩) ∘ groupIso pl red := by
  funext x
  letI := Fintype.ofFinite (GoodIdempotentBadPlaces.PlAll pb)
  letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
  symm
  refine Fintype.prod_equiv (Equiv.sigmaCongrRight (plEquiv h pl red)) _ _ fun v => ?_
  exact congrArg _ (compAt_eq h pl red x v).symm

theorem goodTypes_eq (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) :
    GoodIdempotentBadPlaces.goodTypes h om D.R.r = (fun τ => τ ∘ groupIso pl red) '' LevelCuspCharacters.goodTypes (H := D.host) om := by
  ext τ
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨_, ⟨_, fun i => ?_, rfl⟩, (tupleChar_eq h pl red s).symm⟩
    exact (goodAt_comp (p := D.host.g i) (K := ℂ) (r := D.R.r) _ _ (plEquiv h pl red i).surjective
      (fun w : GoodIdempotentBadPlaces.PlOf pb i => (s ⟨i, w⟩ : LevelCuspCharacters.SSParam (D.host.g i) ℂ D.R.r))).2 (hs i)
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨fun u => s ⟨u.1, (plEquiv h pl red u.1).symm u.2⟩, fun i => ?_, ?_⟩
    · exact (goodAt_comp (p := D.host.g i) (K := ℂ) (r := D.R.r) _ _ (plEquiv h pl red i).symm.surjective
        (fun w : LevelCuspCharacters.PlOver D.host i => (s ⟨i, w⟩ : LevelCuspCharacters.SSParam (D.host.g i) ℂ D.R.r))).2 (hs i)
    · rw [tupleChar_eq h pl red]
      congr 2
      funext v
      exact congrArg (β := LevelCuspCharacters.SSParam (D.host.g v.1) ℂ D.R.r) (fun w : LevelCuspCharacters.PlOver D.host v.1 => (s ⟨v.1, w⟩ : LevelCuspCharacters.SSParam (D.host.g v.1) ℂ D.R.r))
        ((plEquiv h pl red v.1).symm_apply_apply v.2)

theorem coeff_goodIdem (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) {n : ℕ} (hn : n = D.R.r)
    (x : G0 (GoodIdempotentBadPlaces.typePl pb) n) :
    (LevelCuspCharacters.goodIdem (H := D.host) om).coeff (GoodReductionModelReading.readG0 pl red hn x) = (GoodIdempotentBadPlaces.goodIdem h om n).coeff x := by
  subst hn
  exact coeff_sum_centralIdem (groupIso pl red) _ _ (goodTypes_eq h pl red om) x

theorem eGoodOp_eq (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) (ψ : ∀ w : Pl D.host.E, AddChar (kP w) ℂ) (j : ℕ)
    (hj : (D.sp.W j).rank = D.R.r) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)) :
    GoodReductionModelReading.eGoodOp (D.sp.W j) hj β ψ pl red om = GoodIdempotentBadPlaces.eW h om ψ j β := by
  ext F x
  simp only [GoodReductionModelReading.eGoodOp, coeff_goodIdem h, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul]
  letI := Fintype.ofFinite (G0 (GoodIdempotentBadPlaces.typePl pb) (D.sp.W j).rank)
  exact (Finsupp.sum_fintype (GoodIdempotentBadPlaces.goodIdem h om (D.sp.W j).rank).coeff
    (fun g c => c * Lev.actG0 (D.sp.W j) β (GoodIdempotentBadPlaces.levelDatumAtBasePrime (D.sp.W j) pb ψ) g F x) (fun _ => zero_mul _)).symm

end Match

theorem isBadSet_iff (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : GoodReductionModelReading.IsBadSet D Sb ↔ Sb = GoodIdempotentBadPlaces.badPl D := by
  simp only [GoodReductionModelReading.IsBadSet, Finset.ext_iff, GoodIdempotentBadPlaces.mem_badPl]

theorem exists_haar (V : HSp D) : ∃ μ : Measure (GA D V), μ.IsHaarMeasure := by
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact ⟨Measure.haar, inferInstance⟩

theorem petOrth_iff {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (T T' : MMap M) :
    GoodReductionModelReading.PetOrth M T T' ↔ ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure →
      IsFundamentalDomain (GQ V) 𝓕 μ → IsMultIP M μ 𝓕 T T' 0 :=
  ⟨fun h μ 𝓕 hμ h𝓕 => (h.2 μ hμ).2 𝓕 h𝓕, fun h => ⟨exists_haar V, fun μ hμ =>
    ⟨GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ, fun 𝓕 h𝓕 => h μ 𝓕 hμ h𝓕⟩⟩⟩

theorem conclusion_iff (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    {pb : Fin 2 → 𝓞 D.host.E} (h : IsTypeDatum D.host.g pb) (pl : LevelCuspCharacters.Sq D.host ≃ ↥(GoodIdempotentBadPlaces.typePl pb))
    (red : ∀ v : LevelCuspCharacters.Sq D.host, kP (pl v).1 ≃+* ZMod (D.host.g v.1))
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) (ψ : ∀ w : Pl D.host.E, AddChar (kP w) ℂ)
    (hm : (D.sp.W D.R.m).rank = D.R.r) (Mm : GoodReductionModelReading.ModelW D D.R.m) (βm : GL (Fin (D.sp.W D.R.m).rank) (Lev.EAf D))
    (j : ℕ) (hj : (D.sp.W j).rank = D.R.r) (M : GoodReductionModelReading.ModelW D j) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)) :
    GoodReductionModelReading.IsOrthSum (GoodReductionModelReading.PetOrth M) (GoodReductionModelReading.goodW θ j hj M β ψ pl red om)
        (GoodReductionModelReading.partW θ j hj M β ψ pl red om (GoodIdempotentBadPlaces.badPl D))
        (GoodReductionModelReading.occursW θ D.R.m hm Mm βm ψ pl red om (GoodIdempotentBadPlaces.badPl D)) ↔
      GoodIdempotentBadPlaces.IsOrthSum θ h om ψ j β M (GoodIdempotentBadPlaces.occurring θ h om ψ D.R.m βm Mm) := by
  have e1 : GoodReductionModelReading.goodW θ j hj M β ψ pl red om = GoodIdempotentBadPlaces.goodForms θ h om ψ j β M := by
    rw [GoodReductionModelReading.goodW, eGoodOp_eq h]; rfl
  have e2 : GoodReductionModelReading.partW θ j hj M β ψ pl red om (GoodIdempotentBadPlaces.badPl D) = GoodIdempotentBadPlaces.heckePart θ h om ψ j β M := by
    funext c; rw [GoodReductionModelReading.partW, eGoodOp_eq h]; rfl
  have e3 : GoodReductionModelReading.occursW θ D.R.m hm Mm βm ψ pl red om (GoodIdempotentBadPlaces.badPl D) = GoodIdempotentBadPlaces.occurring θ h om ψ D.R.m βm Mm := by
    rw [GoodReductionModelReading.occursW, eGoodOp_eq h]; rfl
  rw [e1, e2, e3]
  refine and_congr Iff.rfl (and_congr (by rw [iSup_subtype']) (and_congr Iff.rfl ?_))
  simp only [petOrth_iff]
  exact ⟨fun H μ 𝓕 hμ h𝓕 c hc c' hc' hne T hT T' hT' => H c hc c' hc' hne T hT T' hT' μ 𝓕 hμ h𝓕,
    fun H c hc c' hc' hne T hT T' hT' μ 𝓕 hμ h𝓕 => H μ 𝓕 hμ h𝓕 c hc c' hc' hne T hT T' hT'⟩

theorem sumW_iff_goodFormsOrthSum (D : D7) : GoodReductionModelReading.SumW D ↔ GoodIdempotentBadPlaces.GoodFormsOrthSum D := by
  constructor
  · intro H θ hθ pb h om hom ψ hψ βm hβm Mm j h1 h2 β hβ M
    obtain ⟨pl, hpl, ⟨red⟩⟩ := exists_placeMatch h
    have hm := D.sp.W_rank D.R.m (h1.trans h2) le_rfl
    have hj := D.sp.W_rank j h1 h2
    exact (conclusion_iff θ h pl red om ψ hm Mm βm j hj M β).1
      (H θ hθ pb _ ⟨h, rfl⟩ pl hpl red ψ hψ om hom _ ((isBadSet_iff _).2 rfl) hm Mm βm hβm j h1 h2 hj M β hβ)
  · rintro H θ hθ pb Pg ⟨h, rfl⟩ pl - red ψ hψ om hom Sb hSb hm Mm βm hβm j h1 h2 hj M β hβ
    obtain rfl := (isBadSet_iff Sb).1 hSb
    exact (conclusion_iff θ h pl red om ψ hm Mm βm j hj M β).2 (H θ hθ pb h om hom ψ hψ βm hβm Mm j h1 h2 β hβ M)

end GlobalTheory.SumWCompare
