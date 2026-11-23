import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LinearCoefficientData
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToPartFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsSemisimpleParameterGLFiniteFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeMonicPolyLabelsSemisimpleParameterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameLabelsOfGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicCharacterEqProdSuperdiagonalSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LemmaLSeriesWeightsOfGreenCuspidalParametrisatio
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TameGeneratorWindow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open Formalism.L2.DIV (Pl kP primesOf IsTypeDatum G0 IsGenericPsi mem_primesOf LevelP P0)
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.SumWCompare
open scoped TensorProduct

namespace GlobalTheory.DimPartsCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

variable {D : D7}

theorem paramGap_of_params {L : SizeData₂ D} (h : ParameterChoice' D L) : LinearCoefficientData.ParamGap D := by
  intro τ n hn
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hg : (D.R.r : ℝ) ≤ LevelStarExponents.gapS D h.Cgap := by
    have h1 : D.R.r ≤ D.R.N D.R.m * D.R.m ^ 10 := by
      have a : D.R.r ≤ D.R.N D.R.m := by
        unfold Ranks.r Ranks.N
        have : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
        omega
      exact a.trans (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
    have h2 : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 := by exact_mod_cast h1
    have h3 : 0 ≤ h.Cgap * D.R.k * (D.R.m : ℝ) ^ 4 := by have := h.Cgap_pos; positivity
    unfold LevelStarExponents.gapS
    linarith
  have key : ∀ x : ℚ, LevelStarExponents.gapS D h.Cgap < (x : ℝ) → (D.R.r : ℚ) ≤ x := fun x hx => by
    have : ((D.R.r : ℚ) : ℝ) ≤ (x : ℝ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨s1, s2, s3⟩ := h.sig_gaps τ
  have hr : n + 1 < D.R.k + D.R.m - 1 := hn
  unfold Formalism.L2.NTheta.lamAt
  by_cases h1 : n + 1 < D.R.k - 1
  · rw [dif_pos h1, dif_pos (by omega : n < D.R.k - 1)]
    have := key _ (s1 n h1)
    linarith
  · by_cases h2 : n + 1 = D.R.k - 1
    · rw [dif_neg h1, dif_pos (by omega : n < D.R.k - 1), dif_pos (by omega : n + 1 - (D.R.k - 1) < D.R.m)]
      have := key _ (s2 (by omega) (by omega))
      have e1 : (⟨n + 1 - (D.R.k - 1), by omega⟩ : Fin D.R.m) = ⟨0, by omega⟩ := Fin.ext (by simp only; omega)
      have e2 : (⟨n, by omega⟩ : Fin (D.R.k - 1)) = ⟨D.R.k - 2, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e1, e2]
      linarith
    · have P1 : n + 1 - (D.R.k - 1) < D.R.m := by omega
      have P2 : n - (D.R.k - 1) < D.R.m := by omega
      rw [dif_neg h1, dif_neg (by omega : ¬ n < D.R.k - 1), dif_pos P1, dif_pos P2]
      have := key _ (s3 (n - (D.R.k - 1)) (by omega))
      have e1 : (⟨n + 1 - (D.R.k - 1), P1⟩ : Fin D.R.m) = ⟨n - (D.R.k - 1) + 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [e1]
      linarith

theorem star_conj (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

def cPl (w : Pl D.host.E) : Pl D.host.E :=
  ⟨w.asIdeal.comap (cj D.host.E), haveI := w.isPrime; Ideal.comap_isPrime _ _, fun h0 => w.ne_bot (by
    rw [eq_bot_iff]
    intro x hx
    have : cj _ x ∈ w.asIdeal.comap (cj D.host.E) := by rwa [Ideal.mem_comap, cj_cj]
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot, ← cj_cj x, this, map_zero])⟩

theorem mem_cPl (w : Pl D.host.E) (x : 𝓞 D.host.E) : x ∈ (cPl w).asIdeal ↔ cj _ x ∈ w.asIdeal := Iff.rfl

theorem cPl_cPl (w : Pl D.host.E) : cPl (cPl w) = w := HeightOneSpectrum.ext (by ext x; rw [mem_cPl, mem_cPl, cj_cj])

theorem isConjPl_cPl (w : Pl D.host.E) : Formalism.BasicNotions.IsConjPl D.host w (cPl w) := by
  intro x y hxy
  have : y = cj _ x := RingOfIntegers.ext (hxy.trans (star_conj _).symm)
  rw [mem_cPl, this, cj_cj]

theorem plGw_ne_cPl (k : Fin 2) (v v' : D.nd.PlG k) : D.naut.plGw k v ≠ cPl (D.naut.plGw k v') := fun e =>
  D.naut.plGw_nconj k v' v (e ▸ isConjPl_cPl _)

theorem g_mem_plGw (k : Fin 2) (v : D.nd.PlG k) : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal :=
  D.naut.plGw_over k v

theorem cover (k : Fin 2) (w : Pl D.host.E) (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ∃ v, w = D.naut.plGw k v ∨ w = cPl (D.naut.plGw k v) := by
  let f : D.nd.PlG k ⊕ D.nd.PlG k → Formalism.BasicNotions.placesOver D.host.E (D.host.g k) :=
    Sum.elim (fun v => ⟨D.naut.plGw k v, g_mem_plGw k v⟩) fun v => ⟨cPl (D.naut.plGw k v), by
      show cj _ _ ∈ (D.naut.plGw k v).asIdeal
      rw [map_natCast]; exact g_mem_plGw k v⟩
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e <;> have e' := congrArg Subtype.val e
    · rw [D.naut.plGw_inj k e']
    · exact absurd e' (plGw_ne_cPl k a b)
    · exact absurd e'.symm (plGw_ne_cPl k b a)
    · have := congrArg cPl e'
      simp only [f, Sum.elim_inr, cPl_cPl] at this
      rw [D.naut.plGw_inj k this]
  have hE : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
    have h5 : D.R.f = 2 * D.R.ord := rfl
    rw [h1, h5]; ring
  have hc : Nat.card (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)) = Nat.card (D.nd.PlG k ⊕ D.nd.PlG k) := by
    rw [Nat.card_coe_set_eq, D.nd.g_split k, hE, Nat.card_sum, Nat.card_eq_fintype_card, D.nd.card_PlG k, two_mul]
  haveI : Finite (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_coe_set_eq, D.nd.g_split k]
    exact Module.finrank_pos.ne'
  obtain ⟨x, hx⟩ := ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hc.symm⟩).2 ⟨w, hw⟩
  rcases x with v | v
  · exact ⟨v, Or.inl (congrArg Subtype.val hx).symm⟩
  · exact ⟨v, Or.inr (congrArg Subtype.val hx).symm⟩

theorem place_facts (k : Fin 2) (w : Pl D.host.E) (hw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    Nat.card (kP w) = D.host.g k ∧ ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw
  refine ⟨?_, h2⟩
  rw [← h1, Ideal.absNorm_apply, Submodule.cardQuot_apply]

def PlaceTie (D : D7) : Prop :=
  ∃ pb : Fin 2 → 𝓞 D.host.E, ∀ k, (pb k : D.host.E) ∈ D.host.K ∧
    (pb k : D.host.E) * star (pb k : D.host.E) = (D.host.g k : D.host.E) ∧ ∀ v, pb k ∈ (D.naut.plGw k v).asIdeal

theorem isTypeDatum_of_norm {pb : Fin 2 → 𝓞 D.host.E}
    (hn : ∀ k, (pb k : D.host.E) * star (pb k : D.host.E) = (D.host.g k : D.host.E)) : IsTypeDatum D.host.g pb := by
  have hn' : ∀ k, pb k * cj _ (pb k) = (D.host.g k : 𝓞 D.host.E) := fun k =>
    RingOfIntegers.ext (by simpa [cj_coe] using hn k)
  have hg : ∀ k (w : Pl D.host.E), pb k ∈ w.asIdeal → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := fun k w h => by
    rw [← hn']; exact w.asIdeal.mul_mem_right _ h
  refine ⟨D.host.g_prime, D.host.g_ne, hn, fun k w h => (place_facts k w (hg k w h)).1, fun k w h h2 => ?_,
    fun k w h c hc h2 => ?_⟩
  · exact (place_facts k w (hg k w h)).2 (by rw [← hn']; exact Ideal.mul_mem_right _ _ h2)
  · have : c = cj _ (pb k) := RingOfIntegers.ext hc
    refine (place_facts k w (hg k w h)).2 ?_
    rw [← hn', pow_two, ← this]
    exact Ideal.mul_mem_mul h h2

theorem idx_eq_of_mem {i k : Fin 2} {w : Pl D.host.E} (hi : ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) : i = k :=
  idx_eq ((place_facts i w hi).1.symm.trans (place_facts k w hk).1)

def OnePrime (D : D7) : Prop :=
  ∀ k v v', (D.naut.plGw k v).under (𝓞 D.host.K) = (D.naut.plGw k v').under (𝓞 D.host.K)

def below (k : Fin 2) (v : D.nd.PlG k) : LevelCuspCharacters.PlOver D.host k :=
  ⟨(D.naut.plGw k v).under (𝓞 D.host.F), by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ (D.naut.plGw k v).asIdeal
    rw [map_natCast]; exact g_mem_plGw k v⟩

theorem under_cPl (w : Pl D.host.E) : (cPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  apply HeightOneSpectrum.ext
  ext x
  show cj _ (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ∈ w.asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ w.asIdeal
  rw [cj_algMap D.sp.cm]

theorem eq_or_of_under_eq {w w' : Pl D.host.E} (h : w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F)) :
    w = w' ∨ w = cPl w' := by
  have hsub : (w.asIdeal : Set (𝓞 D.host.E)) ⊆ w'.asIdeal ∪ (cPl w').asIdeal := by
    intro y hy
    obtain ⟨x, hx⟩ := exists_norm D.sp.cm y
    have h1 : x ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ w.asIdeal
      rw [hx]; exact Ideal.mul_mem_right _ _ hy
    rw [h] at h1
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ w'.asIdeal := h1
    rw [hx] at h2
    exact w'.isPrime.mem_or_mem h2
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h1))
  · exact Or.inr (HeightOneSpectrum.ext (w.isMaximal.eq_of_le (cPl w').isPrime.ne_top h1))

theorem below_bijective (k : Fin 2) : Function.Bijective (below (D := D) k) := by
  constructor
  · intro v v' e
    rcases eq_or_of_under_eq (congrArg Subtype.val e) with h | h
    · exact D.naut.plGw_inj k h
    · exact absurd h (plGw_ne_cPl k v v')
  · rintro ⟨u, hu⟩
    have hu1 := u.isPrime
    obtain ⟨⟨W, hW, hWv⟩⟩ := (inferInstance : Nonempty (u.asIdeal.primesOver (𝓞 D.host.E)))
    let w : Pl D.host.E := ⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot u.ne_bot W⟩
    have hwv : w.under (𝓞 D.host.F) = u := HeightOneSpectrum.ext hWv.over.symm
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← hwv] at hu
      have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal := hu
      rwa [map_natCast] at h1
    obtain ⟨v, h | h⟩ := cover k w hg
    · exact ⟨v, Subtype.ext (show (D.naut.plGw k v).under (𝓞 D.host.F) = u by rw [← h, hwv])⟩
    · exact ⟨v, Subtype.ext (show (D.naut.plGw k v).under (𝓞 D.host.F) = u by rw [← under_cPl, ← h, hwv])⟩

def sqEquiv (D : D7) : (Σ k : Fin 2, D.nd.PlG k) ≃ LevelCuspCharacters.Sq D.host :=
  Equiv.sigmaCongrRight fun k => Equiv.ofBijective _ (below_bijective k)

theorem sq_ext {a a' : LevelCuspCharacters.Sq D.host} (h : a.2.1 = a'.2.1) : a = a' := by
  obtain ⟨kv, rfl⟩ := (sqEquiv D).surjective a
  obtain ⟨i, u⟩ := a'
  obtain ⟨k, v⟩ := kv
  have h1 : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ ((D.naut.plGw k v).under (𝓞 D.host.F)).asIdeal := by
    have : (D.naut.plGw k v).under (𝓞 D.host.F) = u.1 := h
    rw [this]; exact u.2
  have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ (D.naut.plGw k v).asIdeal := h1
  rw [map_natCast] at h2
  obtain rfl := idx_eq_of_mem h2 (g_mem_plGw k v)
  exact congrArg (Sigma.mk i) (Subtype.ext h)

section Match

variable {Pg : Finset (Pl D.host.E)} (h : LinearCoefficientData.IsRecPlaces D Pg)

def idxEquiv : Pg ≃ (Σ k : Fin 2, D.nd.PlG k) where
  toFun := LinearCoefficientData.idx h
  invFun kv := ⟨D.naut.plGw kv.1 kv.2, (h _).2 ⟨kv, rfl⟩⟩
  left_inv PP := Subtype.ext (LinearCoefficientData.idx_spec h PP)
  right_inv kv := LinearCoefficientData.idx_eq h _ kv rfl

theorem isBelow_iff (b : Pg ≃ LevelCuspCharacters.Sq D.host) : BadPlacesGoodCoefficients.IsBelow b ↔ b = (idxEquiv h).trans (sqEquiv D) := by
  have key : ∀ PP : Pg, (((idxEquiv h).trans (sqEquiv D)) PP).2.1.asIdeal =
      PP.1.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := fun PP => by
    conv_rhs => rw [← LinearCoefficientData.idx_spec h PP]
    rfl
  exact ⟨fun hb => Equiv.ext fun PP => sq_ext (HeightOneSpectrum.ext ((hb PP).trans (key PP).symm)), fun e => e ▸ key⟩

include h in

theorem exists_match : ∃ b : Pg ≃ LevelCuspCharacters.Sq D.host, BadPlacesGoodCoefficients.IsBelow b ∧
    Nonempty (∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* kP PP.1) := by
  refine ⟨_, (isBelow_iff h _).2 rfl, ⟨fun PP => ?_⟩⟩
  haveI := Fintype.ofFinite (kP PP.1)
  exact ZMod.ringEquivOfPrime _ (D.host.g_prime _) (by
    rw [← Nat.card_eq_fintype_card]; exact (place_facts _ _ (LinearCoefficientData.idx_mem h PP)).1)

end Match

def pull (x : LevelCuspCharacters.LevelGroup D.host) : G0g D.nd := fun kv => x ⟨kv.1, below kv.1 kv.2⟩

theorem pull_bijective : Function.Bijective (pull (D := D)) :=
  (Equiv.piCongrLeft (fun v : LevelCuspCharacters.Sq D.host => GL (Fin D.R.r) (ZMod (D.host.g v.1))) (sqEquiv D)).symm.bijective

def IdemTie (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : Prop :=
  ∀ x, D.ntypes.e0.coeff (pull x) = (LevelCuspCharacters.goodIdem (H := D.host) om).coeff x

section Idem

variable {Pg : Finset (Pl D.host.E)} (h : LinearCoefficientData.IsRecPlaces D Pg) {b : Pg ≃ LevelCuspCharacters.Sq D.host} (hb : BadPlacesGoodCoefficients.IsBelow b)
  (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* kP PP.1)

end Idem

theorem isFrameOf_of_atG {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} (h : BadPlacesGoodCoefficients.IsFrameAtG V β) : LinearCoefficientData.IsFrameOf V β :=
  let ⟨Λ, _, h⟩ := h; ⟨Λ, _, h⟩

theorem sphOff {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} (hβ : BadPlacesGoodCoefficients.IsFrameAtG V β) (hr : V.rank = D.R.r)
    {Pg : Finset (Pl D.host.E)} (h : ∀ PP ∈ Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (P : LevelP Pg D.R.r ℂ) (fr : Lev.Frm) :
    SphOff (Lev.levG V β (LinearCoefficientData.datR V hr Pg P fr) : Set (GA D V)) (Lev.levChi V β (LinearCoefficientData.datR V hr Pg P fr))
      (BadPlacesGoodCoefficients.badPlaces D) := by
  intro w hw
  obtain ⟨Λ, c, hΛ⟩ := hβ
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro hm
    obtain ⟨x, hx, hx'⟩ := hw (w.under (𝓞 D.host.F)) ((BadPlacesGoodCoefficients.mem_badPlaces _).2 (by
      show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ w.asIdeal
      rwa [map_natCast]))
    exact hx' (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) rfl hx
  have hk : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro k hk
    apply hg
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk
    · exact Ideal.mul_mem_left _ _ hk
  obtain ⟨e, f, hef⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 w
  have := (GlobalTheory.LevSplit.lev_split V β Λ _ (LinearCoefficientData.datR V hr Pg P fr) hΛ).2 w e f hef
    (by rw [Nat.cast_pow]; exact fun hm => hg (w.isPrime.mem_of_pow_mem _ hm)) (by
      rintro PP (hP | hP)
      · obtain ⟨k, hkP⟩ := h PP hP
        refine ⟨fun e => hk k (e ▸ hkP), fun hc => ?_⟩
        obtain ⟨c', hc', e'⟩ := hc _ hkP
        have : c' = ((D.host.g k : ℕ) : 𝓞 D.host.E) := RingOfIntegers.ext (by simpa using e')
        exact hk k (this ▸ hc')
      · exact absurd hP (Finset.notMem_empty _))
  exact ⟨e, f, hef, this.1, this.2.1⟩

section Parts

variable {Pg : Finset (Pl D.host.E)} (h : LinearCoefficientData.IsRecPlaces D Pg) (θ : LinearCoefficientData.InfFam D) (P : LevelP Pg D.R.r ℂ)
  (c : LinearCoefficientData.Eig D)

end Parts

theorem rank_eq_iff {X : Type} [AddCommGroup X] [Module ℂ X] (d : ℕ) :
    Module.rank ℂ X = d ↔ FiniteDimensional ℂ X ∧ Module.finrank ℂ X = d := by
  constructor
  · intro h
    exact ⟨Module.finite_of_rank_eq_nat h, Module.finrank_eq_of_rank_eq h⟩
  · rintro ⟨h, rfl⟩
    exact (Module.finrank_eq_rank ℂ X).symm

section Level

variable {Pg : Finset (Pl D.host.E)}

def FirstAtBad (h : LinearCoefficientData.IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ) : Prop :=
  ∀ (θ : LinearCoefficientData.InfFam D), IsInfFam θ →
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M₀ : DSModel (D.sp.Y 0) (parB (tparRec D) 0))
    (M₁ : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j))))
    (β₀ : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (β₁ : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    BadPlacesGoodCoefficients.IsFrameAtG (D.sp.Y 0) β₀ → BadPlacesGoodCoefficients.IsFrameAtG (D.sp.W j) β₁ →
  ∀ c : LinearCoefficientData.Eig D,
    FiniteDimensional ℂ (LinearCoefficientData.EEc θ M₀ h β₀ P (BadPlacesGoodCoefficients.badPlaces D) c) ∧
      FiniteDimensional ℂ (LinearCoefficientData.Wc θ j h1 h2 M₁ h β₁ P (BadPlacesGoodCoefficients.badPlaces D) c) ∧
      Module.finrank ℂ (LinearCoefficientData.Wc θ j h1 h2 M₁ h β₁ P (BadPlacesGoodCoefficients.badPlaces D) c) =
        Module.finrank ℂ (LinearCoefficientData.EEc θ M₀ h β₀ P (BadPlacesGoodCoefficients.badPlaces D) c)

def RowsFinite (h : LinearCoefficientData.IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ) : Prop :=
  ∀ (θ : LinearCoefficientData.InfFam D), IsInfFam θ → ∀ (M₀ : DSModel (D.sp.Y 0) (parB (tparRec D) 0))
    (β₀ : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)), BadPlacesGoodCoefficients.IsFrameAtG (D.sp.Y 0) β₀ →
    ∀ c : LinearCoefficientData.Eig D, FiniteDimensional ℂ (LinearCoefficientData.EEc θ M₀ h β₀ P (BadPlacesGoodCoefficients.badPlaces D) c)

def HasLift (D : D7) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ Nonempty (DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) ∧
    ∃ β, BadPlacesGoodCoefficients.IsFrameAtG (D.sp.W j) β

def SecondAt (D : D7) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) (e : G0 Pg D.R.r →₀ ℂ) : Prop :=
  ∀ (θ : LinearCoefficientData.InfFam D), IsInfFam θ → ∀ (M₀ : DSModel (D.sp.Y 0) (parB (tparRec D) 0))
    (β₀ : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)), BadPlacesGoodCoefficients.IsFrameAtG (D.sp.Y 0) β₀ →
  ∀ c : LinearCoefficientData.Eig D, ∃ d : ℕ, Module.rank ℂ (BadPlacesGoodCoefficients.rowPart θ M₀ β₀ P e c) = d ∧
    ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
      (M : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
      BadPlacesGoodCoefficients.IsFrameAtG (D.sp.W j) β → Module.rank ℂ (BadPlacesGoodCoefficients.formPart θ h1 h2 M β P e c) = d

variable (h : LinearCoefficientData.IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ)

end Level

def FirstRec (D : D7) : Prop :=
  ∀ (Pg : Finset (Pl D.host.E)) (h : LinearCoefficientData.IsRecPlaces D Pg) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ),
    IsGenericPsi Pg ψ → FirstAtBad h (P0 Pg D.R.r ψ)

def SecondRec (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : Prop :=
  ∀ (Pg : Finset (Pl D.host.E)), LinearCoefficientData.IsRecPlaces D Pg →
    ∀ (b : Pg ≃ LevelCuspCharacters.Sq D.host), BadPlacesGoodCoefficients.IsBelow b → ∀ (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* kP PP.1)
      (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi Pg ψ →
      SecondAt D Pg (P0 Pg D.R.r ψ) (BadPlacesGoodCoefficients.goodCoeff b φ om)

section Above

variable {Pg : Finset (Pl D.host.E)}

def eVia (a : Pg ≃ (Σ k : Fin 2, D.nd.PlG k)) (φ : ∀ PP : Pg, ZMod (D.host.g (a PP).1) →+* kP PP.1) : G0 Pg D.R.r →₀ ℂ :=
  Finsupp.mapDomain (fun (γ : G0g D.nd) (PP : Pg) => Matrix.GeneralLinearGroup.map (φ PP) (γ (a PP))) D.ntypes.e0.coeff

def FirstAt (D : D7) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) (e : G0 Pg D.R.r →₀ ℂ) : Prop :=
  ∀ (θ : LinearCoefficientData.InfFam D), IsInfFam θ →
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M₀ : DSModel (D.sp.Y 0) (parB (tparRec D) 0))
    (M₁ : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j))))
    (β₀ : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (β₁ : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    LinearCoefficientData.IsFrameOf (D.sp.Y 0) β₀ → LinearCoefficientData.IsFrameOf (D.sp.W j) β₁ →
  ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    SphOff (Lev.levG (D.sp.Y 0) β₀ (LinearCoefficientData.datE D Pg P) : Set (GA D (D.sp.Y 0)))
      (Lev.levChi (D.sp.Y 0) β₀ (LinearCoefficientData.datE D Pg P)) S →
    SphOff (Lev.levG (D.sp.W j) β₁ (LinearCoefficientData.datWj D j h1 h2 Pg P) : Set (GA D (D.sp.W j)))
      (Lev.levChi (D.sp.W j) β₁ (LinearCoefficientData.datWj D j h1 h2 Pg P)) S →
  ∀ c : LinearCoefficientData.Eig D, ∃ d : ℕ,
    Module.rank ℂ (EEpart θ M₀ (Lev.levG (D.sp.Y 0) β₀ (LinearCoefficientData.datE D Pg P)) (Lev.levChi (D.sp.Y 0) β₀ (LinearCoefficientData.datE D Pg P))
      (LinearCoefficientData.eLin (D.sp.Y 0) β₀ (LinearCoefficientData.datE D Pg P) e) S c) = d ∧
    Module.rank ℂ (Wpart θ j M₁ (Lev.levG (D.sp.W j) β₁ (LinearCoefficientData.datWj D j h1 h2 Pg P))
      (Lev.levChi (D.sp.W j) β₁ (LinearCoefficientData.datWj D j h1 h2 Pg P))
      (LinearCoefficientData.eLin (D.sp.W j) β₁ (LinearCoefficientData.datWj D j h1 h2 Pg P) e) S c) = d

theorem dimPartsAt_iff (h : LinearCoefficientData.IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ) :
    LinearCoefficientData.DimPartsAt h P ↔ FirstAt D Pg P (LinearCoefficientData.eCoef h) := by
  constructor
  · intro H θ hθ j h1 h2 M₀ M₁ β₀ β₁ a b S s t c
    obtain ⟨x, y, z⟩ := H θ hθ j h1 h2 M₀ M₁ β₀ β₁ a b S s t c
    exact ⟨_, (rank_eq_iff _).2 ⟨x, rfl⟩, (rank_eq_iff _).2 ⟨y, z⟩⟩
  · intro H θ hθ j h1 h2 M₀ M₁ β₀ β₁ a b S s t c
    obtain ⟨d, x, y⟩ := H θ hθ j h1 h2 M₀ M₁ β₀ β₁ a b S s t c
    obtain ⟨x1, x2⟩ := (rank_eq_iff _).1 x
    obtain ⟨y1, y2⟩ := (rank_eq_iff _).1 y
    exact ⟨x1, y1, y2.trans x2.symm⟩

def DimPartsAny : Prop :=
  ∀ D : D7, LinearCoefficientData.ParamGap D → GlobalTheory.GLq.ESerTie D →
    ∀ (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Lev.IsConjPl PP PP') →
    ∀ (a : Pg ≃ (Σ k : Fin 2, D.nd.PlG k)) (φ : ∀ PP : Pg, ZMod (D.host.g (a PP).1) →+* kP PP.1)
      (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi Pg ψ → FirstAt D Pg (P0 Pg D.R.r ψ) (eVia a φ)

theorem eq_cPl_of_isConjPl {w w' : Pl D.host.E} (h : Lev.IsConjPl w w') : w = cPl w' := by
  refine HeightOneSpectrum.ext (w.isMaximal.eq_of_le (cPl w').isPrime.ne_top fun c hc => ?_)
  obtain ⟨c', hc', e⟩ := h c hc
  have : c' = cj _ c := RingOfIntegers.ext e
  rwa [mem_cPl, ← this]

theorem DimPartsAny.first (H : DimPartsAny) : LinearCoefficientData.DimParts := by
  intro D h1 h2 Pg h ψ hψ
  refine (dimPartsAt_iff h _).2 (H D h1 h2 Pg ?_ (idxEquiv h) _ ψ hψ)
  intro PP hP PP' hP' hc
  obtain ⟨⟨k, v⟩, rfl⟩ := (h PP).1 hP
  obtain ⟨⟨k', v'⟩, rfl⟩ := (h PP').1 hP'
  have e := eq_cPl_of_isConjPl hc
  have hg : ((D.host.g k' : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := by
    rw [e, mem_cPl, map_natCast]; exact g_mem_plGw k' v'
  obtain rfl := idx_eq_of_mem hg (g_mem_plGw k v)
  exact plGw_ne_cPl _ v v' e

theorem eVia_eq {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (b : Pg ≃ LevelCuspCharacters.Sq D.host)
    (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* kP PP.1) :
    eVia (b.trans (sqEquiv D).symm) (fun PP => (φ PP).toRingHom) = BadPlacesGoodCoefficients.goodCoeff b φ om := by
  have e0 : D.ntypes.e0.coeff = Finsupp.mapDomain pull (LevelCuspCharacters.goodIdem (H := D.host) om).coeff := by
    rw [Finsupp.ext_iff, pull_bijective.2.forall]
    simp only [Finsupp.mapDomain_apply pull_bijective.1]
    exact hI
  unfold eVia BadPlacesGoodCoefficients.goodCoeff
  rw [e0, ← Finsupp.mapDomain_comp]
  congr 1
  funext x PP
  refine congrArg (Matrix.GeneralLinearGroup.map (φ PP).toRingHom) ?_
  exact congrArg (β := GL (Fin D.R.r) (ZMod (D.host.g (b PP).1)))
    (fun w : LevelCuspCharacters.PlOver D.host (b PP).1 => x ⟨(b PP).1, w⟩)
    ((Equiv.ofBijective _ (below_bijective (b PP).1)).apply_symm_apply (b PP).2)

theorem DimPartsAny.second (H : DimPartsAny) {L : SizeData₂ D} (hP : ParameterChoice' D L) (hE : GlobalTheory.GLq.ESerTie D) (hL : HasLift D)
    {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (hPg : BadPlacesGoodCoefficients.IsReadingPlaces D Pg)
    (b : Pg ≃ LevelCuspCharacters.Sq D.host) (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* kP PP.1)
    (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (hψ : IsGenericPsi Pg ψ) :
    SecondAt D Pg (P0 Pg D.R.r ψ) (BadPlacesGoodCoefficients.goodCoeff b φ om) := by
  obtain ⟨pb, -, hT, rfl⟩ := hPg
  have hg : ∀ k (w : Pl D.host.E), pb k ∈ w.asIdeal → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := fun k w h => by
    have : pb k * cj _ (pb k) = (D.host.g k : 𝓞 D.host.E) := RingOfIntegers.ext (by simpa [cj_coe] using hT.norm k)
    rw [← this]; exact Ideal.mul_mem_right _ _ h
  have hover : ∀ PP ∈ primesOf (pb 0 * pb 1), ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP h =>
    ((mem_typePl hT PP).1 h).imp fun k hk => hg k PP hk
  have key := H D (paramGap_of_params hP) hE _ (by
    intro PP h PP' h' hc
    obtain ⟨k, hk⟩ := (mem_typePl hT PP).1 h
    obtain ⟨k', hk'⟩ := (mem_typePl hT PP').1 h'
    have e := eq_cPl_of_isConjPl hc
    have h3 : ((D.host.g k' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [e, mem_cPl, map_natCast]; exact hg k' PP' hk'
    obtain rfl := idx_eq_of_mem h3 (hg k PP hk)
    rw [e, mem_cPl] at hk
    exact hT.split _ PP' hk' _ (cj_coe _) hk) (b.trans (sqEquiv D).symm) (fun PP => (φ PP).toRingHom) ψ hψ
  rw [eVia_eq hI] at key
  intro θ hθ M₀ β₀ hβ₀ c
  have k2 := fun j h1 h2 M β (hβ : BadPlacesGoodCoefficients.IsFrameAtG (D.sp.W j) β) =>
    key θ hθ j h1 h2 M₀ M β₀ β (isFrameOf_of_atG hβ₀) (isFrameOf_of_atG hβ) _
      (sphOff hβ₀ _ hover _ _) (sphOff hβ _ hover _ _) c
  obtain ⟨j, h1, h2, ⟨M⟩, β, hβ⟩ := hL
  obtain ⟨d, hd, -⟩ := k2 j h1 h2 M β hβ
  refine ⟨d, hd, fun j h1 h2 M β hβ => ?_⟩
  obtain ⟨d', x, y⟩ := k2 j h1 h2 M β hβ
  exact y.trans (x.symm.trans hd)

end Above

def TameTie (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : Prop :=
  ∀ k : Fin 2, ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k ∧
    (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
    ∀ v j, ∃ χ, (χ = LevelCuspCharacters.chiTame (H := D.host) om k j ∨ χ = (LevelCuspCharacters.chiTame (H := D.host) om k j)⁻¹) ∧
      ∀ a : (ZMod (D.host.g k))ˣ,
        GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod (D.host.g k)) _ (D.nd.chiT k v j : ZMod (D.host.g k)))
          (algebraMap (ZMod (D.host.g k)) _ (a : ZMod (D.host.g k))) = ((χ a : ℂˣ) : ℂ)

theorem TameTie.eSerTie {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (h : TameTie D om) : GlobalTheory.GLq.ESerTie D :=
  fun k => let ⟨L, h1, h2, _⟩ := h k; ⟨L, h1, h2⟩

section Comparison₂

open GlobalTheory.ParamLabel GlobalTheory.GLq

theorem irr_one_ne_zero {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsIrr χ) : χ 1 ≠ 0 := by
  intro h0
  have h1 := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central G χ χ h h).2.2
  obtain ⟨V, -, hV⟩ := h
  have h2 : Module.finrank ℂ V = 0 := by
    have := hV 1
    rw [FDRep.char_one, h0] at this
    exact_mod_cast this
  haveI : Subsingleton V := Module.finrank_zero_iff.1 h2
  have h3 : ∀ x, χ x = 0 := fun x => by
    rw [← hV, FDRep.character, Subsingleton.elim (V.ρ x) 0, map_zero]
  simp [ip, h3] at h1

theorem eq_of_prod_eq {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    {χ χ' : ∀ i, G i → ℂ} (h : ∀ i, IsIrr (χ i)) (h' : ∀ i, IsIrr (χ' i))
    (e : ∀ a : ∀ i, G i, ∏ i, χ i (a i) = ∏ i, χ' i (a i)) (i : ι) : χ i = χ' i := by
  classical
  have key : ∀ (χ : ∀ i, G i → ℂ) (y : G i), ∏ k, χ k (Pi.mulSingle (M := G) i y k) = χ i y * ∏ k ∈ Finset.univ.erase i, χ k 1 := by
    intro χ y
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Pi.mulSingle_eq_same]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hk)]
  by_contra hne
  have h1 := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ _ _ (h i) (h i)).2.2
  have h2 := (GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central _ _ _ (h i) (h' i)).2.2
  rw [if_pos rfl] at h1
  rw [if_neg hne] at h2
  have h3 : ip (χ i) (χ i) * ∏ k ∈ Finset.univ.erase i, χ k 1 = ip (χ i) (χ' i) * ∏ k ∈ Finset.univ.erase i, χ' k 1 := by
    simp only [ip, mul_assoc, Finset.sum_mul, ← key, e]
  rw [h1, h2, one_mul, zero_mul] at h3
  exact Finset.prod_ne_zero_iff.2 (fun k _ => irr_one_ne_zero (h k)) h3

def Rel (L : ∀ k, LabelDatum (D.host.g k)) (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1))
    (s : ∀ v : LevelCuspCharacters.Sq D.host, LevelCuspCharacters.SSParam (D.host.g v.1) ℂ D.R.r) : Prop :=
  ∀ k v, ∃ x, Labels (L k) (s ⟨k, below k v⟩) x (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))

theorem TameTie.idemTie (hG : Green) {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hT : TameTie D om) : IdemTie D om := by
  classical
  choose L _ hE hχ using hT
  have h5 := five_le_typePrime D
  have good : ∀ a s, Rel L a s →
      (D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔ LevelCuspCharacters.IsGoodParam om s) := by
    intro a s h
    refine forall_congr' fun k => ?_
    choose x hx using h k
    rw [← goodAt_comp _ (below k) (below_bijective k).2]
    refine (good_iff (L k) (h5 k) _ x _ hx _ (D.nd.chiT k) fun v j => ?_).symm
    obtain ⟨χ, rfl | rfl, h⟩ := hχ k v j
    exacts [Or.inl h, Or.inr h]
  have ser : ∀ a s, Rel L a s → D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) → ∀ k v,
      {χ | IsIrr χ ∧ HasLabel (L k) χ (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))} = {LevelCuspCharacters.typeChar (s ⟨k, below k v⟩)} ∧
      eSerC (L k) D.R.r (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) = LevelCuspCharacters.centralIdem (LevelCuspCharacters.typeChar (s ⟨k, below k v⟩)) := by
    intro a s h hg k v
    obtain ⟨x, hx⟩ := h k v
    exact hx.series hG (h5 k) ((hg k).1.2.1 v)
  have mem : ∀ a s, Rel L a s → D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) → ∀ k v,
      IsIrr (LevelCuspCharacters.typeChar (s ⟨k, below k v⟩)) ∧
        HasLabel (L k) (LevelCuspCharacters.typeChar (s ⟨k, below k v⟩)) (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := fun a s h hg k v =>
    ((Set.ext_iff.1 (ser a s h hg k v).1) _).2 rfl
  have exa : ∀ s, ∃ a, Rel L a s := by
    intro s
    choose x f hf using fun kv : (Σ k : Fin 2, D.nd.PlG k) => GlobalTheory.T.exists_labels_semisimple_parameter_GL_finiteField _ (L kv.1) _ (s ⟨kv.1, below kv.1 kv.2⟩)
    refine ⟨fun kv i => (f kv).coeff i, fun k v => ⟨x ⟨k, v⟩, ?_⟩⟩
    rw [Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ (hf ⟨k, v⟩).2.2.1 (GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization _ _ _ _ _ (hf ⟨k, v⟩).2).1]
    exact hf ⟨k, v⟩
  have exs : ∀ a, D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) → ∃ s, Rel L a s := by
    intro a hg
    choose s hs using fun k v => GlobalTheory.T.squarefree_monic_poly_labels_semisimple_parameter _ (L k) _ _ ((hg k).1.1 v).1 ((hg k).1.1 v).2.1 ((hg k).1.1 v).2.2 ((hg k).1.2.1 v)
    refine ⟨fun w => s w.1 ((Equiv.ofBijective _ (below_bijective w.1)).symm w.2), fun k v => ?_⟩
    have : (Equiv.ofBijective _ (below_bijective k)).symm (below k v) = v :=
      (Equiv.ofBijective _ (below_bijective k)).symm_apply_apply v
    have e : ∀ v', v' = v → ∃ x, Labels (L k) (s k v') x (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := fun v' e => e ▸ hs k v
    exact e _ this
  choose S hS using exs
  have tup : ∀ s y, LevelCuspCharacters.tupleChar (H := D.host) (K := ℂ) s y =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), LevelCuspCharacters.typeChar (s ⟨kv.1, below kv.1 kv.2⟩) (pull y kv) := fun s y => by
    letI := Fintype.ofFinite (LevelCuspCharacters.Sq D.host)
    exact (Fintype.prod_equiv (sqEquiv D) _ _ fun kv => rfl).symm
  intro y
  show (∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), (Fin D.R.r → ZMod (D.host.g kv.1))),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (pull y kv) else 0) = _
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter]
  simp only [LevelCuspCharacters.goodIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_bij (fun a ha => LevelCuspCharacters.tupleChar (S a (Finset.mem_filter.1 ha).2)) (fun a ha => ?_)
    (fun a ha a' ha' e => ?_) (fun τ hτ => ?_) (fun a ha => ?_)
  · exact (Set.Finite.mem_toFinset _).2 ⟨_, (good a _ (hS a _)).1 (Finset.mem_filter.1 ha).2, rfl⟩
  · have m := mem a _ (hS a (Finset.mem_filter.1 ha).2) (Finset.mem_filter.1 ha).2
    have m' := mem a' _ (hS a' (Finset.mem_filter.1 ha').2) (Finset.mem_filter.1 ha').2
    funext kv
    have e1 := eq_of_prod_eq (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (m kv.1 kv.2).1) (fun kv => (m' kv.1 kv.2).1)
      (fun z => by
        obtain ⟨y, rfl⟩ := pull_bijective.2 z
        rw [← tup, ← tup, e]) kv
    have e2 := Label.label_unique (L kv.1) (h5 _) _ (m kv.1 kv.2).1 _ _ (m kv.1 kv.2).2 (e1 ▸ (m' kv.1 kv.2).2)
    funext i
    rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt (a kv) i, ← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt (a' kv) i]
    exact congrArg (Polynomial.coeff · i) e2
  · obtain ⟨s, hs, rfl⟩ := (Set.Finite.mem_toFinset _).1 hτ
    obtain ⟨a, ha⟩ := exa s
    have hg := (good a s ha).2 hs
    refine ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩, funext fun z => ?_⟩
    rw [tup, tup]
    refine Finset.prod_congr rfl fun kv _ => congrFun (Set.singleton_injective ?_) _
    rw [← (ser a _ (hS a hg) hg kv.1 kv.2).1, ← (ser a _ ha hg kv.1 kv.2).1]
  · have hg := (Finset.mem_filter.1 ha).2
    have hc : (Nat.card (LevelCuspCharacters.LevelGroup D.host) : ℂ) =
        ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (Nat.card (Gn (D.host.g kv.1) D.R.r) : ℂ) := by
      rw [Nat.card_eq_of_bijective _ pull_bijective, Nat.card_pi, Nat.cast_prod]
    rw [coeff_centralIdem, tup, tup, hc, ← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [hE, (ser a _ (hS a hg) hg kv.1 kv.2).2, coeff_centralIdem]
    rfl

end Comparison₂

section Move

open GlobalTheory.PartsOccurProof Formalism.IndefR.Lev Formalism.L2.DIV

variable {Pg Pg' : Finset (Pl D.host.E)} (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg)
  (red : ∀ v : LevelCuspCharacters.Sq D.host, kP (pl v).1 ≃+* ZMod (D.host.g v.1))
  (φ₁ : ∀ PP : ↥Pg, ZMod (D.host.g (pl.symm PP).1) ≃+* kP PP.1) (b : ↥Pg' ≃ LevelCuspCharacters.Sq D.host)
  (φ : ∀ PP : ↥Pg', ZMod (D.host.g (b PP).1) ≃+* kP PP.1) (S : Set (LevelCuspCharacters.Sq D.host))

end Move

def UniformTame (D : D7) : Prop :=
  ∀ k : Fin 2, ∃ γ : (ZMod (D.host.g k))ˣ, Subgroup.zpowers γ = ⊤ ∧
    ∀ v (j : Fin D.R.m), D.nd.chiT k v j = γ ^ (2 * (j.1 + 1)) ∨ D.nd.chiT k v j = (γ ^ (2 * (j.1 + 1)))⁻¹

theorem tameTie_of_typesTrue {P : Formalism.L2.Host.PiBar D.host} {W : Formalism.L2.Host.Omg D.host}
    (h : GlobalTheory.Mem.Top.TypesTrue D.ntypes P W) :
    LevelCuspCharacters.IsGeneratorFamily (H := D.host) W.om ∧ TameTie D W.om ∧ OnePrime D :=
  ⟨W.gen, fun k => ⟨_, (h.teich k).symm, h.ser k, fun v j =>
    ⟨_, Or.inl rfl, fun a => GlobalTheory.Mem.TypePl.thetaOf_of_isCharLab _ (h.isCharLab k v j) a⟩⟩,
    fun k v v' => (h.pl k v).trans (h.pl k v').symm⟩

def SecondAll (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : Prop :=
  ∀ (Pg : Finset (Pl D.host.E)), BadPlacesGoodCoefficients.IsReadingPlaces D Pg →
    ∀ (b : Pg ≃ LevelCuspCharacters.Sq D.host), BadPlacesGoodCoefficients.IsBelow b → ∀ (φ : ∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* kP PP.1)
      (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi Pg ψ →
      SecondAt D Pg (P0 Pg D.R.r ψ) (BadPlacesGoodCoefficients.goodCoeff b φ om)

theorem exists_reading {L : SizeData₂ D} (hP : ParameterChoice' D L) : ∃ Pg, BadPlacesGoodCoefficients.IsReadingPlaces D Pg ∧
    ∃ b : Pg ≃ LevelCuspCharacters.Sq D.host, BadPlacesGoodCoefficients.IsBelow b ∧ Nonempty (∀ PP : Pg, ZMod (D.host.g (b PP).1) ≃+* kP PP.1) := by
  choose π hK hN using hP.g_norm
  have hπ : IsTypeDatum D.host.g π := isTypeDatum_of_norm fun k => by rw [star_conj]; exact hN k
  obtain ⟨pl, hpl, ⟨red⟩⟩ := exists_placeMatch hπ
  refine ⟨_, ⟨π, hK, hπ, rfl⟩, pl.symm, fun PP => ?_, Classical.nonempty_pi.2 fun PP => ?_⟩
  · rw [← GlobalTheory.PartsOccurProof.below_of_match hpl, Equiv.apply_symm_apply]
  · have := red (pl.symm PP)
    rw [Equiv.apply_symm_apply] at this
    exact ⟨this.symm⟩

def FirstOff {Pg : Finset (Pl D.host.E)} (h : LinearCoefficientData.IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ) : Prop :=
  ∀ (θ : LinearCoefficientData.InfFam D), IsInfFam θ →
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M₀ : DSModel (D.sp.Y 0) (parB (tparRec D) 0))
    (M₁ : DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j))))
    (β₀ : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (β₁ : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    LinearCoefficientData.IsFrameOf (D.sp.Y 0) β₀ → LinearCoefficientData.IsFrameOf (D.sp.W j) β₁ →
  ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    SphOff (Lev.levG (D.sp.Y 0) β₀ (LinearCoefficientData.datE D Pg P) : Set (GA D (D.sp.Y 0)))
      (Lev.levChi (D.sp.Y 0) β₀ (LinearCoefficientData.datE D Pg P)) S →
    SphOff (Lev.levG (D.sp.W j) β₁ (LinearCoefficientData.datWj D j h1 h2 Pg P) : Set (GA D (D.sp.W j)))
      (Lev.levChi (D.sp.W j) β₁ (LinearCoefficientData.datWj D j h1 h2 Pg P)) S →
    ¬ (BadPlacesGoodCoefficients.IsFrameAtG (D.sp.Y 0) β₀ ∧ BadPlacesGoodCoefficients.IsFrameAtG (D.sp.W j) β₁ ∧ S = BadPlacesGoodCoefficients.badPlaces D) →
  ∀ c : LinearCoefficientData.Eig D,
    FiniteDimensional ℂ (LinearCoefficientData.EEc θ M₀ h β₀ P S c) ∧ FiniteDimensional ℂ (LinearCoefficientData.Wc θ j h1 h2 M₁ h β₁ P S c) ∧
      Module.finrank ℂ (LinearCoefficientData.Wc θ j h1 h2 M₁ h β₁ P S c) = Module.finrank ℂ (LinearCoefficientData.EEc θ M₀ h β₀ P S c)

def FirstOffRec (D : D7) : Prop :=
  ∀ (Pg : Finset (Pl D.host.E)) (h : LinearCoefficientData.IsRecPlaces D Pg) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ),
    IsGenericPsi Pg ψ → FirstOff h (P0 Pg D.R.r ψ)

def Tied (D : D7) : Prop :=
  (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) ∧ ∃ om, LevelCuspCharacters.IsGeneratorFamily (H := D.host) om ∧ TameTie D om

def Core : Prop := ∀ D : D7, Tied D → FirstRec D

def CoreSecond : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L) om, LevelCuspCharacters.IsGeneratorFamily (H := D.host) om → TameTie D om → SecondAll D om

def ExcessRecords : Prop := ∀ D : D7, LinearCoefficientData.ParamGap D → GlobalTheory.GLq.ESerTie D → ¬ Tied D → LinearCoefficientData.DimensionDecompositionAtBasePrime D

def ExcessLattices : Prop := ∀ D : D7, Tied D → FirstOffRec D

def ExcessChars : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L) om, LevelCuspCharacters.IsGeneratorFamily (H := D.host) om → ¬ TameTie D om → SecondAll D om

end GlobalTheory.DimPartsCompare

end
