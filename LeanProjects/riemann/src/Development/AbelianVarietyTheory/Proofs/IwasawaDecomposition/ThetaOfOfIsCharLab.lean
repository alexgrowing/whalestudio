import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfPlacesTypePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfPow

noncomputable section

namespace GlobalTheory.Mem.TypePl

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp NumberField IsDedekindDomain
open scoped Pointwise

section Places

variable {R : Ranks} {H : Host R}

theorem isConjPl_iff_conjPl (w w' : PlE H) : IsConjPl H w w' ↔ Chr.ConjPl H.conj.toRingEquiv w w' :=
  (HalfPlaces.isConjPl_iff H w w').trans (Chr.conjPl_iff_smul H.conj w w').symm

theorem under_eq_iff (w w' : PlE H) : w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ w' = w ∨ IsConjPl H w w' := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  rw [Chr.under_eq_iff_conjPl c hcm.rank hcm.ne, isConjPl_iff_conjPl]
  have e : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  rw [e]

theorem under_mem {p : ℕ} {w : PlE H} : w.under (𝓞 H.F) ∈ placesOver H.F p ↔ w ∈ placesOver H.E p := by
  show algebraMap (𝓞 H.F) (𝓞 H.E) ((p : ℕ) : 𝓞 H.F) ∈ w.asIdeal ↔ _
  rw [map_natCast]
  rfl

theorem exists_under (v : HeightOneSpectrum (𝓞 H.F)) : ∃ w : PlE H, w.under (𝓞 H.F) = v := by
  have := v.isPrime
  obtain ⟨⟨W, hW, hWv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 H.E)))
  exact ⟨⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot W⟩, HeightOneSpectrum.ext hWv.over.symm⟩

theorem div_over (P : PiBar H) {k : Fin 2} {w : PlE H} (h : P.Div k w) : w ∈ placesOver H.E (H.g k) := by
  have h1 := P.pb_over k
  rw [← (show w.under (𝓞 H.K) = P.pb k from h)] at h1
  have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((H.g k : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h1
  rwa [map_natCast] at h2

theorem div_iff_not_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    {w w' : PlE H} (hw : w ∈ placesOver H.E (H.g k)) (h : IsConjPl H w w') : P.Div k w ↔ ¬ P.Div k w' :=
  ((Chr.splitsC_main R H (H.g k) (H.g_prime k) hs w hw).2.2.2 (P.pb k) (P.pb_over k) w'
    ((isConjPl_iff_conjPl w w').1 h)).2

theorem not_isConjPl (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    {w w' : PlE H} (hw : P.Div k w) (hw' : P.Div k w') : ¬ IsConjPl H w w' :=
  fun h => (div_iff_not_div P hs (div_over P hw) h).1 hw hw'

def below {p : ℕ} {I : Type} (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p) (i : I) : placesOver H.F p :=
  ⟨(pl i).under (𝓞 H.F), under_mem.2 (h i)⟩

theorem below_injective {p : ℕ} {I : Type} (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p)
    (h1 : Function.Injective pl) (h2 : ∀ i j, ¬ IsConjPl H (pl i) (pl j)) : Function.Injective (below pl h) :=
  fun i j e => ((under_eq_iff (pl j) (pl i)).1 (congrArg Subtype.val e)).elim (fun e => h1 e) fun e => absurd e (h2 j i)

theorem card_placesOver {p : ℕ} (hp : p.Prime) (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E) :
    Nat.card (placesOver H.F p) = R.f := by
  obtain ⟨e, h, h1, h2, h3⟩ := HalfPlaces.exists_places_cover H hp hs
  have hb : Function.Bijective (below e h) := by
    refine ⟨below_injective e h h1 h2, fun v => ?_⟩
    obtain ⟨w, hw⟩ := exists_under v.1
    obtain ⟨i, hi⟩ := h3 w (under_mem.1 (hw ▸ v.2))
    exact ⟨i, Subtype.ext (((under_eq_iff (e i) w).2 hi).symm.trans hw)⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem below_bijective {p : ℕ} (hp : p.Prime) (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E)
    {I : Type} [Fintype I] (hI : Fintype.card I = R.f) (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p)
    (h1 : Function.Injective pl) (h2 : ∀ i j, ¬ IsConjPl H (pl i) (pl j)) : Function.Bijective (below pl h) := by
  have hc := card_placesOver hp hs
  haveI : Finite (placesOver H.F p) := Nat.finite_of_card_ne_zero (hc ▸ (GaloisStage.f_pos R).ne')
  exact (Nat.bijective_iff_injective_and_card _).2
    ⟨below_injective pl h h1 h2, by rw [hc, Nat.card_eq_fintype_card, hI]⟩

theorem existsUnique_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : ∃! w : PlE H, P.Div k w ∧ w.under (𝓞 H.F) = v := by
  obtain ⟨w, hw⟩ := exists_under v.1
  have hex : ∃ w : PlE H, P.Div k w ∧ w.under (𝓞 H.F) = v := by
    by_cases h : P.Div k w
    · exact ⟨w, h, hw⟩
    · obtain ⟨w', hw', -⟩ := Chr.existsUnique_conjPl H.conj.toRingEquiv w
      have hc := (isConjPl_iff_conjPl w w').2 hw'
      refine ⟨w', ?_, ((under_eq_iff w w').2 (Or.inr hc)).trans hw⟩
      by_contra h'
      exact h ((div_iff_not_div P hs (under_mem.1 (hw ▸ v.2)) hc).2 h')
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, fun b hb => ?_⟩
  exact ((under_eq_iff a b).1 (hb.2.trans ha.2.symm)).elim id fun e => absurd e (not_isConjPl P hs ha.1 hb.1)

def above (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : PlE H := (existsUnique_div P hs v).choose

theorem above_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : P.Div k (above P hs v) := (existsUnique_div P hs v).choose_spec.1.1

theorem above_under (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : (above P hs v).under (𝓞 H.F) = v := (existsUnique_div P hs v).choose_spec.1.2

theorem above_injective (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    Function.Injective (above P hs) :=
  fun v v' e => Subtype.ext (by rw [← above_under P hs v, e, above_under])

end Places

section Labels

def labDat (g : ℕ) [Fact g.Prime] : LabelDatum g := (LabelModel.inhab g).some

variable {g : ℕ} [Fact g.Prime]

def charLab (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) : (ZMod g)ˣ :=
  Units.mk0 (GLp.Model.isCharLab_exists L ω).choose (GLp.Model.isCharLab_exists L ω).choose_spec.1

theorem isCharLab_charLab (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) : IsCharLab L ω (charLab L ω) :=
  (GLp.Model.isCharLab_exists L ω).choose_spec

theorem isCharLab_pow (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) (n : ℕ) :
    IsCharLab L (ω ^ n) ((charLab L ω ^ n : (ZMod g)ˣ) : ZMod g) := by
  refine ⟨Units.ne_zero _, fun u hu => ?_⟩
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow,
    (isCharLab_charLab L ω).2 u hu]

theorem orderOf_charLab (L : LabelDatum g) {ω : (ZMod g)ˣ →* ℂˣ} (h : Function.Injective ω) :
    orderOf (charLab L ω) = g - 1 := by
  obtain ⟨u, hu, ho⟩ := GLp.Model.exists_gen L
  let T : (ZMod g)ˣ →* ℂ := L.teich.comp ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom _))
  have hT : Function.Injective T := fun a b e => Units.ext <| (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
    (L.teich_inj _ _ (by simp) (by simp) e)
  have e : T (charLab L ω) = (ω u : ℂ) := ((isCharLab_charLab L ω).2 u hu).symm
  rw [← orderOf_injective T hT, e, orderOf_units, orderOf_injective ω h, ho]

theorem thetaOf_of_isCharLab (L : LabelDatum g) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g} (hc : IsCharLab L χ c)
    (a : (ZMod g)ˣ) : thetaOf L 1 (algebraMap (ZMod g) _ c) (algebraMap (ZMod g) _ (a : ZMod g)) = ((χ a : ℂˣ) : ℂ) := by
  obtain ⟨u, hu, ho⟩ := GLp.Model.exists_gen L
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ho, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, u ^ m = a := mem_powers_iff_mem_zpowers.2 (htop ▸ Subgroup.mem_top a)
  have hcp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc.1, map_one]
  rw [Units.val_pow_eq_pow_val, map_pow, hu, LabelModel.thetaOf_pow g L one_pos hcp, map_pow,
    Units.val_pow_eq_pow_val, hc.2 u hu]

end Labels

end GlobalTheory.Mem.TypePl

end
