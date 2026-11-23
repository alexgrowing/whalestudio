import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoStmt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV
open scoped Matrix

namespace GlobalTheory.Ord2.Test

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem isConj_iff (s : G ℚ Ω) : IsConj s ↔ IsCC s := Iff.rfl

theorem vanishOrd_of (h : X.LemmaKatoW) : VanishOrd := fun l _ _ Ω _ _ _ ι e he W hW => by
  obtain ⟨f, M, φ, hM, hφ, hf⟩ := hW.modular
  exact h e he f l Ω ι W hW.cont M hM φ hφ hf

theorem cohomology_inputs_of_unitary (h : U3.Inp) : Inp0 :=
  { h.toCohInp with
    lemM := h.lemM, lemM' := h.lemM', lemP := h.lemP, adK := h.adK, adQ := h.adQ, newAut := h.newAut,
    number := h.number }

theorem om_mulVec (A : Matrix (Fin 2) (Fin 2) (Qbar l)) (x y : Fin 2 → Qbar l) :
    om (A *ᵥ x) (A *ᵥ y) = A.det * om x y := by
  simp [om, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

theorem om_equiv (W : R2 Ω l) (s : G ℚ Ω) (x y : Fin 2 → Qbar l) :
    om (mat W s *ᵥ x) (mat (dual1 W) s *ᵥ y) = eps l s * om x y := by
  have h1 : mat (dual1 W) s = (eps l s * ((mat W s).det)⁻¹) • mat W s := by
    rw [mat, dual1, tw_val]; simp [dt]
  have h2 : (mat W s).det ≠ 0 := (Matrix.GeneralLinearGroup.det (W s)).ne_zero
  have h3 : ∀ (a : Qbar l) (u v : Fin 2 → Qbar l), om u (a • v) = a * om u v := fun a u v => by
    simp [om]; ring
  rw [h1, Matrix.smul_mulVec, h3, om_mulVec]; field_simp

theorem om_add_left (x y z : Fin 2 → Qbar l) : om (x + y) z = om x z + om y z := by simp [om]; ring
theorem om_add_right (x y z : Fin 2 → Qbar l) : om z (x + y) = om z x + om z y := by simp [om]; ring
theorem om_sub_left (x y z : Fin 2 → Qbar l) : om (x - y) z = om x z - om y z := by simp [om]; ring

theorem mat_mul (W : R2 Ω l) (s t : G ℚ Ω) : mat W (s * t) = mat W s * mat W t := by simp [mat]

theorem cup_coc (W : R2 Ω l) (a b : G ℚ Ω → Fin 2 → Qbar l) (ha : ∀ s t, a (s * t) = a s + mat W s *ᵥ a t)
    (hb : ∀ s t, b (s * t) = b s + mat (dual1 W) s *ᵥ b t) (r s t : G ℚ Ω) :
    eps l r * cup W a b s t + cup W a b r (s * t) = cup W a b (r * s) t + cup W a b r s := by
  simp only [cup]
  rw [ha, hb, mat_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_add, om_add_left, om_add_right, om_equiv]
  ring

theorem cup_cob (W : R2 Ω l) (a : Fin 2 → Qbar l) (z : G ℚ Ω → Fin 2 → Qbar l)
    (hz : ∀ s t, z (s * t) = z s + mat (dual1 W) s *ᵥ z t) (s t : G ℚ Ω) :
    cup W (fun s => mat W s *ᵥ a - a) z s t = eps l s * om a (z t) - om a (z (s * t)) + om a (z s) := by
  simp only [cup]
  rw [hz, om_sub_left, om_add_right, om_equiv]
  ring

theorem ht_cob (W : R2 Ω l) (a : Fin 2 → Qbar l) (z : G ℚ Ω → Fin 2 → Qbar l) (s : G ℚ Ω) :
    ht W (fun s => mat W s *ᵥ a - a) z (fun s => om a (z s)) s = 0 := by
  have h : mat W s *ᵥ a - a = (mat W s - 1) *ᵥ a := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [ht]
  rw [h, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp [om]; ring

theorem gr_of_triv (W : R2 Ω l) (A : ValuationSubring Ω) (hW : ∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0)
    (c : G ℚ Ω → Fin 2 → Qbar l) (h : Triv W A c) : Gr W A c := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x 1, fun s hs => ?_⟩
  rw [hx s hs]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hW s hs]

theorem strZero_of_grZero (W : R2 Ω l) (A : ValuationSubring Ω) (hW : ∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0)
    (h : GrZero W A) : StrZero W A := fun c hc hu ht => h c hc hu (gr_of_triv W A hW c ht)

theorem eps_eq (s : G ℚ Ω) : eps l s = algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]) := rfl

theorem cont_int : Continuous (algebraMap ℤ_[l] (Qbar l)) :=
  (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val

theorem cg_refl (n : ℕ) (a : Qbar l) : Cg n a a := by simp [Cg]

theorem cycZ_ine [IsAlgClosure ℚ Ω] {v : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) : cycZ ℚ Ω l σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
  simp

theorem cyclotomic_two_cocycle [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (hS : ContainsAbove S l) :
    Coc2 c n S (fun s _ : G ℚ Ω => eps l s) where
  cont := (cont_int.comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))).comp continuous_fst
  int s _ := c.O.algebraMap_mem _
  coc r s t := by
    have : eps l (r * s) = eps l r * eps l s := by simp [eps]
    rw [this]; exact cg_refl _ _
  unr s t a ha b _ := by
    have hu : UnramOutside (S : Set Pl) (cycZ ℚ Ω l) := by
      rw [unramOutside_iff _ _ (continuous_cycZ ℚ Ω l)]
      exact fun v hv A hA σ hσ => cycZ_ine (fun h => hv (hS v h)) hA hσ
    have h1 : cycZ ℚ Ω l a = 1 := hu a ((QuotientGroup.eq_one_iff a).1 ha)
    rw [eps_eq, eps_eq, map_mul, h1, mul_one]; exact cg_refl _ _

theorem cyclotomic_two_coboundary (c : Coef l) (n : ℕ) (H : Subgroup (G ℚ Ω)) : Cob2 c n H (fun s _ : G ℚ Ω => eps l s) :=
  ⟨fun _ => 1, continuousOn_const, fun _ => c.O.one_mem, fun s _ t _ => by simpa using cg_refl n (eps l s)⟩

def coefBot (l : ℕ) [Fact l.Prime] : Coef l :=
  have hi : Function.Injective (algebraMap ℤ_[l] (Qbar l)) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  { O := ⊥
    dvr := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (Algebra.botEquivOfInjective hi).symm
    fin := Module.Finite.equiv (Algebra.botEquivOfInjective hi).symm.toLinearEquiv }

theorem tame_zero (c : Coef l) (W : R2 Ω l) (y : G ℚ Ω → Fin 2 → Qbar l) (n : ℕ) (w : Pl)
    (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (h : ∀ (B : ValuationSubring Ω) (σ : G ℚ Ω), IsPlaceOver B w → IsFrob B (normV w) σ → Cg n 0 (mat W σ - 1).det) :
    Tame c W y n w ψ := by
  refine ⟨0, 0, 1, 0, continuous_const, fun _ _ _ => c.O.zero_mem, c.O.zero_mem, norm_one, fun _ => c.O.zero_mem,
    by simp, by simp, fun B σ h1 h2 => by simpa using h B σ h1 h2, fun q _ _ => ?_⟩
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω q
  exact ⟨B, hB, 0, fun _ _ => c.O.zero_mem, by simp⟩

def lgE (l : ℕ) [Fact l.Prime] (s : G ℚ Ω) : ℚ_[l] := Formalism.MainNotions.LocalSituation.logZl l ((cycZ ℚ Ω l s : ℤ_[l]) : ℚ_[l])

theorem nu (u : ℤ_[l]ˣ) : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u

theorem lgE_mul (s t : G ℚ Ω) : lgE l (s * t) = lgE l s + lgE l t := by
  rw [lgE, map_mul, Units.val_mul, PadicInt.coe_mul]
  exact (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (nu _) (nu _)

theorem es_one [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : OverL l A) : ES (1 : R2 Ω l) A := by
  obtain ⟨hm, hc, hi, hn⟩ := GlobalTheory.PadicLogUnits.logZl_hom l
  have hcont : Continuous (lgE (Ω := Ω) l) :=
    hc.comp_continuous (continuous_subtype_val.comp ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l))) fun _ => nu _
  refine ⟨coefBot l, fun s => ![0, algebraMap ℚ_[l] (Qbar l) (lgE l s)], ∅, fun s i j => ?_, ⟨?_, fun s t => ?_⟩,
    fun s i => ?_, fun w hw => ?_, ?_, fun n _ w _ _ ψ _ _ => tame_zero _ _ _ _ _ _ fun B σ _ _ => ?_⟩
  · by_cases h : i = j
    · subst h; simpa [mat] using (coefBot l).O.one_mem
    · simpa [mat, Matrix.one_apply_ne h] using (coefBot l).O.zero_mem
  · refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_const
    · exact (continuous_algebraMap _ _).comp hcont
  · ext i
    fin_cases i <;> simp [Loc.colRep, lgE_mul]
  · fin_cases i
    · exact (coefBot l).O.zero_mem
    · exact (coefBot l).O.algebraMap_mem (⟨lgE l s, hi _ (nu _)⟩ : ℤ_[l])
  · obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
    refine ⟨B, hB, 0, fun s hs => ?_⟩
    have h1 := hm 1 1 norm_one norm_one
    rw [mul_one] at h1
    have h2 : Formalism.MainNotions.LocalSituation.logZl l 1 = 0 := by linear_combination -h1
    have h3 : lgE l s = 0 := by rw [lgE, cycZ_ine hw hB hs]; simpa using h2
    ext i
    fin_cases i <;> simp [h3]
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv, hl⟩ := hA
    have hA' : A.valuation (l : Ω) < 1 := by simpa using (hv (l : 𝓞 ℚ)).2 hl
    have hl2 : ‖((l : ℤ_[l])) ^ 2‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (by simp [PadicInt.norm_p, inv_lt_one_of_one_lt₀, (Fact.out : l.Prime).one_lt]) two_ne_zero
    have hu : IsUnit (1 + (l : ℤ_[l]) ^ 2) := by
      have := (Units.oneSub (-(l : ℤ_[l]) ^ 2) (by rwa [norm_neg])).isUnit
      rwa [Units.val_oneSub, sub_neg_eq_add] at this
    obtain ⟨u, hu⟩ := hu
    obtain ⟨s, hs, e⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA' u
    have h1 := hx s (Ine_le_Dec A hs)
    have h2 : lgE l s = 0 := by simpa [mat] using h1
    have h3 : ((u : ℤ_[l]) : ℚ_[l]) - 1 = (l : ℚ_[l]) ^ 2 := by rw [hu]; simp
    have h4 := hn 2 (by norm_num) (fun _ => le_rfl) ((u : ℤ_[l]) : ℚ_[l]) (by rw [h3, norm_pow, Padic.norm_p]; simp)
    rw [lgE, e] at h2
    rw [h2, h3, norm_zero, eq_comm, norm_eq_zero] at h4
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast pow_eq_zero_iff two_ne_zero |>.1 h4)
  · simpa [mat] using cg_refl n (0 : Qbar l)

theorem deriv_rel (W : R2 Ω l) (n : ℕ) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)))
    (Y : G ℚ Ω → ZMod (l ^ n) → Fin 2 → Qbar l)
    (hY : ∀ s t x, Y (s * t) x = Y s x + mat W s *ᵥ Y t (x - (ψ s).toAdd)) (s t : G ℚ Ω) :
    ∃ k : ZMod (l ^ n) → ℕ, ∑ᶠ x, (x.val : Qbar l) • Y (s * t) x + ((l : Qbar l) ^ n) • ∑ᶠ x, (k x : Qbar l) • (mat W s *ᵥ Y t x) =
      ∑ᶠ x, (x.val : Qbar l) • Y s x + mat W s *ᵥ (∑ᶠ x, (x.val : Qbar l) • Y t x) +
        (((ψ s).toAdd).val : Qbar l) • (mat W s *ᵥ ∑ᶠ x, Y t x) := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set a := (ψ s).toAdd
  refine ⟨fun x => (x.val + a.val) / l ^ n, ?_⟩
  simp only [finsum_eq_sum_of_fintype]
  rw [Matrix.mulVec_sum, Matrix.mulVec_sum, Finset.smul_sum, Finset.smul_sum]
  simp only [hY, smul_add, Finset.sum_add_distrib, Matrix.mulVec_smul]
  rw [← Equiv.sum_comp (Equiv.addRight a) (fun x : ZMod (l ^ n) => ((x.val : Qbar l) • (mat W s *ᵥ Y t (x - a)) : Fin 2 → Qbar l))]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := Nat.mod_add_div (x.val + a.val) (l ^ n)
  rw [← ZMod.val_add] at h
  have h' : (((x + a).val : ℕ) : Qbar l) + (l : Qbar l) ^ n * (((x.val + a.val) / l ^ n : ℕ) : Qbar l) = x.val + a.val := by
    exact_mod_cast congrArg (Nat.cast : ℕ → Qbar l) h
  simp only [Equiv.coe_addRight, add_sub_cancel_right, smul_smul]
  rw [add_assoc, add_assoc, ← add_smul, ← add_smul, h']

end GlobalTheory.Ord2.Test

end
