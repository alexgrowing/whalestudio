import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem algPow_ne {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : Plc F)
    (hh : (F →+* Qbar l) → ℤ) (x : (w.adicCompletion F)ˣ) : algPow w hh (x : w.adicCompletion F) ≠ 0 := by
  unfold algPow
  apply finprod_induction (fun z : Qbar l => z ≠ 0) one_ne_zero
  · intro a b ha hb
    exact mul_ne_zero ha hb
  · intro j
    exact zpow_ne_zero _ ((map_ne_zero _).mpr x.ne_zero)

private theorem algPow_mul {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : Plc F)
    (hh : (F →+* Qbar l) → ℤ) (x y : w.adicCompletion F) : algPow w hh (x * y) = algPow w hh x * algPow w hh y := by
  haveI := finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [map_mul, mul_zpow]

private noncomputable def algHom {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : Plc F)
    (hh : (F →+* Qbar l) → ℤ) : (w.adicCompletion F)ˣ →* (Qbar l)ˣ :=
  MonoidHom.mk' (fun x => Units.mk0 _ (algPow_ne w hh x)) fun x y => Units.ext (algPow_mul w hh x y)

private theorem artin_unique (H : GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {a a' : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (ha' : IsLocalArtin h a') : a' = a := by
  obtain ⟨art, hart⟩ := H F Ω
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart w
  exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)

private theorem part_iff (H : GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)
    (ι : Qbar l ≃+* ℂ) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (hh : (F →+* Qbar l) → ℤ)
    (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ω : (w.adicCompletion F)ˣ →* ℂˣ) (ho : OrdChar ι a ω hh ψ)
    (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ) :
    IsWtPart h ψ (fun τ => hh (τ.1.comp (algebraMap F (w.adicCompletion F)))) ph ↔
      ∀ σ : ↥(Ine (F := F) A), ι (ph σ : Qbar l) = ((ω (a (ineIncl h σ)))⁻¹ : ℂˣ) := by
  have key : ∀ σ : Ine (F := F) A,
      ((ψ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) : Qbar l)) =
        ι.symm (ω (a (ineIncl h σ)) : ℂ) * algPow w (-hh) (a (ineIncl h σ) : w.adicCompletion F) :=
    fun σ => ho.val _ _ rfl (Set.mem_univ _)
  constructor
  · rintro ⟨-, hw⟩ σ
    have e := hw a ha σ
    rw [Units.val_mul, key σ] at e
    change _ = algPow w (-hh) _ at e
    have hP : algPow w (-hh) (a (ineIncl h σ) : w.adicCompletion F) ≠ 0 := algPow_ne w (-hh) _
    have e2 : ι.symm (ω (a (ineIncl h σ)) : ℂ) * (ph σ : Qbar l) = 1 := by
      apply mul_right_cancel₀ hP
      rw [one_mul]
      convert e using 1
      ring
    apply_fun ι at e2
    rw [map_mul, map_one, RingEquiv.apply_symm_apply] at e2
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right e2
  · intro hR
    refine ⟨?_, fun a' ha' σ => ?_⟩
    · have hker : (ph.ker : Set (Ine (F := F) A)) = (fun σ => a (ineIncl h σ)) ⁻¹' (ω.ker : Set _) := by
        ext σ
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage]
        constructor
        · intro h1
          have e := hR σ
          rw [h1, Units.val_one, map_one] at e
          exact inv_eq_one.mp (Units.val_eq_one.mp e.symm)
        · intro h1
          have e := hR σ
          rw [h1, inv_one, Units.val_one] at e
          exact Units.val_eq_one.mp (ι.injective (e.trans (map_one ι).symm))
      rw [hker]
      exact IsOpen.preimage ha.cont ho.smooth
    · rw [artin_unique H ha ha', Units.val_mul, key σ]
      change _ = algPow w (-hh) _
      have e := hR σ
      have hph : (ph σ : Qbar l) = ι.symm (((ω (a (ineIncl h σ)))⁻¹ : ℂˣ) : ℂ) := by
        rw [← e, RingEquiv.symm_apply_apply]
      rw [hph, Units.val_inv_eq_inv_val, map_inv₀]
      have hne : ι.symm (ω (a (ineIncl h σ)) : ℂ) ≠ 0 := by simp
      field_simp

theorem UpperTheory.V.Loc.ordCharIff :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (ι : Qbar l ≃+* ℂ) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (hh : (F →+* Qbar l) → ℤ) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), ((∃ ω, OrdChar ι a ω hh ψ) ↔ Continuous ψ ∧ IsLocAlg h ψ fun τ => hh (τ.1.comp (algebraMap F (w.adicCompletion F)))) ∧ ∀ ω, OrdChar ι a ω hh ψ → ∀ ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ, (IsWtPart h ψ (fun τ => hh (τ.1.comp (algebraMap F (w.adicCompletion F)))) ph ↔ ∀ σ : ↥(Ine (F := F) A), ι (ph σ : Qbar l) = ((ω (a (ineIncl h σ)))⁻¹ : ℂˣ)) := by
  intro H F Ω _ _ _ _ _ l _ A w h ι a ha hh ψ
  refine ⟨⟨fun ⟨ω, ho⟩ => ⟨ho.cont, ?_⟩, fun ⟨hc, ph, hph⟩ => ?_⟩,
    fun ω ho ph => part_iff H h ι a ha hh ψ ω ho ph⟩
  · let ph : Ine (F := F) A →* (Qbar l)ˣ :=
      (Units.map (ι.symm : ℂ →+* Qbar l).toMonoidHom).comp ((ω.comp (a.comp (ineIncl h)))⁻¹)
    refine ⟨ph, (part_iff H h ι a ha hh ψ ω ho ph).mpr fun σ => ?_⟩
    simp [ph]
  · let incl : Weil h →* Dec (F := F) A := Subgroup.inclusion (Weil_le_Dec h)
    let ξ : Weil h →* ℂˣ :=
      (Units.map (ι : Qbar l →+* ℂ).toMonoidHom).comp (ψ.comp incl * ((algHom w (-hh)).comp a)⁻¹)
    have hξ : ∀ s, ((ξ s : ℂˣ) : ℂ) =
        ι ((ψ (incl s) : Qbar l) / algPow w (-hh) (a s : w.adicCompletion F)) := by
      intro s
      simp [ξ, algHom, div_eq_mul_inv]
    have hsm : IsSmooth ξ := by
      have hset : {σ | ξ (ineIncl h σ) = 1} = (ph.ker : Set (Ine (F := F) A)) := by
        ext σ
        simp only [Set.mem_setOf_eq, SetLike.mem_coe, MonoidHom.mem_ker]
        have e := hph.2 a ha σ
        change ((ψ (incl (ineIncl h σ)) * ph σ : (Qbar l)ˣ) : Qbar l) =
          algPow w (-hh) (a (ineIncl h σ) : w.adicCompletion F) at e
        have hP := algPow_ne w (-hh) (a (ineIncl h σ))
        constructor
        · intro h1
          have h2 : (ψ (incl (ineIncl h σ)) : Qbar l) / algPow w (-hh) (a (ineIncl h σ) : w.adicCompletion F) = 1 := by
            apply ι.injective
            rw [← hξ, h1, Units.val_one, map_one]
          rw [div_eq_one_iff_eq hP] at h2
          rw [Units.val_mul, h2] at e
          apply Units.ext
          rw [Units.val_one]
          exact mul_left_cancel₀ hP (e.trans (mul_one _).symm)
        · intro h1
          rw [Units.val_mul, h1, Units.val_one, mul_one] at e
          apply Units.ext
          rw [Units.val_one, hξ, e, div_self hP, map_one]
      show IsOpen {σ | ξ (ineIncl h σ) = 1}
      rw [hset]
      exact hph.1
    obtain ⟨χ, hχs, hχ⟩ := ha.factor ξ hsm
    refine ⟨χ, ⟨hχs, hc, ?_⟩⟩
    intro s g hg _
    have hgs : g = incl s := Subtype.ext (by exact hg)
    subst hgs
    show (ψ (incl s) : Qbar l) = ι.symm (χ (a s) : ℂ) * algPow w (-hh) (a s : w.adicCompletion F)
    have hχa : χ (a s) = ξ s := by
      rw [hχ]
      rfl
    rw [hχa, hξ, RingEquiv.symm_apply_apply, div_mul_cancel₀ _ (algPow_ne w (-hh) (a s))]
