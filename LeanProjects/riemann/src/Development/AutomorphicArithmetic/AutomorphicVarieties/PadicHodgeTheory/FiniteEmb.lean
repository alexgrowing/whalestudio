import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem finite_emb {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (w : Plc F) :
    Finite (Emb l w) := by
  refine Finite.of_injective
    (fun j : Emb l w => (j.1.comp (algebraMap F (w.adicCompletion F)) : F →+* Qbar l)) fun j j' hjj => ?_
  refine Subtype.ext (DFunLike.coe_injective ?_)
  refine (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w)).equalizer j.2 j'.2 ?_
  funext x
  exact DFunLike.congr_fun hjj x

private theorem wt_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)
    (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ)
    (ho : IsOpen (ph.ker : Set ↥(Ine (F := F) A)))
    (H : ∀ σ : ↥(Ine (F := F) A), κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ = 1) :
    IsWtPart h κ 0 ph :=
  ⟨ho, fun a _ σ => by rw [H]; simp⟩

private theorem wt_mul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {κ κ' : ↥(Dec (F := F) A) →* (Qbar l)ˣ} {wt wt' : Emb l w → ℤ} {ph ph' : ↥(Ine (F := F) A) →* (Qbar l)ˣ}
    (H : IsWtPart h κ wt ph) (H' : IsWtPart h κ' wt' ph') : IsWtPart h (κ * κ') (wt + wt') (ph * ph') := by
  haveI := finite_emb l w
  haveI := Fintype.ofFinite (Emb l w)
  refine ⟨?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := ph.ker ⊓ ph'.ker) (fun x hx => ?_) (H.1.inter H'.1)
    have h1 : ph x = 1 := hx.1
    have h2 : ph' x = 1 := hx.2
    simp [MonoidHom.mem_ker, h1, h2]
  · have h1 := H.2 a ha σ
    have h2 := H'.2 a ha σ
    rw [finprod_eq_prod_of_fintype] at h1 h2 ⊢
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, mul_mul_mul_comm, Units.val_mul, h1, h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Pi.add_apply, neg_add, zpow_add₀ ((map_ne_zero τ.1).2 (Units.ne_zero _))]

private theorem wt_zpow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w}
    {κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ} {wt : Emb l w → ℤ} {ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ}
    (H : IsWtPart h κ wt ph) (m : ℤ) : IsWtPart h (κ ^ m) (m • wt) (ph ^ m) := by
  haveI := finite_emb l w
  haveI := Fintype.ofFinite (Emb l w)
  refine ⟨?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := ph.ker) (fun x hx => ?_) H.1
    have h1 : ph x = 1 := hx
    rw [MonoidHom.mem_ker, MonoidHom.zpow_apply, h1, one_zpow]
  · have h1 := H.2 a ha σ
    rw [finprod_eq_prod_of_fintype] at h1 ⊢
    rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply, ← mul_zpow, Units.val_zpow_eq_zpow_val, h1, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_mul, Pi.smul_apply, smul_eq_mul, neg_mul, mul_comm]

theorem UpperTheory.V.Loc.laMul :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), (∀ (κ κ' : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt wt' : Emb l w → ℤ) (ph ph' : ↥(Ine (F := F) A) →* (Qbar l)ˣ), IsWtPart h κ wt ph → IsWtPart h κ' wt' ph' → IsWtPart h (κ * κ') (wt + wt') (ph * ph') ∧ IsWtPart h κ⁻¹ (-wt) ph⁻¹) ∧ (∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt : Emb l w → ℤ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ) (m : ℤ), IsWtPart h κ wt ph → IsWtPart h (κ ^ m) (m • wt) (ph ^ m)) ∧ ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ph : ↥(Ine (F := F) A) →* (Qbar l)ˣ), IsOpen (ph.ker : Set ↥(Ine (F := F) A)) → (∀ σ : ↥(Ine (F := F) A), κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ = 1) → IsWtPart h κ 0 ph := by
  intro F Ω _ _ _ _ _ l _ A w h
  refine ⟨fun κ κ' wt wt' ph ph' H H' => ⟨wt_mul H H', ?_⟩, fun κ wt ph m H => wt_zpow H m, wt_one h⟩
  simpa only [zpow_neg_one, neg_smul, one_smul] using wt_zpow H (-1)
