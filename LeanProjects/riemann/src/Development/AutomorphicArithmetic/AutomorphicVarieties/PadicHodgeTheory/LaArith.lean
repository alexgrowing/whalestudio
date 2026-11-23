import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteEmb
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterFirst
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem cyc_continuous (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cyc_continuous F Ω l

theorem UpperTheory.V.Loc.laArith :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous κ → ∀ (m : ℤ) (k : ℕ), 0 < k → (∀ g : ↥(Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (κ g * cycBar F Ω l g ^ (-m)) ^ k = 1) → IsLocAlg h κ fun _ => -m := by
  intro H F Ω _ _ _ _ _ l _ A w h hl κ hκ m k hk hpow
  set c : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype with hc
  have hcc : Continuous c := (cyc_continuous F Ω l).comp continuous_subtype_val
  let i : ↥(Ine (F := F) A) →* ↥(Dec (F := F) A) := (Subgroup.inclusion (Weil_le_Dec h)).comp (ineIncl h)
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  let χ : ↥(Dec (F := F) A) →* (Qbar l)ˣ := κ * c ^ (-m)
  have hχ : Continuous χ := hκ.mul ((continuous_zpow (-m)).comp hcc)
  have ho : IsOpen ((χ.comp i)⁻¹.ker : Set ↥(Ine (F := F) A)) := by
    refine isOpen_ker_of_pow _ (hχ.comp hi).inv hk fun σ => ?_
    have h1 : χ (i σ) ^ k = 1 := hpow (i σ) σ.2
    rw [MonoidHom.inv_apply, MonoidHom.comp_apply, inv_pow, h1, inv_one]
  obtain ⟨hmul, hz, h0⟩ := UpperTheory.V.Loc.laMul (l := l) h
  have H0 : IsWtPart h χ 0 (χ.comp i)⁻¹ := h0 χ _ ho fun σ => mul_inv_cancel _
  have H1 := (hmul _ _ _ _ _ _ H0 (hz _ _ _ m (UpperTheory.V.Loc.laCyc H h hl))).1
  have e : χ * c ^ m = κ := by
    simp only [χ, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have e' : (0 + m • fun _ : Emb l w => (-1 : ℤ)) = fun _ => -m := by
    funext τ
    simp
  rw [← hc, e, e'] at H1
  exact ⟨_, H1⟩
