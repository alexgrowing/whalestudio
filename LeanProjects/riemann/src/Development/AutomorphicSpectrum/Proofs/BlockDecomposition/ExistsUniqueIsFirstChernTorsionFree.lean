import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineCocycleClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLiftStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree

section Core

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I}

def precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick ((B.schFn q).cr b ht κ)} {D : E.LineData X}
    (Λ₀ : B.CLift g D) (h : C' ⥤ C) : B.CLift (h ⋙ g) D where
  p c := Λ₀.p (h.obj c)
  hp c := Λ₀.hp (h.obj c)
  w φ := Λ₀.w (h.map φ)
  hw φ hh := Λ₀.hw (h.map φ) hh

end Core

section Main

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} {γ : DividedPowers I} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {l s : ℕ}

theorem dpow_vanish {T : Thick (nlFun γ 0 X q (κA O I))} (hT : TF l s T) (k : ℕ) (hk : s ≤ k) (x : T.B) (hx : x ∈ T.J) :
    (k.factorial : T.B) * T.δ.dpow (k + 1) x = 0 := by
  have h1 : T.δ.dpow (k + 1) x ∈ T.pdPow s := by
    rw [pdPow_eq]
    refine Ideal.subset_span ⟨[(k + 1, x)], ?_, ?_, ?_⟩
    · intro z hz
      rw [List.mem_singleton] at hz
      rw [hz]
      exact hx
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    · simp
  rw [hT.1] at h1
  rw [(Ideal.mem_bot.1 h1), mul_zero]

theorem lifts_of_mem (D : E.LineData X) (T : Thick (nlFun γ 0 X q (κA O I))) (h : ∃ V ∈ 𝒱D D, InU V T) :
    ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = pt T := by
  obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := h
  have hr : Set.range (pt T) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨IsOpenImmersion.lift V.ι (pt T) hr ≫ σ, ?_⟩
  rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]

end Main

theorem existsUnique_isFirstChernTorsionFree : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∃! z, IsFirstChernThickening (TS γ q l s {⊤}) D s z := by
  intro O A _ _ _ I γ X q l s D hD
  have hle : St (TF l s) (𝒱D D) ≤ TS γ q l s {⊤} := fun T h => ⟨h.1, ⊤, rfl, fun _ _ => trivial⟩
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun γ 0 X q (κA O I)))) := Or.inl ⟨rfl, l, s, rfl⟩
  have hb := (GlobalTheory.T.cech_refinement_cohomology_bijective (TF l s) hU (𝒱D D) {⊤} hle (by rintro W rfl; rw [hD]) 2).2.2
  let Q : ObjectProperty (Thick (nlFun γ 0 X q (κA O I))) := TS γ q l s {⊤}
  let Q' : ObjectProperty (Thick (nlFun γ 0 X q (κA O I))) := St (TF l s) (𝒱D D)
  let G₀ : Q'.FullSubcategory ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := Q'.ι
  obtain ⟨Λ₀⟩ := GlobalTheory.T.exists_crystalline_lift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) G₀ D
    (fun T => lifts_of_mem D T.obj T.property.2)
  have hz₀ := (GlobalTheory.T.crystalline_cocycle_closed G₀ D (RingHom.id A) s (fun T k hk x hx => dpow_vanish T.property.1 k hk x hx)).1 Λ₀
  obtain ⟨x, hx⟩ := hb.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G hG Λ₁
    let G₁ : C ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := G ⋙ Q.ι
    have hcl := GlobalTheory.T.crystalline_cocycle_closed G₁ D (RingHom.id A) s
      (fun T k hk x hx => dpow_vanish (G.obj T).property.1 k hk x hx)
    let G' : C ⥤ Q'.FullSubcategory := Q'.lift (G ⋙ Q.ι) fun T => ⟨(G.obj T).property.1, hG T⟩
    let Λ' : B.CLift G₁ D := precomp Λ₀ G'
    refine ⟨hcl.1 Λ₁, ?_⟩
    refine (hcl.2 Λ₁ Λ' (hcl.1 Λ₁) (hcl.1 Λ')).trans ?_
    have e1 : (CH.Mor.restrict (CH.modF (sP Q).A) G).pull 2 x =
        (CH.Mor.restrict (CH.modF (sP Q').A) G').pull 2 ((incl hle).o.pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hb.1
    obtain ⟨h1, h2⟩ := hy _ (ObjectProperty.ιOfLE hle) (fun T => T.property.2) Λ₀
    have e : (incl hle).o.pull 2 y = (CH.Mor.restrict (CH.modF (sP Q).A) (ObjectProperty.ιOfLE hle)).pull 2 y := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl
    rw [hx, e]
    exact h2.symm

end GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree
