import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLiftStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FirstChernPullback

theorem mem_VD_pb {X X' : Scheme.{0}} (D : E.LineData X) (u : X' ⟶ X) {V : X.Opens} (hV : V ∈ 𝒱D D) :
    u ⁻¹ᵁ V ∈ 𝒱D (D.pb u) := by
  obtain ⟨σ, hσ⟩ := hV
  refine ⟨Limits.pullback.lift ((u ∣_ V) ≫ σ) (u ⁻¹ᵁ V).ι ?_, ?_⟩
  · rw [Category.assoc, hσ, morphismRestrict_ι]
  · exact Limits.pullback.lift_snd _ _ _

theorem sSup_preimage {X X' : Scheme.{0}} (𝒲 : Set X.Opens) (u : X' ⟶ X) (h : sSup 𝒲 = ⊤) :
    sSup ((fun V : X.Opens => u ⁻¹ᵁ V) '' 𝒲) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have hx : u x ∈ sSup 𝒲 := by rw [h]; trivial
  obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
  exact TopologicalSpace.Opens.mem_sSup.2 ⟨_, ⟨V, hV, rfl⟩, hxV⟩

theorem u_congr {X : Scheme.{0}} (D : E.LineData X) {A : CommRingCat.{0}} {a a' b b' : Spec A ⟶ D.Y} (ea : a = a') (eb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) :
    (Scheme.ΓSpecIso A).hom.hom (D.u a b h) = (Scheme.ΓSpecIso A).hom.hom (D.u a' b' h') := by
  subst ea eb
  rfl

end GlobalTheory.CompanionTheory.FirstChernPullback

open GlobalTheory.CompanionTheory.FirstChernPullback in

theorem GlobalTheory.CompanionTheory.FirstChernPullback.firstChern_pullback : ∀ {O O' R R' : Type} [CommRing O] [CommRing O'] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O')}
    {κ : O →+* R ⧸ I} {κ' : O' →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q' κ' σ) {p : ℕ}
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q₀ : ObjectProperty (Thick (nlFun γ' p X' q' κ'))) (hQ : Used Q₀)
    (h : ∀ T, St Q₀ {⊤} T → Q ((m.mor p).obj T)) (D : E.LineData X) (N : ℕ) (z : HO Q 2) (z' : HO (St Q₀ {⊤}) 2),
    sSup (𝒱D D) = ⊤ → IsFirstChernThickening Q D N z → IsFirstChernThickening (St Q₀ {⊤}) (D.pb m.u) N z' → (m.smor Q (St Q₀ {⊤}) h).o.pull 2 z = z' := by
  intro O O' R R' _ _ _ _ I I' γ γ' X X' q q' κ κ' σ m p Q Q₀ hQ h D N z z' hD hz hz'
  let 𝒱 : Set X'.Opens := (fun V : X.Opens => m.u ⁻¹ᵁ V) '' 𝒱D D
  have h1 : St Q₀ 𝒱 ≤ St Q₀ {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, fun _ _ => trivial⟩
  have hc : ∀ W ∈ ({⊤} : Set X'.Opens), W ≤ sSup 𝒱 := by
    rintro W rfl
    exact (sSup_preimage _ m.u hD).ge
  apply (GlobalTheory.T.cech_refinement_cohomology_bijective Q₀ hQ 𝒱 {⊤} h1 hc 2).2.2.1
  let G' : (St Q₀ 𝒱).FullSubcategory ⥤ (St Q₀ {⊤}).FullSubcategory := ObjectProperty.ιOfLE h1
  let sm := m.smor Q (St Q₀ {⊤}) h
  let G'' : (St Q₀ 𝒱).FullSubcategory ⥤ Q.FullSubcategory := G' ⋙ sm.G
  have hV' : ∀ T, ∃ V ∈ 𝒱D (D.pb m.u), InU V (G'.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨_, mem_VD_pb D m.u hV, hT⟩
  have hV : ∀ T, ∃ V ∈ 𝒱D D, InU V (G''.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨V, hV, hT⟩
  obtain ⟨Λ'⟩ := GlobalTheory.T.exists_crystalline_lift (q := q') (b := nlBase R' I' γ' p) (ht := rfl) (κ := κ') (G' ⋙ (St Q₀ {⊤}).ι) (D.pb m.u) (fun T => by
    obtain ⟨V, ⟨s, hs⟩, hT⟩ := hV' T
    have hr : Set.range (pt (G'.obj T).obj) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hT (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt (G'.obj T).obj) hr ≫ s, ?_⟩
    rw [Category.assoc, hs, IsOpenImmersion.lift_fac]
    rfl)
  let Λ : B.CLift (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) (G'' ⋙ Q.ι) D :=
    { p := fun T => Λ'.p T ≫ Limits.pullback.fst D.f m.u
      hp := fun T => by
        have e := Λ'.hp T
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ m.u) e
      w := fun φ => Λ'.w φ
      hw := fun {T T'} φ hh => by
        have hh' : (B.thSp ((G' ⋙ (St Q₀ {⊤}).ι).map φ) ≫ Λ'.p T) ≫ (D.pb m.u).f = Λ'.p T' ≫ (D.pb m.u).f := by
          rw [Category.assoc, Λ'.hp T, Λ'.hp T']
          exact congrArg (fun y => y.1.2) ((G' ⋙ (St Q₀ {⊤}).ι).map φ).pt
        refine (Λ'.hw φ hh').trans ?_
        exact u_congr D (Category.assoc _ _ _) rfl _ hh }
  obtain ⟨hz1, hcl1⟩ := hz' _ G' hV' Λ'
  obtain ⟨hz2, hcl2⟩ := hz _ G'' hV Λ
  let ψ : CH.Mor (G' ⋙ CH.modF (sP (St Q₀ {⊤})).A) (CH.modF (sP (St Q₀ 𝒱)).A) (RingHom.id R') :=
    { G := 𝟭 _, τ := fun T => (incl h1).o.τ T, nat := fun φ x => (incl h1).o.nat φ x }
  let μ : CH.Mor (G'' ⋙ CH.modF (sP Q).A) (CH.modF (sP (St Q₀ 𝒱)).A) σ :=
    { G := 𝟭 _, τ := fun T => sm.o.τ (G'.obj T), nat := fun φ x => sm.o.nat (G'.map φ) x }
  have e1 : (incl h1).o.pull 2 z' = ψ.pull 2 ((CH.Mor.restrict (CH.modF (sP (St Q₀ {⊤})).A) G').pull 2 z') := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
    rfl
  have e2 : (incl h1).o.pull 2 (sm.o.pull 2 z) = μ.pull 2 ((CH.Mor.restrict (CH.modF (sP Q).A) G'').pull 2 z) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  have hE : μ.pullC 2 (Λ.coc (RingHom.id R) N) = ψ.pullC 2 (Λ'.coc (RingHom.id R') N) := by
    funext s
    rfl
  have b1 : CH.d _ 2 (ψ.pullC 2 (Λ'.coc (RingHom.id R') N)) = 0 := by
    rw [ψ.d_pullC, hz1, map_zero]
  have b2 : CH.d _ 2 (μ.pullC 2 (Λ.coc (RingHom.id R) N)) = 0 := by
    rw [μ.d_pullC, hz2, map_zero]
  have k1 : ψ.pull 2 ((CH.cx _).cls _ hz1) = (CH.cx _).cls _ b1 := CrystallineSemistableComparison.P.mapH_cls ψ.hom 2 _ hz1 b1
  have k2 : μ.pull 2 ((CH.cx _).cls _ hz2) = (CH.cx _).cls _ b2 := CrystallineSemistableComparison.P.mapH_cls μ.hom 2 _ hz2 b2
  have key : ∀ (a b : CH.Cn (CH.modF (sP (St Q₀ 𝒱)).A) 2) (ha : CH.d _ 2 a = 0) (hb : CH.d _ 2 b = 0), a = b →
      (CH.cx _).cls a ha = (CH.cx _).cls b hb := by
    rintro a _ ha hb rfl
    rfl
  rw [e1, e2, ← hcl1, ← hcl2, k1, k2]
  exact key _ _ b2 b1 hE
