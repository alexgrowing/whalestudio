import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Tors

theorem torsion_exhaust_geometric : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → IsUnit (N : R) → ∀ (C : Type) (b : C → (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A)), (∀ c, b c ^ N = 1) → (∀ p : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (p : Over.mk x ⟶ P.A), p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c := by
  intro hL R _ _ _ P N hN1 hNu C b hb hgen K _ _ x p hp
  have hNu' : IsUnit (N : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hNu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨hfin, -, -, het, hcard⟩ := hL.mulN (Spec (CommRingCat.of R)) P N hN1
  have : Etale (mulA P.A N).left := het hNu'
  have : IsSeparated (mulA P.A N).left := inferInstance
  have hmul : ∀ {Z : Over (Spec (CommRingCat.of R))} (y : Z ⟶ P.A), y ≫ mulA P.A N = y ^ N := fun y => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over (Spec (CommRingCat.of R))}, (1 : Z ⟶ P.A).left = Z.hom ≫ η[P.A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  let Kk : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.snd (mulA P.A N).left η[P.A].left)
  have hη : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  let i : Kk ⟶ P.A := Over.homMk (pullback.fst (mulA P.A N).left η[P.A].left) (by
    change pullback.fst (mulA P.A N).left η[P.A].left ≫ P.A.hom = pullback.snd (mulA P.A N).left η[P.A].left
    rw [← Over.w (mulA P.A N), pullback.condition_assoc]
    erw [hη]
    exact Category.comp_id _)
  have hlift : ∀ {Z : Over (Spec (CommRingCat.of R))} (y : Z ⟶ P.A), y ^ N = 1 → ∃ l : Z ⟶ Kk, l ≫ i = y := by
    intro Z y hy
    have e : y.left ≫ (mulA P.A N).left = Z.hom ≫ η[P.A].left := by
      rw [← Over.comp_left, hmul, hy, hone]
    exact ⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hmono : ∀ {Z : Over (Spec (CommRingCat.of R))} (l l' : Z ⟶ Kk), l ≫ i = l' ≫ i → l = l' := by
    intro Z l l' e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congr(($e).left)
    · exact (Over.w l).trans (Over.w l').symm
  have : Etale Kk.hom := inferInstanceAs (Etale (pullback.snd (mulA P.A N).left η[P.A].left))
  have : IsSeparated Kk.hom := inferInstanceAs (IsSeparated (pullback.snd (mulA P.A N).left η[P.A].left))

  have inj : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R))
      (σ τ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A), σ ^ N = 1 → τ ^ N = 1 →
      toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ τ → σ = τ := by
    intro F _ y σ τ hσ hτ e
    obtain ⟨ls, rfl⟩ := hlift σ hσ
    obtain ⟨lt, rfl⟩ := hlift τ hτ
    have e' : toUnit (Over.mk y) ≫ ls = toUnit (Over.mk y) ≫ lt := hmono _ _ (by simpa using e)
    have hu : (toUnit (Over.mk y)).left = y := by
      simpa using Over.w (toUnit (Over.mk y))
    have : ConnectedSpace (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
      inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of R)))
    have key : ls.left = lt.left := by
      refine GlobalTheory.eq_of_connected_of_unramified_of_point Kk.hom
        ((Over.w ls).trans (Over.w lt).symm) y ?_
      have h2 := congr(($e').left)
      rw [Over.comp_left, Over.comp_left, hu] at h2
      exact h2
    rw [Over.OverMorphism.ext key]
  have natK : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)), (N : F) ≠ 0 :=
    fun y => by simpa using (hNu.map (Spec.preimage y).hom).ne_zero
  let T0 := {σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A // σ ∈ Set.range b}
  have tor : ∀ σ : T0, σ.1 ^ N = 1 := fun σ => by obtain ⟨c, hc⟩ := σ.2; rw [← hc]; exact hb c
  let res : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      T0 → {q : Over.mk y ⟶ P.A // q ^ N = 1} := fun y σ =>
    ⟨toUnit _ ≫ σ.1, by rw [← MonObj.comp_pow, tor σ, MonObj.comp_one]⟩
  have resInj : ∀ {F : Type} [Field F] (y : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      Function.Injective (res y) := fun y σ τ e =>
    Subtype.ext (inj y σ.1 τ.1 (tor σ) (tor τ) (congrArg Subtype.val e))
  let Ω := AlgebraicClosure (FractionRing R)
  have c0 := hcard Ω (TF (R := R) Ω).hom (natK (TF (R := R) Ω).hom)
  have cx := hcard K x (natK x)
  have hpos : N ^ (2 * P.g) ≠ 0 := pow_ne_zero _ (by omega)
  have : Finite {q : Over.mk (TF (R := R) Ω).hom ⟶ P.A // q ^ N = 1} := Nat.finite_of_card_ne_zero (c0 ▸ hpos)
  have : Finite {q : Over.mk x ⟶ P.A // q ^ N = 1} := Nat.finite_of_card_ne_zero (cx ▸ hpos)
  have bij0 : Function.Bijective (res (TF (R := R) Ω).hom) := by
    refine ⟨resInj _, fun q => ?_⟩
    obtain ⟨c, hc⟩ := hgen q.1 q.2
    exact ⟨⟨b c, c, rfl⟩, Subtype.ext hc.symm⟩
  have cT : Nat.card T0 = N ^ (2 * P.g) := (Nat.card_eq_of_bijective _ bij0).trans c0
  have bijx := (Nat.bijective_iff_injective_and_card (res x)).2 ⟨resInj x, cT.trans cx.symm⟩
  obtain ⟨⟨σ, c, rfl⟩, hσ⟩ := bijx.2 ⟨p, hp⟩
  exact ⟨c, (congrArg Subtype.val hσ).symm⟩

end GlobalTheory.Poinc.Tors
