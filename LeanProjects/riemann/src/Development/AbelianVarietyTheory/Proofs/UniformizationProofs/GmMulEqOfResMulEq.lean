import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem gm_mul_eq_of_res_mul_eq {Y Z : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂}
    {h₃ : V ≤ U₃} {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : res h₁ a * res h₂ b = res h₃ c * res h₄ d) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ V) :
    gm r z U₁ a * gm r z U₂ b = gm r z U₃ c * gm r z U₄ d := by
  have e := congrArg (gm r z V) H
  rwa [map_mul, map_mul, gm_res r z h₁ hz, gm_res r z h₂ hz, gm_res r z h₃ hz, gm_res r z h₄ hz] at e

theorem res_mul_eq_of_gm_mul_eq {Y : Scheme.{0}} {V U₁ U₂ U₃ U₄ : Y.Opens} {h₁ : V ≤ U₁} {h₂ : V ≤ U₂}
    {h₃ : V ≤ U₃} {h₄ : V ≤ U₄} {a : Γ(Y, U₁)ˣ} {b : Γ(Y, U₂)ˣ} {c : Γ(Y, U₃)ˣ} {d : Γ(Y, U₄)ˣ}
    (H : ∀ y ∈ V, gm (𝟙 Y) y U₁ a * gm (𝟙 Y) y U₂ b = gm (𝟙 Y) y U₃ c * gm (𝟙 Y) y U₄ d) :
    res h₁ a * res h₂ b = res h₃ c * res h₄ d := by
  apply unit_ext
  intro y hy
  rw [map_mul, map_mul, gm_res (𝟙 Y) y h₁ hy, gm_res (𝟙 Y) y h₂ hy, gm_res (𝟙 Y) y h₃ hy,
    gm_res (𝟙 Y) y h₄ hy]
  exact H y hy

theorem square_res_iff_gw {X X' G G' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {L : LB G} {L' : LB G'}
    {F : X' ⟶ X} {B : G' ⟶ G} {p : Y ⟶ X} {p' : Y' ⟶ X'} {f : Y ⟶ G} {f' : Y' ⟶ G'} {h : Y' ⟶ Y}
    (hf : h ≫ f = f' ≫ B) (hp : p' ≫ F = h ≫ p)
    (wM : LB.Iso M' (M.pull F)) (wL : LB.Iso L' (L.pull B))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) :
    (∀ (jM : PUnit → M.ι) (jM' : M'.ι) (jL' : L'.ι) (jL : PUnit → L.ι),
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_left) :
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM') ⊓
            (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') ⊓
            h ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (jM, jL) ⊓
            f' ⁻¹ᵁ (LB.div (L.pull B) L').U (jL, jL') ≤
          p' ⁻¹ᵁ (LB.div (M.pull F) M').U (jM, jM'))
        (pullU p' _ (wM.s (jM, jM'))) *
      res (X := Y') (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (w'.s (fun _ => jM', fun _ => jL')) =
      res (X := Y') (inf_le_left.trans inf_le_right) (pullU h _ (w.s (jM, jL))) *
      res (X := Y') inf_le_right (pullU f' _ (wL.s (jL, jL')))) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      F (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → B (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL' := by
  have ef : ∀ y : Y', f (h y) = B (f' y) := fun y => congrArg (fun g => g y) hf
  have ep : ∀ y : Y', p (h y) = F (p' y) := fun y => congrArg (fun g => g y) hp.symm
  constructor
  · intro H Z r z jM jM' jL jL' h₁ h₂ h₃ h₄
    have m₁ : p' (r z) ∈ (LB.div (M.pull F) M').U (fun _ => jM, jM') := ⟨mem_pull.2 h₁, h₂⟩
    have m₂ : r z ∈ (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') :=
      ⟨mem_pull.2 h₂, mem_pull.2 h₄⟩
    have m₃ : h (r z) ∈ (LB.div (M.pull p) (L.pull f)).U (fun _ => jM, fun _ => jL) :=
      ⟨mem_pull.2 (by rw [ep]; exact h₁), mem_pull.2 (by rw [ef]; exact h₃)⟩
    have m₄ : f' (r z) ∈ (LB.div (L.pull B) L').U (fun _ => jL, jL') := ⟨mem_pull.2 h₃, h₄⟩
    have e := gm_mul_eq_of_res_mul_eq (H (fun _ => jM) jM' jL' (fun _ => jL)) r z ⟨⟨⟨m₁, m₂⟩, m₃⟩, m₄⟩
    rw [gm_pull r p' z _ m₁, gm_pull r h z _ m₃, gm_pull r f' z _ m₄] at e
    exact e
  · intro H jM jM' jL' jL
    refine res_mul_eq_of_gm_mul_eq fun y hy => ?_
    have e := H Y' (𝟙 Y') y (jM PUnit.unit) jM' (jL PUnit.unit) jL' (mem_pull.1 hy.1.1.1.1) hy.1.1.1.2
      (mem_pull.1 hy.2.1) hy.2.2
    rw [gm_pull (𝟙 Y') p' y _ hy.1.1.1, gm_pull (𝟙 Y') h y _ hy.1.2, gm_pull (𝟙 Y') f' y _ hy.2]
    exact e

theorem isPullUnif_iff_stalks : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' ↔ ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wL.IsGen ∧ ∃ he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G, LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) ∧ ∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL') := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc U U'
  constructor
  · rintro ⟨wL, hg, he, hr, H⟩
    refine ⟨wL, hg, he, hr, fun e => ?_⟩
    obtain ⟨h, hf, hp, ht, hw⟩ := H e
    refine ⟨h, hf, ⟨hp, fun x => ?_⟩, (square_res_iff_gw hf hp hD.w wL (U.w e) (U'.w e)).1 hw⟩
    obtain ⟨hψ, hm⟩ := ht x
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ h _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1 hm⟩
  · rintro ⟨wL, hg, he, hr, H⟩
    refine ⟨wL, hg, he, hr, fun e => ?_⟩
    obtain ⟨h, hf, ⟨hp, ht⟩, hw⟩ := H e
    refine ⟨h, hf, hp, fun x => ?_, (square_res_iff_gw hf hp hD.w wL (U.w e) (U'.w e)).2 hw⟩
    obtain ⟨hψ, hm⟩ := ht x
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ h _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2 hm⟩

end GlobalTheory
