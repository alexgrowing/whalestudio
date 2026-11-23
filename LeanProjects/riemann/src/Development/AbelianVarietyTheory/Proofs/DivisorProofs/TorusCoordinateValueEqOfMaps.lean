import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValTorusPointAndTranslate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem val_eq_of_maps_pullAlong {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (F : X ⟶ X) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (W : LB.Iso (LB.LinComb L φ ε) (LB.LinComb (L.pull F) φ ε)) (a t : LB.Gen (LB.LinComb L φ ε))
    (f f' : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k) (hψ' : ∀ k, φ k ≫ F = f' ≫ φ k)
    (h : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f φ ε φ hψ t)) (h' : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f' φ ε φ hψ' t))
    (z : Y) (J : (Y ⟶ X) → L.ι) (hJ : Good L z J) : val t f z J = val t f' z J := by
  let jj : K → (L.pull F).ι := fun k _ => J (φ k ≫ F)
  let q : K → L.ι := fun k => J (φ k)
  have m₁ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ (φ k ≫ F)
  have m₂ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart L φ q := Set.mem_iInter.2 fun k => hJ (φ k)
  have m : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q := ⟨m₁, m₂⟩
  have key : ∀ (f : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k),
      val t f z J = gm (𝟙 Y) z _ (res (inf_le_left : LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q ≤ _)
        ((GeneratorPullback.pullAlong L F f φ ε φ hψ t).s jj)) := by
    intro f hψ
    rw [val_of t f z J (fun k => J (φ k ≫ F)) (fun k => by rw [hψ k])]
    exact ((gm_res (𝟙 Y) z _ m _).trans ((gm_res (𝟙 Y) z _ m₁ _).trans
      (gm_pull (𝟙 Y) f z _ (@GeneratorPullback.pullAlong_le _ _ _ _ L _ _ F f φ φ hψ jj z m₁) _))).symm
  rw [key f hψ, key f' hψ']
  exact congrArg (gm (𝟙 Y) z _) ((h (jj, q)).trans (h' (jj, q)).symm)

theorem gtCoord_val_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J :=
  fun g F _ f f' x hψ hψ' h h' z J hJ => val_eq_of_maps_pullAlong F _ Oinvε _ (g.t x) (g.t x) f f' hψ hψ' h h' z J hJ

end GlobalTheory.Mum
