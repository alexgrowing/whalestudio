import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ShiftExp

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·) (gs_res r z le_top (hJ.mem _ r) _) rfl)

theorem gs_scal {Y Z : Scheme.{0}} {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem shift (hG : GlobalFnsSt) (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]
    (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) (hx : U.TorPt a x) (e : ℕ) (Z : Scheme.{0})
    (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left)
    (h₁ : rG ≫ (snd _ G).left = y ≫ (fstG I e G).left)
    (h₂ : y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left) :
    y' ≫ (U.gt e).pG.left = y ≫ (U.gt e).pG.left ∧ ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J →
      (val ((U.gt e).t χ) y' z J).val =
        gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd χ)).val) *
          (val ((U.gt e).t χ) y z J).val := by
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let yo : T ⟶ thickObj R I e G := Over.homMk y rfl
  have hb : rG ≫ (TA R W ⊗ G).hom = T.hom ≫ thick R I e := by
    rw [← Over.w (snd (TA R W) G), ← Category.assoc, h₁, Category.assoc, Over.w (fstG I e G)]
    exact (Category.assoc _ _ _).symm
  let ro : Over.mk (T.hom ≫ thick R I e) ⟶ TA R W ⊗ G := Over.homMk rG hb
  let x₀ : Over.mk (T.hom ≫ thick R I e) ⟶ G := ro ≫ fst _ _ ≫ x
  let xe : T ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift x₀.left T.hom (Over.w x₀)) (pullback.lift_snd _ _ _)
  have hxe : xe.left ≫ pullback.fst G.hom (thick R I e) = x₀.left := pullback.lift_fst _ _ _
  have hm := (isGrpPullback_pullback G (thick R I e)).2 T xe yo x₀ (ro ≫ snd _ _) hxe.symm h₁
  have ht : ro ≫ translPt G x = x₀ * (ro ≫ snd _ _) := MonObj.comp_mul ro (fst _ _ ≫ x) (snd _ _)
  have hf : y' ≫ pullback.fst G.hom (thick R I e) = (xe * yo).left ≫ pullback.fst G.hom (thick R I e) :=
    h₂.trans ((congrArg (fun q => q.left) ht).trans hm)
  haveI : Mono (thick R I e) := by
    haveI : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hy : y' = (xe * yo).left := (cancel_mono (pullback.fst G.hom (thick R I e))).1 hf
  obtain ⟨p₁, p₂⟩ := hx e Z (rG ≫ (fst (TA R W) G).left) xe.left (hxe.trans (Category.assoc _ _ _).symm)
  have hone : GlobalTheory.TorusCoord.im (U.gt e) xe = 1 := by
    have : (ro ≫ fst _ _) ≫ (1 : TA R W ⟶ D.P.A) = 1 := MonObj.comp_one _
    exact (Over.OverMorphism.ext p₁).trans this
  subst hy
  refine ⟨?_, fun χ z J hJ => ?_⟩
  · have := GlobalTheory.TorusCoord.im_mul (U.gt e) xe yo
    rw [hone, _root_.one_mul] at this
    exact congrArg (fun q => q.left) this
  · have k := GlobalTheory.TorusCoord.val_t_mul_points (U.gt e) hG χ xe yo z J hJ
    have c : GlobalTheory.TorusCoord.cubeVal (U.gt e) χ z J xe yo = 1 := by
      unfold GlobalTheory.TorusCoord.cubeVal
      rw [hone]
      exact (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ).face₂ _ _
    rw [c, _root_.mul_one] at k
    exact (congrArg Units.val k).trans ((Units.val_mul _ _).trans (congrArg (· * _) (p₂ χ z J hJ)))

end GlobalTheory.UU.ShiftExp

theorem GlobalTheory.UU.expansion_translate_torus : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (W : Type) [CommRing W] [Algebra R W] (a : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G), U.TorPt a x → ∀ (k : ℕ) (σ : U.SecGT (TA R W) k) (f : ∀ α, SecBT D (TA R W) k α), U.ExpT (TA R W) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ (Z : Scheme.{0}) (y y' : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (TA R W ⊗ G).left) (rB : Z ⟶ (TA R W ⊗ D.P.A).left), rG ≫ (snd _ G).left = y ≫ (fstG I e G).left → rB ≫ (snd _ D.P.A).left = y ≫ (U.gt e).pG.left → rB ≫ (fst _ D.P.A).left = rG ≫ (fst _ G).left → y' ≫ (fstG I e G).left = rG ≫ (translPt G x).left → ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J → (∀ α ∉ s, sval (twist a f α) rB z J = 0) ∧ (U.wv e y' z JG J).val ^ k * sval σ (rG ≫ (translT G x).left) z JG = ∑ α ∈ s, sval (twist a f α) rB z J * (val ((U.gt e).t α) y z J).val := by
  intro hG R _ _ I D A G _ _ U W _ _ a x hx k σ f hf e
  obtain ⟨s, hs⟩ := hf e
  refine ⟨s, fun Z y y' rG rB h₁ h₂ h₃ h₄ z JG J hJG hJ => ?_⟩
  obtain ⟨p₁, p₂⟩ := ShiftExp.shift hG U a x hx e Z y y' rG h₁ h₄
  have e₁ : (translT G x).left ≫ (snd (TA R W) G).left = (translPt G x).left :=
    congrArg (fun q => q.left) (lift_snd (fst (TA R W) G) (translPt G x))
  have e₂ : (translT G x).left ≫ (fst (TA R W) G).left = (fst (TA R W) G).left :=
    congrArg (fun q => q.left) (lift_fst (fst (TA R W) G) (translPt G x))
  obtain ⟨q₁, q₂⟩ := hs Z y' (rG ≫ (translT G x).left) rB (by rw [Category.assoc, e₁, h₄]) (h₂.trans p₁.symm)
    (by rw [Category.assoc, e₂, h₃]) z JG J hJG hJ
  have tw : ∀ α, sval (twist a f α) rB z J =
      gs (𝟙 Z) z ⊤ (scal (R := W) (rG ≫ (fst (TA R W) G).left) (a (Multiplicative.ofAdd α)).val) *
        sval (f α) rB z J := fun α => by
    rw [← h₃]
    exact (ShiftExp.sval_secScale _ _ rB z hJ).trans (congrArg (· * _) (ShiftExp.gs_scal _ rB z _))
  refine ⟨fun α hα => by rw [tw, q₁ α hα, mul_zero], q₂.trans (Finset.sum_congr rfl fun α _ => ?_)⟩
  rw [tw, p₂ α z J hJ]
  ring
