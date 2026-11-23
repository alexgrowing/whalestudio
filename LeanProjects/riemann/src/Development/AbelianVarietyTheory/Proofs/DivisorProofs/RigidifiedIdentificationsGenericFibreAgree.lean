import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GenEqual

theorem key {X₁ X₂ X₃ XE S₁ S₂ S₃ SE : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {L₃ : LB X₃} {LE : LB XE}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) (hLE : LE.IsLB)
    (Fp : X₃ ⟶ X₁) (Φ : X₃ ⟶ X₂) (κ : XE ⟶ X₃)
    (e₁ : S₁ ⟶ X₁) (e₂ : S₂ ⟶ X₂) (e₃ : S₃ ⟶ X₃) (eE : SE ⟶ XE)
    (t₁ : S₃ ⟶ S₁) (t₂ : S₃ ⟶ S₂) (sE : SE ⟶ S₃) (pE : XE ⟶ SE) (hpE : eE ≫ pE = 𝟙 _)
    (hsurj : Function.Surjective pE.appTop.hom) (hc : eE ≫ κ = sE ≫ e₃)
    (r₁ : LB.Gen (L₁.pull e₁)) (r₂ : LB.Gen (L₂.pull e₂)) (r₃ : LB.Gen (L₃.pull e₃)) (rE : LB.Gen (LE.pull eE))
    (wp : LB.Iso L₃ (L₁.pull Fp)) (w : LB.Iso L₃ (L₂.pull Φ)) (F₁ : XE ⟶ X₁) (F₂ : XE ⟶ X₂) (h₁ : κ ≫ Fp = F₁) (h₂ : κ ≫ Φ = F₂) (u₁ : LB.Iso LE (L₁.pull F₁))
    (u₂ : LB.Iso LE (L₂.pull F₂)) (gp : PGen wp) (gw' : PGen w) (g₁ : PGen u₁) (g₂ : PGen u₂)
    (mp : PMaps wp (K := PUnit) (fun _ => e₃) (fun _ => e₁) (fun _ => 1) r₃ r₁ t₁)
    (mw : PMaps w (K := PUnit) (fun _ => e₃) (fun _ => e₂) (fun _ => 1) r₃ r₂ t₂)
    (m₁ : PMaps u₁ (K := PUnit) (fun _ => eE) (fun _ => e₁) (fun _ => 1) rE r₁ (sE ≫ t₁))
    (m₂ : PMaps u₂ (K := PUnit) (fun _ => eE) (fun _ => e₂) (fun _ => 1) rE r₂ (sE ≫ t₂))
    (Z : Scheme.{0}) (f : Z ⟶ XE) (z : Z) (j : L₂.ι) (i : L₃.ι) (k : LE.ι) (l : L₁.ι)
    (hj : F₂ (f z) ∈ L₂.U j) (hi : κ (f z) ∈ L₃.U i) (hk : f z ∈ LE.U k) (hl : F₁ (f z) ∈ L₁.U l) :
    gw w (f ≫ κ) z j i * (gw wp (f ≫ κ) z l i)⁻¹ = gw u₂ f z j k * (gw u₁ f z l k)⁻¹ := by
  subst h₁ h₂
  obtain ⟨v, Tv⟩ := exists_cancel hL₁ wp u₁ gp g₁ hL₃ hLE
  have gv := Tv.pgen_cancel hL₁ gp g₁
  have rv := Tv.pmaps_cancel hL₁ (fun _ => hc) mp m₁
  obtain ⟨u, Tu⟩ := exists_comp hL₃ w v gw' gv hL₂ hLE
  have gu := Tu.pgen_comp hL₃ gw' gv
  have ru := Tu.pmaps_comp hL₃ (fun _ => hc) mw rv
  have e := GlobalTheory.OverMove.gw_eq_of_pmaps hL₂ hLE pE eE hpE hsurj rfl gu g₂ rfl ru m₂ f z j k
  rw [← e, Tu Z f z j i k hj hi hk, Tv Z f z l i k hl hi hk]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem genequal : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w → PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) → ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  intro R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ _ hκ hκp hκΦ w hw hr Z f z j i k l hj hi hk hl
  have hs : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
  have m₁ := GlobalTheory.FieldPull.pmaps_rig q₁
  have m₂ := GlobalTheory.FieldPull.pmaps_rig q₂
  rw [hs] at m₁ m₂
  exact key D₁.P.isLB D₂.P.isLB D₃.P.isLB E.P.isLB (GlobalTheory.PsiEvenPull.proj p) Φ κ (eSec D₁.P.A) (eSec D₂.P.A)
    (eSec D₃.P.A) (eSec E.P.A) (spMap ρ) (spMap ρ) (spMap (algebraMap R' (FractionRing R'))) E.P.A.hom
    (Over.w η[E.P.A]) (GlobalTheory.globalFns_holds _ E.P.A E.P.isAb).2 (cubeMapOf hκ).e_comm D₁.rig D₂.rig D₃.rig E.rig
    p.w w _ _ hκp hκΦ q₁.w q₂.w ((isGen_iff _).1 p.w_gen) hw ((isGen_iff _).1 q₁.w_gen) ((isGen_iff _).1 q₂.w_gen)
    (GlobalTheory.FieldPull.pmaps_rig p) hr m₁ m₂ Z f z j i k l hj hi hk hl

end GlobalTheory.GenEqual
