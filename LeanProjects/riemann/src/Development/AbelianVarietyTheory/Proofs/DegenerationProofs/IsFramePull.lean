import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.Mono

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_pull {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨_, fun Z r z J hJ => ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem isFrame_pull {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {R₁ R₂ : Type} [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂)
    (hh : ∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) (x : Sp (FractionRing R₁) ⟶ S)
    (x' : Sp (FractionRing R₂) ⟶ S) (hx : spMap h' ≫ x = x') {n : ℕ} (f : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x)))
    (hf : GlobalTheory.LN.IsFrame G L N x f) : ∃ f', GlobalTheory.LN.IsFrame (n := n) G L N x' f' := by
  let ρ : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap h') hx
  have e : ∀ _ : Fin 1, (ρ ▷ G).left ≫ (snd (Over.mk x) G).left = (snd (Over.mk x') G).left := fun _ => by
    rw [← Over.comp_left, whiskerRight_snd]
  choose f' hf' using fun i => exists_pull (L := L) (φ := fun _ : Fin 1 => (snd (Over.mk x) G).left)
    (φ' := fun _ : Fin 1 => (snd (Over.mk x') G).left) (ε := fun _ => (N : ℤ)) (f i) (ρ ▷ G).left e
  refine ⟨f', fun W _ _ _ hW φ gam hg χ hχ => ?_⟩
  have hχ' : spMap (gam.comp h') ≫ x = jK W ≫ χ := by rw [sp_comp, Category.assoc, hx, hχ]
  obtain ⟨b', hb, hs⟩ := hf W hW (φ.comp h) (gam.comp h') (fun r => by
    rw [RingHom.comp_apply, hh, hg, RingHom.comp_apply]) χ hχ'
  refine ⟨b', hb, fun i => ?_⟩
  obtain ⟨s, h₁, h₂⟩ := hs i
  refine ⟨s, fun z J hJ => (h₁ z J hJ).trans ?_, h₂⟩
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  refine congrArg _ (Eq.trans ?_ (hf' i _ _ z J hJ).symm)
  have hc : (Over.homMk (spMap (gam.comp h')) hχ' : Over.mk (jK W ≫ χ) ⟶ Over.mk x) =
      (Over.homMk (spMap gam) hχ : Over.mk (jK W ≫ χ) ⟶ Over.mk x') ≫ ρ := Over.OverMorphism.ext (sp_comp h' gam)
  rw [hc, comp_whiskerRight, Over.comp_left]

theorem mono : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂), h.Finite → (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) → (GlobalTheory.LN.TraitData Y a g y₁ → GlobalTheory.LN.TraitData Y a (h.comp g) (spMap h' ≫ y₁)) ∧ (RealAt Y a g y₁ → RealAt Y a (h.comp g) (spMap h' ≫ y₁)) ∧ ∀ (N n : ℕ) f, GlobalTheory.LN.IsFrame (n := n) Y.t.G Y.t.PP.L N (y₁ ≫ Y.j) f → ∃ f', GlobalTheory.LN.IsFrame (n := n) Y.t.G Y.t.PP.L N ((spMap h' ≫ y₁) ≫ Y.j) f' := by
  intro _ _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a _ R₁ _ _ g y₁ _ _ _ R₂ _ _ h h' hfin hh
  refine ⟨fun hT => ⟨?_, fun W _ _ _ hW φ gam hg χ hχ => ?_⟩, fun hR => hR.comp h h' hfin hh,
    fun N n f hf => isFrame_pull _ _ N h h' hh _ _ (Category.assoc _ _ _).symm f hf⟩
  · have e : spMap h' ≫ jK R₁ = jK R₂ ≫ spMap h :=
      (sp_comp (algebraMap R₁ _) h').symm.trans ((congrArg spMap (RingHom.ext hh)).trans (sp_comp h (algebraMap R₂ _)))
    rw [Category.assoc, hT.1, sp_comp, ← Category.assoc, e]
    simp only [Category.assoc]
  · exact hT.2 W hW (φ.comp h) (gam.comp h') (fun r => by rw [RingHom.comp_apply, hh, hg, RingHom.comp_apply]) χ
      (by rw [sp_comp, Category.assoc, ← hχ, Category.assoc])

end GlobalTheory.Ex.Mono
end
