import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.UnivFibre

theorem exists_fibre_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), σ (baseKA l).ρ = H.rt0 → g = Module.finrank ℚ E / 2 * (D.p + D.q) → IsPeriod (U.Di i) ty P → ∃ (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (m : SABMap t Xo.univ.t (U.u i P)), (∀ z, (e z).left ≫ m.φ = (U.ex i P z).left) ∧ (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond (U.Di i) t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : (U.Di i).La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((U.Di i).EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  intro E _ _ _ H D l Xo σ g ty U i P hσ hg hP
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp ℂ), Nonempty (SABMap t Xo.univ.t (U.u i P)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (U.u i P) Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  have hL : LBIso t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨π, hπ⟩ := LiePull.exists_pushEquiv m.cart (𝟙_ (Over (Sp ℂ))) (U.u i P) (Category.id_comp _).symm
  have he : ∀ z, (π.symm (U.ex i P z)).left ≫ m.φ = (U.ex i P z).left := fun z => by
    rw [← hπ, π.apply_symm_apply]
  obtain ⟨ha, hk⟩ := amplePt _ ℂ (U.u i P) Xo.univ.t.G t.G m.φ m.cart _ _ Xo.univ.t.PP.isLB t.PP.isLB hL
    Xo.univ.ample Xo.univ.ktriv
  have hdet := (Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)).1
  rw [hσ] at hdet
  refine ⟨t, fun z => π.symm (U.ex i P z), m, he,
    MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper, ?_, ha, hk, fun τ => ?_,
    fun z w => (congrArg π.symm (U.ex_add i P hP z w)).trans (map_mul π.symm _ _), π.symm.surjective.comp (U.ex_onto i P hP),
    fun z => by rw [← U.ex_ker i P hP z, map_eq_one_iff _ π.symm.injective], fun a z => ?_, ?_,
    fun k a b c hk hc => ?_⟩
  · rw [hg]
    have := smoothOfRelativeDimension_isStableUnderBaseChange (Module.finrank ℚ E / 2 * (D.p + D.q))
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension _) m.cart.1
      (ObjDim.smoothOfRelativeDimension Xo.univ)
  · rw [LiePull.lieMult_pull _ _ _ Xo.univ.t.G t.G _ m.φ Xo.univ.t.act t.act m.cart m.act,
      LiePull.lieMult_pull _ _ _ Xo.univ.t.G t.G _ m.φ Xo.univ.t.act t.act m.cart m.act, Category.id_comp,
      (U.sig i).1, (U.sig i).2]
    exact hdet τ
  · apply π.injective
    rw [π.apply_symm_apply, U.ex_lin i P hP]
    apply Over.OverMorphism.ext
    rw [hπ, Over.comp_left, Over.comp_left, Category.assoc, ← he z, Category.assoc]
    exact congrArg _ (m.act a).symm
  · refine HolTorsion.isHolTo_of_isPullback m.cart.1
      (HolTorsion.isHolTo_congr (HolHom.isHolTo_ex U i hP) fun z _ => he z)
      (HolTorsion.isHolTo_congr (c := fun _ => 𝟙 (Sp ℂ))
        (HolHom.isHolTo_of_holAt isOpen_univ fun z _ => HolHom.holAt_const _ _)
        fun z _ => Over.w (π.symm (U.ex i P z)))
  · have h := U.ex_weil i P hP k a b c hk hc
    have key : ∀ (y : Sp ℂ ⟶ Xo.X) (_ : y = (𝟙_ (Over (Sp ℂ))).hom ≫ U.u i P) (x₀ y₀ : Over.mk y ⟶ Xo.univ.t.G)
        (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ t.G), x.left ≫ m.φ = x₀.left → x'.left ≫ m.φ = y₀.left →
        Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k x₀ y₀ (unitOn c) → Out.WeilIs t.G t.PP.L k x x' (unitOn c) := by
      rintro y rfl x₀ y₀ x x' h₁ h₂ h₃
      exact (weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ Xo.univ.t.PP.isLB t.PP.isLB m.cart hL _ k x x' x₀ y₀ _
        h₁.symm h₂.symm).2 h₃
    exact key _ (Category.id_comp _).symm _ _ _ _ (he _) (he _) h

end GlobalTheory.UnivFibre
