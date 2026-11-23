import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianExtensionNormalModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemiabelianActionPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSabExtensionGenFibreStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegTripleExt

theorem exists_sab_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : ℕ) (φ : InvFun ℤ) (n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ) (R K : Type) [CommRing R] [Field K] (ω : R →+* K) (U Y : Scheme.{0}) (sY : Y ⟶ Sp R) (jQ : U ⟶ pullback sY (spMap ω)) (π : Y ⟶ S) (t₀ : SAB H U) (y : U ⟶ F.X) (α : t₀.G.left ⟶ F.univ.A.left) (α₂ : (G2 t₀.G).left ⟶ (G2 F.univ.A).left), 3 ≤ n → SiegData g φ n F S s j G e BD d N → IsDedFrac ω → Geo.Tor.IsNormalScheme Y → IsProjOver sY → Flat sY → IsOpenImmersion jQ → Dense (Set.range jQ) → IsFinite π → IsProper t₀.G.hom → jQ ≫ pullback.fst _ _ ≫ π = y ≫ j → IsGrpPullback t₀.G F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ t₀.G t₀.PP.L) (F.univ.P.pull α₂) → ∃ (t : SAB H Y) (m : SABMap t₀ t (jQ ≫ pullback.fst _ _)) (μ : t.G.left ⟶ G.left), IsGrpPullback t.G G π μ ∧ m.φ ≫ μ = α ≫ e ∧ abLocus t.G = π ⁻¹' abLocus G := by
  intro E _ _ _ H g φ' n F S s j _ G _ e BD d N R K _ _ ω U Y sY jQ π t₀ y α α₂ hn hSD hω hY hproj hflat hjQ hdense hπ hprop hyj hα hsq hlb
  have hG : IsSemiAbelian G := hSD.2.2.2.2.1
  haveI : IsCommMonObj G := hG.comm
  have hAG : IsGrpPullback F.univ.A G j e := hSD.2.2.2.2.2.2.1
  have hμ := isGrpPullback_pullback G π
  have semi' : IsSemiAbelian ((Over.pullback π).obj G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback π G hG
  haveI : IsCommMonObj ((Over.pullback π).obj G) := semi'.comm
  have hcomp : IsGrpPullback t₀.G G ((jQ ≫ pullback.fst _ _) ≫ π) (α ≫ e) :=
    (hα.comp hAG).congr (by rw [Category.assoc, hyj]) rfl
  let ψ : t₀.G.left ⟶ ((Over.pullback π).obj G).left :=
    pullback.lift (α ≫ e) (t₀.G.hom ≫ jQ ≫ pullback.fst _ _) (by
      have := hcomp.1.w
      simpa [Category.assoc] using this)
  have hψμ : ψ ≫ pullback.fst G.hom π = α ≫ e := pullback.lift_fst _ _ _
  have hψ : IsGrpPullback t₀.G ((Over.pullback π).obj G) (jQ ≫ pullback.fst _ _) ψ :=
    hμ.cancel (hcomp.congr rfl hψμ.symm) (pullback.lift_snd _ _ _)
  obtain ⟨act, hact⟩ := GlobalTheory.T.semiabelian_extension_normal_model E H R K ω U Y sY jQ _ t₀ ψ hω hY hproj hflat hjQ hdense semi' hψ
  obtain ⟨M, hM, hMψ⟩ := GlobalTheory.T.semiabelian_action_pullback E H g φ' n F S s j G e BD d N U Y (jQ ≫ pullback.fst _ _) π _ _ act t₀ y α α₂ ψ
    hSD (by rw [Category.assoc, hyj]) hμ hψ hψμ hact hα hsq hlb
  obtain ⟨PP, cub, h₁, h₂', h₃, m, hm⟩ :=
    GlobalTheory.T.semiabelian_action_extends_alt E H R K ω U Y sY jQ _ semi' act t₀ ψ hω hY hproj hflat hjQ hdense hprop hψ hact M hM hMψ
  refine ⟨SAB.mk _ semi' act PP cub h₁ h₂' h₃, m, pullback.fst G.hom π, hμ, by rw [hm]; exact hψμ, ?_⟩
  ext x
  exact (GlobalTheory.OneArcCompare.mem_abLocus_pullback hG hμ.1 x).symm

end GlobalTheory.SiegTripleExt
