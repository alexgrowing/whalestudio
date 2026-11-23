import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfExtensionLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTypeOfExtensionLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionOfJumpsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.ExtGood

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l}
  [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l)

abbrev ext (T : QLat LL) (z : ↥(latticeCocycles T.L)) : QLat LL :=
  GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z

theorem aeval_mul_eq_zero {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (A : Module.End K M)
    (p q : Polynomial K) (x : M) (h : Polynomial.aeval A q x = 0) : Polynomial.aeval A (p * q) x = 0 := by
  rw [map_mul, Module.End.mul_apply, h, map_zero]

theorem isGood_mono (T : QLat LL) {Sig : Finset (ZMod e)} {U : Finset ℤ} (h : IsGood a ϖ Pl T {0} {0})
    (hS : (0 : ZMod e) ∈ Sig) (hU : (0 : ℤ) ∈ U) : IsGood a ϖ Pl T Sig U := by
  refine ⟨h.crys, fun g hg w hw x hx => ?_, fun τ j hj => ?_⟩
  · have h1 := h.type g hg w hw x hx
    rw [Finset.prod_singleton] at h1
    rw [← Finset.prod_erase_mul _ _ hS]
    exact aeval_mul_eq_zero _ _ _ _ h1
  · have h2 := h.jumps τ j hj
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at h2
    subst h2
    exact hU

def incl (T : QLat LL) (z : ↥(latticeCocycles T.L)) : LatHom T.L (ext T z).L where
  f := LinearMap.inl ↥LL.1 T.V ↥LL.1
  equiv g x := by
    change ((T.ρ g x, 0) : T.V × ↥LL.1) = (T.ρ g x + (0 : ↥LL.1) • (z : Gl l → T.V) g, 0)
    simp
  cont := continuous_id.prodMk continuous_const
  T_le x hx := ⟨hx, 0, map_zero _⟩

def proj (T : QLat LL) (z : ↥(latticeCocycles T.L)) : LatHom (ext T z).L (unitLat (Gl l) : QLat LL).L where
  f := LinearMap.snd ↥LL.1 T.V ↥LL.1
  equiv g x := rfl
  cont := continuous_snd
  T_le x hx := hx.2

theorem extLat_isGood : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ), (0 : ZMod e) ∈ Sig → (0 : ℤ) ∈ U → IsGood a ϖ Pl (unitLat (Gl l) : QLat LL) Sig U ∧ ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ (Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L) (v : Tp.V), IsSESLat (Qp := ℚ_[l]) f g ∧ v ∈ Tp.L.T ∧ g.f v = (1 : ↥LL.1) ∧ (∀ h, Tp.ρ h v - v = f.f (c h)) ∧ IsGood a ϖ Pl Tp Sig U := by
  intro _ l _ a e _ _ ϖ LL _ _ Pl AI hstd Sig U hS hU
  refine ⟨isGood_mono ϖ Pl _ (UnitModel.isGood_of_trivial ϖ Pl _ fun _ _ => rfl) hS hU, fun T hT c hc => ?_⟩
  let z : ↥(latticeCocycles T.L) := ⟨c, hc.1⟩
  have hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ := hc.2
  have hcr := GlobalTheory.T.crystalline_of_extension_lattice ϖ Pl T hT.crys z hz
  refine ⟨ext T z, incl T z, proj T z, ((0 : T.V), (1 : ↥LL.1)), ⟨LinearMap.inl_injective,
    fun y => ⟨(0, y), rfl⟩, fun y hy => ?_, fun x => ?_, fun y hy => ?_⟩, ⟨zero_mem _, 1, (algebraMap (OL LL) LL.1).map_one⟩, rfl,
    fun h => ?_, ⟨hcr, GlobalTheory.T.tame_type_of_extension_lattice ϖ Pl T Sig hS hT.type z hz, GlobalTheory.T.crystalline_extension_of_jumps ϖ Pl AI hstd T U hU hT.crys hT.jumps z hcr⟩⟩
  · obtain ⟨o, rfl⟩ := hy
    exact ⟨(0, Algebra.linearMap _ _ o), ⟨zero_mem _, o, rfl⟩, rfl⟩
  · change x.2 = 0 ↔ ∃ y, ((y, 0) : T.V × ↥LL.1) = x
    exact ⟨fun h0 => ⟨x.1, Prod.ext rfl h0.symm⟩, fun ⟨y, hy⟩ => by rw [← hy]⟩
  · exact hy.1
  · change ((T.ρ h 0 + (1 : ↥LL.1) • (z : Gl l → T.V) h, (1 : ↥LL.1)) : T.V × ↥LL.1) - (0, 1) = (c h, 0)
    simp only [map_zero, zero_add, one_smul]
    exact Prod.ext (sub_zero _) (sub_self _)

end GlobalTheory.ExtGood
