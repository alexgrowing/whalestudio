import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistAbsoluteCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem typed_tw_finite {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z : ℂ)
    (H : ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)),
      IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U K W))
    (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (hW : FiniteDimensional ℂ W) :
    FiniteDimensional ℂ (typed (tw U z) K W) := by
  have hK₀ : IsOpen ((K ⊓ KO E N : Subgroup (GL (Fin N) (Af E))) : Set (GL (Fin N) (Af E))) := by
    rw [Subgroup.coe_inf]
    exact hK.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E N)
  have hfin := H (K ⊓ KO E N) W hK₀ hW
  have hflat : FlatFn (absFn (E := E) N (-z)) := GlobalTheory.T.flat_absolute_character N (-z)
  have hval : ∀ (φ : Sm E N) x, (mulChi N (GlobalTheory.CuspRep.Model.absC E (-z)) φ).1 x =
      absFn N (-z) x * φ.1 x := fun φ x => by
    simp only [mulChi_apply, absFn]
    exact mul_comm _ _
  have hfinv : ∀ (g : GA E N), ∀ u ∈ KO E N, absFn (E := E) N (-z) (g * finGL E N u) = absFn N (-z) g := by
    intro g u hu
    have := hflat.rinv g 1 u hu
    simpa [cf] using this
  have hkinv : ∀ (g : GA E N) (k : Kinf E N),
      absFn (E := E) N (-z) (g * infGL E N (Unitary.toUnits k)) = absFn N (-z) g := by
    intro g k
    have := hflat.rinv g k 1 (one_mem _)
    simpa [cf] using this
  let L : Sm E N ≃ₗ[ℂ] Sm E N := mulChi N (GlobalTheory.CuspRep.Model.absC E (-z))
  have hle : (typed (tw U z) K W).map (L : Sm E N →ₗ[ℂ] Sm E N) ≤ typed U (K ⊓ KO E N) W := by
    rintro _ ⟨φ, ⟨⟨ψ, hψ, rfl⟩, hlev, htype⟩, rfl⟩
    set φ : Sm E N := mulChi N (GlobalTheory.CuspRep.Model.absC E z) ψ with hφ
    have hL : ∀ x, (L φ).1 x = absFn N (-z) x * φ.1 x := hval φ
    refine ⟨?_, ?_, ?_⟩
    · have hback : L φ = ψ := by
        refine Subtype.ext (funext fun x => ?_)
        have e : ∀ s : ℂ, ((chiDet N (GlobalTheory.CuspRep.Model.absC E s) x : ℂˣ) : ℂ) =
            Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x)) := fun _ => rfl
        rw [hL, hφ, mulChi_apply, absFn, e, e, mul_left_comm, ← Complex.exp_add]
        simp
      show L φ ∈ U
      rw [hback]
      exact hψ
    · intro u hu g
      have h2 : φ.1 (g * finGL E N u) = φ.1 g := hlev u hu.1 g
      show (L φ).1 (g * finGL E N u) = (L φ).1 g
      rw [hL, hL, hfinv g u hu.2, h2]
    · intro g
      have h3 : (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W := htype g
      have h4 : (fun k : Kinf E N => (L φ).1 (g * infGL E N (Unitary.toUnits k))) =
          absFn N (-z) g • (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) := by
        funext k
        rw [hL, hkinv g k]
        rfl
      show (fun k : Kinf E N => (L φ).1 (g * infGL E N (Unitary.toUnits k))) ∈ W
      rw [h4]
      exact W.smul_mem _ h3
  have h1 : FiniteDimensional ℂ ((typed (tw U z) K W).map (L : Sm E N →ₗ[ℂ] Sm E N)) :=
    Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (L.submoduleMap (typed (tw U z) K W)).symm

end GlobalTheory.CompanionTheory.LimV
