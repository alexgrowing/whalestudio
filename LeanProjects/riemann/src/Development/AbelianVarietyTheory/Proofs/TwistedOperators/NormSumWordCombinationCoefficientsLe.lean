import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.IoPhase

open GlobalTheory.ConjLiftUnique

theorem isONBasis_of_adapted {n : ℕ} {G B : Mn n} (h : IsAdapted G 1 B) : IsONBasis G 1 B n := by
  obtain ⟨ε, h1, h2⟩ := h
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have c : Formalism.REAL.Jm ε * (Bᴴ * G) * B = 1 := by rw [Matrix.mul_assoc, h1, hJ]
  have e : Formalism.REAL.Jm ε = 1 := by
    calc Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Bᴴ * G) * B * Formalism.REAL.Jm ε := by rw [c, Matrix.one_mul]
      _ = 1 := by rw [Matrix.mul_assoc _ B, ← h2, Matrix.one_mul, c]
  exact ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [h1, e], by simp⟩

theorem io_eq_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {S : D.what₂.Tau → SPar} {M : DSModel W S}
    (hω : IsWeilDatumO ψ V W χV χW ω) (h1 : Formalism.IndefR.FWT.LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {c : CoefA V}
    (hc : c.Is) (pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ)) (ht : ∀ P, IsThetaFunO ψ V W (pt P))
    (hinj : Function.Injective pt) {Δ : PolF D W.rank V.rank}
    {io io' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} (hio : IsIoW θ M c ω pt Δ io)
    (hio' : IsIoW θ M c ω pt Δ io') : ∃ a : ℂ, ‖a‖ = 1 ∧ io' = a • io := by
  classical
  let F : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W := io.compr₂ (pt.codRestrict _ ht)
  let F' : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] thetaSub ψ V W := io'.compr₂ (pt.codRestrict _ ht)
  have f1 : ∀ x w, (F x w).1 = pt (io x w) := fun _ _ => rfl
  have f2 : ∀ x w, (F' x w).1 = pt (io' x w) := fun _ _ => rfl
  clear_value F F'
  have hF : Eqv θ ω F := ⟨fun u hu x w => by rw [f1, f1, hio.1 u hu],
    fun τ k hk v u hu w => by rw [f1, f1, hio.2.1 τ k hk v u hu]⟩
  have hF' : Eqv θ ω F' := ⟨fun u hu x w => by rw [f2, f2, hio'.1 u hu],
    fun τ k hk v u hu w => by rw [f2, f2, hio'.2.1 τ k hk v u hu]⟩
  obtain ⟨v₀, w₀, n1, n2, e⟩ := hio.2.2
  obtain ⟨v₁, w₁, n1', n2', e'⟩ := hio'.2.2
  obtain ⟨b, hb⟩ := exists_invForm hω
  obtain ⟨c₁, k1⟩ := exists_const_of_eqv h1 h2 hc hb hF hF w₀ n2
  obtain ⟨c₂, k2⟩ := exists_const_of_eqv h1 h2 hc hb hF' hF' w₀ n2
  obtain ⟨c₃, k3⟩ := exists_const_of_eqv h1 h2 hc hb hF hF' w₀ n2
  obtain ⟨κ, hκ, hk⟩ := exists_phase b hb.symm hb.pos hb.defin (fun v w => F (PiTensorProduct.tprod ℂ v) w)
    (fun v w => F' (PiTensorProduct.tprod ℂ v) w) k1 k2 k3 n1 n1' n2 n2' (l := 1) norm_one
    (Subtype.ext (by rw [one_smul, f1, f2, e, e']))
  have hFF : F' = κ • F := PiTensorProduct.ext (MultilinearMap.ext fun v => LinearMap.ext (hk v))
  refine ⟨κ, hκ, LinearMap.ext fun x => LinearMap.ext fun w => hinj ?_⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, ← f1, ← f2, hFF]
  rfl

theorem ioUniq (D : D7) : IoUniq D := by
  intro i M M' ψ θ χS χT ω hθ hω _ c hc _ BV f hf io io' hio hio'
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h : ∃ ρ, tauE D ρ = σ
    · exact ⟨h.choose⟩
    · exact ⟨(not_not.1 fun h' => h ((GlobalTheory.PointAtPlace.tauE_cm σ).2 h')).choose⟩
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ M' fun τ =>
    GlobalTheory.LowSmooth.shape_at M' τ (D.hc τ) (Formalism.IndefR.FWT.rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i τ) rfl
  have hB := fun τ => isONBasis_of_adapted (hf τ).onS
  exact io_eq_smul hω hlow.1 hlow.2 hc _
    (GlobalTheory.GalLift.Vec.theta_pureTensorO hω.std hθ (fun _ => 1) BV (cart M') (onb M') (hf τ₀).theta)
    (GlobalTheory.FockIndep.pureTensorO_injective D ψ θ _ _ _ M' BV f hω.std hθ
      (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hB τ)) hB (hf τ₀).theta (hf τ₀).ne fun τ => (hf τ).vac) hio hio'

theorem ioUniq_of_discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoUniq D :=
  fun _ _ => ioUniq

end GlobalTheory.ArchRec.IoPhase

end
