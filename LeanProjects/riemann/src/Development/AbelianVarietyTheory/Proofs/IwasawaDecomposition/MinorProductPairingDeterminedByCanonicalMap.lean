import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLSubR
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KForm.WWUnique

theorem aeval_map_nablaX {Lt : Type} [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.aeval (R := ℂ_[l]) (fun v : Lt × ℕ × Fin N1 => ∑ a : Fin N0,
        (MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2)) :
          MvPolynomial (KM.XZ Lt N0 N1) ℂ_[l]))
      (MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.nablaX N1 nu I)) =
    MvPolynomial.map (Int.castRingHom ℂ_[l]) (KM.Gxz N0 N1 nu I) := by
  simp only [KM.nablaX, KM.Gxz, KM.minorXZ, map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, RingHom.map_det, AlgHom.map_det]
  congr 1
  ext i k
  simp [MvPolynomial.map_X, MvPolynomial.aeval_X, map_sum, map_mul]

theorem ww_unique : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1) (nu : Bool × HH D → YoungDiagram)
    (hnu : ∀ z, (nu z).colLen 0 ≤ N0) (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[p])
    (ph : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N0) ℂ_[p]))
    (ph' : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]))
    (κ : ℂ_[p]) (Q : MvPolynomial ((Bool × HH D) × Fin N0 × ℕ) ℂ_[p])
    (hQ : ∀ y : Bool × HH D → Fin N0 → ℕ → ℂ_[p], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (GL3Columns.DeX N0 nu y))
    (h : ∀ y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p],
      ph' (GL3Columns.DeX N1 nu fun s => GL3Columns.colsOf (y' (tauPl D s))) = κ * GL3Columns.applyQ p N0 N1 Th Q (fun s => GL3Columns.colsOf (y' (tauPl D s))))
    (I : KM.ColChoice N1 nu), ph' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu I)) = κ * ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu I)) := by
  intro D p _ N0 N1 hN nu hnu Th ph ph' κ Q hQ h I
  classical
  haveI : Finite (KM.ColChoice N1 nu) := by
    unfold KM.ColChoice
    infer_instance
  letI : Fintype (KM.ColChoice N1 nu) := Fintype.ofFinite _
  let J : ((Bool × HH D) × Fin N0 × Fin N1 →₀ ℕ) → ℂ_[p] :=
    fun m => (m.prod fun _ k => (k.factorial : ℂ_[p])) * MvPowerSeries.coeff m Th
  let σ : (Bool × HH D) × ℕ × Fin N1 → MvPolynomial (KM.XZ (Bool × HH D) N0 N1) ℂ_[p] :=
    fun v => ∑ a : Fin N0, MvPolynomial.X (Sum.inl (v.1, v.2.1, a)) * MvPolynomial.X (Sum.inr (v.1, a, v.2.2))
  let L : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) :=
    ph ∘ₗ GlobalTheory.KFormCore.jetL J ∘ₗ (MvPolynomial.aeval (R := ℂ_[p]) σ).toLinearMap
  have hL : ∀ J' : KM.ColChoice N1 nu, L (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu J')) =
      ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu J')) := by
    intro J'
    simp only [L, LinearMap.comp_apply, AlgHom.toLinearMap_apply, σ]
    rw [aeval_map_nablaX, GlobalTheory.KFormCore.applyAt0_eq]
  have hLD : ∀ y, L (GL3Columns.DeX N1 nu y) = GL3Columns.applyQ p N0 N1 Th Q y := by
    intro y
    rw [GL3Columns.ww_holds D p N0 N1 nu Th ph Q hQ y, GL3Columns.wwCB_holds D ℂ_[p] N1 nu y, finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun J' _ => ?_
    rw [← MvPolynomial.smul_eq_C_mul, map_smul, hL, smul_eq_mul]
  let ψ : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]) := ph' - κ • L
  have hψ : ∀ y, ψ (GL3Columns.DeX N1 nu y) = 0 := by
    intro y
    let e := Equiv.ofBijective (tauPl D) (tauPl_bij D)
    let y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p] := fun τ => Matrix.of fun a b => y (e.symm τ) a b
    have hy : GL3Columns.DeX N1 nu y = GL3Columns.DeX N1 nu (fun s => GL3Columns.colsOf (y' (tauPl D s))) := by
      unfold GL3Columns.DeX
      refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
      congr 1
      ext i j
      have hj : (j : ℕ) < N1 :=
        lt_of_lt_of_le j.2 ((YoungDiagram.colLen_anti _ 0 c (Nat.zero_le _)).trans ((hnu s).trans hN))
      have hs : e.symm (tauPl D s) = s := e.symm_apply_apply s
      simp [GL3Columns.colsOf, hj, y', hs]
    rw [hy]
    simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, h, hLD, smul_eq_mul, sub_self]
  have h4 := GL3Columns.wwInj_holds D p N1 nu ψ hψ I
  simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hL] at h4
  exact sub_eq_zero.mp h4

end GlobalTheory.KForm.WWUnique
