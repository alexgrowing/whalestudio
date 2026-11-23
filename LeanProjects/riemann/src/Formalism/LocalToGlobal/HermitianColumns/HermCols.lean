import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure HermCols (D : D7) where

  lev0 : LevelData D

  lev : ∀ (u : D.what₂.Word) (i : ℕ), 1 ≤ i → i ≤ D.R.m →
    StepLevel D.sp.cm (D.sp.X i) D.host.g (D.mem u).A.T D.R.f

  cls : ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m),
    ClassTie D.sp.cm (D.sp.X i) (lev u i h1 hm).Lb (lev u i h1 hm).U ((D.mem u).C.stab i) (D.clsLat u i)

  vT : ∀ u : D.what₂.Word, (D.mem u).A.vT ≃
    {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

  Fv : ∀ (u : D.what₂.Word) (v : (D.mem u).A.vT), (D.mem u).A.Fv v ≃+* (𝓞 D.host.F ⧸ (vT u v).1.asIdeal)

structure HermTied (D : D7) extends HermCols D where

  dt : unitaryOneFiniteAdeles D.sp.cm →* D.Dt
  dt_surj : Function.Surjective dt

  dt_ker : ∀ x : unitaryOneFiniteAdeles D.sp.cm, dt x = 1 → (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) ∈ IntegralUnitGroup D.sp.cm

  dt_open : letI := tensTopL (F := D.host.F) (E := D.host.E) (Af D.host.F)
    IsOpen {x : unitaryOneFiniteAdeles D.sp.cm | dt x = 1}

  dt_UO : D.UO = ((IntegralUnitGroup D.sp.cm).subgroupOf (unitaryOneFiniteAdeles D.sp.cm)).map dt

  dt_rat : ∀ (z : unitary D.host.E) (x : unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) = unitaryOneRationalAdele D.host.F z →
    D.e1Dt z = dt x

  det0 : ∀ (u : D.what₂.Word) (c : (D.mem u).C.cls 0) (x : unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) =
      Matrix.GeneralLinearGroup.det (((lev0 u).y c : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] Af D.host.F))) →
    D.detCls u 0 c = dt x

  detI : ∀ (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (c : (D.mem u).C.cls i) (x : unitaryOneFiniteAdeles D.sp.cm),
    Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Af D.host.F)) =
      Matrix.GeneralLinearGroup.det
        (((cls u i h1 hm).y c : GL (Fin (D.sp.X i).rank) (D.host.E ⊗[D.host.F] Af D.host.F))) →
    D.detCls u i c = dt x

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory in

def VolumeCompatible (D : D7) : Prop :=
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) →
    ∀ μ, Formalism.MainNotions.StandardLattice.IsVolMeas D W P Q μ →
    ∀ 𝓕, IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
      μ 𝓕 = ENNReal.ofReal (D.vol W)

end Formalism.L2.Herm

end
