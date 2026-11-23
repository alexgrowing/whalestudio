import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [Fact p.Prime]

structure FData (X : Sys p) (D : D7) where
  kerN : ∀ j, X.Lt j → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E)
  trG : ∀ j, X.Lt j → (Fin ((X.Pj j).m + 1) → D.host.E) ≃ₗ[D.host.E] (Fin ((X.Pj j).m + 1) → D.host.E)
  dt : ∀ j, X.Lt j → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ
  frM : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)

variable (X : Sys p) (D : D7)

def twG (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) : X.G.P.Qq v →+* ℂ_[p] :=
  E.iK.comp ((X.G.P.ι v).comp ((X.G.P.σ v ^ s.val : X.G.P.Qq v ≃+* X.G.P.Qq v).toRingHom))

variable {X D}

open Classical in

def subBG (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (j : ℕ) (La : X.Lt j)
    (La' : X.Lt (j + 1)) (x y : D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) : ℂ_[p] :=
  if x.1 = y.1 then
    (if IsOddPos (pos.symm x.1).2 then
      ((fd.frM j La (pos.symm x.1).1).map (twG X E _ (pos.symm x.1).2)) x.2.2 y.2.2 *
        (((fd.frM (j + 1) La' (pos.symm x.1).1)⁻¹).map (twG X E _ (pos.symm x.1).2)) y.2.1 x.2.1
    else
      ((fd.frM (j + 1) La' (pos.symm x.1).1).map (twG X E _ (pos.symm x.1).2)) x.2.1 y.2.1 *
        (((fd.frM j La (pos.symm x.1).1)⁻¹).map (twG X E _ (pos.symm x.1).2)) y.2.2 x.2.2)
  else 0

def FrecG (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D)
    {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
    (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ)
    (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) (c : ℂ_[p])
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) :
    MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p] :=
  linSub (fun x y => c * subBG E pos fd j La La' x y) <|
  ((p : ℂ_[p]) ^ (∑ v : X.Pl, X.vm v (j + 1) * (len X v (j + 1) La'.2 - len X v j La.2))) •
  serP lam fun z =>
    (muT (j + 1) (fd.dt (j + 1) La') * (muT (j + 1) (fd.dt j La))⁻¹ *
      (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ *
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN j La)) ^ (-(((j * (X.t + 1) / 2 : ℕ) : ℤ))) *
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (fd.kerN (j + 1) La')) ^ ((((j + 1) * (X.t + 1) / 2 : ℕ) : ℤ))) *
    kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (movD (Ξ₀ j La La') (fd.trG j La) (fd.trG (j + 1) La')) z

structure ChartPts (X : Sys p) (D : D7) where
  N : ∀ j, X.Lt j → ℕ
  hk : ∀ j La, (X.Pj j).m + 1 = N j La
  J : ∀ j La, Matrix (Fin (N j La)) (Fin (N j La)) D.host.E
  Lb : ∀ j La, Submodule (𝓞 D.host.E) (Fin (N j La) → D.host.E)
  Uloc : ∀ j La, ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (N j La)) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))
  y : ∀ j La, GL (Fin (N j La)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  B : ∀ j La, GL (Fin (N j La)) D.host.E
  iw : ∀ j, X.Lt j → ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v

def fdOfCharts (cp : ChartPts X D) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) : FData X D where
  kerN := fun j La => (toStd (D.sp.cm.sig : D.host.E →+* D.host.E) (cp.J j La)
      (compan (sp := D.sp) (cp.J j La) a (latAd (cp.y j La) (cp.Lb j La)))).map
    (((reE (E := D.host.E) (cp.hk j La).symm : _ ≃ₗ[D.host.E] _) : _ →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))
  trG := fun j La => ((reE (E := D.host.E) (cp.hk j La).symm).symm.trans
      ((toLE (gamAd (cp.Uloc j La) bad (cp.y j La))).trans (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (cp.J j La)))).trans
    (reE (cp.hk j La).symm)
  dt := fun j La => Matrix.GeneralLinearGroup.det (cp.y j La)
  frM := fun j La v => ((((LinearMap.toMatrix' ((stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (cp.J j La) :
      (Fin (cp.N j La) → D.host.E) ≃ₗ[D.host.E] (Fin (cp.N j La) → D.host.E)) :
        (Fin (cp.N j La) → D.host.E) →ₗ[D.host.E] (Fin (cp.N j La) → D.host.E))) *
    (cp.B j La : Matrix (Fin (cp.N j La)) (Fin (cp.N j La)) D.host.E)).map (cp.iw j La v)).submatrix
      (finCongr (cp.hk j La)) (finCongr (cp.hk j La)))

end Formalism.L2.PairingIndexBounds.F
