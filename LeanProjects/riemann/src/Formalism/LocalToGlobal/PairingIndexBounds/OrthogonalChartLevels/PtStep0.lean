import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]

def gamAd {N : ℕ} (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (bad : Finset (HeightOneSpectrum (𝓞 F))) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : GL (Fin N) E :=
  Classical.epsilon fun γ : GL (Fin N) E => ∀ v ∈ bad,
    bc (prV (E := E) v) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ) ∈ Uloc v

def toLE {N : ℕ} (γ : GL (Fin N) E) : (Fin N → E) ≃ₗ[E] (Fin N → E) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin N → E) (Matrix.GeneralLinearGroup.toLin γ)

def stdG {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) : (Fin N → E) ≃ₗ[E] (Fin N → E) :=
  (stdCo σ J).symm.trans ((toLE γ).trans (stdCo σ J))

def reE {N n : ℕ} (h : N = n) : (Fin N → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.funCongrLeft E E (finCongr h.symm)

structure PtD (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) where
  N : Submodule (𝓞 E) (Fin n → E)
  g : (Fin n → E) ≃ₗ[E] (Fin n → E)
  dt : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ

def PtD.re {N n : ℕ} (h : N = n) (Λ : Submodule (𝓞 E) (Fin N → E)) (g : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (dt : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : PtD F E n where
  N := Λ.map (((reE (E := E) h : (Fin N → E) ≃ₗ[E] (Fin n → E)) : (Fin N → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))
  g := ((reE h).symm.trans g).trans (reE h)
  dt := dt

variable {I : LocId L p nV W Qq} {N m : ℕ}

def ptStep (S : StepG I N) (hk : m + 1 = N) (a : 𝓞 E) (bad : Finset (HeightOneSpectrum (𝓞 F))) (i : S.comp)
    (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) : PtD F E (m + 1) :=
  PtD.re hk.symm (kerLat (sp := sp) S hk a i Lt)
    ((toLE (gamAd S.Uloc bad (ptAd S hk i Lt))).trans (stdCo (sp.cm.sig : E →+* E) S.J))
    (Matrix.GeneralLinearGroup.det (ptAd S hk i Lt))

def ptAd0 (hdet : IsUnit sp.gram0.det) (hk : m + 1 = R.k) (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F))
    (i : compL L p) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  ((y i * jQ I hdet hk (gOf Lt) : GA sp) : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))

def ptStep0 (hdet : IsUnit sp.gram0.det) (hk : m + 1 = R.k) (y : compL L p → UPts sp.cm.sig sp.gram0 (Formalism.L2.Herm.Af F))
    (a : 𝓞 E) (bad : Finset (HeightOneSpectrum (𝓞 F))) (i : compL L p) (Lt : Fin nV → Submodule W (Fin (m + 1) → Qq)) :
    PtD F E (m + 1) :=
  PtD.re hk.symm
    (toStd (sp.cm.sig : E →+* E) sp.gram0 (compan (sp := sp) sp.gram0 a (latAd (ptAd0 (I := I) hdet hk y i Lt) L.Lb)))
    ((toLE (gamAd L.Uloc bad (ptAd0 (I := I) hdet hk y i Lt))).trans (stdCo (sp.cm.sig : E →+* E) sp.gram0))
    (Matrix.GeneralLinearGroup.det (ptAd0 (I := I) hdet hk y i Lt))

def frCoM (J : Matrix (Fin N) (Fin N) E) {Lb : Submodule (𝓞 E) (Fin N → E)} (fr : FrS I Lb) (hk : m + 1 = N) (v : Fin nV) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) Qq :=
  ((((LinearMap.toMatrix' ((stdCo (sp.cm.sig : E →+* E) J : (Fin N → E) ≃ₗ[E] (Fin N → E)) :
      (Fin N → E) →ₗ[E] (Fin N → E))).map ((fstV I v).comp (inclE (F := F) ((I.plc v).adicCompletion F)))) *
    ((fr.fr (I.plc v) (I.pl v).2 : GL (Fin N) ((I.plc v).adicCompletion F)) :
      Matrix (Fin N) (Fin N) ((I.plc v).adicCompletion F))).map (I.eQ v).symm).submatrix (finCongr hk) (finCongr hk)

end Formalism.L2.PairingIndexBounds.F
