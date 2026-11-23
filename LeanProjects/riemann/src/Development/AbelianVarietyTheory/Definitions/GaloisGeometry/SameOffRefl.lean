import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
import Formalism.LocalToGlobal.Divisibility.Tuples

noncomputable section

namespace GlobalTheory.TwV.Xc

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

def phiA (A : LocAt F E n G) (v : Fin G.P.nV) : AfE F E →+* G.P.Qq v :=
  ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp ((A.ph v).comp (prV (E := E) (A.pl v).1))

def ordA (A : LocAt F E n G) (v : Fin G.P.nV) (x : (AfE F E)ˣ) : ℤ := ordP (G.P.W v) p (phiA A v (x : AfE F E))

def OneOff (w : HeightOneSpectrum (𝓞 F)) (x : (AfE F E)ˣ) : Prop :=
  ∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → prV (E := E) w' (x : AfE F E) = 1

def SameOff (w : HeightOneSpectrum (𝓞 F)) {N : ℕ} (x y : GL (Fin N) (AfE F E)) : Prop :=
  ∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → bc (prV (E := E) w') x = bc (prV (E := E) w') y

def PrimeOf (p : ℕ) (W : Type) {Q : Type} [CommRing W] [Field Q] [Algebra W Q] (ρ : E →+* Q) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Q y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)

def eMat {a N : ℕ} (hr : a = N) (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) : Matrix (Fin a) (Fin a) E :=
  (LinearMap.toMatrix' (stdG σ J γ).toLinearMap).submatrix (finCongr hr) (finCongr hr)

theorem phiA_incl (A : LocAt F E n G) (v : Fin G.P.nV) (x : E) : phiA A v (x ⊗ₜ[F] 1) = A.iw v x := by
  have hp : prV (E := E) (A.pl v).1 (x ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) = x ⊗ₜ[F] 1 := by
    simp [prV]
  simp only [phiA, LocAt.iw, LocAt.phE, RingHom.comp_apply, hp]
  rfl

end GlobalTheory.TwV.Xc

end
