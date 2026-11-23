import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFull
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFullTeich
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LamInstall
open ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NT

variable {D : D7} (hE : IsEmpty D.nd.Loc) {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)}
  {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) (F : TwF T)

abbrev recE (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex) : TwNew D :=
  ⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩

abbrev recL (L : TwL T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))) :
    TwNew D :=
  ⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩

variable {hE Sp F} {L : TwL T} {ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))}
  {h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g}
  {th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex}
  {th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))}

set_option maxHeartbeats 4000000 in

def twFC (X : TwFrameC (recE hE Sp F ex h0 th).toD7) : TwFrameC (recL hE Sp F L ex h0 th').toD7 := { X with }

set_option maxHeartbeats 4000000 in

def expC (X : NExpTied (recE hE Sp F ex h0 th).toD7) : NExpTied (recL hE Sp F L ex h0 th').toD7 :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      letI := X.acgWt i j b
      letI : Module (FractionRing ((recL hE Sp F L ex h0 th').toD7.ntw.O i)) (X.Wt i j b) := X.modWt i j b
      { X.mtV i j b k Q ψ h1 h2 h with } }

set_option maxHeartbeats 4000000 in

theorem sideB_keep {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (B : SideB (recE hE Sp F ex h0 th).toD7 ((recE hE Sp F ex h0 th).cf cf) ((recE hE Sp F ex h0 th).row Rw) low Pq
      ((recE hE Sp F ex h0 th).rat S) hL eig θ)
    (chiI : ∀ s, L.abelian₂ s → NC.HC D.host.E)
    (hqs : ∀ i lam P, P ∉ T.S0 i →
      B.twF.iCq i (L.qs i lam P) = ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(L.s2 i lam : ℝ) / 2) : ℝ) : ℂ))
    (hlam : ∀ s lam, NC.Read D.nd.plOm.1 (L.lamG s lam) (algebraMap (T.O s) (FractionRing (T.O s)))
      (B.chiD.embO s (L.sideL s lam)) (NC.complexEmbeddingRestrictedToSubfield D) (id (α := NC.HC D.host.E) (B.chiD.mu0 (L.jL s lam)) * id (α := NC.HC D.host.E) (B.chiD.del s) * (chiI s lam)⁻¹) 0) :
    Nonempty (SideB (recL hE Sp F L ex h0 th').toD7 ((recL hE Sp F L ex h0 th').cf cf) ((recL hE Sp F L ex h0 th').row Rw) low Pq
      ((recL hE Sp F L ex h0 th').rat S) hL eig θ) :=
  ⟨{ B with
      twF := twFC B.twF
      tw := { B.tw with qs_pos := hqs }
      chiD := { B.chiD with chiI := chiI }
      chi := { B.chi with lamG := hlam }
      exp := expC B.exp }⟩

end GlobalTheory.LamInstall
