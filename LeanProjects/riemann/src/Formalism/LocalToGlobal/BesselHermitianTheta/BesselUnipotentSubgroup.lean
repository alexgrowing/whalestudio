import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsSplitSetIdem (D : D7) (e : AE D) : Prop :=
  ∃ (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ev : HeightOneSpectrum (𝓞 D.host.F) → AE D),
    (∀ v ∈ S, IsSplitIdem D (ev v) ∧ ∃ ε, IsPlaceIdem D v ε ∧ ev v + cA D (ev v) = algebraMap (AF D.host.F) (AE D) ε) ∧
    e = ∑ v ∈ S, ev v

structure IsDualFlag {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (f : Matrix (Fin B.rank) (Fin d.ρ) D.host.E) :
    Prop where
  iso : IsIsoSub B f
  pair : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) d.e * B.gram * f = 1
  perpA : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat B A ι) * B.gram * f = 0
  perpZ : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) f * B.gram).mulVec d.z = 0

def besselUnipotentSubgroup {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (f : Matrix (Fin B.rank) (Fin d.ρ) D.host.E) (eS : AE D) :
    Subgroup (GA D B) :=
  Subgroup.closure {g |
    SuppAt eS B g ∧
    (∀ k : Fin A.rank, eS • (subOne B g).mulVec (ratV fun i => frameMat B A ι i k) = 0) ∧
    (∀ k : Fin d.ρ, eS • (subOne B g).mulVec (ratV fun i => f i k) = 0) ∧
    (∀ k : Fin d.ρ, k.1 = 0 → eS • (subOne B g).mulVec (ratV fun i => d.e i k) = 0) ∧
    (d.ρ = 0 → eS • (subOne B g).mulVec (ratV d.z) = 0) ∧
    ∀ x : Fin B.rank → D.host.E, ∃ a : Fin A.rank → AE D,
      eS • (subOne B g).mulVec (ratV x) = ((frameMat B A ι).map (incA D)).mulVec a}

structure BesselCompatibility' (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (B : BesselTied D X T Wl) where

  eS : D.what₂.Word → AE D
  eS_split : ∀ u, IsSplitSetIdem D (eS u)

  f : ∀ u (ho : Odd ((D.sp.Y 0).rank - (D.sp.X 0).rank)),
    Matrix (Fin (D.sp.Y 0).rank) (Fin (B.dat _ _ _ ho (X.pos1 u)).ρ) D.host.E
  f_dual : ∀ u ho, IsDualFlag (B.dat _ _ _ ho (X.pos1 u)) (f u ho)

  mu1 : ∀ u ho, Measure (besselUnipotentSubgroup (B.dat _ _ _ ho (X.pos1 u)) (f u ho) (eS u))
  mu_one_isHaarMeasure : ∀ u ho, (mu1 u ho).IsHaarMeasure

  bper1 : ∀ u (ho : Odd ((D.sp.Y 0).rank - (D.sp.X 0).rank)), (D.sp.X 0).rank ≤ (D.sp.Y 0).rank → (D.sp.X 0).SigOK →
    HSpace.IsIsomEmb (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) → ∀ (sF : X.FJd (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0)),
    ∀ μ 𝓕, IsVolPair D (D.sp.X 0) μ 𝓕 →
    ∀ (μN : Measure (NFlag (D.sp.Y 0) (B.dat _ _ _ ho (X.pos1 u)).e)) (𝓕N : Set (NFlag (D.sp.Y 0) (B.dat _ _ _ ho (X.pos1 u)).e)),
      μN.IsHaarMeasure → IsFundamentalDomain (NFlagQ (D.sp.Y 0) (B.dat _ _ _ ho (X.pos1 u)).e) 𝓕N μN → μN 𝓕N = 1 →
    ∀ s : GA D (D.sp.X 0) → GA D (D.sp.Y 0), (∀ h, EmbRel (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (s h) h) →
    ∀ (φ : X.AF (D.sp.X 0)) (F : X.cusp (D.sp.Y 0)), IsAniso (D.sp.X 0) ∨ φ ∈ X.cusp (D.sp.X 0) →
      X.Bper (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) (X.pos1 u) sF φ F =
        ∫ g, ((B.besC _ _ _ (X.pos1 u) * T.petC (D.sp.X 0) : ℝ) : ℂ) *
          ∫ h in 𝓕, ∫ n in 𝓕N, star (T.ev (D.sp.X 0) φ h) *
            T.ev (D.sp.Y 0) (F : X.AF (D.sp.Y 0))
              ((n : GA D (D.sp.Y 0)) * s h * (g : GA D (D.sp.Y 0)) * ((B.dat _ _ _ ho (X.pos1 u)).y : GA D (D.sp.Y 0))) *
            star (besChar Wl.ψ (B.dat _ _ _ ho (X.pos1 u)) (n : GA D (D.sp.Y 0))) ∂μN ∂μ ∂(mu1 u ho)

end Formalism.L2.Theta

end
