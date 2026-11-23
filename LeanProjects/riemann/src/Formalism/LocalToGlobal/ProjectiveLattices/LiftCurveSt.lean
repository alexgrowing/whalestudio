import Formalism.LocalToGlobal.ProjectiveLattices.NormalizedValuationMul
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j}

structure CurveModel (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (g0 : B.Cusp j wF) where

  A' : Subalgebra (Kp (xplus X E hM) la G.N) ↥(Frac0 (xplus X E hM) la G.w)
  sA : ∀ i : Fin (WeightFamilies.dimY D j), sfr (xplus X E hM) la G.w i.succ ∈ A'

  h : ↥A'
  h_one : h - 1 ∈ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, sA i⟩ : ↥A'))
  fin : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥A' ⧸ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, sA i⟩ : ↥A')))
  red : IsReduced (↥A' ⧸ Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
      (⟨sfr (xplus X E hM) la G.w i.succ, sA i⟩ : ↥A')))

  loc : ∀ b : ↥(Frac0 (xplus X E hM) la G.w), ∃ m : ℕ, ∃ a : ↥A', (h : ↥(Frac0 (xplus X E hM) la G.w)) ^ m * b = a

  base_form_injective : Function.Injective fun a : ↥A' =>
    ((a : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
      (emb (xplus X E hM) la G.N (X.inc wF g0))

  base_form_local : ∀ x : ↥(HK (xplus X E hM) la G.w wF), ∃ m : ℕ, ∃ a : ↥A',
    ((h : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) ^ m * (x : Lw (xplus X E hM) la G.w) =
      ((a : ↥(Frac0 (xplus X E hM) la G.w)) : Lw (xplus X E hM) la G.w) * algebraMap (Rp (xplus X E hM) la G.N) (Lw (xplus X E hM) la G.w)
        (emb (xplus X E hM) la G.N (X.inc wF g0))

def InCurveSecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF),
    Nonempty (CurveModel G la g0) →
    (∀ ζ, (hs ζ).ev (emb (xplus X E hM) la G.N (X.inc wF g0)) ≠ 0) →
    (secQ y hs g0).InCurve

structure LiftModel (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (y : PtsG G la → E.Pt' la)
    (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF) (T : ℕ) where

  Λ : Type
  [cr : CommRing Λ]

  ι : Lw (xplus X E hM) la G.w →+* Λ

  hd : (Idx D j G.N →₀ ℕ) → Λ →+ Λ
  hd_zero : ∀ x, hd 0 x = x
  hd_ι : ∀ β x, hd β (ι x) = ι (hasse (xplus X E hM) la G.w β x)
  hd_mul : ∀ β x z, hd β (x * z) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal β, hd q.1 x * hd q.2 z

  ev : ∀ ζ, Λ →+* (hs ζ).T.Fr
  ev_ι : ∀ ζ x, ev ζ (ι x) = (hs ζ).lift x

  RG : Subring Λ
  RG_hd : ∀ β, ∀ r ∈ RG, hd β r ∈ RG
  RG_int : ∀ ζ, ∀ r ∈ RG, 0 ≤ nval (hs ζ).T.V 1 (ev ζ r)

  e' : Λ
  e'_hd : ∀ β, β ≠ 0 → hd β e' = 0
  e'_int : ∀ ζ, 0 ≤ nval (hs ζ).T.V 1 (ev ζ e')

  res_ker : ∀ x : ↥(HK (xplus X E hM) la G.w wF), ι (x : Lw (xplus X E hM) la G.w) ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w)) →
    toA0K (xplus X E hM) la G.w wF x = 0

  ball : ∀ a ∈ (secQ y hs g0).A0, ∃ r ∈ RG, ∃ x : ↥(HK (xplus X E hM) la G.w wF),
    toA0K (xplus X E hM) la G.w wF x = a ∧
    ι (x : Lw (xplus X E hM) la G.w) - r * e' ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w))

  approx : ∀ r ∈ RG, ∃ x : ↥(HK (xplus X E hM) la G.w wF),
    ι (x : Lw (xplus X E hM) la G.w) - r * e' ∈
      Ideal.span (Set.range fun i : Fin (WeightFamilies.dimY D j) =>
        ι (sfr (xplus X E hM) la G.w i.succ : Lw (xplus X E hM) la G.w)) ^ (a0 D j T)

attribute [instance] LiftModel.cr

def InLiftSecSt (G : GlobalFamilyData (xplus X E hM) ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (Gc Prw : ℝ) : Prop :=
  ∀ (y : PtsG G la → E.Pt' la) (hs : ∀ ζ, SecPt ζ (y ζ)) (g0 : B.Cusp j wF) (T : ℕ),
    Nonempty (LiftModel G la y hs g0 T) →
    G.TiedW S Gc Prw → (secQ y hs g0).InCurve → (secQ y hs g0).InTie S → (secQ y hs g0).InLift T

end Formalism.L2.Pj
