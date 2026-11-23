import Formalism.LocalToGlobal.HermitianForms.TiedTwAll

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7}

section Gen

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def sgTG : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => shW (M.sg τ) ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)

set_option maxHeartbeats 1000000 in

structure ClassesAtPrimes (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) where
  lev : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad

  y : M.clsP → UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  lat : M.clsP → Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)
  y_lat : ∀ c (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb
  lat_fin : ∀ c, Module.Finite (𝓞 D.host.E) (lat c)

  stabI : ∀ c, M.stabilizer₂ c →* UJ (sigD D : D.host.E →+* D.host.E) (gramP D)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

variable {M}

set_option maxHeartbeats 1000000 in

structure ValuationAtPrimes {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (K : ClassesAtPrimes M bad) (okW : D.what₂.places.Pl → Prop) where

  sg : ∀ τ (i : Fin (D.R.N D.R.m - 1)),
    ((M.sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i

  eW : P.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ)

  ptC : ∀ z, z ∈ M.ptC ↔ eW z ∈ FiC K.lev (embT D) (sgTG M) K.y

  ipP : ∀ (o : FrP D), o.IsON → ∀ (z z' : P.Wrow)
    (Pc Qc : M.clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ),
    (∀ c, Pc c ∈ CSpan M.sg) → (∀ c, Qc c ∈ CSpan M.sg) →
    (∀ c, eW z c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) (Pc c)) →
    (∀ c, eW z' c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) (Qc c)) →
    M.ipP z z' = ∑ c, ((Nat.card (M.stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll M.sg (Qc c) (Pc c)

  rat : ∀ z, (∃ x, M.ptEmb x = z) ↔
    z ∈ M.ptC ∧ ∀ c, ∃ Pc ∈ RatSpan D M.sg, eW z c = fnOf _ (shiftOf (sgTG M)) 1 Pc

  lat : ∀ w, okW w → ∀ x : M.ptLat.V, x ∈ M.SP w ↔
    ∀ (c : M.clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w) (K.lat c : Set _) B →
      ∃ Pc ∈ IntSpan D w M.sg, eW (M.ptEmb x) c =
        fnOf _ (shiftOf (sgTG M)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N D.R.m - 1)) D.host.E).1) Pc

def NormPTieG {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}
    (W : ValuationAtPrimes K okW) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : M.ptLat.V)
    (Pc : M.clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
    (∀ c, W.eW (M.ptEmb x) c =
      fnOf _ (shiftOf (sgTG M)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))) →
    ∀ o : Frames (gramC (gramP D) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt M.ptLat.b M.ptLat.X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card (M.stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (sgTG M) τ)) *
          (nfAll M.sg (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

end Gen

theorem sgTG_fm (u : D.what₂.Word) : sgTG (D.fm u) = sgT u := rfl

def ClsPTied.toG {u : D.what₂.Word} (K : ClsPTied u) : ClassesAtPrimes (D.fm u) (badG D) where
  lev := K.lev
  y := K.y
  y_bij := K.y_bij
  lat := K.lat
  y_lat := K.y_lat
  lat_fin := K.lat_fin
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

end Formalism.L2.Forms

end
