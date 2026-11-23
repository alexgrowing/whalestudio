import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately

open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt

theorem vV_algebraMap_of_isUnit (T : CDVR) {u : T.V} (hu : IsUnit u) : vV T.V (algebraMap T.V T.Fr u) = 0 := by
  have : valV T.V (algebraMap T.V T.Fr u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal u).1 h hu
  simp [vV, this]

theorem rho_vw_eq_vAdd_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ w, s.rho_vw w = (vAdd w b : ℝ) - (vAdd w (P.B w τ.1).det : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s b hb hev w
  obtain ⟨v, hv⟩ := s.hasPts.2 w
  have hval := s.val_eq hv
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  have hval' : nval T.V e (evR Xo c s.sig y.1) = ((flDefect_vw Dw c τ w + s.rho_vw w : ℝ) : EReal) := hval
  have hδ : flDefect_vw Dw c τ w = 0 := by simp [flDefect_vw, hD.q]
  rw [hδ, zero_add] at hval'
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c c.F T.Fr
    (Algebra.ofId c.F T.Fr) P.y₀
  obtain ⟨ha, hB, hloc⟩ := P.loc w
  have hx : y.1.x = z.x := (P.only T.Fr y.1 hy.2).trans hz.1.symm
  obtain ⟨Y, u, hY, hch⟩ := hloc T io e ho y.1 z y.2.2 hz hx
  have hdet : ∀ τ', ((P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)).det =
      io (P.B w τ').det * algebraMap T.V T.Fr (Y τ').det := fun τ' => by
    rw [Matrix.det_mul, RingHom.map_det, RingHom.map_det]; rfl
  have hYne : ∀ τ', algebraMap T.V T.Fr (Y τ').det ≠ 0 := fun τ' => ((hY τ').map _).ne_zero
  have hBne : ∀ τ', io (P.B w τ').det ≠ 0 := fun τ' => (map_ne_zero io).2 (hB τ')
  have key := hev T.Fr z y.1 (fun τ' => (P.B w τ').map io * (Y τ').map (algebraMap T.V T.Fr)) _
    (fun τ' => by rw [hdet]; exact (mul_ne_zero (hBne τ') (hYne τ')).isUnit)
    (mul_ne_zero ((map_ne_zero io).2 ha) (u.isUnit.map _).ne_zero).isUnit hz hch
  rw [hdet] at key
  have key' : evR Xo c s.sig y.1 * (io (P.B w τ.1).det * algebraMap T.V T.Fr (Y τ.1).det) = io b := key
  have hbne : io b ≠ 0 := (map_ne_zero io).2 hb
  have h0 : evR Xo c s.sig y.1 ≠ 0 := left_ne_zero_of_mul (key' ▸ hbne)
  have h1 := congrArg (vV T.V) key'
  rw [vV_mul h0 (mul_ne_zero (hBne _) (hYne _)), vV_mul (hBne _) (hYne _), vV_algebraMap_of_isUnit T (hY _),
    ho.2, ho.2] at h1
  rw [nval_of_ne h0, EReal.coe_eq_coe_iff] at hval'
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h2 := congrArg (Int.cast : ℤ → ℝ) h1
  push_cast at h2
  rw [← hval', div_eq_iff he]
  show _ = ((vLa w b : ℝ) - (vLa w (P.B w τ.1).det : ℝ)) * e
  linarith

end GlobalTheory.DefPt
