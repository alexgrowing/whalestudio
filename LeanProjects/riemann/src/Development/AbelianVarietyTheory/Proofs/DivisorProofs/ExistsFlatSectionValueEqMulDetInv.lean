import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameRingOverTestRingStatement

open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.FlatValue

theorem exists_reduced_frameRing (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) :
    ∃ (A : TRing K) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), (∀ τ, IsUnit (X τ).det) ∧
      ∀ (T : Type) [CommRing T] [Algebra K T] (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T) (a : Tˣ),
        (∀ τ, IsUnit (g τ).det) → ∃ k : A.R →ₐ[K] T, (∀ τ, (X τ).map k = g τ) ∧ k (s : A.R) = (a : T) := by
  let p : TRing K := ⟨0, ⊥, Ideal.isRadical_bot⟩
  obtain ⟨A, π, X, s, hA⟩ := GlobalTheory.T.exists_frameRing_over_testRing K J m p
  refine ⟨A, X, s, hA.1, fun T _ _ g a hg => ?_⟩
  let ψ : p.R →ₐ[K] T := Ideal.Quotient.liftₐ ⊥ (MvPolynomial.aeval Fin.elim0) (fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero])
  obtain ⟨k, ⟨-, h1, h2⟩, -⟩ := hA.2 T ψ g a hg
  exact ⟨k, h1, h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exOf_flatWt (hq : Dw.q = 0) (τ : Psi H) (b : E →+* ℂ) (i : Fin (Dw.mult b)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) = if b = τ.1 then -1 else 0 := by
  have hi := i.2
  by_cases h : b (H.rt : E) = H.rt0
  · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
    refine (wtOf_big _ 0 ⟨b, h⟩ i hp).trans ?_
    simp [flatWt, parWt, Subtype.ext_iff]
  · have hq' : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
    omega

theorem evR_mul_det_field (hq : Dw.q = 0) (τ : Psi H) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (K : Type) [Field K] [Algebra c.F K] (z y : FrPt Xo c K) (Y : Mats Dw K) (u : Kˣ) (hY : ∀ b, (Y b).det ≠ 0)
    (h : FrChg (fun b => (Y b)ᵀ) (u : K) z y) : evR Xo c f y * (Y τ.1).det = evR Xo c f z := by
  obtain ⟨G, hG, hev⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c K z _
    (fun b => if b = τ.1 then 1 else 0) (fun _ _ => 0) rfl
    (fun b i => by rw [exOf_flatWt hq]; split_ifs <;> simp) f hf
  simp only [Finset.sum_const_zero] at hG
  have hC : G = MvPolynomial.C (G.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hG.totalDegree_le)
  have h1 := hev y Y u hY h
  have h2 := hev z (fun _ => 1) 1 (fun _ => by simp) (by
    simpa using (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K z z z).1)
  rw [hC] at h1 h2
  simp only [Formalism.L2.LamCM.evalFr, MvPolynomial.eval_C, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq',
    Finset.mem_univ, if_true, Matrix.det_one, ite_self, Finset.prod_const_one, one_mul] at h1 h2
  rw [mul_comm, h1, h2]

theorem exists_evR_mul_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ), ∃ b : c.F, b ≠ 0 ∧ (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s
  refine ⟨evR Xo c s.sig P.y₀,
    left_ne_zero_of_mul_eq_one (s.evR_mul_inv P.on (GlobalTheory.FlagTan.fromTest_of_isLocalRing _)), ?_⟩
  obtain ⟨A, X, t, hX, hA⟩ := exists_reduced_frameRing c.F (E →+* ℂ) Dw.mult
  haveI : _root_.IsReduced A.R := (Ideal.isRadical_iff_quotient_reduced _).1 A.rad
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.FlagTan.exists_frMap (Algebra.ofId c.F A.R) P.y₀
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A.R w₀ (fun b => (X b)ᵀ) t
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  have step : ∀ (S : Type) [CommRing S] [Algebra c.F S] (k : A.R →ₐ[c.F] S) (z y : FrPt Xo c S),
      FrMap (Algebra.ofId c.F S) P.y₀ z → (FrMap k w y ↔ FrChg (fun b => ((X b).map k)ᵀ) (k t) z y) := by
    intro S _ _ k z y hz
    have h0 : FrMap k w₀ z := GlobalTheory.FlagTan.frMap_of_comp hw₀ hz fun a => k.commutes a
    exact GlobalTheory.FlagTan.frMap_iff_frChg hw h0
  have nat : ∀ (S : Type) [CommRing S] [Algebra c.F S] (k : A.R →ₐ[c.F] S) (y : FrPt Xo c S), FrMap k w y →
      evR Xo c s.sig y = k (evR Xo c s.sig w) := fun S _ _ k y h =>
    GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c s.sig s.sig_mem.1 k w y h
  have univ : evR Xo c s.sig w * (X τ.1).det = algebraMap c.F A.R (evR Xo c s.sig P.y₀) := by
    rw [← sub_eq_zero]
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
    let K : Type := q.ResidueField
    let k : A.R →ₐ[c.F] K := IsScalarTower.toAlgHom c.F A.R K
    obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap (Algebra.ofId c.F K) P.y₀
    obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frMap k w
    have hd : ∀ b, ((X b).map k).det = k (X b).det := fun b => (AlgHom.map_det k (X b)).symm
    have h1 := evR_mul_det_field hD.q τ s.sig_mem K z y (fun b => (X b).map k)
      (Units.map (k : A.R →* K) t) (fun b => by rw [hd]; exact ((hX b).map k).ne_zero) ((step K k z y hz).1 hy)
    rw [nat K k y hy, GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hz, hd] at h1
    rw [← Ideal.algebraMap_residueField_eq_zero]
    show k _ = 0
    rw [map_sub, map_mul, h1, k.commutes]
    exact sub_self _
  intro S _ _ z y Y u hY hu hz h
  obtain ⟨k, hk, hkt⟩ := hA S Y hu.unit hY
  have hy : FrMap k w y := (step S k z y hz).2 (by
    rw [hkt, IsUnit.unit_spec]
    simpa only [hk] using h)
  rw [nat S k y hy, ← hk τ.1, ← k.commutes, ← univ, map_mul]
  exact congrArg _ (AlgHom.map_det k (X τ.1)).symm

end GlobalTheory.FlatValue
