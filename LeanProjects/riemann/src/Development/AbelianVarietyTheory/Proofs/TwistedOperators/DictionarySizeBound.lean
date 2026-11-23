import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetDatumVectorFiniteHeisenbergCombinationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticesDifferentiableOperatorStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.DictFree

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

noncomputable def conjQ : Qbar →+* Qbar where
  toFun x := ⟨starRingEnd ℂ x, by
    have h : IsAlgebraic ℚ (x : ℂ) := (mem_algebraicClosure_iff).1 x.2
    exact (mem_algebraicClosure_iff).2
      (h.algHom ((Complex.conjAe.restrictScalars ℚ : ℂ ≃ₐ[ℚ] ℂ) : ℂ →ₐ[ℚ] ℂ))⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

noncomputable def oppQ {T : Type} : Pair T → (Qbar →+* Qbar)
  | .chi _ _ => conjQ
  | .core _ => conjQ
  | _ => RingHom.id _

theorem oppQ_coe {T : Type} (p : Pair T) (x : Qbar) : ((oppQ p x : Qbar) : ℂ) = opp p (x : ℂ) := by
  cases p <;> rfl

theorem opp_opp {T : Type} (p : Pair T) (z : ℂ) : opp p (opp p z) = z := by
  cases p <;> simp [opp]

end GlobalTheory.DictFree

namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial

theorem jetTab_comb {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil)
    (B : VertexFrames G) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f) {n : ℕ}
    (a : Fin n → ℂ) (w : Fin n → WO (G.pS p) (G.pT p)) (hw : ∀ i, (w i).map (infPart D) = 0)
    (X : FinPt G p.small) (Y : FinPt G p.big) (mon : Formalism.L2.Ker.DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ) :
    jetTab W B p (∑ i, a i • heisO W.ψ _ _ (w i) f) X Y mon = ∑ i, a i * jetTab W B p (heisO W.ψ _ _ (w i) f) X Y mon := by
  have h1 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (G.pS p) (G.pT p) W.ψ_std W.θ_is
    (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f hf n a w hw (monomial (mon.mapDomain (fvar G p)) 1)).1
  have h2 : ∀ i, heisO W.ψ _ _ (w i) (pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f
      (monomial (mon.mapDomain (fvar G p)) 1)) = pureTensorO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p)
      (G.onT B p) (heisO W.ψ _ _ (w i) f) (monomial (mon.mapDomain (fvar G p)) 1) := fun i => by
    have := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (G.pS p) (G.pT p) W.ψ_std W.θ_is
      (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) f hf 1 (fun _ => 1) (fun _ => w i) (fun _ => hw i)
      (monomial (mon.mapDomain (fvar G p)) 1)).1
    simpa using this
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO]
  rw [← h1]
  simp only [← h2, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.DictFree

namespace GlobalTheory.DictFree
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 MvPolynomial

theorem differentiable_U {D : D7} (Tr : Tor D) {N N' : ℕ} (s : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (Formalism.MainNotions.TaylorLogMetric.U D Tr s G) := by
  unfold Formalism.MainNotions.TaylorLogMetric.U Formalism.MainNotions.TaylorLogMetric.Hf
  fun_prop

theorem dictAt_big : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun ch => GlobalTheory.SumSize.DictAt ch := by
  intro hP hI
  obtain ⟨CF0, hCF⟩ := GlobalTheory.T.self_dual_lattices_differentiable_operator hP hI
  refine ⟨CF0, fun ε CF hCF0 => ?_⟩
  obtain ⟨x₀, hx⟩ := hCF ε CF hCF0
  refine ⟨x₀, ?_⟩
  intro D large₂ hε hx₀ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt
  have H2 := hx D large₂ hε hx₀ Γ Pl0 T A Ks R F hS ch hIs hAt
  intro t p hp k d hk hcos hz hP' x y
  obtain ⟨Ls, Lt, κ, hLs, hLt, hκ, hdiff, hq, htr⟩ := H2 p hp x y
  obtain ⟨n, c, w, hwL, hwf, hcI, hcN, hvec⟩ := GlobalTheory.T.cosetDatumVector_finite_heisenbergCombination ch.S.toGridChoice t p hp k d hk hcos hz hP'
  choose ζ s hζ hs hjet using fun i => htr k hk (w i) (hwL i)
  refine ⟨Ls, Lt, κ, n, fun i => oppQ p (c i) * ζ i, s, hLs, hLt, hκ, hs, fun i => ?_, fun ρ => ?_, hq, fun mon => ?_⟩
  · obtain ⟨m, hm, hζm⟩ := hζ i
    have hζi : IsIntegral ℤ (ζ i) := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hζm]⟩
    have e : (k : Qbar) ^ (D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank) * (oppQ p (c i) * ζ i) =
        oppQ p ((k : Qbar) ^ (D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank) * c i) * ζ i := by
      rw [map_mul, map_pow, map_natCast]; ring
    rw [e]
    exact ((hcI i).map (oppQ p).toIntAlgHom).mul hζi
  · have h1 : ∀ i, ‖ρ (ζ i)‖ = 1 := fun i => by
      obtain ⟨m, hm, hζm⟩ := hζ i
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, ← map_pow, hζm, map_one, norm_one])
    calc ∑ i, ‖ρ (oppQ p (c i) * ζ i)‖ = ∑ i, ‖(ρ.comp (oppQ p)) (c i)‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_mul, norm_mul, h1, mul_one]; rfl
      _ ≤ 1 := hcN _
  · have hvac : IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vac p) := (ch.S.Z.vac_is p hp).2.theta
    show jetTab ch.W ch.S.N.frC p (ch.S.Z.vec d) _ _ mon = _
    rw [hvec, jetTab_comb ch.W ch.S.N.frC p hvac _ w hwf]
    simp only [hjet]
    set Gt := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
      (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p) with hGt
    set M := MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) (1 : ℂ)
    set Per := (mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e
    have hGi : ∀ i, Differentiable ℂ (fun z => κ * ((ζ i : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z)) :=
      fun i => ((differentiable_U _ (s i) hdiff).const_mul _).const_mul _
    have hfun : (fun z => κ * ∑ i, ((oppQ p (c i) * ζ i : Qbar) : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z) =
        ∑ i ∈ Finset.univ, ((oppQ p (c i) : Qbar) : ℂ) • fun z => κ * ((ζ i : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) (s i) Gt z) := by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    rw [hfun, GlobalTheory.NormSum.RepInv.applyAt0_sum _ _ _ hGi, Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [oppQ_coe]
    simp only [map_mul, opp_opp]
    ring

end GlobalTheory.DictFree

end
