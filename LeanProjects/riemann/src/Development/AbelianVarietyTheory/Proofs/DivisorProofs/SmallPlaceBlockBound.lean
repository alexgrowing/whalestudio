import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameAut

theorem norm_val_of_orderDvd {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n)
    (v : HeightOneSpectrum (𝓞 E)) : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := by
  have h1 : (χ.val v) ^ n = 1 := by
    have h2 := congrArg (fun ψ : Formalism.L2.Host.HChar E => ψ.val v) h
    simpa [Formalism.L2.Host.HChar.val, Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc] using h2
  have h3 : ((χ.val v : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h3 hn.ne'

theorem norm_sq_valTw_half {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (h : χ.IsUnitary)
    (v : HeightOneSpectrum (𝓞 E)) : ‖χ.valTw (1 / 2) v‖ ^ 2 = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  have h1 : ‖((χ.val v : ℂˣ) : ℂ)‖ = 1 := h _
  have hq : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  have hq' : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast hq
  rw [Formalism.L2.Host.HChar.valTw, norm_mul, h1, one_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re, Complex.ofReal_re,
    ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, ← Real.rpow_neg_one]
  norm_num

theorem norm_sq_firstValA {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    (j : Fin D.R.m) (t : T) (P : Pl0) (hP : P ∈ A.ok t) :
    ‖D.what₂.embLL (Formalism.L2.Col.firstValA (A.muVal j t) A.etaVal A.q A.r P)‖ ^ 2 = (A.q P : ℝ) ^ A.r := by
  obtain ⟨hQ, -, -, h4⟩ := GlobalTheory.GoodPrimes.good_primes R F hL
  have hq := (h4 hF t P hP).2.2
  obtain ⟨gramR, c0R, c0L, hT⟩ := hF.tie
  have hP0 : P ∈ A.ok A.μ0 := by
    obtain ⟨h1, h2, h3⟩ := (hT.ok t P).1 hP
    refine (hT.ok _ P).2 ?_
    rw [hQ, Finset.coe_empty, Set.union_empty]
    exact ⟨h1, fun h => h2 (Or.inl h), fun Q h => h3 Q (Or.inl h)⟩
  have hmu : ‖D.what₂.embLL (A.muVal j t P : D.what₂.LL)‖ = 1 := by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    rw [hF.muVal j t P hP, Formalism.L2.Host.HChar.val_mul, Units.val_mul, norm_mul, norm_val_of_orderDvd _ hn ho, mul_one]
    exact (R.C.isMu0 j).unitary _
  have heta : ‖D.what₂.embLL (A.etaVal P : D.what₂.LL)‖ ^ 2 = (A.q P : ℝ)⁻¹ := by
    rw [hF.etaVal P hP0, hq]
    exact norm_sq_valTw_half _ R.C.isEta.unitary _
  have hq0 : (A.q P : ℝ) ≠ 0 := by
    rw [hq]
    exact_mod_cast fun e => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  obtain ⟨s, hs⟩ : Odd A.r := hT.ranks.2.1 ▸ Formalism.L2.NTheta.odd_r D.R
  have hd : (A.r + 1) / 2 = s + 1 := by omega
  unfold Formalism.L2.Col.firstValA
  rw [hd, hs]
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Units.val_inv_eq_inv_val, map_inv₀, norm_inv, hmu, inv_one, one_mul,
    mul_pow, heta, Complex.norm_natCast]
  field_simp
  ring

theorem norm_sq_blockValue : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), PtAt.Rows p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ ν hν Q
  have h := norm_sq_firstValA p.R.toRealDat p.F.lv2 p.charW.base.lev p.charW.base.fam j (p.R.mu w) Q.1 Q.2
  obtain rfl : ν = fun Q => Formalism.L2.Col.firstValA (p.P.A3.A.muVal j (p.R.mu w)) p.P.A3.A.etaVal p.P.A3.A.q p.P.A3.A.r Q.1 :=
    List.mem_singleton.1 hν
  have e : (blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t = p.P.A3.A.r := Nat.add_sub_cancel ..
  rw [e]
  exact h

end GlobalTheory.FrameAut
