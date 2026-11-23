import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.MulVecEqOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexMatrixDescendsOfRationalOnTuple
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveICRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EV0MemGoodFRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEV0EqICPqRowsStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem out_sum_tw {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {n : ℕ}
    (f : E →ₗ[ℂ] ℂ) (φ : (Fin n → ℂ) →ₗ[ℂ] Tw s E) (z : Fin n → ℂ) :
    f (Tw.out (φ z)) = ∑ k, cj s (z k) * f (Tw.out (φ (Pi.single k 1))) := by
  let o : Tw s E →+ E := ⟨⟨Tw.out, rfl⟩, Tw.out_add⟩
  have e : z = ∑ k, z k • (Pi.single k 1 : Fin n → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext j; by_cases hj : j = k <;> simp [hj]
  conv_lhs => rw [e, map_sum]
  rw [show Tw.out (∑ k, φ (z k • Pi.single k 1)) = ∑ k, Tw.out (φ (z k • (Pi.single k 1 : Fin n → ℂ))) from
    map_sum o (fun k => φ (z k • (Pi.single k 1 : Fin n → ℂ))) Finset.univ, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Tw.out_smul, map_smul, smul_eq_mul]

theorem twist_conj_base_embedding_eq (p : PtAt ex Csz) (a : D.what₂.LL) :
    cj (twAt D.what₂.embLL p.P.A3.A.v0) (p.P.A3.fam3.base3.v0.embedding a) = D.what₂.embLL a := by
  rw [show p.P.A3.fam3.base3.v0 = p.P.A3.A.v0 from rfl, emb_eq D.what₂.embLL p.P.A3.A.v0 a, cj_cj, sgAt_mk _ p.R.hv0]

theorem mul_eq_one_of_covolume_identity (κ zt z0 ct c0 v : ℂ) (hκ : κ ≠ 0) (hzt : zt ≠ 0) (hz0 : z0 ≠ 0) (hct : ct ≠ 0) (hc0 : c0 ≠ 0) :
    κ⁻¹ * z0 * c0 * (κ * v / (zt * ct)) = (zt / z0 * (ct / c0))⁻¹ * v := by
  field_simp

set_option maxHeartbeats 1600000 in

theorem oneMap_at (p : PtAt ex Csz) (hp : p.Rows) {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (ht : TieAt d a)
    (hwf : (Df p).WF) (hR : ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false)
    (hQ : (∀ b u, ConvK a.ch b u) ∧ (∀ u, (∀ b, psiK a.ch b u = 0) → u = 0) ∧
      (∀ i j t, SquareNonzero a.ch.W a.ch.S.B a.ch.rm t i j ∧ a.ch.c i j t ≠ 0) ∧
      (a.ch.FieldOK → ∃ κ ze, FormulaAt a.ch κ ze)) :
    ∃ ze : Tup p → D.what₂.LL, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
      LeafC (p.S false) (d.data ze ∅ fun _ => 0) := by
  classical
  obtain ⟨hL, hI, hC, hF⟩ := hQ
  obtain ⟨κ, ze, hz, hform⟩ := hF ht.ok.field
  obtain ⟨R0, hR0⟩ := hR
  obtain ⟨hinj, hrow⟩ := GlobalTheory.T.injective_iC_rows p hp
  have hzK : ∀ t, ze t ≠ 0 := fun t h => by
    obtain ⟨n, hn, e⟩ := hz t
    rw [h, zero_pow hn.ne'] at e
    exact zero_ne_one e
  have hze : ∀ t, D.what₂.embLL (ze t) ≠ 0 := fun t => (map_ne_zero _).2 (hzK t)
  have hc0 : ∀ t, cTot a.ch t ≠ 0 := fun t => (cTot_ne_zero_iff _ _).2 fun i j => (hC i j t).2

  have key : ∀ t (y : Fin ((Df p).nV t) → D.what₂.LL) (b : Fin d.n),
      D.what₂.embLL (ze t) * cTot a.ch t * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
        (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) =
        κ * D.what₂.embLL ((d.V t).mulVec y b) := by
    intro t y b
    rw [← GlobalTheory.T.theta_eV0_eq_iC_Pq_rows p hp t y, ht.sums t (TieModel.inUse p t) y b]
    exact hform t _ (GlobalTheory.T.eV0_mem_goodF_rows p hp t y) b

  have lin : ∀ (b : Fin d.n) (z : Fin (p.S false).D → D.what₂.LL),
      psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (cpt p.P.A3.fam3.base3.v0.embedding z)) =
        ∑ k, D.what₂.embLL (z k) *
          psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1)) := by
    intro b z
    have := out_sum_tw (twAt D.what₂.embLL p.P.A3.A.v0) (psiL a.ch b (hL b))
      ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0) (cpt p.P.A3.fam3.base3.v0.embedding z)
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    exact congrArg (· * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1))) (twist_conj_base_embedding_eq p (z k))

  have hκ : κ ≠ 0 := by
    intro hκ0
    have h0 : ∀ y, (p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0
        (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec y)) = 0 := by
      intro y
      apply hI
      intro b
      have := key p.P.A3.fam3.base3.μ0 y b
      rw [hκ0, zero_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero (hze _) (hc0 _))
    have i0 : Fin ((Df p).dQ p.P.A3.fam3.base3.μ0) := ⟨0, R0.pos⟩
    obtain ⟨y, hy⟩ := hwf.Pq_surj p.P.A3.fam3.base3.μ0 (Pi.single i0 1)
    have h1 := h0 y
    rw [hy] at h1
    have h2 := congrFun (hinj (h1.trans (map_zero _).symm)) i0
    simp [cpt] at h2

  let c0 : ℂ := κ⁻¹ * D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) * cTot a.ch p.P.A3.fam3.base3.μ0
  let Ψc : Matrix (Fin d.n) (Fin (p.S false).D) ℂ := Matrix.of fun b k =>
    c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false p.P.A3.fam3.base3.μ0 (Pi.single k 1))
  let ze' : Tup p → D.what₂.LL := fun t => ze t / ze p.P.A3.fam3.base3.μ0
  let r : Tup p → D.what₂.LL := fun t => ze' t * ∏ ij, d.rq t ij
  have hmain : ∀ t ∈ (Set.univ : Set (Tup p)),
      Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL = ((r t)⁻¹ • d.V t).map D.what₂.embLL := by
    intro t _
    have H : ∀ y : Fin ((Df p).nV t) → D.what₂.LL, ∀ b,
        (Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          (((r t)⁻¹ • d.V t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b := by
      intro y b
      have e1 : Ψc.mulVec (cpt D.what₂.embLL (((p.S false).ι t).mulVec (((Df p).Pq t).mulVec y))) b =
          c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) := by
        rw [← hrow, lin, Finset.mul_sum]
        simp only [Matrix.mulVec, dotProduct, Ψc, Matrix.of_apply, cpt]
        exact Finset.sum_congr rfl fun k _ => by ring
      have e3 := (TieModel.ratio_eq ht t).2
      have eL : (Ψc * ((p.S false).ι t * (Df p).Pq t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          c0 * psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) := by
        rw [← Matrix.mulVec_mulVec, ← cpt_mulVec, ← Matrix.mulVec_mulVec]
        exact e1
      have eR : (((r t)⁻¹ • d.V t).map D.what₂.embLL).mulVec (cpt D.what₂.embLL y) b =
          (D.what₂.embLL (ze t) / D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) *
            (cTot a.ch t / cTot a.ch p.P.A3.fam3.base3.μ0))⁻¹ * D.what₂.embLL ((d.V t).mulVec y b) := by
        rw [← cpt_mulVec]
        show D.what₂.embLL ((((r t)⁻¹ • d.V t).mulVec y) b) = _
        rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        rw [show r t = ze t / ze p.P.A3.fam3.base3.μ0 * ∏ ij, d.rq t ij from rfl, map_mul, map_div₀, e3]
        rfl
      have hP : psiK a.ch b ((p.R.toCx3 p.F).iC p.F.cr false t
            (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y))) =
          κ * D.what₂.embLL ((d.V t).mulVec y b) / (D.what₂.embLL (ze t) * cTot a.ch t) :=
        eq_div_of_mul_eq (mul_ne_zero (hze t) (hc0 t)) (by rw [mul_comm]; exact key t y b)
      rw [eL, eR, hP]
      exact mul_eq_one_of_covolume_identity _ _ _ _ _ _ hκ (hze t) (hze _) (hc0 t) (hc0 _)
    ext b col
    have := H (Pi.single col 1) b
    have hs : cpt D.what₂.embLL (Pi.single col (1 : D.what₂.LL)) = Pi.single col 1 := by
      funext i; by_cases hi : i = col <;> simp [cpt, hi]
    rw [hs, Matrix.mulVec_single, Matrix.mulVec_single] at this
    simpa using this
  have hbij : Function.Bijective ((p.S false).ι p.P.A3.fam3.base3.μ0).mulVec := (hR0 ▸ R0.l1c).1 _
  obtain ⟨⟨Ψ, -, hΨ⟩, -⟩ := GlobalTheory.complex_matrix_descends_of_rational_on_tuple D.what₂.embLL d.n (p.S false).D (Df p).dQ
    (Df p).nV (p.S false).ι (Df p).Pq d.V r Set.univ p.P.A3.fam3.base3.μ0 Ψc trivial hbij
    (hwf.Pq_surj _) hmain
  refine ⟨ze', by simp only [ze']; exact div_self (hzK _), fun t => ?_, Ψ, fun t _ => ?_⟩
  · obtain ⟨n, hn, e⟩ := hz t
    obtain ⟨m, hm, e'⟩ := hz p.P.A3.fam3.base3.μ0
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    show (ze t / ze p.P.A3.fam3.base3.μ0) ^ (n * m) = 1
    rw [div_pow, pow_mul (ze t), e, one_pow, pow_mul' (ze _), e', one_pow, div_one]
  · refine (hΨ t trivial).trans ?_
    show _ = (∏ ij, d.rq t ij)⁻¹ • ((ze' t)⁻¹ • d.V t)
    rw [smul_smul, mul_inv, mul_comm]

theorem oneMap_of_rows (hB : Bundle) (hS : SetAt) (h1 : LinK) (h2 : InjK) (h3 : ConstK) (h4 : Formula2K) : OneMap @Comparison₂ := by
  obtain ⟨CF0, hQ⟩ := hS.atPt (h1.and (h2.and (h3.and h4)))
  refine ⟨CF0, fun CF hCF => (hQ CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => evPt_imp e fun x hx i p hp q d hd => ?_⟩⟩
  obtain ⟨-, a, ht⟩ := hd
  obtain ⟨wf, R0, hR⟩ := hB p hp
  exact oneMap_at p hp d a ht wf ⟨R0, hR⟩ (q d.G d.W d.n a ht.ok)

end GlobalTheory.BigTop.Fun
