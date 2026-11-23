import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.BigTop.Fun.TieModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem inUse (p : PtAt ex Csz) (t : Tup p) : InUse p t := p.charW.tup.mu_used t

theorem mu_eq (p : PtAt ex Csz) : (p.S false).μ = p.R.mu ∧ p.P.A3.fam3.base3.μ0 = p.P.A3.A.μ0 := ⟨rfl, rfl⟩

theorem toR_eq (p : PtAt ex Csz) (t : Tup p) (x) :
    p.F.cr.toR (p.R.toCx3 p.F).zs false t x =
      eV0 p t (((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) ((p.R.toCx3 p.F).zs.Z t)).mulVec x) := rfl

theorem mem_goodPart_iff (p : PtAt ex Csz) (t : Tup p) (W : Submodule D.what₂.LL (p.P.A3.A.fam.R t).S.Forms) (x) :
    x ∈ (p.P.A3.A.fam.R t).inV0 (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) W ↔ eV0 p t x ∈ W := by
  constructor
  · rintro ⟨y, hy, e⟩
    have : eV0 p t x = y := (p.P.A3.A.fam.R t).S.basis.equivFun.symm_apply_eq.2 e.symm
    exact this ▸ hy
  · intro h
    exact ⟨_, h, (p.P.A3.A.fam.R t).S.basis.equivFun.apply_symm_apply _⟩

theorem hd_eq (ij : Sq D) : sqRank D ij / 2 = SqNum.halfRank D ij.1 ij.2 := by
  unfold sqRank SqNum.halfRank
  congr 1
  simp only [rankV]; ring

theorem isIntExp_mono {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} {C C' : ℝ} {dl}
    (hb : 0 ≤ Real.log sc.b) (h : SqNum.IsIntExp G C dl) (hC : C ≤ C') : SqNum.IsIntExp G C' dl := by
  obtain ⟨S, del, h1, h2, h3, h4⟩ := h
  have hm : ∀ (f N : ℕ) (B : ℕ) (Q : ℕ), GlobalTheory.NormSum.intBound C f N B (Real.log sc.b) Q ≤
      GlobalTheory.NormSum.intBound C' f N B (Real.log sc.b) Q := fun f N B Q => by
    have a : 0 ≤ Real.log ((f : ℝ) * (2 * (N : ℝ))) := by exact_mod_cast Real.log_natCast_nonneg (f * (2 * N))
    have b := Real.log_natCast_nonneg Q
    unfold GlobalTheory.NormSum.intBound
    gcongr
  refine ⟨S, del, ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.trans (hm ..)⟩, h2, ?_, h4⟩
  intro δ t0 K _ _ _ _ σ ι P P' zA zA' a b c
  obtain ⟨x, y, z⟩ := h3 δ t0 K σ ι P P' zA zA' a b c
  exact ⟨x, fun F => (y F).trans (hm ..), z⟩

variable {p : PtAt ex Csz} {CF : ℝ}

theorem mulVec_eq_of_basis {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) (t : Tup p)
    (hS : ∀ i, a.ch.S.SumOK t (a.ch.Phi i)) (V : Matrix (Fin n) (Fin ((Df p).nV t)) D.what₂.LL)
    (h : ∀ i k, D.what₂.embLL (V i k) = vK a.ch t (eV0 p t (Pi.single k 1)) i) (x) (i : Fin n) :
    D.what₂.embLL (V.mulVec x i) = vK a.ch t (eV0 p t x) i := by
  induction x using Pi.single_induction with
  | zero =>
    have := vK_smul a.ch t 0 (eV0 p t 0) i
    rw [zero_smul, map_zero, zero_mul] at this
    rw [Matrix.mulVec_zero, map_zero, this]; simp
  | add x y hx hy => rw [Matrix.mulVec_add, Pi.add_apply, map_add, map_add, hx, hy]; exact (vK_add a.ch t (hS i) _ _).symm
  | single k c =>
    have e : (Pi.single k c : _ → D.what₂.LL) = c • Pi.single k 1 := by ext j; by_cases hj : j = k <;> simp [hj]
    rw [e, map_smul, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    refine Eq.trans ?_ (vK_smul a.ch t c _ i).symm
    rw [← h]; simp

theorem entry {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (h : TieV d a) (t : Tup p) (i k) :
    D.what₂.embLL (d.V t i k) = vK a.ch t (eV0 p t (Pi.single k 1)) i := by
  rw [← h t (inUse p t)]; simp

theorem ratio_eq {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (h : TieAt d a) (t : Tup p) :
    cTot a.ch p.P.A3.A.μ0 ≠ 0 ∧ D.what₂.embLL (∏ ij, d.rq t ij) = ratio a.ch t := by
  have h0 : ∀ i j, a.ch.c i j p.P.A3.A.μ0 ≠ 0 := fun i j => by
    obtain ⟨c, c0, hc⟩ := h.sq.ratio (i, j)
    have := hc _ (Or.inl rfl)
    rwa [h.ok.is.toIsBase.c_eq this.1 this.2.1]
  refine ⟨(cTot_ne_zero_iff _ _).2 h0, ?_⟩
  rw [ratio_eq_prod, map_prod, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  exact eq_div_of_mul_eq (h0 i j)
    (IsSqOf.rq_mul h.sq (ij := (i, j)) (inUse p t) (h.ok.is.const i j _) (h.ok.is.const i j t))

theorem exists_tie {G : Grid p CF} {W : G.Weil} (hW : W.Over p.R.toRealDat) {n : ℕ} (a : SlopeTestRemainingChoices p G W n) (ha : a.OK)
    (hS : ∀ t i, a.ch.S.SumOK t (a.ch.Phi i)) (hR : ∀ t x i, vK a.ch t x i ∈ Set.range D.what₂.embLL)
    (hc : ∀ i j t, SquareNonzero W a.S.B a.rm t i j ∧ a.c i j t ≠ 0)
    (hr : ∀ i j t, sqRatio a.ch i j t ∈ Set.range D.what₂.embLL)
    (hB : BottomsWith G p.P.A3.A.μ0 fun _ => True)
    (h3 : ∀ (ij : Sq D) (s : ℕ), 1 ≤ s → s ≤ SqNum.halfRank D ij.1 ij.2 → ∃ zd g n,
      SqNum.IsTorVal G p.P.A3.A.μ0 ij.1 ij.2 s zd g ∧ SqNum.IsDenom G ij.1 ij.2 s n ∧ {l | l.Prime ∧ n l ≠ 0}.Finite)
    (h4 : ∃ dl, SqNum.IsIntExp G CF dl) : ∃ d : FunIn p CF, d.G = G ∧ Comparison₂ p CF d := by
  obtain ⟨X', M, hM⟩ := exists_isTestLat G a.rp n a.e
  choose v hv using hR
  choose r hr using hr
  obtain ⟨dl, h4⟩ := h4
  obtain ⟨δ, t0, hB⟩ := ha.sq.norms hB
  choose P P' hP hP1 hP2 using hB
  choose zA hA using hP1
  choose zA' hA' using hP2
  have h5 : {w | p.R.mu w ≠ p.P.A3.A.μ0}.Finite :=
    p.R.twPl.finite_toSet.subset fun w hw => by_contra fun h => hw (p.charW.tup.mu_off w h)
  obtain ⟨zT, zTd, gT, ch, N0, Sd, Se, Bw, hq⟩ := exists_isSqOf (W := W) (B := a.S.B) (ρ := a.rm) (C := CF) (μ := p.R.mu)
    (rq := fun t ij => r ij.1 ij.2 t) (zA := zA) (zA' := zA') (dl := dl)
    (fun ij => ⟨a.c ij.1 ij.2, (hc _ _ _).2, fun t _ => ⟨(hc _ _ t).1, ha.is.const _ _ t, by
      rw [hr]; exact div_mul_cancel₀ _ (hc _ _ _).2⟩⟩)
    ⟨δ, t0, fun ij => ⟨P ij, P' ij, hP ij, hA ij, hA' ij⟩⟩ h3 h4 h5
  exact ⟨⟨G, W, hW, n, X', M, fun t => Matrix.of fun i k => v t (eV0 p t (Pi.single k 1)) i, fun t ij => r ij.1 ij.2 t, dl, Sd, Se,
    N0, zA, zA', zT, zTd, gT, ch, Bw⟩, rfl, a, ha, hM,
    fun t _ x i => mulVec_eq_of_basis a t (hS t) _ (fun i k => hv _ _ _) x i, hq⟩

theorem pos_of_tie (d : FunIn p CF) (h : Comparison₂ p CF d) : 0 < d.n := by
  obtain ⟨a, -⟩ := h
  obtain ⟨i⟩ := GlobalTheory.TestLat.SlopeModel.nonempty_idx (LaP d.G)
  exact (a.e.symm (⟨fun _ => default, Quotient.mk'' 1⟩, i)).pos

theorem matrix_unique {G : Grid p CF} {W : G.Weil} {n : ℕ} (a : SlopeTestRemainingChoices p G W n) (t : Tup p)
    (V V' : Matrix (Fin n) (Fin ((Df p).nV t)) D.what₂.LL)
    (h : ∀ x i, D.what₂.embLL (V.mulVec x i) = vK a.ch t (eV0 p t x) i)
    (h' : ∀ x i, D.what₂.embLL (V'.mulVec x i) = vK a.ch t (eV0 p t x) i) : V = V' := by
  ext i k
  simpa using D.what₂.embLL.injective ((h (Pi.single k 1) i).trans (h' (Pi.single k 1) i).symm)

theorem ofGrid_tie {G : Grid p CF} {W : G.Weil} {hW n V} (h : Comparison₂ p CF (.ofGrid G W hW n V)) :
    (∀ w : PlL D, ((D.host.pde : ℕ) : 𝓞 D.what₂.LL) ∈ w.asIdeal) ∧
      ∃ (S : Finset ℕ) (del : ℕ → ℝ), 1 ≤ del 2 ∧ Formalism.PairingDivisionLocalBalance.wt (K := D.what₂.LL) S del = 0 := by
  obtain ⟨a, h⟩ := h
  obtain ⟨S, del, -, h2, -, h4⟩ := h.sq.int
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  exact ⟨fun w => (h.sq.choice w).1 rfl, S, del, h2.one_le_two hN (Nat.cast_nonneg _), h4.symm⟩

end GlobalTheory.BigTop.Fun.TieModel

end
