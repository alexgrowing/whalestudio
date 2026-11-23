import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

variable {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF)

theorem N_eq : d.O.N = GlobalTheory.ChiGrid.bigN D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  have : D.R.r + 6 = D.R.k + D.R.m + 5 := by unfold Ranks.r; omega
  rw [this]

theorem nr_eq : d.O.nr = GlobalTheory.ChiGrid.nRk D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m = D.R.r + 1
  unfold Ranks.r; omega

theorem s_eq : d.O.s = GlobalTheory.ChiGrid.sLen D := by
  have := D.R.two_le_m
  show D.R.k + D.R.m + 5 = D.R.r + 6
  unfold Ranks.r; omega

theorem PPF_eq (C b : ℝ) : d.O.PPF C b = GlobalTheory.ChiGrid.sizeP D C b := by
  unfold FunData.PPF GlobalTheory.ChiGrid.sizeP
  rw [nr_eq]; rfl

theorem Lc_eq : d.O.Lc = GlobalTheory.ChiGrid.cloudLen D := by
  classical
  have h : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  unfold FunData.Lc GlobalTheory.ChiGrid.cloudLen
  refine le_antisymm (Finset.sup_le fun τ hτ => ?_) (Finset.sup_le fun τ _ => ?_)
  · have hτ' : τ < Fintype.card D.what₂.Tau := h ▸ Finset.mem_range.1 hτ
    refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ =>
      ((GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v 2 - (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) 0 0 0).v D.R.k).toNat)
      (Finset.mem_univ ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, hτ'⟩)))
    show (cloud D τ 2 - cloud D τ D.R.k).toNat = _
    simp only [cloud, dif_pos hτ']
  · refine le_trans (le_of_eq ?_) (Finset.le_sup (f := fun τ => (d.O.cl τ 2 - d.O.cl τ d.O.k).toNat)
      (Finset.mem_range.2 (show ((Fintype.equivFin D.what₂.Tau τ : Fin _) : ℕ) < D.R.f from h ▸ (Fintype.equivFin D.what₂.Tau τ).2)))
    show _ = (cloud D _ 2 - cloud D _ D.R.k).toNat
    simp only [cloud, dif_pos (Fintype.equivFin D.what₂.Tau τ).2, Fin.eta, Equiv.symm_apply_apply]

theorem ga_eq (C : ℝ) : d.O.ga C = GlobalTheory.ChiGrid.gap D C := by
  unfold FunData.ga GlobalTheory.ChiGrid.gap
  rw [N_eq, nr_eq, s_eq, Lc_eq d]; rfl

theorem ee_eq (h : Ideal.absNorm d.G.pl.v0.asIdeal = GlobalTheory.ChiGrid.q0 D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    d.O.ee CF p.Z.b v = d.G.pl.depth ⟨1, CF, p.Z.b⟩ v := by
  unfold FunData.ee GlobalTheory.ChiGrid.Places.depth GlobalTheory.ChiGrid.depth0
  rw [PPF_eq]
  have e : d.O.qq d.O.sv0 = GlobalTheory.ChiGrid.q0 D := h
  rw [e]
  by_cases hv : v = d.G.pl.v0
  · rw [if_pos hv]; exact if_pos hv
  · rw [if_neg hv]; exact if_neg hv

theorem square_ranks (C b : ℝ) : (∀ ij, d.O.dd ij = 2 * d.O.hd ij) ∧ (∀ ij, d.O.dd ij ≤ 2 * d.O.N) ∧
    (∀ ij, d.O.yy ij + 1 ≤ d.O.m) ∧ ∀ q ∈ d.O.S0, d.O.cc q ≤ d.O.ee C b q := by
  refine ⟨fun ij => ?_, fun ij => ?_, fun ij => ?_, fun q _ => ?_⟩
  · show sqRank D ij = 2 * (sqRank D ij / 2)
    have : Even (sqRank D ij) := by
      unfold sqRank
      rw [Nat.even_add, GlobalTheory.ChiGrid.even_rankV, GlobalTheory.ChiGrid.even_rankV]
      have : (ij.1 : ℕ) + (ij.2 + 1) = ij.1 + 1 + ij.2 := by ring
      rw [this]
    obtain ⟨a, ha⟩ := this
    omega
  · rw [N_eq]
    show sqRank D ij ≤ _
    unfold sqRank GlobalTheory.ChiGrid.rankV GlobalTheory.ChiGrid.bigN
    have h1 : (ij.1 : ℕ) + 1 ≤ D.R.m := ij.1.2
    have h2 : (ij.2 : ℕ) + 1 ≤ D.R.m := ij.2.2
    have h3 : D.R.r ≤ D.R.k + D.R.m := by unfold Ranks.r; omega
    nlinarith [Nat.mul_le_mul_right D.R.t h2, Nat.mul_le_mul_right (GlobalTheory.ChiGrid.sLen D) h1]
  · have := D.R.two_le_m
    show D.R.m - 1 - ij.2 + 1 ≤ D.R.m
    omega
  · unfold FunData.ee
    by_cases hv : q = d.O.sv0
    · rw [if_pos hv]
      have : d.O.cc q = 1 := if_pos hv
      omega
    · rw [if_neg hv]
      exact le_of_eq (if_neg hv)

theorem yy_eq (ij : Sq D) : d.O.yy ij =
    (GlobalTheory.ChiGrid.Node.grid ij.1 (ij.2 + 1)).neg D.R.m + (GlobalTheory.ChiGrid.Node.grid (ij.1 + 1) ij.2).neg D.R.m := by
  have := ij.2.2
  show D.R.m - 1 - ij.2 = (D.R.m - (ij.2 + 1)) / 2 + (D.R.m - ij.2) / 2
  omega

theorem not_leafMM_zero (G : Grid p CF) (W : G.Weil) (h : W.Over p.R.toRealDat) (C : ℝ) :
    ¬ LeafMM (FunIn.ofGrid G W h 0 fun _ => 0).O C := fun hM =>
  hM.2.1 ((Submodule.eq_bot_iff _).2 fun _ _ => funext fun i => i.elim0)

theorem ofGrid_lattice (G : Grid p CF) (W : G.Weil) (h : W.Over p.R.toRealDat) (V) :
    (FunIn.ofGrid G W h 1 V).M.FG ∧ (FunIn.ofGrid G W h 1 V).M ≠ ⊥ ∧ ∀ v, IsUnit ((FunIn.ofGrid G W h 1 V).X' v).det := by
  refine ⟨Submodule.fg_span (Set.finite_range _), fun e => ?_, fun v => ?_⟩
  · have e' : Submodule.span (𝓞 D.what₂.LL) (Set.range (Pi.basisFun D.what₂.LL (Fin 1))) = ⊥ := e
    exact (Pi.basisFun D.what₂.LL (Fin 1)).ne_zero 0 (Submodule.span_eq_bot.1 e' _ ⟨0, rfl⟩)
  · show IsUnit (1 : Matrix (Fin 1) (Fin 1) ℂ).det
    simp

end GlobalTheory.BigTop.Fun.Model

namespace GlobalTheory.BigTop.Fun.FieldProbe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pow_le_finrank {K : Type} [Field K] [NumberField K] {q e : ℕ} (hq : q.Prime) {z : K}
    (hz : IsPrimitiveRoot z (q ^ (e + 1))) : q ^ e ≤ Module.finrank ℚ K := by
  have h0 : 0 < q ^ (e+1) := pow_pos hq.pos _
  have h1 := (IsPrimitiveRoot.lcm_totient_le_finrank hz hz (by
    rw [Nat.lcm_self]; exact Polynomial.cyclotomic.irreducible_rat h0) : _ ≤ Module.finrank ℚ K)
  rw [Nat.lcm_self, Nat.totient_prime_pow_succ hq] at h1
  have : 1 ≤ q - 1 := by have := hq.two_le; omega
  nlinarith [pow_pos hq.pos e]

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem degree_of_fit (p : PtAt ex Csz) (CF : ℝ) (G : Grid p CF) (h : GridFit p G)
    (h0 : Ideal.absNorm G.pl.v0.asIdeal = GlobalTheory.ChiGrid.q0 D) :
    GlobalTheory.ChiGrid.q0 D ^ ⌊GlobalTheory.ChiGrid.sizeP D CF p.Z.b / Real.log (GlobalTheory.ChiGrid.q0 D)⌋₊ ≤ Module.finrank ℚ D.LL0 := by
  obtain ⟨z, hz⟩ := h.field.roots _ (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  rw [h0] at hz
  refine pow_le_finrank (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1 (z := z) ?_
  simpa [GlobalTheory.ChiGrid.Places.depth, GlobalTheory.ChiGrid.depth0] using hz

theorem nonempty_iff (p : PtAt ex Csz) (CF : ℝ) : Nonempty (FunIn p CF) ↔
    ∃ (G : GlobalTheory.ChiGrid.GridData p.R.toRealDat.toLevCh ⟨1, CF, p.Z.b⟩) (W : G.Weil), W.Over p.R.toRealDat :=
  ⟨fun ⟨d⟩ => ⟨d.G, d.W, d.ext⟩, fun ⟨G, W, h⟩ => ⟨.ofGrid G W h 1 fun _ => 0⟩⟩

end GlobalTheory.BigTop.Fun.FieldProbe

end
