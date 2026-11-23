import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSumSubsetAndConjugateFlip
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDataLocalPureTensorsLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorRowFactorLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnFlatTensorExpansionLargeDepthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestColumnInductionLocalToGlobalExpansionStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem exists_idemSum_singleton : ∀ {D : D7} (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ w ∈ P, ∃ e' : AE D, IsIdemSum e' {w} := fun e P he w hw =>
  (GlobalTheory.IdemFlip.idemSum_sub_and_flip _ e P {w} he (Finset.singleton_subset_iff.2 hw)).1

theorem oneProduct : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t) (fr : SchRow ch.G), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ σ : (PureDat ch.G t × Combs ch.G) →₀ ℂ, (∀ k ∈ σ.support, (∀ j : Fin D.R.m, (k.1.1 j).e = e ∧ IsCombOf ch.W (k.1.1 j) (k.2.1 j)) ∧ ∀ n, (k.1.2 n).e = e ∧ IsCombOf ch.W (k.1.2 n) (k.2.2 n)) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → (σ.sum fun k x => x * ((∏ j, (k.1.1 j).fn (u j)) * ∏ n, (k.1.2 n).fn (y n))) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ (u : ColPt ch.G) (y : RowPt ch.G), evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) fr u y = (∏ w, ζ w) * σ.sum fun k x => x * evT (combC ch.W k.2 (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) (combR ch.rm k.2) u y := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_) ((GlobalTheory.T.rowData_localPureTensors_largeDepth.and GlobalTheory.T.flatTensor_rowFactor_largeDepth).and (GlobalTheory.T.columnFlatTensor_expansion_largeDepth.and GlobalTheory.T.rowTest_columnInduction_localToGlobalExpansion))
  obtain ⟨⟨hR, hF⟩, hL, hC⟩ := h
  intro s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd fr hfd hfr
  obtain ⟨dr, cr, hdr, hcr, hdrfn⟩ := hR t e he φ fr hfr
  have heL : ∀ w : locPl ch.G t, ∃ eL, IsIdemSum eL {w.1} := fun w => exists_idemSum_singleton e _ he w.1 w.2
  choose eL heL using heL
  have hloc := fun w : locPl ch.G t => hL t β w (eL w) (heL w) (φ w) (hφ w)
  choose I S x d c hdc hexp using hloc
  obtain ⟨J, SJ, xJ, dJ, cJ, hJ, hJexp, hJev⟩ :=
    hC s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd hfd eL heL I S x d c hdc hexp
  let key : J → PureDat ch.G t × Combs ch.G := fun a => ((dJ a, dr), (cJ a, cr))
  have hsum : ∀ F : PureDat ch.G t × Combs ch.G → ℂ,
      ((∑ a ∈ SJ, Finsupp.single (key a) (xJ a)).sum fun k x => x * F k) = ∑ a ∈ SJ, xJ a * F (key a) := by
    intro F
    rw [← Finsupp.sum_finset_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    exact Finset.sum_congr rfl fun a _ => Finsupp.sum_single_index (zero_mul _)
  refine ⟨∑ a ∈ SJ, Finsupp.single (key a) (xJ a), ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨a, ha, hk'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hk)
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hk')]
    exact ⟨fun j => hJ a ha j, fun n => hdr n⟩
  · intro u y hu hy
    rw [hsum]
    have hrow : ∏ n, (dr n).fn (y n) = ∏ n : Fin D.R.m, ∏ w : locPl ch.G t, φ w (.ex n D.R.m)
        (ch.S.B.coord t w.1 (X := (n, D.R.m)) (Y := (n + 1, D.R.m)) ⟨n.2.le, le_rfl⟩ ⟨n.2, le_rfl⟩
          ((y n).map fun a => cpt w.1 (toEAf D a))) :=
      Finset.prod_congr rfl fun n _ => hdrfn n (y n) (hy n)
    calc (∑ a ∈ SJ, xJ a * ((∏ j, ((key a).1.1 j).fn (u j)) * ∏ n, ((key a).1.2 n).fn (y n)))
        = (∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j)) * ∏ n, (dr n).fn (y n) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun a _ => by simp only [key]; ring
      _ = _ := by
          rw [hJexp u hu, hrow, Finset.prod_comm, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun w _ => (hF t β w (φ w) (hφ w) u y).symm
  · intro P p hp u y
    rw [hsum]
    have hev : ∀ (C : BiFam ch.G) (f : SchRow ch.G), evT C f u y = evT C 1 u 0 * ∏ i, f i (y i) := by
      intro C f
      simp only [evT, Pi.one_apply, Finset.prod_const_one, mul_one]
    have hcomb : ∀ a (C₀ : BiFam ch.G), evT (combC ch.W (key a).2 C₀) (combR ch.rm (key a).2) u y =
        evT (combC ch.W (cJ a, 0) C₀) 1 u 0 * ∏ i, fr i (y i) := by
      intro a C₀
      rw [hev]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by simp only [key, combR, hcr i]
    rw [hev, hJev P p hp u, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [hcomb a]; ring

end GlobalTheory.LocAsm

end
