import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)

namespace GlobalTheory.ThmAUpper

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ChiGrid in

theorem qn_not_mem : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ)
    (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → ∀ w : HeightOneSpectrum (𝓞 D.what₂.LL), p.R.mu w ≠ p.P.A3.A.μ0 →
      ((Qn d.G (p.R.mu w) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit w hw
  classical
  obtain ⟨htw, hxi⟩ := xiH_twisted p w hw
  have hl : D.ntw.l (ex.nch.twI (D.plEq.symm w)) = D.what₂.places.resChar (D.plEq.symm w) :=
    (hfit.1.setting.1 _ htw).1
  have hQ := hfit.1.cond _ htw
  have hlev := p.charW.base.lev
  have key : ∀ PP ∈ twPl d.G (p.R.mu w),
      ((D.what₂.places.resChar (D.plEq.symm w) : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hlP
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hPP
    obtain ⟨hloc, hW0⟩ := hPP
    have hQt : PP ∈ p.R.toRealDat.toLevCh.Q (p.R.mu w) := hloc.resolve_left hW0
    have hS1 : PP.under (𝓞 D.host.F) ∉ S1 D := fun h => hW0 (by
      rw [d.G.pl.w_Q _ PP hQt h]
      exact Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem h))
    have hram : ¬ (p.R.toRealDat.toLevCh.xiH (p.R.mu w)).UnrAt PP := (hlev.Q_ram _ PP).2 (Or.inl hQt)
    rw [hxi] at hram
    by_cases hd : (p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w))).UnrAt PP
    · have hψ : ¬ (p.Tp.psi (D.plEq.symm w)).UnrAt PP := fun h => hram (hd.mul h)
      have hmem : PP ∈ ex.nch.Q (D.plEq.symm w) := by
        by_contra hn
        exact hψ (((p.Tp.psi_is _ htw).ram PP).2 hn)
      have hS0 : PP ∈ D.ntw.S0 (ex.nch.twI (D.plEq.symm w)) := D.ntw.twistExcludedPlaces_contains_residueChar _ (by rw [hl]; exact hlP)
      exact Finset.disjoint_left.1 hQ.2.1 hmem hS0
    · have hover : ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        unfold Formalism.L2.Host.CharFrame.delAt at hd
        split_ifs at hd
        · by_contra h
          exact hd (p.R.C.isDel'.unr PP fun h' => h (Or.inr h'))
        · by_contra h
          exact hd (p.R.C.isDel.unr PP fun h' => h (Or.inl h'))
      apply hS1
      rw [S1_mem_OmF]
      rcases hover with h | h
      · right; right; left
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
      · right; right; right
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
  intro hmem
  rw [Qn, Nat.cast_prod] at hmem
  obtain ⟨PP, hPP, hin⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hmem
  have : NeZero PP.asIdeal := ⟨PP.ne_bot⟩
  have hq : (Ideal.absNorm (PP.asIdeal.under ℤ)).Prime := Nat.absNorm_under_prime PP.asIdeal
  have : PP.asIdeal.LiesOver (Ideal.span {((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ)}) :=
    Int.liesOver_span_absNorm PP.asIdeal
  rw [Ideal.absNorm_eq_pow_inertiaDeg' PP.asIdeal hq, Nat.cast_pow] at hin
  have hqw := w.isPrime.mem_of_pow_mem _ hin
  have hqP : ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h : algebraMap ℤ (𝓞 D.host.E) ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ) ∈ PP.asIdeal :=
      Ideal.absNorm_mem (PP.asIdeal.under ℤ)
    rw [eq_intCast, Int.cast_natCast] at h
    exact h
  have e := resChar_eq (D.plEq.symm w) hq (by rw [Equiv.apply_symm_apply]; exact hqw)
  exact key PP hPP (e ▸ hqP)

end GlobalTheory.ThmAUpper
