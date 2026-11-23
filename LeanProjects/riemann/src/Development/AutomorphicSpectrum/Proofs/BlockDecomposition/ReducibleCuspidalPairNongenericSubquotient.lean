import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGenericStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankEqProdOfNonemptyEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwKerWhitCharReflect
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspPair

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem apply_mem_twKer {σ : Representation ℂ G V} {τ : Representation ℂ G W} (q : σ.IntertwiningMap τ)
    (H : Subgroup G) (χ : H →* ℂˣ) {v : V} (hv : v ∈ twKer σ H χ) : q v ∈ twKer τ H χ := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, u, rfl⟩ := hx
    refine Submodule.subset_span ⟨n, q u, ?_⟩
    rw [map_sub, map_smul, q.isIntertwining]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem exists_subquotient_subsingleton [TopologicalSpace G] [IsTopologicalGroup G] (π : Representation ℂ G V)
    (H : Subgroup G) (χ : H →* ℂˣ) (hs : IsSmooth π) (hf : HasFiniteLength π) (hn : ¬ π.IsIrreducible)
    (h1 : Module.finrank ℂ (TwJacquet π H χ) = 1)
    (hr : ∀ (S : Subrepresentation π) (v : S.toSubmodule), (v : V) ∈ twKer π H χ → v ∈ twKer S.toRepresentation H χ) :
    ∃ τ : IrrRep G, IsSubquotient τ.ρ π ∧ Subsingleton (TwJacquet τ.ρ H χ) := by
  have hq1 : Nontrivial (TwJacquet π H χ) := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  have hV : Nontrivial V := (Submodule.mkQ_surjective (twKer π H χ)).nontrivial
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨S, hS0, hST⟩ : ∃ S : Subrepresentation π, S ≠ ⊥ ∧ S ≠ ⊤ := by
    by_contra hc
    push_neg at hc
    exact hn { exists_pair_ne := ⟨⊥, ⊤, hbt⟩
               eq_bot_or_eq_top := fun S => (eq_or_ne S ⊥).imp_right (hc S) }
  by_cases hSK : S.toSubmodule ≤ twKer π H χ
  · let i : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun g => rfl⟩
    have hi : Function.Injective i := Subtype.val_injective
    have hsq := IsSubquotient.of_injective i hi
    have hSn : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 fun h =>
      hS0 (by ext v; rw [h]; rfl)
    obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient S.toRepresentation
      (hsq.isSmooth hs) (GlobalTheory.ProdLength.hasFiniteLength_of_injective i hi hf) hSn
    refine ⟨⟨Y, τ, hτs, hτi⟩, ⟨S, q, hq⟩, ?_⟩
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
    obtain ⟨v, rfl⟩ := hq w
    exact apply_mem_twKer q H χ (hr S v (hSK v.2))
  · obtain ⟨s, hsS, hsK⟩ := SetLike.not_le_iff_exists.1 hSK
    have hs0 : (Submodule.mkQ (twKer π H χ)) s ≠ 0 := fun h => hsK ((Submodule.Quotient.mk_eq_zero _).1 h)
    have hline := (finrank_eq_one_iff_of_nonzero' _ hs0).1 h1
    let U : Submodule ℂ V := S.toSubmodule
    have hU : ∀ g, U ≤ U.comap (π g) := fun g v hv => S.apply_mem_toSubmodule g hv
    let σ : Representation ℂ G (V ⧸ U) := π.quotient U hU
    let p : π.IntertwiningMap σ := ⟨U.mkQ, fun g => by ext v; rfl⟩
    have hp : Function.Surjective p := Submodule.mkQ_surjective U
    have hsq := IsSubquotient.of_surjective p hp
    have hUn : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 fun h =>
      hST (by ext v; rw [show S.toSubmodule = ⊤ from h]; rfl)
    have hfq : HasFiniteLength σ := IsFiniteLength.of_surjective hf
      (f := Representation.IntertwiningMap.equivLinearMapAsModule π σ p) hp
    obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ := GlobalTheory.SmGL.IrrQuot.exists_irreducible_smooth_quotient σ
      (hsq.isSmooth hs) hfq hUn
    refine ⟨⟨Y, τ, hτs, hτi⟩, (IsSubquotient.of_surjective q hq).trans hsq, ?_⟩
    refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
    obtain ⟨b, rfl⟩ := hq w
    obtain ⟨v, rfl⟩ := hp b
    obtain ⟨c, hc⟩ := hline (Submodule.mkQ _ v)
    have hk : v - c • s ∈ twKer π H χ := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      exact sub_eq_zero.2 hc.symm
    have hpe : p v = p (v - c • s) := by
      have h0 : p (c • s) = 0 := (Submodule.Quotient.mk_eq_zero U).2 (U.smul_mem c hsS)
      have h2 : v = (v - c • s) + c • s := by abel
      conv_lhs => rw [h2, map_add, h0, add_zero]
    rw [hpe]
    exact apply_mem_twKer q H χ (apply_mem_twKer p H χ hk)

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finrank_twJacquet_of_isCusp (hW : WhitRankIrr k) {ψ : AddChar k Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1)
    {x : IrrGL k} (hx : x.IsCusp) :
    Module.finrank ℂ (TwJacquet x.rep (unipB k (Fin x.1)) (whitChar ψ x.1)) = 1 := by
  obtain ⟨d, c⟩ := x
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have := hx.1; simp at this; omega⟩
  have hV : Nontrivial c.rep.V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨a, b, hab⟩ := c.rep.irr.exists_pair_ne
    refine hab ?_
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => b.toSubmodule.zero_mem, fun _ => a.toSubmodule.zero_mem⟩
  have hg : IsGenericFor ψ c.rep.ρ := GlobalTheory.T.cuspidal_is_generic k ψ hc h1 n _ c.rep.ρ hx.2 hV
  have hle := hW ψ hc h1 (n + 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  haveI : Nontrivial (TwJacquet c.rep.ρ (unipB k (Fin (n + 1))) (whitChar ψ (n + 1))) := hg
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle (Cardinal.one_le_iff_pos.2 rank_pos))

theorem exists_nongeneric_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitRankIrr k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N), x.IsCusp → y.IsCusp →
      ¬ (prodIrr ![x, y] hd).IsIrreducible →
      ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ (prodIrr ![x, y] hd) ∧ ¬ IsGenericFor ψ τ.ρ := by
  intro k _ _ _ _ hW ψ hc h1 x y N hd hx hy hn
  have hcusp : ∀ a, (![x, y] a).IsCusp := Fin.forall_fin_two.2 ⟨hx, hy⟩
  have hP := GlobalTheory.CompanionTheory.WhitRank.whitRankProd_of_heredity k (GlobalTheory.T.whittaker_heredity k) ψ hc h1 2 N ![x, y] hd
  have hrank : Module.finrank ℂ (TwJacquet (prodIrr ![x, y] hd) (unipB k (Fin N)) (whitChar ψ N)) = 1 :=
    hP.trans (Finset.prod_eq_one fun a _ => finrank_twJacquet_of_isCusp hW hc h1 (hcusp a))
  have hf : HasFiniteLength (prodIrr ![x, y] hd) :=
    GlobalTheory.ProdFiniteLength.multiProd_hasFiniteLength GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k 2 N
      (fun a => (![x, y] a).1) (fun a => GlobalTheory.SplitRead.Irr.ofIrrRep (![x, y] a).2.rep) _
  have hs := isSmooth_prodIrr ![x, y] hd
  obtain ⟨τ, hτ, hsub⟩ := exists_subquotient_subsingleton (prodIrr ![x, y] hd) (unipB k (Fin N)) (whitChar ψ N) hs hf hn hrank
    fun S v hv => by
      let i : S.toRepresentation.IntertwiningMap (prodIrr ![x, y] hd) := ⟨S.toSubmodule.subtype, fun g => rfl⟩
      exact GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hc N S.toRepresentation (prodIrr ![x, y] hd)
        ((IsSubquotient.of_injective i Subtype.val_injective).isSmooth hs) hs S.toSubmodule.subtype
        Subtype.val_injective (fun g v => rfl) v hv
  exact ⟨τ, hτ, not_nontrivial_iff_subsingleton.2 hsub⟩

end Local

end GlobalTheory.CompanionTheory.CuspPair

end
