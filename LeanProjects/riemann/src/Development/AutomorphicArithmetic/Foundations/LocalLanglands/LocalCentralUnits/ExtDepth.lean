import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatible
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDim

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.extDepth :
    UpperTheory.Zero.LLC.ExtDepth := by
  intro E Ω _ _ _ _ _ A w h a ha r rc hr hext x hgood hdz
  rw [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly]
  intro σ hσ
  obtain ⟨⟨hdim, s, hsup, hcusp, hchar⟩, -⟩ := UpperTheory.Zero.LLC.extDim E Ω A w h a ha r rc hr hext x
  obtain ⟨s0, hsup0, hgc⟩ := hgood
  have hs : s0 = s := (UpperTheory.Zero.LLC.goodSeg _).2.2 x s0 s hsup0 hsup
  subst hs
  have hdzy : ∀ y ∈ s0, UpperTheory.Zero.LLC.DZ y := by
    obtain ⟨m, f, hf, hcs⟩ := hsup
    intro y hy
    rw [← hf] at hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
    have key := UpperTheory.Zero.LLC.Pr.dzs _ x.fst (GlobalTheory.SplitRead.Irr.ofIrrRep x.snd.rep) m (fun i => (f i).fst)
      (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (f i).snd.rep) hcs ((Submodule.ne_bot_iff _).mp hdz) i
    exact (Submodule.ne_bot_iff _).mpr key
  have htame : ∀ y ∈ s0, (r y).charPol σ = (X - 1) ^ y.fst := by
    intro y hy
    have hy' := hr.depth y (hcusp y hy) (hgc y hy) (hdzy y hy)
    rw [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly] at hy'
    rw [hy' σ hσ, hr.dim y (hcusp y hy)]
  rw [hchar σ, Multiset.map_congr rfl htame, GlobalTheory.LlcDepth.prod_map_pow (X - 1) Sigma.fst s0,
    HasSupport.sum_fst hsup, Fintype.card_fin, hdim]
