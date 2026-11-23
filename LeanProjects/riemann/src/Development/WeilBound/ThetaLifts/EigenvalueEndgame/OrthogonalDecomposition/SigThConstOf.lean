import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
import Development.WeilBound.ThetaLifts.LatticeBasics.SchToPol
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.ExistsFull

noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

open PositivityTheory.ThKEst

theorem chrW_inv_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F} {χ χ' : Chr F E}
    {t : E →ₐ[F] Fv F v} {x} (h : chrW (χ / χ') t x ≠ 1) : chrW (χ' / χ) t x ≠ 1 := fun e => h (by
  simp only [chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply] at e ⊢
  rw [map_div, div_eq_one] at e ⊢
  exact e.symm)

theorem sigThConst_of (hP : TriplePair) (hN : GoodNe) (hC : ConstOfGood) (h1 : LocDecomp) (h2 : PairLoc) (h3 : ThAut) :
    SigThConst := by
  classical
  intro F E _ _ _ _ _ σ B a a' G X om om' hT f hf hr μ D hμ hD
  obtain ⟨p, p', -⟩ := hP F E σ B a a' G X om om' hT
  have ha' : 2 ≤ a' := by have := hT.geo.aBig; omega
  have ha : 2 ≤ a := by have := hT.geo.lt; omega
  have g : ∀ v ∉ insert B.v₁ X.T, SplitsFully E v → X.Good v ∧ v ≠ B.v₁ := fun v hv hs =>
    ⟨⟨fun h => hv (Finset.mem_insert_of_mem h), hs⟩, fun h => hv (h ▸ Finset.mem_insert_self _ _)⟩
  refine ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨c, i⟩ := h3 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p μ D hμ hD f hr Ψ hΨ
    refine hC F E σ B a G.V _ _ hT.base hT.geo.hV ha (insert B.v₁ X.T) _ c i fun v hv hs u hu x => ?_
    obtain ⟨⟨t⟩, ht⟩ := hN F E σ B a a' G X om om' hT v (g v hv hs).1
    exact h2 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p _ _ _ _ _ _ _ _ p' rfl rfl v t (chrW_inv_ne (ht t)) μ D hμ hD f
      (h1 F E σ B a a' G X om om' hT f hf hr v (g v hv hs).1 (g v hv hs).2).2 Ψ hΨ u hu x
  · obtain ⟨c, i⟩ := h3 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' μ D hμ hD f hr Ψ hΨ
    refine hC F E σ B a' G.V' _ _ hT.base hT.geo.hV' ha' (insert B.v₁ X.T) _ c i fun v hv hs u hu x => ?_
    obtain ⟨⟨t⟩, ht⟩ := hN F E σ B a a' G X om om' hT v (g v hv hs).1
    exact h2 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' _ _ _ _ _ _ _ _ p (add_comm _ _) rfl v t (ht t) μ D hμ hD f
      (h1 F E σ B a a' G X om om' hT f hf hr v (g v hv hs).1 (g v hv hs).2).1 Ψ hΨ u hu x

theorem orthIso_of (hB : ThetaBasic) (hP : TriplePair) (hW : WeilConv) (hD : DomSoU) (hF : SoFin) (hS : PolSch) (hN : GoodNe)
    (h1 : SigRapid) (h2 : SigThConst) (h3 : ThZero) (h4 : ThPerp) : OrthIso := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT f hf hc
  obtain ⟨p, p', w⟩ := hP F E σ B a a' G X om om' hT
  have hr := h1 F E σ B a a' G X om om' hT f hf hc
  have hk := h2 F E σ B a a' G X om om' hT f hf hr
  have hn := (hN F E σ B a a' G X om om' hT _ hT.chars.good).2
  have e1 := hT.geo.aBig
  have e2 := hT.geo.lt
  have e3 := hT.geo.eBig
  refine ⟨fun hp Φ hΦ => ?_, fun hq Φ hΦ => ?_⟩
  · have s := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p Φ hΦ
    obtain ⟨c1, c2⟩ := (hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p (Or.inl w)).1 Φ s
    exact h4 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p f hr Φ s c1 c2 fun μ D hμ hD =>
      h3 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p (by omega) hp (by omega) (by omega)
        (fun t e => chrW_inv_ne (hn t) (by rw [e]; rfl)) μ D hμ hD f hr (hk μ D hμ hD).1 Φ s
  · have s := hS F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' Φ hΦ.1
    obtain ⟨m, f₀, φ, hφ, rfl⟩ := (hF F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p').1 Φ hΦ.2
    obtain ⟨c1, c2, -⟩ := dom_sum hB p' (dom_of_domSoU hD p') f₀ φ hφ fun i => (hφ i).1
    exact h4 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' f hr _ s c1 c2 fun μ D hμ hD =>
      h3 F E σ B _ _ _ _ _ _ _ _ _ _ _ _ p' hq (by omega) (by omega) (by omega)
        (fun t e => hn t (by rw [Chars.ν, e]; rfl)) μ D hμ hD f hr (hk μ D hμ hD).2 _ s

end PositivityTheory.ThKEnd.Orth

end
