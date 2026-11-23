import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOrderedFormSnoc

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc GlobalTheory.CompanionTheory.ExhGood

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isL_add_segment_of_injective_of_not_precedes [CharZero k] (HS : GlobalTheory.Published.StandardCosocleGL) (HL : LSocleGL k) (x : IrrGL k)
    (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = x.1) (s : Segment k) (𝔫 : Multiset (Segment k))
    (hs : IsLSeg s (y 0).rep) (hn : IsL 𝔫 (y 1).rep)
    (hf : ∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f)
    (hp : ∀ Δ ∈ 𝔫, ¬ Δ.Precedes s) :
    IsL (𝔫 + {s}) x.rep := by
  obtain ⟨c, t, ht, ⟨D, hD, hDt⟩, hcos⟩ := hn
  have hsum' : ∑ a : Fin c, (t a.rev).fst = (y 1).fst := by
    rw [← ht]
    exact Equiv.sum_comp Fin.revPerm (fun a => (t a).fst)
  have hsoc := HL 𝔫 c (y 1).fst t hsum' ⟨D, hD, hDt⟩ (y 1).rep ⟨c, t, ht, ⟨D, hD, hDt⟩, hcos⟩
  obtain ⟨_, g, hg, _⟩ := hsoc
  have hw_sum : ∑ a, ((Fin.snoc t (y 0) : Fin (c + 1) → IrrGL k) a).fst = x.fst := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [ht, ← hd, Fin.sum_univ_two]
    omega
  have hw_sum' : ∑ a : Fin (c + 1), ((Fin.snoc t (y 0) : Fin (c + 1) → IrrGL k) a.rev).fst = x.fst := by
    rw [← hw_sum]
    exact Equiv.sum_comp Fin.revPerm (fun a => ((Fin.snoc t (y 0) : Fin (c + 1) → IrrGL k) a).fst)
  have hLF : LFactors (𝔫 + {s}) (Fin.snoc t (y 0) : Fin (c + 1) → IrrGL k) := by
    refine ⟨Fin.snoc D s, isOrderedForm_snoc hD s hp, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last, Fin.snoc_last]
      exact hs
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hDt j
  obtain ⟨π, hπ⟩ := HS k (𝔫 + {s}) (c + 1) x.fst _ hw_sum hLF
  have hπL : IsL (𝔫 + {s}) π.ρ := ⟨c + 1, _, hw_sum, hLF, hπ⟩
  have hsoc2 := HL (𝔫 + {s}) (c + 1) x.fst _ hw_sum' hLF π.ρ hπL
  obtain ⟨F, hF⟩ := embed_family (N := x.fst) y ((Fin.snoc t (y 0) : Fin (c + 1) → IrrGL k) ∘ Fin.rev)
    (t ∘ Fin.rev) (by simp) (fun i => by simp [Fin.rev_succ]) hd hw_sum' hsum' g hg
  obtain ⟨f, hfi⟩ := hf
  obtain ⟨e⟩ := IsSocle.equiv_of_embeds hsoc2 x.snd.rep.irr ⟨F.comp f, hF.comp hfi⟩
  exact IsL.of_equiv hπL e.symm

theorem peelGoodP (h1 : GlobalTheory.Published.StandardCosocleGL) (h2 : Zc.LSocleGL k) (_h3 : RefineP k) [CharZero k] :
    Zc.PeelGoodP k := by
  intro x y hd Δ 𝔫 hs hn hf hp
  exact isL_add_segment_of_injective_of_not_precedes h1 h2 x y hd Δ 𝔫 hs hn hf hp

end PositivityTheory.Exh

end
