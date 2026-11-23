import Mathlib
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength

open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

theorem getElem_of_canonList_eq {g : ℕ} [Fact g.Prime] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (Q : List (GlobalTheory.GLq.Pc g))
    (h : canonList b lam = Q) (c : Fin s) (hc : (c : ℕ) < Q.length) :
    Q[(c : ℕ)] = ⟨Fintype.card {i // b i = c},
      fun x => (Formalism.IrreducibleCountingLemmas.TYPES.transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ := by
  subst h
  have e : (List.finRange s)[(c : ℕ)]'(by simp) = c := by simp
  simp only [canonList, List.getElem_map]
  rw [e]

theorem hasLabelO_of_hasLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) → P = O.lab d V) → (∀ (d : ℕ) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCusp χ → ∃ V : FDRep ℂ (GL (Fin d) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = χ x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → (∀ (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f := by
  intro g _ L C O hU hReal hTr hCon hSurj r τ f hτ hL
  obtain ⟨Q, hQ, hdeg, hf, hip⟩ := hL
  subst hdeg
  have hQScusp : ∀ p ∈ (Q.map Prod.snd), 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hc : GlobalTheory.GLq.IsCusp q.2.2 := (hQ q hq).2.1
    exact ⟨hc.1, hReal _ _ hc⟩
  obtain ⟨b, lam, hb, hlam, hcan⟩ := hSurj (Q.map Prod.snd) hQScusp
  have key : ∀ c : Fin (Q.map Prod.snd).length, ∀ hcQ : (c : ℕ) < Q.length,
      Formalism.IrreducibleCountingLemmas.TYPES.labO O (lam c) = (Q[(c : ℕ)]'hcQ).1 := by
    intro c hcQ
    have hcusp := hQ _ (List.getElem_mem hcQ)
    have h2 : (Q[(c : ℕ)]'hcQ).2 = (Q.map Prod.snd)[(c : ℕ)] := by simp
    rw [h2, getElem_of_canonList_eq b lam (Q.map Prod.snd) hcan c c.2] at hcusp
    exact (hU _ _ _ hcusp.2.1.1 (Formalism.L2.PT.simple_transp _ (hlam c).1)
      (Formalism.L2.PT.isCuspidal_transp _ (hlam c).2) hcusp).symm
  refine ⟨(Q.map Prod.snd).length, b, lam, hb, hlam, ?_, ?_⟩
  · rw [hCon _ _ b lam τ hτ]
    have htr : (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam)
        (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) = GlobalTheory.GLq.hcL (Q.map Prod.snd) (GlobalTheory.GLq.degL (Q.map Prod.snd)) := by
      funext x
      rw [hTr _ _ b lam hb x, hcan]
    rw [htr]
    exact hip
  · have hlen : (Q.map Prod.fst).length = (Q.map Prod.snd).length := by simp
    rw [hf, ← Fin.prod_univ_getElem (Q.map Prod.fst)]
    refine Fintype.prod_equiv (finCongr hlen) _ _ (fun c => ?_)
    have hcQ : (c : ℕ) < Q.length := by simpa using c.2
    rw [key _ hcQ]
    simp

end GlobalTheory.SerCmp
