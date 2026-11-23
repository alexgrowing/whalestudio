import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.DivisorFrames.MemIntAdelesAndIdealIffSplitEmbeddings

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem toEAf_surj' (D : D7) (z : EAf D) : ∃ a : AE D, toEAf D a = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x a => exact ⟨(show AF D.host.F from ((0, a) : _ × _)) ⊗ₜ x, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

private theorem evW_eq_piF {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (z : EAf D) : GlobalTheory.BotMatch.evW τ z = piF τ z := by
  obtain ⟨a, rfl⟩ := toEAf_surj' D z
  rw [GlobalTheory.BotMatch.evW_toEAf, piF_toEAf]

private theorem cpt_eq_one {D : D7} {e : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (h : IsIdemSum e S)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ S) : GlobalTheory.StdFrames.cpt w (toEAf D e) = 1 := by
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := h
  rw [map_sum, map_sum, Finset.sum_eq_single w (fun Q hQ hne => (GlobalTheory.StdFrames.cpt_of_isIdemAt (h1 Q hQ)).2 w hne.symm)
    (fun hn => absurd hw hn)]
  exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (h1 w hw)).1

private theorem conjPrime_notMem {D : D7} {e : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (h : IsIdemSum e S)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ S) : GlobalTheory.IdemSupport.cP w ∉ S := by
  intro hc
  have h1 := cpt_eq_one h hw
  have h2 := cpt_eq_one h hc
  have h3 := congrArg (fun x => GlobalTheory.StdFrames.cpt w (toEAf D x)) h.2
  simp only [map_mul, map_zero, h1, one_mul, GlobalTheory.StdFrames.toEAf_cA] at h3
  have h4 := GlobalTheory.StdFrames.cpt_sg_eq_zero (Q := w) (z := toEAf D e - 1) (by rw [map_sub, h2, map_one, sub_self])
  rw [map_sub, map_sub, map_one, map_one, h3, zero_sub, neg_eq_zero] at h4
  exact one_ne_zero h4

theorem UpperTheory.mem_intAf_and_inId_iff_splitComponents :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        ∀ (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (z : EAf D), toEAf D e₀ * z = z →
        (z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ v : P, piF (t v) z ∈ (ValuativeRel.valuation (Fv D.host.F v)).integer) ∧
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ S, w.asIdeal ^ c w) z ↔
          ∀ v : P, piF (t v) z ∈ GlobalTheory.SplitWeil.cball (unifAt v.1 ^ c (splitPrime (t v)))) := by
  intro D e₀ S hS P t hP ht c z hz
  have h1 : ∀ w, w ∈ S ↔ ∃ i : P, splitPrime (t i) = w := by
    intro w
    refine ⟨fun hw => ?_, fun ⟨i, hi⟩ => hi ▸ ht i⟩
    let i : P := ⟨w.under (𝓞 D.host.F), (hP _).2 ⟨w, hw, rfl⟩⟩
    refine ⟨i, ?_⟩
    have hu : (splitPrime (t i)).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := GlobalTheory.AdelicU.splitPrime_under (t i)
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu with h | h
    · exact h
    · exact absurd (h ▸ ht i) (conjPrime_notMem hS hw)
  have h2 : Function.Injective (fun i : P => splitPrime (t i)) := fun i j hij =>
    Subtype.ext ((GlobalTheory.AdelicU.splitPrime_under (t i)).symm.trans
      ((congrArg (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.under (𝓞 D.host.F)) hij).trans
        (GlobalTheory.AdelicU.splitPrime_under (t j))))
  have h := UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings D e₀ S hS P (fun v => v.1) t h1 h2 c z hz
  simp only [evW_eq_piF] at h
  exact h
