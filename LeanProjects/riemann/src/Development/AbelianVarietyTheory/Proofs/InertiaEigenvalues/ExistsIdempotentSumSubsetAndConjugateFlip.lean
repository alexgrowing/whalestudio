import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemOrth
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.IdemFlip

theorem idemSum_sub_and_flip : ∀ (D : D7) (e : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → T ⊆ P →
    (∃ eT : AE D, IsIdemSum eT T) ∧ ∃ e' : AE D, IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) := by
  intro D e P T he hT
  have hnc := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he
  obtain ⟨⟨es, hes, hsum⟩, h0⟩ := he
  have hmul : ∀ S R : Finset (Formalism.L2.DIV.Pl D.host.E), S ⊆ R → R ⊆ P →
      (∑ a ∈ S, es a) * (∑ b ∈ R, es b) = ∑ a ∈ S, es a := by
    intro S R hSR hRP
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single a]
    · exact (hes a (hRP (hSR ha))).1.1
    · intro b hb hba
      exact Formalism.IndefR.Fin.idem_orth (hnc a (hRP (hSR ha)) a (hRP (hSR ha))) (hes a (hRP (hSR ha))) (hes b (hRP hb))
        (Ne.symm hba)
    · intro h; exact absurd (hSR ha) h
  have h1 : (∑ a ∈ T, es a) * e = ∑ a ∈ T, es a := by rw [hsum]; exact hmul T P hT subset_rfl
  have h2 : (∑ a ∈ T, es a) * (∑ a ∈ T, es a) = ∑ a ∈ T, es a := hmul T T subset_rfl hT
  have hTT : (∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a) = 0 := by
    calc (∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a)
        = ((∑ a ∈ T, es a) * e) * cA D ((∑ a ∈ T, es a) * e) := by rw [h1]
      _ = ((∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a)) * (e * cA D e) := by rw [map_mul]; ring
      _ = 0 := by rw [h0, mul_zero]
  have hIT : IsIdemSum (∑ a ∈ T, es a) T := ⟨⟨es, fun a ha => hes a (hT ha), rfl⟩, hTT⟩
  refine ⟨⟨_, hIT⟩, ?_⟩
  obtain ⟨⟨es2, hes2, hsum2⟩, -⟩ := Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hIT
  have hdisj : Disjoint (P \ T) (T.image Formalism.L2.DIV.conjPl) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha'
    exact hnc b (hT hb) _ (Finset.mem_sdiff.1 ha).1 (fun c hc => ⟨Formalism.L2.DIV.starO c,
      (Formalism.L2.DIV.isConjPl_conjPl b c _ (by rw [Formalism.L2.DIV.starO_coe])).1 hc, by rw [Formalism.L2.DIV.starO_coe]⟩)
  have hf : ∑ a ∈ P \ T, es a = e - ∑ a ∈ T, es a := by
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff hT, hsum]
  refine ⟨(e - ∑ a ∈ T, es a) + cA D (∑ a ∈ T, es a),
    ⟨⟨fun a => if a ∈ P \ T then es a else es2 a, ?_, ?_⟩, ?_⟩⟩
  · intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · simp only [if_pos h]; exact hes a (Finset.mem_sdiff.1 h).1
    · simp only [if_neg (Finset.disjoint_right.1 hdisj h)]; exact hes2 a h
  · rw [Finset.sum_union hdisj, ← hf, hsum2]
    congr 1
    · exact Finset.sum_congr rfl fun a ha => (if_pos ha).symm
    · exact Finset.sum_congr rfl fun a ha => (if_neg (Finset.disjoint_right.1 hdisj ha)).symm
  · generalize (∑ a ∈ T, es a) = t at h1 h2 hTT ⊢
    have h4 : cA D t * cA D e = cA D t := by rw [← map_mul, h1]
    have h5 : cA D t * cA D t = cA D t := by rw [← map_mul, h2]
    rw [map_add, map_sub, Formalism.L2.Theta.cA_cA]
    linear_combination h0 - (-(e) * h4 + cA D t * h0) + h1 - (-(cA D e) * h1 + t * h0)
      + 2 * hTT - h2 + h4 - h5

end GlobalTheory.IdemFlip
