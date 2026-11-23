import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS.HeckeSum

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem heckeVec_finset_sum {ι : Type} (ρ : Representation ℂ G V) (K : Subgroup G) (s : Finset ι) (f : ι → ℂ)
    (h : ι → G → ℂ) (x : V) (hf : ∀ p ∈ s, {c : G ⧸ K | h p c.out ≠ 0}.Finite) :
    heckeVec ρ K (fun g => ∑ p ∈ s, f p * h p g) x = ∑ p ∈ s, f p • heckeVec ρ K (h p) x := by
  have e : ∀ c : G ⧸ K, (∑ p ∈ s, f p * h p c.out) • ρ c.out x =
      ∑ p ∈ s, f p • (h p c.out • ρ c.out x) := fun c => by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun p _ => mul_smul _ _ _
  unfold heckeVec
  rw [finsum_congr e, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_finsum]
  · intro p hp
    exact (hf p hp).subset fun c hc h0 => hc (by simp [h0])

theorem biInv_out {K : Subgroup G} {h : G → ℂ} (hh : IsBiInv K h) (g : G) :
    h ((g : G ⧸ K).out) = h g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  have e := hh 1 k g
  simp only [OneMemClass.coe_one, one_mul] at e
  rw [hk, e]

variable {A B : Type} [Group A] [Group B]

theorem finite_pair {KA : Subgroup A} {KB : Subgroup B} {fA : A → ℂ} {fB : B → ℂ}
    (hA : IsBiInv KA fA) (hB : IsBiInv KB fB) (fa : {c : A ⧸ KA | fA c.out ≠ 0}.Finite)
    (fb : {c : B ⧸ KB | fB c.out ≠ 0}.Finite) :
    {c : (A × B) ⧸ KA.prod KB | fA c.out.1 * fB c.out.2 ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image
    (f := fun c : (A × B) ⧸ KA.prod KB => (((c.out.1 : A ⧸ KA)), ((c.out.2 : B ⧸ KB))))
    ((fa.prod fb).subset ?_) ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : fA c.out.1 * fB c.out.2 ≠ 0 := hc
    refine ⟨?_, ?_⟩
    · change fA ((c.out.1 : A ⧸ KA).out) ≠ 0
      rw [biInv_out hA]
      exact left_ne_zero_of_mul hc'
    · change fB ((c.out.2 : B ⧸ KB).out) ≠ 0
      rw [biInv_out hB]
      exact right_ne_zero_of_mul hc'
  · intro c _ d _ e
    have e1 := QuotientGroup.eq.1 (congrArg Prod.fst e)
    have e2 := QuotientGroup.eq.1 (congrArg Prod.snd e)
    rw [← c.out_eq', ← d.out_eq']
    exact QuotientGroup.eq.2 (Subgroup.mem_prod.2 ⟨by simpa using e1, by simpa using e2⟩)

end Abstract

theorem heckeVec_Tj_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℂ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : V),
    heckeVec ρ (K2 a b w) (fun g => ∑ p ∈ s, f p * (Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2)) x =
      ∑ p ∈ s, f p • heckeVec ρ (K2 a b w) (fun g => Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2) x := by
  intro E _ _ _ a b w ϖ hϖ s f V _ _ ρ x
  refine heckeVec_finset_sum ρ (K2 a b w) s f
    (fun p g => Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2) x fun p _ => ?_
  have ha := Tj_mem_hecke (n := a) hϖ p.1
  have hb := Tj_mem_hecke (n := b) hϖ p.2
  exact finite_pair ha.1 hb.1 (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w a) ha.2)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm E w b) hb.2)

end GlobalTheory.CompanionTheory.CtS.HeckeSum
