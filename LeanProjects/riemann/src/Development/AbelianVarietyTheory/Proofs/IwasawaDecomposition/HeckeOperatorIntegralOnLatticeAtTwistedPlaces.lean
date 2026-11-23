import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.NumberFieldFamilies.JMtInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem exists_preimage_comb {K L V W : Type} [Field K] [Field L] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    (σ : K →+* L) (f : V →ₛₗ[σ] W) (hf : Function.Injective f) (S : Finset W) (hS : ∀ y ∈ S, y ∈ Set.range f)
    (c : W → K) (x : V) (hx : f x = ∑ g ∈ S, σ (c g) • g) :
    ∃ F : Finset V, (↑F ⊆ {x : V | f x ∈ S}) ∧ x = ∑ y ∈ F, c (f y) • y := by
  classical
  refine ⟨S.preimage f hf.injOn, fun y hy => by simpa using hy, hf ?_⟩
  rw [hx, map_sum]
  simp only [LinearMap.map_smulₛₗ]
  exact (Finset.sum_preimage f S hf.injOn (fun g => σ (c g) • g) (fun g hg hn => absurd (hS g hg) hn)).symm

theorem heckeIntTw_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → HeckeIntTw (base M C hR X hS) := by
  intro D M C hR X hS tup hI hsp j w h1 h2 hw v k hg x hx
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨s, ϖ, hc, hu⟩ := hsp v hg.1
  obtain ⟨c, hc0, he⟩ := hI.int w ⟨j', by omega⟩ v k s ϖ hw hg hc hu _ hx
  have h3 := hLC_spec (mt0 M) C.Q hR (j' + 1) w v k h1 h2 hg s ϖ hc hu x
  have h4 := (M (D.what₂.muTw w) (j' + 1) h1 h2).real_inj (h3.trans he)
  obtain ⟨F, hF, hsum⟩ := exists_preimage_comb D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) (j' + 1))
    (LatticeFinitenessFree.jMt_injective _ _) _ (D.what₂.MtLat_sub _ _) c _ h4
  exact ⟨F, fun y => c (D.what₂.jMt (D.what₂.muTw w) (j' + 1) y), hF, fun y _ => hc0 _, hsum⟩

end GlobalTheory.HeckeLocN
