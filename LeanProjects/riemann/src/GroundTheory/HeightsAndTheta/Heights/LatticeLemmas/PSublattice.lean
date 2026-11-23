import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField GroundTheory.Heights₂.Heights

noncomputable section

theorem gramDet_sub {K : Type*} [Field K] [NumberField K] (M : HermitianBundle K)
    (F : Submodule (𝓞 K) M.carrier) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → F) :
    gramDet (M.sub F).metric σ s = gramDet M.metric σ (fun i ↦ (s i : M.carrier)) := by
  have hG : (Matrix.gram ℂ fun i ↦ fibreVec (M.sub F).metric σ (s i)) =
      Matrix.gram ℂ fun i ↦ fibreVec M.metric σ (s i : M.carrier) := by
    ext i j
    rfl
  simp only [gramDet]
  rw [hG]

theorem card_quotient_span_sub {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E]
    [Module (𝓞 K) E] (F : Submodule (𝓞 K) E) {ι : Type*} (s : ι → F) :
    Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : E))) =
      Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) * Nat.card (E ⧸ F) := by
  set S := Submodule.span (𝓞 K) (Set.range s)
  set T := Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : E))
  have hspan : T = S.map F.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  have hTF : T ≤ F := by
    rw [hspan]; exact Submodule.map_subtype_le F S
  rw [← Submodule.card_quotient_mul_card_quotient F T hTF]
  congr 1
  have hk : LinearMap.ker (T.mkQ ∘ₗ F.subtype) = S := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, hspan,
      Submodule.comap_map_eq_of_injective F.injective_subtype]
  have hr : LinearMap.range (T.mkQ ∘ₗ F.subtype) = F.map T.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hk, ← hr]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm

theorem Sublattice.proof : Sublattice.Statement := by
  intro K _ _ M F hF
  have : Module.Finite (𝓞 K) F := inferInstanceAs (Module.Finite (𝓞 K) (M.sub F).carrier)
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := F)
  have ht : LinearIndependent (𝓞 K) (fun i ↦ (s i : M.carrier)) :=
    hs.map' F.subtype (LinearMap.ker_eq_bot.mpr F.injective_subtype)
  have hcardF : Fintype.card (Fin (Module.finrank (𝓞 K) F)) = Module.finrank (𝓞 K) F :=
    Fintype.card_fin _
  have hcardM : Fintype.card (Fin (Module.finrank (𝓞 K) F)) = Module.finrank (𝓞 K) M.carrier := by
    rw [Fintype.card_fin, hF]
  have hdM : M.arithDegree = degreeWith M.metric (fun i ↦ (s i : M.carrier)) :=
    arithDegree_eq _ ht hcardM
  have hdF : (M.sub F).arithDegree = Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s))) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ (fun i ↦ (s i : M.carrier))) := by
    have h1 := arithDegree_eq (M.sub F).metric hs hcardF
    rw [HermitianBundle.arithDegree, h1]
    unfold degreeWith
    simp only [gramDet_sub]
    rfl
  have hfin := finite_quotient_span ht hcardM
  have hpos : 0 < Nat.card (M.carrier ⧸ Submodule.span (𝓞 K) (Set.range fun i ↦ (s i : M.carrier))) :=
    Nat.card_pos
  have hc := card_quotient_span_sub F s
  rw [hc] at hpos
  have ha : (0 : ℝ) < Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    exact_mod_cast Nat.pos_of_mul_pos_right hpos
  have hb : (0 : ℝ) < Nat.card (M.carrier ⧸ F) := by
    exact_mod_cast Nat.pos_of_mul_pos_left hpos
  have hsum : M.arithDegree = (M.sub F).arithDegree + Real.log (Nat.card (M.carrier ⧸ F)) := by
    rw [hdM, hdF, degreeWith, hc, Nat.cast_mul, Real.log_mul ha.ne' hb.ne']
    ring
  have hlog : 0 ≤ Real.log (Nat.card (M.carrier ⧸ F)) := Real.log_natCast_nonneg _
  have hdeg : M.deg = (M.sub F).deg + Real.log (Nat.card (M.carrier ⧸ F)) / Module.finrank ℚ K := by
    simp only [HermitianBundle.deg]
    rw [hsum, add_div]
  refine ⟨hdeg, ?_⟩
  rw [hdeg]
  exact le_add_of_nonneg_right (div_nonneg hlog (Nat.cast_nonneg _))

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
