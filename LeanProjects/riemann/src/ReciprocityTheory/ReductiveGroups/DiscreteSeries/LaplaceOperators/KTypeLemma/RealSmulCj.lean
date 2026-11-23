import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.OfDInjective

noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
  {ε : Fin n → Bool}

def sdd (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) : Cj H →L[ℂ] Cj H :=
  opCj (σ (sub g))

theorem urep_sdd {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (UJset (ε ∘ Fin.rev)) (sdd σ) := by
  obtain ⟨⟨h1, hm⟩, hn, hc⟩ := hσ
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold sdd; rw [sub_one, h1]; rfl
  · intro a ha b hb; unfold sdd; rw [sub_mul, hm _ (inUJ_sub ha) _ (inUJ_sub hb)]; rfl
  · intro g hg v; exact hn _ (inUJ_sub hg) (ofCj v)
  · intro v
    have hcs : Continuous (sub : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      continuous_id.matrix_submatrix _ _
    exact (hc (ofCj v)).comp hcs.continuousOn (fun g hg => inUJ_sub hg)

theorem smul_ofD (c : ℂ) (u : D) : c • ofD u = ofD (conj c • u) := by
  rw [ofD_smul]; simp

theorem sum_rev_swap {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    ∑ a, ∑ b, F a b = ∑ a, ∑ b, F (Fin.rev b) (Fin.rev a) := by
  rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Fin.revPerm]
  rfl

theorem actM_Edd {E : Fin n → Fin n → Module.End ℂ D} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG (ε ∘ Fin.rev) X) (u : D) : actM (Edd ε E) X (ofD u) = ofD (actM E (sub X) u) := by
  unfold actM
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Edd_ofD, smul_ofD, ofD_sum]
  rw [sum_rev_swap]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.rev_rev, sub_apply, smul_smul]
  congr 2
  have he := inG_entry hX (Fin.rev b) (Fin.rev a)
  simp only [Function.comp_apply, Fin.rev_rev] at he
  rw [he]
  unfold sg
  simp only [Fin.rev_rev]
  cases ε a <;> cases ε b <;> simp

theorem real_smul_cj (r : ℝ) (x : Cj H) : r • x = toCj (r • ofCj x) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ) r (ofCj x),
    ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace.smul_def, RCLike.conj_ofReal]

def toCjR : H →L[ℝ] Cj H where
  toFun := toCj
  map_add' _ _ := rfl
  map_smul' r x := (real_smul_cj r (toCj x)).symm
  cont := continuous_id

theorem derived_sdd {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
    (hD : IsDerivedOn ε σ D E) : IsDerivedOn (ε ∘ Fin.rev) (sdd σ) (cjSub D) (Edd ε E) where
  glRep := glRep_Edd ε hD.glRep
  kStable k hk v hv := hD.kStable (sub k) (K_sub hk) (ofCj v) hv
  deriv X hX v := by
    have h3 := hD.deriv (sub X) (inG_sub hX) (toD v)
    have h4 := (toCjR (H := H)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
    have hv : v = ofD (toD v) := rfl
    rw [hv, actM_Edd hX]
    convert h4 using 1
    · funext t
      simp only [sdd, Function.comp_apply, ← exp_sub, sub_smul]
      rfl
    · rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal
