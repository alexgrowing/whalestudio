import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

noncomputable section

section Fold

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

def foldTensor {n : ℕ} (L : Fin n → Kleiman.LineBundle S x) (l : List (Fin n)) (Q : Kleiman.LineBundle S x) :
    Kleiman.LineBundle S x :=
  l.foldl (fun P i => P.tensor (L i)) Q

theorem foldTensor_toSubSystem {n : ℕ} (L : Fin n → Kleiman.LineBundle S x) (l : List (Fin n))
    (Q : Kleiman.LineBundle S x) :
    (foldTensor L l Q).toSubSystem = l.foldl (fun P i => P.twist (L i).toSubSystem) Q.toSubSystem := by
  induction l generalizing Q with
  | nil => rfl
  | cons a l ih =>
    rw [foldTensor, List.foldl_cons, List.foldl_cons, ← Kleiman.LineBundle.tensor_toSubSystem]
    exact ih _

end Fold

theorem realises_foldTensor (hT : TensorRealises.Statement)
    {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [Algebra F Ω] {y : (Σ k, ι k) → Ω} {k₀ : K} {N : ℕ} {e : ι k₀ ≃ Fin (N + 1)}
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) {n : ℕ}
    (L : Fin n → Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (δ : Fin n → K → ℤ)
    (hL : ∀ i, BundleRealises y k₀ (L i) (δ i)) (l : List (Fin n)) :
    ∀ (Q : Kleiman.LineBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (β : K → ℤ),
      BundleRealises y k₀ Q β → BundleRealises y k₀ (foldTensor L l Q) (β + (l.map δ).sum) := by
  induction l with
  | nil => intro Q β hQ; simpa [foldTensor] using hQ
  | cons a l ih =>
    intro Q β hQ
    have h := ih (Q.tensor (L a)) (β + δ a) (hT F K ι Ω y k₀ N e hmod Q (L a) β (δ a) hQ (hL a))
    rw [List.map_cons, List.sum_cons, ← add_assoc]
    exact h

theorem TensorRealise.proof (hT : TensorRealises.Statement) : TensorRealise.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n L δ hL T
  subst hx
  refine Filter.Eventually.of_forall fun c => ?_
  have h0 := BaseRealises.proof F K ι Ω y k₀ N e _ rfl hmod 0
  have h := realises_foldTensor hT hmod L δ hL ((List.finRange n).filter (· ∈ T)) _ _ h0 (c : ℤ)
  rw [foldTensor_toSubSystem, Kleiman.twistBundle_toSubSystem] at h
  have hsum : (((List.finRange n).filter (· ∈ T)).map δ).sum = ∑ i ∈ T, δ i := by
    rw [← List.sum_toFinset δ ((List.nodup_finRange n).filter _)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp
  rw [hsum, zero_smul, zero_add] at h
  exact h

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
