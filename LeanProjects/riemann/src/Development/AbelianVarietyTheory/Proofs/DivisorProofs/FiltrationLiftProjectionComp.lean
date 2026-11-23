import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomOfSecSecPowAppChartSec

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM resM_self)
open scoped Classical

namespace GlobalTheory.GrFilt

theorem proj_liftT_app {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules}
    {r : ι → ℕ} (o : ι → ℕ) (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a) (hm : FrameMem r o T u)
    (b : ι) (κ : (filtSub o T (o b + 1)).toMod ⟶ E' b) (hκ : IsProj r o T u b κ)
    {V : X.Opens} (f : ∀ a, Fin (r a) → Γ(E a, V)) (hf : ∀ a, IsFrame (f a)) (f' : ∀ a, Fin (r a) → Γ(E' a, V))
    (hf' : ∀ a, IsFrame (f' a)) (c : (Σ a, Fin (r a)) → Γ(L, V)) (hc : IsFrame c)
    (had : AdaptedAt o T u f f' hf' c hc) (i : Fin (r b)) :
    κ.app V ((liftT o T b).app V (f b i)) = (u b).app V (f b i) := by
  obtain ⟨t, -, ht⟩ := exists_isFrame_subP (filtSub o T (o b + 1)) c hc (fun z => o z.1 < o b + 1)
    (fun V' h a => (hm (o b + 1) V f hf f' hf' c hc had V' h a).trans (by simp only [not_lt]))
  set w := (hc.basis le_rfl).repr ((T b).app V (f b i)) with hw
  have h1 : (liftT o T b).app V (f b i) = ∑ z : {z : Σ a, Fin (r a) // o z.1 < o b + 1}, w z • t z := by
    apply (filtSub o T (o b + 1)).incl_app_injective V
    have e : (filtSub o T (o b + 1)).incl.app V ((liftT o T b).app V (f b i)) = (T b).app V (f b i) := rfl
    rw [e]
    conv_lhs => rw [← (hc.basis le_rfl).sum_repr ((T b).app V (f b i))]
    simp only [map_sum, Scheme.Modules.Hom.app_smul, ht, IsFrame.basis_apply, resM_self]
    symm
    refine Finset.sum_of_injOn Subtype.val Subtype.val_injective.injOn
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun j _ hj => ?_) (fun _ _ => rfl)
    rw [(had b i).1 j (by
      by_contra hq
      exact hj ⟨⟨j, by omega⟩, by simp, rfl⟩), zero_smul]
  rw [h1]
  conv_rhs => rw [← ((hf' b).basis le_rfl).sum_repr ((u b).app V (f b i))]
  simp only [map_sum, Scheme.Modules.Hom.app_smul, IsFrame.basis_apply, resM_self]
  symm
  refine Finset.sum_of_injOn (fun j => ⟨⟨b, j⟩, Nat.lt_succ_self _⟩) ?_
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun z _ hz => ?_) (fun j _ => ?_)
  · intro j _ j' _ h
    simpa using h
  · rw [hκ V f hf f' hf' c hc had z.1 (t z) (ht z), dif_neg, smul_zero]
    obtain ⟨⟨a, j⟩, hz'⟩ := z
    intro h
    dsimp only at h
    subst h
    exact hz ⟨j, by simp, rfl⟩
  · rw [hκ V f hf f' hf' c hc had ⟨b, j⟩ (t ⟨⟨b, j⟩, Nat.lt_succ_self _⟩) (ht _), dif_pos rfl, ← (had b i).2 j]
    rfl

theorem liftT_comp_proj : ∀ {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules}
    {r : ι → ℕ} (o : ι → ℕ), Function.Injective o → ∀ (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a),
    (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ LocAdapted r o T u V) → FrameMem r o T u →
    ∀ (b : ι) (κ : (filtSub o T (o b + 1)).toMod ⟶ E' b), IsProj r o T u b κ → liftT o T b ≫ κ = u b := by
  intro X _ ι _ L E E' r o _ T u hloc hm b κ hκ
  refine GlobalTheory.LinePow.hom_ext_of_frames (ι := Fin (r b)) fun x => ?_
  obtain ⟨V, hx, hV⟩ := hloc x
  obtain ⟨f, hf, f', hf', c, hc, had⟩ := (locAdapted_iff o T u V).1 hV
  exact ⟨V, f b, hx, hf b, fun i => proj_liftT_app o T u hm b κ hκ f hf f' hf' c hc had i⟩

end GlobalTheory.GrFilt
