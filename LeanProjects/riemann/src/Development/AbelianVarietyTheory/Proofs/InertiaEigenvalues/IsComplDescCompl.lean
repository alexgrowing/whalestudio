import Mathlib
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DeterminantInTorus
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseChangeInertUnramified
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

namespace GlobalTheory.RetractionComplement

open Formalism.MainNotions.N Matrix

section SlopeTestRemainingChoices

variable {k k' : Type} [Field k] [Field k'] [Algebra k k'] {n : ℕ}

theorem exists_retraction : ∃ l : k' →ₗ[k] k, ∀ c : k, l (algebraMap k k' c) = c := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k k')
    (LinearMap.ker_eq_bot.mpr (algebraMap k k').injective)
  exact ⟨g, fun c => by simpa using LinearMap.congr_fun hg c⟩

theorem form_mulVec (l : k' →ₗ[k] k) (A : Matrix (Fin n) (Fin n) k) (x : Fin n → k') :
    (fun i => l ((A.map (algebraMap k k')).mulVec x i)) = A.mulVec (fun i => l (x i)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem ext_mulVec (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    (A.map (algebraMap k k')).mulVec (fun i => algebraMap k k' (v i))
      = fun i => algebraMap k k' (A.mulVec v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

def extSub (k' : Type) [Field k'] [Algebra k k'] (W : Submodule k (Fin n → k)) :
    Submodule k' (Fin n → k') :=
  Submodule.span k' ((fun (v : Fin n → k) (i : Fin n) => algebraMap k k' (v i)) '' W)

theorem form_mem (l : k' →ₗ[k] k) (W : Submodule k (Fin n → k)) (x : Fin n → k')
    (hx : x ∈ extSub k' W) : (fun i => l (x i)) ∈ W := by
  have key : ∀ c : k', (fun i => l (c * x i)) ∈ W := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      intro c
      convert W.smul_mem (l c) hw using 1
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    | zero =>
      intro c
      convert W.zero_mem using 1
      funext i
      simp
    | add y z _ _ hy hz =>
      intro c
      convert W.add_mem (hy c) (hz c) using 1
      funext i
      simp [mul_add]
    | smul a y _ hy =>
      intro c
      convert hy (c * a) using 1
      funext i
      simp [mul_assoc]
  simpa using key 1

theorem extSub_stable (A : Matrix (Fin n) (Fin n) k) (W : Submodule k (Fin n → k))
    (hA : ∀ v ∈ W, A.mulVec v ∈ W) (x : Fin n → k') (hx : x ∈ extSub k' W) :
    (A.map (algebraMap k k')).mulVec x ∈ extSub k' W := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [ext_mulVec]
    exact Submodule.subset_span ⟨_, hA w hw, rfl⟩
  | zero =>
    rw [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hy

def descCompl (l : k' →ₗ[k] k) (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k')) :
    Submodule k (Fin n → k) where
  carrier := {v | ∃ x ∈ extSub k' W, ∃ u ∈ U, x + u = (fun i => algebraMap k k' (v i)) ∧
    (fun i => l (x i)) = 0}
  zero_mem' := ⟨0, Submodule.zero_mem _, 0, U.zero_mem, by funext i; simp, by funext i; simp⟩
  add_mem' := by
    rintro v w ⟨x, hx, u, hu, h1, h2⟩ ⟨x', hx', u', hu', h1', h2'⟩
    refine ⟨x + x', Submodule.add_mem _ hx hx', u + u', U.add_mem hu hu', ?_, ?_⟩
    · funext i
      have a := congrFun h1 i
      have b := congrFun h1' i
      simp only [Pi.add_apply, map_add] at a b ⊢
      rw [← a, ← b]; ring
    · funext i
      have a := congrFun h2 i
      have b := congrFun h2' i
      simp only [Pi.add_apply, map_add, Pi.zero_apply] at a b ⊢
      rw [a, b, add_zero]
  smul_mem' := by
    rintro c v ⟨x, hx, u, hu, h1, h2⟩
    refine ⟨algebraMap k k' c • x, Submodule.smul_mem _ _ hx, algebraMap k k' c • u,
      U.smul_mem _ hu, ?_, ?_⟩
    · funext i
      have a := congrFun h1 i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul] at a ⊢
      rw [← a]; ring
    · funext i
      have a := congrFun h2 i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a ⊢
      rw [← Algebra.smul_def, map_smul, a, smul_zero]

theorem isCompl_descCompl (l : k' →ₗ[k] k) (hl : ∀ c : k, l (algebraMap k k' c) = c)
    (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k'))
    (h : IsCompl (extSub k' W) U) : IsCompl W (descCompl l W U) := by
  have hmem : ∀ v ∈ W, (fun i => algebraMap k k' (v i)) ∈ extSub k' W :=
    fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩
  have hback : ∀ v : Fin n → k, (fun i => l (algebraMap k k' (v i))) = v :=
    fun v => funext fun i => hl (v i)
  constructor
  · rw [Submodule.disjoint_def]
    rintro v hv ⟨x, hx, u, hu, h1, h2⟩
    have hu' : u ∈ extSub k' W := by
      have e : u = (fun i => algebraMap k k' (v i)) - x := by rw [← h1]; abel
      rw [e]
      exact Submodule.sub_mem _ (hmem v hv) hx
    have hu0 : u = 0 := (Submodule.disjoint_def.mp h.disjoint) u hu' hu
    rw [hu0, add_zero] at h1
    rw [h1, hback] at h2
    exact h2
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : (fun i => algebraMap k k' (v i)) ∈ extSub k' W ⊔ U := by
      rw [h.sup_eq_top]
      trivial
    obtain ⟨x, hx, u, hu, hxu⟩ := Submodule.mem_sup.mp hv
    obtain ⟨w, hw⟩ : ∃ w : Fin n → k, w = fun i => l (x i) := ⟨_, rfl⟩
    have hwW : w ∈ W := hw ▸ form_mem l W x hx
    have hd : v - w ∈ descCompl l W U := by
      refine ⟨x - fun i => algebraMap k k' (w i), Submodule.sub_mem _ hx (hmem w hwW), u, hu, ?_, ?_⟩
      · funext i
        have e := congrFun hxu i
        simp only [Pi.add_apply, Pi.sub_apply, map_sub] at e ⊢
        rw [← e]
        ring
      · funext i
        simp [hw, hl]
    simpa using Submodule.add_mem_sup hwW hd

theorem descCompl_stable (l : k' →ₗ[k] k) (A : Matrix (Fin n) (Fin n) k)
    (W : Submodule k (Fin n → k)) (U : Submodule k' (Fin n → k'))
    (hA : ∀ v ∈ W, A.mulVec v ∈ W)
    (hU : ∀ u ∈ U, (A.map (algebraMap k k')).mulVec u ∈ U) :
    ∀ v ∈ descCompl l W U, A.mulVec v ∈ descCompl l W U := by
  rintro v ⟨x, hx, u, hu, h1, h2⟩
  refine ⟨(A.map (algebraMap k k')).mulVec x, extSub_stable A W hA x hx,
    (A.map (algebraMap k k')).mulVec u, hU u hu, ?_, ?_⟩
  · rw [← Matrix.mulVec_add, h1, ext_mulVec]
  · rw [form_mulVec, h2, Matrix.mulVec_zero]

end SlopeTestRemainingChoices

theorem isSSRep_of_mapRep {Γ k k' : Type} [Group Γ] [Field k] [Field k'] {n : ℕ}
    (ι : k →+* k') (ρ : Γ →* GL (Fin n) k) (h : IsSSRep (mapRep ι ρ)) : IsSSRep ρ := by
  let _ : Algebra k k' := ι.toAlgebra
  have hcoe : ∀ g, ((mapRep ι ρ g : GL (Fin n) k') : Matrix (Fin n) (Fin n) k') =
      (ρ g : Matrix (Fin n) (Fin n) k).map (algebraMap k k') := fun _ => rfl
  obtain ⟨l, hl⟩ := exists_retraction (k := k) (k' := k')
  intro W hW
  have hWe : IsInv (mapRep ι ρ) (extSub k' W) := fun g x hx => by
    rw [hcoe]
    exact extSub_stable _ W (hW g) x hx
  obtain ⟨U, hU, hc⟩ := h _ hWe
  refine ⟨descCompl l W U, fun g => ?_, isCompl_descCompl l hl W U hc⟩
  exact descCompl_stable l _ W U (hW g) fun u hu => by
    rw [← hcoe]
    exact hU g u hu

end GlobalTheory.RetractionComplement
