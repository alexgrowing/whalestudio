import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.HTSpanLeft
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

def RepM (f : Fin (r + 1) → S.V) (φ : S.V ≃ₗ[E] S.V) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Prop :=
  ∀ b, φ (f b) = ∑ c, A c b • f c

variable {f : Fin (r + 1) → S.V}

theorem apply_comb {φ : S.V ≃ₗ[E] S.V} {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : RepM f φ A)
    (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (b : Fin (r + 1)) :
    φ (∑ c, B c b • f c) = ∑ d, (A * B) d b • f d := by
  have h' : ∀ c, φ (f c) = ∑ d, A d c • f d := h
  simp only [map_sum, map_smul, h', Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]

theorem repM_mul {φ ψ : S.V ≃ₗ[E] S.V} {A B : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hA : RepM f φ A) (hB : RepM f ψ B) : RepM f (φ * ψ) (A * B) := fun b => by
  show φ (ψ (f b)) = _
  rw [hB b]
  exact apply_comb hA B b

theorem sum_one (a : Fin (r + 1)) : ∑ d, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) d a • f d = f a := by
  simp [Matrix.one_apply]

theorem repM_inv {n : S.V ≃ₗ[E] S.V} {N : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (h : RepM f n N)
    (hN : IsUnit N.det) : RepM f n⁻¹ N⁻¹ := fun b => by
  have key : n (∑ c, N⁻¹ c b • f c) = f b := by
    rw [apply_comb h, Matrix.mul_nonsing_inv N hN, sum_one]
  rw [← key]
  exact n.symm_apply_apply _

theorem exists_upUni {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}
    (hn : n ∈ NLam Λ F) :
    ∃ N : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni N ∧ RepM (frame F) n N := by
  obtain ⟨-, h1, h2⟩ := hn
  have hzo : ∀ x ∈ Submodule.span E (Set.range F.fl.e), S.hT x F.fl.z = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.fl.z_orth a
    | zero => simp
    | add y w _ _ hy hw => simp [hy, hw]
    | smul a y _ hy => simp [hy]
  have hzmem : F.fl.z ∈ orth S (Xsp F) := by
    simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
    exact fun x hx => hzo x hx
  have col : ∀ b : Fin (r + 1), ∃ v : Fin (r + 1) → E,
      (∀ c, b < c → v c = 0) ∧ v b = 1 ∧ n (frame F b) = ∑ c, v c • frame F c := by
    intro b
    cases b using Fin.lastCases with
    | last =>
      have hm : n F.fl.z - F.fl.z ∈ Submodule.span E (Set.range F.fl.e) := h2 _ hzmem
      obtain ⟨d, hd⟩ : ∃ d : Fin r → E, ∑ i, d i • F.fl.e i = n F.fl.z - F.fl.z := by
        rwa [Submodule.mem_span_range_iff_exists_fun] at hm
      refine ⟨Fin.snoc (α := fun _ => E) d 1, fun c hc => absurd hc (not_lt.2 (Fin.le_last c)), by simp, ?_⟩
      simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, one_smul]
      rw [hd]
      abel
    | cast i =>
      have hi : F.fl.e i ∈ Submodule.span E (F.fl.e '' {k : Fin r | k.1 < i.1 + 1}) :=
        Submodule.subset_span ⟨i, by simp, rfl⟩
      have hm : n (F.fl.e i) - F.fl.e i ∈ Submodule.span E (F.fl.e '' {k : Fin r | k.1 < i.1}) := h1 i.1 _ hi
      obtain ⟨l, hl, hle⟩ : ∃ l ∈ Finsupp.supported E E {k : Fin r | k.1 < i.1},
          Finsupp.linearCombination E F.fl.e l = n (F.fl.e i) - F.fl.e i := by
        rw [← Finsupp.mem_span_image_iff_linearCombination]
        exact hm
      rw [Finsupp.mem_supported'] at hl
      have hli : l i = 0 := hl i (by simp)
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l (fun k a => a • F.fl.e k) (fun k => zero_smul E _)] at hle
      refine ⟨Fin.snoc (α := fun _ => E) (fun k => if k = i then 1 else l k) 0, ?_, by simp, ?_⟩
      · intro c hc
        cases c using Fin.lastCases with
        | last => simp
        | cast k =>
          have hik : i < k := Fin.castSucc_lt_castSucc_iff.1 hc
          simp only [Fin.snoc_castSucc, if_neg (ne_of_gt hik)]
          exact hl k (by simp only [Set.mem_setOf_eq, not_lt]; exact Fin.le_iff_val_le_val.1 hik.le)
      · have key : ∀ k, (if k = i then (1 : E) else l k) = l k + if k = i then 1 else 0 := by
          intro k
          split_ifs with h
          · simp [h, hli]
          · simp
        simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, zero_smul, add_zero, key, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [hle]
        abel
  choose v hv0 hv1 hvn using col
  refine ⟨fun c b => v b c, ?_, ?_⟩
  · intro i j
    exact ⟨fun hji => hv0 j i hji, fun hij => by subst hij; exact hv1 i⟩
  · intro b
    exact hvn b

end Gen

end Formalism.L2.SG.Pf.RelativeIndexFlags
