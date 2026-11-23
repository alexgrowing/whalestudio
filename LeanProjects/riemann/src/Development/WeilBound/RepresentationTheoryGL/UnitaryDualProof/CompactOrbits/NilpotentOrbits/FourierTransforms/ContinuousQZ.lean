import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP
import GroundTheory.AutomorphicForms.WhittakerDistribution

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.T.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}

theorem continuous_qZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) :
    Continuous (qZ Z : Matrix (Fin n) (Fin n) k → _) := by
  unfold qZ
  exact continuous_pi fun i => (continuous_const.matrix_mul continuous_id).matrix_trace

theorem isClosed_Bz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (Bz Z) := by
  have : Bz Z = ⋂ a ∈ Z, {x : Matrix (Fin n) (Fin n) k | a * x = x * a} := by
    ext x
    simp [Bz]
  rw [this]
  exact isClosed_biInter fun a _ =>
    isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    (x : Matrix (Fin n) (Fin n) k) : qZ Z (g.val * x * g⁻¹.val) = qZ Z x := by
  funext i
  unfold qZ
  have hb := hg _ ((Module.finBasis k Z) i).2
  set b : Matrix (Fin n) (Fin n) k := ((Module.finBasis k Z) i : Matrix (Fin n) (Fin n) k)
  have h1 : b * (g.val * x * g⁻¹.val) = g.val * (b * x) * g⁻¹.val := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hb, Matrix.mul_assoc g.val b x]
  rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  have h2 : g⁻¹.val * g.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h2, Matrix.one_mul]

private theorem exists_term_d_sub_termMap_mem {X : Type} [TopologicalSpace X] {A : Set X} (hA : IsClopen A) {f : X → ℂ}
    (hf : f ∈ supportedIn (univ : Set X)) :
    (fun x => A.indicator 1 x * f x) ∈ supportedIn (univ : Set X) := by
  rw [mem_supportedIn] at hf ⊢
  obtain ⟨hlc, -⟩ := hf
  have hlc' : IsLocallyConstant f ∧ HasCompactSupport f := hlc
  refine ⟨?_, subset_univ _⟩
  have hi : IsLocallyConstant (A.indicator (1 : X → ℂ)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ A
    · filter_upwards [hA.isOpen.mem_nhds hx] with y hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hx] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  exact ⟨hi.mul hlc'.1, HasCompactSupport.mul_left hlc'.2⟩

theorem locQ_pf : LocQ (k := k) := by
  intro n Z hCR hfib ξ hsupp hinv f hf
  haveI : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  let W : Submodule ℂ (Sp k n → ℂ) :=
    { carrier := {w | ∀ V : Set (Fin (Module.finrank k Z) → k), IsClopen V →
        ξ (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x * w x) = 0}
      add_mem' := by
        intro a b ha hb V hV
        have e : (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x * (a + b) x) =
            (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x * a x) +
              (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x * b x) := by
          funext x
          simp only [Pi.add_apply]
          ring
        rw [e, map_add, ha V hV, hb V hV, add_zero]
      zero_mem' := by
        intro V hV
        simp only [Pi.zero_apply, mul_zero]
        exact map_zero ξ
      smul_mem' := by
        intro c a ha V hV
        have e : (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x * (c • a) x) =
            c • (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x * a x) := by
          funext x
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [e, map_smul, ha V hV, smul_zero] }
  have hp : Continuous (fun q : Sp k n => qZ Z q.1) := (continuous_qZ Z).comp continuous_fst
  have hC : IsClosed (Bz Z ×ˢ (univ : Set (Fin n → k))) := (isClosed_Bz Z).prod isClosed_univ
  have hf' : f ∈ supportedIn (univ : Set (Sp k n)) := by
    rw [mem_supportedIn] at hf ⊢
    exact ⟨hf.1, subset_univ _⟩
  have h1 : supportedIn (univ : Set (Sp k n)) ⊓ vanishingOn (Bz Z ×ˢ (univ : Set (Fin n → k))) ≤ W := by
    intro w hw
    rw [Submodule.mem_inf] at hw
    intro V hV
    refine hsupp _ (exists_term_d_sub_termMap_mem (hV.preimage hp) hw.1) ?_
    intro x hx
    have : w x = 0 := hw.2 x hx
    simp [this]
  have h2 : ∀ V : Set (Fin (Module.finrank k Z) → k), IsClopen V → ∀ w ∈ W,
      (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x * w x) ∈ W := by
    intro V hV w hw V' hV'
    have := hw (V ∩ V') (hV.inter hV')
    convert this using 2
    funext x
    by_cases ha : qZ Z x.1 ∈ V <;> by_cases hb : qZ Z x.1 ∈ V' <;> simp [Set.indicator, ha, hb]
  have hfW : f ∈ W := by
    refine mem_of_forall_fiber hC hp h1 h2 hf' ?_
    intro y
    by_contra hny
    obtain ⟨l, hlf, hlM⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hny inferInstance
    have hl0 : ∀ m ∈ W ⊔ supportedIn (univ : Set (Sp k n)) ⊓
        vanishingOn (Bz Z ×ˢ (univ : Set (Fin n → k)) ∩ (fun q : Sp k n => qZ Z q.1) ⁻¹' {y}), l m = 0 := by
      intro m hm
      have hm' : l m ∈ Submodule.map l (W ⊔ supportedIn (univ : Set (Sp k n)) ⊓
          vanishingOn (Bz Z ×ˢ (univ : Set (Fin n → k)) ∩ (fun q : Sp k n => qZ Z q.1) ⁻¹' {y})) :=
        Submodule.mem_map_of_mem hm
      rw [hlM] at hm'
      simpa using hm'
    apply hlf
    refine hfib y l ?_ ?_ f hf
    · intro g hg hgv
      apply hl0
      refine Submodule.mem_sup_right (Submodule.mem_inf.2 ⟨hg, ?_⟩)
      intro x hx
      apply hgv x
      show x ∈ (Bz Z ∩ qZ Z ⁻¹' {y}) ×ˢ (univ : Set (Fin n → k))
      exact ⟨⟨hx.1.1, hx.2⟩, trivial⟩
    · intro g hg h hh
      have hd : (fun q => h (act g q)) - h ∈ W := by
        intro V hV
        have hc := exists_term_d_sub_termMap_mem (hV.preimage hp) hh
        have e : (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x *
              ((fun q => h (act g q)) - h) x) =
            (fun q => (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x * h x) (act g q)) -
              (fun x => ((fun q : Sp k n => qZ Z q.1) ⁻¹' V).indicator 1 x * h x) := by
          funext x
          have hpx : qZ Z (act g x).1 = qZ Z x.1 := qZ_conj Z hg x.1
          by_cases ha : qZ Z x.1 ∈ V
          · have ha' : qZ Z (act g x).1 ∈ V := by
              rw [hpx]
              exact ha
            simp [Set.indicator, ha, ha']
          · have ha' : qZ Z (act g x).1 ∉ V := by
              rw [hpx]
              exact ha
            simp [Set.indicator, ha, ha']
        rw [e, map_sub, hinv g hg _ hc, sub_self]
      have hd' := hl0 _ (Submodule.mem_sup_left hd)
      rw [map_sub, sub_eq_zero] at hd'
      exact hd'
  have := hfW univ isClopen_univ
  simpa using this

end PositivityTheory.RgUd.T.Nil.Four
