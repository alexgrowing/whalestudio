import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.GramSt

namespace ReciprocityTheory.GeometryOfNumbersTheory.HadamardFrameExtension

open NumberField Module ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem qf_im_eq_zero {n : ℕ} (F : Fin n → Fin n → ℂ) (hF : ∀ i j, starRingEnd ℂ (F i j) = F j i)
    (c : Fin n → ℂ) : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * F i j).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simp only [map_sum, map_mul, Complex.conj_conj, hF]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_append_frame {E : Submodule (𝓞 K) V} {a r : ℕ} (u0 : Fin a → V)
    (hu0 : LinearIndependent K u0) (hu0E : ∀ i, u0 i ∈ E) (w : Fin r → V) (hw : IsFrame K E w) :
    ∃ m, ∃ w' : Fin m → V, (∀ j, ∃ i, w' j = w i) ∧ IsFrame K E (Fin.append u0 w') := by
  classical
  unfold IsFrame at hw
  obtain ⟨hwE, -, hwspan⟩ := hw
  obtain ⟨b, hbt, hsb, hspan, hb⟩ := exists_linearIndepOn_id_extension
    (by first
      | exact hu0.linearIndepOn_id_range
      | exact (linearIndepOn_id_range_iff hu0.injective).2 hu0
      | exact hu0.to_subtype_range)
    (Set.subset_union_left : Set.range u0 ⊆ Set.range u0 ∪ Set.range w)
  have hTfin : (b \ Set.range u0).Finite := (Set.finite_range w).subset (by
    intro x hx
    rcases hbt hx.1 with h | h
    · exact absurd h hx.2
    · exact h)
  haveI := hTfin.fintype
  let e := (Fintype.equivFin (b \ Set.range u0 : Set V)).symm
  have hT : ∀ j, (e j : V) ∈ b ∧ (e j : V) ∉ Set.range u0 := fun j => (e j).2
  have hfrom : ∀ j, ∃ i, (e j : V) = w i := by
    intro j
    rcases hbt (hT j).1 with h | h
    · exact absurd h (hT j).2
    · obtain ⟨i, hi⟩ := h
      exact ⟨i, hi.symm⟩
  refine ⟨Fintype.card (b \ Set.range u0 : Set V), fun j => (e j : V), hfrom, ?_⟩
  unfold IsFrame
  have hmemb : ∀ x, Fin.append u0 (fun j => (e j : V)) x ∈ b := by
    intro x
    induction x using Fin.addCases with
    | left i => rw [Fin.append_left]; exact hsb ⟨i, rfl⟩
    | right j => rw [Fin.append_right]; exact (hT j).1
  have hinj : Function.Injective (Fin.append u0 (fun j => (e j : V))) := by
    intro x y hxy
    induction x using Fin.addCases with
    | left i =>
      induction y using Fin.addCases with
      | left i' =>
        rw [Fin.append_left, Fin.append_left] at hxy
        rw [hu0.injective hxy]
      | right j' =>
        rw [Fin.append_left, Fin.append_right] at hxy
        exact absurd ⟨i, hxy⟩ (hT j').2
    | right j =>
      induction y using Fin.addCases with
      | left i' =>
        rw [Fin.append_right, Fin.append_left] at hxy
        exact absurd ⟨i', hxy.symm⟩ (hT j).2
      | right j' =>
        rw [Fin.append_right, Fin.append_right] at hxy
        rw [e.injective (Subtype.ext hxy)]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    induction x using Fin.addCases with
    | left i => rw [Fin.append_left]; exact hu0E i
    | right j =>
      rw [Fin.append_right]
      obtain ⟨i, hi⟩ := hfrom j
      rw [hi]
      exact hwE i
  · exact hb.comp (fun x => (⟨Fin.append u0 (fun j => (e j : V)) x, hmemb x⟩ : b))
      (fun x y h => hinj (congrArg Subtype.val h))
  · have hbr : b ⊆ Set.range (Fin.append u0 (fun j => (e j : V))) := by
      intro y hy
      by_cases hyu : y ∈ Set.range u0
      · obtain ⟨i, rfl⟩ := hyu
        exact ⟨Fin.castAdd _ i, Fin.append_left _ _ _⟩
      · refine ⟨Fin.natAdd _ (e.symm ⟨y, hy, hyu⟩), ?_⟩
        rw [Fin.append_right]
        simp
    intro x hx
    have h1 : x ∈ Submodule.span K (Set.range w) := hwspan hx
    have h2 : Submodule.span K (Set.range w) ≤ Submodule.span K b :=
      Submodule.span_le.2 fun y hy => hspan (Set.mem_union_right _ hy)
    exact Submodule.span_mono hbr (h2 h1)

theorem relIndex_le_of_append {E' : Submodule (𝓞 K) V'} {E : Submodule (𝓞 K) V} (hE : E.FG)
    (α : V' →ₗ[K] V) (hαE : ∀ x ∈ E', α x ∈ E) {a m : ℕ} (v : Fin a → V') (hv : IsFrame K E' v)
    (w' : Fin m → V) (hu : IsFrame K E (Fin.append (fun i => α (v i)) w')) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E'.toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range (Fin.append (fun i => α (v i)) w'))).toAddSubgroup.relIndex
        E.toAddSubgroup := by
  classical
  have hA : ∀ x ∈ E', α x ∈ Submodule.span (𝓞 K) (Set.range (Fin.append (fun i => α (v i)) w')) →
      x ∈ Submodule.span (𝓞 K) (Set.range v) := by
    intro x hxE hxS
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hv.2.2 hxE)
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hxS
    have hli := Fintype.linearIndependent_iff.mp hu.2.1
    have key : ∀ k, algebraMap (𝓞 K) K (d k) = Fin.append c (fun _ : Fin m => (0 : K)) k := by
      intro k
      refine sub_eq_zero.mp (hli (fun k => algebraMap (𝓞 K) K (d k) -
        Fin.append c (fun _ : Fin m => (0 : K)) k) ?_ k)
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have h1 : ∑ k, algebraMap (𝓞 K) K (d k) • Fin.append (fun i => α (v i)) w' k = α x := by
        rw [← hd]
        exact Finset.sum_congr rfl fun k _ => algebraMap_smul K (d k) _
      rw [h1, ← hc, map_sum, Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right, map_smul]
    rw [← hc]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi := key (Fin.castAdd m i)
    rw [Fin.append_left] at hi
    rw [← hi, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hB : ∀ x ∈ Submodule.span (𝓞 K) (Set.range v),
      α x ∈ Submodule.span (𝓞 K) (Set.range (Fin.append (fun i => α (v i)) w')) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨Fin.castAdd m i, by simp⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [← algebraMap_smul K r y, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ r hy
  have hfin := IsFrame.relIndex_ne_zero hE hu
  have hmap : E'.toAddSubgroup.map α.toAddMonoidHom ≤ E.toAddSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    exact hαE x hx
  have hS'E : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup ⊓ E'.toAddSubgroup =
      ((Submodule.span (𝓞 K) (Set.range (Fin.append (fun i => α (v i)) w'))).toAddSubgroup.comap
        α.toAddMonoidHom) ⊓ E'.toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup,
      LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hB x h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hA x h2 h1, h2⟩
  calc (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E'.toAddSubgroup
      = ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup ⊓ E'.toAddSubgroup).relIndex
          E'.toAddSubgroup := (AddSubgroup.inf_relIndex_right _ _).symm
    _ = (((Submodule.span (𝓞 K) (Set.range (Fin.append (fun i => α (v i)) w'))).toAddSubgroup.comap
          α.toAddMonoidHom) ⊓ E'.toAddSubgroup).relIndex E'.toAddSubgroup := by rw [hS'E]
    _ = ((Submodule.span (𝓞 K) (Set.range (Fin.append (fun i => α (v i)) w'))).toAddSubgroup.comap
          α.toAddMonoidHom).relIndex E'.toAddSubgroup := AddSubgroup.inf_relIndex_right _ _
    _ = (Submodule.span (𝓞 K) (Set.range (Fin.append (fun i => α (v i)) w'))).toAddSubgroup.relIndex
          (E'.toAddSubgroup.map α.toAddMonoidHom) := AddSubgroup.relIndex_comap _ _ _
    _ ≤ _ := AddSubgroup.relIndex_le_of_le_right hmap hfin

theorem re_le_sq_of_sqrt_le {x l : ℝ} (h : Real.sqrt x ≤ l) : x ≤ l ^ 2 := by
  rcases le_or_gt 0 x with hx | hx
  · have h0 := Real.sqrt_nonneg x
    calc x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx).symm
      _ ≤ l ^ 2 := by gcongr
  · nlinarith [sq_nonneg l]

theorem log_det_append_le (h' : HermFam K V') (h : HermFam K V) (α : V' →ₗ[K] V)
    (hα : Function.Injective α) (σ : K →+* ℂ) (A l : ℝ) (hA : 0 < A) (hl : 0 < l) {a m : ℕ}
    (v : Fin a → V') (hv : LinearIndependent K v) (w' : Fin m → V)
    (hu : LinearIndependent K (Fin.append (fun i => α (v i)) w'))
    (hnorm : (((A : ℂ) ^ 2) • h'.gram σ v - h.gram σ (fun i => α (v i))).PosSemidef)
    (hwl : ∀ j, h.nrm σ (w' j) ≤ l) :
    Real.log (h.gram σ (Fin.append (fun i => α (v i)) w')).det.re ≤
      2 * a * Real.log A + Real.log (h'.gram σ v).det.re + 2 * m * Real.log l := by
  set u := Fin.append (fun i => α (v i)) w' with hu_def
  have hαv : LinearIndependent K (fun i => α (v i)) := hv.map' α (LinearMap.ker_eq_bot.mpr hα)
  have hGu : (h.gram σ u).PosDef := h.posDef σ _ u hu
  have hGav : (h.gram σ (fun i => α (v i))).PosDef := h.posDef σ _ _ hαv
  have hGv : (h'.gram σ v).PosDef := h'.posDef σ _ v hv
  have h1 := det_re_le_mul_prod_diag (a := a) (b := m) hGu
  have hsub : (h.gram σ u).submatrix (Fin.castAdd m) (Fin.castAdd m) =
      h.gram σ (fun i => α (v i)) := by
    ext i j; simp [HermFam.gram, u]
  rw [hsub] at h1
  have hdiag : ∀ j, ((h.gram σ u) (Fin.natAdd a j) (Fin.natAdd a j)).re ≤ l ^ 2 := fun j => by
    have := hwl j
    unfold HermFam.nrm at this
    simp only [HermFam.gram, Matrix.of_apply, u, Fin.append_right]
    exact re_le_sq_of_sqrt_le this
  have hdpos : ∀ j, 0 < ((h.gram σ u) (Fin.natAdd a j) (Fin.natAdd a j)).re := fun j =>
    (Complex.pos_iff.mp hGu.diag_pos).1
  have h2 : ∏ j, ((h.gram σ u) (Fin.natAdd a j) (Fin.natAdd a j)).re ≤ (l ^ 2) ^ m := by
    calc _ ≤ ∏ _j : Fin m, l ^ 2 :=
          Finset.prod_le_prod (fun j _ => (hdpos j).le) (fun j _ => hdiag j)
      _ = _ := by simp
  have h3 := det_re_le_of_sub_posSemidef hGav hnorm
  rw [Matrix.det_smul, Fintype.card_fin,
    show ((A : ℂ) ^ 2) ^ a = (((A ^ 2) ^ a : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul] at h3
  have hdu := (posDef_det_re_pos hGu).1
  have hdv := (posDef_det_re_pos hGv).1
  have hprodpos : 0 ≤ ∏ j, ((h.gram σ u) (Fin.natAdd a j) (Fin.natAdd a j)).re :=
    Finset.prod_nonneg fun j _ => (hdpos j).le
  have key : (h.gram σ u).det.re ≤ (A ^ 2) ^ a * (h'.gram σ v).det.re * (l ^ 2) ^ m :=
    h1.trans (mul_le_mul h3 h2 hprodpos (by positivity))
  have := Real.log_le_log hdu key
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    at this
  simp only [Real.log_pow] at this
  push_cast at this
  linarith

theorem deg_bot (h : HermFam K V) : deg h (⊥ : Submodule (𝓞 K) V) = 0 := by
  have key : ∀ {r : ℕ} (v : Fin r → V), IsFrame K (⊥ : Submodule (𝓞 K) V) v → degreeOfFamily h ⊥ v = 0 := by
    intro r v hv
    obtain ⟨hmem, hli, -⟩ := hv
    have hr : r = 0 := by
      by_contra hr
      exact hli.ne_zero ⟨0, Nat.pos_of_ne_zero hr⟩ ((Submodule.mem_bot _).1 (hmem _))
    subst hr
    unfold degreeOfFamily
    have h1 : Submodule.span (𝓞 K) (Set.range v) = ⊥ := by simp [Set.range_eq_empty]
    rw [h1]
    simp [HermFam.gram]
  unfold deg
  split_ifs with hE
  · exact key _ hE.choose_spec
  · rfl

theorem latRank_bot : latRank K (⊥ : Submodule (𝓞 K) V) = 0 := by
  unfold latRank
  simp

end ReciprocityTheory.GeometryOfNumbersTheory.HadamardFrameExtension
