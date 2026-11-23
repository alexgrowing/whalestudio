import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem mem_unipOn' [IsArtinianRing E] {n : ℕ} {A B : Submodule E (Fin n → E)} (hBA : B ≤ A)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (h1 : ∀ v ∈ A, g v - v ∈ B) : g ∈ unipOn A B := by
  have h2 : ∀ v ∈ A, g v ∈ A := fun v hv => by simpa using A.add_mem (hBA (h1 _ hv)) hv
  refine ⟨fun v => ⟨fun hv => ?_, h2 v⟩, h1⟩
  have hs := IsArtinian.surjective_of_injective_endomorphism (g.toLinearMap.restrict h2)
    (fun a b hab => Subtype.ext (g.injective (congrArg Subtype.val hab)))
  obtain ⟨a, ha⟩ := hs ⟨g v, hv⟩
  have : (a : Fin n → E) = v := g.injective (congrArg Subtype.val ha)
  exact this ▸ a.2

theorem hf_sum (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι κ : Type} [Fintype ι]
    [Fintype κ] (a : ι → E) (b : κ → E) (x : ι → Fin n → E) (y : κ → Fin n → E) :
    hf L Hm (∑ i, a i • x i) (∑ j, b j • y j) = ∑ i, ∑ j, a i * L.cj (b j) * hf L Hm (x i) (y j) := by
  have h1 : ∀ (s : Finset ι) (z : Fin n → E),
      hf L Hm (∑ i ∈ s, a i • x i) z = ∑ i ∈ s, a i * hf L Hm (x i) z := by
    intro s z
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, hf_smul_l, ih]
  have h2 : ∀ (s : Finset κ) (z : Fin n → E),
      hf L Hm z (∑ i ∈ s, b i • y i) = ∑ i ∈ s, L.cj (b i) * hf L Hm z (y i) := by
    intro s z
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, hf_smul_r, ih]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

theorem hf_sum_l (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} [Fintype ι]
    (a : ι → E) (x : ι → Fin n → E) (z : Fin n → E) :
    hf L Hm (∑ i, a i • x i) z = ∑ i, a i * hf L Hm (x i) z := by
  have := hf_sum L Hm a (fun _ : Unit => (1 : E)) x (fun _ => z)
  simpa using this

theorem isom_span (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (φ : (Fin n → E) →ₗ[E] (Fin n → E)) (G : Set (Fin n → E))
    (h : ∀ x ∈ G, ∀ y ∈ G, hf L Hm (φ x) (φ y) = hf L Hm x y) :
    ∀ x ∈ Submodule.span E G, ∀ y ∈ Submodule.span E G, hf L Hm (φ x) (φ y) = hf L Hm x y := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp [hf]
    | add a b _ _ ha hb => rw [map_add, hf_add_r, hf_add_r, ha, hb]
    | smul c a _ ha => rw [map_smul, hf_smul_r, hf_smul_r, ha]
  | zero => simp [hf]
  | add a b _ _ ha hb => rw [map_add, hf_add_l, hf_add_l, ha, hb]
  | smul c a _ ha => rw [map_smul, hf_smul_l, hf_smul_l, ha]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_top (g : Fin (r + 1) → S.V) : S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    ext i; simpa using i.2
  simp only [Frames.spanTo, hs, Set.image_univ]

theorem pair_eq (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    hf L S.Hm (∑ i, s' i b • S.f' i) (∑ i, s i a • S.f i) = (cT L s * S.Zh * s') a b := by
  rw [hf_sum]
  simp only [Matrix.mul_apply, Finset.sum_mul, cT, Frames.Zh, Frames.h, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gram_eq (g : Fin (r + 1) → S.V) (T : Fˣ)
    (gram : ∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (a b : Fin (r + 1)) :
    hf L S.Hm (∑ i, s i a • g i) (∑ i, s i b • g i) = hf L S.Hm (g a) (g b) := by
  have hl : ∀ a, s (Fin.last r) a = if a = Fin.last r then 1 else 0 := by
    intro a
    split_ifs with h
    · rw [h, hs.2]
    · exact hs.1 _ _ (lt_of_le_of_ne (Fin.le_last a) h)
  rw [hf_sum, Finset.sum_eq_single (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · rw [hl, hl, gram, gram]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb]
  · intro j _ hj; simp [gram, hj]
  · simp
  · intro j _ hj; simp [gram, hj]
  · simp

theorem step_mem (g : Fin (r + 1) → S.V)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (h : S.GLV) (hg : ∀ j, h (g j) = ∑ i, s i j • g i) (l : ℕ) :
    ∀ v ∈ S.spanTo g (l + 1), h v - v ∈ S.spanTo g l := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : (j : ℕ) < l + 1 := hj
    rw [hg, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), hs.2, one_smul, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun i hi => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · have h' : (i : ℕ) < j := h
      exact Submodule.smul_mem _ _ (mem_spanTo S g (by omega))
    · rw [hs.1 i j h]; simp
  | zero => simp
  | add x y _ _ hx hy =>
    have : h (x + y) - (x + y) = (h x - x) + (h y - y) := by rw [map_add]; abel
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hx

theorem mem_Nof [IsArtinianRing E] (g g' : Fin (r + 1) → S.V) (T : Fˣ)
    (gram : ∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
    (W : Submodule E S.V) (hW : ∀ w ∈ W, ∀ y ∈ S.spanTo g (r + 1), hf L S.Hm w y = 0)
    (htop : (S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) ⊔ W = ⊤)
    (hnd : ∀ u ∈ S.spanTo g' (r + 1), (∀ y ∈ S.spanTo g (r + 1), hf L S.Hm u y = 0) → u = 0)
    (s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hs : (∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1))
    (hs' : (∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1))
    (h : S.GLV) (hi : h ∈ isomG L S.Hm) (hg : ∀ j, h (g j) = ∑ i, s i j • g i)
    (hg' : ∀ j, h (g' j) = ∑ i, s' i j • g' i) (hw : ∀ w ∈ W, h w = w) : h ∈ S.Nof g := by
  have hu : ∀ l, h ∈ unipOn (S.spanTo g (l + 1)) (S.spanTo g l) := fun l =>
    mem_unipOn' (spanTo_mono S g (Nat.le_succ _)) h (step_mem S g s hs h hg l)
  refine ⟨⟨hi, Subgroup.mem_iInf.2 fun l => hu l⟩, mem_unipOn' (spanTo_le_perp S g T gram) h ?_⟩
  intro v hv
  have hv' : v ∈ (S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) ⊔ W := htop ▸ Submodule.mem_top
  obtain ⟨m, hm, w, hw', rfl⟩ := Submodule.mem_sup.1 hv'
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hm
  have hxp : x ∈ perp L S.Hm (S.spanTo g r) := by
    have : S.spanTo g (r + 1) ≤ perp L S.Hm (S.spanTo g r) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, -, rfl⟩
      exact mem_perp S g T gram i
    exact this hx
  have hwp : w ∈ perp L S.Hm (S.spanTo g r) := fun z hz => hW w hw' z (spanTo_mono S g (Nat.le_succ _) hz)
  have hyp : y ∈ perp L S.Hm (S.spanTo g r) := by
    have := sub_mem (sub_mem hv hwp) hxp
    simpa using this
  have hy0 : h y - y = 0 := by
    refine hnd _ (spanTo_mono S g' (Nat.le_succ _) (step_mem S g' s' hs' h hg' r y hy)) fun z hz => ?_
    have hz1 : h.symm z ∈ S.spanTo g (r + 1) := ((hu r).1 _).1 (by simpa using hz)
    have hz2 := hyp _ ((hu r).2 _ hz1)
    have hz3 := hi y (h.symm z)
    rw [LinearEquiv.apply_symm_apply] at hz2 hz3
    rw [hf_sub_r] at hz2
    rw [hf_sub_l, hz3]
    linear_combination -hz2
  have : h (x + y + w) - (x + y + w) = h x - x := by
    rw [map_add, map_add, hw w hw', sub_eq_zero.1 hy0]; abel
  rw [this]
  exact (hu r).2 x hx

end

theorem stab_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ h ∈ S.St, ∀ w ∈ S.W0, h w = w) ∧ ∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) → (cT L s * S.Zh * s' = S.Zh ↔ ∃ h ∈ S.St, (∀ j, h (S.f j) = ∑ i, s i j • S.f i) ∧ ∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hli, hco, -, hU, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hU' : IsUnit S.Zh.det := hU
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    rw [Frames.ME, spanTo_top, spanTo_top, Set.Sum.elim_range, Submodule.span_union]
  refine ⟨fun h hh w hw => ?_, fun s s' hs hs' => ⟨fun hz => ?_, ?_⟩⟩
  · have hd := (linearIndependent_sum.1 hli).2.2
    have h1 : h w - w ∈ S.spanTo S.f r := hh.1.2.2 w fun y hy =>
      hw y (Submodule.mem_sup_left (spanTo_mono S _ (Nat.le_succ _) hy))
    have h2 : h w - w ∈ S.spanTo S.f' r := hh.2.2.2 w fun y hy =>
      hw y (Submodule.mem_sup_right (spanTo_mono S _ (Nat.le_succ _) hy))
    have h3 := spanTo_mono S _ (Nat.le_succ _) h1
    have h4 := spanTo_mono S _ (Nat.le_succ _) h2
    rw [spanTo_top] at h3 h4
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h3 h4)
  · have hco' := hco
    rw [hME] at hco'
    let t : Fin (r + 1) ⊕ Fin (r + 1) → S.V :=
      Sum.elim (fun j => ∑ i, s i j • S.f i) (fun j => ∑ i, s' i j • S.f' i)
    let φ : S.V →ₗ[E] S.V :=
      LinearMap.ofIsCompl hco' ((Module.Basis.span hli).constr E t) S.W0.subtype
    have hφ1 : ∀ i, φ (Sum.elim S.f S.f' i) = t i := by
      intro i
      have h1 := LinearMap.ofIsCompl_apply_left hco' (φ := (Module.Basis.span hli).constr E t)
        (ψ := S.W0.subtype) (Module.Basis.span hli i)
      rw [Module.Basis.constr_basis, Module.Basis.span_apply] at h1
      exact h1
    have hφ2 : ∀ w ∈ S.W0, φ w = w := fun w hw =>
      LinearMap.ofIsCompl_apply_right hco' (φ := (Module.Basis.span hli).constr E t)
        (ψ := S.W0.subtype) ⟨w, hw⟩
    have hmem : ∀ i, Sum.elim S.f S.f' i ∈ S.ME := fun i => hME ▸ Submodule.subset_span ⟨i, rfl⟩
    have htm : ∀ i, t i ∈ S.ME := by
      rintro (j | j)
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem (Sum.inl i))
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem (Sum.inr i))
    have hmix : ∀ a b, hf L S.Hm (t (Sum.inr b)) (t (Sum.inl a)) = hf L S.Hm (S.f' b) (S.f a) := by
      intro a b
      have := pair_eq S s s' a b
      rw [hz] at this
      exact this
    have hiso : ∀ x y, hf L S.Hm (φ x) (φ y) = hf L S.Hm x y := by
      have h1 := isom_span L S.Hm φ (Set.range (Sum.elim S.f S.f') ∪ S.W0) (by
        rintro _ (⟨i, rfl⟩ | hx) _ (⟨j, rfl⟩ | hy)
        · rw [hφ1, hφ1]
          rcases i with i | i <;> rcases j with j | j
          · exact gram_eq S S.f S.T S.gram s hs i j
          · rw [← hf_cj L S.herm.1, hmix, hf_cj L S.herm.1]; rfl
          · exact hmix j i
          · exact gram_eq S S.f' S.T' S.gram' s' hs' i j
        · rw [hφ1, hφ2 _ hy, ← hf_cj L S.herm.1, hy _ (htm i), ← hf_cj L S.herm.1 _ (Sum.elim _ _ _),
            hy _ (hmem i)]
        · rw [hφ1, hφ2 _ hx, hx _ (htm j), hx _ (hmem j)]
        · rw [hφ2 _ hx, hφ2 _ hy])
      rw [Submodule.span_union, Submodule.span_eq, hco'.sup_eq_top] at h1
      exact fun x y => h1 x trivial y trivial
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      apply Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 S.herm.2)
      funext j
      have h1 := hiso v (Pi.single j 1)
      rw [hv] at h1
      simpa [hf, Pi.single_apply, Matrix.vecMul, dotProduct, apply_ite L.cj] using h1.symm
    let h : S.GLV := LinearEquiv.ofBijective φ (IsArtinian.bijective_of_injective_endomorphism φ hinj)
    have hg : ∀ j, h (S.f j) = ∑ i, s i j • S.f i := fun j => hφ1 (Sum.inl j)
    have hg' : ∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i := fun j => hφ1 (Sum.inr j)
    refine ⟨h, ⟨?_, ?_⟩, hg, hg'⟩
    · refine mem_Nof S S.f S.f' S.T S.gram S.W0 (fun w hw y hy => hw y (Submodule.mem_sup_left hy))
        hco.sup_eq_top ?_ s s' hs hs' h hiso hg hg' hφ2
      intro u hu h0
      obtain ⟨c, -, rfl⟩ := coords S _ hu
      have : c = 0 := by
        apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
        funext a
        have h1 := h0 _ (mem_spanTo S S.f a.2)
        rw [hf_sum_l] at h1
        rw [Matrix.mulVec_zero, Pi.zero_apply, ← h1]
        unfold Matrix.mulVec dotProduct
        exact Finset.sum_congr rfl fun b _ => mul_comm _ _
      simp [this]
    · refine mem_Nof S S.f' S.f S.T' S.gram' S.W0 (fun w hw y hy => hw y (Submodule.mem_sup_right hy))
        (by rw [sup_comm (S.spanTo S.f' _)]; exact hco.sup_eq_top) ?_ s' s hs' hs h hiso hg' hg hφ2
      intro u hu h0
      obtain ⟨c, -, rfl⟩ := coords S _ hu
      have : (fun i => L.cj (c i)) = 0 := by
        apply Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
        funext a
        have h1 := congrArg L.cj (h0 _ (mem_spanTo S S.f' a.2))
        rw [hf_sum_l, map_zero, map_sum] at h1
        simp only [map_mul, hf_cj L S.herm.1] at h1
        simp only [Matrix.zero_vecMul, Pi.zero_apply]
        exact h1
      have h2 : ∀ i, c i = 0 := fun i => by simpa using congrFun this i
      simp [h2]
  · rintro ⟨h, hh, h1, h2⟩
    ext a b
    rw [← pair_eq, ← h1, ← h2]
    exact hh.1.1.1 _ _

end GlobalTheory.HL.FrameStab
