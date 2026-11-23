import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.MirPatch.Decomp

open GlobalTheory.JSW GlobalTheory.SmGL Topology

theorem exists_distinct {ι X : Type} [Finite ι] (C : ι → Set X)
    (hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j) :
    ∃ (N : ℕ) (f : Fin N → ι), (∀ i j x, x ∈ C (f i) → x ∈ C (f j) → i = j) ∧
      ∀ x, (∃ i, x ∈ C i) ↔ ∃ j, x ∈ C (f j) := by
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Set.range C)
  have hf : ∀ j, C (e.symm j).2.choose = (e.symm j).1 := fun j => (e.symm j).2.choose_spec
  refine ⟨N, fun j => (e.symm j).2.choose, fun i j x hi hj => ?_, fun x => ⟨fun ⟨i, hi⟩ => ?_, fun ⟨j, hj⟩ => ⟨_, hj⟩⟩⟩
  · have h := hC _ _ x hi hj
    rw [hf, hf] at h
    exact e.symm.injective (Subtype.ext h)
  · refine ⟨e ⟨C i, i, rfl⟩, ?_⟩
    simp only
    rw [hf, Equiv.symm_apply_apply]
    exact hi

theorem exists_finite_reps {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K A : Set G} (hK : IsCompact K) (hA : A ⊆ K) (V : Subgroup G) (hV : IsOpen (V : Set G)) :
    ∃ (ι : Type) (_ : Finite ι) (k : ι → G), (∀ i, k i ∈ A) ∧ ∀ a ∈ A, ∃ i, (k i)⁻¹ * a ∈ V := by
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hK (V := (V : Set G))
    (by rw [hV.interior_eq]; exact ⟨1, V.one_mem⟩)
  let ι := {g : G // g ∈ t ∧ ∃ a ∈ A, g * a ∈ V}
  haveI : Finite ι := Finite.of_injective (fun x : ι => (⟨x.1, x.2.1⟩ : t))
    (fun x y h => Subtype.ext (congrArg (fun z : t => (z : G)) h))
  refine ⟨ι, inferInstance, fun x => x.2.2.choose, fun x => x.2.2.choose_spec.1, fun a ha => ?_⟩
  obtain ⟨g, hg, hga⟩ := Set.mem_iUnion₂.1 (ht (hA ha))
  have hga' : g * a ∈ V := hga
  refine ⟨⟨g, hg, a, ha, hga'⟩, ?_⟩
  have hb := (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose_spec.2
  have e : ((⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * a =
      (g * (⟨g, hg, a, ha, hga'⟩ : ι).2.2.choose)⁻¹ * (g * a) := by group
  rw [e]
  exact mul_mem (inv_mem hb) hga'

theorem cell_eq_of_mem {F : Type} [NormedField F] {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (h : g ∈ Cut.cell z (U : Set (GL (Fin n) F))) :
    Cut.cell z (U : Set (GL (Fin n) F)) = Cut.cell g (U : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u⁻¹, mul_mem hu' (inv_mem hu), k⁻¹ * k', mul_mem (inv_mem hk) hk', by group⟩
  · rintro ⟨u', hu', k', hk', rfl⟩
    exact ⟨u' * u, mul_mem hu' hu, k * k', mul_mem hk hk', by group⟩

variable {E : Type} [Field E] [NumberField E]

theorem map_comp_eq {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GA E a) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := rfl

theorem af_eq {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y := FiniteAdeleRing.ext _ h

open Classical in

theorem pLoc_list_prod {n : ℕ} (u : ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin n) (w.adicCompletion E))
    (l : List (HeightOneSpectrum (𝓞 E))) (hl : l.Nodup) (v : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (pLoc E v) (l.map fun w => locGL E n w (u w)).prod = if v ∈ l then u v else 1 := by
  classical
  induction l with
  | nil => simp
  | cons w l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih (List.nodup_cons.1 hl).2]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, if_neg (List.nodup_cons.1 hl).1, if_pos (by simp), mul_one]
    · rw [pLoc_locGL_of_ne h, one_mul]
      simp only [List.mem_cons, h, false_or]

theorem loc_mem_unipB {a : ℕ} {u : GA E a} (hu : u ∈ NA E a) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) u ∈ unipB (w.adicCompletion E) (Fin a) :=
  (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j h => by
    show pLoc E w (pFin E _) = 0
    rw [hu.1 i j h, map_zero, map_zero], fun i => by
    show pLoc E w (pFin E _) = 1
    rw [hu.2 i, map_one, map_one]⟩

variable [IsTotallyComplex E]

theorem finGL_mem_NA {a : ℕ} {v : GL (Fin a) (Af E)}
    (hv : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a)) : finGL E a v ∈ NA E a := by
  have e1 : ∀ i j, pInf E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) =
      ((1 : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j := fun i j =>
    congrArg (fun g : GL (Fin a) (Cinf E) => (g : Matrix (Fin a) (Fin a) (Cinf E)) i j) (pInf_finGL (E := E) v)
  have e2 : ∀ i j, pFin E ((finGL E a v : Matrix (Fin a) (Fin a) (Ad E)) i j) = (v : Matrix (Fin a) (Fin a) (Af E)) i j :=
    fun i j => congrArg (fun g : GL (Fin a) (Af E) => (g : Matrix (Fin a) (Fin a) (Af E)) i j) (pFin_finGL (E := E) v)
  refine ⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
  · rw [e1, Units.val_one, Matrix.one_apply_ne (ne_of_gt h), map_zero]
  · rw [e2, map_zero]
    exact af_eq fun w => by rw [map_zero]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).1 i j h
  · rw [e1, Units.val_one, Matrix.one_apply_eq, map_one]
  · rw [e2, map_one]
    exact af_eq fun w => by rw [map_one]; exact ((GlobalTheory.SmGL.mem_unipB _).1 (hv w)).2 i

theorem mem_cell_iff {a : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a)
    {p : GA E a} (hp : p ∈ supS E a S) :
    p ∈ cell K q ↔ ∃ k ∈ K,
      (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) ∈
        unipB (w.adicCompletion E) (Fin a)) ∧
      ∀ w ∈ S, ∃ u ∈ unipB (w.adicCompletion E) (Fin a), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p =
        u * GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) q * k) := by
  constructor
  · rintro ⟨u, hu, k, hk, y, rfl⟩
    have hf : GeneralLinearGroup.map (pFin E) (u * q * finGL E a k * infGL E a y) =
        GeneralLinearGroup.map (pFin E) u * (GeneralLinearGroup.map (pFin E) q * k) := by
      rw [map_mul, map_mul, map_mul, pFin_finGL, pFin_infGL, mul_one, mul_assoc]
    refine ⟨k, hk, fun w hw => ?_, fun w _ => ⟨_, loc_mem_unipB hu w, ?_⟩⟩
    · have h1 := hp w hw
      rw [map_comp_eq, hf, map_mul] at h1
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem (loc_mem_unipB hu w)
    · rw [map_comp_eq, hf, map_mul, map_comp_eq]
  · rintro ⟨k, hk, hout, hin⟩
    set v := GeneralLinearGroup.map (pFin E) p * (GeneralLinearGroup.map (pFin E) q * k)⁻¹ with hv
    have hvN : ∀ w, GeneralLinearGroup.map (pLoc E w) v ∈ unipB (w.adicCompletion E) (Fin a) := by
      intro w
      rw [hv, map_mul, map_inv]
      by_cases hw : w ∈ S
      · obtain ⟨u, hu, he⟩ := hin w hw
        rw [← map_comp_eq, he, mul_inv_cancel_right]
        exact hu
      · rw [← map_comp_eq, hp w hw, one_mul]
        exact inv_mem (hout w hw)
    refine ⟨finGL E a v, finGL_mem_NA hvN, k, hk,
      (GeneralLinearGroup.map (pInf E) q)⁻¹ * GeneralLinearGroup.map (pInf E) p, ga_ext ?_ ?_⟩
    · simp only [map_mul, pInf_finGL, pInf_infGL, one_mul, mul_one, mul_inv_cancel_left]
    · simp only [map_mul, pFin_finGL, pFin_infGL, mul_one, hv]
      group

end GlobalTheory.JSW.MirPatch.Decomp

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.JSW GlobalTheory.SmGL Decomp

theorem cell_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (K : Subgroup (GL (Fin (m + 1)) (Af E))), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) → IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) → ∀ q : GA E (m + 1), ∃ (U : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))) (N : ℕ) (z : Fin N → ∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)), (∀ w ∈ S, IsCompact (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ IsOpen (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) ∧ ∀ u ∈ U w, locGL E (m + 1) w u ∈ K) ∧ (∀ p ∈ GlobalTheory.JSW.mirS E S m, ∀ i j : Fin N, (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z j w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) → i = j) ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, (p ∈ GlobalTheory.JSW.MirPatch.cell K q ↔ ∃ i : Fin N, ∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p ∈ GlobalTheory.JSW.Cut.cell (z i w) (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))) := by
  intro E _ _ _ m S K hKo hKc q
  classical
  choose U hUo hUc hUK using fun w => LocEx.exists_compact_open (a := m + 1) w K hKo
  set qf := GeneralLinearGroup.map (pFin E) q with hqf
  let A : Set (GL (Fin (m + 1)) (Af E)) := {k | k ∈ K ∧ ∀ w ∉ S,
    GeneralLinearGroup.map (pLoc E w) (qf * k) ∈ unipB (w.adicCompletion E) (Fin (m + 1))}
  let V : Subgroup (GL (Fin (m + 1)) (Af E)) :=
    { carrier := {v | ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) v ∈ U w}
      mul_mem' := fun ha hb w hw => by rw [map_mul]; exact mul_mem (ha w hw) (hb w hw)
      one_mem' := fun w _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun ha w hw => by rw [map_inv]; exact inv_mem (ha w hw) }
  have hVo : IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) := by
    have e : (V : Set (GL (Fin (m + 1)) (Af E))) =
        ⋂ w ∈ S, GeneralLinearGroup.map (pLoc E w) ⁻¹' (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E))) := by
      ext v; simp [V]
    rw [e]
    exact isOpen_biInter_finset fun w _ => (hUo w).preimage (LocEx.continuous_map_pLoc w)
  obtain ⟨ι, _, k, hkA, hcov⟩ := exists_finite_reps (A := A) hKc (fun x hx => hx.1) V hVo
  let C : ι → Set (∀ w : HeightOneSpectrum (𝓞 E), GL (Fin (m + 1)) (w.adicCompletion E)) := fun i =>
    {x | ∀ w ∈ S, x w ∈ Cut.cell (GeneralLinearGroup.map (pLoc E w) (qf * k i))
      (U w : Set (GL (Fin (m + 1)) (w.adicCompletion E)))}
  have hC : ∀ i j x, x ∈ C i → x ∈ C j → C i = C j := by
    intro i j x hi hj
    ext y
    exact forall₂_congr fun w hw => by rw [cell_eq_of_mem (hi w hw), cell_eq_of_mem (hj w hw)]
  obtain ⟨N, f, huniq, hiff⟩ := exists_distinct C hC
  refine ⟨U, N, fun j w => GeneralLinearGroup.map (pLoc E w) (qf * k (f j)), fun w _ => ⟨hUc w, hUo w, hUK w⟩,
    fun p _ i j hi hj => huniq i j (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p) hi hj,
    fun p hp => ?_⟩
  rw [mem_cell_iff S K q hp.1]
  refine Iff.trans ?_ (hiff (fun w => GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p))
  constructor
  · rintro ⟨k', hk', hout, hin⟩
    obtain ⟨i, hi⟩ := hcov k' ⟨hk', hout⟩
    refine ⟨i, fun w hw => ?_⟩
    obtain ⟨u, hu, he⟩ := hin w hw
    refine ⟨u, hu, GeneralLinearGroup.map (pLoc E w) ((k i)⁻¹ * k'), hi w hw, ?_⟩
    show GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = _
    rw [he, mul_assoc u, ← map_mul, mul_assoc, mul_inv_cancel_left]
  · rintro ⟨i, hi⟩
    choose! uu huu cc hcc heq using hi
    let g : GL (Fin (m + 1)) (Af E) := (S.toList.map fun w => locGL E (m + 1) w (cc w)).prod
    have hgK : g ∈ K := by
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      exact hUK w _ (hcc w (Finset.mem_toList.1 hw))
    have hg : ∀ v, GeneralLinearGroup.map (pLoc E v) g = if v ∈ S then cc v else 1 := fun v => by
      rw [pLoc_list_prod cc _ S.nodup_toList v]
      simp only [Finset.mem_toList]
    refine ⟨k i * g, mul_mem (hkA i).1 hgK, fun w hw => ?_, fun w hw => ⟨uu w, huu w hw, ?_⟩⟩
    · rw [← mul_assoc, map_mul, hg w, if_neg hw, mul_one]
      exact (hkA i).2 w hw
    · refine (heq w hw).trans ?_
      rw [← mul_assoc qf, map_mul (GeneralLinearGroup.map (pLoc E w)) (qf * k i) g, hg w, if_pos hw, mul_assoc]

end GlobalTheory.JSW.MirPatch
