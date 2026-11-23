import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSubgroupSubsetNhdsOne
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.MirPatch.Cover

open GlobalTheory.JSW GlobalTheory.JSW.MirPatch Topology

section UT

variable {R R' : Type} [CommRing R] [CommRing R'] {a : ℕ}

def IsUT (M : Matrix (Fin a) (Fin a) R) : Prop :=
  (∀ i j : Fin a, j < i → M i j = 0) ∧ ∀ i, M i i = 1

theorem isUT_one : IsUT (1 : Matrix (Fin a) (Fin a) R) :=
  ⟨fun i j h => Matrix.one_apply_ne (ne_of_gt h), fun i => Matrix.one_apply_eq i⟩

theorem IsUT.mul {M N : Matrix (Fin a) (Fin a) R} (hM : IsUT M) (hN : IsUT N) : IsUT (M * N) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hM.1 i k h, zero_mul]
    · rw [hN.1 k j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM.2, hN.2, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hM.1 i k h, zero_mul]
      · rw [hN.1 k i h, mul_zero]
    · simp

theorem IsUT.map {M : Matrix (Fin a) (Fin a) R} (hM : IsUT M) (f : R →+* R') : IsUT (M.map f) :=
  ⟨fun i j h => by rw [Matrix.map_apply, hM.1 i j h, map_zero], fun i => by rw [Matrix.map_apply, hM.2 i, map_one]⟩

theorem IsUT.inv {g : GL (Fin a) R} (hg : IsUT (g : Matrix (Fin a) (Fin a) R)) :
    IsUT ((g⁻¹ : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) := by
  letI := g.invertible
  have ht : ((g⁻¹ : GL (Fin a) R) : Matrix (Fin a) (Fin a) R).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular (b := id) fun i j h => hg.1 i j h
  refine ⟨fun i j h => ht h, fun i => ?_⟩
  have e : ((g⁻¹ : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) * (g : Matrix (Fin a) (Fin a) R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e2 := congrFun (congrFun e i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hg.2 i, mul_one, Matrix.one_apply_eq] at e2
  · exact e2
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [ht h, zero_mul]
    · rw [hg.1 k i h, mul_zero]
  · simp

end UT

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mem_NA_iff_isUT (u : GA E a) : u ∈ NA E a ↔ IsUT (u : Matrix (Fin a) (Fin a) (Ad E)) := Iff.rfl

theorem NA_mul {u v : GA E a} (hu : u ∈ NA E a) (hv : v ∈ NA E a) : u * v ∈ NA E a := by
  rw [mem_NA_iff_isUT, Units.val_mul]; exact IsUT.mul hu hv

theorem NA_inv {u : GA E a} (hu : u ∈ NA E a) : u⁻¹ ∈ NA E a := IsUT.inv hu

theorem last_row_mul {m : ℕ} {u : GA E (m + 1)} (hu : u ∈ NA E (m + 1)) (c : GA E (m + 1)) (j : Fin (m + 1)) :
    ((u * c : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m), hu.2, one_mul]
  · intro k _ hk
    rw [hu.1 _ _ (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul]
  · simp

theorem mem_cell_iff (K : Subgroup (GL (Fin a) (Af E))) (q p : GA E a) :
    p ∈ cell K q ↔ ∃ u ∈ NA E a, GeneralLinearGroup.map (pFin E) (q⁻¹ * u⁻¹ * p) ∈ K := by
  constructor
  · rintro ⟨u, hu, k, hk, y, rfl⟩
    refine ⟨u, hu, ?_⟩
    have : q⁻¹ * u⁻¹ * (u * q * finGL E a k * infGL E a y) = finGL E a k * infGL E a y := by group
    rw [this, map_mul, pFin_finGL, pFin_infGL, mul_one]; exact hk
  · rintro ⟨u, hu, hk⟩
    refine ⟨u, hu, _, hk, GeneralLinearGroup.map (pInf E) (q⁻¹ * u⁻¹ * p), ?_⟩
    rw [mul_assoc (u * q), ← infGL_comm, infGL_mul_finGL]
    group

theorem isOpen_cell {K : Subgroup (GL (Fin a) (Af E))} (hK : IsOpen (K : Set (GL (Fin a) (Af E)))) (q : GA E a) :
    IsOpen (cell K q) := by
  have e : cell K q = ⋃ u ∈ NA E a, (fun p => GeneralLinearGroup.map (pFin E) (q⁻¹ * u⁻¹ * p)) ⁻¹' (K : Set _) := by
    ext p; rw [mem_cell_iff]; simp
  rw [e]
  refine isOpen_biUnion fun u _ => hK.preimage ?_
  exact (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp (continuous_const.mul continuous_id)

theorem cell_mono {K K' : Subgroup (GL (Fin a) (Af E))} (h : K ≤ K') (q : GA E a) : cell K q ⊆ cell K' q := by
  rintro p ⟨u, hu, k, hk, y, rfl⟩
  exact ⟨u, hu, k, h hk, y, rfl⟩

theorem cell_subset_of_mem {K : Subgroup (GL (Fin a) (Af E))} {q x : GA E a} (hx : x ∈ cell K q) :
    cell K x ⊆ cell K q := by
  obtain ⟨u', hu', k', hk', y', rfl⟩ := hx
  rintro p ⟨u, hu, k, hk, y, rfl⟩
  refine ⟨u * u', NA_mul hu hu', k' * k, K.mul_mem hk' hk, y' * y, ?_⟩
  rw [map_mul, map_mul]
  have e := infGL_comm (E := E) y' k
  calc u * (u' * q * finGL E a k' * infGL E a y') * finGL E a k * infGL E a y
      = u * u' * q * finGL E a k' * (infGL E a y' * finGL E a k) * infGL E a y := by group
    _ = _ := by rw [e]; group

theorem mem_cell_symm {K : Subgroup (GL (Fin a) (Af E))} {q x : GA E a} (hx : x ∈ cell K q) : q ∈ cell K x := by
  obtain ⟨u, hu, k, hk, y, rfl⟩ := hx
  refine ⟨u⁻¹, NA_inv hu, k⁻¹, K.inv_mem hk, y⁻¹, ?_⟩
  rw [map_inv, map_inv]
  have e := infGL_comm (E := E) y k⁻¹
  calc q = u⁻¹ * (u * q * finGL E a k * infGL E a y) * (infGL E a y)⁻¹ * (finGL E a k)⁻¹ := by group
    _ = u⁻¹ * (u * q * finGL E a k * infGL E a y) * ((infGL E a y)⁻¹ * (finGL E a k)⁻¹) := by group
    _ = _ := by
      rw [← map_inv, ← map_inv, infGL_comm, map_inv, map_inv]; group

theorem cell_eq_of_mem {K : Subgroup (GL (Fin a) (Af E))} {x x' p : GA E a} (h : p ∈ cell K x)
    (h' : p ∈ cell K x') : cell K x = cell K x' :=
  le_antisymm ((cell_subset_of_mem (mem_cell_symm h)).trans (cell_subset_of_mem h'))
    ((cell_subset_of_mem (mem_cell_symm h')).trans (cell_subset_of_mem h))

theorem NA_mul_mem_cell {K : Subgroup (GL (Fin a) (Af E))} {q c u : GA E a} (hu : u ∈ NA E a) (hc : c ∈ cell K q) :
    u * c ∈ cell K q := by
  obtain ⟨v, hv, k, hk, y, rfl⟩ := hc
  exact ⟨u * v, NA_mul hu hv, k, hk, y, by group⟩

end GlobalTheory.JSW.MirPatch.Cover

namespace GlobalTheory.JSW.MirPatch.Cover

open GlobalTheory.JSW GlobalTheory.JSW.MirPatch Topology

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

variable (E) in

def Zset (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : Set (GA E (m + 1)) :=
  {c | (∀ j, (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧
    ∀ w ∉ S, IsUT ((GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) c : GL (Fin (m + 1)) (w.adicCompletion E)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E))}

theorem isClosed_Zset (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : IsClosed (Zset E S m) := by
  have hent : ∀ i j : Fin (m + 1), Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) i j :=
    fun i j => (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem i j
  have hloc : ∀ (w : HeightOneSpectrum (𝓞 E)) (i j : Fin (m + 1)),
      Continuous fun c : GA E (m + 1) => ((pLoc E w).comp (pFin E)) ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) i j) :=
    fun w i j => ((RestrictedProduct.continuous_eval w).comp continuous_snd).comp (hent i j)
  have e : Zset E S m = (⋂ j, {c : GA E (m + 1) | (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
        if j = Fin.last m then 1 else 0}) ∩
      ⋂ w, ⋂ (_ : w ∉ S), ((⋂ i, ⋂ j, ⋂ (_ : j < i), {c : GA E (m + 1) |
        ((pLoc E w).comp (pFin E)) ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) i j) = 0}) ∩
        ⋂ i, {c : GA E (m + 1) | ((pLoc E w).comp (pFin E)) ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) i i) = 1}) := by
    ext c
    simp only [Zset, IsUT, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rfl
  rw [e]
  exact (isClosed_iInter fun j => isClosed_eq (hent _ _) continuous_const).inter
    (isClosed_iInter fun w => isClosed_iInter fun _ => (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => isClosed_eq (hloc w i j) continuous_const).inter
        (isClosed_iInter fun i => isClosed_eq (hloc w i i) continuous_const))

theorem mem_Zset_of {S : Finset (HeightOneSpectrum (𝓞 E))} {m : ℕ} {c u : GA E (m + 1)} (hu : u ∈ NA E (m + 1))
    (h : u * c ∈ mirS E S m) : c ∈ Zset E S m := by
  refine ⟨fun j => by rw [← last_row_mul hu c j]; exact h.2 j, fun w hw => ?_⟩
  have h1 := h.1 w hw
  rw [map_mul] at h1
  rw [eq_inv_of_mul_eq_one_right h1]
  exact IsUT.inv (g := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) u) (IsUT.map hu _)

theorem exists_NA_of_mem_Zset {S : Finset (HeightOneSpectrum (𝓞 E))} {m : ℕ} {c : GA E (m + 1)}
    (hc : c ∈ Zset E S m) : ∃ u ∈ NA E (m + 1), u * c ∈ mirS E S m := by
  classical
  set cf := GeneralLinearGroup.map (pFin E) c
  set L : GL (Fin (m + 1)) (Af E) :=
    (S.toList.map fun w => locGL E (m + 1) w (GeneralLinearGroup.map (pLoc E w) cf)).prod
  have hL : ∀ w, GeneralLinearGroup.map (pLoc E w) L =
      if w ∈ S then GeneralLinearGroup.map (pLoc E w) cf else 1 := by
    intro w
    have key : ∀ l : List (HeightOneSpectrum (𝓞 E)), l.Nodup → GeneralLinearGroup.map (pLoc E w)
        (l.map fun v => locGL E (m + 1) v (GeneralLinearGroup.map (pLoc E v) cf)).prod =
        if w ∈ l then GeneralLinearGroup.map (pLoc E w) cf else 1 := by
      intro l hl
      induction l with
      | nil => simp
      | cons v l ih =>
        rw [List.nodup_cons] at hl
        rw [List.map_cons, List.prod_cons, map_mul, ih hl.2]
        by_cases h : w = v
        · subst h; rw [pLoc_locGL, if_neg hl.1, if_pos List.mem_cons_self, mul_one]
        · rw [pLoc_locGL_of_ne h, one_mul]; simp [h]
    rw [key _ (Finset.nodup_toList _)]; simp
  set k := cf⁻¹ * L
  have hk : ∀ w, GeneralLinearGroup.map (pLoc E w) k =
      if w ∈ S then 1 else (GeneralLinearGroup.map (pLoc E w) cf)⁻¹ := by
    intro w; rw [map_mul, map_inv, hL]; split_ifs <;> simp
  have hkUT : ∀ w, IsUT ((GeneralLinearGroup.map (pLoc E w) k : GL (Fin (m + 1)) (w.adicCompletion E)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) := by
    intro w; rw [hk]; split_ifs with hw
    · exact isUT_one
    · exact IsUT.inv (hc.2 w hw)
  have huNA : finGL E (m + 1) k ∈ NA E (m + 1) := by
    refine ⟨fun i j hij => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
    · show (GeneralLinearGroup.map (pInf E) (finGL E (m + 1) k) : Matrix _ _ _) i j = pInf E 0
      rw [pInf_finGL, map_zero]; exact Matrix.one_apply_ne (ne_of_gt hij)
    · show (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) k) : Matrix _ _ _) i j = pFin E 0
      rw [pFin_finGL, map_zero]
      exact FiniteAdeleRing.ext _ fun w => (hkUT w).1 i j hij
    · show (GeneralLinearGroup.map (pInf E) (finGL E (m + 1) k) : Matrix _ _ _) i i = pInf E 1
      rw [pInf_finGL, map_one]; exact Matrix.one_apply_eq i
    · show (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) k) : Matrix _ _ _) i i = pFin E 1
      rw [pFin_finGL, map_one]
      exact FiniteAdeleRing.ext _ fun w => (hkUT w).2 i
  refine ⟨_, huNA, fun w hw => ?_, fun j => ?_⟩
  · change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) k * c)) = 1
    rw [map_mul, pFin_finGL, map_mul, hk, if_neg hw, inv_mul_cancel]
  · rw [last_row_mul huNA]; exact hc.1 j

theorem exists_base {S : Finset (HeightOneSpectrum (𝓞 E))} {m : ℕ} {d : GA E (m + 1)} (hd : d ∈ Zset E S m)
    (V : GA E (m + 1) → Subgroup (GL (Fin (m + 1)) (Af E))) :
    ∃ q, q ∈ mirS E S m ∧ GeneralLinearGroup.map (pInf E) q = 1 ∧ d ∈ cell (V q) q := by
  obtain ⟨u, hu, hm⟩ := exists_NA_of_mem_Zset hd
  set p := u * d with hp
  refine ⟨finGL E (m + 1) (GeneralLinearGroup.map (pFin E) p), ⟨fun w hw => ?_, fun j => ?_⟩, pInf_finGL _, ?_⟩
  · change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) _)) = 1
    rw [pFin_finGL]; exact hm.1 w hw
  · refine ad_ext ?_ ?_
    · show (GeneralLinearGroup.map (pInf E) (finGL E (m + 1) _) : Matrix _ _ _) (Fin.last m) j =
        pInf E (if j = Fin.last m then 1 else 0)
      rw [pInf_finGL]
      split_ifs with h
      · subst h; simp
      · rw [map_zero]; exact Matrix.one_apply_ne (Ne.symm h)
    · show (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) _) : Matrix _ _ _) (Fin.last m) j =
        pFin E (if j = Fin.last m then 1 else 0)
      rw [pFin_finGL]
      show pFin E ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) = _
      rw [hm.2 j]
  · refine ⟨u⁻¹, NA_inv hu, 1, (V _).one_mem, GeneralLinearGroup.map (pInf E) p, ?_⟩
    rw [map_one, mul_one, mul_assoc, ← infGL_comm, infGL_mul_finGL, hp, inv_mul_cancel_left]

end GlobalTheory.JSW.MirPatch.Cover

namespace GlobalTheory.JSW.MirPatch.Cover

open GlobalTheory.JSW GlobalTheory.JSW.MirPatch Topology

theorem exists_cover : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (C : Set (GA E (m + 1))), IsCompact C → ∀ V : GA E (m + 1) → Subgroup (GL (Fin (m + 1)) (Af E)), (∀ q, IsOpen (V q : Set (GL (Fin (m + 1)) (Af E)))) → ∃ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (R : Finset (GA E (m + 1))) (j : GA E (m + 1) → GA E (m + 1)), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) ∧ IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) ∧ (∀ x ∈ R, j x ∈ GlobalTheory.JSW.mirS E S m ∧ GeneralLinearGroup.map (pInf E) (j x) = 1 ∧ K ≤ V (j x) ∧ GlobalTheory.JSW.MirPatch.cell K x ⊆ GlobalTheory.JSW.MirPatch.cell (V (j x)) (j x)) ∧ (∀ p ∈ GlobalTheory.JSW.mirS E S m, (∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → ∃ x ∈ R, p ∈ GlobalTheory.JSW.MirPatch.cell K x) ∧ (∀ x ∈ R, ∀ x' ∈ R, ∀ p ∈ GlobalTheory.JSW.mirS E S m, p ∈ GlobalTheory.JSW.MirPatch.cell K x → p ∈ GlobalTheory.JSW.MirPatch.cell K x' → x = x') := by
  intro E _ _ _ m S C hC V hV
  classical
  set D := C ∩ Zset E S m
  have hD : IsCompact D := hC.inter_right (isClosed_Zset S m)
  have hq : ∀ d ∈ D, ∃ q, q ∈ mirS E S m ∧ GeneralLinearGroup.map (pInf E) q = 1 ∧ d ∈ cell (V q) q :=
    fun d hd => exists_base hd.2 V
  choose! q hq using hq
  obtain ⟨t, htD, hcov⟩ := hD.elim_nhds_subcover (fun d => cell (V (q d)) (q d))
    (fun d hd => (isOpen_cell (hV _) _).mem_nhds (hq d hd).2.2)
  have hB : (⋂ d ∈ t, (V (q d) : Set (GL (Fin (m + 1)) (Af E)))) ∈ 𝓝 (1 : GL (Fin (m + 1)) (Af E)) :=
    (isOpen_biInter_finset fun d _ => hV (q d)).mem_nhds (Set.mem_iInter₂.2 fun d _ => (V (q d)).one_mem)
  obtain ⟨K, hKo, hKc, hKB⟩ := GlobalTheory.GLFin.exists_compact_open_subgroup_subset_nhds_one E (m + 1) _ hB
  have hKle : ∀ d ∈ t, K ≤ V (q d) := fun d hd k hk => Set.mem_iInter₂.1 (hKB hk) d hd
  obtain ⟨t2, ht2D, hcov2⟩ := hD.elim_nhds_subcover (fun d => cell K d)
    (fun d _ => (isOpen_cell hKo d).mem_nhds (self_mem_cell K d))
  have hj : ∀ x ∈ t2, ∃ d ∈ t, x ∈ cell (V (q d)) (q d) := fun x hx => by
    simpa using hcov (ht2D x hx)
  choose! dj hdj using hj
  let rep : Set (GA E (m + 1)) → GA E (m + 1) := fun s => if h : ∃ x ∈ t2, cell K x = s then h.choose else 1
  have hrep : ∀ x ∈ t2, rep (cell K x) ∈ t2 ∧ cell K (rep (cell K x)) = cell K x := by
    intro x hx
    have h : ∃ y ∈ t2, cell K y = cell K x := ⟨x, hx, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨K, t2.image fun x => rep (cell K x), fun x => q (dj x), hKo, hKc, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, -⟩ := hrep x0 hx0
    have hd := hdj _ h1
    have hqd := hq _ (htD _ hd.1)
    exact ⟨hqd.1, hqd.2.1, hKle _ hd.1, (cell_mono (hKle _ hd.1) _).trans (cell_subset_of_mem hd.2)⟩
  · rintro p hp ⟨u, hu, hc⟩
    have hcD : u⁻¹ * p ∈ D := ⟨hc, mem_Zset_of (u := u) hu (by rwa [mul_inv_cancel_left])⟩
    obtain ⟨x, hx, hmem⟩ : ∃ x ∈ t2, u⁻¹ * p ∈ cell K x := by simpa using hcov2 hcD
    refine ⟨rep (cell K x), Finset.mem_image_of_mem _ hx, ?_⟩
    rw [(hrep x hx).2]
    have := NA_mul_mem_cell hu hmem
    rwa [mul_inv_cancel_left] at this
  · intro x hx x' hx' p _ h1 h2
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨x0', hx0', rfl⟩ := Finset.mem_image.1 hx'
    have e : cell K x0 = cell K x0' := by
      rw [← (hrep x0 hx0).2, ← (hrep x0' hx0').2]; exact cell_eq_of_mem h1 h2
    simp only [e]

end GlobalTheory.JSW.MirPatch.Cover
