import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfAbsNormEqSq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Fact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_KGL_of {w : Pl E} (g : GL (Fin n) (w.adicCompletion E))
    (h1 : ∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) (h2 : ∀ i j, g⁻¹.1 i j ∈ w.adicCompletionIntegers E) :
    g ∈ GlobalTheory.LFun.KGL w n := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KGL (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w n := by
  have h : ∀ g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E), ∀ᶠ w : Pl E in cofinite,
      ∀ i j, pLoc E w (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]
    exact fun i j => (g.val i j).2
  filter_upwards [h x, h x⁻¹] with w a b
  exact mem_KGL_of _ a (by rw [← map_inv]; exact b)

theorem map_prjG (T : Finset (Pl E)) (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) {w : Pl E} (hw : w ∈ T) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T x) = GeneralLinearGroup.map (pLoc E w) x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have he : pLoc E w (idem E T) = 1 := by
    show (if w ∈ T then (1 : w.adicCompletion E) else 0) = 1
    rw [if_pos hw]
  show pLoc E w ((idem E T • x.val + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))) i j) =
    pLoc E w (x.val i j)
  simp [Matrix.add_apply, Matrix.smul_apply, map_add, map_mul, map_sub, he]

theorem mem_orb_iff {u w : Pl E} : w ∈ (orb E u : Set (Pl E)) ↔
    w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := by
  have hm := GlobalTheory.QuadPlaces.main (maximalRealSubfield E) E (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj E) (IsCMField.complexConj_ne_one E) u
  simp only [orb, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact hm.2.1
  · intro h
    exact hm.1 w h

theorem finprod_orb (S : Set (Pl E)) (φ : ∀ w : Pl E, GLw n w → ℂ) (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E))
    (u : Pl E) :
    FU E n S φ u (pfU E n u x) = ∏ w ∈ orb E u, (if w ∈ S then φ w (GeneralLinearGroup.map (pLoc E w) x) else
      (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x)) := by
  set f : Pl E → ℂ := fun w => if w ∈ S then φ w (GeneralLinearGroup.map (pLoc E w) x) else
      (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x) with hf
  have hx : ∀ w ∈ (orb E u : Set (Pl E)), GeneralLinearGroup.map (pLoc E w) (pfU E n u x).1 =
      GeneralLinearGroup.map (pLoc E w) x := fun w hw => map_prjG (orb E u) x hw
  have h1 : (∏ᶠ w ∈ S ∩ ↑(orb E u), φ w (GeneralLinearGroup.map (pLoc E w) (pfU E n u x).1)) =
      ∏ᶠ w ∈ ↑(orb E u) ∩ S, f w := by
    rw [Set.inter_comm]
    refine finprod_mem_congr rfl fun w hw => ?_
    rw [hf]; dsimp only; rw [if_pos hw.2, hx w hw.1]
  have h2 : (∏ᶠ w ∈ Sᶜ ∩ ↑(orb E u), (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1
      (GeneralLinearGroup.map (pLoc E w) (pfU E n u x).1)) = ∏ᶠ w ∈ ↑(orb E u) \ S, f w := by
    rw [Set.diff_eq, Set.inter_comm]
    refine finprod_mem_congr rfl fun w hw => ?_
    rw [hf]; dsimp only; rw [if_neg hw.2, hx w hw.1]
  rw [FU, h1, h2, finprod_mem_inter_mul_diff S (orb E u).finite_toSet, finprod_mem_coe_finset]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (GLw n w), IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' → ∀ φ : ∀ w : Pl E, GLw n w → ℂ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E), (∏ᶠ w ∈ S, φ w (GeneralLinearGroup.map (pLoc E w) x)) * ∏ᶠ w ∈ Sᶜ, (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x) = ∏ᶠ u : S, GlobalTheory.EulerTw.FU E n S φ u.1 (GlobalTheory.EulerTw.pfU E n u.1 x) := by
  intro E _ _ _ n S hS K' _ φ hφ x
  set f : Pl E → ℂ := fun w => if w ∈ S then φ w (GeneralLinearGroup.map (pLoc E w) x) else
      (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x) with hf

  have hfin : (Function.mulSupport f).Finite := by
    refine (Filter.eventually_cofinite.1 (hφ.2.and (eventually_mem_KGL (E := E) x))).subset fun w hw => ?_
    rintro ⟨h1, h2⟩
    apply hw
    have hi : (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) (GeneralLinearGroup.map (pLoc E w) x) = 1 :=
      Set.indicator_of_mem h2 _
    show f w = 1
    rw [hf]; dsimp only
    split_ifs
    · rw [h1]; exact hi
    · exact hi

  have hL : (∏ᶠ w ∈ S, φ w (GeneralLinearGroup.map (pLoc E w) x)) * ∏ᶠ w ∈ Sᶜ,
      (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x) = ∏ᶠ w, f w := by
    have e1 : (∏ᶠ w ∈ S, φ w (GeneralLinearGroup.map (pLoc E w) x)) = ∏ᶠ w ∈ S, f w :=
      finprod_mem_congr rfl fun w hw => by rw [hf]; dsimp only; rw [if_pos hw]
    have e2 : (∏ᶠ w ∈ Sᶜ, (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x)) =
        ∏ᶠ w ∈ Sᶜ, f w :=
      finprod_mem_congr rfl fun w hw => by rw [hf]; dsimp only; rw [if_neg hw]
    rw [e1, e2, ← finprod_mem_union'' (disjoint_compl_right.mono Set.inter_subset_left Set.inter_subset_left) (hfin.subset Set.inter_subset_right)
      (hfin.subset Set.inter_subset_right), Set.union_compl_self, finprod_mem_univ]

  let r : Pl E → S := fun w => ⟨(hS w).exists.choose, (hS w).exists.choose_spec.1⟩
  have hr : ∀ w, (r w).1.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
    fun w => (hS w).exists.choose_spec.2
  have hru : ∀ (u : S) w, w ∈ (orb E u.1 : Set (Pl E)) ↔ r w = u := fun u w => by
    rw [mem_orb_iff]
    constructor
    · intro h
      exact Subtype.ext ((hS w).unique ⟨(r w).2, hr w⟩ ⟨u.2, h.symm⟩)
    · rintro rfl
      exact (hr w).symm
  set s := hfin.toFinset with hs
  have hsupp : ∀ w, w ∉ s → f w = 1 := fun w hw => by
    rw [hs, Set.Finite.mem_toFinset] at hw
    exact Function.notMem_mulSupport.1 hw
  rw [hL, finprod_eq_prod_of_mulSupport_subset f (s := s) (by rw [hs, Set.Finite.coe_toFinset])]
  have hg : ∀ u : S, FU E n S φ u.1 (pfU E n u.1 x) = ∏ w ∈ s with r w = u, f w := fun u => by
    rw [finprod_orb]
    refine (Finset.prod_subset (fun w hw => ?_) fun w hw hw' => ?_).symm
    · rw [← Finset.mem_coe, hru]
      exact (Finset.mem_filter.1 hw).2
    · by_contra hne
      exact hw' (Finset.mem_filter.2 ⟨by_contra fun h => hne (hsupp w h), (hru u w).1 (Finset.mem_coe.2 hw)⟩)
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := s.image r) fun u hu => ?_]
  · rw [Finset.prod_congr rfl fun u _ => hg u]
    exact (Finset.prod_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem r hw) f).symm

  · rw [Function.mem_mulSupport, hg u] at hu
    obtain ⟨w, hw, -⟩ := Finset.exists_ne_one_of_prod_ne_one hu
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨w, (Finset.mem_filter.1 hw).1, (Finset.mem_filter.1 hw).2⟩)

end GlobalTheory.EulerTw.Fact
