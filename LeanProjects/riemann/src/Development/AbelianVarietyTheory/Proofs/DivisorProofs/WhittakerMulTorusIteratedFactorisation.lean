import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW

theorem map_pLoc_pFin_finGL_locGL_of_ne {E : Type} [Field E] [NumberField E] {a : ℕ}
    {v w : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (k : GL (Fin a) (w.adicCompletion E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a (locGL E a w k)) = 1 := by
  have e : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a (locGL E a w k)) =
      GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) (finGL E a (locGL E a w k))) := by
    ext; rfl
  rw [e, pFin_finGL, pLoc_locGL_of_ne h]

theorem whit_mul_list_prod (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ) (φ) (hφV : φ ∈ π.V)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) → Fin a → ℕ)
    (L : List (HeightOneSpectrum (𝓞 E))) (hL : L.Nodup)
    (hw : ∀ w ∈ L, (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) ∧
      HasSatGL w (π.locRep w) (Finset.univ.val.map (α w)) ∧
      (∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) ∧ IsUnifV E w (ϖ w : w.adicCompletion E)) :
    ∀ g : GA E a, (∀ w ∈ L, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1) →
      GlobalTheory.JSW.whit φ.1 (g * (L.map fun w => finGL E a (locGL E a w (diagPow (ϖ w) (l w)))).prod) =
        (L.map fun w => GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)).prod * GlobalTheory.JSW.whit φ.1 g := by
  induction L with
  | nil => intro g _; simp
  | cons w L ih =>
    intro g hg
    rw [List.nodup_cons] at hL
    have hw0 := hw w (List.mem_cons_self ..)
    have ih' := ih hL.2 (fun v hv => hw v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, ih' (g * finGL E a (locGL E a w (diagPow (ϖ w) (l w)))) ?_,
      whit_mul_locGL_diagPow E a π w (α w) hw0.1 hw0.2.1 φ hφV hw0.2.2.1 g (hg w (List.mem_cons_self ..))
        (ϖ w) hw0.2.2.2 (l w)]
    · ring
    · intro v hv
      have hne : v ≠ w := fun h => hL.1 (h ▸ hv)
      rw [map_mul, hg v (List.mem_cons_of_mem _ hv), map_pLoc_pFin_finGL_locGL_of_ne hne, one_mul]

theorem whit_mul_tl : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.JSW.tl ϖ l) = (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ.1 x := by
  intro E _ _ _ a S hψ π α hα φ hφV hφ ϖ hϖ l hl x hx
  have hmem : ∀ w ∈ l.support.toList, w ∉ S := fun w hw => hl w (Finset.mem_toList.1 hw)
  rw [tl, whit_mul_list_prod E a π α φ hφV ϖ l l.support.toList (Finset.nodup_toList _)
      (fun w hw => ⟨hψ w (hmem w hw), hα w (hmem w hw), hφ w (hmem w hw), hϖ w⟩) x
      (fun w hw => hx w (hmem w hw))]
  congr 1
  exact Finset.prod_map_toList _ _

end GlobalTheory.JSW
