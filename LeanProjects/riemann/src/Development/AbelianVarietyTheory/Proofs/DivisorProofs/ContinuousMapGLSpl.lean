import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

theorem pLoc_idem_spl (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

theorem pLoc_prjG_spl (T : Finset (Pl E)) (w : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T g) =
      if w ∈ T then GeneralLinearGroup.map (pLoc E w) g else 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pLoc E w (((idem E T • g.val + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))) :
    Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = _
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, pLoc_idem_spl]
  split_ifs with h
  · simp
  · simp [Matrix.one_apply, apply_ite (pLoc E w)]

theorem glAf_ext_spl {g h : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (H : ∀ w, GeneralLinearGroup.map (pLoc E w) g = GeneralLinearGroup.map (pLoc E w) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun x : GL (Fin n) (w.adicCompletion E) => x.val i j) (H w)

theorem continuous_pLoc_spl (w : Pl E) : Continuous (pLoc E w) :=
  RestrictedProduct.continuous_eval (R := fun w : Pl E => w.adicCompletion E)
    (A := fun w : Pl E => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) w

theorem continuous_sLoc_spl (v : Pl E) : Continuous (sLoc E v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (Pl E)) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun u : Pl E => u.adicCompletion E)
      (fun u => (u.adicCompletionIntegers E : Set (u.adicCompletion E))) (Filter.principal {v}ᶜ) :=
    fun a => ⟨Pi.single v a, fun u hu => by
      rw [Set.mem_setOf_eq, Pi.single_eq_of_ne hu]; exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

theorem continuous_mapGL_spl (w : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_pLoc_spl E w))

theorem continuous_locGL_spl (w : Pl E) : Continuous (locGL E n w) :=
  Continuous.units_map _ (continuous_const.add (Continuous.matrix_map continuous_id (continuous_sLoc_spl E w)))

variable {E n}

def psiG_spl (u : Pl E) (p : GLw n u × GLw n (cPl E u)) : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) :=
  locGL E n u p.1 * locGL E n (cPl E u) p.2

theorem pLoc_psiG_self_spl {u : Pl E} (hu : cPl E u ≠ u) (p : GLw n u × GLw n (cPl E u)) :
    GeneralLinearGroup.map (pLoc E u) (psiG_spl u p) = p.1 := by
  rw [psiG_spl, map_mul, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hu), mul_one]

theorem pLoc_psiG_conj_spl {u : Pl E} (hu : cPl E u ≠ u) (p : GLw n u × GLw n (cPl E u)) :
    GeneralLinearGroup.map (pLoc E (cPl E u)) (psiG_spl u p) = p.2 := by
  rw [psiG_spl, map_mul, pLoc_locGL, pLoc_locGL_of_ne hu, one_mul]

theorem pLoc_psiG_of_ne_spl {u w : Pl E} (h1 : w ≠ u) (h2 : w ≠ cPl E u) (p : GLw n u × GLw n (cPl E u)) :
    GeneralLinearGroup.map (pLoc E w) (psiG_spl u p) = 1 := by
  rw [psiG_spl, map_mul, pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]

theorem mem_orb_spl {u w : Pl E} : w ∈ orb E u ↔ w = u ∨ w = cPl E u := by
  simp [orb]

theorem pLoc_gam_of_ne_spl {u w : Pl E} (h1 : w ≠ u) (h2 : w ≠ cPl E u) (g : Gam E n u) :
    GeneralLinearGroup.map (pLoc E w) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) = 1 := by
  obtain ⟨h, hh⟩ := g.2
  rw [← hh, pLoc_prjG_spl, if_neg (by rw [mem_orb_spl]; tauto)]

theorem psiG_mem_spl {u : Pl E} (hu : cPl E u ≠ u) (p : GLw n u × GLw n (cPl E u)) : psiG_spl u p ∈ Gam E n u := by
  refine ⟨psiG_spl u p, glAf_ext_spl E n fun w => ?_⟩
  rw [pLoc_prjG_spl]
  split_ifs with hw
  · rfl
  · rw [mem_orb_spl, not_or] at hw
    rw [pLoc_psiG_of_ne_spl hw.1 hw.2]

theorem rho_apply_spl (u : Pl E) (g : Gam E n u) :
    rho E n u g = (GeneralLinearGroup.map (pLoc E u) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)),
      GeneralLinearGroup.map (pLoc E (cPl E u)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) := rfl

def rhoHomeo_spl {u : Pl E} (hu : cPl E u ≠ u) : Gam E n u ≃ₜ GLw n u × GLw n (cPl E u) where
  toFun := rho E n u
  invFun p := ⟨psiG_spl u p, psiG_mem_spl hu p⟩
  left_inv g := by
    refine Subtype.ext (glAf_ext_spl E n fun w => ?_)
    change GeneralLinearGroup.map (pLoc E w) (psiG_spl u (rho E n u g)) = _
    by_cases h1 : w = u
    · subst h1; rw [pLoc_psiG_self_spl hu]; rfl
    by_cases h2 : w = cPl E u
    · subst h2; rw [pLoc_psiG_conj_spl hu]; rfl
    rw [pLoc_psiG_of_ne_spl h1 h2, pLoc_gam_of_ne_spl h1 h2]
  right_inv p := by
    rw [rho_apply_spl]
    exact Prod.ext (pLoc_psiG_self_spl hu p) (pLoc_psiG_conj_spl hu p)
  continuous_toFun :=
    ((continuous_mapGL_spl E n u).comp continuous_subtype_val).prodMk
      ((continuous_mapGL_spl E n (cPl E u)).comp continuous_subtype_val)
  continuous_invFun :=
    Continuous.subtype_mk (((continuous_locGL_spl E n u).comp continuous_fst).mul
      ((continuous_locGL_spl E n (cPl E u)).comp continuous_snd)) _

end GlobalTheory.EulerTw
