import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUn
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Pointwise

noncomputable section

namespace GlobalTheory.UnitarySplit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* finU E n :=
  ((((finGL E n).comp (GeneralLinearGroup.map (pFin E))).comp (UA E n).subtype).codRestrict (UA E n)
    fun g => GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin g)).codRestrict (finU E n)
    fun _ => pInf_finGL _

def infPart : UA E n →* infU E n :=
  (((infGL E n).comp cInf).codRestrict (UA E n)
    fun g => by
      have h := (UA E n).mul_mem g.2 ((UA E n).inv_mem (finPart g).1.2)
      have e : (finPart g).1.1 = finGL E n (GeneralLinearGroup.map (pFin E) g.1) := rfl
      rw [e] at h
      nth_rewrite 1 [← infGL_mul_finGL g.1] at h
      rw [mul_inv_cancel_right] at h
      exact h).codRestrict (infU E n)
    fun _ => pFin_infGL _

theorem finPart_val (g : UA E n) : (finPart g).1.1 = finGL E n (GeneralLinearGroup.map (pFin E) g.1) := rfl

theorem infPart_val (g : UA E n) : (infPart g).1.1 = infGL E n (GeneralLinearGroup.map (pInf E) g.1) := rfl

theorem continuous_finPart : Continuous (finPart (E := E) (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact GlobalTheory.DefU.ClassFin.continuous_finGL.comp
    ((Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
      continuous_subtype_val)

theorem continuous_infPart : Continuous (infPart (E := E) (n := n)) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  exact GlobalTheory.DefU.continuous_infGL.comp GlobalTheory.DefU.continuous_cInf

theorem finPart_mul_infPart (g : UA E n) : g = (finPart g).1 * (infPart g).1 := by
  rw [GlobalTheory.DefU.fin_mul_inf (finPart g).2 (infPart g).2]
  exact Subtype.ext (infGL_mul_finGL g.1).symm

theorem cInf_infPart (g : UA E n) : cInf (infPart g).1 = cInf g := pInf_infGL _

theorem finPart_fin (g : finU E n) : finPart g.1 = g :=
  Subtype.ext (Subtype.ext (GlobalTheory.CuspRep.ga_ext ((pInf_finGL _).trans g.2.symm) (pFin_finGL _)))

theorem infPart_inf (k : infU E n) : infPart k.1 = k :=
  Subtype.ext (Subtype.ext (GlobalTheory.CuspRep.ga_ext (pInf_infGL _) ((pFin_infGL _).trans k.2.symm)))

theorem finPart_inf (k : infU E n) : finPart k.1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  have h : GeneralLinearGroup.map (pFin E) k.1.1 = 1 := k.2
  rw [finPart_val, h, map_one]
  rfl

theorem infPart_fin (g : finU E n) : infPart g.1 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  have h : GeneralLinearGroup.map (pInf E) g.1.1 = 1 := g.2
  rw [infPart_val, h, map_one]
  rfl

theorem dense_rat_inf : Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} := by
  intro k
  rw [← infPart_inf k]
  refine closure_mono ?_ (image_closure_subset_closure_image continuous_infPart
    ⟨k.1, GlobalTheory.WeightRealExt.dense_rat_fin k.1, rfl⟩)
  rintro _ ⟨_, ⟨γ, hγ, g, hg, rfl⟩, rfl⟩
  refine ⟨γ, hγ, ?_⟩
  have hg' : cInf g = 1 := hg
  rw [cInf_infPart, map_mul, hg', mul_one]

theorem dense_and_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), Dense ((ratU E n : Set (UA E n)) * (finU E n : Set (UA E n))) ∧ Dense {k : infU E n | ∃ γ ∈ ratU E n, cInf k.1 = cInf γ} ∧ (∀ k : infU E n, ∀ g ∈ finU E n, k.1 * g = g * k.1) ∧ ∃ (a : UA E n →* finU E n) (b : UA E n →* infU E n), Continuous a ∧ Continuous b ∧ (∀ x, x = (a x).1 * (b x).1) ∧ ∀ (g : finU E n) (k : infU E n), a (g.1 * k.1) = g ∧ b (g.1 * k.1) = k := by
  intro E _ _ _ n
  refine ⟨GlobalTheory.WeightRealExt.dense_rat_fin, dense_rat_inf, fun k g hg => (GlobalTheory.DefU.fin_mul_inf hg k.2).symm,
    finPart, infPart, continuous_finPart, continuous_infPart, finPart_mul_infPart, fun g k => ⟨?_, ?_⟩⟩
  · rw [map_mul, finPart_fin, finPart_inf, mul_one]
  · rw [map_mul, infPart_fin, infPart_inf, one_mul]

end GlobalTheory.UnitarySplit

end
