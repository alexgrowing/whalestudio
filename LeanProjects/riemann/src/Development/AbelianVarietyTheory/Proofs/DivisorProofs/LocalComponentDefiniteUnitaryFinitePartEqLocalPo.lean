import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPtLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def fstA (E : Type) [Field E] [NumberField E] : Ad E →+* InfiniteAdeleRing E := RingHom.fst _ _

theorem fst_entry (γ : GL (Fin n) E) (i j : Fin n) :
    fstA E ((finGL E n (ratF E n γ)).val i j) = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E)) i j := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).1 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem snd_entry (γ : GL (Fin n) E) (i j : Fin n) :
    pFin E ((finGL E n (ratF E n γ)).val i j) = algebraMap E (Af E) (γ.val i j) := by
  change ((1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E × Af E)) i j -
      ((0 : InfiniteAdeleRing E), (1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      ((0 : InfiniteAdeleRing E), algebraMap E (Af E) (γ.val i j))).2 = _
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_cT {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (M : Matrix (Fin n) (Fin n) A) : (cT σ M).map f = cT τ (M.map f) := by
  ext i j; simp [cT, h]

theorem ext_ad (M N : Matrix (Fin n) (Fin n) (Ad E)) (h1 : M.map (fstA E) = N.map (fstA E))
    (h2 : M.map (pFin E) = N.map (pFin E)) : M = N := by
  ext i j
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem mem_UA (γ : UE E n) : finGL E n (ratF E n γ.1) ∈ UA E n := by
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  show cT (conjAd E) (finGL E n (ratF E n γ.1)).val * 1 * (finGL E n (ratF E n γ.1)).val = 1
  have hf : (finGL E n (ratF E n γ.1)).val.map (fstA E) = 1 := by
    ext i j; rw [Matrix.map_apply, fst_entry]
  have hs : (finGL E n (ratF E n γ.1)).val.map (pFin E) = γ.1.val.map (algebraMap E (Af E)) := by
    ext i j; rw [Matrix.map_apply, snd_entry]; rfl
  apply ext_ad
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (fstA E) (conjAd E) ((infEq E).toRingHom.comp ((starRingEnd (Cinf E)).comp (infEq E).symm.toRingHom)) (fun x => rfl), hf, Matrix.map_one _ (map_zero _) (map_one _)]
    ext i j; simp [cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_cT (pFin E) (conjAd E) (conjFin (IsCMField.complexConj E).toRingEquiv) (fun x => rfl), hs,
      Matrix.map_one _ (map_zero _) (map_one _)]
    have : cT (conjFin (IsCMField.complexConj E).toRingEquiv) (γ.1.val.map (algebraMap E (Af E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val).map (algebraMap E (Af E)) := by
      ext i j; simp [cT, conjFin_algebraMap]
    rw [this, ← Matrix.map_one (algebraMap E (Af E)) (map_zero _) (map_one _), ← Matrix.map_mul, ← Matrix.map_mul, hγ]

theorem toSub_of_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (h : g ∈ H) : toSub H g = ⟨g, h⟩ :=
  dif_pos h

theorem mem_finU (γ : UE E n) : (⟨_, mem_UA γ⟩ : UA E n) ∈ finU E n := by
  show cInf (⟨_, mem_UA γ⟩ : UA E n) = 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change (infEq E).symm (fstA E ((finGL E n (ratF E n γ.1)).val i j)) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j
  rw [fst_entry]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem finPt_eq (γ : UE E n) : ((finPt γ : finU E n) : UA E n) = ⟨_, mem_UA γ⟩ := by
  have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = ⟨_, mem_UA γ⟩ := toSub_of_mem _ _ (mem_UA γ)
  unfold finPt
  rw [h1, toSub_of_mem _ _ (mem_finU γ)]

end GlobalTheory.BCT.FinPtLoc

theorem GlobalTheory.BCT.locPt_finPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (γ : UE E n) (w : Pl E),
    toSub (UL n w) (cLoc w ((finPt γ : finU E n) : UA E n)) = locPt w γ := by
  intro E _ _ _ _ n γ w
  rw [FinPtLoc.finPt_eq]
  unfold locPt
  congr 1
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
  rw [FinPtLoc.snd_entry]
  rfl
