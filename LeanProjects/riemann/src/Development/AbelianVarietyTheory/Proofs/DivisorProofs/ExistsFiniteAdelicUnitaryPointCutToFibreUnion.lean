import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FibreCut

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def idemF (P : Set (Pl E)) : Af E :=
  ⟨fun v => if v ∈ P then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      dsimp only
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩

def idem (P : Set (Pl E)) : Ad E := sFin E (idemF P)

theorem idem_mul_idem (P : Set (Pl E)) : idem P * idem P = idem P := by
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext E fun v => ?_)
  change (idemF P).1 v * (idemF P).1 v = (idemF P).1 v
  simp only [idemF]
  split_ifs <;> simp

def sIdem (P : Set (Pl E)) : Ad E →ₙ+* Ad E where
  toFun x := idem P * x
  map_mul' x y := by
    calc idem P * (x * y) = (idem P * idem P) * (x * y) := by rw [idem_mul_idem]
      _ = idem P * x * (idem P * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pInf_sIdem (P : Set (Pl E)) (x : Ad E) : pInf E (sIdem P x) = 0 := by
  change pInf E (sFin E (idemF P) * x) = 0
  rw [map_mul]
  have : pInf E (sFin E (idemF P)) = 0 := map_zero (infEq E).symm
  rw [this, zero_mul]

theorem pLoc_sIdem_of_mem (P : Set (Pl E)) {v : Pl E} (hv : v ∈ P) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem P x) = ((pLoc E v).comp (pFin E)) x := by
  change ((pLoc E v).comp (pFin E)) (idem P) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem P) = 1 := by
    change (idemF P).1 v = 1
    simp only [idemF, if_pos hv]
  rw [this, one_mul]
  rfl

theorem pLoc_sIdem_of_not_mem (P : Set (Pl E)) {v : Pl E} (hv : v ∉ P) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem P x) = 0 := by
  change ((pLoc E v).comp (pFin E)) (idem P) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem P) = 0 := by
    change (idemF P).1 v = 0
    simp only [idemF, if_neg hv]
  rw [this, zero_mul]

theorem conjAd_idem (P : Set (Pl E))
    (hP : ∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P) :
    conjAd E (idem P) = idem P := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun v => ?_)
  · change (infEq E) ((starRingEnd (Cinf E)) ((infEq E).symm 0)) = 0
    simp
  change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (idemF P)) = (idemF P).1 v
  rw [pLoc_conjFin]
  change conjLoc _ v ((idemF P).1 _) = (idemF P).1 v
  have hc := GlobalTheory.DefU.LocRet.under_conjSrc (E := E) v
  simp only [idemF]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (hP _ _ hc h1) h2
  · exact absurd (hP _ _ hc.symm h2) h1
  · simp

variable {n : ℕ}

theorem cT_corner (P : Set (Pl E))
    (hP : ∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P)
    (M : Matrix (Fin n) (Fin n) (Ad E)) :
    cT (conjAd E) (corner (matN n (sIdem P)) M) = corner (matN n (sIdem P)) (cT (conjAd E) M) := by
  ext i j
  change conjAd E ((1 : Matrix (Fin n) (Fin n) (Ad E)) j i - idem P * (1 : Matrix (Fin n) (Fin n) (Ad E)) j i +
      idem P * M j i) = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - idem P * (1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      idem P * conjAd E (M j i)
  rw [map_add, map_sub, map_mul, map_mul, conjAd_idem P hP, Matrix.one_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem corner_mem (P : Set (Pl E))
    (hP : ∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P)
    (g : UA E n) : cornerGL n (sIdem P) g.1 ∈ UA E n := by
  have hg : cT (conjAd E) (g.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * g.1 = 1 := g.2
  change cT (conjAd E) (corner (matN n (sIdem P)) g.1.1) * 1 * corner (matN n (sIdem P)) g.1.1 = 1
  rw [cT_corner P hP, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT (conjAd E) _), hg, map_one]

theorem exists_cut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Set (Pl E)),
    (∀ u v : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v.under (𝓞 (maximalRealSubfield E)) → u ∈ P → v ∈ P) →
    ∀ g ∈ finU E n, ∃ x ∈ finU E n, ∀ v : Pl E, cLoc v x = if v ∈ P then cLoc v g else 1 := by
  intro E _ _ _ n P hP g _
  refine ⟨⟨cornerGL n (sIdem P) g.1, corner_mem P hP g⟩, ?_, fun v => ?_⟩
  · exact MonoidHom.mem_ker.2 (map_cornerGL_of_zero _ _ (pInf_sIdem P) _)
  · split_ifs with hv
    · exact map_cornerGL_of_hom _ _ _ (pLoc_sIdem_of_mem P hv) _
    · exact map_cornerGL_of_zero _ _ (pLoc_sIdem_of_not_mem P hv) _

end GlobalTheory.FibreCut

end
