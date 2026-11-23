import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU.LocRet

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem under_conjSrc (v : HeightOneSpectrum (𝓞 E)) :
    (conjSrc (IsCMField.complexConj E).toRingEquiv v).under (𝓞 (maximalRealSubfield E)) =
      v.under (𝓞 (maximalRealSubfield E)) := by
  have h := conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v
  ext y
  change algebraMap _ (𝓞 E) y ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv v).asIdeal ↔ algebraMap _ (𝓞 E) y ∈ v.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← h]
  have : (IsCMField.complexConj E).toRingEquiv ((algebraMap _ (𝓞 E) y : 𝓞 E) : E) = ((algebraMap _ (𝓞 E) y : 𝓞 E) : E) := by
    change (IsCMField.complexConj E) (algebraMap (maximalRealSubfield E) E (y : maximalRealSubfield E)) = _
    rw [AlgEquiv.commutes]
    rfl
  rw [this]

variable (w : HeightOneSpectrum (𝓞 E))

open Classical in

def idemF : Af E :=
  ⟨fun v => if v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      dsimp only
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩

def idem : Ad E := sFin E (idemF w)

theorem idem_mul_idem : idem w * idem w = idem w := by
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext E fun v => ?_)
  change (idemF w).1 v * (idemF w).1 v = (idemF w).1 v
  simp only [idemF]
  split_ifs <;> simp

def sIdem : Ad E →ₙ+* Ad E where
  toFun x := idem w * x
  map_mul' x y := by
    calc idem w * (x * y) = (idem w * idem w) * (x * y) := by rw [idem_mul_idem]
      _ = idem w * x * (idem w * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pInf_sIdem (x : Ad E) : pInf E (sIdem w x) = 0 := by
  change pInf E (sFin E (idemF w) * x) = 0
  rw [map_mul]
  have : pInf E (sFin E (idemF w)) = 0 := map_zero (infEq E).symm
  rw [this, zero_mul]

theorem pLoc_sIdem_of_eq {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem w x) = ((pLoc E v).comp (pFin E)) x := by
  change ((pLoc E v).comp (pFin E)) (idem w) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem w) = 1 := by
    change (idemF w).1 v = 1
    simp only [idemF, if_pos hv]
  rw [this, one_mul]
  rfl

theorem pLoc_sIdem_of_ne {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem w x) = 0 := by
  change ((pLoc E v).comp (pFin E)) (idem w) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem w) = 0 := by
    change (idemF w).1 v = 0
    simp only [idemF, if_neg hv]
  rw [this, zero_mul]

theorem conjAd_idem : conjAd E (idem w) = idem w := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun v => ?_)
  · change (infEq E) ((starRingEnd (Cinf E)) ((infEq E).symm 0)) = 0
    simp
  change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (idemF w)) = (idemF w).1 v
  rw [pLoc_conjFin]
  change conjLoc _ v ((idemF w).1 _) = (idemF w).1 v
  have hc := under_conjSrc (E := E) v
  simp only [idemF]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (hc.symm.trans h1) h2
  · exact absurd (hc.trans h2) h1
  · simp

variable {w} {n : ℕ}

theorem ga_ext' {g h : GA E n} (h1 : GeneralLinearGroup.map (pInf E) g = GeneralLinearGroup.map (pInf E) h)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g =
      GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) h) : g = h := by
  refine ga_ext h1 (Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_))
  exact congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (h2 v)

theorem cT_corner (M : Matrix (Fin n) (Fin n) (Ad E)) :
    cT (conjAd E) (corner (matN n (sIdem w)) M) = corner (matN n (sIdem w)) (cT (conjAd E) M) := by
  ext i j
  change conjAd E ((1 : Matrix (Fin n) (Fin n) (Ad E)) j i - idem w * (1 : Matrix (Fin n) (Fin n) (Ad E)) j i +
      idem w * M j i) = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - idem w * (1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      idem w * conjAd E (M j i)
  rw [map_add, map_sub, map_mul, map_mul, conjAd_idem, Matrix.one_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem corner_mem (g : UA E n) : cornerGL n (sIdem w) g.1 ∈ UA E n := by
  have hg : cT (conjAd E) (g.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * g.1 = 1 := g.2
  change cT (conjAd E) (corner (matN n (sIdem w)) g.1.1) * 1 * corner (matN n (sIdem w)) g.1.1 = 1
  rw [cT_corner, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT (conjAd E) _), hg, map_one]

variable (n w) in

def ret0 : UA E n →* UA E n := ((cornerGL n (sIdem w)).comp (UA E n).subtype).codRestrict (UA E n) corner_mem

theorem infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one (g : UA E n) : GeneralLinearGroup.map (pInf E) (ret0 w n g).1 = 1 :=
  map_cornerGL_of_zero _ _ (pInf_sIdem w) _

theorem localProj_unitaryAdelicLocalRetractionEnd_of_under_eq {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (g : UA E n) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1 = GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g.1 :=
  map_cornerGL_of_hom _ _ _ (pLoc_sIdem_of_eq w hv) _

theorem localProj_unitaryAdelicLocalRetractionEnd_of_under_ne {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) (g : UA E n) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1 = 1 :=
  map_cornerGL_of_zero _ _ (pLoc_sIdem_of_ne w hv) _

theorem unitaryAdelicLocalRetractionEnd_mem_localPoints (g : UA E n) : ret0 w n g ∈ locU n w := by
  refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one g), Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
  exact MonoidHom.mem_ker.2 (localProj_unitaryAdelicLocalRetractionEnd_of_under_ne hu g)

theorem mem_locU_inf {x : UA E n} (hx : x ∈ locU n w) : GeneralLinearGroup.map (pInf E) x.1 = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1

theorem mem_locU_ne {x : UA E n} (hx : x ∈ locU n w) {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) x.1 = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 v) hv)

variable (n w) in

def ret : UA E n →* locU n w := (ret0 w n).codRestrict (locU n w) unitaryAdelicLocalRetractionEnd_mem_localPoints

theorem continuous_ret : Continuous (ret w n) := by
  have hc : Continuous (corner (matN n (sIdem w))) := by
    change Continuous fun M : Matrix (Fin n) (Fin n) (Ad E) => 1 - (1 : Matrix (Fin n) (Fin n) (Ad E)).map (idem w * ·) +
      M.map (idem w * ·)
    exact continuous_const.add (continuous_id.matrix_map (continuous_const.mul continuous_id))
  exact Continuous.subtype_mk (Continuous.subtype_mk ((Continuous.units_map _ hc).comp continuous_subtype_val) _) _

theorem ret_of_mem (x : locU n w) : ret w n x = x := by
  refine Subtype.ext (Subtype.ext (ga_ext' ?_ fun v => ?_))
  · exact (infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one x.1).trans (mem_locU_inf x.2).symm
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · exact localProj_unitaryAdelicLocalRetractionEnd_of_under_eq hv x.1
    · exact (localProj_unitaryAdelicLocalRetractionEnd_of_under_ne hv x.1).trans (mem_locU_ne x.2 hv).symm

theorem commute_ret (g : UA E n) (y : locU n w) : Commute ((ret w n g : UA E n)⁻¹ * g) (y : UA E n) := by
  refine Subtype.ext (ga_ext' ?_ fun v => ?_)
  · simp only [Subgroup.coe_mul, map_mul, mem_locU_inf y.2, one_mul, mul_one]
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · have h : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (((ret w n g : UA E n)⁻¹ * g : UA E n) : GA E n) = 1 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        change (GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1)⁻¹ * _ = 1
        rw [localProj_unitaryAdelicLocalRetractionEnd_of_under_eq hv g, inv_mul_cancel]
      simp only [Subgroup.coe_mul, map_mul] at h ⊢
      rw [h, one_mul, mul_one]
    · simp only [Subgroup.coe_mul, map_mul, mem_locU_ne y.2 hv, one_mul, mul_one]

theorem exists_ret (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ r : UA E n →* locU n w, Continuous r ∧ (∀ x : locU n w, r x = x) ∧
      ∀ (g : UA E n) (y : locU n w), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) :=
  ⟨ret w n, continuous_ret, ret_of_mem, commute_ret⟩

end GlobalTheory.DefU.LocRet

end
