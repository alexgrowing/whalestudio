import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitaryStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.ClassFinLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* finU E n where
  toFun u := ⟨⟨finGL E n (GeneralLinearGroup.map (pFin E) u.1), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin u)⟩,
    pInf_finGL _⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' a b := Subtype.ext (Subtype.ext (by simp))

theorem finPart_fin (k : finU E n) : finPart (k : UA E n) = k :=
  Subtype.ext (Subtype.ext (GlobalTheory.DefU.ClassFin.finGL_pFin k))

theorem finPart_inf {x : UA E n} (hx : x ∈ infU E n) : finPart x = 1 := by
  have h : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext (Subtype.ext ?_)
  change finGL E n (GeneralLinearGroup.map (pFin E) x.1) = 1
  rw [h, map_one]

theorem finPart_rat {γ : UA E n} (hγ : γ ∈ ratU E n) : finPart γ ∈ ratFinU E n := by
  obtain ⟨γ₀, hγ₀'⟩ := hγ
  have hγ₀ : ratGL E n γ₀ = γ.1 := hγ₀'
  have hg : cT (conjAd E) γ.1.val * 1 * γ.1.val = 1 := γ.2
  rw [← hγ₀, mul_one] at hg
  have hv : (ratGL E n γ₀).val = γ₀.val.map (algebraMap E (Ad E)) := rfl
  rw [hv, GlobalTheory.DefU.ClassFin.cT_map (algebraMap E (Ad E)) (IsCMField.complexConj E).toRingEquiv.toRingHom (conjAd E)
    (fun y => (conjAd_algebraMap y).symm), ← Matrix.map_mul] at hg
  have hU : γ₀ ∈ UE E n := by
    change cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * 1 * γ₀.val = 1
    rw [mul_one]
    ext i j
    have := congrFun₂ hg i j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    haveI hnt : Nontrivial (Ad E) := show Nontrivial (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E) from inferInstance
    apply (algebraMap E (Ad E)).injective
    rw [this]
    split_ifs <;> simp
  refine ⟨γ₀, hU, ?_⟩
  change finGL E n (ratF E n γ₀) = finGL E n (GeneralLinearGroup.map (pFin E) γ.1)
  rw [← hγ₀]
  rfl

theorem finite_doubleCoset_of_isOpen (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n))) :
    Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (K : Set (finU E n))) := by
  obtain ⟨T, hT⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hK
  let φ : T → DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (K : Set (finU E n)) :=
    fun s => DoubleCoset.mk _ _ (finPart (s : UA E n))
  refine Finite.of_surjective φ fun q => ?_
  obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk _ _ g = q := ⟨q.out, DoubleCoset.out_eq' _ _ q⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hT (g : UA E n)
  refine ⟨⟨s, hs⟩, ?_⟩
  have hg : g = finPart γ * finPart s * k := by
    have := congrArg finPart e
    rw [finPart_fin, map_mul, map_mul, map_mul, finPart_inf hx, mul_one, finPart_fin] at this
    exact this
  show DoubleCoset.mk _ _ (finPart (s : UA E n)) = DoubleCoset.mk _ _ g
  rw [hg]
  exact (DoubleCoset.eq _ _ _ _).2 ⟨finPart γ, finPart_rat hγ, k, hk, rfl⟩

end GlobalTheory.BCT.ClassFinLev

open GlobalTheory.BCT.ClassFinLev in

theorem GlobalTheory.BCT.finite_doubleCoset_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n))) := by
  intro E _ _ _ hE n _ S _ K' hK
  exact finite_doubleCoset_of_isOpen _ (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hE n S K' hK)
