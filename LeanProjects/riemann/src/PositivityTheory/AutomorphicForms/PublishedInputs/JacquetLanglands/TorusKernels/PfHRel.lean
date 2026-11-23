import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.HeckeRelationLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def asm (g : InfinitePlace F → GL (Fin 2) ℝ) : GL (Fin 2) (TR.Rinf F) where
  val := Matrix.of fun i j v => (g v).val i j
  inv := Matrix.of fun i j v => (g v)⁻¹.val i j
  val_inv := by
    refine Matrix.ext fun i j => funext fun v => ?_
    have h := congrFun (congrFun (g v).mul_inv i) j
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (g v).val i 0 * (g v)⁻¹.val 0 j + (g v).val i 1 * (g v)⁻¹.val 1 j = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v
    rw [h]
    fin_cases i <;> fin_cases j <;> rfl
  inv_val := by
    refine Matrix.ext fun i j => funext fun v => ?_
    have h := congrFun (congrFun (g v).inv_mul i) j
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (g v)⁻¹.val i 0 * (g v).val 0 j + (g v)⁻¹.val i 1 * (g v).val 1 j = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j v
    rw [h]
    fin_cases i <;> fin_cases j <;> rfl

omit [NumberField F] [IsTotallyReal F] in
theorem gv_asm (g : InfinitePlace F → GL (Fin 2) ℝ) (v : InfinitePlace F) : gv v (asm g) = g v :=
  Units.ext (Matrix.ext fun _ _ => rfl)

omit [NumberField F] [IsTotallyReal F] in
theorem exists_g (hc : B1c) (z : X (InfinitePlace F)) : ∃ g : GL (Fin 2) (TR.Rinf F), (fun v => gv v g • iP) = z := by
  choose h _ _ hh using fun v => hc.2.2.2.2.2 (z v)
  exact ⟨asm h, funext fun v => by rw [gv_asm, hh]⟩

theorem inf_of (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    Matrix.GeneralLinearGroup.map (TR.pInf F) (TR.infGL F 2 g * finGL F 2 x) = g := by
  rw [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one]

theorem fin_of (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    Matrix.GeneralLinearGroup.map (pFin F) (TR.infGL F 2 g * finGL F 2 x) = x := by
  rw [map_mul, TR.pFin_infGL, pFin_finGL, one_mul]

end UpperTheory.Esk.HeckeRelationLemmas

open UpperTheory.Esk in
theorem UpperTheory.Esk.pf_HRel : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.HRel := by
  intro hb hc F _ _ _ k
  have hne : ∀ g : GL (Fin 2) (TR.Rinf F), ∏ v, j1 (k v) (gv v g) iP ≠ 0 :=
    fun g => Finset.prod_ne_zero_iff.2 fun v _ => hb.2.1 _ _ _
  refine ⟨fun f => ⟨fun a => f (fun v => gv v (Matrix.GeneralLinearGroup.map (TR.pInf F) a) • iP,
      Matrix.GeneralLinearGroup.map (pFin F) a) / ∏ v, j1 (k v) (gv v (Matrix.GeneralLinearGroup.map (TR.pInf F) a)) iP,
      fun g x => ?_⟩, fun f φ φ' h h' => ?_, fun f f' φ h h' => ?_, fun f f' φ φ' s h h' => ?_, fun g x => ?_,
      fun n a f φ h => ?_⟩
  · simp only [HeckeRelationLemmas.inf_of, HeckeRelationLemmas.fin_of]
    exact div_mul_cancel₀ _ (hne g)
  · funext a
    rw [← TR.infGL_mul_finGL a]
    exact mul_right_cancel₀ (hne _) ((h _ _).trans (h' _ _).symm)
  · funext p
    obtain ⟨z, x⟩ := p
    obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    rw [← h g x, ← h' g x]
  · intro g x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, h g x, h' g x]
  · simp
  · intro g x
    simp only [Dat.Op, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change φ.1 (TR.infGL F 2 g * finGL F 2 x * finGL F 2 (a i)) * _ = _
    rw [mul_assoc, ← map_mul, h g (x * a i)]
