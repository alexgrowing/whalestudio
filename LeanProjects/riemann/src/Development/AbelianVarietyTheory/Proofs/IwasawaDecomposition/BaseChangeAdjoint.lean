import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open scoped TensorProduct
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame

namespace GlobalTheory.RedForm

theorem bilin_skew_of_alt {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) (halt : ∀ x, B x x = 0)
    (x y : M) : B x y = - B y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)

theorem baseChange_adjoint {K M : Type} [CommRing K] [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)
    (f g : Module.End ℤ M) (h : ∀ x y, B x (f y) = B (g x) y) (x y : K ⊗[ℤ] M) :
    B.baseChange K x (f.baseChange K y) = B.baseChange K (g.baseChange K x) y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k' m' => simp [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]
    | add y1 y2 h1 h2 => simp only [map_add, h1, h2]
  | add x1 x2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]

theorem baseChange_nondeg {K M : Type} [CommRing K] [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (B : LinearMap.BilinForm ℤ M) (hskew : ∀ x y, B x y = - B y x) (hB : Function.Bijective B)
    (x : K ⊗[ℤ] M) (hx : ∀ y, B.baseChange K x y = 0) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ M
  let b' := Algebra.TensorProduct.basis K b
  choose c hc using fun j => hB.2 (b.coord j)
  have key : ∀ j, (B.baseChange K).flip (1 ⊗ₜ (-c j)) = b'.coord j := by
    intro j
    refine b'.ext fun i => ?_
    show B.baseChange K (b' i) (1 ⊗ₜ (-c j)) = b'.coord j (b' i)
    rw [Algebra.TensorProduct.basis_apply, LinearMap.BilinForm.baseChange_tmul,
      Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul, map_neg, hskew, neg_neg, hc, Module.Basis.coord_apply,
      b.repr_self, one_smul, one_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne' hij]
  refine b'.forall_coord_eq_zero_iff.1 fun j => ?_
  rw [← key j]
  exact hx _

theorem free_of_unimod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) :
    Module.Free ℤ Dw.La := by
  have := Dw.fin
  have : Module.Finite ℤ Dw.La := .trans (𝓞 E) _
  have : Module.IsTorsionFree ℤ Dw.La := by
    have : NoZeroSMulDivisors ℤ Dw.La := by
      refine ⟨fun {n x} h => or_iff_not_imp_left.2 fun hn => Dw.unimod.1 ?_⟩
      refine LinearMap.ext fun y => ?_
      have h1 : Dw.EF (n • x) y = n * Dw.EF x y := by simp
      rw [h, map_zero, LinearMap.zero_apply] at h1
      simpa [hn] using h1.symm
    infer_instance
  exact Module.free_of_finite_type_torsion_free'

theorem psiBar_props : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
  (∀ a : 𝓞 D.host.E, (A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ((A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) a) = a) ∧
  (∀ (a : 𝓞 D.host.E) (x y : ct.LaBar), ct.psiBar x ((baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a y) = ct.psiBar ((baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) ((A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) a) x) y) ∧
  (∀ x : ct.LaBar, (∀ y, ct.psiBar x y = 0) → x = 0) := by
  intro D A N j S κ p ct
  have hbb : ∀ a : 𝓞 D.host.E, A.H.bar (A.H.bar a) = a := fun a => by
    apply RingOfIntegers.ext
    rw [A.H.bar_eq, A.H.bar_eq, IsCMField.complexConj_apply_apply]
  have hskew := bilin_skew_of_alt S.Dw.EF S.Dw.alt
  refine ⟨fun a => hbb a, fun a x y => ?_, fun x hx => ?_⟩
  · rw [baseChangeAction_apply, baseChangeAction_apply]
    refine baseChange_adjoint S.Dw.EF _ _ (fun u v => ?_) x y
    simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, RingHom.coe_coe]
    rw [hskew, S.Dw.adj, hskew (A.H.bar a • u)]
  · have := free_of_unimod S.Dw
    have := S.Dw.fin
    have : Module.Finite ℤ S.Dw.La := .trans (𝓞 D.host.E) _
    exact baseChange_nondeg S.Dw.EF hskew S.Dw.unimod x hx

end GlobalTheory.RedForm
