import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.IndepBaseChange

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_contract {k E : Type} [Field k] [Field E] [Algebra k E] {A B : CommRingCat.{0}}
    {f : CommRingCat.of k ⟶ A} {p : A ⟶ B} {q : CommRingCat.of E ⟶ B}
    (po : IsPushout f (CommRingCat.ofHom (algebraMap k E)) p q) (l : E →ₗ[k] k) :
    ∃ Λ : B →+ A, ∀ (e : E) (a : A), Λ (q.hom e * p.hom a) = f.hom (l e) * a := by
  letI : Algebra k A := f.hom.toAlgebra
  have w := (CommRingCat.isPushout_tensorProduct k A E).w
  let d := po.desc _ _ w
  let m : A ⊗[k] E →ₗ[k] A := (TensorProduct.rid k A).toLinearMap ∘ₗ l.lTensor A
  refine ⟨m.toAddMonoidHom.comp d.hom.toAddMonoidHom, fun e a => ?_⟩
  have h₁ : d.hom (p.hom a) = a ⊗ₜ[k] (1 : E) := congrArg (fun g => g.hom a) (po.inl_desc _ _ w)
  have h₂ : d.hom (q.hom e) = (1 : A) ⊗ₜ[k] e := congrArg (fun g => g.hom e) (po.inr_desc _ _ w)
  change m (d.hom (q.hom e * p.hom a)) = _
  rw [map_mul, h₁, h₂, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  simp only [m, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul]
  rfl

theorem comb_f {k : Type} [Field k] (S : LinSys k) (u : Fin S.N → k) (i : S.L.ι) {W : S.Y.Opens}
    (h : W ≤ S.L.U i) : resG S.Y h ((S.comb u).f i) =
      ∑ j, ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top).hom (u j) *
        resG S.Y h ((S.b j).f i) := by
  let e : S.L.Sec →+ Γ(S.Y, W) :=
    { toFun := fun s => resG S.Y h (s.f i), map_zero' := map_zero _, map_add' := fun _ _ => map_add _ _ _ }
  refine (map_sum e _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  refine (map_mul (resG S.Y h) _ _).trans (congrArg (· * _) ?_)
  refine (LB.resG_resG _ _ _).trans ?_
  rfl

theorem indep_baseChange (k E : Type) [Field k] [Field E] [Algebra k E] (S : LinSys k) (hS : S.Indep) :
    (S.baseChange E).Indep := by
  intro u hu
  have key : ∀ l : E →ₗ[k] k, (fun j => l (u j)) = (0 : Fin S.N → k) := fun l => by
    refine hS _ (LB.f_injective (funext fun i => ?_))
    refine S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _
      (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_
    · obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy
      exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩
    obtain ⟨⟨W, hW⟩, hle⟩ := W
    have H := S.isPullback_baseChange E
    have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top
      (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)
    have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top)
        (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl)
        ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
          (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top) := by
      refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
        (by simp) ?_ (by simp) (by simp)
      rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    obtain ⟨Λ, hΛ⟩ := exists_contract po' l
    have hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i :=
      fun y hy => Set.mem_iInter.2 fun _ => hle hy
    have e := comb_f (S.baseChange E) u (fun _ => i) hle'
    rw [hu] at e
    have e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) =
        ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i)) := fun j => by
      have a := (S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i)
        (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op
      have b := (S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op
      exact congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)
    have e₂ := congrArg Λ e
    simp only [e', map_sum, hΛ] at e₂
    refine (comb_f S _ i hle).trans (e₂.symm.trans ?_)
    exact ((congrArg Λ (map_zero _)).trans (map_zero Λ)).trans (map_zero _).symm
  funext j
  exact (Module.forall_dual_apply_eq_zero_iff k (u j)).1 fun l => congrFun (key l) j

end GlobalTheory.Adelic.IndepBaseChange
