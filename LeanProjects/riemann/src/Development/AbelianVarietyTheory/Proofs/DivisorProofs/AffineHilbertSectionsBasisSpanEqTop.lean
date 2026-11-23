import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem span_gen_eq_top (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (functor A B r).obj (op Z))
    (W : Z.affineOpens) :
    Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)) = ⊤ := by
  have sq : IsPullback (pullback.fst (str A B) y.1) (pullback.snd (str A B) y.1) (str A B) y.1 :=
    IsPullback.of_hasPullback _ _
  haveI : IsAffineHom (pullback.snd (str A B) y.1) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback sq inferInstance
  have hpo := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance (isAffineOpen_top _) W.2
    (by simp) (by simp)
  have hQ : IsAffineOpen (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage _
  have hsurj := y.2.1.subschemeι_app_surjective ⟨_, hQ⟩
  let R := Γ(Spec (CommRingCat.of A), ⊤)
  let S := Γ(Spec (CommRingCat.of B), ⊤)
  let T := Γ(Z, (W : Z.Opens))
  let Q := Γ(pullback (str A B) y.1, pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))
  letI : Algebra R S := (show R ⟶ S from (str A B).app ⊤).hom.toAlgebra
  letI : Algebra R T := (y.1.appLE ⊤ W (by simp)).hom.toAlgebra
  letI : Algebra T Q := ((pullback.snd (str A B) y.1).app W).hom.toAlgebra
  letI : Algebra S Q :=
    (show S ⟶ Q from (pullback.fst (str A B) y.1).appLE (str A B ⁻¹ᵁ ⊤) _ (by simp)).hom.toAlgebra
  letI : Algebra R Q :=
    ((y.1.appLE ⊤ W (by simp)) ≫ (pullback.snd (str A B) y.1).app W).hom.toAlgebra
  haveI : IsScalarTower R T Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq (fun x => by
    have h := congr($(hpo.w).hom x)
    exact h.symm)
  haveI : Algebra.IsPushout R T S Q := (CommRingCat.isPushout_iff_isPushout).mp hpo.flip
  have hbc := Algebra.IsPushout.out (R := R) (S := T) (R' := S) (S' := Q)

  have key : ∀ s : S, (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom
      (algebraMap S Q s) = ((y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤
        (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp)).hom s := by
    intro s
    have h : (Scheme.Hom.appLE (pullback.fst (str A B) y.fst) (str A B ⁻¹ᵁ ⊤)
      (pullback.snd (str A B) y.fst ⁻¹ᵁ ↑W) (by simp)) ≫ y.2.1.subschemeι.app _ =
        (y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤
        (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    exact congrArg (fun f => (CommRingCat.Hom.hom f) s) h
  have hι : ∀ (t : T) (n : Q), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (t • n) =
      t • (show Sec A B y W from
        (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom n) := by
    intro t n
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
  have term : ∀ (c : A) (j : Fin N), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (algebraMap S Q
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c * e j))) =
      (algebraMap R T ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c)) • gen A B y W (e j) := by
    intro c j
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c) =
        algebraMap R S ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c) :=
      congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))).hom c)
    rw [map_mul, h1, map_mul, ← IsScalarTower.algebraMap_apply R S Q,
      IsScalarTower.algebraMap_apply R T Q, ← Algebra.smul_def, hι, key]
    rfl
  have hB : ∀ b : B, (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (algebraMap S Q ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b))) ∈
      Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)) := by
    intro b
    rw [← e.sum_repr b, map_sum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def, term]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨q, rfl⟩ := hsurj x
  refine hbc.inductionOn q (fun q => (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom q) ∈ Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)))
    ?_ ?_ ?_ ?_
  · convert zero_mem (Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)))
    exact map_zero _
  · intro s
    obtain ⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b = s :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s, by simp⟩
    exact hB b
  · intro t n hn
    rw [hι]
    exact Submodule.smul_mem _ _ hn
  · intro a b ha hb
    rw [map_add]
    exact add_mem ha hb

end GlobalTheory.HilbAff
