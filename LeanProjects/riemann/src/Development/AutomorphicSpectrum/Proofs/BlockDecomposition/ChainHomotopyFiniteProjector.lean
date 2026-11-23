import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open AlgebraicTopology AlgebraicTopology.DoldKan Simplicial

namespace GlobalTheory.CompanionTheory.NerveNorm

section Cos

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def cosMap {x y : SimplexCategory} (θ : x ⟶ y) : Cn F x.len →ₗ[R] Cn F y.len where
  toFun f c := mp F (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last x.len)))))
    (f (θ.toOrderHom.monotone.functor ⋙ c))
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ map_smul _ _ _

theorem cosMap_apply {x y : SimplexCategory} (θ : x ⟶ y) (f : Cn F x.len) (c : Fin (y.len + 1) ⥤ C) :
    cosMap F θ f c = mp F (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last x.len)))))
      (f (θ.toOrderHom.monotone.functor ⋙ c)) := rfl

def cosK : SimplexCategory ⥤ ModuleCat.{0} R where
  obj x := ModuleCat.of R (Cn F x.len)
  map θ := ModuleCat.ofHom (cosMap F θ)
  map_id x := by
    ext f c
    have h : c.map (homOfLE (Fin.le_last ((𝟙 x : x ⟶ x).toOrderHom (Fin.last x.len)))) = 𝟙 _ :=
      (congrArg c.map (Subsingleton.elim _ _)).trans (c.map_id _)
    exact (congrArg (fun φ ↦ mp F φ (f c)) h).trans (mp_id F _ _)
  map_comp {x y z} θ ψ := by
    ext f c
    have h : c.map (homOfLE (Fin.le_last ((θ ≫ ψ).toOrderHom (Fin.last x.len)))) =
        c.map (homOfLE (ψ.toOrderHom.monotone (Fin.le_last (θ.toOrderHom (Fin.last x.len))))) ≫
          c.map (homOfLE (Fin.le_last (ψ.toOrderHom (Fin.last y.len)))) :=
      (congrArg c.map (Subsingleton.elim _ _)).trans (c.map_comp _ _)
    exact (congrArg (fun φ ↦ mp F φ (f ((θ ≫ ψ).toOrderHom.monotone.functor ⋙ c))) h).trans
      (mp_comp F _ _ _)

theorem cosK_map_δ (n : ℕ) (i : Fin (n + 2)) :
    ((cosK F).map (SimplexCategory.δ i)).hom = cof F n i := rfl

end Cos

section Norm

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev simpX : SimplicialObject (ModuleCat.{0} R)ᵒᵖ := (cosK F).op

def eN (n : ℕ) : Cn F n →ₗ[R] Cn F n := ((PInfty (X := simpX F)).f n).unop.hom

def hN (n : ℕ) : Cn F (n + 1) →ₗ[R] Cn F n := ((homotopyPInftyToId (simpX F)).hom n (n + 1)).unop.hom

theorem d_unop (n : ℕ) :
    ((AlternatingFaceMapComplex.obj (simpX F)).d (n + 1) n).unop.hom = dn F n := by
  rw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [unop_sum, unop_zsmul, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  unfold dn
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul R]
  push_cast
  rw [← cosK_map_δ F n i]
  rfl

theorem eN_idem (n : ℕ) : eN F n ∘ₗ eN F n = eN F n := by
  exact congrArg (fun f => f.unop.hom) (PInfty_f_idem (X := simpX F) n)

theorem eN_comm (n : ℕ) : eN F (n + 1) ∘ₗ dn F n = dn F n ∘ₗ eN F n := by
  have h := congrArg (fun f => f.unop.hom) ((PInfty (X := simpX F)).comm (n + 1) n)
  rw [← d_unop]
  exact h

theorem eN_zero : eN F 0 = LinearMap.id + hN F 0 ∘ₗ dn F 0 := by
  have h := (homotopyPInftyToId (simpX F)).comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
  have key : eN F 0 = hN F 0 ∘ₗ dn F 0 + LinearMap.id := by
    rw [← d_unop]
    exact congrArg (fun f => f.unop.hom) h
  exact key.trans (add_comm _ _)

theorem eN_succ (n : ℕ) :
    eN F (n + 1) = LinearMap.id + dn F n ∘ₗ hN F n + hN F (n + 1) ∘ₗ dn F (n + 1) := by
  have h := (homotopyPInftyToId (simpX F)).comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have key : eN F (n + 1) = dn F n ∘ₗ hN F n + hN F (n + 1) ∘ₗ dn F (n + 1) + LinearMap.id := by
    rw [← d_unop, ← d_unop]
    exact congrArg (fun f => f.unop.hom) h
  rw [key]
  abel

theorem cosMap_σ_eN (n : ℕ) (i : Fin (n + 1)) :
    cosMap F (SimplexCategory.σ i) ∘ₗ eN F (n + 1) = 0 := by
  unfold eN
  change ((simpX F).σ i ≫ (PInfty (X := simpX F)).f (n + 1)).unop.hom = 0
  rw [σ_comp_PInfty]
  rfl

end Norm

section Vanish

variable {R : Type} [CommRing R] {P : Type} [PartialOrder P]

theorem exists_stutter [Finite P] (n : ℕ) (hn : Nat.card P < n + 1) (c : Fin (n + 2) ⥤ Pᵒᵖ) :
    ∃ i : Fin (n + 1), c.obj i.castSucc = c.obj i.succ := by
  by_contra hne
  simp only [not_exists] at hne
  have hanti : StrictAnti fun k : Fin (n + 2) => (c.obj k).unop := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have hle : (c.obj i.succ).unop ≤ (c.obj i.castSucc).unop :=
      leOfHom (c.map (homOfLE (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le)).unop
    exact lt_of_le_of_ne hle fun heq => hne i (Opposite.unop_injective heq).symm
  haveI := Fintype.ofFinite P
  have hcard := Fintype.card_le_of_injective _ hanti.injective
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at hcard
  omega

theorem zero_of_degenerate (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) {m : ℕ} (g : Cn F m) {c₁ c₂ : Fin (m + 1) ⥤ Pᵒᵖ}
    (h : c₁ = c₂) {T : Pᵒᵖ} (φ : c₁.obj (Fin.last m) ⟶ T) (hT : c₂.obj (Fin.last m) = T)
    (h0 : mp F φ (g c₁) = 0) : g c₂ = 0 := by
  subst h
  subst hT
  have hφ : φ = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hφ, mp_id] at h0
  exact h0

theorem eN_vanish [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (n : ℕ) (hn : Nat.card P < n + 1) :
    eN F (n + 1) = 0 := by
  refine LinearMap.ext fun f => funext fun c => ?_
  show eN F (n + 1) f c = 0
  obtain ⟨i, hi⟩ := exists_stutter n hn c
  have h0 := congrFun (LinearMap.congr_fun (cosMap_σ_eN F n i) f)
    ((SimplexCategory.δ i.castSucc).toOrderHom.monotone.functor ⋙ c)
  rw [LinearMap.comp_apply, cosMap_apply, LinearMap.zero_apply, Pi.zero_apply] at h0
  have hlast : (SimplexCategory.δ i.castSucc).toOrderHom (Fin.last n) = Fin.last (n + 1) := by
    show i.castSucc.succAbove (Fin.last n) = Fin.last (n + 1)
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))]
    exact Fin.succ_last n
  have hfun : (SimplexCategory.σ i).toOrderHom.monotone.functor ⋙
      ((SimplexCategory.δ i.castSucc).toOrderHom.monotone.functor ⋙ c) = c := by
    fapply CategoryTheory.Functor.ext
    · intro k
      show c.obj (i.castSucc.succAbove (i.predAbove k)) = c.obj k
      by_cases hk : k = i.castSucc
      · subst hk
        rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
        exact hi.symm
      · rw [Fin.succAbove_predAbove hk]
    · intro _ _ _
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  exact zero_of_degenerate F (eN F (n + 1) f) hfun _ (congrArg c.obj hlast.symm) h0

end Vanish

theorem exists_normalisation {R : Type} [CommRing R] (P : Type) [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) :
    ∃ (e : ∀ n, Cn F n →ₗ[R] Cn F n) (h : ∀ n, Cn F (n + 1) →ₗ[R] Cn F n) (B : ℕ),
      (∀ n, e n ∘ₗ e n = e n) ∧ (∀ n, e (n + 1) ∘ₗ dn F n = dn F n ∘ₗ e n) ∧
      e 0 = LinearMap.id + h 0 ∘ₗ dn F 0 ∧
      (∀ n, e (n + 1) = LinearMap.id + dn F n ∘ₗ h n + h (n + 1) ∘ₗ dn F (n + 1)) ∧
      ∀ n, B < n → e n = 0 := by
  refine ⟨eN F, hN F, Nat.card P, eN_idem F, eN_comm F, eN_zero F, eN_succ F, fun n hn => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_lt_zero _)
  | succ m => exact eN_vanish F m hn

end GlobalTheory.CompanionTheory.NerveNorm
