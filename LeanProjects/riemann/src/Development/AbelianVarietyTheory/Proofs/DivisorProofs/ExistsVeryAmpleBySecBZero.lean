import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtPull

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.WeightZero

open GlobalTheory.ProjSpace GlobalTheory.AbLaw GlobalTheory.Cartier

theorem veryAmpleBy_of_sval {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Z ⟶ X)} {ε' : K' → ℤ}
    (g : Z ⟶ Y) [IsIso g] (f : Y ⟶ Sp R) {m : ℕ} (s : Fin (m + 1) → (LB.LinComb L φ ε).Sec)
    (t : Fin (m + 1) → (LB.LinComb L φ' ε').Sec)
    (h : ∀ i z J, Good L z J → sval (t i) (𝟙 Z) z J = sval (s i) g z J) (hs : VeryAmpleBy f _ s) :
    VeryAmpleBy (g ≫ f) _ t := by
  obtain ⟨hc, hi⟩ := (veryAmpleBy_iff f s).1 hs
  have key : ∀ z : Z, ∃ (W : Z.Opens) (_ : z ∈ W) (k : (LB.LinComb L φ ε).ι)
      (hk : W ≤ g ⁻¹ᵁ (LB.LinComb L φ ε).U k) (l : (LB.LinComb L φ' ε').ι) (hl : W ≤ (LB.LinComb L φ' ε').U l),
      ∀ j, resG Z hl ((t j).f l) = (g.appLE _ W hk).hom ((s j).f k) := by
    intro z
    choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ z)
    refine ⟨LB.wchart L φ' (fun k => J (𝟙 Z ≫ φ' k)) ⊓ g ⁻¹ᵁ LB.wchart L φ (fun k => J (g ≫ φ k)),
      ⟨Good.mem hJ φ' (𝟙 Z), Good.mem hJ φ g⟩, fun k => J (g ≫ φ k), inf_le_right, fun k => J (𝟙 Z ≫ φ' k),
      inf_le_left, fun j => fn_ext fun y hy => ?_⟩
    obtain ⟨J', hJ', e⟩ := exists_good L hL y (Sum.elim (fun k => 𝟙 Z ≫ φ' k) (fun k => g ≫ φ k))
      (fun a => J (Sum.elim (fun k => 𝟙 Z ≫ φ' k) (fun k => g ≫ φ k) a)) (fun a b e => congrArg J e) (by
        rintro (a | a)
        exacts [Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a])
    have e₁ := h j y J' hJ'
    rw [sval_of (t j) _ y J' _ (fun k => e (.inl k)), sval_of (s j) _ y J' _ (fun k => e (.inr k))] at e₁
    refine (gs_res _ y _ hy _).trans (e₁.trans (Eq.symm ?_))
    exact (gs_res (𝟙 Z) y inf_le_right hy _).trans (gs_pull (𝟙 Z) g y _ hy.2 _)
  have ht : ⨆ i, nonzeroLocus (t i) = ⊤ := by
    refine _root_.top_le_iff.1 fun z _ => ?_
    obtain ⟨W, hz, k, hk, l, hl, e⟩ := key z
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (g z)))
    have h₁ : z ∈ Z.basicOpen (resG Z hl ((t i).f l)) := by
      rw [e i, Scheme.basicOpen_appLE]
      exact ⟨hz, (mem_nonzeroLocus_iff _ k (hk hz)).1 hi⟩
    rw [Scheme.basicOpen_res] at h₁
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, basicOpen_le_nonzeroLocus _ l h₁.2⟩
  refine (veryAmpleBy_iff _ t).2 ⟨ht, ?_⟩
  rw [toProj_eq_comp_of_locally hc g ht fun z => by
    obtain ⟨W, hz, k, hk, l, hl, e⟩ := key z
    exact ⟨W, hz, k, hk, l, hl, 1, fun j => (e j).trans (_root_.one_mul _).symm⟩]
  infer_instance

theorem formEq_weight_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) :
    FormEq (fun _ : Fin k => 𝟙 D.P.A.left) (fun _ => 1) (D.famφB 0) (DegPre.famε k) := by
  intro U _ h
  have h0 : D.c 0 = 1 := by
    have h : D.c 0 = D.c 0 * D.c 0 := by
      have := D.c_add 0 0
      rwa [add_zero] at this
    exact mul_eq_left.1 h.symm
  have h1 : toUnit D.P.A ≫ D.c 0 = 1 := by rw [h0, comp_one]
  have h2 : toUnit D.P.A ≫ η[D.P.A] = 1 := rfl
  have h3 : padd D.P.A (𝟙 D.P.A) (1 : D.P.A ⟶ D.P.A) = 𝟙 _ := _root_.mul_one (𝟙 D.P.A)
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφB, DegPre.famε, h1, h2, h3]
  simp [zpow_sub]

theorem exists_veryAmpleBy_secB_zero (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R) (k : ℕ)
    (hk : 4 ≤ k) : ∃ (m : ℕ) (s : Fin (m + 1) → D.SecB k 0), VeryAmpleBy D.P.A.hom _ s := by
  obtain ⟨m, s, H⟩ := (GlobalTheory.allSixLaws.1.ample (Sp R) D.P k hk).2 ⊤ (isAffineOpen_top _)
  have : IsIso (⊤ : (Sp R).Opens).ι := inferInstanceAs (IsIso (Sp R).topIso.hom)
  have : IsIso (D.P.A.hom ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso D.P.A.left.topIso.hom)
  have h' := (veryAmpleBy_comp_iff (D.P.A.hom ∣_ ⊤) (⊤ : (Sp R).Opens).ι s).2 H
  rw [morphismRestrict_ι] at h'
  let ψ := inv (D.P.A.hom ⁻¹ᵁ ⊤).ι
  have hψ : ψ ≫ (D.P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ := IsIso.inv_hom_id _
  choose s' hs' using fun i => exists_sec_pull (L := D.P.L) _ _ (s i) ψ (fun _ : Fin k => 𝟙 D.P.A.left) fun _ => hψ.symm
  choose t ht using fun i => exists_sec D.P.isLB (formEq_weight_zero D k) (s' i)
  have := veryAmpleBy_of_sval D.P.isLB ψ _ s t (fun i z J hJ => by
    refine (ht i _ _ z J hJ).trans ((hs' i _ z _ (hJ.mem _ _)).trans ?_)
    rw [Category.id_comp, sval_of (s i) ψ z J (fun _ => J (𝟙 _ ≫ 𝟙 _)) fun _ => by rw [hψ, Category.id_comp]]) h'
  rw [← Category.assoc, hψ, Category.id_comp] at this
  exact ⟨m, t, this⟩

end GlobalTheory.Mum.WeightZero
