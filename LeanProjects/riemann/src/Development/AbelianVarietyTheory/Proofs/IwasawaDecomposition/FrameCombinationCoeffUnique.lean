import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.Proof.frame_combination_coeff_unique

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem pairwise_letters (Dw : Datum H) :
    (letters Dw).Pairwise fun x y : GlobalTheory.ShFam.Pad.Letter Dw => x.1 = y.1 → (x.2 : ℕ) < y.2 := by
  refine List.pairwise_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_finRange _).imp ?_
    exact fun h _ => h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hx y hy h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
    exact absurd ((Fintype.equivFin (E →+* ℂ)).symm.injective h) hab

theorem get_bijective (Dw : Datum H) : Function.Bijective (letters Dw).get :=
  ⟨List.nodup_iff_injective_get.1 (LetterConjugation.nodup_letters Dw), fun x => List.get_of_mem (LetterConjugation.mem_letters Dw x)⟩

variable {X : Scheme.{0}} {t : SAB H X} {k : Type} [CommRing k] {x : Sp k ⟶ X}

theorem comb_iff {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (u i)).left) a w ↔ w = (tv (∑ i, a i • u i)).left := by
  have h0 := (GlobalTheory.LieMet.isComb_iff u a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨q, hq, hq'⟩ := h0
  obtain rfl : p = q := funext fun i => Over.OverMorphism.ext ((hp i).trans (hq i).symm)
  exact hq'

end

theorem concat_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (f : c.F →+* k) (x : Sp k ⟶ X) (u : Vecs Dw t k), GlobalTheory.LocM.IsFrame t f x u → (∀ cf cf' w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf w → IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf' w → cf = cf') ∧ ∀ (j : Fin (letters Dw).length) (cf : Fin (Dw.mult ((letters Dw).get j).1) → k) w, (∀ m, ((letters Dw).get j).2 < m → cf m = 0) → IsCombAtG t x (u ((letters Dw).get j).1) cf w → ∃ cg : Fin (letters Dw).length → k, (∀ m, j < m → cg m = 0) ∧ cg j = cf ((letters Dw).get j).2 ∧ IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cg w := by
  intro E _ _ _ H Dw l c X t k _ f x u hu
  classical
  let _ : Algebra c.F k := f.toAlgebra
  let U : (y : GlobalTheory.ShFam.Pad.Letter Dw) → TanM x t.G := fun y => GlobalTheory.LieMet.tanOf (hu.1 y.1 y.2).1
  let e := Equiv.ofBijective _ (get_bijective Dw)
  have hc : ∀ cf w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
      cf w ↔ w = (tv (∑ y, cf (e.symm y) • U y)).left := fun cf w => by
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    exact comb_iff (fun i => U (e i)) cf w
  have hτ : ∀ τ cf w, IsCombAtG t x (u τ) cf w ↔ w = (tv (∑ i, cf i • U ⟨τ, i⟩)).left := fun τ cf w =>
    comb_iff (fun i => U ⟨τ, i⟩) cf w
  refine ⟨fun cf cf' w h h' => ?_, fun j cf w h0 h => ?_⟩
  · have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
    obtain ⟨α, hinj, -, -⟩ :=
      exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
    let ρ := actR (x0 := x) (S := k) t.act
    have hE : ∀ τ (v : TanM x t.G), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) v ↔ ∀ a : 𝓞 E,
        (tv v).left ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ (tv v).left := fun τ v =>
      forall_congr' fun a => ⟨fun h => congrArg (fun z => (tv z).left) h, fun h => GlobalTheory.LieMet.tan_ext h⟩
    have hS : ∀ τ (a : Fin (Dw.mult τ) → k), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) (∑ i, a i • U ⟨τ, i⟩) := fun τ a s => by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hE τ (U ⟨τ, i⟩)).2 (hu.1 τ i).2 s, smul_comm]
    have h1 := GlobalTheory.LieMet.tan_ext (((hc cf w).1 h).symm.trans ((hc cf' w).1 h'))
    rw [Fintype.sum_sigma, Fintype.sum_sigma] at h1
    funext i
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective i
    have h2 := congrArg (proj ρ (embK c) α τ) h1
    rw [proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _), proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _)] at h2
    have h3 := hu.2 τ _ (GlobalTheory.LieMet.isTan_tv _) ((hE τ _).1 (hS τ fun i => cf (e.symm ⟨τ, i⟩)))
    exact congrFun (h3.unique ((hτ τ _ _).2 rfl) ((hτ τ _ _).2 (congrArg (fun z => (tv z).left) h2))) i
  · let B : GlobalTheory.ShFam.Pad.Letter Dw → k := fun y => if h : y.1 = ((letters Dw).get j).1 then cf (h ▸ y.2) else 0
    refine ⟨fun m => B ((letters Dw).get m), fun m hm => ?_, by simp [B], ?_⟩
    · have hp := List.pairwise_iff_get.1 (pairwise_letters Dw) j m hm
      show B ((letters Dw).get m) = 0
      revert hp
      generalize (letters Dw).get m = y
      obtain ⟨τ, i⟩ := y
      intro hp
      by_cases hy : τ = ((letters Dw).get j).1
      · subst hy
        exact (dif_pos rfl).trans (h0 _ (hp rfl))
      · exact dif_neg hy
    · rw [hc, (hτ _ _ _).1 h]
      congr 2
      have : ∀ y, (letters Dw).get (e.symm y) = y := e.apply_symm_apply
      simp only [this]
      rw [Fintype.sum_sigma, Finset.sum_eq_single ((letters Dw).get j).1]
      · exact Finset.sum_congr rfl fun i _ => by simp [B]
      · intro σ _ hσ
        exact Finset.sum_eq_zero fun i _ => by rw [show B ⟨σ, i⟩ = 0 from dif_neg hσ, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.Proof.frame_combination_coeff_unique
