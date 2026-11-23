import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDoubleCosetOfSmallerLevelSameLocalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSublevelFiniteIndexMorePlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallerLevelHecke
open Formalism.IndefR.Lev Formalism.L2.NTheta GlobalTheory.SplitHeckeAdj

theorem local_group_two {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (L L' : LevDat D.host.E ℂ V.rank) (hβ : IsBaseFrame V β Λ 1)
    (P : Formalism.L2.DIV.Pl D.host.E) (e : Formalism.L2.Theta.AE D) (he : IsIdemAt e P)
    (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    (hoff' : ∀ PP, PP ∈ L'.Pg ∨ PP ∈ L'.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) :
    ∃ Lc : Subgroup (Bridge.Gf V), (∀ g, SuppAt e V g → fin V g ∈ Lc) ∧
      (∀ g, SuppAt e V g → fin V g⁻¹ ∈ Lc) ∧
      (∀ k ∈ (levEnv V β L).J, ∃ k₁ ∈ (levEnv V β L).J, ∃ k₂ ∈ (levEnv V β L).J,
        k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l) ∧
      (levEnv V β L).J ⊓ Lc ≤ (levEnv V β L').J := by
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have h01 := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ hP
  have hff := h01.1
  have hcf := h01.2.1
  have h02 := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hff hcf).1
  refine h02.elim fun L₀ hL₀ => ?_
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have h03 := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L) hβ).2 P e _ hP h1 hoff
  have hK' := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ 1 (flag1L L') hβ).2 P e _ hP h1 hoff').1
  have hK := h03.1
  have hχ := h03.2.1
  have hsp := h03.2.2
  have hL : ∀ g, g ∈ L₀ ↔ SuppAt e V g := hL₀
  have h04 := (GlobalTheory.T.involution_spherical_hecke_anti V P e he).1
  have h05 := transport_local (fin V) (GfC V) (levG V β (flag1L L)) L₀ (levEnv V β L).J (SuppAt e V)
    (SuppF V (1 - (e + cA D e))) (KsphC V ∅) (fun k => ((levEnv V β L).χ k : ℂ)) (levChi V β (flag1L L))
    (fin_lift V) (fun g g' => fin_inj V) (fun g => mem_J V β L) (fun g hg => hg.1) hL (fun g => supp_fin V he)
    (fun g g' => commute_compl V _ hff hcf) (fun g => chi_eq V β L) hK hχ hsp h04
  refine ⟨L₀.map (fin V), fun g hg => ⟨g, (hL g).2 hg, rfl⟩,
    fun g hg => ⟨g⁻¹, L₀.inv_mem ((hL g).2 hg), rfl⟩, h05.1, ?_⟩
  rintro _ ⟨hj, g, hg, rfl⟩
  have a := (hL g).1 hg
  have b := supp_fin V he a
  exact (mem_J V β L' b).2 ((hK' g a).2 ((hK g a).1 ((mem_J V β L b).1 hj)))

theorem isDC_smaller_level : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSDFrame V β Λ 1 → ∀ (L : LevDat D.host.E ℂ V.rank) (Q' : Finset (Pl D.host.E)) (xq : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), L.Q ⊆ Q' → ∀ (Pl0 : Type) (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ), (∀ PP, PP ∈ L.Pg ∨ PP ∈ Q' → PP ≠ pl i.1 ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i.1)) → i.2 ≤ V.rank → ∀ (x : Bridge.Gf V) (A : Finset (Bridge.Gf V)), isTEnv V pl ok i x → (∀ a ∈ A, isLocEnv V pl ok i a) → Bridge.IsDC (levEnv V β L).J x A → Bridge.IsDC (levEnv V β { L with Q := Q', xq := xq }).J x A := by
  intro D V β Λ hSD L Q' xq hQ Pl0 pl ok i hoff hi x A hx hA hDC
  have hle := (GlobalTheory.T.parahoricSublevel_finiteIndex_more_places D V β Λ hSD L Q' xq hQ).1
  obtain ⟨cc, hβ⟩ := hSD
  rw [one_pow] at hβ
  obtain ⟨α, ⟨e, ϖ, he, -, -, hα⟩, hxα⟩ := hx hi
  obtain ⟨Lc, l1, l2, l3, l4⟩ := local_group_two V β Λ L { L with Q := Q', xq := xq } hβ (pl i.1) e he
    (fun PP h => hoff PP (h.imp_right fun h' => hQ h')) hoff
  have e1 : x = fin V α⁻¹ := Subtype.ext hxα
  refine GlobalTheory.T.isDoubleCoset_of_smaller_level_same_local _ _ Lc x A hle l4 l3 ?_ (fun a ha => ?_) hDC
  · rw [e1]
    exact l2 α hα.2.1
  · obtain ⟨g, hg, rfl⟩ := loc_supp V (hA a ha) he
    exact l1 g hg

end GlobalTheory.SmallerLevelHecke
