import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.LocTest

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem flipOrder_nodup (m : ℕ) : (flipOrder m).Nodup ∧ ∀ i j, (i, j) ∈ flipOrder m ↔ i < m ∧ j < m :=
  ⟨List.Nodup.product (List.nodup_range (n := m)) (List.nodup_range (n := m)), fun i j => by simp [flipOrder]⟩

example : Module.Free (AF D.host.F) (AE D) ∧ Module.Finite (AF D.host.F) (AE D) := ⟨inferInstance, inferInstance⟩

theorem moveArgs_one_transpose {k : Type*} [Field k] (Γ : Grid k) (g : Γ.VertexGroup) (x : Γ.Args) (b : Edge) :
    (Γ.moveArgs .one g x b)ᵀ = ((g b.src)⁻¹).val * (x b)ᵀ * (g b.tgt).val := by
  simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val, transpose_mul, transpose_transpose, Matrix.mul_assoc]

theorem stepFn_twist (t : T) (w : Pl D.host.E) (h1 : w ∉ L.Pg) (h2 : w ∈ L.Q t) (j : ℕ)
    {g : GL (Fin D.R.r) (Kw w)} (hg : g ∈ KO (Kw w) _) :
    stepFn L t w j (fromBlocks g.val 0 0 0) = ((L.xiH t).loc w (GeneralLinearGroup.det g) : ℂˣ) := by
  rw [stepFn, if_neg h1, if_pos h2, parPhi_fromBlocks _ hg rfl maxM_zero intM_zero intM_zero]
  simp

theorem hasTypes_twist (G : GridData L sc) (t : T) (w : Pl D.host.E) (h1 : w ∉ L.Pg) (h2 : w ∈ L.Q t) (j : ℕ)
    (hξ : IsTame ((L.xiH t).loc w)⁻¹) (hμ : IsUnram ((muBase L (j + 1)).loc w)⁻¹) :
    HasTypes ((locGrid G t w).mu (j + 1))⁻¹ (parahoric _ _ _ hξ).toLevel (parahoric _ _ _ hξ).toLevel (stepFn L t w j) := by
  have e : ((locGrid G t w).mu (j + 1))⁻¹ = ((muBase L (j + 1)).loc w)⁻¹ * ((L.xiH t).loc w)⁻¹ := by
    rw [← mul_inv]; rfl
  rw [e, stepFn, if_neg h1, if_pos h2]
  exact hasTypes_parPhi hξ hμ

theorem stepGroup_twist (t : T) (w : Pl D.host.E) (h1 : w ∉ L.Pg) (h2 : w ∈ L.Q t) (j : ℕ)
    (hξ : IsTame ((L.xiH t).loc w)⁻¹) : stepGroup L t w j = (parahoric _ _ _ hξ).J := by
  rw [stepGroup, if_neg h1, if_pos h2]; rfl

theorem intM_of_stepFn (t : T) (w : Pl D.host.E) (j : ℕ) {x} (h : stepFn L t w j x ≠ 0) : IntM x := by
  unfold stepFn at h
  split_ifs at h
  · intro i l
    simpa using TypeDatum.intM_of_Phi_ne_zero _ _ h ((ixSucc _ _ j).symm i) l
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff _).1 h
    rintro (i | i) (l | l)
    · have := intM_of_mem_KO hg i l
      rwa [e] at this
    · exact h12 i l
    · exact (h21 i l).le
    · exact h22 i l
  · by_contra hx
    exact h (Set.indicator_of_notMem (s := {x | IntM x}) hx _)

theorem givenStage_not_const {G : GridData L sc} (t : T) (w : Pl D.host.E) (B : Frames G) (Φ : G.Datum) :
    (∃ x, (givenStage t w B Φ).tensor x = 1) ∧ ∃ x, (givenStage t w B Φ).tensor x = 0 := by
  refine ⟨exists_givenStage_eq_one t w B Φ, fun _ => Matrix.of fun _ _ => ((unifAt w)⁻¹ : (Kw w)ˣ), ?_⟩
  have hm := D.R.two_le_m
  refine List.prod_eq_zero (List.mem_map.2 ⟨.theta 0 0, by simp [givenPath]; omega, ?_⟩)
  by_contra h
  have hr : 0 < D.R.r := (odd_r D).pos
  have h1 := intM_of_stepFn t w 0 h (.inl ⟨0, hr⟩) (.inl ⟨0, hr⟩)
  have h2 : valuation (Kw w) ((unifAt w : (Kw w)ˣ) : Kw w) < 1 := (isUnif_unifAt w) ▸ uniformizer_lt_one
  have h3 : valuation (Kw w) (((unifAt w)⁻¹ : (Kw w)ˣ) : Kw w) ≤ 1 := h1
  have h4 := mul_lt_one_of_lt_of_le h2 h3
  rw [← map_mul, Units.mul_inv, map_one] at h4
  exact lt_irrefl _ h4

theorem flips_eq_zero {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (l : List (ℕ × ℕ)) (S : Γ.PiLocalization₂)
    (i j : ℕ) (x : Γ.Args) (hx : x (.theta (i + 1) j) ∉ matLat _ (stdLat k _)) :
    (S.flips .one ψ ϖ e (l ++ [(i, j)])).tensor x = 0 := by
  rw [Grid.PiLocalization₂.flips, List.foldl_append]
  change invFourierSum _ _ _ _ _ _ = 0
  rw [invFourierSum_apply, if_neg]
  intro h
  refine hx (mem_matLat_stdLat.2 fun a b => ?_)
  exact h b (.inr a) (by simp [Assignment.block])

theorem Tflip_eq_zero {G : GridData L sc} (W : G.Weil) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E) {n : ℕ}
    (hn : D.R.m = n + 1) (x : (locGrid G t w).Args) (hx : x (.theta (n + 1) n) ∉ matLat _ (stdLat (Kw w) _)) :
    Tflip W B t Φ w x = 0 := by
  have e : ∃ l, flipOrder D.R.m = l ++ [(n, n)] := by
    rw [hn, flipOrder, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_append, ← List.append_assoc]
    exact ⟨_, rfl⟩
  obtain ⟨l, e⟩ := e
  rw [Tflip, flipStage, e]
  exact flips_eq_zero _ _ _ _ _ _ _ _ hx

theorem edgeFactor_theta {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : Grid k) (hη : IsUnram Γ.eta) (g : Γ.VertexGroup) (hg : ∀ X, g X ∈ KO k _) (i j : ℕ)
    (Φ : Matrix (Fin (Γ.rank (i, j + 1))) (Fin (Γ.rank (i, j))) k → ℂ) (x : Γ.Args) :
    Γ.edgeFactor .one g (.theta i j) * Φ (Γ.moveArgs .one g x (.theta i j))ᵀ =
      om (Γ.mu (j + 1))⁻¹ (g (i, j)) (g (i, j + 1)) Φ (x (.theta i j))ᵀ := by
  have h1 : ∀ X, Γ.eta (gdet (g X)) = 1 := fun X => hη _ (valuation_gdet_of_mem_KO (hg X))
  rw [om_of_mem_KO _ (hg _) (hg _), moveArgs_one_transpose]
  simp only [Grid.edgeFactor, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO (hg _)))]
  have h2 : ∀ X, Γ.kappa (.theta i j) X (gdet (g X)) = Γ.mu (j + 1) (gdet (g X)) := fun X => by
    simp [Grid.kappa, Grid.blockChar, h1]
  rw [h2, h2, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv, mul_one, mul_one, mul_comm (Γ.mu _ _ : ℂ)]

end GlobalTheory.FunObj.LocTest

end
