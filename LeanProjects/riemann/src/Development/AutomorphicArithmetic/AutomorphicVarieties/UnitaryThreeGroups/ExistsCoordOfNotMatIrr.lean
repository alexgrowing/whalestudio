import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjugateStarMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MatGstar
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SingleMemOfDiagonal

open Matrix UpperTheory.V.U3

private theorem single_mem_of_diag {κ : Type} [Field κ] {m : ℕ} (d : Fin m → κ)
    (hd : Function.Injective d) (W : Submodule κ (Fin m → κ))
    (hW : ∀ v ∈ W, Matrix.diagonal d *ᵥ v ∈ W) (v : Fin m → κ) (hv : v ∈ W) (i : Fin m)
    (hi : v i ≠ 0) : (Pi.single i 1 : Fin m → κ) ∈ W :=
  _root_.UpperTheory.Reformulated.B.SingleMemOfDiagonal.single_mem_of_diag d hd W hW v hv i hi

private theorem exists_coord_of_not_matIrr {G κ : Type} [Group G] [Field κ] {m : ℕ}
    (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) κ) (d : Fin m → κ)
    (hd : Function.Injective d) (g₁ g₂ : G) (h₁ : g₁ ∈ H) (h₂ : g₂ ∈ H)
    (hD : a g₁ - a g₂ = Matrix.diagonal d) (h : ¬ MatIrr H a) :
    ∃ S : Fin m → Prop, (∃ j, S j) ∧ (∃ i, ¬ S i) ∧
      ∀ i j, S j → ¬ S i → ∀ g ∈ H, a g i j = 0 := by
  classical
  unfold MatIrr at h
  push Not at h
  obtain ⟨W, hW, hb, ht⟩ := h
  have hWd : ∀ v ∈ W, Matrix.diagonal d *ᵥ v ∈ W := fun v hv => by
    rw [← hD, Matrix.sub_mulVec]
    exact W.sub_mem (hW _ h₁ _ hv) (hW _ h₂ _ hv)
  have hs := single_mem_of_diag d hd W hWd
  refine ⟨fun j => (Pi.single j 1 : Fin m → κ) ∈ W, ?_, ?_, ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    exact ⟨j, hs v hv j hj⟩
  · by_contra hc
    push Not at hc
    apply ht
    rw [eq_top_iff]
    intro v _
    rw [pi_eq_sum_univ' v]
    exact W.sum_mem fun i _ => W.smul_mem _ (hc i)
  · intro i j hj hi g hg
    by_contra hc
    apply hi
    refine hs _ (hW g hg _ hj) i ?_
    simpa using hc

theorem UpperTheory.V.U3.shape_cases :
    ∀ {G κ : Type} [Group G] [Field κ] (η : G →* ℤˣ) (r : G →* GG 3 κ) (c g₁ : G), (2 : κ) ≠ 0 → HasMult η r → η c = -1 → η g₁ = 1 →
      Normalised c g₁ r → zeta c g₁ r ≠ 0 → TypeI η r ∨ Upper η r ∨ Lower η r ∨ TypeII η r := by
  intro G κ _ _ η r c g₁ h2 hm hc hg hn hz
  have hc' : (r c).right = -1 := (hm c).trans hc
  have hD := zmat_diag r c g₁ h2.isUnit hc' ((hm g₁).trans hg) hn
  have hst : ∀ g ∈ η.ker, gstar c g ∈ η.ker := fun g hg =>
    (hm _).symm.trans (mat_gstar r c g hn.atc hc' ((hm g).trans hg)).2
  set ζ := zeta c g₁ r with hζ
  have hne : ζ ≠ -ζ := fun h => hz (by
    have : (2 : κ) * ζ = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2)
  let Z : Fin 3 → Fin 3 → Prop := fun i j => ∀ g ∈ η.ker, (r g).mat i j = 0
  have hsym : ∀ i j : Fin 3, Z i j → Z j.rev i.rev := by
    intro i j h g hg
    have h1 := h _ (hst g hg)
    rw [(mat_gstar r c g hn.atc hc' ((hm g).trans hg)).1] at h1
    revert h1
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  have s10 : Z 1 0 → Z 2 1 := hsym 1 0
  have s21 : Z 2 1 → Z 1 0 := hsym 2 1
  have s01 : Z 0 1 → Z 1 2 := hsym 0 1
  have s12 : Z 1 2 → Z 0 1 := hsym 1 2
  have hU : Z 1 0 → Z 2 0 → Upper η r := by
    intro h1 h2 g hg a b hab
    have := h1 g hg
    have := h2 g hg
    have := s10 h1 g hg
    fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)
  have hL : Z 0 1 → Z 0 2 → Lower η r := by
    intro h1 h2 g hg a b hab
    have := h1 g hg
    have := h2 g hg
    have := s01 h1 g hg
    fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)
  have hB : Z 0 1 → Z 1 0 → Upper η r ∨ Lower η r ∨ TypeII η r := by
    intro h1 h2
    by_cases hI : MatIrr η.ker fun g => corner (r g).mat
    · refine Or.inr (Or.inr ⟨?_, hI⟩)
      intro g hg a b hab
      have := h1 g hg
      have := h2 g hg
      have := s01 h1 g hg
      have := s10 h2 g hg
      fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)
    · have hinj : Function.Injective ![ζ, -ζ] := by
        intro i j h
        fin_cases i <;> fin_cases j <;> simp_all [hne.symm]
      obtain ⟨S, ⟨j, hj⟩, ⟨i, hi⟩, hS⟩ := exists_coord_of_not_matIrr η.ker _ ![ζ, -ζ] hinj g₁
        (gstar c g₁) hg (hst g₁ hg) (by
          ext i j
          have := congrFun (congrFun hD (![0, 2] i)) (![0, 2] j)
          refine Eq.trans this ?_
          fin_cases i <;> fin_cases j <;> simp) hI
      have h3 := hS i j hj hi
      fin_cases i <;> fin_cases j
      · exact absurd hj hi
      · exact Or.inr (Or.inl (hL h1 h3))
      · exact Or.inl (hU h2 h3)
      · exact absurd hj hi
  by_cases hI : TypeI η r
  · exact Or.inl hI
  right
  have hinj : Function.Injective ![ζ, 0, -ζ] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [hne.symm]
  obtain ⟨S, ⟨j, hj⟩, ⟨i, hi⟩, hS⟩ := exists_coord_of_not_matIrr η.ker (mats r) _ hinj g₁
    (gstar c g₁) hg (hst g₁ hg) hD hI
  have hS' : ∀ i j, S j → ¬ S i → Z i j := hS
  by_cases a0 : S 0 <;> by_cases a1 : S 1 <;> by_cases a2 : S 2
  · fin_cases i <;> contradiction
  · exact Or.inl (hU (s21 (hS' _ _ a1 a2)) (hS' _ _ a0 a2))
  · exact hB (s12 (hS' _ _ a2 a1)) (hS' _ _ a0 a1)
  · exact Or.inl (hU (hS' _ _ a0 a1) (hS' _ _ a0 a2))
  · exact Or.inr (Or.inl (hL (hS' _ _ a1 a0) (hS' _ _ a2 a0)))
  · exact hB (hS' _ _ a1 a0) (s21 (hS' _ _ a1 a2))
  · exact Or.inr (Or.inl (hL (s12 (hS' _ _ a2 a1)) (hS' _ _ a2 a0)))
  · fin_cases j <;> contradiction
