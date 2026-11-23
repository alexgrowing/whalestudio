import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD
open GroundTheory.Automorphic.Whittaker

theorem UpperTheory.Gal.LocD.cellStep :
    StabSub → CellStep := by
  intro hSt X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hsτ χ hχL D hD hsum U C x₀ hU hC hUC hHU hsU hsx₀ hvan f hf
  obtain ⟨L, hLo, hL1⟩ := hχL
  obtain ⟨L₀, hL₀c, hL₀o, hL₀L, hL₀τ⟩ := hSt H τ p hp hτ hτp L hLo
  have hχL₀ : ∀ l ∈ L₀, χ l = 1 := fun l hl => hL1 l (hL₀L hl)
  have hsp' : ∀ y, s^[p - 1 + 1] y = y := fun y => by rw [Nat.sub_add_cancel hp]; exact hsp y
  have toCc : ∀ g ∈ supportedIn U, g ∈ Cc X := by
    intro g hg
    obtain ⟨h1, -⟩ := hg
    exact h1
  let e : X ≃ₜ X :=
    { toFun := s
      invFun := s^[p - 1]
      left_inv := fun y => by
        show s^[p - 1] (s y) = y
        rw [← Function.iterate_succ_apply s (p - 1) y]
        exact hsp' y
      right_inv := fun y => by
        show s (s^[p - 1] y) = y
        rw [← Function.iterate_succ_apply' s (p - 1) y]
        exact hsp' y
      continuous_toFun := hs
      continuous_invFun := hs.iterate (p - 1) }
  have hcomp : ∀ g ∈ supportedIn U, g ∘ s ∈ supportedIn U := by
    intro g hg
    obtain ⟨hg1, hsupp⟩ := hg
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hg1
    obtain ⟨hlc, hcs⟩ := hg1
    refine ⟨GroundTheory.Automorphic.mem_locallyConstantCompactSupport.2
      ⟨hlc.comp_continuous hs, hcs.comp_homeomorph e⟩, ?_⟩
    intro x hx
    exact (hsU x).1 (hsupp hx)
  have hiter : ∀ i, ∀ g ∈ supportedIn U, g ∘ s^[i] ∈ supportedIn U := by
    intro i
    induction i with
    | zero =>
      intro g hg
      exact hg
    | succ i ih =>
      intro g hg
      exact hcomp _ (ih g hg)
  obtain ⟨f₀, hf₀U, hf₀eq⟩ :=
    exists_lift_orbit_piece hU hC hUC hL₀c hL₀o (y := x₀) (mem_orbit_self x₀)
  have hs_orb : ∀ y ∈ orbit H x₀, s y ∈ orbit H x₀ := by
    rintro _ ⟨h, rfl⟩
    exact ⟨τ h, by
      show τ h • x₀ = s (h • x₀)
      rw [hsτ, hsx₀]⟩
  have hs_piece : ∀ z ∈ orbitPiece L₀ x₀, s z ∈ orbitPiece L₀ x₀ := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨τ l, (hL₀τ l).2 hl, by
      show τ l • x₀ = s (l • x₀)
      rw [hsτ, hsx₀]⟩
  have hpiece_iter : ∀ n, ∀ z ∈ orbitPiece L₀ x₀, s^[n] z ∈ orbitPiece L₀ x₀ := by
    intro n
    induction n with
    | zero =>
      intro z hz
      exact hz
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      exact hs_piece _ (ih z hz)
  have hs_piece_iff : ∀ z, s z ∈ orbitPiece L₀ x₀ ↔ z ∈ orbitPiece L₀ x₀ := by
    intro z
    refine ⟨fun hz => ?_, hs_piece z⟩
    have h1 := hpiece_iter (p - 1) _ hz
    rw [← Function.iterate_succ_apply s (p - 1) z, hsp'] at h1
    exact h1
  have hf₀s : ∀ x ∈ orbit H x₀, f₀ (s x) = f₀ x := by
    intro x hx
    rw [hf₀eq _ (hs_orb x hx), hf₀eq x hx]
    by_cases hz : x ∈ orbitPiece L₀ x₀
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hs_piece_iff x).2 hz)]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((hs_piece_iff x).1 h))]
  have hf₀i : ∀ i, ∀ x ∈ orbit H x₀, f₀ (s^[i] x) = f₀ x := by
    intro i
    induction i with
    | zero =>
      intro x _
      rfl
    | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply, ih _ (hs_orb x hx)]
      exact hf₀s x hx
  have hDi : ∀ i, D (f₀ ∘ s^[i]) = D f₀ := by
    intro i
    have hm := sub_mem_of_eqOn_orbit hUC (hiter i f₀ hf₀U) hf₀U (fun x hx => hf₀i i x hx)
    have h0 := hvan _ hm
    rwa [map_sub, sub_eq_zero] at h0
  have hD0 : D f₀ = 0 := by
    have h0 := hsum f₀ (toCc f₀ hf₀U)
    simp only [hDi, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr hp.ne')
    · exact h
  let W : Submodule ℂ (X → ℂ) := supportedIn U ⊓ LinearMap.ker D
  have hrel : relSpan χ U ≤ W := by
    refine le_inf (relSpan_le_supportedIn χ hHU) (Submodule.span_le.mpr ?_)
    rintro g ⟨h, f', hf'U, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
    rw [hD h f' (toCc f' hf'U)]
    ring
  have hmem : f₀ ∈ W ⊔ supportedIn U ⊓ vanishingOn C :=
    Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hf₀U, LinearMap.mem_ker.mpr hD0⟩)
  have hle := supportedIn_le_of_base hU hC hUC hHU χ (W := W) inf_le_left hrel L₀ hL₀c hL₀o
    hχL₀ f₀ hf₀eq hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hle hf)
  rw [map_add, LinearMap.mem_ker.mp (Submodule.mem_inf.mp ha).2, hvan b hb, add_zero]
