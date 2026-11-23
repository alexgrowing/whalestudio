import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EchelonLowerTriangularOfIsUnitStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (tanPull initSpan initSpan_le_of_tri)

namespace GlobalTheory.FrameDescent

section Lin

variable {K N : Type} [Field K] [AddCommGroup N] [Module K N] {m : ℕ}

theorem sum_comb (P : Matrix (Fin m) (Fin m) K) (V : Fin m → N) (c : Fin m → K) :
    ∑ i, c i • ∑ j, P i j • V j = ∑ j, (Matrix.vecMul c P) j • V j := by
  simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem isUnit_of_comb {U V : Fin m → N} {P : Matrix (Fin m) (Fin m) K} (hU : LinearIndependent K U)
    (h : ∀ i, U i = ∑ j, P i j • V j) : IsUnit P := by
  rw [← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff]
  intro c hc
  refine Fintype.linearIndependent_iff.1 hU c ?_
  have h0 : Matrix.vecMul c P = 0 := by
    funext j
    have := congrFun hc j
    simpa [Finset.sum_apply, Matrix.vecMul, dotProduct] using this
  simp only [h, sum_comb, h0, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

theorem comb_frame {V : Fin m → N} {P : Matrix (Fin m) (Fin m) K} (hP : IsUnit P) (hV : LinearIndependent K V) :
    LinearIndependent K (fun i => ∑ j, P i j • V j) ∧
      Submodule.span K (Set.range fun i => ∑ j, P i j • V j) = Submodule.span K (Set.range V) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have back : ∀ k, V k = ∑ i, P⁻¹ k i • ∑ j, P i j • V j := by
    intro k
    rw [sum_comb]
    have e : Matrix.vecMul (P⁻¹ k) P = fun j => (1 : Matrix (Fin m) (Fin m) K) k j := by
      funext j
      rw [← hQP, Matrix.mul_apply]
      rfl
    rw [e]
    simp [Matrix.one_apply]
  refine ⟨Fintype.linearIndependent_iff.2 fun c hc => ?_, le_antisymm ?_ ?_⟩
  · rw [sum_comb] at hc
    have h0 := Fintype.linearIndependent_iff.1 hV _ hc
    have h1 : Matrix.vecMul c P = 0 := funext h0
    have h2 : c = Matrix.vecMul (Matrix.vecMul c P) P⁻¹ := by
      rw [Matrix.vecMul_vecMul, hPQ, Matrix.vecMul_one]
    intro i
    rw [h2, h1, Matrix.zero_vecMul]
    rfl
  · refine Submodule.span_le.2 (Set.range_subset_iff.2 fun i => ?_)
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · refine Submodule.span_le.2 (Set.range_subset_iff.2 fun k => ?_)
    rw [back k]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem vecs_bc_bc {X : Scheme.{0}} {t : SAB H X} {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S)
    (ψ : S →+* T) (u : Vecs Dw t R) : (u.bc φ).bc ψ = u.bc (ψ.comp φ) := by
  funext τ i
  rw [Vecs.bc, Vecs.bc, Vecs.bc, GlobalTheory.FlagMod.dualMap_comp, ← spMap_comp', Category.assoc]

theorem exists_frame_flag : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {c : Coeff l} {X : Scheme.{0}} (t : SAB H X) (ty : (E →+* ℂ) → Finset ℕ) {K' : Type} [Field K'] (L₀ : Subfield K')
    (f : c.F →+* L₀) (y₀ : Sp L₀ ⟶ X) (v : Vecs Dw t L₀) (u : Vecs Dw t K'),
    (∀ (R : Type) [Field R] (g : L₀ →+* R), IsFrame t (g.comp f) (spMap g ≫ y₀) (v.bc g)) →
    IsFrame t (L₀.subtype.comp f) (spMap L₀.subtype ≫ y₀) u →
    ∃ (L : Subfield K') (hL : L₀ ≤ L) (cf : Fin (∑ τ : E →+* ℂ, (Dw.mult τ).choose 2) → K'),
      L ≤ Subfield.closure ((L₀ : Set K') ∪ Set.range cf) ∧ ∃ uL : Vecs Dw t L,
        IsFrame t ((Subfield.inclusion hL).comp f) (spMap (Subfield.inclusion hL) ≫ y₀) uL ∧
        IsFrame t (L₀.subtype.comp f) (spMap L₀.subtype ≫ y₀) (uL.bc L.subtype) ∧
        SameFlag ty t (spMap L₀.subtype ≫ y₀) u (uL.bc L.subtype) := by
  intro E _ _ _ H Dw l c X t ty K' _ L₀ f y₀ v u hv hu
  classical
  have hv' := hv K' L₀.subtype
  obtain ⟨U, rfl⟩ := exists_up fun σ i => (hu.1 σ i).1
  obtain ⟨V, hV⟩ := exists_up fun σ i => (hv'.1 σ i).1
  rw [← hV] at hv'
  have hU := (isFrame_up_iff _ U).1 hu
  have hV' := (isFrame_up_iff _ V).1 hv'
  have hM : ∀ σ, ∃ P : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K', ∀ i, U σ i = ∑ j, P i j • V σ j := by
    intro σ
    have h : ∀ i, ∃ a : Fin (Dw.mult σ) → K', U σ i = ∑ j, a j • V σ j := fun i => by
      have : U σ i ∈ Submodule.span K' (Set.range (V σ)) := by
        rw [(hV' σ).2, ← (hU σ).2]
        exact Submodule.subset_span ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K').1 this
      exact ⟨a, ha.symm⟩
    choose a ha using h
    exact ⟨a, ha⟩
  choose M hMe using hM
  have hMu : ∀ σ, IsUnit (M σ) := fun σ => isUnit_of_comb (hU σ).1 (hMe σ)
  choose g s hg hgt hgs using fun σ => GlobalTheory.T.echelon_lower_triangular_of_isUnit (Dw.mult σ) (M σ) (hMu σ)
  let e : Fin (∑ τ : E →+* ℂ, (Dw.mult τ).choose 2) ≃ Σ τ : E →+* ℂ, Fin ((Dw.mult τ).choose 2) :=
    (Fintype.equivFinOfCardEq (by simp [Fintype.card_sigma])).symm
  let cf : Fin (∑ τ : E →+* ℂ, (Dw.mult τ).choose 2) → K' := fun k => s (e k).1 (e k).2
  let L := Subfield.closure ((L₀ : Set K') ∪ Set.range cf)
  have hL : L₀ ≤ L := fun x hx => Subfield.subset_closure (Or.inl hx)
  have hmem : ∀ σ i j, (g σ * M σ) i j ∈ L := fun σ i j => by
    rcases hgs σ i j with h | h | ⟨k, h⟩
    · rw [h]; exact L.zero_mem
    · rw [h]; exact L.one_mem
    · rw [← h]
      refine Subfield.subset_closure (Or.inr ⟨e.symm ⟨σ, k⟩, ?_⟩)
      show s (e (e.symm ⟨σ, k⟩)).1 (e (e.symm ⟨σ, k⟩)).2 = s σ k
      rw [Equiv.apply_symm_apply]
  let NL : ∀ σ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L := fun σ i j => ⟨_, hmem σ i j⟩
  have hNLu : ∀ σ, IsUnit (NL σ) := fun σ => by
    have e0 : (NL σ).map L.subtype = g σ * M σ := by
      ext i j
      rfl
    have h1 : IsUnit ((NL σ).map L.subtype) := by
      rw [e0]
      exact (hg σ).mul (hMu σ)
    rw [Matrix.isUnit_iff_isUnit_det] at h1 ⊢
    have e1 : L.subtype (NL σ).det = ((NL σ).map L.subtype).det := RingHom.map_det _ _
    rw [← e1, isUnit_iff_ne_zero] at h1
    rw [isUnit_iff_ne_zero]
    intro h0
    exact h1 (by rw [h0, map_zero])
  have hvL := hv L (Subfield.inclusion hL)
  obtain ⟨VL, hVL⟩ := exists_up fun σ i => (hvL.1 σ i).1
  rw [← hVL] at hvL
  have hVL' := (isFrame_up_iff _ VL).1 hvL
  let WL : TVecs Dw t (spMap (Subfield.inclusion hL) ≫ y₀) := fun σ i => ∑ j, NL σ i j • VL σ j
  have hWL : IsFrame t ((Subfield.inclusion hL).comp f) (spMap (Subfield.inclusion hL) ≫ y₀) (up WL) := by
    refine (isFrame_up_iff _ WL).2 fun σ => ?_
    obtain ⟨h1, h2⟩ := comb_frame (hNLu σ) (hVL' σ).1
    exact ⟨h1, h2.trans (hVL' σ).2⟩
  have ex : spMap L.subtype ≫ spMap (Subfield.inclusion hL) ≫ y₀ = spMap L₀.subtype ≫ y₀ := by
    rw [← Category.assoc, spMap_comp']
    rfl
  have hWb : (up WL).bc L.subtype = up fun σ i => tanPull L.subtype ex (WL σ i) := (up_tanPull _ ex WL).symm
  refine ⟨L, hL, cf, le_rfl, up WL, hWL, ?_, ?_⟩
  · have h := GlobalTheory.LocM.isFrame_bc E H Dw l c X t _ _ _ L.subtype _ _ hWL
    rw [ex] at h
    exact h
  · have hTV : (fun σ j => tanPull L.subtype ex (VL σ j)) = V := up_injective (by
      rw [up_tanPull, hVL, vecs_bc_bc]
      exact hV.symm)
    rw [hWb, sameFlag_up_iff]
    intro σ k _
    refine initSpan_le_of_tri (B := (g σ).transpose) (hgt σ) (fun i => ?_) k
    have e2 : tanPull L.subtype ex (WL σ i) = ∑ j, (g σ * M σ) i j • V σ j := by
      simp only [WL, map_sum, map_smulₛₗ]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← congrFun (congrFun hTV σ) j]
      rfl
    rw [e2]
    simp only [Matrix.transpose_apply, hMe σ, sum_comb]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply]
    rfl

end GlobalTheory.FrameDescent
