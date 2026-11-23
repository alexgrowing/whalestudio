import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanExistsMarkedFormInCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormMemCellConeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdBalancedFormVanishesLowRankStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark GlobalTheory.CompanionTheory.Ar.Fan
open _root_.GlobalTheory.PolFan.Mark.Exist

namespace GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone

section Face

variable {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O} {q : ℕ}
  {ψ lab : InvFun O} {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]

theorem inFace_iff (hb : CMOrd O bar) (hψ : IsPolyFan bar q ψ) (hl : IsCarrierDim bar q ψ lab)
    (hX : Module.finrank O X ≤ q) (hD : Dominates bar X) {m : ℕ} {τ : Fin m → LinearMap.BilinForm ℤ X}
    (hτ : IsCell bar ψ τ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone τ β) (hr : (genRank τ : ℝ) ≤ lab.evalZ β)
    (x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab β x ↔ InRCone τ x := by
  have b1 := cone_bal hτ.mem hβ
  have b2 := cone_nonneg hτ.nonneg hβ
  constructor
  · rintro ⟨h1, h2, -, h4, h5⟩
    exact GlobalTheory.T.psd_balanced_form_mem_cell_cone O bar hb q ψ lab hψ hl X hX hD m τ hτ β b1 b2 hβ x h1 h2 h4 h5
  · intro hx
    have hs := cone_add hβ hx
    refine ⟨cone_bal hτ.mem hx, cone_nonneg hτ.nonneg hx, fun y hy => cone_vanish hx fun j =>
      GlobalTheory.T.psd_balanced_form_vanishes_low_rank O bar hb q ψ lab hψ hl X hX hD m τ hτ β b1 b2 hβ hr j y hy,
      evalZ_add_of_linearOn_inRCone _ ψ X m τ hτ.linear _ _ hβ hx, le_antisymm ((lab_le hl hX hτ hs).trans hr) ?_⟩
    obtain ⟨c, hc, e⟩ := hx
    refine carrierDim_le_of_add_cell _ bar q ψ lab hl X hX m τ hτ β b1 b2 _ (cone_bal hτ.mem hs)
      (cone_nonneg hτ.nonneg hs) hβ 1 c one_pos hc ?_
    rw [← e]
    exact LinearMap.ext₂ fun a b => by simp

theorem isIndec_iff (hb : CMOrd O bar) (hψ : IsPolyFan bar q ψ) (hl : IsCarrierDim bar q ψ lab)
    (hX : Module.finrank O X ≤ q) (hD : Dominates bar X) {m : ℕ} {τ : Fin m → LinearMap.BilinForm ℤ X}
    (hτ : IsCell bar ψ τ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone τ β) (hr : (genRank τ : ℝ) ≤ lab.evalZ β)
    (x : LinearMap.BilinForm ℤ X) :
    IsIndec bar ψ lab β x ↔
      InRCone τ x ∧ x ≠ 0 ∧ ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x := by
  simp only [IsIndec, inFace_iff hb hψ hl hX hD hτ hβ hr]

end Face

theorem exists_isMarked_inRCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ : LinearMap.BilinForm ℤ X, IsMarked bar ψ lab i X β₀ ∧ InRCone v β₀ := by
  intro O _ _ _ _ bar hbar q ψ lab i hDom hψ hl X _ _ _ _ hX m v hv β hb hp hvβ hlab
  classical
  have hD := hDom X
  have hfan := hψ X hX
  have : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, τ, hτ, hβ, hr⟩ := exists_min hl hX hv hvβ
  have hF := inFace_iff hbar hψ hl hX hD hτ hβ hr.le
  have hI := isIndec_iff hbar hψ hl hX hD hτ hβ hr.le
  have hβ0 : β ≠ 0 := by
    rintro rfl
    have h0 : ∀ j, τ j = 0 := fun j => eq_zero_of_diag (hτ.mem j).1 fun y =>
      GlobalTheory.T.psd_balanced_form_vanishes_low_rank O bar hbar q ψ lab hψ hl X hX hD n τ hτ 0 hb hp hβ hr.le j y rfl
    have h1 : Submodule.span ℤ (Set.range τ) = ⊥ := Submodule.span_eq_bot.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
    have h2 : genRank τ = 0 := by rw [genRank, h1, finrank_bot]
    rw [h2, hlab] at hr
    have : (0 : ℕ) = i + 1 := by exact_mod_cast hr
    omega
  have hfin := finite_indec_inRCone X n τ
  set S := hfin.toFinset with hSdef
  have hS : ∀ x, x ∈ S ↔ InRCone τ x ∧ x ≠ 0 ∧ ∀ y z, InRCone τ y → InRCone τ z → y ≠ 0 → z ≠ 0 → y + z ≠ x :=
    fun x => by simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hSτ : ∀ x ∈ S, InRCone τ x := fun x hx => ((hS x).1 hx).1
  have hcl : β ∈ AddSubmonoid.closure {y | IsIndec bar ψ lab β y} :=
    GlobalTheory.T.mem_closure_sum_indecomposable_face_of_additive _ bar ψ lab X β
      (fun x y hx hy => ⟨(hF _).2 (cone_add ((hF _).1 hx) ((hF _).1 hy)),
        evalZ_add_of_linearOn_inRCone _ ψ X n τ hτ.linear _ _ ((hF _).1 hx) ((hF _).1 hy)⟩)
      (fun x hx => hfan.integral x hx.1 hx.2.1) (fun x hx h0 => hfan.pos x hx.1 hx.2.1 h0) β ((hF _).2 hβ)
  have hadd := evalZ_sum hτ.linear S hSτ
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : {y | IsIndec bar ψ lab β y} = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
      have := (hS y).2 ((hI y).1 hy)
      rw [h] at this
      exact Finset.notMem_empty _ this
    rw [this, AddSubmonoid.closure_empty, AddSubmonoid.mem_bot] at hcl
    exact hβ0 hcl
  have hσ : ∑ x ∈ S, x ≠ 0 := fun h => by
    rw [h, evalZ_zero'] at hadd
    refine (Finset.sum_pos (fun x hx => ?_) hne).ne hadd
    exact hfan.pos x (cone_bal hτ.mem (hSτ x hx)) (cone_nonneg hτ.nonneg (hSτ x hx)) ((hS x).1 hx).2.1
  obtain ⟨g, β₀, hg, hgβ, hprim⟩ := GlobalTheory.bilinForm_exists_primitive_of_ne_zero X _ hσ
  have hτ0 : InRCone τ β₀ := (cone_smul_iff hg).1 (hgβ ▸ cone_sum hSτ)
  have hge : lab.evalZ β ≤ lab.evalZ β₀ := by
    obtain ⟨k, γ, hγ, hγ0, hrγ⟩ := exists_min hl hX hτ hτ0
    have hσγ : InRCone γ (∑ x ∈ S, x) := hgβ ▸ (cone_smul_iff hg).2 hγ0
    let u : Fin S.card → LinearMap.BilinForm ℤ X := fun j => (S.equivFin.symm j : LinearMap.BilinForm ℤ X)
    have hu : ∀ {M : Type} [AddCommMonoid M] (f : LinearMap.BilinForm ℤ X → M), ∑ j, f (u j) = ∑ x ∈ S, f x :=
      fun f => by
        rw [← Finset.sum_coe_sort S f]
        exact S.equivFin.symm.sum_comp fun x => f x
    have hu1 : ∑ j, u j = ∑ x ∈ S, x := hu fun x => x
    have huτ : ∀ j, InRCone τ (u j) := fun j => hSτ _ (S.equivFin.symm j).2
    have hall := inRCone_of_evalZ_sum_le _ bar ψ X k γ hγ _ u (fun j => cone_bal hτ.mem (huτ j))
      (fun j => cone_nonneg hτ.nonneg (huτ j)) (by rw [hu1]; exact hσγ) (by rw [hu1, hu ψ.evalZ, hadd])
    have hSγ : ∀ x ∈ S, InRCone γ x := fun x hx => by
      simpa [u] using hall (S.equivFin ⟨x, hx⟩)
    have hβγ : InRCone γ β := AddSubmonoid.closure_induction (motive := fun x _ => InRCone γ x)
      (fun x hx => hSγ x ((hS x).2 ((hI x).1 hx))) cone_zero (fun _ _ _ _ => cone_add) hcl
    exact (lab_le hl hX hγ hβγ).trans hrγ.le
  have hle : lab.evalZ β₀ ≤ lab.evalZ β := (lab_le hl hX hτ hτ0).trans hr.le
  refine ⟨β₀, ⟨cone_bal hτ.mem hτ0, cone_nonneg hτ.nonneg hτ0, hprim, (le_antisymm hle hge).trans hlab, S,
    fun x => (hS x).trans (isIndec_iff hbar hψ hl hX hD hτ hτ0 (hr.le.trans hge) x).symm, g, hg, hgβ⟩, ?_⟩
  refine (cone_smul_iff hg).1 (hgβ ▸ cone_sum fun x hx => ?_)
  obtain ⟨h1, h2, -, h4, h5⟩ := (hF x).2 (hSτ x hx)
  exact GlobalTheory.T.psd_balanced_form_mem_cell_cone O bar hbar q ψ lab hψ hl X hX hD m v hv β hb hp hvβ x h1 h2 h4 h5

end GlobalTheory.CompanionTheory.Ar.Fan.MarkedRayInCone
