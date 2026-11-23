import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SESExact

theorem homW_exact_middle : ∀ {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ} {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂} {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : GlobalTheory.BK.Hom P₀ P₁} {H : GlobalTheory.BK.Hom P₁ P₂} (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H), ∀ v : κ → OW l O, homW t ϖ H v = 0 → ∃ w, homW t ϖ F w = v := by
  intro l _ a _ e _ O K _ _ _ _ _ _ _ _ _ t ϖ G _ _ ι κ μ _ _ _ _ _ _ P₀ P₁ P₂ T₀ T₁ T₂ I₀ I₁ I₂ f g F H hS hF hH v hv
  obtain ⟨-, -, hOnto, hker, hsat⟩ := hS
  set f₁ := (f.f.restrictScalars O).restrict f.T_le with hf₁
  set g₁ := (g.f.restrictScalars O).restrict g.T_le with hg₁
  have hgs : Function.Surjective g₁ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := hOnto y hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hex : Function.Exact f₁ g₁ := by
    rintro ⟨y, hy⟩
    constructor
    · intro h0
      have h0' : g.f y = 0 := congrArg Subtype.val h0
      obtain ⟨z, hz⟩ := (hker y).1 h0'
      have hzT : z ∈ T₀.L.T := hsat z (hz ▸ hy)
      exact ⟨⟨z, hzT⟩, Subtype.ext hz⟩
    · rintro ⟨⟨z, hzT⟩, hz⟩
      apply Subtype.ext
      have hz' : f.f z = y := congrArg Subtype.val hz
      exact (hker y).2 ⟨z, hz'⟩
  have hT := lTensor_exact (OW l O) hex hgs
  have h1 : latW g (I₁.j v) = 0 := by
    rw [← hH v, hv, map_zero]
  obtain ⟨z, hz⟩ := (hT (I₁.j v)).1 h1
  refine ⟨I₀.j.symm z, I₁.j.injective ?_⟩
  rw [hF, LinearEquiv.apply_symm_apply]
  exact hz

end GlobalTheory.BKReal.SESExact
