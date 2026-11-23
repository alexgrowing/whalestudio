import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict

noncomputable section

namespace PositivityTheory.ThK.SplitAsm

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip
open PositivityTheory.KCo PositivityTheory.ThK.SplitLoc PositivityTheory.ThK.SplitDict PositivityTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ChrFacts : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Base F E) (X : Chars F E)
    (a a' : ℕ) (v : Pl F) (τ : E →ₐ[F] Fv F v), X.IsGood B a a' →
    (∀ x, ‖(chrW X.α τ x : ℂ)‖ = 1) ∧ (∀ x, ‖(chrW X.β τ x : ℂ)‖ = 1) ∧ chrW X.ν τ = chrW X.α τ / chrW X.β τ ∧
    (∃ e : ℕ, CondLE (unifAt v) e (chrW X.α τ) ∧ CondLE (unifAt v) e (chrW X.β τ)) ∧
    (v ∈ X.T → ¬ GlobalTheory.SplitWeil.IsUnram (chrW X.ν τ)) ∧
    (v ∉ X.T → GlobalTheory.SplitWeil.IsUnram (chrW X.α τ) ∧ GlobalTheory.SplitWeil.IsUnram (chrW X.β τ))

theorem sb_eq (Y : Type) [TopologicalSpace Y] : GlobalTheory.SplitWeil.SB Y = GlobalTheory.WeilM.SB Y := by
  exact SetLike.ext fun _ => Iff.rfl

theorem extendOn {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ V)
    (g : V → W) (hg : ∀ x ∈ S, ∀ y ∈ S, ∀ c : ℂ, g (x + c • y) = g x + c • g y) :
    ∃ p : V →ₗ[ℂ] W, ∀ x ∈ S, p x = g x := by
  have h0 : g 0 = 0 := by
    have h1 := hg 0 S.zero_mem 0 S.zero_mem 1
    rw [smul_zero, add_zero, one_smul] at h1
    have h2 : g 0 + g 0 = g 0 + 0 := by
      rw [add_zero]
      exact h1.symm
    exact add_left_cancel h2
  let gS : S →ₗ[ℂ] W :=
    { toFun := fun x => g x
      map_add' := fun x y => by
        have h3 := hg x x.2 y y.2 1
        rw [one_smul, one_smul] at h3
        simpa using h3
      map_smul' := fun c x => by
        have h3 := hg 0 S.zero_mem x x.2 c
        rw [zero_add, h0, zero_add] at h3
        simpa using h3 }
  obtain ⟨p, hp⟩ := LinearMap.exists_extend gS
  refine ⟨p, fun x hx => ?_⟩
  have h4 := LinearMap.congr_fun hp ⟨x, hx⟩
  simpa [gS] using h4

theorem mk_p {D M P : Type} [AddCommGroup P] [Module ℂ P] (SD : Submodule ℂ (D → ℂ)) (SM : Submodule ℂ (M → ℂ))
    (ι : (D → ℂ) →ₗ[ℂ] (M → ℂ)) (hι : Set.BijOn ι SD SM) (N : Submodule ℂ P) (f : (M → ℂ) → P)
    (hlin : ∀ Φ ∈ SM, ∀ Φ₁ ∈ SM, ∀ c : ℂ, f (Φ + c • Φ₁) = f Φ + c • f Φ₁) (hmem : ∀ Φ ∈ SM, f Φ ∈ N)
    (hon : ∀ y ∈ N, ∃ Φ ∈ SM, f Φ = y) :
    ∃ p : (D → ℂ) →ₗ[ℂ] N, (∀ φ ∈ SD, (p φ : P) = f (ι φ)) ∧ SD.map p = ⊤ := by
  classical
  let g : (D → ℂ) → N := fun φ => if h : ι φ ∈ SM then ⟨f (ι φ), hmem _ h⟩ else 0
  have hgS : ∀ φ ∈ SD, (g φ : P) = f (ι φ) := by
    intro φ hφ
    show ((if h : ι φ ∈ SM then (⟨f (ι φ), hmem _ h⟩ : N) else 0 : N) : P) = f (ι φ)
    rw [dif_pos (show ι φ ∈ SM from hι.mapsTo hφ)]
  obtain ⟨p, hp⟩ := extendOn SD g (by
    intro x hx y hy c
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, hgS _ (SD.add_mem hx (SD.smul_mem c hy)), hgS _ hx, hgS _ hy,
      map_add, map_smul]
    exact hlin _ (hι.mapsTo hx) _ (hι.mapsTo hy) c)
  refine ⟨p, fun φ hφ => by rw [hp φ hφ]; exact hgS φ hφ, ?_⟩
  rw [eq_top_iff]
  rintro y -
  obtain ⟨Φ, hΦ, hfΦ⟩ := hon y.1 y.2
  obtain ⟨φ, hφ, hιφ⟩ := hι.surjOn hΦ
  refine ⟨φ, hφ, ?_⟩
  apply Subtype.ext
  rw [hp φ hφ, hgS φ hφ, hιφ, hfΦ]

end PositivityTheory.ThK.SplitAsm
