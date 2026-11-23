import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtLatCheck

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem secVal_one {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) : secVal x W h 1 = 1 := by
  simp [secVal]

theorem fullTorsion_one : FullTorsion G ξ 1 := by
  intro k _ i g hg
  rw [pow_one] at hg
  subst hg
  refine ⟨1, ?_⟩
  have h := MonObj.comp_one (M := G) (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ)
  rw [← h]; rfl

theorem isHTAt_add_nsmul {x : Over.mk ξ ⟶ G} {q : Cpt ξ} {w w' : Module.Dual Ω E}
    (hw : M.IsHTAt L n x q w) (hw' : w' ∈ M.omLat q) : M.IsHTAt L n x q (w + n • w') := by
  obtain ⟨h1, W, f, hW, hv, hd⟩ := hw
  refine ⟨(M.omLat q).add_mem h1 ((M.omLat q).toAddSubmonoid.nsmul_mem hw' n), W, f, hW, hv, fun e v he h => ?_⟩
  obtain ⟨r, hr, hre⟩ := hd e v he h
  refine ⟨r + w' e, (regAt ξ q).add_mem hr (hw' e (Submodule.subset_span ⟨v, he⟩)), ?_⟩
  simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hre]; ring

theorem isHTAt_one_zero (q : Cpt ξ)
    (h1 : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ),
      Out.WeilIs G L n 1 g (unitOn c) → c = 1) : M.IsHTAt L n 1 q 0 := by
  refine ⟨Submodule.zero_mem _, ⊤, 1, trivial, fun k _ _ i xk g c h hx _ hc => ?_, fun e v _ h => ⟨0, (regAt ξ q).zero_mem, ?_⟩⟩
  · have hx1 : xk = 1 := by
      have h := MonObj.comp_one (M := G) (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ ξ) ⟶ Over.mk ξ)
      ext1
      rw [hx, ← h]; rfl
    subst hx1
    rw [secVal_one, h1 k i g c hc]; rfl
  · rw [secVal_one]; simp only [TrivSqZeroExt.snd_one, LinearMap.zero_apply, mul_zero, add_zero]
    exact (RingHom.map_zero (genMap ξ q)).symm

theorem nsmul_mem_htOm (q : Cpt ξ)
    (h1 : ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ),
      Out.WeilIs G L n 1 g (unitOn c) → c = 1) {w : Module.Dual Ω E} (hw : w ∈ M.omLat q) :
    n • w ∈ M.htOm L n q :=
  Submodule.subset_span ⟨1, one_pow _, by
    simpa using isHTAt_add_nsmul M L n (isHTAt_one_zero M L n q h1) hw⟩

theorem mem_htW_iff (𝔡 : Ideal O) (q : Cpt ξ) (e : E) :
    e ∈ M.htW L n ρ σ 𝔡 q ↔ e ∈ eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q := by
  refine ⟨fun he => ⟨M.mem_eigSp_of_mem_htW L n ρ σ 𝔡 he, ?_⟩, fun h => Submodule.subset_span h⟩
  induction he using Submodule.span_induction with
  | mem x hx => exact hx.2
  | zero => intro d _; simp
  | add x y _ _ hx hy => intro d hd; rw [smul_add]; exact Submodule.add_mem _ (hx d hd) (hy d hd)
  | smul c x _ hx =>
    intro d hd
    have : σ d • (c • x) = c • (σ d • x) := by
      show σ d • ((c : Ω) • x) = (c : Ω) • (σ d • x)
      exact smul_comm _ _ _
    rw [this]; exact Submodule.smul_mem _ c (hx d hd)

theorem htW_span_singleton (d : O) (hd : σ d ≠ 0) (q : Cpt ξ) (hσ : ∀ a, σ a ∈ regAt ξ q) :
    M.htW L n ρ σ (Ideal.span {d}) q = (M.htDual L n ρ σ).scale (σ d)⁻¹ q := by
  ext e
  rw [mem_htW_iff]
  constructor
  · rintro ⟨-, h⟩
    refine Submodule.mem_map.2 ⟨σ d • e, h d (Ideal.mem_span_singleton_self d), ?_⟩
    simp [smul_smul, inv_mul_cancel₀ hd]
  · intro h
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 h
    have hue := M.mem_eigSp_of_mem_htDual L n ρ σ hu
    refine ⟨(eigSp ρ σ).smul_mem _ hue, fun a ha => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have : σ (b * d) • ((σ d)⁻¹ • u) = (⟨σ b, hσ b⟩ : regAt ξ q) • u := by
      show _ = σ b • u
      rw [smul_smul, map_mul, mul_inv_cancel_right₀ hd]
    show σ (b * d) • ((σ d)⁻¹ • u) ∈ _
    rw [this]; exact Submodule.smul_mem _ _ hu

theorem htDual_bounded (q : Cpt ξ) (hn : ∀ w ∈ M.omLat q, n • w ∈ M.htOm L n q) {e : E}
    (he : e ∈ M.htDual L n ρ σ q) {w : Module.Dual Ω E} (hw : w ∈ M.omLat q) : w (n • e) ∈ regAt ξ q := by
  have := ((M.mem_htDual_iff L n ρ σ q e).1 he).2 _ (hn w hw)
  simpa using this

end GlobalTheory.CompanionTheory.Ar.HtLatCheck
