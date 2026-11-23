import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

def secVal {B : Type} [CommRing B] {Z : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Z) (W : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Z, W)) : B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((x.appLE W ⊤ h).hom f)

def FullTorsion (G : Over X) [GrpObj G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ) : Prop :=
  ∀ (k : Type) [Field k] (i : Ω →+* k) (g : Over.mk (spMap i ≫ ξ) ⟶ G), g ^ n = 1 →
    ∃ x : Over.mk ξ ⟶ G, g.left = spMap i ≫ x.left

namespace LieModel

def IsHTAt (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) (x : Over.mk ξ ⟶ G) (q : Cpt ξ)
    (w : Module.Dual Ω E) : Prop :=
  w ∈ M.omLat q ∧ ∃ (W : G.left.Opens) (f : Γ(G.left, W)), (η[G]).left q.1 ∈ W ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (xk g : Over.mk (spMap i ≫ ξ) ⟶ G) (c : kˣ)
      (h : ⊤ ≤ g.left ⁻¹ᵁ W), xk.left = spMap i ≫ x.left → g ^ n = 1 →
        Out.WeilIs G L n xk g (unitOn c) → secVal (B := k) g.left W h f = c) ∧
    ∀ e v, M.Extends q e v → ∀ h : ⊤ ≤ v.left ⁻¹ᵁ W, ∃ r ∈ regAt ξ q,
      w e = genMap ξ q (secVal (B := DualNumber (X.presheaf.stalk q.1)) v.left W h f).snd + n * r

def htOm (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) : Lat ξ (Module.Dual Ω E) := fun q =>
  Submodule.span (regAt ξ q) {w | ∃ x : Over.mk ξ ⟶ G, x ^ n = 1 ∧ M.IsHTAt L n x q w}

def htOmEig (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ (Module.Dual Ω (eigSp ρ σ)) :=
  (M.htOm L n).map (eigSp ρ σ).subtype.dualMap

def htDual (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q}

def htW (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
    (σ : O →+* Ω) (𝔡 : Ideal O) : Lat ξ E := fun q =>
  Submodule.span (regAt ξ q) {e | e ∈ eigSp ρ σ ∧ ∀ d ∈ 𝔡, σ d • e ∈ M.htDual L n ρ σ q}

variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem htOm_le (q : Cpt ξ) : M.htOm L n q ≤ M.omLat q :=
  Submodule.span_le.2 fun _ ⟨_, _, h⟩ => h.1

theorem mem_htDual_iff (q : Cpt ξ) (e : E) :
    e ∈ M.htDual L n ρ σ q ↔ e ∈ eigSp ρ σ ∧ ∀ w ∈ M.htOm L n q, w e ∈ regAt ξ q := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨(eigSp ρ σ).zero_mem, fun w _ => by simpa using (regAt ξ q).zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨(eigSp ρ σ).add_mem hx.1 hy.1, fun w hw => by
        simpa using (regAt ξ q).add_mem (hx.2 w hw) (hy.2 w hw)⟩
    | smul c x _ hx =>
      refine ⟨(eigSp ρ σ).smul_mem (c : Ω) hx.1, fun w hw => ?_⟩
      have : w (c • x) = (c : Ω) * w x := by
        show w ((c : Ω) • x) = _
        rw [map_smul, smul_eq_mul]
      rw [this]
      exact (regAt ξ q).mul_mem c.2 (hx.2 w hw)
  · exact fun h => Submodule.subset_span h

theorem mem_eigSp_of_mem_htDual {q : Cpt ξ} {e : E} (he : e ∈ M.htDual L n ρ σ q) : e ∈ eigSp ρ σ :=
  ((M.mem_htDual_iff L n ρ σ q e).1 he).1

theorem mem_htDual (q : Cpt ξ) (e : eigSp ρ σ) :
    (e : E) ∈ M.htDual L n ρ σ q ↔ ∀ u ∈ M.htOmEig L n ρ σ q, u e ∈ regAt ξ q := by
  rw [mem_htDual_iff]
  constructor
  · rintro ⟨-, h⟩ u hu
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hu
    exact h w hw
  · intro h
    refine ⟨e.2, fun w hw => ?_⟩
    exact h _ (Submodule.mem_map.2 ⟨w, hw, rfl⟩)

theorem eigLat_le_htDual (q : Cpt ξ) : M.eigLat ρ σ q ≤ M.htDual L n ρ σ q :=
  fun e he => Submodule.subset_span ⟨he.2, fun w hw => (M.htOm_le L n q hw) e he.1⟩

theorem mem_eigSp_of_mem_htW (𝔡 : Ideal O) {q : Cpt ξ} {e : E} (he : e ∈ M.htW L n ρ σ 𝔡 q) :
    e ∈ eigSp ρ σ := by
  induction he using Submodule.span_induction with
  | mem x hx => exact hx.1
  | zero => exact (eigSp ρ σ).zero_mem
  | add x y _ _ hx hy => exact (eigSp ρ σ).add_mem hx hy
  | smul c x _ hx => exact (eigSp ρ σ).smul_mem (c : Ω) hx

example (q : Cpt ξ) : (0 : Module.Dual Ω (eigSp ρ σ)) ∈ M.htOmEig L n ρ σ q := Submodule.zero_mem _

end LieModel

open Classical in

def Lat.patch (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat ξ E := fun q =>
  if ∃ p ∈ S, InFibre ξ p q then ⨅ p ∈ S, ⨅ _ : InFibre ξ p q, Lp p q else L₀ q

theorem Lat.patch_empty (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) : Lat.patch ∅ L₀ Lp = L₀ := by
  funext q; simp [Lat.patch]

theorem Lat.patch_of_not (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ}
    (hq : ∀ p ∈ S, ¬ InFibre ξ p q) : Lat.patch S L₀ Lp q = L₀ q := by
  simp only [Lat.patch]; rw [if_neg]; rintro ⟨p, hp, h⟩; exact hq p hp h

theorem Lat.patch_of_unique (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ} {p : ℕ} (hp : p ∈ S)
    (hq : InFibre ξ p q) (hu : ∀ p' ∈ S, InFibre ξ p' q → p' = p) : Lat.patch S L₀ Lp q = Lp p q := by
  simp only [Lat.patch]; rw [if_pos ⟨p, hp, hq⟩]
  refine le_antisymm (iInf₂_le_of_le p hp (iInf_le _ hq)) (le_iInf₂ fun p' hp' => le_iInf fun h => ?_)
  rw [hu p' hp' h]

end GlobalTheory.CompanionTheory.Ar
