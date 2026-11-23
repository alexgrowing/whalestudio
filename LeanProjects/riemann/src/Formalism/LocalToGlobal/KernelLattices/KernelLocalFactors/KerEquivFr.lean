import Mathlib
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Frames

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem liftFr_smul {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : DecoSet E n ST SG) (a : UF E n × GLG E n SG) (w : SG) :
    ∃ κ : ↥(GLint E n w.1), (a • d).1.liftFr w = a.1.1 * d.1.liftFr w * κ.1 ∧
      ∀ x ∈ stdAt E n w.1, redV w.1 (κ.1 x) = ((a.2 w)⁻¹ : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x) := by
  set γ : Sp E n ≃ₗ[E] Sp E n := a.1.1 with hγ
  set F := d.1.liftFr w with hFdef
  set F₁ := (a • d).1.liftFr w with hF₁def
  have hF : d.1.IsLift w F := Deco.liftFr_spec (d.2.hasLift w)
  have hF₁ : (a • d).1.IsLift w F₁ := Deco.liftFr_spec ((a • d).2.hasLift w)
  have hat : ∀ y, y ∈ (a • d).1.at w.1 ↔ γ.symm y ∈ d.1.at w.1 := fun y => mem_localization_gmap _ _ _ _
  have hbe : ∀ y, (a • d).1.be w y = (a.2 w).1.mulVec (d.1.be w (γ.symm y)) := fun _ => rfl
  have hκx : ∀ x, (F⁻¹ * γ⁻¹ * F₁) x = F.symm (γ.symm (F₁ x)) := fun _ => rfl
  have hmem : F⁻¹ * γ⁻¹ * F₁ ∈ GLint E n w.1 := by
    intro x
    change (F⁻¹ * γ⁻¹ * F₁) x ∈ stdAt E n w.1 ↔ x ∈ stdAt E n w.1
    rw [hκx, ← hF.1, LinearEquiv.apply_symm_apply, ← hat, hF₁.1]
  refine ⟨⟨F⁻¹ * γ⁻¹ * F₁, hmem⟩, ?_, ?_⟩
  · change F₁ = γ * F * (F⁻¹ * γ⁻¹ * F₁)
    group
  · intro x hx
    change redV w.1 ((F⁻¹ * γ⁻¹ * F₁) x) = _
    have hk : (F⁻¹ * γ⁻¹ * F₁) x ∈ stdAt E n w.1 := (hmem x).2 hx
    have h1 := hF.2 _ hk
    rw [hκx, LinearEquiv.apply_symm_apply] at h1
    have h2 := hF₁.2 x hx
    rw [hbe, h1] at h2
    rw [hκx, ← h2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end Frames

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem frsF_smul {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j)
    (Λ : LevFam X.E X.K (R.N j) Pr.vGs) (Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
    (g : FrmG Λ Θ) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    ∃ κ : ↥(GLint X.E (R.N j) P.1), frsF sel mu (g • p) P = g.1.1 * frsF sel mu p P * κ.1 ∧
      ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (κ.1 x) =
        (((g.2.1 : GLG X.E (R.N j) Pr.vGs) ⟨P.1, hP⟩)⁻¹ : GL _ _).1.mulVec (redV P.1 x) := by
  have e : (g • p).deco = ((g.1, (g.2.1 : GLG X.E (R.N j) Pr.vGs)) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs) • p.deco := rfl
  unfold frsF
  rw [dif_pos hP, dif_pos hP, e]
  exact liftFr_smul p.deco (g.1, (g.2.1 : GLG X.E (R.N j) Pr.vGs)) ⟨P.1, hP⟩

end Chain

section PhiT

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem phiT_smul (K : Type) [Field K] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (d : DecoSet E a ST SG) (d' : DecoSet E b ST SG') (γ : UF E a) (h : GLG E a SG) (γ' : UF E b) (h' : GLG E b SG')
    (x : HomE E a b) :
    phiT K ((γ, h) • d).1 ((γ', h') • d').1 (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = phiT K d.1 d'.1 x := by
  have hat : ∀ (P : ST) y, y ∈ ((γ, h) • d).1.at P.1 ↔ γ.1.symm y ∈ d.1.at P.1 := fun P y => mem_localization_gmap _ _ _ _
  have hat' : ∀ (P : ST) y, y ∈ ((γ', h') • d').1.at P.1 ↔ γ'.1.symm y ∈ d'.1.at P.1 := fun P y => mem_localization_gmap _ _ _ _
  have hf : ∀ (P : ST) y, ((γ, h) • d).1.f P y = d.1.f P (γ.1.symm y) := fun _ _ => rfl
  have hf' : ∀ (P : ST) y, ((γ', h') • d').1.f P y = d'.1.f P (γ'.1.symm y) := fun _ _ => rfl
  have hx : ∀ y, (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) y = γ'.1 (x (γ.1.symm y)) := fun _ => rfl
  have key : (∀ P : ST, ∀ y ∈ ((γ, h) • d).1.at P.1,
      (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) y ∈ ((γ', h') • d').1.at P.1 ∧
        ((γ', h') • d').1.f P ((γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) y) = ((γ, h) • d).1.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.1.at P.1, x y ∈ d'.1.at P.1 ∧ d'.1.f P (x y) = d.1.f P y) := by
    constructor
    · intro H P y hy
      have := H P (γ.1 y) ((hat P _).2 (by rwa [LinearEquiv.symm_apply_apply]))
      rw [hx, hat', hf', hf, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at this
      exact this
    · intro H P y hy
      rw [hx, hat', hf', hf, LinearEquiv.symm_apply_apply]
      exact H P _ ((hat P y).1 hy)
  unfold phiT
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.1 h1) h2
  · exact absurd (key.2 h2) h1
  · rfl

theorem phiT_add_mul (K : Type) [Field K] {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}
    (d : DecoSet E a ST SG) (d' : DecoSet E b ST SG') (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ P : ST, P.1 ∈ S)
    (T : ℕ) (hT : ∀ P : ST, (T : 𝓞 E) ∈ P.1.asIdeal) (x z : HomE E a b)
    (hz : z ∈ mulLat T (homAt S d.1.N d'.1.N)) :
    phiT K d.1 d'.1 (x + z) = phiT K d.1 d'.1 x := by
  obtain ⟨z₀, hz₀, rfl⟩ := Submodule.mem_map.1 hz
  have hzy : ∀ (P : ST), ∀ y ∈ d.1.at P.1, ((T : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z₀ y ∈ d'.1.at P.1 ∧
      d'.1.f P ((((T : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z₀) y) = 0 := by
    intro P y hy
    have e : ((T : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z₀ y = (T : 𝓞 E) • z₀ y := rfl
    have hm : z₀ y ∈ d'.1.at P.1 := hz₀ P.1 (hS P) y hy
    rw [e]
    refine ⟨Submodule.smul_mem _ _ hm, ?_⟩
    rw [d'.2.f_smul P _ _ hm, Ideal.Quotient.eq_zero_iff_mem.2 (hT P), zero_mul]
  have key : (∀ P : ST, ∀ y ∈ d.1.at P.1, (x + ((T : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z₀) y ∈ d'.1.at P.1 ∧
        d'.1.f P ((x + ((T : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z₀) y) = d.1.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.1.at P.1, x y ∈ d'.1.at P.1 ∧ d'.1.f P (x y) = d.1.f P y) := by
    constructor
    · intro H P y hy
      obtain ⟨h1, h2⟩ := H P y hy
      obtain ⟨h3, h4⟩ := hzy P y hy
      rw [LinearMap.add_apply] at h1 h2
      have hxm : x y ∈ d'.1.at P.1 := by simpa using sub_mem h1 h3
      refine ⟨hxm, ?_⟩
      rw [d'.2.f_add P _ hxm _ h3, h4, add_zero] at h2
      exact h2
    · intro H P y hy
      obtain ⟨h1, h2⟩ := H P y hy
      obtain ⟨h3, h4⟩ := hzy P y hy
      rw [LinearMap.add_apply]
      refine ⟨add_mem h1 h3, ?_⟩
      rw [d'.2.f_add P _ h1 _ h3, h4, add_zero, h2]
  unfold phiT
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.1 h1) h2
  · exact absurd (key.2 h2) h1
  · rfl

end PhiT

end Formalism.L2.Ker
