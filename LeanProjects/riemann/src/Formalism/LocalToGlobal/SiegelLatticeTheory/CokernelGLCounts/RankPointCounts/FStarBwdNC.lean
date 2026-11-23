import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNB

noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem X_le_orth (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) : X ≤ orth S X :=
  fun x hx => (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun y hy => hXiso y hy x hx

theorem orth_X {X : Submodule E S.V} {u x : S.V} (hu : u ∈ orth S X) (hx : x ∈ X) : S.hT x u = 0 :=
  (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hu x hx

theorem orth_X' {X : Submodule E S.V} {u x : S.V} (hu : u ∈ orth S X) (hx : x ∈ X) : S.hT u x = 0 := by
  rw [hsw S x u, orth_X S hu hx, star_zero]

theorem stepB (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (z : S.V) (hzX : z ∈ orth S X)
    (Λ Λ₂ : Submodule (𝓞 E) S.V) (hΛ₂ : Submodule.IsLattice E Λ₂) (hSD₂ : SD S Λ₂)
    (hX : ∀ x ∈ X, x ∈ Λ₂ → x ∈ Λ) (hz : z ∈ Λ) (hz₂ : z ∈ Λ₂)
    (hL : ∀ x ∈ Λ₂, x ∈ orth S X → ∃ y ∈ Λ, y - x ∈ X)
    (hy : ∃ y ∈ Λ₂, y ∈ orth S X ∧ S.hT y z = 1) :
    ∃ A : orth S X →ₗ[E] S.V, (∀ u, A u ∈ X) ∧ (∀ u : orth S X, (u : S.V) ∈ X → A u = 0) ∧
      A ⟨z, hzX⟩ = 0 ∧ ∀ (x : S.V) (hx : x ∈ orth S X), x ∈ Λ₂ → x + A ⟨x, hx⟩ ∈ Λ := by
  classical
  obtain ⟨y, hyΛ, hyX, hyz⟩ := hy
  let M₂ : Submodule (𝓞 E) S.V := Λ₂ ⊓ (orth S X).restrictScalars (𝓞 E)
  have hM₂fg : M₂.FG := Submodule.FG.of_le hΛ₂.fg inf_le_left
  have hXo := X_le_orth S X hXiso
  obtain ⟨δ, hδX, hδ0, hδΛ⟩ := glift S M₂ Λ hM₂fg X X (fun x hx hxX => hX x hxX hx.1)
    (fun x hx => hL x hx.1 hx.2)
  let z₂ : M₂ := ⟨z, hz₂, hzX⟩
  let κ : M₂ →ₗ[𝓞 E] E := ((S.hT y).restrictScalars (𝓞 E)) ∘ₗ M₂.subtype
  let δ' : M₂ →ₗ[𝓞 E] S.V := δ - κ.smulRight (δ z₂)
  have hδ'app : ∀ m, δ' m = δ m - S.hT y m • δ z₂ := fun m => rfl
  have hδ'X : ∀ m, δ' m ∈ X := fun m => by
    rw [hδ'app]; exact X.sub_mem (hδX m) (X.smul_mem _ (hδX z₂))
  have hδ'0 : ∀ m : M₂, (m : S.V) ∈ X → δ' m = 0 := fun m hm => by
    rw [hδ'app, hδ0 m hm, orth_X' S hyX hm, zero_smul, sub_zero]
  have hδ'z : δ' z₂ = 0 := by
    rw [hδ'app]; show δ z₂ - S.hT y z • δ z₂ = 0; rw [hyz, one_smul, sub_self]
  have hδzΛ : δ z₂ ∈ Λ := by
    have := Λ.sub_mem (hδΛ z₂) hz
    have e : (z₂ : S.V) + δ z₂ - z = δ z₂ := by show z + δ z₂ - z = δ z₂; abel
    rwa [e] at this
  have hδ'Λ : ∀ m : M₂, (m : S.V) + δ' m ∈ Λ := fun m => by
    rw [hδ'app, ← add_sub_assoc]
    exact Λ.sub_mem (hδΛ m) (int_smul_mem (sd_int hSD₂ m.2.1 hyΛ) hδzΛ)
  have hfull : ∀ u ∈ orth S X, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ M₂ := fun u hu => by
    obtain ⟨d, hd, hdu⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.exists_smul_mem S Λ₂ hΛ₂ u
    exact ⟨d, hd, hdu, by show d • u ∈ orth S X; rw [oSmul]; exact (orth S X).smul_mem _ hu⟩
  obtain ⟨A, hA⟩ := ext_lat S (W := S.V) (orth S X) M₂ (fun x hx => hx.2) hfull δ'
  have hscale : ∀ u : orth S X, ∃ d : 𝓞 E, d ≠ 0 ∧ ∃ hm : ((d : E) • (u : S.V)) ∈ M₂,
      (d : E) • A u = δ' ⟨_, hm⟩ := fun u => by
    obtain ⟨d, hd, hdu⟩ := hfull u u.2
    rw [oSmul] at hdu
    refine ⟨d, hd, hdu, ?_⟩
    rw [← map_smul, ← hA _ hdu]
    rfl
  refine ⟨A, fun u => ?_, fun u hu => ?_, ?_, fun x hx hxΛ => ?_⟩
  · obtain ⟨d, hd, hm, he⟩ := hscale u
    have h1 : (d : E) • A u ∈ X := by rw [he]; exact hδ'X _
    have h2 := X.smul_mem ((d : E)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (coe_ne_zero hd), one_smul] at h2
  · obtain ⟨d, hd, hm, he⟩ := hscale u
    rw [hδ'0 _ (X.smul_mem _ hu)] at he
    exact (smul_eq_zero.1 he).resolve_left (coe_ne_zero hd)
  · rw [hA z ⟨hz₂, hzX⟩]; exact hδ'z
  · rw [hA x ⟨hxΛ, hx⟩]; exact hδ'Λ ⟨x, hxΛ, hx⟩

theorem stepW (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (A : orth S X →ₗ[E] S.V)
    (hA : ∀ u, A u ∈ X) (hA0 : ∀ u : orth S X, (u : S.V) ∈ X → A u = 0) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ a b, S.hT (g a) (g b) = S.hT a b) ∧ ∀ u : orth S X, g u = u + A u := by
  let f : orth S X →ₗ[E] S.V := (orth S X).subtype + A
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have h1 : (u : S.V) = -A u := eq_neg_of_add_eq_zero_left hu
    have h2 : (u : S.V) ∈ X := by rw [h1]; exact X.neg_mem (hA u)
    have h3 := hA0 u h2
    rw [h3, neg_zero] at h1
    exact (Submodule.mem_bot E).2 (Subtype.ext h1)
  have hiso : ∀ u v : orth S X, S.hT (f u) (f v) = S.hT u v := fun u v => by
    show S.hT ((u : S.V) + A u) ((v : S.V) + A v) = S.hT u v
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, orth_X' S u.2 (hA v), orth_X S v.2 (hA u),
      hXiso _ (hA u) _ (hA v)]
    ring
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem E S.V S.hT (fun x y => by rw [hsw S x y])
    (fun x hx => S.nondeg.1 x hx) (orth S X) f hinj hiso
  exact ⟨g, hg, fun u => hgf u⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
