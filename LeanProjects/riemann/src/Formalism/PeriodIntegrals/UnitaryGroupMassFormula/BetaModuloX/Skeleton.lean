import Mathlib
import Formalism.PeriodIntegrals.ScalPairs

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

namespace PI.UnitaryGroupMassFormula.BetaModX

section Gen

def ModXAbs : Prop :=
  ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r T' g : ℕ)
    (F' : LFlag S r (T' : E)) (Λ : Submodule (𝓞 E) S.V) (γ : S.V ≃ₗ[E] S.V),
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    0 < T' → 3 ≤ g → Submodule.IsLattice E Λ →
    (∀ τ : E →+* ℂ, ∀ w ∈ orth S (Xplus F'), w ∉ Xsp F' → 0 < (τ (S.hT w w)).re) →
    IsAutLam S Λ γ → (Xsp F').map (γ : S.V →ₗ[E] S.V) = Xsp F' → γ F'.fl.z = F'.fl.z →
    (∀ w ∈ Lrep Λ F', γ w - w ∈ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F') →
    ∀ v ∈ orth S (Xsp F'), γ v - v ∈ Xsp F'

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem xa_r {T : E} (F : FlagG S r T) : F.Xa r = F.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  have : {i : Fin r | i.1 < r} = Set.univ := Set.eq_univ_of_forall (fun i => i.2)
  rw [this, Set.image_univ]

theorem mem_aut_iff {Λ : Submodule (𝓞 E) S.V} {β : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ β) (x : S.V) :
    β x ∈ Λ ↔ x ∈ Λ := by
  have h2 := h.2
  unfold Formalism.HermitianLatticesTheory.gmap at h2
  constructor
  · intro hx
    rw [← h2] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := β.injective hyx
    rw [← this]; exact hy
  · intro hx
    rw [← h2]
    exact ⟨x, hx, rfl⟩

theorem aut_inv {Λ : Submodule (𝓞 E) S.V} {β : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ β) : IsAutLam S Λ β⁻¹ := by
  refine ⟨Subgroup.inv_mem _ h.1, ?_⟩
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← mem_aut_iff h]
    show β (β.symm y) ∈ Λ
    simpa using hy
  · intro hx
    refine ⟨β x, (mem_aut_iff h x).2 hx, ?_⟩
    show β.symm (β x) = x
    exact β.symm_apply_apply x

theorem aut_mul {Λ : Submodule (𝓞 E) S.V} {β β' : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ β) (h' : IsAutLam S Λ β') :
    IsAutLam S Λ (β * β') := by
  refine ⟨Subgroup.mul_mem _ h.1 h'.1, ?_⟩
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show β (β' y) ∈ Λ
    exact (mem_aut_iff h _).2 ((mem_aut_iff h' _).2 hy)
  · intro hx
    refine ⟨β'.symm (β.symm x), ?_, ?_⟩
    · have h1 : β.symm x ∈ Λ := by
        rw [← mem_aut_iff h]; simpa using hx
      rw [SetLike.mem_coe, ← mem_aut_iff h']; simpa using h1
    · show β (β' (β'.symm (β.symm x))) = x
      simp

theorem isPair_refl (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') :
    IsPair Λ F F' F' (LinearEquiv.refl E S.V) g := by
  refine ⟨⟨fun _ _ => rfl, ?_⟩, fun j => ?_, rfl, fun _ _ _ _ => Iff.rfl⟩
  · unfold Formalism.HermitianLatticesTheory.gmap
    ext x; simp
  · ext x; simp

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IotaSurj : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ →
    ∀ x : Carrier (PD D Λ (lf D F0) u'), ∀ w ∈ Lrep Λ x.1,
      ∃ l ∈ Lrep Λ (lf D F0), l - w ∈ NgX Λ (gS D) (lf D F0) x.1

def XLamSub : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ →
    ∀ y : Carrier (PD D Λ (lf D F0) u'),
      XLam Λ (lf D F0) ≤ Ideal.span {(gS D : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1

def PosW : Prop :=
  ∀ (D : D7) (T' : ℕ) (F' : LFlag (hS D) D.R.rS ((T' : ℕ) : D.host.E)) (τ : D.host.E →+* ℂ) (w : (hS D).V),
    0 < T' → w ∈ orth (hS D) (Xplus F') → w ∉ Xsp F' → 0 < (τ ((hS D).hT w w)).re

theorem gS_ge_three (D : D7) (hg : ∀ i, 3 ≤ D.host.g i ∧ PI.ScalPairs.Unram D.host.E (D.host.g i)) :
    3 ≤ gS D := by
  unfold gS
  have h0 := (hg 0).1
  have h1 := (hg 1).1
  nlinarith

theorem betaModX_of (h1 : IotaSurj) (h2 : XLamSub) (h3 : PosW) (h4 : ModXAbs)
    (D : D7) (u u' : D.what₂.Word) : PI.ScalPairs.BetaL D u u' := by
  intro hg F0 Λ hΛ x y _ _ β₁ β₂ hP1 hP2 v hv
  set γ : (VS D).V ≃ₗ[D.host.E] (VS D).V := β₂⁻¹ * β₁ with hγ
  have hγv : ∀ w, γ w = β₂.symm (β₁ w) := fun w => rfl
  have hA : IsAutLam (VS D) Λ γ := aut_mul (aut_inv hP2.1) hP1.1
  have hX1 : (Xsp x.1).map (β₁ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp y.1 := by
    have := hP1.2.1 D.R.rS
    simpa [Xflag, Xsp, xa_r] using this
  have hX2 : (Xsp x.1).map (β₂ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp y.1 := by
    have := hP2.2.1 D.R.rS
    simpa [Xflag, Xsp, xa_r] using this
  have hmem2 : ∀ w, β₂ w ∈ Xsp y.1 ↔ w ∈ Xsp x.1 := by
    intro w
    rw [← hX2]
    constructor
    · rintro ⟨w', hw', hww⟩
      have : w' = w := β₂.injective hww
      rw [← this]; exact hw'
    · intro hw; exact ⟨w, hw, rfl⟩
  have hmem1 : ∀ w, β₁ w ∈ Xsp y.1 ↔ w ∈ Xsp x.1 := by
    intro w
    rw [← hX1]
    constructor
    · rintro ⟨w', hw', hww⟩
      have : w' = w := β₁.injective hww
      rw [← this]; exact hw'
    · intro hw; exact ⟨w, hw, rfl⟩
  have hXγ : (Xsp x.1).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp x.1 := by
    ext w
    constructor
    · rintro ⟨w', hw', rfl⟩
      rw [← hmem2]
      show β₂ (β₂.symm (β₁ w')) ∈ Xsp y.1
      rw [LinearEquiv.apply_symm_apply]
      exact (hmem1 w').2 hw'
    · intro hw
      refine ⟨β₁.symm (β₂ w), ?_, ?_⟩
      · rw [SetLike.mem_coe, ← hmem1]; simpa using (hmem2 w).2 hw
      · show β₂.symm (β₁ (β₁.symm (β₂ w))) = w
        simp
  have hz : γ x.1.fl.z = x.1.fl.z := by
    show β₂.symm (β₁ x.1.fl.z) = x.1.fl.z
    rw [hP1.2.2.1, ← hP2.2.2.1, LinearEquiv.symm_apply_apply]
  have hcong : ∀ w ∈ Lrep Λ x.1,
      γ w - w ∈ Ideal.span {(gS D : 𝓞 D.host.E)} • Λ ⊔ XLam Λ x.1 := by
    intro w hw
    obtain ⟨l, hl, hlw⟩ := h1 D u u' F0 Λ hΛ x w hw
    have e1 := (hP1.2.2.2 w hw l hl).1 hlw
    have e2 := (hP2.2.2.2 w hw l hl).1 hlw
    have hN : NgX Λ (gS D) (lf D F0) y.1 ≤
        Ideal.span {(gS D : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1 := by
      unfold NgX
      exact sup_le (sup_le le_sup_left (h2 D u u' F0 Λ hΛ y)) le_sup_right
    have hd : β₁ w - β₂ w ∈ Ideal.span {(gS D : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1 := by
      have : β₁ w - β₂ w = (l - β₂ w) - (l - β₁ w) := by abel
      rw [this]
      exact hN (Submodule.sub_mem _ e2 e1)
    let φ : (VS D).V →ₗ[𝓞 D.host.E] (VS D).V :=
      ((β₂⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)
    have hΛφ : Λ.map φ = Λ := (aut_inv hP2.1).2
    have hφ : (Ideal.span {(gS D : 𝓞 D.host.E)} • Λ ⊔ XLam Λ y.1).map φ ≤
        Ideal.span {(gS D : 𝓞 D.host.E)} • Λ ⊔ XLam Λ x.1 := by
      rw [Submodule.map_sup, Submodule.map_smul'', hΛφ]
      refine sup_le le_sup_left (le_trans ?_ le_sup_right)
      rintro _ ⟨t, ⟨htΛ, htX⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hΛφ]; exact ⟨t, htΛ, rfl⟩
      · show β₂.symm t ∈ Xsp x.1
        rw [← hmem2]; simpa using htX
    have : γ w - w = φ (β₁ w - β₂ w) := by
      show β₂.symm (β₁ w) - w = β₂.symm (β₁ w - β₂ w)
      rw [map_sub, LinearEquiv.symm_apply_apply]
    rw [this]
    exact hφ ⟨_, hd, rfl⟩
  have hpos : 0 < Tu D u' := (D.mem u').A.T_prime.pos
  have key := h4 (VS D) D.R.rS (Tu D u') (gS D) x.1 Λ γ (fun τ => D.sp.cm.cmUnram.2.1 τ) hpos
    (gS_ge_three D hg) hΛ.2.1.1 (fun τ w hw hwX => h3 D (Tu D u') x.1 τ w hpos hw hwX) hA hXγ hz hcong v hv
  have : β₁ v - β₂ v = β₂ (γ v - v) := by
    rw [map_sub, hγv, LinearEquiv.apply_symm_apply]
  rw [this]
  exact (hmem2 _).2 key

end D7

end PI.UnitaryGroupMassFormula.BetaModX
