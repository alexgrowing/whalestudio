import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceS

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul' (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V) = 1 := by
  simp [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_eq {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h x = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) x) (Formalism.L2.Theta.mt S g⁻¹) := rfl

theorem actO_actO {S T : HSp D} (g g' : GA D S) (h h' : GA D T) (x : WO S T) :
    actO S T g h (actO S T g' h' x) = actO S T (g * g') (h * h') x := by
  rw [actO_eq, actO_eq, actO_eq, _root_.mul_inv_rev, mt_mul', mt_mul']
  simp only [Matrix.mul_assoc]

theorem actO_one {S T : HSp D} (x : WO S T) : actO S T 1 1 x = x := by
  rw [actO_eq, inv_one, mt_one', mt_one', Matrix.one_mul, Matrix.mul_one]

theorem actO_add {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  rw [actO_eq, actO_eq, actO_eq, Matrix.mul_add, Matrix.add_mul]

theorem actO_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_eq, Matrix.mul_zero, Matrix.zero_mul]
  | succ k ih => rw [succ_nsmul, actO_add, ih, succ_nsmul]

theorem isHalf_mul_mul {e : AE D} {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (AE D)) (x : Matrix (Fin b) (Fin c) (AE D))
    (N : Matrix (Fin c) (Fin c) (AE D)) (hx : IsHalf e x) : IsHalf e (M * x * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [← hx k l]
  ring

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
      rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
    rw [← this]
    exact isHalf_mul_mul _ _ _ hx
  · intro hx
    exact isHalf_mul_mul _ _ _ hx

def actPull {S T : HSp D} (p : GA D S × GA D T) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun t => Φ (actO S T p.1⁻¹ p.2⁻¹ t)

theorem actPull_mul {S T : HSp D} (p q : GA D S × GA D T) (Φ : WO S T → ℂ) :
    actPull p (actPull q Φ) = actPull (p * q) Φ := by
  funext t
  simp only [actPull, actO_actO, Prod.fst_mul, Prod.snd_mul, _root_.mul_inv_rev]

def ActsLin {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (e : AE D) (Λ : AddSubgroup (WO S T)) (p : GA D S × GA D T) (c : ℂ) :
    Prop :=
  ∀ Φ, IsSBHalf e Λ Φ → om p (Tm Φ) = c • Tm (actPull p Φ)

theorem actsLin_one {S T : HSp D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D} {Λ : AddSubgroup (WO S T)} : ActsLin om Tm e Λ 1 1 := by
  intro Φ _
  have : actPull (1 : GA D S × GA D T) Φ = Φ := by
    funext t; simp [actPull, actO_one]
  rw [this, map_one, one_smul]
  rfl

theorem sbHalf_actPull {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)} (p : GA D S × GA D T)
    (hΛ : ∀ t, IsHalf e t → (actO S T p.1⁻¹ p.2⁻¹ t ∈ Λ ↔ t ∈ Λ)) {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) :
    IsSBHalf e Λ (actPull p Φ) := by
  obtain ⟨hsupp, k, hk, hinv, hcpt⟩ := hΦ
  refine ⟨fun t ht => (isHalf_actO _ _ t).1 (hsupp _ ht), k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
  · simp only [actPull]
    rw [actO_add, actO_nsmul]
    exact hinv _ ((hΛ u hue).2 hu) ((isHalf_actO _ _ u).2 hue) _
  · have hth : IsHalf e t := (isHalf_actO _ _ t).1 (hsupp _ ht)
    have h1 := hcpt _ ht
    rw [← actO_nsmul] at h1
    have hkt : IsHalf e (k • t) := fun i j => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, hth i j]
    exact (hΛ _ hkt).1 h1

theorem actsLin_mul {S T : HSp D} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} {e : AE D} {Λ : AddSubgroup (WO S T)} {p q : GA D S × GA D T} {c d : ℂ}
    (hp : ActsLin om Tm e Λ p c) (hq : ActsLin om Tm e Λ q d)
    (hsb : ∀ Φ, IsSBHalf e Λ Φ → IsSBHalf e Λ (actPull q Φ)) : ActsLin om Tm e Λ (p * q) (c * d) := by
  intro Φ hΦ
  rw [map_mul, Module.End.mul_apply, hq Φ hΦ, LinearMap.map_smul, hp _ (hsb Φ hΦ), actPull_mul, smul_smul, mul_comm d c]

theorem actsLin_of_splitLin (hSL : SplitLin D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀)
    (hfix : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e u ∨ IsHalf (cA D e) u) → heisO ψ S T u f₀ = f₀)
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm)
    {e₁ : AE D} (hs : IsSplitIdem D e₁) (h1 : e₁ * e = e₁) {g : GA D S} {h : GA D T}
    (hg : SuppAt e₁ S g) (hh : SuppAt e₁ T h) {x y : (AE D)ˣ} (hx : IsDetAt e₁ S g x) (hy : IsDetAt e₁ T h y)
    (hlat : ∀ t : WO S T, IsHalf e t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT))
    (hn : ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1) :
    ActsLin om Tm e (latAll S T ΛS ΛT) (g, h) (splitFacO χS χT x y : ℂ) := by
  obtain ⟨r, _, hact, hr1⟩ :=
    hSL ψ S T χS χT om hW ΛS ΛT hsS hsT P e he f₀ hf₀ hfix Tm hTm e₁ hs h1 g h hg hh x y hx hy
  have hr : r = 1 := hr1 hlat hn
  intro Φ hΦ
  rw [hact Φ hΦ, hr]
  simp only [Complex.ofReal_one, one_mul]
  rfl

theorem isPlaceModel_comp {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D}
    {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm)
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ)) (p : GA D S × GA D T)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T p.1 p.2 x = x) (h0 : om p f₀ = f₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ ((om p).comp Tm) where
  trans Φ hΦ x hx := by
    rw [LinearMap.comp_apply, hTm.trans Φ hΦ x hx, LinearMap.comp_apply]
    have := hW.om_heis p.1 p.2 x (Tm Φ) (hth Φ hΦ)
    rw [hfx x (Or.inl hx)] at this
    exact this
  modul Φ hΦ y hy := by
    rw [LinearMap.comp_apply, hTm.modul Φ hΦ y hy, LinearMap.comp_apply]
    have := hW.om_heis p.1 p.2 y (Tm Φ) (hth Φ hΦ)
    rw [hfx y (Or.inr hy)] at this
    exact this
  vac := by rw [LinearMap.comp_apply, hTm.vac, h0]

theorem om_fix_of_thetaAt {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D}
    {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (hθ : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (hth : ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm →
      ∀ Φ', IsSBHalf e Λ Φ' → IsThetaFunO ψ S T (Tm Φ')) (p : GA D S × GA D T)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T p.1 p.2 x = x) (h0 : om p f₀ = f₀) :
    om p f = f := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hf : f = Tm Φ := hall Tm hTm
  have h2 : f = ((om p).comp Tm) Φ := hall _ (isPlaceModel_comp hW hTm (hth Tm hTm) p hfx h0)
  rw [LinearMap.comp_apply, ← hf] at h2
  exact h2.symm

end Formalism.IndefR.Fin.LevelGroupLemmas

end
