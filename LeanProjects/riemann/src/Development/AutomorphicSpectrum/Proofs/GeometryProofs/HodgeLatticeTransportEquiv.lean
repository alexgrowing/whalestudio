import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat

namespace HodgeTransport

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V V' : Type} [AddCommGroup V] [Module Ω V]
  [AddCommGroup V'] [Module Ω V'] {F F' : Type} [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
  {E : Type} [Field E] [NumberField E]

def conjE (e : V ≃ₗ[Ω] V') : (V × Module.Dual Ω V) ≃ₗ[Ω] (V' × Module.Dual Ω V') :=
  e.prodCongr e.symm.dualMap

theorem conjE_apply (e : V ≃ₗ[Ω] V') (y : V × Module.Dual Ω V) :
    conjE e y = (e y.1, y.2 ∘ₗ e.symm.toLinearMap) := rfl

theorem conjE_symm_apply (e : V ≃ₗ[Ω] V') (y : V' × Module.Dual Ω V') :
    (conjE e).symm y = (e.symm y.1, y.2 ∘ₗ e.toLinearMap) := rfl

def cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) : 𝓞 E →+* Module.End Ω F' :=
  (g.conjRingEquiv : Module.End Ω F →+* Module.End Ω F').comp ρ

theorem cj_apply (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (a : 𝓞 E) (y : F') :
    cj g ρ a y = g (ρ a (g.symm y)) := rfl

theorem mem_map_equiv (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (p : Cpt ξ) (y : F') :
    y ∈ M.map g.toLinearMap p ↔ g.symm y ∈ M p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem map_symm_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') :
    (M.map g.toLinearMap).map g.symm.toLinearMap = M := by
  funext p
  ext y
  rw [mem_map_equiv, mem_map_equiv]
  simp

theorem isFrameAt_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F} {p : Cpt ξ}
    (h : M.IsFrameAt b p) : (M.map g.toLinearMap).IsFrameAt (g ∘ b) p := by
  refine ⟨(LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1, ?_⟩
  change Submodule.map _ (M p) = _
  rw [h.2, Submodule.map_span, Set.range_comp]
  rfl

theorem isFrameAt_map_iff {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F'} {p : Cpt ξ} :
    (M.map g.toLinearMap).IsFrameAt b p ↔ M.IsFrameAt (g.symm ∘ b) p := by
  constructor
  · intro h
    have := isFrameAt_map g.symm h
    rwa [map_symm_map] at this
  · intro h
    have := isFrameAt_map g h
    have e : g ∘ g.symm ∘ b = b := by funext i; simp
    rwa [e] at this

theorem detLat_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') {r : ℕ} (u : Fin r → F') :
    detLat (M.map g.toLinearMap) u = detLat M (g.symm ∘ u) := by
  funext p
  simp only [detLat]
  congr 1
  ext t
  refine exists_congr fun A => and_congr_left fun _ => ?_
  rw [isFrameAt_map_iff]
  have e : (g.symm ∘ fun i => ∑ j, A i j • u j) = fun i => ∑ j, A i j • (g.symm ∘ u) j := by
    funext i
    simp
  rw [e]

theorem isFreeOn_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {ρ : 𝓞 E →+* Module.End Ω F} {p : Cpt ξ} {N : ℕ}
    {t : Fin N → F} (h : HT.IsFreeOn ρ (M p) t) :
    HT.IsFreeOn (cj g ρ) (M.map g.toLinearMap p) (g ∘ t) := by
  have e : (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      cj g ρ (RingOfIntegers.basis E q.2) ((g ∘ t) q.1)) =
      g ∘ fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        ρ (RingOfIntegers.basis E q.2) (t q.1) := by
    funext q
    simp [cj_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact (LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1
  · have e2 : ((M.map g.toLinearMap p : Submodule _ F') : Set F') = g '' (M p : Set F) := rfl
    rw [e2]
    have := Submodule.map_span g.toLinearMap (M p : Set F)
    rw [h.2.1, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm
  · rw [e]
    change Submodule.map _ (M p) = _
    rw [h.2.2, Submodule.map_span, Set.range_comp]
    rfl

theorem eigProj_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    HT.eigProj (cj g ρ) σ y = g (HT.eigProj ρ σ (g.symm y)) := by
  simp [HT.eigProj, LinearMap.sum_apply, cj_apply, map_sum]

theorem mem_eigSp_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    y ∈ HT.eigSp (cj g ρ) σ ↔ g.symm y ∈ HT.eigSp ρ σ := by
  rw [HT.LatBasic.mem_eigSp, HT.LatBasic.mem_eigSp]
  refine forall_congr' fun a => ?_
  rw [cj_apply, ← map_smul, LinearEquiv.eq_symm_apply]

theorem eigQuot_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) :
    (M.map g.toLinearMap).map (HT.eigProj (cj g ρ) σ) = (M.map (HT.eigProj ρ σ)).map g.toLinearMap := by
  funext p
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩

variable {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {ρ' : 𝓞 E →+* Module.End Ω V'} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

def transport (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v)) :
    HodgeLat (L.map e.toLinearMap) ρ' bar r where
  ρH := cj (conjE e) 𝓗.ρH
  HL := 𝓗.HL.map (conjE e).toLinearMap
  act_fst a y := by
    rw [cj_apply, conjE_apply, 𝓗.act_fst, h, conjE_symm_apply]
    simp
  act_inr a φ := by
    rw [cj_apply, conjE_symm_apply]
    simp only [map_zero]
    rw [𝓗.act_inr, conjE_apply]
    refine Prod.ext (by simp) (LinearMap.ext fun x => ?_)
    simp [h]
  map_fst := by
    funext p
    conv_rhs => rw [← 𝓗.map_fst]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  comap_inr := by
    funext p
    ext φ
    have h1 : (φ ∈ (𝓗.HL.map (conjE e).toLinearMap).comap (LinearMap.inr Ω V' (Module.Dual Ω V')) p) ↔
        ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p := by
      change ((0, φ) : V' × Module.Dual Ω V') ∈ 𝓗.HL.map (conjE e).toLinearMap p ↔ _
      rw [mem_map_equiv, conjE_symm_apply]
      simp
    have h2 : ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p ↔
        φ ∘ₗ e.toLinearMap ∈ L.dual p := by
      rw [← 𝓗.comap_inr]
      rfl
    rw [h1, h2]
    change (∀ x ∈ L p, φ (e x) ∈ regAt ξ p) ↔ ∀ x ∈ L.map e.toLinearMap p, φ x ∈ regAt ξ p
    constructor
    · rintro hφ _ ⟨z, hz, rfl⟩
      exact hφ z hz
    · intro hφ z hz
      exact hφ _ ⟨z, hz, rfl⟩
  free p := by
    obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
    exact ⟨U, hU, conjE e ∘ x, fun q hq => isFreeOn_map (conjE e) (hx q hq)⟩
  vb := by
    rw [← e.finrank_eq]
    intro p hp
    obtain ⟨U, hU, b, hb, hf⟩ := 𝓗.vb p hp
    refine ⟨U, hU, e ∘ b, ?_, fun q hq hqU => isFrameAt_map e (hf q hq hqU)⟩
    rw [Set.range_comp]
    have := Submodule.map_span e.toLinearMap (Set.range b)
    rw [hb, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm

theorem transport_degZero (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v))
    (σ : E →+* Ω) (ϖ : Ω) (hd : 𝓗.DegZero σ ϖ) : (transport e 𝓗 h).DegZero σ ϖ := by
  intro u hu hsp
  have hq : (transport e 𝓗 h).quot σ = (𝓗.quot σ).map (conjE e).toLinearMap :=
    eigQuot_map 𝓗.HL (conjE e) 𝓗.ρH σ
  rw [hq, detLat_map]
  refine hd _ ((LinearMap.linearIndependent_iff (conjE e).symm.toLinearMap (LinearEquiv.ker _)).2 hu) ?_
  ext y
  have h1 : Set.range ((conjE e).symm ∘ u) = (conjE e).symm.toLinearMap '' Set.range u := Set.range_comp _ _
  rw [h1, ← Submodule.map_span, hsp]
  change _ ↔ y ∈ HT.eigSp 𝓗.ρH σ
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_eigSp_cj (conjE e) 𝓗.ρH σ z).1 hz
  · intro hy
    refine ⟨conjE e y, (mem_eigSp_cj (conjE e) 𝓗.ρH σ _).2 (by simpa using hy), by simp⟩

end HodgeTransport

theorem hodgeLat_transport : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [Field E] [NumberField E] (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (e : V ≃ₗ[Ω] V') (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r), (∀ a v, e (ρ a v) = ρ' a (e v)) → ∃ 𝓗' : HodgeLat (L.map e.toLinearMap) ρ' bar r, ∀ σ ϖ, 𝓗.DegZero σ ϖ → 𝓗'.DegZero σ ϖ := by
  intro X Ω _ ξ E _ _ V V' _ _ _ _ e L ρ ρ' bar r 𝓗 h
  exact ⟨HodgeTransport.transport e 𝓗 h, fun σ ϖ hd => HodgeTransport.transport_degZero e 𝓗 h σ ϖ hd⟩

end GlobalTheory.CompanionTheory.Ar.Flat
