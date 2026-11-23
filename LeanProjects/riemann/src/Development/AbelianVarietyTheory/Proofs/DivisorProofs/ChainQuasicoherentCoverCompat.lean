import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBaseOf

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc.DownRes

theorem span_pullbackSections {X Y : Scheme.{0}} (f : X ⟶ Y) (G : Y.Modules) [G.IsQuasicoherent] {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (T : Set Γ(G, V))
    (hT : Submodule.span Γ(Y, V) T = ⊤) :
    Submodule.span Γ(X, U) ((fun s => pullbackSections f G e s) '' T) = ⊤ := by
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  have key : ∀ s : Γ(G, V), pullbackSections f G e s ∈
      Submodule.span Γ(X, U) ((fun s => pullbackSections f G e s) '' T) := fun s => by
    have hs : s ∈ Submodule.span Γ(Y, V) T := hT ▸ trivial
    induction hs using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a b _ hb => rw [pullbackSections_smul]; exact Submodule.smul_mem _ _ hb
  refine eq_top_iff.2 fun y _ => ?_
  refine (isBaseChange_pullbackSections f G hU hV e).inductionOn y (fun y => y ∈ Submodule.span Γ(X, U) ((fun s => pullbackSections f G e s) '' T)) (zero_mem _) key
    (fun a n hn => Submodule.smul_mem _ _ hn) (fun a b ha hb => add_mem ha hb)

noncomputable def resSl {X : Scheme.{0}} (F : X.Modules) {U V : X.Opens} (h : V ≤ U) : Γ(F, U) →ₛₗ[resG X h] Γ(F, V) where
  toFun := resM F h
  map_add' := map_add _
  map_smul' := GlobalTheory.Twist.resM_smul h

theorem resM_pull {X Y : Scheme.{0}} (f : X ⟶ Y) (G : Y.Modules) {V V' : Y.Opens} (h : V' ≤ V) (s : Γ(G, V)) :
    resM _ (f.preimage_mono h) (pullbackSections f G le_rfl s) = pullbackSections f G le_rfl (resM G h s) :=
  (res_pullbackSections f G le_rfl _ s).trans (pullbackSections_res f G le_rfl h s).symm

theorem sq_of_span {A₁ A₂ B₁ B₂ L₁ L₂ N₁ N₂ : Type} [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    [AddCommGroup L₁] [Module A₁ L₁] [AddCommGroup L₂] [Module A₂ L₂] [AddCommGroup N₁] [Module B₁ N₁] [AddCommGroup N₂]
    [Module B₂ N₂] {g₁ : A₁ →+* B₁} {g₂ : A₂ →+* B₂} {φ' : A₁ →+* A₂} {φ : B₁ →+* B₂} (hc : ∀ a, φ (g₁ a) = g₂ (φ' a))
    (l₁ : L₁ →ₛₗ[g₁] N₁) (l₂ : L₂ →ₛₗ[g₂] N₂) (l' : L₁ →ₛₗ[φ'] L₂) (l : N₁ →ₛₗ[φ] N₂) {T : Set L₁}
    (hT : Submodule.span A₁ T = ⊤) (k : ∀ y ∈ T, l (l₁ y) = l₂ (l' y)) (y : L₁) : l (l₁ y) = l₂ (l' y) := by
  have hy : y ∈ Submodule.span A₁ T := hT ▸ trivial
  induction hy using Submodule.span_induction with
  | mem w hw => exact k w hw
  | zero => simp only [map_zero]
  | add a b _ _ ha hb => simp only [map_add, ha, hb]
  | smul a b _ hb => simp only [map_smulₛₗ, hb, hc]

set_option maxHeartbeats 800000 in

theorem down_res : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), Lie.V.IsQuasicoherent → Om.V.IsQuasicoherent → IsSys C M → IsCov f g → ∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (S : Set (Γ(Om.V, U.1) × (C U).L 0)) (S' : Set (Γ(Om.V, U'.1) × (C U').L 0)) (D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1)) (D' : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U'.1)), IsDown C f g U S D → IsDown C f g U' S' D' → Submodule.span Γ(B.X, U.1) {w | ∃ s ∈ S, s.1 = w ∧ ∃ s' ∈ S', s'.1 = resM Om.V hle w ∧ s'.2.1 = piMap (AffOp.res hle) (Fin h) s.2.1} = ⊤ → ResMap (f.f.preimage_mono hle) D D' := by
  intro O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g hL hO hS hC U U' hle S S' D D' k k' hsp
  obtain ⟨l₁, m₁, hl₁, -, H₁, -, hb, hρ₁, -, -⟩ := k
  obtain ⟨l₂, m₂, hl₂, -, H₂, hm, -, hρ₂, hd, hp⟩ := k'
  obtain ⟨-, l, m, hl, -, H⟩ := hS.1 U U' hle
  have hc : ∀ a, AffOp.res hle (g U a) = g U' (resG B'.X (f.f.preimage_mono hle) a) := fun a =>
    (hC.2.2.2.2 U U' hle a).symm
  unfold ResMap
  refine GlobalTheory.RingChain.MapDown.map_down p h o _ _ _ _ (g U) (g U') (resG B'.X (f.f.preimage_mono hle)) (AffOp.res hle)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D D' (C U) (C U') 1 l₁ m₁ l₂.toAddMonoidHom m₂ l m (resM ((pullA f.f).obj Lie).V (f.f.preimage_mono hle))
    (resSl _ (f.f.preimage_mono hle)) _ (RingHom.ext hc) ?_ (hC.map_cst U' π) hd hp (fun n hn x => (hm n hn x).2) hb
    H₁ H₂ H ?_ (span_pullbackSections f.f Om.V (hC.isAffineOpen U) U.2.1 le_rfl _ hsp) ?_
  · exact res_res_ring _ _ _
  · refine sq_of_span hc l₁ l₂ (resSl _ (f.f.preimage_mono hle)) l (span_pullbackSections f.f Lie.V (hC.isAffineOpen U)
      U.2.1 le_rfl _ Submodule.span_univ) ?_
    rintro _ ⟨s, -, rfl⟩
    exact (congrArg l (hl₁ s)).trans ((hl s).trans ((hl₂ _).symm.trans (congrArg l₂ (resM_pull f.f Lie.V hle s).symm)))
  · intro w hw
    obtain ⟨w₀, ⟨s, hs, e₀, s', hs', e₁, e₂⟩, ew⟩ := hw
    subst e₀
    subst ew
    obtain ⟨x, hx, kx⟩ := hρ₁ s hs
    obtain ⟨x', hx', kx'⟩ := hρ₂ s' hs'
    refine ⟨x, x', ?_, kx, ?_⟩
    · rw [GlobalTheory.RingChain.MapDown.mv_one]
      funext i
      refine hC.2.2.1 U' ?_
      rw [← hc]
      have a := congrFun (hx'.trans e₂) i
      rw [← hx] at a
      exact a
    · rw [e₁] at kx'
      exact (congrArg D'.ρ (resM_pull f.f Om.V hle s.1)).trans kx'

end GlobalTheory.ChainDesc.DownRes
