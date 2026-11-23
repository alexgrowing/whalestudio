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

namespace GlobalTheory.ChainDesc.DownAct

theorem span_pullbackSections {X Y : Scheme.{0}} (f : X ⟶ Y) (G : Y.Modules) [G.IsQuasicoherent] {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) (T : Set Γ(G, V)) (hT : Submodule.span Γ(Y, V) T = ⊤) :
    Submodule.span Γ(X, U) ((fun s => pullbackSections f G e s) '' T : Set Γ((Scheme.Modules.pullback f).obj G, U)) = ⊤ := by
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  rw [eq_top_iff]
  intro y hy
  clear hy
  induction y using (isBaseChange_pullbackSections f G hU hV e).inductionOn with
  | zero => exact zero_mem _
  | tmul s =>
    have hs : s ∈ Submodule.span Γ(Y, V) T := hT ▸ trivial
    induction hs using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ⟨s, hs, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a b _ hb => rw [pullbackSections_smul]; exact Submodule.smul_mem _ _ hb
  | smul a b hb => exact Submodule.smul_mem _ _ hb
  | add a b ha hb => exact add_mem ha hb

set_option maxHeartbeats 1600000 in

theorem map_act : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), Lie.V.IsQuasicoherent → Om.V.IsQuasicoherent → IsSys C M → IsCov f g → ∀ (U : AffOp B.X) (S : Set (Γ(Om.V, U.1) × (C U).L 0)) (D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1)) (a : Λ), IsDown C f g U S D → Submodule.span Γ(B.X, U.1) {w | ∃ s ∈ S, s.1 = w ∧ ∃ s' ∈ S, s'.1 = (Om.ρ a : Om.V ⟶ Om.V).app _ w ∧ s'.2.1 = mv (RingHom.id _) (M a) s.2.1} = ⊤ → D.Map D (RingHom.id _) (M a) ((((pullA f.f).obj Lie).ρ a : ((pullA f.f).obj Lie).V ⟶ ((pullA f.f).obj Lie).V).app _) ((((pullA f.f).obj Om).ρ a : ((pullA f.f).obj Om).V ⟶ ((pullA f.f).obj Om).V).app _) := by
  intro O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g qL qO hC hf U S D a hD hS
  obtain ⟨l, m, hl, hm, hmap, hL, hb, hρ, hd, hp⟩ := hD
  obtain ⟨l₀, m₀, hl₀, hm₀, H⟩ := hC.2 U a
  have hU := hf.isAffineOpen U
  let l' := appLinear ((Scheme.Modules.pullback f.f).map (Lie.ρ a : Lie.V ⟶ Lie.V)) (f.f ⁻¹ᵁ U.1)
  let m' := appLinear ((Scheme.Modules.pullback f.f).map (Om.ρ a : Om.V ⟶ Om.V)) (f.f ⁻¹ᵁ U.1)
  have hll : ∀ y, l₀ (l y) = l (l' y) := fun y => by
    have hy : y ∈ Submodule.span _ _ :=
      span_pullbackSections f.f Lie.V hU U.2.1 le_rfl Set.univ Submodule.span_univ ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, -, rfl⟩ := hy
      rw [hl, hl₀, ← hl]
      exact congrArg l (pullback_map_app_pullbackSections f.f (Lie.ρ a : Lie.V ⟶ Lie.V) le_rfl s).symm
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul r y _ hy => rw [map_smulₛₗ, map_smul, map_smul, map_smulₛₗ, hy]
  refine GlobalTheory.RingChain.MapDown.map_down p h o _ _ _ _ (g U) (g U) (RingHom.id _) (RingHom.id _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    D D (C U) (C U) (M a) l m l.toAddMonoidHom m l₀ m₀ l' m' _ rfl rfl (hf.map_cst U π) hd hp
    (fun n hn x hx => (hL n hn x).2 hx) hb hmap hmap H hll (span_pullbackSections f.f Om.V hU U.2.1 le_rfl _ hS) ?_
  rintro _ ⟨_, ⟨s, hs, rfl, s', hs', e₁, e₂⟩, rfl⟩
  obtain ⟨x, hx, kx⟩ := hρ s hs
  obtain ⟨x', hx', kx'⟩ := hρ s' hs'
  refine ⟨x, x', ?_, kx, ?_⟩
  · funext i
    refine hf.2.2.1 U ?_
    have := congrFun (hx'.trans e₂) i
    rw [← hx, GlobalTheory.RingChain.MapDown.mv_apply] at this
    rw [GlobalTheory.RingChain.MapDown.mv_apply, map_sum]
    simp only [map_mul, map_intCast]
    exact this
  · rw [← kx', e₁]
    exact congrArg D.ρ (pullback_map_app_pullbackSections f.f (Om.ρ a : Om.V ⟶ Om.V) le_rfl s.1)

end GlobalTheory.ChainDesc.DownAct
