import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective

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

noncomputable section

namespace GlobalTheory.ChainDesc.UpSmallJ

theorem mv_one {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {h : ℕ} (x : Fin h → A) :
    mv φ 1 x = piMap φ (Fin h) x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

theorem exists_lift {A A' : Type} [CommRing A] [CommRing A'] {p h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type}
    [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] {π' : A'} {γ' : ℕ → A'} {Lie' Om' : Type}
    [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om'] [Module A' Om'] {C : RChain p A h o π γ Lie Om}
    {C' : RChain p A' h o π' γ' Lie' Om'} {φ : A →+* A'} {l : Lie → Lie'} {m : Om → Om'} (k : C.Map C' φ 1 l m)
    (s : Lie) (s' : Lie') (e : l s = s') (y : C.L 0) (hy : C.j s = Submodule.Quotient.mk y) :
    ∃ y' : C'.L 0, y'.1 = piMap φ (Fin h) y.1 ∧ C'.j s' = Submodule.Quotient.mk y' :=
  ⟨⟨_, k.mem 0 y.1 y.2⟩, mv_one φ y.1, e ▸ k.j s y ⟨_, k.mem 0 y.1 y.2⟩ rfl hy⟩

set_option maxHeartbeats 1600000 in

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : ℕ → B'.X.Modules) (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) (Q : B'.X.Modules) (t : E 0 ⟶ Q) (j : ((pullA f.f).obj Lie).V ⟶ Q), Lie.V.IsQuasicoherent → IsSys C M → IsCov f g → IsLatOf C f g ι → ∀ (U : AffOp B.X) (S : Set (Γ(Om.V, U.1) × (C U).L 0)) (D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1)), IsDown C f g U S D → JOn (ι 0) D t j → ∀ U' : AffOp B.X, U'.1 ≤ U.1 → JUp C f g U' (ι 0) t j := by
  intro O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g E ι Q t j hq hS hc hι U S D hD hJ U' hle s
  have hfit : D.L 0 = latOf (ι 0) _ := hD.fits hι 0 (Nat.zero_le _)
  obtain ⟨l, m, hl, -, hM, -⟩ := hD
  obtain ⟨-, l', m', hl', -, hM'⟩ := hS.1 U U' hle
  letI := resAlgebra hle
  letI := resModule Lie.V hle
  haveI := res_isScalarTower Lie.V hle
  refine (isBaseChange_resLinear Lie.V U.2.1 U'.2.1 hle).inductionOn s _ ?_ (fun s₀ => ?_) (fun a s k => ?_)
    (fun s s' k k' => ?_)
  · refine ⟨0, 0, by rw [map_zero, map_zero]; rfl, by rw [TensorProduct.tmul_zero, map_zero]; rfl, ?_⟩
    letI := appLEModule f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_rfl : f.f ⁻¹ᵁ U'.1 ≤ _)
    rw [map_zero, map_zero, map_zero]
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (D.j (pullbackSections f.f Lie.V le_rfl s₀))
    obtain ⟨x, hx⟩ : y.1 ∈ latOf (ι 0) _ := hfit.le y.2
    have h1 := hJ (pullbackSections f.f Lie.V le_rfl s₀) x y hx.symm hy.symm
    obtain ⟨y₁, e₁, h2⟩ := exists_lift hM _ _ (hl s₀) y hy.symm
    obtain ⟨y₂, e₂, h3⟩ := exists_lift hM' _ _ (hl' s₀) y₁ h2
    refine ⟨resM (E 0) (f.f.preimage_mono hle) x, y₂, ?_, h3, ?_⟩
    · rw [e₂, e₁, crd_resM, hx]
      funext i
      exact (hc.2.2.2.2 U U' hle _).symm
    · have e : pullbackSections f.f Lie.V le_rfl (resLinear Lie.V hle s₀) =
          resM _ (f.f.preimage_mono hle) (pullbackSections f.f Lie.V le_rfl s₀) :=
        (pullbackSections_res f.f Lie.V le_rfl hle s₀).trans (res_pullbackSections f.f Lie.V le_rfl _ s₀).symm
      rw [e]
      exact (hom_app_res j _ _).trans ((congrArg _ h1).trans (hom_app_res t _ _).symm)
  · obtain ⟨x, y, h1, h2, h3⟩ := k
    refine ⟨(f.f.app U'.1).hom a • x, algebraMap Γ(B.X, U'.1) U'.Bp a • y, ?_, ?_, ?_⟩
    · rw [map_smul, LinearMap.map_smulₛₗ, hc.2.2.2.1, ← h1]; rfl
    · rw [TensorProduct.tmul_smul, ← algebraMap_smul U'.Bp a, map_smul, h2]; rfl
    · rw [pullbackSections_smul, Scheme.Hom.appLE_eq_app]
      exact (j.app_smul _ _).trans ((congrArg _ h3).trans (t.app_smul _ _).symm)
  · obtain ⟨x, y, h1, h2, h3⟩ := k
    obtain ⟨x', y', h1', h2', h3'⟩ := k'
    refine ⟨x + x', y + y', ?_, ?_, ?_⟩
    · rw [map_add, map_add, ← h1, ← h1']; rfl
    · rw [TensorProduct.tmul_add, map_add, h2, h2']; rfl
    · letI := appLEModule f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_rfl : f.f ⁻¹ᵁ U'.1 ≤ _)
      rw [map_add, map_add, map_add, h3, h3']

end GlobalTheory.ChainDesc.UpSmallJ

end
