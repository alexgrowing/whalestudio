import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulMemOfMemSpanImage

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

namespace GlobalTheory.ChainDesc.UpLocJ

theorem mv_one {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {h : ℕ} (x : Fin h → A) :
    mv φ 1 x = piMap φ (Fin h) x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

theorem piMap_mem_baseOf {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {ϖ : A} {h : ℕ} {v : Fin h → A}
    (hv : v ∈ baseOf ϖ h) : piMap φ (Fin h) v ∈ baseOf (φ ϖ) h := by
  obtain ⟨w, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem_pointwise_smul _ _ _ trivial

theorem baseOf_le_span {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (ϖ : A) (h : ℕ) :
    baseOf (φ ϖ) h ≤ Submodule.span A' (piMap φ (Fin h) '' (baseOf ϖ h : Set (Fin h → A))) := by
  intro v hv
  obtain ⟨w, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hv
  have e : φ ϖ • w = ∑ i, w i • piMap φ (Fin h) (ϖ • Pi.single i 1) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, apply_ite φ, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨_, Submodule.smul_mem_pointwise_smul _ _ _ trivial, rfl⟩)

theorem sub_mem_of_map {A A' : Type} [CommRing A] [CommRing A'] {p h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type}
    [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] {π' : A'} {γ' : ℕ → A'} {Lie' Om' : Type}
    [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om'] [Module A' Om'] {C : RChain p A h o π γ Lie Om}
    {C' : RChain p A' h o π' γ' Lie' Om'} {φ : A →+* A'} {l : Lie → Lie'} {m : Om → Om'} (k : C.Map C' φ 1 l m)
    {y : Lie} {y' : Lie'} (e : l y = y') {x : C.L 0} {x' : C'.L 0} (hx : Submodule.Quotient.mk x = C.j y)
    (hx' : C'.j y' = Submodule.Quotient.mk x') : piMap φ (Fin h) x.1 - x'.1 ∈ baseOf π' h := by
  have e1 := k.j y x ⟨_, k.mem 0 _ x.2⟩ rfl hx.symm
  rw [e, hx'] at e1
  have e2 := (Submodule.Quotient.eq _).1 e1.symm
  rw [← mv_one]
  exact e2

theorem app_pull_resM {X Y : Scheme.{0}} (f : X ⟶ Y) {F : Y.Modules} {Q : X.Modules}
    (j : (Scheme.Modules.pullback f).obj F ⟶ Q) {U U' : Y.Opens} (hle : U' ≤ U) (s : Γ(F, U)) :
    j.app _ (pullbackSections f F le_rfl (resM F hle s)) =
      resM Q (f.preimage_mono hle) (j.app _ (pullbackSections f F le_rfl s)) := by
  rw [← GlobalTheory.Twist.app_resM]
  congr 1
  exact (pullbackSections_res f F le_rfl hle s).trans
    (res_pullbackSections f F le_rfl (f.preimage_mono hle) s).symm

theorem res_cstBp {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : GlobalTheory.Vert.Model O}
    {U U' : AffOp B.X} (hle : U'.1 ≤ U.1) (a : Γ(B.X, ⊤)) : AffOp.res hle (cstBp U a) = cstBp U' a := by
  refine Subtype.ext (congrArg (algebraMap B.X.functionField (GlobalTheory.GroupBplus.Kbar B.X)) ?_)
  exact (B.X.presheaf.germ_res_apply (homOfLE le_top) _ _ a).trans
    (B.X.presheaf.germ_res_apply (homOfLE le_top) _ _ a).symm

theorem sub_mem_trans {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {h : ℕ} {N : Submodule A' (Fin h → A')}
    {a b : Fin h → A} {c c' : Fin h → A'} (h1 : piMap φ (Fin h) a - c ∈ N) (e : c = c')
    (h2 : c' - piMap φ (Fin h) b ∈ N) : piMap φ (Fin h) (a - b) ∈ N := by
  have k := N.add_mem h1 (e ▸ h2)
  rwa [sub_add_sub_cancel, ← map_sub] at k

theorem crd_sub_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : GlobalTheory.Vert.Model O} {Λ : Type}
    [CommRing Λ] {h : ℕ} {π : Γ(B.X, ⊤)} {M : Λ →+* Matrix (Fin h) (Fin h) ℤ} {f : GlobalTheory.Vert.Model.Hom B' B}
    {g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp} {E : B'.X.Modules} {ι : E ⟶ freeModule B'.X (Fin h)}
    {Q : AM B' Λ} {t : E ⟶ Q.V} (hC : IsCov f g) (hQ : IsQuot M ι (baseOn h (f.f.appTop π)) Q t) {U U' : AffOp B.X}
    (hle : U'.1 ≤ U.1) {x : Γ(E, f.f ⁻¹ᵁ U.1)} {x' : Γ(E, f.f ⁻¹ᵁ U'.1)}
    (e : t.app _ x' = resM Q.V (f.f.preimage_mono hle) (t.app _ x)) :
    piMap (g U') (Fin h) (crd ι _ x') - piMap (AffOp.res hle) (Fin h) (piMap (g U) (Fin h) (crd ι _ x)) ∈
      baseOf (cstBp U' π) h := by
  have hp := f.f.preimage_mono hle
  have e3 : t.app _ (x' - resM E hp x) = 0 := by
    rw [map_sub, GlobalTheory.Twist.app_resM, e, sub_self]
  have e4 := piMap_mem_baseOf (g U') (((hQ.2 _ (hC.isAffineOpen U')).2.1 _).1 e3)
  have e5 : piMap (g U') (Fin h) (crd ι _ (x' - resM E hp x)) =
      piMap (g U') (Fin h) (crd ι _ x') - piMap (AffOp.res hle) (Fin h) (piMap (g U) (Fin h) (crd ι _ x)) := by
    rw [(crd ι _).map_sub, (piMap (g U') (Fin h)).map_sub, crd_resM]
    exact congrArg _ (funext fun i => hC.2.2.2.2 U U' hle _)
  rw [← hC.map_cst U' π, ← e5]
  exact e4

theorem exists_affOp_le {X : Scheme.{0}} (U U₁ : AffOp X) {z : X} (hz : z ∈ U.1) (hz₁ : z ∈ U₁.1) :
    ∃ U' : AffOp X, z ∈ U'.1 ∧ U'.1 ≤ U.1 ∧ U'.1 ≤ U₁.1 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show z ∈ ((U.1 ⊓ U₁.1 : X.Opens) : Set X) from ⟨hz, hz₁⟩) (U.1 ⊓ U₁.1).2
  exact ⟨⟨V, hV, ⟨⟨z, hzV⟩⟩⟩, hzV, fun w hw => (hle hw).1, fun w hw => (hle hw).2⟩

theorem res_sub_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {B B' : GlobalTheory.Vert.Model O}
    {Λ : Type} [CommRing Λ] {h o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)}
    {M : Λ →+* Matrix (Fin h) (Fin h) ℤ} {C : ChainsBp p h o Lie Om π γ} {f : GlobalTheory.Vert.Model.Hom B' B}
    {g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp} {E : B'.X.Modules} {ι : E ⟶ freeModule B'.X (Fin h)}
    {Q : AM B' Λ} {t : E ⟶ Q.V} {j : (Scheme.Modules.pullback f.f).obj Lie.V ⟶ Q.V} (hS : IsSys C M) (hC : IsCov f g)
    (hQ : IsQuot M ι (baseOn h (f.f.appTop π)) Q t) {U U' : AffOp B.X} (hle : U'.1 ≤ U.1) (hU' : JUp C f g U' ι t j)
    {s : Γ(Lie.V, U.1)} {x : Γ(E, f.f ⁻¹ᵁ U.1)} (hx : t.app _ x = j.app _ (pullbackSections f.f Lie.V le_rfl s))
    {y : (C U).L 0} (hy : Submodule.Quotient.mk y = (C U).j (1 ⊗ₜ s)) :
    piMap (AffOp.res hle) (Fin h) (y.1 - piMap (g U) (Fin h) (crd ι _ x)) ∈ baseOf (cstBp U' π) h := by
  obtain ⟨x', y', hy', hj', ht'⟩ := hU' (resM Lie.V hle s)
  obtain ⟨-, l, m, hl, -, hM⟩ := hS.1 U U' hle
  have e2 := sub_mem_of_map hM (hl s) hy hj'
  have e3 : t.app _ x' = resM Q.V (f.f.preimage_mono hle) (t.app _ x) := by
    rw [hx, ← ht']
    exact app_pull_resM f.f j hle s
  exact sub_mem_trans (AffOp.res hle) e2 hy' (crd_sub_mem hC hQ hle e3)

theorem jUp_of_local : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : ℕ → B'.X.Modules) (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) (Q : AM B' Λ) (t : E 0 ⟶ Q.V) (j : (pullA f.f).obj Lie ⟶ Q), IsSys C M → IsCov f g → IsLatOf C f g ι → IsQuot M (ι 0) (baseOn h (f.f.appTop π)) Q t → (∀ z : B.X, ∃ U : AffOp B.X, z ∈ U.1 ∧ ∀ U' : AffOp B.X, U'.1 ≤ U.1 → JUp C f g U' (ι 0) t j.hom) → ∀ U : AffOp B.X, JUp C f g U (ι 0) t j.hom := by
  intro O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g E ι Q t j hS hC hL hQ hloc U s
  obtain ⟨x, hx⟩ := (hQ.2 _ (hC.isAffineOpen U)).1 (j.hom.app _ (pullbackSections f.f Lie.V le_rfl s))
  obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ ((C U).j (1 ⊗ₜ s))
  have hy : piMap (g U) (Fin h) (crd (ι 0) _ x) ∈ (C U).L 0 := by
    have h1 : crd (ι 0) _ x ∈ latOf (ι 0) (f.f ⁻¹ᵁ U.1) := ⟨x, rfl⟩
    rw [((hL 0).2.2 U).1, Nat.zero_min] at h1
    exact h1
  refine ⟨x, ⟨_, hy⟩, rfl, hy₀.symm.trans ((Submodule.Quotient.eq _).2 ?_), hx.symm⟩
  change y₀.1 - piMap (g U) (Fin h) (crd (ι 0) _ x) ∈ baseOf (cstBp U π) h
  refine GlobalTheory.ChainDesc.mem_of_locally_mem_span B.X U h _ _ fun z hz => ?_
  obtain ⟨U₁, hz₁, hU₁⟩ := hloc z
  obtain ⟨U', hz', h1, h2⟩ := exists_affOp_le U U₁ hz hz₁
  refine ⟨U', h1, hz', baseOf_le_span _ _ _ ?_⟩
  rw [res_cstBp]
  exact res_sub_mem hS hC hQ h1 (hU₁ U' h2) hx hy₀

end GlobalTheory.ChainDesc.UpLocJ
