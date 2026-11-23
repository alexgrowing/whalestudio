import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulMemOfMemSpanImage

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

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

namespace GlobalTheory.ChainDesc.RhoLocal

section Ring

variable {A A' : Type} [CommRing A] [CommRing A'] {p h o : ℕ} {π : A} {γ : ℕ → A} {Lie Om : Type} [AddCommGroup Lie]
  [Module A Lie] [AddCommGroup Om] [Module A Om]

def imJ (C : RChain p A h o π γ Lie Om) : Submodule A (Fin h → A) :=
  ((LinearMap.range C.j).comap (Submodule.mkQ _)).map (C.L 0).subtype

theorem mem_imJ (C : RChain p A h o π γ Lie Om) (y : C.L 0) :
    y.1 ∈ imJ C ↔ (Submodule.Quotient.mk y : Qt (C.L 0) (baseOf π h)) ∈ LinearMap.range C.j :=
  ⟨fun ⟨_, h1, h2⟩ => (Subtype.ext h2 : _ = y) ▸ h1, fun k => ⟨y, k, rfl⟩⟩

theorem base_le_imJ (C : RChain p A h o π γ Lie Om) : baseOf π h ≤ imJ C := fun x hx =>
  (mem_imJ C ⟨x, C.base_le 0 hx⟩).2 (by
    rw [(Submodule.Quotient.mk_eq_zero _).2 (show (⟨x, C.base_le 0 hx⟩ : C.L 0) ∈ (baseOf π h).comap (C.L 0).subtype from hx)]
    exact zero_mem _)

theorem mk_mk_eq_iff (C : RChain p A h o π γ Lie Om) (y y' : C.L 0) :
    (Submodule.Quotient.mk (Submodule.Quotient.mk y) : Qt (C.L 0) (baseOf π h) ⧸ LinearMap.range C.j) =
      Submodule.Quotient.mk (Submodule.Quotient.mk y') ↔ y.1 - y'.1 ∈ imJ C := by
  rw [Submodule.Quotient.eq, ← Submodule.Quotient.mk_sub, ← mem_imJ]
  rfl

theorem imJ_le (C : RChain p A h o π γ Lie Om) (S : Submodule A (Fin h → A)) (hb : baseOf π h ≤ S) (G : Set Lie)
    (hG : Submodule.span A G = ⊤) (k : ∀ s ∈ G, ∃ y : C.L 0, C.j s = Submodule.Quotient.mk y ∧ y.1 ∈ S) : imJ C ≤ S := by
  have H : LinearMap.range C.j ≤ (S.comap (C.L 0).subtype).map (Submodule.mkQ _) := by
    rw [← Submodule.map_top, ← hG, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨y, h1, h2⟩ := k s hs
    exact ⟨y, h2, h1.symm⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨y', h1, h2⟩ := H hy
  have h3 : y'.1 - y.1 ∈ baseOf π h := (Submodule.Quotient.eq ((baseOf π h).comap (C.L 0).subtype)).1 h2
  simpa using S.sub_mem h1 (hb h3)

theorem mv_one (φ : A →+* A') (x : Fin h → A) : mv φ 1 x = piMap φ (Fin h) x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

theorem piMap_mem_baseOf (φ : A →+* A') {x : Fin h → A} (hx : x ∈ baseOf π h) :
    piMap φ (Fin h) x ∈ baseOf (φ π) h := by
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  rw [map_smulₛₗ]
  exact Submodule.smul_mem_pointwise_smul _ _ _ trivial

theorem baseOf_le_span (φ : A →+* A') (N : Submodule A (Fin h → A)) (hN : baseOf π h ≤ N) :
    baseOf (φ π) h ≤ Submodule.span A' (piMap φ (Fin h) '' (N : Set (Fin h → A))) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
  have e : φ π • y = ∑ i, y i • piMap φ (Fin h) (π • Pi.single i 1) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, apply_ite φ, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨_, hN (Submodule.smul_mem_pointwise_smul _ _ _ trivial), rfl⟩)

variable {π' : A'} {γ' : ℕ → A'} {Lie' Om' : Type} [AddCommGroup Lie'] [Module A' Lie'] [AddCommGroup Om'] [Module A' Om']
  {C : RChain p A h o π γ Lie Om} {C' : RChain p A' h o π' γ' Lie' Om'} {φ : A →+* A'} {l : Lie → Lie'} {m : Om → Om'}

theorem map_j (k : C.Map C' φ 1 l m) (s : Lie) (s' : Lie') (hs : l s = s') : ∃ y : C'.L 0,
    C'.j s' = Submodule.Quotient.mk y ∧ y.1 ∈ Submodule.span A' (piMap φ (Fin h) '' (imJ C : Set (Fin h → A))) := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (C.j s)
  exact ⟨⟨_, k.mem 0 y.1 y.2⟩, hs ▸ k.j _ y ⟨_, k.mem 0 y.1 y.2⟩ rfl hy.symm,
    Submodule.subset_span ⟨y.1, (mem_imJ _ _).2 ⟨_, hy.symm⟩, (mv_one _ _).symm⟩⟩

theorem map_ρ (k : C.Map C' φ 1 l m) (s : Om) (s' : Om') (hs : m s = s') (y : C.L 0) (y' : C'.L 0)
    (hy : C.ρ s = Submodule.Quotient.mk (Submodule.Quotient.mk y))
    (hy' : C'.ρ s' = Submodule.Quotient.mk (Submodule.Quotient.mk y')) (x : Fin h → A)
    (hx : y'.1 - piMap φ (Fin h) x ∈ imJ C') : piMap φ (Fin h) (y.1 - x) ∈ imJ C' := by
  have h4 := k.ρ _ y ⟨_, k.mem 0 y.1 y.2⟩ rfl hy
  rw [hs, hy'] at h4
  have h9 := add_mem ((mk_mk_eq_iff _ _ _).1 h4.symm) hx
  rw [sub_add_sub_cancel] at h9
  rw [map_sub, ← mv_one φ y.1]
  exact h9

def IsVal (C : RChain p A h o π γ Lie Om) (s : Om) (y : C.L 0) : Prop :=
  C.ρ s = Submodule.Quotient.mk (Submodule.Quotient.mk y)

theorem exists_ρ (C : RChain p A h o π γ Lie Om) (s : Om) :
    ∃ y : C.L 0, IsVal C s y := by
  obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (C.ρ s)
  obtain ⟨y₀, rfl⟩ := Submodule.Quotient.mk_surjective _ y₁
  exact ⟨y₀, hy₁.symm⟩

end Ring

section Geo

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B B' : Vert.Model O} {Λ : Type} [CommRing Λ]
  {p h o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)} {C : ChainsBp p h o Lie Om π γ}
  {M : Λ →+* Matrix (Fin h) (Fin h) ℤ} {f : Vert.Model.Hom B' B} {g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp}

theorem res_cstBp {U U' : AffOp B.X} (hle : U'.1 ≤ U.1) (a : Γ(B.X, ⊤)) : AffOp.res hle (cstBp U a) = cstBp U' a := by
  have e : resG B.X le_top a = resG B.X hle (resG B.X (le_top : U.1 ≤ ⊤) a) := (res_res_ring le_top hle a).symm
  rw [cstBp, cstBp, e]
  exact Subtype.ext
    (congrArg (algebraMap B.X.functionField (GlobalTheory.GroupBplus.Kbar B.X)) (B.X.presheaf.germ_res_apply (homOfLE hle) _ _ _).symm)

theorem span_tmul_resM (F : B.X.Modules) [F.IsQuasicoherent] {U U' : AffOp B.X} (hle : U'.1 ≤ U.1) :
    Submodule.span U'.Bp (Set.range fun s : Γ(F, U.1) => ((1 : U'.Bp) ⊗ₜ resM F hle s : SecBp F U')) = ⊤ := by
  set S := Submodule.span U'.Bp (Set.range fun s : Γ(F, U.1) => ((1 : U'.Bp) ⊗ₜ resM F hle s : SecBp F U'))
  have H : ∀ s : Γ(F, U'.1), ((1 : U'.Bp) ⊗ₜ s : SecBp F U') ∈ S := by
    letI := resAlgebra hle
    letI := resModule F hle
    haveI := res_isScalarTower F hle
    intro s
    induction s using (isBaseChange_resLinear F U.2.1 U'.2.1 hle).inductionOn with
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | tmul s => exact Submodule.subset_span ⟨s, rfl⟩
    | smul a s hs =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul U'.Bp]
      exact S.smul_mem _ hs
    | add s s' hs hs' => rw [TensorProduct.tmul_add]; exact add_mem hs hs'
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a s =>
    have e : (a ⊗ₜ s : SecBp F U') = a • ((1 : U'.Bp) ⊗ₜ s) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact S.smul_mem _ (H s)
  | add x y hx hy => exact add_mem hx hy

theorem imJ_le_span [Lie.V.IsQuasicoherent] (hS : IsSys C M) {U U' : AffOp B.X} (hle : U'.1 ≤ U.1) :
    imJ (C U') ≤ Submodule.span U'.Bp (piMap (AffOp.res hle) (Fin h) '' (imJ (C U) : Set (Fin h → U.Bp))) := by
  obtain ⟨-, l, m, hl, -, hM⟩ := hS.1 U U' hle
  refine imJ_le _ _ ?_ _ (span_tmul_resM Lie.V hle) ?_
  · rw [← res_cstBp hle]
    exact baseOf_le_span _ _ (base_le_imJ _)
  · rintro _ ⟨s, rfl⟩
    exact map_j hM _ _ (hl s)

variable {E : B'.X.Modules} {ι : E ⟶ freeModule B'.X (Fin h)} {Q : AM B' Λ} {t : E ⟶ Q.V} {j : (pullA f.f).obj Lie ⟶ Q}

theorem exact_coker {F G : AM B Λ} [F.V.IsQuasicoherent] [G.V.IsQuasicoherent] (u : F ⟶ G) {W : B.X.Opens}
    (hW : IsAffineOpen W) : Function.Exact (u.hom.app W) ((cokernel.π u).hom.app W) ∧
      Function.Surjective ((cokernel.π u).hom.app W) := by
  have e : (cokernel.π u).hom ≫ (Examples₂.cokV u).hom = cokernel.π u.hom :=
    PreservesCokernel.π_iso_hom (Action.forget B.X.Modules Λ) u
  have e' : (cokernel.π u).hom = cokernel.π u.hom ≫ (Examples₂.cokV u).inv := by
    rw [← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have b : Function.Bijective ((Examples₂.cokV u).inv.app W) :=
    ((sections W).mapIso (Examples₂.cokV u).symm).toLinearEquiv.bijective
  rw [e']
  refine ⟨fun y => ?_, b.2.comp (surjective_cokernel_π_app u.hom hW)⟩
  rw [← exact_cokernel_π_app u.hom hW y, ← app_app]
  exact map_eq_zero_iff (appLinear (Examples₂.cokV u).inv W) b.1

theorem crd_mem_imJ [Lie.V.IsQuasicoherent] (hC : IsCov f g) (hQ : IsQuot M ι (baseOn h (f.f.appTop π)) Q t)
    (U : AffOp B.X) (hJ : JUp C f g U ι t j.hom) (x : Γ(E, f.f ⁻¹ᵁ U.1))
    (hx : (t ≫ (cokernel.π j).hom).app _ x = 0) : piMap (g U) (Fin h) (crd ι _ x) ∈ imJ (C U) := by
  haveI := hQ.1
  haveI : ((pullA f.f).obj Lie).V.IsQuasicoherent := isQuasicoherent_pullback f.f Lie.V
  have H : ∀ z : Γ((Scheme.Modules.pullback f.f).obj Lie.V, f.f ⁻¹ᵁ U.1), ∃ x' : Γ(E, f.f ⁻¹ᵁ U.1),
      appLinear j.hom _ z = appLinear t _ x' ∧ piMap (g U) (Fin h) (crd ι _ x') ∈ imJ (C U) := by
    letI := appLEAlgebra f.f (le_rfl : f.f ⁻¹ᵁ U.1 ≤ _)
    letI := appLEModule f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_rfl : f.f ⁻¹ᵁ U.1 ≤ _)
    haveI := appLE_isScalarTower f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_rfl : f.f ⁻¹ᵁ U.1 ≤ _)
    intro z
    induction z using (isBaseChange_pullbackSections f.f Lie.V (hC.isAffineOpen U) U.2.1 le_rfl).inductionOn with
    | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm, by rw [map_zero, map_zero]; exact zero_mem _⟩
    | tmul s =>
      obtain ⟨x', y, h1, h2, h3⟩ := hJ s
      exact ⟨x', h3, h1 ▸ (mem_imJ _ _).2 ⟨_, h2⟩⟩
    | smul a s hs =>
      obtain ⟨x', h1, h2⟩ := hs
      refine ⟨a • x', ((appLinear j.hom _).map_smul a s).trans (by rw [map_smul]; exact congrArg _ h1), ?_⟩
      rw [map_smul, map_smulₛₗ]
      exact Submodule.smul_mem _ _ h2
    | add s s' hs hs' =>
      obtain ⟨x', h1, h2⟩ := hs
      obtain ⟨x'', h1', h2'⟩ := hs'
      refine ⟨x' + x'', ((appLinear j.hom _).map_add s s').trans (by rw [map_add]; exact congrArg₂ _ h1 h1'), ?_⟩
      rw [map_add, map_add]
      exact add_mem h2 h2'
  obtain ⟨z, hz⟩ := ((exact_coker j (hC.isAffineOpen U)).1 (t.app _ x)).1 hx
  obtain ⟨x', h1, h2⟩ := H z
  have h3 : t.app _ (x - x') = 0 := by
    rw [← appLinear_apply, map_sub, ← h1, sub_eq_zero]
    exact hz.symm
  have h4 := piMap_mem_baseOf (g U) (((hQ.2 _ (hC.isAffineOpen U)).2.1 _).1 h3)
  rw [hC.map_cst, map_sub, map_sub] at h4
  simpa using add_mem (base_le_imJ (C U) h4) h2

theorem exists_affOp_le {W : B.X.Opens} {z : B.X} (hz : z ∈ W) : ∃ U : AffOp B.X, z ∈ U.1 ∧ U.1 ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVle⟩ := B.X.isBasis_affineOpens.exists_subset_of_mem_open hz W.2
  exact ⟨⟨V, hV, ⟨⟨z, hzV⟩⟩⟩, hzV, hVle⟩

theorem piMap_crd_resM (hC : IsCov f g) {U U' : AffOp B.X} (hle : U'.1 ≤ U.1) (x : Γ(E, f.f ⁻¹ᵁ U.1)) :
    piMap (g U') (Fin h) (crd ι _ (resM E (f.f.preimage_mono hle) x)) =
      piMap (AffOp.res hle) (Fin h) (piMap (g U) (Fin h) (crd ι _ x)) := by
  rw [crd_resM]
  exact funext fun i => hC.2.2.2.2 U U' hle _

theorem app_sub_resM {X Y : Scheme.{0}} (a : X ⟶ Y) {F : Y.Modules} {G R : X.Modules} (u : G ⟶ R)
    (r : (Scheme.Modules.pullback a).obj F ⟶ R) {U U' : Y.Opens} (hle : U' ≤ U) (s : Γ(F, U)) (x : Γ(G, a ⁻¹ᵁ U))
    (x' : Γ(G, a ⁻¹ᵁ U')) (hx : r.app _ (pullbackSections a F le_rfl s) = u.app _ x)
    (hx' : r.app _ (pullbackSections a F le_rfl (resM F hle s)) = u.app _ x') :
    u.app _ (x' - resM G (a.preimage_mono hle) x) = 0 := by
  rw [← appLinear_apply, map_sub, sub_eq_zero, appLinear_apply, appLinear_apply, ← hx', GlobalTheory.Twist.app_resM, ← hx,
    ← GlobalTheory.Twist.app_resM]
  exact congrArg _ ((pullbackSections_res a F le_rfl hle s).trans (res_pullbackSections a F le_rfl _ s).symm)

theorem res_sub_mem_imJ [Lie.V.IsQuasicoherent] (hS : IsSys C M) (hC : IsCov f g)
    (hQ : IsQuot M ι (baseOn h (f.f.appTop π)) Q t) {ρ : (Scheme.Modules.pullback f.f).obj Om.V ⟶ (cokernel j).V}
    {U U' : AffOp B.X} (hle : U'.1 ≤ U.1) (hJ : JUp C f g U' ι t j.hom) (hR : RUp C f g U' ι (t ≫ (cokernel.π j).hom) ρ)
    (s : Γ(Om.V, U.1)) (x : Γ(E, f.f ⁻¹ᵁ U.1))
    (hx : ρ.app _ (pullbackSections f.f Om.V le_rfl s) = (t ≫ (cokernel.π j).hom).app _ x) (y : (C U).L 0)
    (hy : IsVal (C U) (1 ⊗ₜ s) y) :
    piMap (AffOp.res hle) (Fin h) (y.1 - piMap (g U) (Fin h) (crd ι _ x)) ∈ imJ (C U') := by
  obtain ⟨x', y', h1, h2, h3⟩ := hR (resM Om.V hle s)
  obtain ⟨-, l, m, -, hm, hM⟩ := hS.1 U U' hle
  have h7 := crd_mem_imJ hC hQ U' hJ _ (app_sub_resM f.f _ ρ hle s x x' hx h3)
  rw [map_sub, map_sub, ← h1, piMap_crd_resM hC hle] at h7
  exact map_ρ hM _ _ (hm s) y y' hy h2 _ h7

end Geo

set_option maxHeartbeats 1600000 in

theorem rUp_of_local : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) (B B' : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (C : ChainsBp p h o Lie Om π γ) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp) (E : ℕ → B'.X.Modules) (ι : ∀ n, E n ⟶ freeModule B'.X (Fin h)) (Q : AM B' Λ) (t : E 0 ⟶ Q.V) (j : (pullA f.f).obj Lie ⟶ Q) (ρ : (pullA f.f).obj Om ⟶ cokernel j), Lie.V.IsQuasicoherent → IsSys C M → IsCov f g → IsLatOf C f g ι → IsQuot M (ι 0) (baseOn h (f.f.appTop π)) Q t → (∀ U : AffOp B.X, JUp C f g U (ι 0) t j.hom) → (∀ z : B.X, ∃ U : AffOp B.X, z ∈ U.1 ∧ ∀ U' : AffOp B.X, U'.1 ≤ U.1 → RUp C f g U' (ι 0) (t ≫ (cokernel.π j).hom) ρ.hom) → ∀ U : AffOp B.X, RUp C f g U (ι 0) (t ≫ (cokernel.π j).hom) ρ.hom := by
  intro O _ _ _ p B B' Λ _ h o Lie Om π γ M C f g E ι Q t j ρ hL hS hC hι hQ hJ hR U s
  haveI := hQ.1
  haveI : ((pullA f.f).obj Lie).V.IsQuasicoherent := isQuasicoherent_pullback f.f Lie.V
  have hs : Function.Surjective ((t ≫ (cokernel.π j).hom).app (f.f ⁻¹ᵁ U.1)) :=
    (exact_coker j (hC.isAffineOpen U)).2.comp (hQ.2 _ (hC.isAffineOpen U)).1
  obtain ⟨x, hq⟩ := hs (ρ.hom.app _ (pullbackSections f.f Om.V le_rfl s))
  have hx : piMap (g U) (Fin h) (crd (ι 0) _ x) ∈ (C U).L 0 := by
    have k : crd (ι 0) _ x ∈ latOf (ι 0) (f.f ⁻¹ᵁ U.1) := ⟨x, rfl⟩
    rw [((hι 0).2.2 U).1, Nat.zero_min] at k
    exact k
  refine (exists_ρ (C U) (1 ⊗ₜ s)).elim fun y₀ hy₀ => ?_
  have key : y₀.1 - piMap (g U) (Fin h) (crd (ι 0) _ x) ∈ imJ (C U) := by
    refine GlobalTheory.ChainDesc.mem_of_locally_mem_span B.X U h _ _ fun z hz => ?_
    obtain ⟨U₀, hz₀, hU₀⟩ := hR z
    obtain ⟨U', hzU, hle⟩ := exists_affOp_le (W := U.1 ⊓ U₀.1) ⟨hz, hz₀⟩
    have h1 : U'.1 ≤ U.1 := hle.trans inf_le_left
    have h2 := res_sub_mem_imJ (ι := ι 0) (ρ := ρ.hom) hS hC hQ h1 (hJ U') (hU₀ U' (hle.trans inf_le_right)) s x hq.symm y₀
    exact ⟨U', h1, hzU, imJ_le_span hS h1 (h2 hy₀)⟩
  exact ⟨x, ⟨_, hx⟩, rfl, Eq.trans hy₀ ((mk_mk_eq_iff (C U) y₀ ⟨_, hx⟩).2 key), hq.symm⟩

end GlobalTheory.ChainDesc.RhoLocal

end
