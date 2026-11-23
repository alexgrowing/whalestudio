import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BadPt

section Der

variable {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Projective R A]
  [Coalgebra.IsCocomm R A]

theorem cobOne_dual_eq_zero_iff (φ : CartierDual R A) : cobOne R (CartierDual R A) φ = 0 ↔
    ∀ a b, φ (a * b) = Coalgebra.counit (R := R) a * φ b + Coalgebra.counit (R := R) b * φ a := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff]
  refine forall₂_congr fun a b => ?_
  rw [map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply, eq_comm, add_comm, mul_comm (φ a)]

theorem apply_eq_of_dUnit_eq {φ : CartierDual R A} (h : cobOne R (CartierDual R A) φ = 0) {a b : A}
    (e : dUnit R a = dUnit R b) : φ a = φ b := by
  have h' := (cobOne_dual_eq_zero_iff φ).1 h
  exact (AugCot.lift_d (Bialgebra.counitAlgHom R A) φ.ofConv h' a).symm.trans
    ((congrArg (AugCot.lift (Bialgebra.counitAlgHom R A) φ.ofConv h') e).trans (AugCot.lift_d _ _ h' b))

theorem cobOne_toConv_comp_d (l : Cot R A →ₗ[R] R) :
    cobOne R (CartierDual R A) (WithConv.toConv (l ∘ₗ AugCot.d (Bialgebra.counitAlgHom R A))) = 0 :=
  (cobOne_dual_eq_zero_iff _).2 fun a b => by
    change l (AugCot.d _ (a * b)) = _
    rw [AugCot.d_mul, map_add, map_smul, map_smul]
    rfl

end Der

theorem exists_form_of_mem_dualSubmodule {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {H W W' W₀ : Type*} [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H]
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] [AddCommGroup W₀] [Module R W₀]
    (a : W →ₗ[K] H) (k : W →ₗ[K] W') (hk : Function.Bijective k) (t : W₀ →ₛₗ[algebraMap R K] W')
    (B : LinearMap.BilinForm K H) (N : Submodule R H) (hN : ∀ x x₀, k x = t x₀ → a x ∈ N) {s : H}
    (hs : s ∈ B.dualSubmodule N) :
    ∃ l : W₀ →ₗ[R] R, ∀ x x₀, k x = t x₀ → B s (a x) = algebraMap R K (l x₀) := by
  let e := LinearEquiv.ofBijective _ hk
  let j : W₀ →ₗ[R] N :=
    { toFun := fun x₀ => ⟨a (e.symm (t x₀)), hN _ x₀ (e.apply_symm_apply _)⟩
      map_add' := fun x y => Subtype.ext (by simp only [map_add]; rfl)
      map_smul' := fun r x => Subtype.ext (by
        change a (e.symm (t (r • x))) = r • a (e.symm (t x))
        rw [map_smulₛₗ, map_smul, map_smul, algebraMap_smul]) }
  refine ⟨B.dualSubmoduleToDual _ ⟨s, hs⟩ ∘ₗ j, fun x x₀ h => ?_⟩
  have h₂ : (j x₀).1 = a x := congrArg a (e.symm_apply_eq.2 h.symm)
  rw [← h₂]
  exact (B.dualSubmoduleParing_spec ⟨s, hs⟩ (j x₀)).symm

section Pair

variable {p : ℕ} [Fact p.Prime] {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {Γ' : PDivGroup p R} {𝒜 : PDivGroup p K}

theorem isConnecting_rig {S S' : Type} [CommRing S] [CommRing S'] {σ : S →+* S'} {G : PDivGroup p S}
    {G' : PDivGroup p S'} (s : SemiHom σ G' G) {y : G.RigExt} {b : G.A 1} (h : G.IsConnecting (G.rigToExt y) b) :
    G'.IsConnecting (G'.rigToExt (s.rig y)) (s.app 1 b) := by
  rw [SemiHom.rigToExt_rig]
  exact s.connecting h

theorem isConnecting_rigExtMap {S : Type} [CommRing S] {G G' : PDivGroup p S} (f : G' ⟶ G) {y : G.RigExt}
    {b : G.A 1} (h : G.IsConnecting (G.rigToExt y) b) :
    G'.IsConnecting (G'.rigToExt (rigExtMap f y)) (f.app 1 b) := by
  rw [← SemiHom.ofHom_rig]
  exact isConnecting_rig (SemiHom.ofHom f) h

theorem pairing_weilProj (κ : Γ'.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) (B : LinearMap.BilinForm K 𝒜.RigExt) (ε : ℤˣ)
    (hB : ∀ (y : 𝒜.dual.RigExt) (b : CartierDual K (𝒜.A 1)), 𝒜.dual.IsConnecting (𝒜.dual.rigToExt y) b →
      ∀ (η' : 𝒜.omega) (a : 𝒜.A 1), dUnit K a = η'.1 1 → B (rigExtMap w y) (𝒜.rigOfOmega η') = ε • b a)
    (y₀ : Γ'.dual.RigExt) (b₀ : CartierDual R (Γ'.A 1)) (h₀ : Γ'.dual.IsConnecting (Γ'.dual.rigToExt y₀) b₀)
    (η' : 𝒜.omega) (η₀ : Γ'.omega) (hη : omegaMap _ _ κ η' = (Γ'.toBase K).omega η₀)
    (a₀ : Γ'.A 1) (ha₀ : dUnit R a₀ = η₀.1 1) :
    B (rigExtMap (weilProj κ w) ((Γ'.dual.toBase K).rig y₀)) (𝒜.rigOfOmega η') = ε • algebraMap R K (b₀ a₀) := by
  have h₁ := isConnecting_rigExtMap (PerfdLat.dualBaseChange K Γ').hom (isConnecting_rig (Γ'.dual.toBase K) h₀)
  have h₂ := isConnecting_rigExtMap (dualHom _ _ κ) h₁
  obtain ⟨a, ha⟩ := AugCot.d_surjective _ (η'.1 1)
  have h₃ := hB _ _ h₂ η' a ha
  rw [weilProj, rigExtMap_comp, rigExtMap_comp]
  refine h₃.trans (congrArg (ε • ·) ?_)
  have e : dUnit K (κ.app 1 a) = dUnit K ((1 : K) ⊗ₜ[R] a₀ : (Γ'.baseChange K).A 1) := by
    have e' := congrArg (fun z => z.1 1) hη
    simp only [omegaMap_val, SemiHom.omega_val] at e'
    rw [← ha₀, ← ha, SemiBialgHom.cot_d] at e'
    exact (PDiv.cotMap_d _ _).symm.trans e'
  refine (apply_eq_of_dUnit_eq (cobOne_eq_zero_of_connecting h₁) e).trans ?_
  refine (CartierDual.baseChange_tmul_tmul K 1 1 b₀ a₀).trans ?_
  rw [_root_.mul_one, Algebra.algebraMap_eq_smul_one]

theorem eq_zero_of_forall_toBase (hR : (p : R) = 0) (κ : Γ'.baseChange K ⟶ 𝒜)
    (hκ : Function.Bijective (omegaMap _ _ κ)) (f : 𝒜.omega →ₗ[K] K)
    (hf : ∀ η' η₀, omegaMap _ _ κ η' = (Γ'.toBase K).omega η₀ → f η' = 0) (η' : 𝒜.omega) : f η' = 0 := by
  let e := LinearEquiv.ofBijective _ hκ
  obtain ⟨t, ht⟩ := (Γ'.omega_baseChange_bijective K hR).2 (e η')
  rw [← e.symm_apply_apply η', ← ht]
  clear ht
  induction t with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, add_zero]
  | tmul r η₀ =>
    rw [PDiv.liftSemi_tmul, map_smul, map_smul, hf _ η₀ (e.apply_symm_apply _), smul_zero]

end Pair

theorem lattice_sup_range_eq_dualSubmodule (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (hR : (p : R) = 0)
    (_hK : (p : K) = 0) (Γ' : PDivGroup p R) (𝒜 : PDivGroup p K) (κ : Γ'.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual)
    [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt] (B : LinearMap.BilinForm K 𝒜.RigExt) (ε : ℤˣ)
    (hκ : Function.Bijective (omegaMap _ _ κ)) (hL : IsLagr B (LinearMap.range 𝒜.rigOfOmega))
    (hB : ∀ (y : 𝒜.dual.RigExt) (b : CartierDual K (𝒜.A 1)), 𝒜.dual.IsConnecting (𝒜.dual.rigToExt y) b →
      ∀ (η' : 𝒜.omega) (a : 𝒜.A 1), dUnit K a = η'.1 1 → B (rigExtMap w y) (𝒜.rigOfOmega η') = ε • b a) :
    lattice κ w ⊔ (LinearMap.range 𝒜.rigOfOmega).restrictScalars R = B.dualSubmodule (latOmega κ) := by
  have hF : (LinearMap.range 𝒜.rigOfOmega).restrictScalars R ≤ B.dualSubmodule (latOmega κ) := by
    rintro x hx _ ⟨η', η₀, rfl, -⟩
    rw [(hL x).1 hx _ ⟨η', rfl⟩]
    exact zero_mem _
  refine le_antisymm (sup_le (sup_le ?_ ?_) hF) fun s hs => ?_
  · rintro _ ⟨η', η₀, rfl, -⟩
    exact hF ⟨η', rfl⟩
  · rintro _ ⟨y₀, rfl⟩ _ ⟨η', η₀, rfl, hη⟩
    obtain ⟨b₀, h₀⟩ := Γ'.dual.exists_connecting hR (Γ'.dual.rigToExt y₀)
    obtain ⟨a₀, ha₀⟩ := AugCot.d_surjective _ (η₀.1 1)
    rw [pairing_weilProj κ w B ε hB y₀ b₀ h₀ η' η₀ hη a₀ ha₀, Units.smul_def]
    exact zsmul_mem (Submodule.algebraMap_mem _) _
  · obtain ⟨l₀, hl₀⟩ := exists_form_of_mem_dualSubmodule 𝒜.rigOfOmega _ hκ (Γ'.toBase K).omega B (latOmega κ)
      (fun x x₀ h => ⟨x, x₀, rfl, h⟩) hs
    let u := LinearEquiv.ofBijective _ (Γ'.omegaLevel_one_bijective hR)
    let l : Cot R (Γ'.A 1) →ₗ[R] R := (ε : ℤ) • (l₀ ∘ₗ u.symm.toLinearMap)
    obtain ⟨x, hx⟩ := exists_of_cobOne_eq_zero (G := Γ'.dual) (cobOne_toConv_comp_d l)
    obtain ⟨y₀, rfl⟩ := Γ'.dual.rigToExt_surjective x
    rw [← add_sub_cancel (rigExtMap (weilProj κ w) ((Γ'.dual.toBase K).rig y₀)) s]
    refine Submodule.add_mem_sup (Submodule.mem_sup_right ⟨y₀, rfl⟩) ((hL _).2 ?_)
    rintro _ ⟨η', rfl⟩
    refine eq_zero_of_forall_toBase hR κ hκ
      (B (s - rigExtMap (weilProj κ w) ((Γ'.dual.toBase K).rig y₀)) ∘ₗ 𝒜.rigOfOmega) (fun η' η₀ hη => ?_) η'
    obtain ⟨a₀, ha₀⟩ := AugCot.d_surjective _ (η₀.1 1)
    have h₃ := pairing_weilProj κ w B ε hB y₀ _ hx η' η₀ hη a₀ ha₀
    refine (B.sub_left _ _ _).trans (sub_eq_zero.2 (Eq.trans ?_ h₃.symm))
    have h₁ : u.symm (AugCot.d _ a₀) = η₀ := u.symm_apply_eq.2 ha₀
    change _ = ε • algebraMap R K ((ε : ℤ) • l₀ (u.symm (AugCot.d _ a₀)))
    rw [h₁, map_zsmul, hl₀ η' η₀ hη, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]

end GlobalTheory.BadPt
