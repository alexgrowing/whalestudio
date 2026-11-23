import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {G H : PDivGroup p R}

theorem omegaMap_baseChangeMap_injective (S : Type) [CommRing S] [Algebra R S] (hp : (p : R) = 0) (f : G ⟶ H)
    (hf : Function.Bijective (omegaMap _ _ f)) : Function.Injective (omegaMap _ _ (baseChangeMap S f)) := by
  have hG := omega_baseChange_bijective G S hp
  have hH := omega_baseChange_bijective H S hp
  let e : S ⊗[R] H.omega ≃ₗ[S] S ⊗[R] G.omega :=
    LinearEquiv.baseChange R S _ _ (LinearEquiv.ofBijective (omegaMap _ _ f) hf)
  have key : ∀ x, omegaMap _ _ (baseChangeMap S f) (PDiv.liftSemi (H.toBase S).omega x) =
      PDiv.liftSemi (G.toBase S).omega (e x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r w =>
      simp only [PDiv.liftSemi_tmul, map_smul, e, LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply]
      exact congrArg _ ((G.toBase S).omega_naturality (H.toBase S) f _ (fun _ _ => rfl) w).symm
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨x, rfl⟩ := hH.2 w
  rw [key, map_eq_zero_iff _ hG.1, map_eq_zero_iff _ e.injective] at hw
  rw [hw, map_zero]

theorem exists_omega_baseChange_eq_sum (S : Type) [CommRing S] [Algebra R S] (hp : (p : R) = 0)
    (t : (G.baseChange S).omega) :
    ∃ (n : ℕ) (r : Fin n → S) (θ : Fin n → G.omega), t = ∑ i, r i • (G.toBase S).omega (θ i) := by
  obtain ⟨x, rfl⟩ := (omega_baseChange_bijective G S hp).2 t
  obtain ⟨n, r, θ, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  exact ⟨n, r, θ, by simp only [map_sum, PDiv.liftSemi_tmul]⟩

theorem omegaMap_frobTwistMap_injective (hp : (p : R) = 0) (f : G ⟶ H)
    (hf : Function.Bijective (omegaMap _ _ f)) : Function.Injective (omegaMap _ _ (frobTwistMap hp f)) :=
  letI := (frobRing hp).toAlgebra
  omegaMap_baseChangeMap_injective R hp f hf

theorem exists_omega_frobTwist_eq_sum (hp : (p : R) = 0) (t : (frobTwist hp G).omega) :
    ∃ (n : ℕ) (r : Fin n → R) (θ : Fin n → G.omega), t = ∑ i, r i • (frobProj hp G).omega (θ i) :=
  letI := (frobRing hp).toAlgebra
  exists_omega_baseChange_eq_sum R hp t

theorem exists_rigExtMap_verschiebung_eq_sum {S : Type} [CommRing S] (hR : (p : R) = 0) (hS : (p : S) = 0)
    {σ : R →+* S} {G' A : PDivGroup p S} (s : SemiHom σ G' G) (κ : G' ⟶ A)
    (hκ : Function.Bijective (omegaMap _ _ κ)) {x : A.RigExt} {z : G.RigExt} (hz : rigExtMap κ x = s.rig z) :
    ∃ (n : ℕ) (r : Fin n → R) (u : Fin n → A.omega) (θ : Fin n → G.omega),
      (∀ i, omegaMap _ _ κ (u i) = s.omega (θ i)) ∧
      rigExtMap (verschiebung hS A) x = ∑ i, σ (r i) • (frobProj hS A).rig (A.rigOfOmega (u i)) := by
  obtain ⟨t, ht⟩ := range_rigExtMap_verschiebung_le hR G ⟨z, rfl⟩
  obtain ⟨v, hv⟩ := range_rigExtMap_verschiebung_le hS A ⟨x, rfl⟩
  obtain ⟨n, r, θ, rfl⟩ := exists_omega_frobTwist_eq_sum hR t
  choose u hu using fun i => hκ.2 (s.omega (θ i))
  refine ⟨n, r, u, θ, hu, ?_⟩
  have h1 : v = ∑ i, σ (r i) • (frobProj hS A).omega (u i) := by
    refine omegaMap_frobTwistMap_injective hS κ hκ ((frobTwist hS G').rigOfOmega_injective_of_eq_zero hS ?_)
    rw [← rigExtMap_rigOfOmega, hv, ← LinearMap.comp_apply (rigExtMap (frobTwistMap hS κ)), ← rigExtMap_comp,
      verschiebung_naturality, rigExtMap_comp, LinearMap.comp_apply, hz,
      ← (s.frobTwist hR hS).rig_naturality s (verschiebung hR G) _ (s.app_verschiebung hR hS) z, ← ht,
      SemiHom.rig_rigOfOmega]
    refine congrArg _ ?_
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, map_smul,
      ← (frobProj hS G').omega_naturality (frobProj hS A) κ (frobTwistMap hS κ) (fun _ _ => rfl), hu,
      s.omega_omega _ ((frobProj hS G').comp s) fun _ _ => rfl]
    exact congrArg _ ((frobProj hR G).omega_omega _ _
      (fun n a => (SemiHom.frobTwist_app_frobProj hR hS s n a).symm) _)
  rw [← hv, h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, SemiHom.rig_rigOfOmega]

end PDivGroup

namespace BadPt

theorem exists_rigExtMap_eq_toBase {p : ℕ} [Fact p.Prime] {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    {Γ : PDivGroup p R} {𝒜 : PDivGroup p K} (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual)
    [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt] (h : Γ ⟶ Γ.dual)
    (e : PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w) {x : 𝒜.RigExt} (hx : x ∈ lattice κ w) :
    ∃ z : Γ.RigExt, rigExtMap κ x = (Γ.toBase K).rig z := by
  obtain ⟨_, ⟨u, u₀, rfl, hu⟩, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
  have h1 : rigExtMap κ (𝒜.rigOfOmega u) = (Γ.toBase K).rig (Γ.rigOfOmega u₀) :=
    (rigExtMap_rigOfOmega κ u).trans ((congrArg _ hu).trans ((Γ.toBase K).rig_rigOfOmega u₀).symm)
  have h2 : rigExtMap κ (rigExtMap (weilProj κ w) ((Γ.dual.toBase K).rig y)) = (Γ.toBase K).rig (rigExtMap h y) :=
    (LinearMap.congr_fun (rigExtMap_comp κ (weilProj κ w)) _).symm.trans
      ((congrArg (fun f => rigExtMap f ((Γ.dual.toBase K).rig y)) e).symm.trans
        ((Γ.toBase K).rig_naturality (Γ.dual.toBase K) h (PDivGroup.baseChangeMap K h) (fun _ _ => rfl) y).symm)
  exact ⟨Γ.rigOfOmega u₀ + rigExtMap h y, (map_add _ _ _).trans
    ((congrArg₂ (· + ·) h1 h2).trans (map_add _ _ _).symm)⟩

theorem rigExtMap_verschiebung_lattice : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (hR : (p : R) = 0) (hK : (p : K) = 0) (Γ' : PDivGroup p R) (𝒜 : PDivGroup p K) (κ : Γ'.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt], Function.Bijective (omegaMap _ _ κ) → Function.Bijective (vecExtMap w) → ∀ h : Γ' ⟶ Γ'.dual, PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w → ∀ x ∈ lattice κ w, ∃ (n : ℕ) (r : Fin n → R) (y : Fin n → 𝒜.RigExt), (∀ i, y i ∈ latOmega κ) ∧ rigExtMap (verschiebung hK 𝒜) x = ∑ i, algebraMap R K (r i) • (frobProj hK 𝒜).rig (y i) := by
  intro p _ R _ _ _ K _ _ _ hR hK Γ 𝒜 κ w _ _ hκ _ h e x hx
  obtain ⟨z, hz⟩ := exists_rigExtMap_eq_toBase κ w h e hx
  obtain ⟨n, r, u, θ, hu, hv⟩ := exists_rigExtMap_verschiebung_eq_sum hR hK (Γ.toBase K) κ hκ hz
  exact ⟨n, r, fun i => 𝒜.rigOfOmega (u i), fun i => ⟨u i, θ i, rfl, hu i⟩, hv⟩

end BadPt

end GlobalTheory
