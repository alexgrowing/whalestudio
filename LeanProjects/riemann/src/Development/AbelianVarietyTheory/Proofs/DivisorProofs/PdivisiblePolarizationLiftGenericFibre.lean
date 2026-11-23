import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneModulesFreeFiniteStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.BadPt

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {G H L : PDivGroup p O}

theorem vecExtMap_comp_apply (f : G ⟶ H) (g : H ⟶ L) (x : L.VecExt) :
    vecExtMap (f ≫ g) x = vecExtMap f (vecExtMap g x) := by
  obtain ⟨y, rfl⟩ := L.rigToExt_surjective x
  rw [← rigToExt_rigExtMap, ← rigToExt_rigExtMap, ← rigToExt_rigExtMap, rigExtMap_comp,
    LinearMap.comp_apply]

theorem vecExtMap_iso_injective (e : G ≅ H) : Function.Injective (vecExtMap e.hom) :=
  Function.LeftInverse.injective (g := vecExtMap e.inv) fun x => by
    rw [← vecExtMap_comp_apply, e.inv_hom_id, vecExtMap_id, LinearMap.id_apply]

theorem omegaMap_dualHom_dualHom_surjective (f : G ⟶ H) (hf : Function.Surjective (omegaMap _ _ f)) :
    Function.Surjective (omegaMap _ _ (dualHom _ _ (dualHom G H f))) := fun x => by
  obtain ⟨y, hy⟩ := hf (omegaMap _ _ G.bidual.hom x)
  refine ⟨omegaMap _ _ H.bidual.inv y, ?_⟩
  rw [← LinearMap.comp_apply, ← omegaMap_comp, dualHom_dualHom_bidual_inv, omegaMap_comp,
    LinearMap.comp_apply, hy, ← LinearMap.comp_apply, ← omegaMap_comp, Iso.inv_hom_id, omegaMap_id,
    LinearMap.id_apply]

theorem vecExtMap_dualHom_injective (hp : (p : O) = 0) (f : G ⟶ H)
    (hf : Function.Surjective (omegaMap _ _ f)) : Function.Injective (vecExtMap (dualHom G H f)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h := primLie_naturality (dualHom G H f) _ _ (extChar_vecExtMap hp (dualHom G H f) x)
  rw [hx, map_zero, map_zero] at h
  refine (map_eq_zero_iff _ (G.dual.extChar_bijective hp).1).1
    ((map_eq_zero_iff _ (G.dual.primLie_bijective hp).1).1 (LinearMap.ext fun w => ?_))
  obtain ⟨v, rfl⟩ := omegaMap_dualHom_dualHom_surjective f hf w
  exact (LinearMap.congr_fun h v).symm

theorem toBase_vecExt_eq_zero [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (hO : (p : O) = 0) (hK : (p : K) = 0) (x : G.VecExt) (hx : (G.toBase K).vecExt x = 0) : x = 0 := by
  have h := (G.toBase K).extChar_vecExt hO hK x
  rw [hx, map_zero] at h
  have h' : (1 : K) ⊗ₜ[O] (G.extChar hO x).1 = 0 := (congrArg Subtype.val h).symm
  refine (map_eq_zero_iff _ (G.extChar_bijective hO).1).1 (Subtype.ext ?_)
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := G.A 1) (Algebra.linearMap O K)
    (IsFractionRing.injective O K)
  have : (1 : O) ⊗ₜ[O] (G.extChar hO x).1 = 0 := hi (by simpa using h')
  simpa using congrArg (TensorProduct.lid O _) this

theorem fg_of_forall_iff {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] (S : Submodule R N) (φ : M → N) (h₁ : ∀ x y, φ (x + y) = φ x + φ y)
    (h₂ : ∀ (r : R) x, φ (r • x) = r • φ x) (h : ∀ x, x ∈ S ↔ ∃ y, φ y = x) : S.FG := by
  let ψ : M →ₗ[R] N := { toFun := φ, map_add' := h₁, map_smul' := h₂ }
  have e : S = Submodule.map ψ ⊤ := Submodule.ext fun x => (h x).trans
    ⟨fun ⟨y, hy⟩ => ⟨y, trivial, hy⟩, fun ⟨y, _, hy⟩ => ⟨y, hy⟩⟩
  rw [e]
  exact Module.Finite.fg_top.map _

theorem vecExtMap_weilProj_injective {R K : Type} [CommRing R] [Field K] [Algebra R K]
    {Γ : PDivGroup p R} {𝒜 : PDivGroup p K} (hK : (p : K) = 0) (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual)
    (hκ : Function.Surjective (omegaMap _ _ κ)) (hw : Function.Injective (vecExtMap w)) :
    Function.Injective (vecExtMap (weilProj κ w)) := fun x y h => by
  rw [weilProj, vecExtMap_comp_apply, vecExtMap_comp_apply, vecExtMap_comp_apply,
    vecExtMap_comp_apply] at h
  exact vecExtMap_iso_injective _ (vecExtMap_dualHom_injective hK κ hκ (hw h))

end SlopeTestRemainingChoices

section Main

variable {p : ℕ} [Fact p.Prime] {R K : Type} [CommRing R] [Field K] [Algebra R K]
  {Γ : PDivGroup p R} {𝒜 : PDivGroup p K} [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]

theorem latOmega_fg (κ : Γ.baseChange K ⟶ 𝒜) (hκ : Function.Bijective (omegaMap _ _ κ))
    [Module.Finite R Γ.omega] : (latOmega κ).FG := by
  let e := LinearEquiv.ofBijective _ hκ
  refine fg_of_forall_iff _ (fun w₀ : Γ.omega => 𝒜.rigOfOmega (e.symm ((Γ.toBase K).omega w₀)))
    (fun x y => by rw [map_add, map_add, map_add])
    (fun r x => by rw [map_smulₛₗ, map_smul, map_smul, algebraMap_smul]) fun x => ⟨?_, ?_⟩
  · rintro ⟨w, w₀, rfl, h⟩
    refine ⟨w₀, ?_⟩
    rw [← h]
    exact congrArg _ (e.symm_apply_apply w)
  · rintro ⟨w₀, rfl⟩
    exact ⟨_, w₀, rfl, e.apply_symm_apply _⟩

theorem latExt_fg {Δ : PDivGroup p R} (π : 𝒜 ⟶ Δ.baseChange K) [Module.Finite R Δ.RigExt] :
    (latExt π).FG :=
  fg_of_forall_iff _ (fun y : Δ.RigExt => rigExtMap π ((Δ.toBase K).rig y))
    (fun x y => by rw [map_add, map_add]) (fun r x => by rw [map_smulₛₗ, map_smul, algebraMap_smul])
    fun _ => exists_congr fun _ => eq_comm

theorem lattice_inf_range [IsDomain R] [IsFractionRing R K] (hR : (p : R) = 0) (hK : (p : K) = 0)
    (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual)
    (hκ : Function.Surjective (omegaMap _ _ κ)) (hw : Function.Injective (vecExtMap w))
    (h : Γ ⟶ Γ.dual) (hh : PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w) :
    lattice κ w ⊓ (LinearMap.range 𝒜.rigOfOmega).restrictScalars R = latOmega κ := by
  have h0 : latOmega κ ≤ (LinearMap.range 𝒜.rigOfOmega).restrictScalars R := by
    rintro _ ⟨η, _, rfl, -⟩
    exact ⟨η, rfl⟩
  refine le_antisymm ?_ (le_inf le_sup_left h0)
  rintro x ⟨hx, hx'⟩
  obtain ⟨u, hu, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
  refine add_mem hu ?_
  have h1 : rigExtMap (weilProj κ w) ((Γ.dual.toBase K).rig y) ∈ LinearMap.range 𝒜.rigOfOmega :=
    (add_mem_cancel_left (h0 hu)).1 hx'
  have h2 := (𝒜.exact_rigOfOmega_rigToExt _).2 h1
  rw [rigToExt_rigExtMap, map_eq_zero_iff _ (vecExtMap_weilProj_injective hK κ w hκ hw),
    SemiHom.rigToExt_rig] at h2
  obtain ⟨η, rfl⟩ := (Γ.dual.exact_rigOfOmega_rigToExt _).1 (toBase_vecExt_eq_zero K hR hK _ h2)
  refine ⟨omegaMap _ _ (weilProj κ w) ((Γ.dual.toBase K).omega η), omegaMap _ _ h η, ?_, ?_⟩
  · rw [SemiHom.rig_rigOfOmega, rigExtMap_rigOfOmega]
  · rw [← LinearMap.comp_apply, ← omegaMap_comp, ← hh]
    exact ((Γ.toBase K).omega_naturality (Γ.dual.toBase K) h (PDivGroup.baseChangeMap K h)
      (fun _ _ => rfl) η).symm

end Main

theorem lattice_fg_and_inf_range : GlobalTheory.Published.BarsottiTateDieudonne.WittModule → ∀ (p : ℕ) [Fact p.Prime] (R : Type)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : (p : R) = 0) (hK : (p : K) = 0) (Γ' : PDivGroup p R) (𝒜 : PDivGroup p K) (κ : Γ'.baseChange K ⟶ 𝒜)
    (w : 𝒜 ⟶ 𝒜.dual) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt], Function.Bijective (omegaMap _ _ κ) →
    Function.Bijective (vecExtMap w) → ∀ h : Γ' ⟶ Γ'.dual, PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w →
    (lattice κ w).FG ∧ lattice κ w ⊓ (LinearMap.range 𝒜.rigOfOmega).restrictScalars R = latOmega κ := by
  intro hW p _ R _ _ _ K _ _ _ hR hK Γ' 𝒜 κ w _ _ hκ hw h hh
  haveI := (GlobalTheory.T.dieudonne_modules_free_finite hW p R hR Γ').2.1
  haveI := (GlobalTheory.T.dieudonne_modules_free_finite hW p R hR Γ'.dual).2.2.2.2.2.2.2
  exact ⟨(latOmega_fg κ hκ).sup (latExt_fg _), lattice_inf_range hR hK κ w hκ.2 hw.1 h hh⟩

end GlobalTheory.BadPt
