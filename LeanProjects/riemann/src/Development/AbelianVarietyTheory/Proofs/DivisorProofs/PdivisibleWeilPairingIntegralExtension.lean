import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeBijectiveOfPEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneModulesFreeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerschiebungFrobeniusKernelRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaInjectiveSaturationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorExtensionSurjectiveFieldStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.BadPt.FrobSpan

section Semi

variable {R K M N : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module K N] (f : M →ₛₗ[algebraMap R K] N)

theorem exists_smul_eq (hf : Function.Surjective (liftSemi f)) (n : N) :
    ∃ r : R, r ≠ 0 ∧ ∃ m, f m = algebraMap R K r • n := by
  obtain ⟨t, rfl⟩ := hf n
  obtain ⟨⟨m, s⟩, e⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (TensorProduct.mk R K M 1) t
  refine ⟨s, nonZeroDivisors.coe_ne_zero s, m, ?_⟩
  rw [← map_smul, algebraMap_smul]
  exact ((congrArg (liftSemi f) e).trans ((liftSemi_tmul f 1 m).trans (one_smul _ _))).symm

theorem injective_of_free [Module.Free R M] (hf : Function.Injective (liftSemi f)) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero _).2 fun m hm => ?_
  have e : TensorProduct.mk R K M 1 m = 0 := hf (by
    rw [map_zero]; exact (liftSemi_tmul f 1 m).trans ((one_smul _ _).trans hm))
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) _).1 e
  exact (smul_eq_zero.1 hs).resolve_left (nonZeroDivisors.coe_ne_zero s)

theorem exists_smul_mem_of_mem_span [Module R N] [IsScalarTower R K N] (P : Submodule R N) {S : Set N}
    (hS : ∀ x ∈ S, ∃ r : R, r ≠ 0 ∧ algebraMap R K r • x ∈ P) {x : N} (hx : x ∈ Submodule.span K S) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R K r • x ∈ P := by
  simp only [algebraMap_smul] at hS ⊢
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨s, hs, hy⟩ := hy
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  | smul c x _ hx =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (nonZeroDivisors R) c
    refine ⟨r * s, mul_ne_zero hr (nonZeroDivisors.coe_ne_zero s), ?_⟩
    have e' : (r * s : R) • c • x = a • r • x := by
      rw [mul_smul, ← algebraMap_smul K (s : R), smul_smul _ c, mul_comm, e, algebraMap_smul, smul_comm]
    rw [e']
    exact Submodule.smul_mem _ _ hx

end Semi

section General

variable {p : ℕ} [Fact p.Prime] {R S : Type} [CommRing R] [CommRing S] {G H L : PDivGroup p R}

theorem vecExtMap_comp (f : G ⟶ H) (g : H ⟶ L) (x : L.VecExt) :
    vecExtMap (f ≫ g) x = vecExtMap f (vecExtMap g x) := by
  obtain ⟨y, rfl⟩ := L.rigToExt_surjective x
  rw [← rigToExt_rigExtMap, ← rigToExt_rigExtMap, ← rigToExt_rigExtMap, rigExtMap_comp, LinearMap.comp_apply]

theorem vecExtMap_iso (e : G ≅ H) : Function.Bijective (vecExtMap e.hom) :=
  Function.bijective_iff_has_inverse.2 ⟨vecExtMap e.inv,
    fun x => by rw [← vecExtMap_comp, e.inv_hom_id, vecExtMap_id, LinearMap.id_apply],
    fun x => by rw [← vecExtMap_comp, e.hom_inv_id, vecExtMap_id, LinearMap.id_apply]⟩

theorem omegaMap_comp_apply (f : G ⟶ H) (g : H ⟶ L) (x : L.omega) :
    omegaMap G L (f ≫ g) x = omegaMap G H f (omegaMap H L g x) := by
  rw [omegaMap_comp, LinearMap.comp_apply]

theorem omegaMap_iso (e : G ≅ H) : Function.Bijective (omegaMap G H e.hom) :=
  Function.bijective_iff_has_inverse.2 ⟨omegaMap H G e.inv,
    fun x => by rw [← omegaMap_comp_apply, e.inv_hom_id, omegaMap_id, LinearMap.id_apply],
    fun x => by rw [← omegaMap_comp_apply, e.hom_inv_id, omegaMap_id, LinearMap.id_apply]⟩

theorem primLie_extChar_comp (h : (p : R) = 0) (f : G ⟶ H) :
    (G.primLie ∘ G.extChar h) ∘ vecExtMap f =
      (omegaMap H.dual G.dual (dualHom G H f)).dualMap ∘ (H.primLie ∘ H.extChar h) :=
  funext fun x => primLie_naturality f _ _ (extChar_vecExtMap h f x)

theorem absFrob_rigOfOmega (h : (p : R) = 0) (w : G.omega) : (absFrob h G).rig (G.rigOfOmega w) = 0 := by
  rw [← rigExtMap_relFrob_rig, SemiHom.rig_rigOfOmega]
  exact LinearMap.congr_fun (rigExtMap_relFrob_comp_rigOfOmega h G) _

theorem absFrob_rigExtMap (h : (p : R) = 0) (f : G ⟶ H) (x : H.RigExt) :
    (absFrob h G).rig (rigExtMap f x) = rigExtMap f ((absFrob h H).rig x) :=
  SemiHom.rig_naturality _ _ f f (fun n a => by rw [absFrob_app, absFrob_app, map_pow]) x

variable [Algebra R S]

theorem absFrob_toBase (h : (p : R) = 0) (h' : (p : S) = 0) (x : G.RigExt) :
    (absFrob h' (G.baseChange S)).rig ((G.toBase S).rig x) = (G.toBase S).rig ((absFrob h G).rig x) :=
  (SemiHom.comp_rig _ _ x).symm.trans (SemiHom.rig_rig _ _ _ (fun n a => by
    rw [SemiHom.comp_app, absFrob_app, absFrob_app, map_pow]) x).symm

theorem toBase_omegaMap (f : G ⟶ H) (w : H.omega) : (G.toBase S).omega (omegaMap G H f w) =
    omegaMap _ _ (PDivGroup.baseChangeMap S f) ((H.toBase S).omega w) :=
  SemiHom.omega_naturality _ _ f _ (fun _ _ => rfl) w

theorem toBase_vecExtMap (f : G ⟶ H) (x : H.VecExt) : (G.toBase S).vecExt (vecExtMap f x) =
    vecExtMap (PDivGroup.baseChangeMap S f) ((H.toBase S).vecExt x) := by
  obtain ⟨y, rfl⟩ := H.rigToExt_surjective x
  rw [← rigToExt_rigExtMap, ← SemiHom.rigToExt_rig, ← SemiHom.rigToExt_rig, ← rigToExt_rigExtMap,
    SemiHom.rig_naturality _ (H.toBase S) f (PDivGroup.baseChangeMap S f) fun _ _ => rfl]

end General

section Field

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] (h : (p : K) = 0) {G H : PDivGroup p K}
include h

theorem omegaMap_dualHom_injective (f : G ⟶ H) (hf : Function.Surjective (vecExtMap f)) :
    Function.Injective (omegaMap H.dual G.dual (dualHom G H f)) := by
  have e := ((G.primLie_bijective h).comp (G.extChar_bijective h)).2.comp hf
  rw [primLie_extChar_comp] at e
  exact LinearMap.dualMap_surjective_iff.1 e.of_comp

theorem vecExtMap_dualHom_bijective (f : G ⟶ H) (hf : Function.Bijective (omegaMap G H f)) :
    Function.Bijective (vecExtMap (dualHom G H f)) := by
  have e : Function.Bijective (omegaMap _ _ (dualHom _ _ (dualHom G H f))) := by
    rw [← Function.Bijective.of_comp_iff' (omegaMap_iso G.bidual), ← LinearMap.coe_comp, ← omegaMap_comp,
      bidual_hom_dualHom_dualHom, omegaMap_comp, LinearMap.coe_comp]
    exact hf.comp (omegaMap_iso H.bidual)
  rw [← Function.Bijective.of_comp_iff' ((H.dual.primLie_bijective h).comp (H.dual.extChar_bijective h)),
    primLie_extChar_comp]
  exact (LinearMap.dualMap_bijective_iff.2 e).comp
    ((G.dual.primLie_bijective h).comp (G.dual.extChar_bijective h))

theorem omegaMap_injective_of_antisymm (f : G ⟶ G.dual) (hf : Function.Surjective (vecExtMap f))
    (e : G.bidual.hom ≫ dualHom _ _ f = -f) : Function.Injective (omegaMap _ _ f) := by
  have k := (omegaMap_iso G.bidual).1.comp (omegaMap_dualHom_injective h f hf)
  rw [← LinearMap.coe_comp, ← omegaMap_comp, e, map_neg] at k
  exact fun x y hxy => k (by rw [LinearMap.neg_apply, LinearMap.neg_apply, hxy])

end Field

section Main

variable {p : ℕ} [Fact p.Prime] {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {Γ Δ : PDivGroup p R} {𝒜 : PDivGroup p K} [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]

def pullRig (π : 𝒜 ⟶ Δ.baseChange K) : Δ.RigExt →ₗ[R] 𝒜.RigExt where
  toFun y := rigExtMap π ((Δ.toBase K).rig y)
  map_add' _ _ := by rw [map_add, map_add]
  map_smul' _ _ := by rw [map_smulₛₗ, map_smul, algebraMap_smul, RingHom.id_apply]

variable (hR : (p : R) = 0) (hK : (p : K) = 0) (κ : Γ.baseChange K ⟶ 𝒜) (π : 𝒜 ⟶ Δ.baseChange K)

omit [IsDomain R] [IsFractionRing R K] in

theorem pullRig_apply (y : Δ.RigExt) : pullRig π y = rigExtMap π ((Δ.toBase K).rig y) := rfl

omit [IsDomain R] [IsFractionRing R K] in

theorem pullRig_smul (r : R) (y : Δ.RigExt) : pullRig π (r • y) = algebraMap R K r • pullRig π y := by
  rw [pullRig_apply, pullRig_apply, map_smulₛₗ, map_smul]

omit [IsDomain R] [IsFractionRing R K] in

theorem absFrob_pullRig (y : Δ.RigExt) :
    (absFrob hK 𝒜).rig (pullRig π y) = pullRig π ((absFrob hR Δ).rig y) := by
  rw [pullRig_apply, pullRig_apply, absFrob_rigExtMap, absFrob_toBase hR]

omit [IsDomain R] [IsFractionRing R K] in

theorem pullRig_rigOfOmega (η : Δ.omega) : pullRig π (Δ.rigOfOmega η) =
    𝒜.rigOfOmega (omegaMap _ _ π ((Δ.toBase K).omega η)) := by
  rw [pullRig_apply, SemiHom.rig_rigOfOmega, rigExtMap_rigOfOmega]

omit [IsDomain R] [IsFractionRing R K] in

theorem rigToExt_pullRig (y : Δ.RigExt) : 𝒜.rigToExt (pullRig π y) =
    vecExtMap π ((Δ.toBase K).vecExt (Δ.rigToExt y)) := by
  rw [pullRig_apply, rigToExt_rigExtMap, SemiHom.rigToExt_rig]

omit [IsDomain R] [IsFractionRing R K] in

theorem span_image_eq :
    Submodule.span R ((absFrob hK 𝒜).rig '' (latOmega κ ⊔ latExt π : Submodule R 𝒜.RigExt)) =
      (Submodule.span R (Set.range (absFrob hR Δ).rig)).map (pullRig π) := by
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨_, ⟨η, -, rfl, -⟩, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨_, ⟨y, rfl⟩, ?_⟩
    rw [map_add, absFrob_rigOfOmega, zero_add, ← absFrob_pullRig hR hK, pullRig_apply]
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨pullRig π y, Submodule.mem_sup_right (show pullRig π y ∈ latExt π from ⟨y, rfl⟩),
      absFrob_pullRig hR hK π y⟩

theorem exists_smul_mem (hπ : Function.Surjective (vecExtMap π)) {x : 𝒜.RigExt}
    (hx : x ∈ Submodule.span K (Set.range (absFrob hK 𝒜).rig)) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R K r • x ∈
      (Submodule.span R (Set.range (absFrob hR Δ).rig)).map (pullRig π) := by
  refine exists_smul_mem_of_mem_span _ ?_ hx
  rintro _ ⟨x, rfl⟩
  obtain ⟨u, hu⟩ := hπ (𝒜.rigToExt x)
  haveI := IsLocalization.flat K (nonZeroDivisors R)
  obtain ⟨r, hr, v, hv⟩ := exists_smul_eq _ (Δ.liftSemi_vecExt_bijective K hR (.inl inferInstance)).2 u
  obtain ⟨y, rfl⟩ := Δ.rigToExt_surjective v
  obtain ⟨η, hη⟩ := (𝒜.exact_rigOfOmega_rigToExt (algebraMap R K r • x - pullRig π y)).1 (by
    rw [map_sub, rigToExt_pullRig, hv, map_smul, map_smul, hu, sub_self])
  have e := absFrob_rigOfOmega hK η
  rw [hη, map_sub, sub_eq_zero, map_smulₛₗ, frobRing_apply, ← map_pow, absFrob_pullRig hR] at e
  exact ⟨r ^ p, pow_ne_zero _ hr, _, Submodule.subset_span ⟨y, rfl⟩, e.symm⟩

include hR hK in

theorem exists_eq_pullRig [Module.Free R Γ.omega] [Module.Free R Δ.VecExt] (h : Γ ⟶ Δ)
    (hh : PDivGroup.baseChangeMap K h = κ ≫ π) (hκ : Function.Injective (omegaMap _ _ κ))
    (hπ : Function.Injective (vecExtMap π)) (hi : Function.Injective (omegaMap _ _ h))
    (hs : ∀ (r : R) (w : Γ.omega), r ≠ 0 → r • w ∈ LinearMap.range (omegaMap _ _ h) →
      w ∈ LinearMap.range (omegaMap _ _ h)) {r : R} (hr : r ≠ 0) {η : 𝒜.omega} {η₀ : Γ.omega} {y z : Δ.RigExt}
    (hη : omegaMap _ _ κ η = (Γ.toBase K).omega η₀)
    (e : pullRig π z = algebraMap R K r • (𝒜.rigOfOmega η + pullRig π y)) :
    ∃ y', r • y' = z ∧ pullRig π y' = 𝒜.rigOfOmega η + pullRig π y := by
  haveI := IsLocalization.flat K (nonZeroDivisors R)
  have i₁ := injective_of_free _ (Δ.liftSemi_vecExt_bijective K hR (.inl inferInstance)).1
  have i₂ := injective_of_free _ (Γ.omega_baseChange_bijective K hR).1
  have e₁ : pullRig π (z - r • y) = 𝒜.rigOfOmega (algebraMap R K r • η) := by
    rw [map_sub, e, smul_add, pullRig_smul, add_sub_cancel_right, map_smul]
  have e₀ : Δ.rigToExt (z - r • y) = 0 := i₁ (hπ (by
    rw [← rigToExt_pullRig, e₁, map_zero, map_zero]
    exact 𝒜.exact_rigOfOmega_rigToExt.apply_apply_eq_zero _))
  obtain ⟨η', hη'⟩ := (Δ.exact_rigOfOmega_rigToExt _).1 e₀
  have e₃ := 𝒜.rigOfOmega_injective_of_eq_zero hK
    ((pullRig_rigOfOmega π η').symm.trans ((congrArg (pullRig π) hη').trans e₁))
  have e₂ : omegaMap _ _ h η' = r • η₀ := i₂ (by
    rw [toBase_omegaMap, hh, omegaMap_comp_apply, e₃, map_smul, hη, map_smulₛₗ])
  obtain ⟨η'', rfl⟩ := hs r η₀ hr ⟨η', e₂⟩
  rw [← map_smul] at e₂
  rw [toBase_omegaMap, hh, omegaMap_comp_apply] at hη
  refine ⟨Δ.rigOfOmega η'' + y, ?_, ?_⟩
  · rw [smul_add, ← map_smul, ← hi e₂, hη', sub_add_cancel]
  · rw [hκ hη, map_add, pullRig_rigOfOmega]

theorem inf_span_eq [Module.Free R Γ.omega] [Module.Free R Δ.VecExt] (h : Γ ⟶ Δ)
    (hh : PDivGroup.baseChangeMap K h = κ ≫ π) (hκ : Function.Injective (omegaMap _ _ κ))
    (hπ : Function.Bijective (vecExtMap π)) (hi : Function.Injective (omegaMap _ _ h))
    (hs : ∀ (r : R) (w : Γ.omega), r ≠ 0 → r • w ∈ LinearMap.range (omegaMap _ _ h) →
      w ∈ LinearMap.range (omegaMap _ _ h))
    (hC : ∀ (r : R) (y : Δ.RigExt), r ≠ 0 → r • y ∈ Submodule.span R (Set.range (absFrob hR Δ).rig) →
      y ∈ Submodule.span R (Set.range (absFrob hR Δ).rig)) :
    (latOmega κ ⊔ latExt π) ⊓ (Submodule.span K (Set.range (absFrob hK 𝒜).rig)).restrictScalars R =
      Submodule.span R ((absFrob hK 𝒜).rig '' (latOmega κ ⊔ latExt π : Submodule R 𝒜.RigExt)) := by
  refine le_antisymm ?_ (le_inf ?_ (Submodule.span_le.2 ?_))
  · rintro x ⟨hx, hx'⟩
    obtain ⟨r, hr, z, hz, e⟩ := exists_smul_mem hR hK π hπ.2 hx'
    obtain ⟨_, ⟨η, η₀, rfl, hη⟩, _, ⟨y, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y', rfl, e'⟩ := exists_eq_pullRig hR hK κ π h hh hκ hπ.1 hi hs hr hη e
    exact (span_image_eq hR hK κ π).ge ⟨y', hC r _ hr hz, e'⟩
  · refine (span_image_eq hR hK κ π).le.trans ?_
    rintro _ ⟨y, -, rfl⟩
    exact Submodule.mem_sup_right (show pullRig π y ∈ latExt π from ⟨y, rfl⟩)
  · rintro _ ⟨x, -, rfl⟩
    exact Submodule.subset_span (R := K) ⟨x, rfl⟩

end Main

theorem lattice_inf_span_frobenius (hW : GlobalTheory.Published.BarsottiTateDieudonne.WittModule) (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K]
    [IsFractionRing R K] (hR : (p : R) = 0) (hK : (p : K) = 0) (Γ : PDivGroup p R) (𝒜 : PDivGroup p K)
    (κ : Γ.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt]
    (hκ : Function.Bijective (omegaMap _ _ κ)) (hw : Function.Bijective (vecExtMap w)) (h : Γ ⟶ Γ.dual)
    (hh : PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w) (hκ₁ : Function.Surjective (κ.app 1))
    (ha : 𝒜.bidual.hom ≫ dualHom _ _ w = -w) :
    lattice κ w ⊓ (Submodule.span K (Set.range (absFrob hK 𝒜).rig)).restrictScalars R =
      Submodule.span R ((absFrob hK 𝒜).rig '' (lattice κ w : Set 𝒜.RigExt)) := by
  obtain ⟨f₁, -, f₂, -, f₃, -⟩ := T.dieudonne_modules_free_finite hW p R hR Γ
  obtain ⟨-, -, -, -, f₄, -⟩ := T.dieudonne_modules_free_finite hW p R hR Γ.dual
  obtain ⟨-, -, -, -, -, -, f₅, -⟩ := T.dieudonne_modules_free_finite hW p R hR (frobTwist hR Γ.dual)
  obtain ⟨-, -, c₁, c₂⟩ := T.verschiebung_frobenius_kernel_range hW p R hR Γ.dual
  haveI := IsLocalization.flat K (nonZeroDivisors R)
  have k₁ := T.vector_extension_surjective_field hW p K hK _ _ κ hκ₁ hκ
  have k₂ : Function.Bijective (vecExtMap (w ≫ dualHom _ _ κ)) := by
    rw [show ⇑(vecExtMap (w ≫ dualHom _ _ κ)) = _ ∘ _ from funext (vecExtMap_comp _ _)]
    exact hw.comp (vecExtMap_dualHom_bijective hK κ hκ)
  have hπ : Function.Bijective (vecExtMap (weilProj κ w)) := by
    rw [weilProj, ← Category.assoc, show ⇑(vecExtMap ((w ≫ dualHom _ _ κ) ≫ _)) = _ ∘ _ from
      funext (vecExtMap_comp _ _)]
    exact k₂.comp (vecExtMap_iso _)
  have k₃ : Function.Injective (omegaMap _ _ (κ ≫ w ≫ dualHom _ _ κ)) := by
    refine omegaMap_injective_of_antisymm hK _ ?_ ?_
    · rw [show ⇑(vecExtMap (κ ≫ w ≫ dualHom _ _ κ)) = _ ∘ _ from funext (vecExtMap_comp _ _)]
      exact k₁.comp k₂.2
    · rw [dualHom_comp, dualHom_comp, Category.assoc, ← Category.assoc, bidual_hom_dualHom_dualHom,
        Category.assoc, ← Category.assoc _ (dualHom _ _ w), ha, Preadditive.neg_comp, Preadditive.comp_neg]
  have k₄ : Function.Injective (omegaMap _ _ (PDivGroup.baseChangeMap K h)) := by
    rw [hh, weilProj, ← Category.assoc w, ← Category.assoc, omegaMap_comp, LinearMap.coe_comp]
    exact k₃.comp (omegaMap_iso _).1
  have hi : Function.Injective (omegaMap _ _ h) := fun x y e =>
    injective_of_free _ (Γ.dual.omega_baseChange_bijective K hR).1
      (k₄ (by rw [← toBase_omegaMap, ← toBase_omegaMap, e]))
  have hs := (T.omega_injective_saturation hW p R hR _ _ h hi fun x => by
    obtain ⟨u₀, hu₀⟩ := k₁ ((Γ.toBase K).vecExt x)
    obtain ⟨u, rfl⟩ := hπ.2 u₀
    obtain ⟨r, hr, v, hv⟩ := exists_smul_eq _ (Γ.dual.liftSemi_vecExt_bijective K hR (.inl inferInstance)).2 u
    refine ⟨r, hr, v, injective_of_free _ (Γ.liftSemi_vecExt_bijective K hR (.inl inferInstance)).1 ?_⟩
    rw [toBase_vecExtMap, hh, hv, map_smul, vecExtMap_comp, hu₀, map_smulₛₗ]).1
  refine inf_span_eq hR hK κ _ h hh hκ.1 hπ hi hs fun r y hr hy => ?_
  rw [← c₂, ← c₁, LinearMap.mem_ker] at hy ⊢
  rw [map_smul] at hy
  exact (smul_eq_zero.1 hy).resolve_left hr

end GlobalTheory.BadPt.FrobSpan
