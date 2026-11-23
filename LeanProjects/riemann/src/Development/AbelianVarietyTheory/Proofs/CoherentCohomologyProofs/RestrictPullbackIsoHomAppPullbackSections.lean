import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct

universe u

noncomputable section

namespace GlobalTheory.QCoh

section Qcqs

variable {X : Scheme.{u}} (F : X.Modules) {U W : X.Opens}

theorem section_eq_of_cover {ι : Type*} (𝒰 : ι → X.Opens) (h : ∀ i, 𝒰 i ≤ W)
    (hcov : W ≤ iSup 𝒰) (s t : Γ(F, W))
    (H : ∀ i, F.presheaf.map (homOfLE (h i)).op s = F.presheaf.map (homOfLE (h i)).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) 𝒰 W
    (fun i ↦ homOfLE (h i)) hcov s t H

theorem exists_finite_affine_cover_of_isCompact (hW : IsCompact (W : Set X)) :
    ∃ (ι : Type u) (_ : Fintype ι) (𝒰 : ι → X.Opens), (∀ i, IsAffineOpen (𝒰 i)) ∧
      W = iSup 𝒰 := by
  obtain ⟨s, hs', hs⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hW, W.2⟩
  exact ⟨s, hs'.fintype, fun i ↦ i.1.1, fun i ↦ i.1.2, by ext1; simpa using hs⟩

variable [F.IsQuasicoherent]

theorem exists_pow_res_smul_eq_zero_of_isCompact (hW : IsCompact (W : Set X)) (h : W ≤ U)
    (f : Γ(X, U)) (t : Γ(F, W))
    (ht : F.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen f ≤ W)).op t = 0) :
    ∃ n : ℕ, X.presheaf.map (homOfLE h).op f ^ n • t = 0 := by
  obtain ⟨ι, _, 𝒰, haff, hcov⟩ := exists_finite_affine_cover_of_isCompact hW
  have hle (i : ι) : 𝒰 i ≤ W := hcov ▸ le_iSup 𝒰 i
  have H (i : ι) : ∃ n : ℕ, X.presheaf.map (homOfLE ((hle i).trans h)).op f ^ n •
      F.presheaf.map (homOfLE (hle i)).op t = 0 := by
    refine exists_pow_smul_eq_zero F (haff i) _ (V := 𝒰 i ⊓ X.basicOpen f) inf_le_left
      (X.basicOpen_res _ _).symm _ ?_
    rw [res_res, ← res_res F inf_le_left (inf_le_inf_right _ (hle i)), ht, map_zero]
  choose n hn using H
  refine ⟨Finset.univ.sup n, section_eq_of_cover F 𝒰 hle hcov.le _ _ fun i ↦ ?_⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ i))
  rw [F.map_smul, map_pow, res_res_ring, hm, pow_add, mul_smul, hn, smul_zero, map_zero]

theorem exists_pow_res_smul_eq_res_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) (s : Γ(F, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(F, U)), X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • s =
      F.presheaf.map (homOfLE (X.basicOpen_le f)).op t := by
  obtain ⟨ι, _, 𝒰, haff, hcov⟩ := exists_finite_affine_cover_of_isCompact hU
  have hle (i : ι) : 𝒰 i ≤ U := hcov ▸ le_iSup 𝒰 i
  have H (i : ι) : ∃ (n : ℕ) (t : Γ(F, 𝒰 i)),
      X.presheaf.map (homOfLE ((inf_le_left : 𝒰 i ⊓ X.basicOpen f ≤ _).trans (hle i))).op f ^ n •
        F.presheaf.map (homOfLE (inf_le_right : 𝒰 i ⊓ X.basicOpen f ≤ _)).op s =
      F.presheaf.map (homOfLE inf_le_left).op t := by
    have := exists_pow_smul_eq_res F (haff i) (X.presheaf.map (homOfLE (hle i)).op f)
      (V := 𝒰 i ⊓ X.basicOpen f) inf_le_left (X.basicOpen_res _ _).symm
      (F.presheaf.map (homOfLE inf_le_right).op s)
    rwa [res_res_ring] at this
  choose n t ht using H
  have H' (i : ι) : ∃ (t : Γ(F, 𝒰 i)),
      X.presheaf.map (homOfLE ((inf_le_left : 𝒰 i ⊓ X.basicOpen f ≤ _).trans (hle i))).op f ^
        Finset.univ.sup n •
        F.presheaf.map (homOfLE (inf_le_right : 𝒰 i ⊓ X.basicOpen f ≤ _)).op s =
      F.presheaf.map (homOfLE inf_le_left).op t := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ i))
    refine ⟨X.presheaf.map (homOfLE (hle i)).op f ^ m • t i, ?_⟩
    rw [F.map_smul, map_pow, res_res_ring, hm, pow_add, mul_smul, ht]
  generalize Finset.univ.sup n = N at H'
  clear ht t n
  choose t ht using H'
  have ht' (i : ι) (V : X.Opens) (h₁ : V ≤ 𝒰 i) (h₂ : V ≤ X.basicOpen f) :
      F.presheaf.map (homOfLE h₁).op (t i) =
        X.presheaf.map (homOfLE (h₁.trans (hle i))).op f ^ N •
          F.presheaf.map (homOfLE h₂).op s := by
    rw [← res_res F inf_le_left (le_inf h₁ h₂), ← ht, F.map_smul, map_pow, res_res_ring, res_res]
  have H (p : ι × ι) : ∃ m : ℕ,
      X.presheaf.map (homOfLE ((inf_le_left : 𝒰 p.1 ⊓ 𝒰 p.2 ≤ _).trans (hle p.1))).op f ^ m •
        (F.presheaf.map (homOfLE (inf_le_left : 𝒰 p.1 ⊓ 𝒰 p.2 ≤ _)).op (t p.1) -
          F.presheaf.map (homOfLE inf_le_right).op (t p.2)) = 0 := by
    refine exists_pow_res_smul_eq_zero_of_isCompact F
      (hU' _ _ (hle p.1) (𝒰 p.1).2 (haff _).isCompact (hle p.2) (𝒰 p.2).2 (haff _).isCompact)
      _ f _ ?_
    rw [map_sub, res_res, res_res, ht' _ _ _ inf_le_right, ht' _ _ _ inf_le_right, sub_self]
  choose m hm using H
  obtain ⟨T, hT, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) 𝒰 U (fun i ↦ homOfLE (hle i)) hcov.le
    (fun i ↦ X.presheaf.map (homOfLE (hle i)).op f ^ Finset.univ.sup m • t i) (by
      intro i j
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := m) (Finset.mem_univ (i, j)))
      change F.presheaf.map (homOfLE inf_le_left).op _ = F.presheaf.map (homOfLE inf_le_right).op _
      rw [F.map_smul, F.map_smul, map_pow, map_pow, res_res_ring, res_res_ring, ← sub_eq_zero,
        ← smul_sub, hk, pow_add, mul_smul, hm (i, j), smul_zero])
  replace hT (i : ι) : F.presheaf.map (homOfLE (hle i)).op T =
    X.presheaf.map (homOfLE (hle i)).op f ^ Finset.univ.sup m • t i := hT i
  refine ⟨Finset.univ.sup m + N, T, section_eq_of_cover F (fun i ↦ 𝒰 i ⊓ X.basicOpen f)
    (fun _ ↦ inf_le_right) ?_ _ _ fun i ↦ ?_⟩
  · rw [← iSup_inf_eq, ← hcov]
    exact le_inf (X.basicOpen_le f) le_rfl
  · rw [res_res, ← res_res F (hle i) inf_le_left, hT, F.map_smul, F.map_smul, map_pow, map_pow,
      res_res_ring, res_res_ring, ht' _ _ _ inf_le_right, pow_add, mul_smul]

end Qcqs

section Push

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)

theorem pushforward_smul (V : Y.Opens) (r : Γ(Y, V))
    (s : Γ((Scheme.Modules.pushforward f).obj F, V)) :
    r • s = (f.app V r • (show Γ(F, f ⁻¹ᵁ V) from s) : Γ(F, f ⁻¹ᵁ V)) := rfl

instance isQuasicoherent_pushforward [QuasiCompact f] [QuasiSeparated f] [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_affine _).mpr fun V hV g ↦ ?_
  have hc : IsCompact (f ⁻¹ᵁ V : Set X) := f.isCompact_preimage hV.isCompact
  have hs : IsQuasiSeparated (f ⁻¹ᵁ V : Set X) := f.isQuasiSeparated_preimage hV.isQuasiSeparated
  have key (D : X.Opens) (h : D ≤ f ⁻¹ᵁ V) (hD : D = X.basicOpen (f.app V g)) :
      (∀ s : Γ(F, D), ∃ (n : ℕ) (t : Γ(F, f ⁻¹ᵁ V)),
        X.presheaf.map (homOfLE h).op (f.app V g) ^ n • s = F.presheaf.map (homOfLE h).op t) ∧
      (∀ t : Γ(F, f ⁻¹ᵁ V), F.presheaf.map (homOfLE h).op t = 0 →
        ∃ n : ℕ, f.app V g ^ n • t = 0) := by
    subst hD
    refine ⟨exists_pow_res_smul_eq_res_of_qcqs F hc hs _, fun t ht ↦ ?_⟩
    have := exists_pow_res_smul_eq_zero_of_isCompact F hc le_rfl (f.app V g) t (by
      rw [← res_res F h inf_le_right, ht, map_zero])
    rwa [res_self_ring] at this
  obtain ⟨h₁, h₂⟩ := key (f ⁻¹ᵁ Y.basicOpen g) (f.preimage_mono (Y.basicOpen_le g))
    (f.preimage_basicOpen g)
  rw [isLocalizedModule_resBasicOpen_iff]
  refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨n, t, ht⟩ := h₁ s
    refine ⟨n, t, Eq.trans ?_ ht⟩
    rw [pushforward_smul, map_pow]
    congr 2
    exact congr($(f.naturality (homOfLE (Y.basicOpen_le g)).op) g)
  · obtain ⟨n, hn⟩ := h₂ t ht
    exact ⟨n, by rw [pushforward_smul, map_pow]; exact hn⟩

theorem finite_sections_pushforward [IsFinite f] {V : Y.Opens} (hV : IsAffineOpen V)
    [hF : Module.Finite Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V)] :
    Module.Finite Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj F, V) := by
  letI := (f.app V).hom.toAlgebra
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV
  letI : Module Γ(Y, V) Γ(F, f ⁻¹ᵁ V) := Module.compHom _ (f.app V).hom
  haveI : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V) := .of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Finite.trans (R := Γ(Y, V)) Γ(X, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V)

end Push

section Sections

variable {X Y : Scheme.{u}}

theorem hom_app_res {F F' : X.Modules} (φ : F ⟶ F') {U V : X.Opens} (h : V ≤ U) (s : Γ(F, U)) :
    φ.app V (F.presheaf.map (homOfLE h).op s) = F'.presheaf.map (homOfLE h).op (φ.app U s) :=
  congr($(φ.mapPresheaf.naturality (homOfLE h).op) s)

def homAppLinear {F F' : X.Modules} (φ : F ⟶ F') (U : X.Opens) : Γ(F, U) →ₗ[Γ(X, U)] Γ(F', U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' := φ.app_smul

@[simp]
theorem homAppLinear_apply {F F' : X.Modules} (φ : F ⟶ F') (U : X.Opens) (s : Γ(F, U)) :
    homAppLinear φ U s = φ.app U s := rfl

variable (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) {U U' : X.Opens} {V V' : Y.Opens}

abbrev appLEAlgebra (e : U ≤ f ⁻¹ᵁ V) : Algebra Γ(Y, V) Γ(X, U) :=
  (f.appLE V U e).hom.toAlgebra

abbrev appLEModule (e : U ≤ f ⁻¹ᵁ V) : Module Γ(Y, V) Γ(F, U) :=
  Module.compHom Γ(F, U) (f.appLE V U e).hom

theorem appLEModule_smul (e : U ≤ f ⁻¹ᵁ V) (r : Γ(Y, V)) (s : Γ(F, U)) :
    letI := appLEModule f F e
    r • s = f.appLE V U e r • s := rfl

theorem appLE_isScalarTower (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEAlgebra f e
    letI := appLEModule f F e
    IsScalarTower Γ(Y, V) Γ(X, U) Γ(F, U) :=
  letI := appLEAlgebra f e
  letI := appLEModule f F e
  .of_algebraMap_smul fun _ _ ↦ rfl

def pullbackSections (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
    Γ(G, V) →ₗ[Γ(Y, V)] Γ((Scheme.Modules.pullback f).obj G, U) :=
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  { toFun s := ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE e).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s)
    map_add' s t := by
      rw [map_add]
      exact map_add _ _ _
    map_smul' r s :=
      (congr(((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE e).op
        $(((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app_smul r s))).trans
        (((Scheme.Modules.pullback f).obj G).map_smul (homOfLE e) (f.app V r) _) }

theorem pullbackSections_apply (e : U ≤ f ⁻¹ᵁ V) (s : Γ(G, V)) :
    pullbackSections f G e s = ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE e).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s) := rfl

theorem pullbackSections_smul (e : U ≤ f ⁻¹ᵁ V) (r : Γ(Y, V)) (s : Γ(G, V)) :
    pullbackSections f G e (r • s) = f.appLE V U e r • pullbackSections f G e s :=
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  (pullbackSections f G e).map_smul r s

theorem res_pullbackSections (e : U ≤ f ⁻¹ᵁ V) (h : U' ≤ U) (s : Γ(G, V)) :
    ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE h).op (pullbackSections f G e s) =
      pullbackSections f G (h.trans e) s :=
  res_res _ _ _ _

theorem pullbackSections_res (e : U ≤ f ⁻¹ᵁ V') (h : V' ≤ V) (s : Γ(G, V)) :
    pullbackSections f G e (G.presheaf.map (homOfLE h).op s) =
      pullbackSections f G (e.trans (f.preimage_mono h)) s :=
  (congr(((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE e).op
    $(hom_app_res ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) h s))).trans
    (res_res ((Scheme.Modules.pullback f).obj G) (f.preimage_mono h) e _)

theorem pullback_map_app_pullbackSections {G G' : Y.Modules} (φ : G ⟶ G') (e : U ≤ f ⁻¹ᵁ V)
    (s : Γ(G, V)) :
    ((Scheme.Modules.pullback f).map φ).app U (pullbackSections f G e s) =
      pullbackSections f G' e (φ.app V s) := by
  refine (hom_app_res ((Scheme.Modules.pullback f).map φ) e _).trans ?_
  rw [pullbackSections_apply]
  congr 1
  exact congr(($((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)).app V s).symm

theorem res_bijective_of_eq (h : U' ≤ U) (e : U' = U) :
    Function.Bijective (F.presheaf.map (homOfLE h).op) := by
  subst e
  have : ⇑(F.presheaf.map (homOfLE h).op) = id := funext (res_self F h)
  rw [this]
  exact Function.bijective_id

theorem fromSpec_image_top (hU : IsAffineOpen U) : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

def sectionsEquivFromSpec (hU : IsAffineOpen U) :
    Γ(F, U) ≃ₗ[Γ(X, U)] Γ(F.restrict hU.fromSpec, ⊤) :=
  LinearEquiv.ofBijective (M₂ := Γ(F.restrict hU.fromSpec, ⊤))
    { toFun s := F.presheaf.map (homOfLE (fromSpec_image_le hU ⊤)).op s
      map_add' s t := map_add (F.presheaf.map (homOfLE (fromSpec_image_le hU ⊤)).op).hom s t
      map_smul' r s := (F.map_smul _ r s).trans (restrict_fromSpec_smul F hU ⊤ r _).symm }
    (res_bijective_of_eq F _ (fromSpec_image_top hU))

theorem sectionsEquivFromSpec_apply (hU : IsAffineOpen U) (s : Γ(F, U)) :
    sectionsEquivFromSpec F hU s = F.presheaf.map (homOfLE (fromSpec_image_le hU ⊤)).op s := rfl

end Sections

section SpecCase

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in

def pushforwardSpecΓIso :
    moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom ≅
      Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
  NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (X₁ := (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj M)
    (X₂ := (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).obj M)
    { __ := AddEquiv.refl _
      map_smul' := fun r m ↦ by
        change (φ r • (show Γ(M, ⊤) from m) : Γ(M, ⊤)) =
          ((Spec.map φ).app ⊤ ((Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op
            ((Scheme.ΓSpecIso R).inv r)) • (show Γ(M, (Spec.map φ) ⁻¹ᵁ ⊤) from m) :)
        rw [Scheme.Modules.smul_Spec_def]
        congr 1
        have h₁ := res_self_ring (X := Spec R) (U := ⊤) le_rfl ((Scheme.ΓSpecIso R).inv r)
        have h₂ := res_self_ring (X := Spec S) (U := ⊤) le_rfl ((Scheme.ΓSpecIso S).inv (φ r))
        refine h₂.trans (Eq.trans ?_ congr((Spec.map φ).app ⊤ $h₁).symm)
        exact congr($(Scheme.ΓSpecIso_inv_naturality φ) r) }) fun _ ↦ rfl

set_option backward.isDefEq.respectTransparency false in

def tildePullbackIso :
    ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ≅
      tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) :=
  (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).ofNatIsoRight
    (pushforwardSpecΓIso φ)).leftAdjointUniq
    (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))

set_option backward.isDefEq.respectTransparency false in
theorem tildePullbackIso_hom_app_toOpen (M : ModuleCat.{u} R) (m : M) :
    ((tildePullbackIso φ).hom.app M).app ⊤
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M m)) =
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
      (tilde.toOpen M ⊤ m) := by
  have := Adjunction.unit_leftAdjointUniq_hom_app
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction).ofNatIsoRight
    (pushforwardSpecΓIso φ))
    (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))) M
  exact congr($this m)

set_option backward.isDefEq.respectTransparency false in

def tildeIsoPullback (M : (Spec R).Modules) [M.IsQuasicoherent] :
    tilde ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) ≅
      (Scheme.Modules.pullback (Spec.map φ)).obj M :=
  haveI := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  (tildePullbackIso φ).app _ ≪≫ (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ)

theorem isQuasicoherent_pullback_Spec (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback (Spec.map φ)).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso (tildeIsoPullback φ M)
    (inferInstanceAs (tilde ((ModuleCat.extendScalars φ.hom).obj
      (moduleSpecΓFunctor.obj M))).IsQuasicoherent)

set_option backward.isDefEq.respectTransparency false in
theorem exists_equiv_pullback_Spec (M : (Spec R).Modules) [M.IsQuasicoherent] :
    letI := φ.hom.toAlgebra
    ∃ e : S ⊗[R] Γ(M, ⊤) ≃ₗ[S] Γ((Scheme.Modules.pullback (Spec.map φ)).obj M, ⊤),
      ∀ m, e (1 ⊗ₜ m) =
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ m := by
  letI := φ.hom.toAlgebra
  refine ⟨(tilde.isoTop ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M)) ≪≫
    moduleSpecΓFunctor.mapIso (tildeIsoPullback φ M)).toLinearEquiv, fun m ↦ ?_⟩
  have h₁ := tildePullbackIso_hom_app_toOpen φ (moduleSpecΓFunctor.obj M) m
  have h₂ := congr(($((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality
    M.fromTildeΓ)).app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m))
  have h₃ : M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m) = m :=
    (congr($(Scheme.Modules.toOpen_fromTildeΓ_app M ⊤) m)).trans (res_self M le_rfl m)
  refine Eq.trans congr(((Scheme.Modules.pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤ $h₁) ?_
  refine h₂.symm.trans ?_
  exact congr(((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤ $h₃)

end SpecCase

section Square

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {p : X' ⟶ Y'} {j : X' ⟶ X} {i : Y' ⟶ Y}
  [IsOpenImmersion i] [IsOpenImmersion j] (w : p ≫ i = j ≫ f)

def restrictPullbackIso :
    Scheme.Modules.restrictFunctor i ⋙ Scheme.Modules.pullback p ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor j :=
  (((Scheme.Modules.restrictAdjunction i).comp
    (Scheme.Modules.pullbackPushforwardAdjunction p)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp p i ≪≫ Scheme.Modules.pushforwardCongr w ≪≫
        (Scheme.Modules.pushforwardComp j f).symm)).leftAdjointUniq
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j))

set_option backward.isDefEq.respectTransparency false in
theorem restrictPullbackIso_hom_app_unit (G : Y.Modules) (V : Y.Opens) (s : Γ(G, V)) :
    ((restrictPullbackIso w).hom.app G).app (j ⁻¹ᵁ f ⁻¹ᵁ V)
      (((Scheme.Modules.pullback p).obj (G.restrict i)).presheaf.map
        (eqToHom (show j ⁻¹ᵁ f ⁻¹ᵁ V = p ⁻¹ᵁ i ⁻¹ᵁ V by
          rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage])).op
        (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (G.restrict i)).app (i ⁻¹ᵁ V)
          (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s))) =
    ((Scheme.Modules.pullback f).obj G).presheaf.map (homOfLE (j.image_preimage_le (f ⁻¹ᵁ V))).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s) := by
  have := Adjunction.unit_leftAdjointUniq_hom_app
    (((Scheme.Modules.restrictAdjunction i).comp
    (Scheme.Modules.pullbackPushforwardAdjunction p)).ofNatIsoRight
      (Scheme.Modules.pushforwardComp p i ≪≫ Scheme.Modules.pushforwardCongr w ≪≫
        (Scheme.Modules.pushforwardComp j f).symm))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (Scheme.Modules.restrictAdjunction j)) G
  exact congr(($this).app V s)

set_option backward.isDefEq.respectTransparency false in

theorem restrictPullbackIso_hom_app_pullbackSections (G : Y.Modules) {V : Y.Opens} {V' : Y'.Opens}
    {U' : X'.Opens} (hV : i ''ᵁ V' ≤ V) (e' : U' ≤ p ⁻¹ᵁ V') (e : j ''ᵁ U' ≤ f ⁻¹ᵁ V)
    (s : Γ(G, V)) :
    ((restrictPullbackIso w).hom.app G).app U'
      (pullbackSections p (G.restrict i) e' (G.presheaf.map (homOfLE hV).op s)) =
    pullbackSections f G e s := by
  have h₁ : U' ≤ j ⁻¹ᵁ f ⁻¹ᵁ V := (j.preimage_image_eq U').ge.trans (j.preimage_mono e)
  have h₂ : V' ≤ i ⁻¹ᵁ V := (i.preimage_image_eq V').ge.trans (i.preimage_mono hV)
  have h₃ : j ⁻¹ᵁ f ⁻¹ᵁ V ≤ p ⁻¹ᵁ i ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  have H : ((restrictPullbackIso w).hom.app G).app (j ⁻¹ᵁ f ⁻¹ᵁ V)
      (pullbackSections p (G.restrict i) h₃
        (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s)) =
      pullbackSections f G (j.image_preimage_le (f ⁻¹ᵁ V)) s :=
    restrictPullbackIso_hom_app_unit w G V s
  have H₁ := hom_app_res ((restrictPullbackIso w).hom.app G) h₁ (pullbackSections p (G.restrict i)
    h₃ (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s))
  have H₂ := res_pullbackSections p (G.restrict i) h₃ h₁
    (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s)
  have H₃ := pullbackSections_res p (G.restrict i) e' h₂
    (G.presheaf.map (homOfLE (i.image_preimage_le V)).op s)
  have H₄ := res_res G (i.image_preimage_le V) (i.image_mono h₂) s
  have H₅ := res_pullbackSections f G (j.image_preimage_le (f ⁻¹ᵁ V)) (j.image_mono h₁) s
  rw [H] at H₁
  refine Eq.trans ?_ (H₁.trans H₅)
  exact congr(((restrictPullbackIso w).hom.app G).app U'
    $(congr(pullbackSections p (G.restrict i) e' $H₄).symm.trans (H₃.trans H₂.symm)))

end Square

section Pull

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) {U : X.Opens} {V : Y.Opens}

theorem exists_affine_pair (x : X) {W : X.Opens} (hx : x ∈ W) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧ U ≤ W ∧
      U ≤ f ⁻¹ᵁ V := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ W ⊓ f ⁻¹ᵁ V from ⟨hx, hxV⟩)
      (W ⊓ f ⁻¹ᵁ V).2
  exact ⟨U, V, hU, hV, hxU, fun _ h ↦ (hle h).1, fun _ h ↦ (hle h).2⟩

variable [G.IsQuasicoherent]

set_option backward.isDefEq.respectTransparency false in

instance isQuasicoherent_pullback : ((Scheme.Modules.pullback f).obj G).IsQuasicoherent := by
  refine isQuasicoherent_of_forall_exists_affine _ fun x ↦ ?_
  obtain ⟨U, V, hU, hV, hx, -, e⟩ := exists_affine_pair f x (W := ⊤) trivial
  refine ⟨U, hU, hx, (isQuasicoherent_restrict_fromSpec_iff _ hU).mp ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
    ((restrictPullbackIso (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e)).app G)
    (isQuasicoherent_pullback_Spec (f.appLE V U e) (G.restrict hV.fromSpec))

set_option backward.isDefEq.respectTransparency false in

theorem isBaseChange_pullbackSections (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) :
    letI := appLEAlgebra f e
    letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
    haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
    IsBaseChange Γ(X, U) (pullbackSections f G e) := by
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  obtain ⟨a, ha⟩ := exists_equiv_pullback_Spec (f.appLE V U e) (G.restrict hV.fromSpec)
  have w := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e
  let κ : Γ((Scheme.Modules.pullback (Spec.map (f.appLE V U e))).obj (G.restrict hV.fromSpec), ⊤)
      ≃ₗ[Γ(X, U)] Γ(((Scheme.Modules.pullback f).obj G).restrict hU.fromSpec, ⊤) :=
    (moduleSpecΓFunctor.mapIso ((restrictPullbackIso w).app G)).toLinearEquiv
  refine IsBaseChange.of_equiv
    ((sectionsEquivFromSpec G hV).baseChange Γ(Y, V) Γ(X, U) _ _ ≪≫ₗ a ≪≫ₗ κ ≪≫ₗ
      (sectionsEquivFromSpec _ hU).symm) fun s ↦ ?_
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul, ha, sectionsEquivFromSpec_apply,
    sectionsEquivFromSpec_apply, res_pullbackSections]
  refine Eq.trans ?_ (restrictPullbackIso_hom_app_pullbackSections w G (V' := ⊤) (U' := ⊤)
    (fromSpec_image_le hV ⊤) le_rfl _ s)
  exact congr(κ $(res_self _ le_rfl _)).symm

theorem isBaseChange_of_eq_pullbackSections (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) [alg : Algebra Γ(Y, V) Γ(X, U)]
    [mod : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj G, U)]
    [IsScalarTower Γ(Y, V) Γ(X, U) Γ((Scheme.Modules.pullback f).obj G, U)]
    (halg : ∀ r, algebraMap Γ(Y, V) Γ(X, U) r = f.appLE V U e r)
    (l : Γ(G, V) →ₗ[Γ(Y, V)] Γ((Scheme.Modules.pullback f).obj G, U))
    (hl : ∀ s, l s = pullbackSections f G e s) : IsBaseChange Γ(X, U) l := by
  obtain rfl : mod = appLEModule f _ e := Module.ext' _ _ fun r s ↦ by
    rw [appLEModule_smul, ← halg, algebraMap_smul]
  obtain rfl : alg = appLEAlgebra f e := Algebra.algebra_ext _ _ halg
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  obtain rfl : l = pullbackSections f G e := LinearMap.ext hl
  exact isBaseChange_pullbackSections f G hU hV e

theorem isBaseChange_pullbackSections_of_isPushout (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra A Γ(Y, V)] [Algebra B Γ(X, U)] [Algebra A Γ(X, U)] [Algebra Γ(Y, V) Γ(X, U)]
    [IsScalarTower A B Γ(X, U)] [IsScalarTower A Γ(Y, V) Γ(X, U)]
    [Algebra.IsPushout A B Γ(Y, V) Γ(X, U)]
    (halg : ∀ r, algebraMap Γ(Y, V) Γ(X, U) r = f.appLE V U e r)
    [Module A Γ(G, V)] [IsScalarTower A Γ(Y, V) Γ(G, V)]
    [Module A Γ((Scheme.Modules.pullback f).obj G, U)]
    [Module B Γ((Scheme.Modules.pullback f).obj G, U)]
    [IsScalarTower A B Γ((Scheme.Modules.pullback f).obj G, U)]
    [IsScalarTower B Γ(X, U) Γ((Scheme.Modules.pullback f).obj G, U)]
    (l : Γ(G, V) →ₗ[A] Γ((Scheme.Modules.pullback f).obj G, U))
    (hl : ∀ s, l s = pullbackSections f G e s) : IsBaseChange B l := by
  letI : Module Γ(Y, V) Γ((Scheme.Modules.pullback f).obj G, U) :=
    Module.compHom _ (algebraMap Γ(Y, V) Γ(X, U))
  haveI : IsScalarTower Γ(Y, V) Γ(X, U) Γ((Scheme.Modules.pullback f).obj G, U) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have h := isBaseChange_of_eq_pullbackSections f G hU hV e halg
    { toFun := pullbackSections f G e
      map_add' s t := by rw [← hl, ← hl, ← hl, map_add]
      map_smul' r s := by
        rw [pullbackSections_smul, ← halg]
        rfl } fun _ ↦ rfl
  refine IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange A B Γ(Y, V) Γ(X, U) Γ(G, V)).symm ≪≫ₗ
      h.equiv.restrictScalars B) fun s ↦ ?_
  simp [hl]

theorem finite_sections_pullback (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    [Module.Finite Γ(Y, V) Γ(G, V)] :
    Module.Finite Γ(X, U) Γ((Scheme.Modules.pullback f).obj G, U) :=
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  Module.Finite.equiv (isBaseChange_pullbackSections f G hU hV e).equiv

end Pull

section Exact

variable {X Y : Scheme.{u}} {F F' : X.Modules}

theorem app_injective_of_mono (φ : F ⟶ F') [Mono φ] (U : X.Opens) :
    Function.Injective (φ.app U) := by
  have : Mono ((Scheme.Modules.toPresheaf X).map φ) := inferInstance
  have : Mono (((Scheme.Modules.toPresheaf X).map φ).app (op U)) :=
    (NatTrans.mono_iff_mono_app _).mp this _
  exact (AddCommGrpCat.mono_iff_injective _).mp this

theorem mono_of_locally_app_injective (φ : F ⟶ F')
    (h : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
      Function.Injective (φ.app U)) : Mono φ := by
  refine (Scheme.Modules.toPresheaf X).mono_of_mono_map ((NatTrans.mono_iff_mono_app _).mpr ?_)
  rintro ⟨W⟩
  refine (AddCommGrpCat.mono_iff_injective _).mpr fun s t e ↦ ?_
  choose 𝒰 hx hle hinj using fun x : W ↦ h W x x.2
  refine section_eq_of_cover F 𝒰 hle (fun x hxW ↦ Opens.mem_iSup.mpr ⟨⟨x, hxW⟩, hx _⟩) s t
    fun i ↦ hinj i ?_
  refine (hom_app_res φ (hle i) s).trans (Eq.trans ?_ (hom_app_res φ (hle i) t).symm)
  exact congr(F'.presheaf.map (homOfLE (hle i)).op $e)

theorem epi_of_locally_app_surjective (φ : F ⟶ F')
    (h : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
      Function.Surjective (φ.app U)) : Epi φ := by
  refine ⟨fun {H} a b e ↦ Scheme.Modules.hom_ext _ _ fun W ↦ ?_⟩
  ext s
  choose 𝒰 hx hle hsurj using fun x : W ↦ h W x x.2
  refine section_eq_of_cover H 𝒰 hle (fun x hxW ↦ Opens.mem_iSup.mpr ⟨⟨x, hxW⟩, hx _⟩) _ _
    fun i ↦ ?_
  obtain ⟨t, ht⟩ := hsurj i (F'.presheaf.map (homOfLE (hle i)).op s)
  refine (hom_app_res a (hle i) s).symm.trans (Eq.trans ?_ (hom_app_res b (hle i) s))
  rw [← ht]
  exact congr(($e).app (𝒰 i) t)

set_option backward.isDefEq.respectTransparency false in

theorem app_surjective_of_epi_of_isAffineOpen (φ : F ⟶ F') [Epi φ] [F.IsQuasicoherent]
    [F'.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (φ.app U) := by
  let ψ := (Scheme.Modules.restrictFunctor hU.fromSpec).map φ
  have h := (Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U))).naturality ψ
  have h₁ : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U))).app
    (F.restrict hU.fromSpec)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (F.restrict hU.fromSpec)
  have h₂ : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U))).app
    (F'.restrict hU.fromSpec)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (F'.restrict hU.fromSpec)
  have h₃ : Epi ((𝟭 _).map ψ) := inferInstanceAs (Epi ψ)
  have h₄ : Epi ((moduleSpecΓFunctor ⋙ tilde.functor Γ(X, U)).map ψ) := by
    rw [← epi_comp_iff_of_isIso _ ((Scheme.Modules.fromTildeΓNatTrans (R := Γ(X, U))).app
      (F'.restrict hU.fromSpec)), h]
    infer_instance
  have h₅ : Epi (moduleSpecΓFunctor.map ψ) := (tilde.functor Γ(X, U)).epi_of_epi_map h₄
  have h₆ : Function.Surjective (φ.app (hU.fromSpec ''ᵁ ⊤)) :=
    (ModuleCat.epi_iff_surjective (moduleSpecΓFunctor.map ψ)).mp h₅
  rwa [fromSpec_image_top hU] at h₆

variable (f : X ⟶ Y)

theorem epi_pushforward_map [IsAffineHom f] (φ : F ⟶ F') [Epi φ] [F.IsQuasicoherent]
    [F'.IsQuasicoherent] : Epi ((Scheme.Modules.pushforward f).map φ) := by
  refine epi_of_locally_app_surjective _ fun W y hy ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy W.2
  exact ⟨V, hyV, hle, app_surjective_of_epi_of_isAffineOpen φ (IsAffineOpen.preimage hV f)⟩

theorem shortExact_map_pushforward [IsAffineHom f] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (Scheme.Modules.pushforward f)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact ShortComplex.ShortExact.mk'
    (hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance)
    (inferInstanceAs (Mono ((Scheme.Modules.pushforward f).map S.f))) (epi_pushforward_map f S.g)

theorem exact_map_pullback {S : ShortComplex Y.Modules} (hS : S.Exact) [Epi S.g] :
    (S.map (Scheme.Modules.pullback f)).Exact ∧ Epi (S.map (Scheme.Modules.pullback f)).g :=
  ⟨hS.map_of_epi_of_preservesCokernel _ inferInstance inferInstance,
    inferInstanceAs (Epi ((Scheme.Modules.pullback f).map S.g))⟩

theorem injective_of_isBaseChange_of_flat {A B M M' N N' : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [AddCommGroup N']
    [Module A N'] [Module B N'] [IsScalarTower A B N'] {l : M →ₗ[A] N} {l' : M' →ₗ[A] N'}
    (hl : IsBaseChange B l) (hl' : IsBaseChange B l') (a : M →ₗ[A] M') (b : N →ₗ[B] N')
    (hab : ∀ m, b (l m) = l' (a m)) (ha : Function.Injective a) : Function.Injective b := by
  have : b ∘ₗ hl.equiv.toLinearMap = hl'.equiv.toLinearMap ∘ₗ a.baseChange B := by
    ext m
    simp [hab]
  have h : Function.Injective (b ∘ₗ hl.equiv.toLinearMap) := by
    rw [this]
    exact hl'.equiv.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap a ha)
  exact Function.Injective.of_comp_right h hl.equiv.surjective

theorem mono_pullback_map [Flat f] {G G' : Y.Modules} (φ : G ⟶ G') [Mono φ] [G.IsQuasicoherent]
    [G'.IsQuasicoherent] : Mono ((Scheme.Modules.pullback f).map φ) := by
  refine mono_of_locally_app_injective _ fun W x hx ↦ ?_
  obtain ⟨U, V, hU, hV, hxU, hle, e⟩ := exists_affine_pair f x hx
  refine ⟨U, hxU, hle, ?_⟩
  letI := appLEAlgebra f e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G') e
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G') e
  haveI : Module.Flat Γ(Y, V) Γ(X, U) := f.flat_appLE hV hU e
  exact injective_of_isBaseChange_of_flat (isBaseChange_pullbackSections f G hU hV e)
    (isBaseChange_pullbackSections f G' hU hV e) (homAppLinear φ V)
    (homAppLinear ((Scheme.Modules.pullback f).map φ) U)
    (pullback_map_app_pullbackSections f φ e) (app_injective_of_mono φ V)

theorem shortExact_map_pullback [Flat f] {S : ShortComplex Y.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    (S.map (Scheme.Modules.pullback f)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact ShortComplex.ShortExact.mk' (exact_map_pullback f hS.exact).1 (mono_pullback_map f S.f)
    (exact_map_pullback f hS.exact).2

end Exact

theorem quasicoherent_push_pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (QuasiCompact f → QuasiSeparated f → ∀ F : X.Modules, F.IsQuasicoherent →
      ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent) ∧
    (IsFinite f ∨ IsClosedImmersion f → ∀ F : X.Modules, F.IsQuasicoherent →
      (∀ U : X.Opens, IsAffineOpen U → Module.Finite Γ(X, U) Γ(F, U)) →
      ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent ∧
        ∀ V : Y.Opens, IsAffineOpen V →
          Module.Finite Γ(Y, V) Γ((Scheme.Modules.pushforward f).obj F, V)) ∧
    (IsAffineHom f → ∀ S : ShortComplex X.Modules, S.ShortExact → S.X₂.IsQuasicoherent →
      S.X₃.IsQuasicoherent → (S.map (Scheme.Modules.pushforward f)).ShortExact) ∧
    (∀ G : Y.Modules, G.IsQuasicoherent →
      ((Scheme.Modules.pullback f).obj G).IsQuasicoherent ∧
      ∀ (U : X.Opens) (V : Y.Opens), IsAffineOpen U → IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
        letI := appLEAlgebra f e
        letI := appLEModule f ((Scheme.Modules.pullback f).obj G) e
        haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) e
        IsBaseChange Γ(X, U) (pullbackSections f G e)) ∧
    (∀ S : ShortComplex Y.Modules, S.Exact → Epi S.g →
      (S.map (Scheme.Modules.pullback f)).Exact ∧ Epi (S.map (Scheme.Modules.pullback f)).g) ∧
    (Flat f → ∀ S : ShortComplex Y.Modules, S.ShortExact → S.X₁.IsQuasicoherent →
      S.X₂.IsQuasicoherent → (S.map (Scheme.Modules.pullback f)).ShortExact) := by
  refine ⟨fun _ _ F _ ↦ inferInstance, fun hf F _ hF ↦ ?_,
    fun _ S hS _ _ ↦ shortExact_map_pushforward f hS,
    fun G _ ↦ ⟨inferInstance, fun _ _ hU hV e ↦ isBaseChange_pullbackSections f G hU hV e⟩,
    fun S hS _ ↦ exact_map_pullback f hS, fun _ S hS _ _ ↦ shortExact_map_pullback f hS⟩
  have : IsFinite f := hf.elim id fun _ ↦ inferInstance
  exact ⟨inferInstance, fun V hV ↦
    finite_sections_pushforward f F hV (hF := hF _ (hV.preimage f))⟩

end GlobalTheory.QCoh
