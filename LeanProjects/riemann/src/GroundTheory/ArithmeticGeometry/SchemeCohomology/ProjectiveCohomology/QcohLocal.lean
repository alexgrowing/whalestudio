import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

abbrev resF (F : X.Modules) {U V : X.Opens} (h : V ≤ U) : Γ(F, U) →+ Γ(F, V) :=
  (F.presheaf.map (homOfLE h).op).hom

abbrev resO {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

lemma resF_smul (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) (m : Γ(F, U)) :
    resF F h (r • m) = resO h r • resF F h m :=
  Scheme.Modules.map_smul F (homOfLE h) r m

lemma resF_resF (F : X.Modules) {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (m : Γ(F, U)) :
    resF F h' (resF F h m) = resF F (h'.trans h) m := by
  change (F.presheaf.map (homOfLE h).op ≫ F.presheaf.map (homOfLE h').op).hom m = _
  rw [← Functor.map_comp]
  rfl

lemma resF_self (F : X.Modules) {U : X.Opens} (h : U ≤ U) (m : Γ(F, U)) : resF F h m = m := by
  simp only [resF]
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, F.presheaf.map_id]
  rfl

lemma resO_resO {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (r : Γ(X, U)) :
    resO h' (resO h r) = resO (h'.trans h) r := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom r = _
  rw [← Functor.map_comp]
  rfl

lemma resO_self {U : X.Opens} (h : U ≤ U) (r : Γ(X, U)) : resO h r = r := by
  simp only [resO]
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, X.presheaf.map_id]
  rfl

section Affine

variable (F : X.Modules) {V : X.Opens} (hV : IsAffineOpen V)

lemma fromSpec_image_le (W : (Spec Γ(X, V)).Opens) : hV.fromSpec ''ᵁ W ≤ V := by
  have := hV.fromSpec.image_le_opensRange W
  rwa [hV.opensRange_fromSpec] at this

lemma fromSpec_image_top : hV.fromSpec ''ᵁ ⊤ = V := by
  rw [Scheme.Hom.image_top_eq_opensRange, hV.opensRange_fromSpec]

lemma appIso_inv_fromSpec (W : (Spec Γ(X, V)).Opens) (r : Γ(X, V)) :
    (hV.fromSpec.appIso W).inv
        ((Spec Γ(X, V)).presheaf.map W.leTop.op ((Scheme.ΓSpecIso Γ(X, V)).inv r)) =
      resO (fromSpec_image_le hV W) r := by
  have e : W ≤ hV.fromSpec ⁻¹ᵁ V := by rw [hV.fromSpec_preimage_self]; exact le_top
  have h1 := Scheme.Hom.appLE_appIso_inv_apply hV.fromSpec e r
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, hV.fromSpec_app_self_apply] at h1
  refine Eq.trans ?_ h1
  congr 1

lemma smul_restrict_fromSpec (W : (Spec Γ(X, V)).Opens) (r : Γ(X, V))
    (x : Γ(F.restrict hV.fromSpec, W)) :
    (show Γ(F, hV.fromSpec ''ᵁ W) from r • x) =
      resO (fromSpec_image_le hV W) r • (show Γ(F, hV.fromSpec ''ᵁ W) from x) := by
  rw [Scheme.Modules.smul_Spec_def, ← appIso_inv_fromSpec hV W r]
  rfl

lemma isLocalizing_restrict [F.IsQuasicoherent] :
    IsLocalizing (modulesSpecToSheaf.obj (F.restrict hV.fromSpec)) := by
  have : (F.restrict hV.fromSpec).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor hV.fromSpec F
  have : IsIso (F.restrict hV.fromSpec).fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _
  exact (isIso_fromTildeΓ_iff_isLocalizing _).mp this

lemma isLocalizedModule_restrict [F.IsQuasicoherent] (f : Γ(X, V)) :
    IsLocalizedModule (Submonoid.powers f) ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom :=
  isLocalizing_restrict F hV f

end Affine

theorem qcoh_exists_res_eq (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (f : Γ(X, V)) (m : Γ(F, X.basicOpen f)) :
    ∃ (e : ℕ) (m' : Γ(F, V)), resF F (X.basicOpen_le f) m' = resO (X.basicOpen_le f) f ^ e • m := by
  have hloc := isLocalizedModule_restrict F hV f
  let D : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen f
  have hD : hV.fromSpec ''ᵁ D = X.basicOpen f := hV.fromSpec_image_basicOpen f
  obtain ⟨⟨x, ⟨s, hs⟩⟩, hx⟩ := hloc.surj (show (modulesSpecToSheaf.obj
        (F.restrict hV.fromSpec)).obj.obj (op D) from resF F hD.le m)
  obtain ⟨e, rfl⟩ := hs
  let x' : Γ(F, hV.fromSpec ''ᵁ ⊤) := x
  refine ⟨e, resF F (fromSpec_image_top hV).ge x', ?_⟩
  have hx' : (show Γ(F, hV.fromSpec ''ᵁ D) from
      (f ^ e) • (show Γ(F.restrict hV.fromSpec, D) from resF F hD.le m)) =
      resF F (hV.fromSpec.image_mono le_top) x' := hx
  rw [smul_restrict_fromSpec] at hx'
  have h2 := congrArg (resF F hD.ge) hx'
  rw [resF_smul, resF_resF, resF_resF, resF_self, resO_resO, map_pow] at h2
  rw [resF_resF, ← h2]

theorem qcoh_exists_pow_smul_eq_zero (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (f : Γ(X, V)) (m : Γ(F, V)) (hm : resF F (X.basicOpen_le f) m = 0) :
    ∃ e : ℕ, f ^ e • m = 0 := by
  have hloc := isLocalizing_restrict F hV f
  have hD : hV.fromSpec ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := hV.fromSpec_image_basicOpen f
  let x : Γ(F.restrict hV.fromSpec, ⊤) := resF F (fromSpec_image_top hV).le m
  have hx : ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom x = 0 := by
    change resF F (hV.fromSpec.image_mono le_top) (resF F (fromSpec_image_top hV).le m) = 0
    rw [resF_resF, ← resF_self F (le_refl _) (resF F _ m)]
    have : resF F (hD.le.trans (X.basicOpen_le f)) m =
        resF F hD.le (resF F (X.basicOpen_le f) m) := (resF_resF F _ _ m).symm
    rw [resF_self, this, hm, map_zero]
  obtain ⟨⟨_, e, rfl⟩, he⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) _).mp hx
  refine ⟨e, ?_⟩
  have he' : (show Γ(F, hV.fromSpec ''ᵁ ⊤) from (f ^ e) • x) = 0 := he
  rw [smul_restrict_fromSpec] at he'
  have h2 := congrArg (resF F (fromSpec_image_top hV).ge) he'
  rw [resF_smul, resF_resF, resF_self, resO_resO, resO_self, map_zero] at h2
  exact h2

lemma isIso_hom_of_modulesIso {M N : X.Modules} (e : M ≅ N) :
    @IsIso (SheafOfModules X.ringCatSheaf) _ M N e.hom :=
  ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩

lemma isIso_of_modulesIsIso {M N : X.Modules} (f : M ⟶ N) [IsIso f] :
    @IsIso (SheafOfModules X.ringCatSheaf) _ M N f :=
  isIso_hom_of_modulesIso (asIso f)

section Criterion

variable (F : X.Modules)

lemma isLocalizing_restrict_of {V : X.Opens} (hV : IsAffineOpen V)
    (h₁ : ∀ (f : Γ(X, V)) (m : Γ(F, X.basicOpen f)),
      ∃ (e : ℕ) (m' : Γ(F, V)), resF F (X.basicOpen_le f) m' = resO (X.basicOpen_le f) f ^ e • m)
    (h₂ : ∀ (f : Γ(X, V)) (m : Γ(F, V)), resF F (X.basicOpen_le f) m = 0 →
      ∃ e : ℕ, f ^ e • m = 0) (f : Γ(X, V)) :
    IsLocalizedModule (Submonoid.powers f) ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom := by
  let D : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen f
  have hD : hV.fromSpec ''ᵁ D = X.basicOpen f := hV.fromSpec_image_basicOpen f
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro y
    let y' : Γ(F, hV.fromSpec ''ᵁ D) := y
    obtain ⟨e, m', hm'⟩ := h₁ f (resF F hD.ge y')
    refine ⟨e, (show Γ(F, hV.fromSpec ''ᵁ ⊤) from resF F (fromSpec_image_top hV).le m'), ?_⟩
    have h2 := congrArg (resF F hD.le) hm'
    rw [resF_resF, resF_smul, resF_resF, resF_self, ← map_pow, resO_resO] at h2
    have key : (show Γ(F, hV.fromSpec ''ᵁ D) from
        (f ^ e) • (show Γ(F.restrict hV.fromSpec, D) from y)) =
        resF F (hV.fromSpec.image_mono le_top) (resF F (fromSpec_image_top hV).le m') := by
      rw [smul_restrict_fromSpec, resF_resF]
      exact h2.symm
    exact key
  · intro x hx
    let x' : Γ(F, hV.fromSpec ''ᵁ ⊤) := x
    have hx' : resF F (X.basicOpen_le f) (resF F (fromSpec_image_top hV).ge x') = 0 := by
      have : resF F (hV.fromSpec.image_mono le_top) x' = 0 := hx
      calc resF F (X.basicOpen_le f) (resF F (fromSpec_image_top hV).ge x')
          = resF F hD.ge (resF F (hV.fromSpec.image_mono le_top) x') := by
            rw [resF_resF, resF_resF]
        _ = 0 := by rw [this, map_zero]
    obtain ⟨e, he⟩ := h₂ f _ hx'
    refine ⟨e, ?_⟩
    have h2 := congrArg (resF F (fromSpec_image_top hV).le) he
    rw [resF_smul, resF_resF, resF_self, map_zero] at h2
    have key : (show Γ(F, hV.fromSpec ''ᵁ ⊤) from
        (f ^ e) • (show Γ(F.restrict hV.fromSpec, ⊤) from x)) = 0 := by
      rw [smul_restrict_fromSpec]
      exact h2
    exact key

noncomputable def presentationOverOfRestrict (U : X.Opens) (P : (F.restrict U.ι).Presentation) :
    (F.over U).Presentation :=
  let E := Scheme.Modules.overEquiv U
  let e₁ : E.functor.obj (F.over U) ≅ F.restrict U.ι := (Scheme.Modules.overFunctorEquiv U).app F
  let G : SheafOfModules.{u} (U : Scheme.{u}).ringCatSheaf ⥤
      SheafOfModules.{u} (X.ringCatSheaf.over U) := E.inverse
  haveI : PreservesColimitsOfSize.{u, u} G :=
    Adjunction.leftAdjoint_preservesColimits.{u, u} E.symm.toAdjunction
  (P.map G (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit _ _).symm).ofIsIso
    (G.mapIso e₁.symm ≪≫ (E.unitIso.app _).symm).hom

theorem isQuasicoherent_of_restrict {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (P : ∀ i, Nonempty (F.restrict (U i).ι).Presentation) : F.IsQuasicoherent :=
  let q : SheafOfModules.QuasicoherentData (R := X.ringCatSheaf) F :=
    { I := ι
      X := U
      coversTop := (Opens.coversTop_iff (T := X) U).2 hU
      presentation := fun i => presentationOverOfRestrict F (U i) (P i).some }
  q.isQuasicoherent

lemma nonempty_presentation_restrict {V : X.Opens} (hV : IsAffineOpen V)
    (h : (F.restrict hV.fromSpec).IsQuasicoherent) : Nonempty (F.restrict V.ι).Presentation := by
  have hiso : IsIso (F.restrict hV.fromSpec).fromTildeΓ :=
    @Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _ _ h
  have := isIso_of_modulesIsIso (F.restrict hV.fromSpec).fromTildeΓ
  let P₀ := presentationTilde.{u}
    ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).presheaf.obj (op ⊤)) .univ (by simp) _
    (Submodule.span_eq _)
  let P₁ := P₀.ofIsIso (F.restrict hV.fromSpec).fromTildeΓ
  let P₂ := Scheme.Modules.presentationRestrict hV.isoSpec.hom P₁
  let e := ((Scheme.Modules.restrictFunctorComp hV.isoSpec.hom hV.fromSpec).app F).symm ≪≫
    ((Scheme.Modules.restrictFunctorCongr hV.isoSpec_hom_fromSpec).app F)
  have := isIso_hom_of_modulesIso e
  exact ⟨P₂.ofIsIso e.hom⟩

end Criterion

section Finite

variable (F : X.Modules) [F.IsQuasicoherent]

lemma finite_basicOpen {V : X.Opens} (hV : IsAffineOpen V) [Module.Finite Γ(X, V) Γ(F, V)]
    (g : Γ(X, V)) : Module.Finite Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) := by
  classical
  obtain ⟨r, gen, hgen⟩ := Module.Finite.exists_fin (R := Γ(X, V)) (M := Γ(F, V))
  refine ⟨⟨Finset.univ.image (fun i => resF F (X.basicOpen_le g) (gen i)), ?_⟩⟩
  rw [eq_top_iff]
  rintro t -
  obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F hV g t
  have hm'' : m' ∈ Submodule.span Γ(X, V) (Set.range gen) := hgen ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hm''
  have hu : IsUnit (resO (X.basicOpen_le g) g ^ e) :=
    (X.toRingedSpace.isUnit_res_basicOpen g).pow e
  have hres : resF F (X.basicOpen_le g) m' ∈ Submodule.span Γ(X, X.basicOpen g)
      (↑(Finset.univ.image (fun i => resF F (X.basicOpen_le g) (gen i)))) := by
    rw [← hc, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [resF_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  rw [hm'] at hres
  exact (Submodule.smul_mem_iff_of_isUnit _ hu).mp hres

lemma exists_pow_smul_mem_span {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) {ι : Type*}
    [Fintype ι] (m : ι → Γ(F, U))
    (hm : Submodule.span Γ(X, X.basicOpen f) (Set.range fun i => resF F (X.basicOpen_le f) (m i)) = ⊤)
    (x : Γ(F, U)) : ∃ n : ℕ, f ^ n • x ∈ Submodule.span Γ(X, U) (Set.range m) := by
  have := hU.isLocalization_basicOpen f
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    (hm ▸ Submodule.mem_top : resF F (X.basicOpen_le f) x ∈ _)
  choose p hab using fun i => IsLocalization.surj (Submonoid.powers f) (c i)
  let a : ι → Γ(X, U) := fun i => (p i).1
  choose k hk using fun i => (Submonoid.mem_powers_iff _ _).mp (p i).2.2
  let B := ∑ i, k i
  have hkB : ∀ i, k i ≤ B := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  let n : Γ(F, U) := ∑ i, (a i * f ^ (B - k i)) • m i
  have hn : n ∈ Submodule.span Γ(X, U) (Set.range m) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hres : resF F (X.basicOpen_le f) (f ^ B • x - n) = 0 := by
    rw [map_sub, resF_smul, ← hc, Finset.smul_sum, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [resF_smul, smul_smul, map_mul]
    congr 1
    have h1 := hab i
    rw [← hk i] at h1
    change c i * resO (X.basicOpen_le f) (f ^ k i) = resO (X.basicOpen_le f) (a i) at h1
    rw [← h1, mul_comm, mul_assoc, ← map_mul, ← pow_add, Nat.add_sub_cancel' (hkB i)]
  obtain ⟨E, hE⟩ := qcoh_exists_pow_smul_eq_zero F hU f _ hres
  refine ⟨E + B, ?_⟩
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hE
  rw [hE]
  exact Submodule.smul_mem _ _ hn

lemma finite_of_finite_basicOpen {U : X.Opens} (hU : IsAffineOpen U) (s : Finset Γ(X, U))
    (hs : Ideal.span (s : Set Γ(X, U)) = ⊤)
    (h : ∀ f ∈ s, Module.Finite Γ(X, X.basicOpen f) Γ(F, X.basicOpen f)) :
    Module.Finite Γ(X, U) Γ(F, U) := by
  classical
  have gens : ∀ f : s, ∃ (r : ℕ) (m : Fin r → Γ(F, U)), Submodule.span Γ(X, X.basicOpen f.1)
      (Set.range fun i => resF F (X.basicOpen_le f.1) (m i)) = ⊤ := by
    intro f
    have := h f.1 f.2
    obtain ⟨r, gen, hgen⟩ := Module.Finite.exists_fin (R := Γ(X, X.basicOpen f.1))
      (M := Γ(F, X.basicOpen f.1))
    choose e m hm using fun i => qcoh_exists_res_eq F hU f.1 (gen i)
    refine ⟨r, m, eq_top_iff.2 ?_⟩
    rw [← hgen, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hu : IsUnit (resO (X.basicOpen_le f.1) f.1 ^ e i) :=
      (X.toRingedSpace.isUnit_res_basicOpen f.1).pow (e i)
    refine (Submodule.smul_mem_iff_of_isUnit _ hu).mp ?_
    rw [← hm i]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose r m hm using gens
  let N := Submodule.span Γ(X, U) (Set.range fun p : (Σ f : s, Fin (r f)) => m p.1 p.2)
  refine ⟨⟨(Finset.univ : Finset (Σ f : s, Fin (r f))).image (fun p => m p.1 p.2), ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, eq_top_iff]
  rintro x -
  have hpow : ∀ f : s, ∃ n : ℕ, f.1 ^ n • x ∈ N := by
    intro f
    obtain ⟨n, hn⟩ := exists_pow_smul_mem_span F hU f.1 (m f) (hm f) x
    refine ⟨n, Submodule.span_mono ?_ hn⟩
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨f, i⟩, rfl⟩
  choose n hn using hpow
  let K := ∑ f, n f
  have hnK : ∀ f, n f ≤ K := fun f => Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ f)
  let I : Ideal Γ(X, U) := N.comap (LinearMap.toSpanSingleton Γ(X, U) Γ(F, U) x)
  have hI : Ideal.span ((fun a => a ^ K) '' (s : Set Γ(X, U))) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    change f ^ K • x ∈ N
    rw [← Nat.sub_add_cancel (hnK ⟨f, hf⟩), pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hn ⟨f, hf⟩)
  rw [Ideal.span_pow_eq_top _ hs K, top_le_iff] at hI
  have h1 : (1 : Γ(X, U)) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end Finite

theorem isQuasicoherent_of_affineCover (F : X.Modules) {ι : Type u} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h₁ : ∀ i (f : Γ(X, V i)) (m : Γ(F, X.basicOpen f)),
      ∃ (e : ℕ) (m' : Γ(F, V i)), resF F (X.basicOpen_le f) m' = resO (X.basicOpen_le f) f ^ e • m)
    (h₂ : ∀ i (f : Γ(X, V i)) (m : Γ(F, V i)), resF F (X.basicOpen_le f) m = 0 →
      ∃ e : ℕ, f ^ e • m = 0) :
    F.IsQuasicoherent := by
  refine isQuasicoherent_of_restrict F V hcov fun i => nonempty_presentation_restrict F (hV i) ?_
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing]
  exact isLocalizing_restrict_of F (hV i) (h₁ i) (h₂ i)

theorem isCoherent_of_affineCover (F : X.Modules) [F.IsQuasicoherent] {ι : Type u}
    (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (hfin : ∀ i, Module.Finite Γ(X, V i) Γ(F, V i)) : IsCoherent F := by
  refine ⟨inferInstance, fun U hU => ?_⟩
  have key : ∀ x : U, ∃ f : Γ(X, U), x.1 ∈ X.basicOpen f ∧
      Module.Finite Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) := by
    intro x
    have hx : x.1 ∈ iSup V := hcov ▸ trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU (hV i) x.1 ⟨x.2, hi⟩
    have := hfin i
    have hg := finite_basicOpen F (hV i) g
    exact ⟨f, hxf, hfg ▸ hg⟩
  choose f hxf hfinf using key
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, hxf ⟨x, hx⟩⟩
  obtain ⟨s, hs, h1⟩ := Submodule.mem_span_finite_of_mem_span
    (hspan ▸ Submodule.mem_top : (1 : Γ(X, U)) ∈ Ideal.span (Set.range f))
  refine finite_of_finite_basicOpen F hU s ((Ideal.eq_top_iff_one _).mpr h1) fun g hg => ?_
  obtain ⟨x, rfl⟩ := hs (Finset.mem_coe.mpr hg)
  exact hfinf x

section Kernel

instance toPresheaf_preservesZeroMorphisms :
    (Scheme.Modules.toPresheaf X).PreservesZeroMorphisms :=
  ⟨fun _ _ => by ext; rfl⟩

instance toPresheaf_eval_preservesZeroMorphisms (W : X.Opens) :
    (Scheme.Modules.toPresheaf X ⋙ (evaluation _ AddCommGrpCat.{u}).obj (op W)).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

variable {F G : X.Modules} (φ : F ⟶ G)

noncomputable def kernelForkAppIsLimit (W : X.Opens) :
    IsLimit ((KernelFork.ofι (kernel.ι φ) (kernel.condition φ)).map
      (Scheme.Modules.toPresheaf X ⋙ (evaluation _ AddCommGrpCat.{u}).obj (op W))) := by
  haveI : PreservesLimit (parallelPair φ 0) (Scheme.Modules.toPresheaf X) := inferInstance
  haveI : PreservesLimit (parallelPair φ 0 ⋙ Scheme.Modules.toPresheaf X)
      ((evaluation _ AddCommGrpCat.{u}).obj (op W)) :=
    evaluation_preservesLimit (parallelPair φ 0 ⋙ Scheme.Modules.toPresheaf X) (op W)
  exact KernelFork.mapIsLimit _ (kernelIsKernel φ) _

lemma kernel_ι_app_injective (W : X.Opens) : Function.Injective ((kernel.ι φ).app W) := by
  have := Fork.IsLimit.mono (kernelForkAppIsLimit φ W)
  exact (AddCommGrpCat.mono_iff_injective _).mp this

lemma kernel_ι_app_exact (W : X.Opens) (m : Γ(F, W)) (hm : φ.app W m = 0) :
    ∃ k : Γ(kernel φ, W), (kernel.ι φ).app W k = m := by
  let ψ : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ Γ(F, W) :=
    AddCommGrpCat.ofHom ((zmultiplesHom _ m).comp AddEquiv.ulift.toAddMonoidHom)
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (kernelForkAppIsLimit φ W) ψ (by
      ext x
      change φ.app W (x.down • m) = 0
      rw [map_zsmul, hm, smul_zero])
  refine ⟨l.hom ⟨1⟩, ?_⟩
  have := congrArg (fun g => g.hom (⟨1⟩ : ULift.{u} ℤ)) hl
  change (kernel.ι φ).app W (l.hom ⟨1⟩) = (1 : ℤ) • m at this
  rwa [one_smul] at this

instance isQuasicoherent_kernel [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (kernel φ).IsQuasicoherent := by
  have hinj := kernel_ι_app_injective φ
  refine isQuasicoherent_of_affineCover _ (fun U : X.affineOpens => (U : X.Opens)) (fun U => U.2)
    (iSup_affineOpens_eq_top X) ?_ ?_
  · intro U f k
    obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F U.2 f ((kernel.ι φ).app _ k)
    have h0 : resF G (X.basicOpen_le f) (φ.app U m') = 0 := by
      have := congrArg (φ.app _) hm'
      rw [Scheme.Modules.Hom.app_smul] at this
      rw [show resF G (X.basicOpen_le f) (φ.app U m') = φ.app _ (resF F (X.basicOpen_le f) m') from
        (NatTrans.naturality_apply φ.mapPresheaf (homOfLE (X.basicOpen_le f)).op m').symm, this]
      rw [show φ.app _ ((kernel.ι φ).app _ k) = 0 from
        congrArg (fun g => g.app (X.basicOpen f) k) (kernel.condition φ) |>.trans rfl, smul_zero]
    obtain ⟨e', he'⟩ := qcoh_exists_pow_smul_eq_zero G U.2 f _ h0
    rw [← Scheme.Modules.Hom.app_smul] at he'
    obtain ⟨k', hk'⟩ := kernel_ι_app_exact φ _ _ he'
    refine ⟨e' + e, k', hinj _ ?_⟩
    rw [show (kernel.ι φ).app _ (resF (kernel φ) (X.basicOpen_le f) k') =
        resF F (X.basicOpen_le f) ((kernel.ι φ).app _ k') from
        NatTrans.naturality_apply (kernel.ι φ).mapPresheaf (homOfLE (X.basicOpen_le f)).op k',
      hk', resF_smul, hm', Scheme.Modules.Hom.app_smul, smul_smul, map_pow, ← pow_add]
  · intro U f k hk
    have h0 : resF F (X.basicOpen_le f) ((kernel.ι φ).app _ k) = 0 := by
      rw [show resF F (X.basicOpen_le f) ((kernel.ι φ).app _ k) =
          (kernel.ι φ).app _ (resF (kernel φ) (X.basicOpen_le f) k) from
          (NatTrans.naturality_apply (kernel.ι φ).mapPresheaf (homOfLE (X.basicOpen_le f)).op k).symm,
        hk, map_zero]
    obtain ⟨e, he⟩ := qcoh_exists_pow_smul_eq_zero F U.2 f _ h0
    refine ⟨e, hinj _ ?_⟩
    rw [Scheme.Modules.Hom.app_smul, he, map_zero]

theorem isCoherent_kernel [IsLocallyNoetherian X] (hF : IsCoherent F) [G.IsQuasicoherent] :
    IsCoherent (kernel φ) := by
  have := hF.1
  refine ⟨isQuasicoherent_kernel φ, fun U hU => ?_⟩
  have := hF.2 U hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let ι' : Γ(kernel φ, U) →ₗ[Γ(X, U)] Γ(F, U) :=
    { toFun := (kernel.ι φ).app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  exact Module.Finite.of_injective ι' (kernel_ι_app_injective φ U)

end Kernel

end

end GroundTheory.Arith.SchemeCoh
