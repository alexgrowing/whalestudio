import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelFramesBaseChange
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ChainPts.KerTens

theorem sum_pullback_eq_zero_iff {X : Scheme.{0}} {R : Type} [CommRing R] (w : Sp R ⟶ X) (Q : X.Modules)
    [Q.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) (hw : ⊤ ≤ w ⁻¹ᵁ V) [Algebra Γ(X, V) R]
    (halg : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (algebraMap Γ(X, V) R a) = w.appLE V ⊤ hw a)
    {r : ℕ} (q : Fin r → Γ(Q, V)) (c : Fin r → R) :
    ∑ l, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c l) • pullbackSections w Q hw (q l) = 0 ↔
      ∑ l, c l ⊗ₜ[Γ(X, V)] q l = 0 := by
  letI := appLEAlgebra w hw
  letI := appLEModule w ((Scheme.Modules.pullback w).obj Q) hw
  haveI := appLE_isScalarTower w ((Scheme.Modules.pullback w).obj Q) hw
  have h := isBaseChange_pullbackSections w Q (isAffineOpen_top _) hV hw
  let φ : R ≃ₐ[Γ(X, V)] Γ(Sp R, ⊤) :=
    { (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv with commutes' := halg }
  have key : h.equiv (TensorProduct.congr φ.toLinearEquiv (LinearEquiv.refl _ _) (∑ l, c l ⊗ₜ[Γ(X, V)] q l)) =
      ∑ l, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c l) • pullbackSections w Q hw (q l) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [TensorProduct.congr_tmul, IsBaseChange.equiv_tmul]
    rfl
  rw [← key, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

theorem mem_kerAt_iff {X : Scheme.{0}} {R : Type} [CommRing R] (w : Sp R ⟶ X) {F Q : X.Modules} (u : F ⟶ Q)
    {V : X.Opens} (hw : ⊤ ≤ w ⁻¹ᵁ V) {r : ℕ} (e : Fin r → Γ(F, V)) (c : Fin r → R) :
    c ∈ kerAt w u hw e ↔
      ∑ l, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c l) • pullbackSections w Q hw (u.app V (e l)) = 0 := by
  simp only [kerAt, Set.mem_setOf_eq, map_sum, Scheme.Modules.Hom.app_smul, pullback_map_app_pullbackSections]

theorem eq_zero_of_tmul {R S N : Type} [CommRing R] [CommRing S] [AddCommGroup N] [Module S N] (φ : R ≃+* S) (x : N)
    (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal],
      letI : Algebra S (Localization.AtPrime 𝔪) :=
        ((algebraMap R (Localization.AtPrime 𝔪)).comp φ.symm.toRingHom).toAlgebra
      (1 : Localization.AtPrime 𝔪) ⊗ₜ[S] x = 0) : x = 0 := by
  by_contra hx
  have hI : Ideal.comap φ.toRingHom (LinearMap.ker (LinearMap.toSpanSingleton S N x)) ≠ ⊤ := fun k =>
    hx (by simpa using (Ideal.eq_top_iff_one _).1 k)
  obtain ⟨𝔪, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  letI : Algebra S (Localization.AtPrime 𝔪) :=
    ((algebraMap R (Localization.AtPrime 𝔪)).comp φ.symm.toRingHom).toAlgebra
  haveI := IsLocalization.isLocalization_of_base_ringEquiv 𝔪.primeCompl (Localization.AtPrime 𝔪) φ
  obtain ⟨⟨_, s, hs, rfl⟩, h0⟩ := (IsLocalizedModule.eq_zero_iff (𝔪.primeCompl.map φ)
    (TensorProduct.mk S (Localization.AtPrime 𝔪) N 1)).1 (h 𝔪)
  exact hs (hle h0)

theorem main : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (F Q : X.Modules) [Q.IsQuasicoherent] (u : F ⟶ Q) (V : X.Opens) (r : ℕ) (e : Fin r → Γ(F, V)) (c : Fin r → R), (∀ (hV : IsAffineOpen V) [Algebra Γ(X, V) R] (hw : ⊤ ≤ (spMap (algebraMap Γ(X, V) R) ≫ hV.fromSpec) ⁻¹ᵁ V), c ∈ kerAt (spMap (algebraMap Γ(X, V) R) ≫ hV.fromSpec) u hw e ↔ ∑ l, c l ⊗ₜ[Γ(X, V)] (u.app V (e l) : Γ(Q, V)) = 0) ∧ (∀ (w : Sp R ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ V), c ∈ kerAt w u hw e ↔ ∀ (𝔪 : Ideal R) [𝔪.IsMaximal] (hw' : ⊤ ≤ (spMap (algebraMap R (Localization.AtPrime 𝔪)) ≫ w) ⁻¹ᵁ V), (fun l => algebraMap R (Localization.AtPrime 𝔪) (c l)) ∈ kerAt (spMap (algebraMap R (Localization.AtPrime 𝔪)) ≫ w) u hw' e) ∧ ∀ (w : Sp R ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ V) (V' : X.Opens) (hle : V' ≤ V) (hw' : ⊤ ≤ w ⁻¹ᵁ V'), kerAt w u hw e = kerAt w u hw' fun l => resM F hle (e l) := by
  intro X R _ F Q _ u V r e c
  refine ⟨fun hV _ hw => ?_, fun w hw => ?_, fun w hw V' hle hw' => ?_⟩
  · rw [mem_kerAt_iff]
    refine sum_pullback_eq_zero_iff _ Q hV hw (fun a => ?_) _ c
    have h1 : hV.fromSpec.appLE V ⊤ hV.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(X, V)).inv := by
      rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      simp
    have h2 := Scheme.Hom.appLE_comp_appLE (spMap (algebraMap Γ(X, V) R)) hV.fromSpec V ⊤ ⊤
      hV.fromSpec_preimage_self.ge le_rfl
    rw [h1] at h2
    have h3 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap Γ(X, V) R))
    exact (congr($h3 a)).trans (congr($h2 a))
  · let φ : R ≃+* Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
    have loc : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal] (hw' : ⊤ ≤ (spMap (algebraMap R (Localization.AtPrime 𝔪)) ≫ w) ⁻¹ᵁ V),
        letI : Algebra Γ(Sp R, ⊤) (Localization.AtPrime 𝔪) :=
          ((algebraMap R (Localization.AtPrime 𝔪)).comp φ.symm.toRingHom).toAlgebra
        (fun l => algebraMap R (Localization.AtPrime 𝔪) (c l)) ∈
          kerAt (spMap (algebraMap R (Localization.AtPrime 𝔪)) ≫ w) u hw' e ↔
        (1 : Localization.AtPrime 𝔪) ⊗ₜ[Γ(Sp R, ⊤)] (∑ l, φ (c l) • pullbackSections w Q hw (u.app V (e l))) = 0 := by
      intro 𝔪 _ hw'
      letI : Algebra Γ(Sp R, ⊤) (Localization.AtPrime 𝔪) :=
          ((algebraMap R (Localization.AtPrime 𝔪)).comp φ.symm.toRingHom).toAlgebra
      have H := sum_pullback_eq_zero_iff (spMap (algebraMap R (Localization.AtPrime 𝔪)))
        ((Scheme.Modules.pullback w).obj Q) (V := ⊤) (isAffineOpen_top _) le_rfl (fun a => ?_)
        (fun l => pullbackSections w Q hw (u.app V (e l))) (fun l => algebraMap R (Localization.AtPrime 𝔪) (c l))
      · have hsum : ∑ l, algebraMap R (Localization.AtPrime 𝔪) (c l) ⊗ₜ[Γ(Sp R, ⊤)]
            pullbackSections w Q hw (u.app V (e l)) =
            (1 : Localization.AtPrime 𝔪) ⊗ₜ[Γ(Sp R, ⊤)] (∑ l, φ (c l) • pullbackSections w Q hw (u.app V (e l))) := by
          rw [TensorProduct.tmul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
          congr 1
          exact congrArg (algebraMap R (Localization.AtPrime 𝔪)) (φ.symm_apply_apply _).symm
        rw [← hsum, ← H, mem_kerAt_iff]
        let I := (Scheme.Modules.pullbackComp (spMap (algebraMap R (Localization.AtPrime 𝔪))) w).app Q
        have hx : I.inv.app ⊤ (∑ l, (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime 𝔪))).inv.hom
              (algebraMap R (Localization.AtPrime 𝔪) (c l)) • pullbackSections _ Q hw' (u.app V (e l))) =
            ∑ l, (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime 𝔪))).inv.hom
              (algebraMap R (Localization.AtPrime 𝔪) (c l)) • pullbackSections _ _ (le_rfl : ⊤ ≤ _ ⁻¹ᵁ ⊤)
                (pullbackSections w Q hw (u.app V (e l))) := by
          simp only [map_sum, Scheme.Modules.Hom.app_smul]
          refine Finset.sum_congr rfl fun l _ => ?_
          congr 1
          exact GlobalTheory.Vert.DivPull.pullbackComp_inv_app _ w Q hw le_rfl hw' _
        rw [← hx]
        generalize (∑ l, (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime 𝔪))).inv.hom
              (algebraMap R (Localization.AtPrime 𝔪) (c l)) • pullbackSections _ Q hw' (u.app V (e l))) = t
        refine ⟨fun h0 => by rw [h0, map_zero], fun h0 => ?_⟩
        have h1 : I.hom.app ⊤ (I.inv.app ⊤ t) = t := congr(($(I.inv_hom_id)).app ⊤ t)
        rw [← h1, h0, map_zero]
      · obtain ⟨b, rfl⟩ := φ.surjective a
        have h3 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (Localization.AtPrime 𝔪)))
        refine Eq.trans ?_ (congr($h3 b))
        exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime 𝔪))).inv.hom
          (algebraMap R (Localization.AtPrime 𝔪) t)) (φ.symm_apply_apply b)
    rw [mem_kerAt_iff]
    refine ⟨fun h0 𝔪 _ hw' => (loc 𝔪 hw').2 ?_, fun h0 => eq_zero_of_tmul φ _ fun 𝔪 _ => ?_⟩
    · letI : Algebra Γ(Sp R, ⊤) (Localization.AtPrime 𝔪) :=
          ((algebraMap R (Localization.AtPrime 𝔪)).comp φ.symm.toRingHom).toAlgebra
      exact (congrArg _ h0).trans (TensorProduct.tmul_zero _ _)
    · have hw' : ⊤ ≤ (spMap (algebraMap R (Localization.AtPrime 𝔪)) ≫ w) ⁻¹ᵁ V :=
        (spMap (algebraMap R (Localization.AtPrime 𝔪))).preimage_mono hw
      exact (loc 𝔪 hw').1 (h0 𝔪 hw')
  · unfold kerAt
    have : ∀ l, pullbackSections w F hw' (resM F hle (e l)) = pullbackSections w F hw (e l) := fun l =>
      pullbackSections_res w F hw' hle (e l)
    simp only [this]

end GlobalTheory.ChainPts.KerTens
