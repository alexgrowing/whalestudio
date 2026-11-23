import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormResFormPullFormPull
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.HodgeTraceEqSumClopenDecomposition
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential GlobalTheory.W1

namespace UpperTheory.Cb.TraceBlocks

private theorem algTrace_algEquiv {B B' C' : Type} [CommRing B] [CommRing B'] [CommRing C']
    [Algebra B B'] [Algebra B C'] [Module.Finite B B'] [Module.Projective B B']
    [Module.Finite B C'] [Module.Projective B C'] (e : B' ≃ₐ[B] C') (b : B') :
    algTrace B C' (e b) = algTrace B B' b := by
  letI : Algebra B' C' := (e : B' →+* C').toAlgebra
  haveI : IsScalarTower B B' C' := .of_algebraMap_eq fun r ↦ (e.commutes r).symm
  haveI : Algebra.IsPushout B B B' C' :=
    ⟨by
      have := IsBaseChange.ofEquiv (R := B) e.toLinearEquiv
      exact this⟩
  exact algTrace_of_isPushout (B := B) (B' := B') (C := B) (C' := C') b

variable {k : Type} [CommRing k] {A B Z : Scheme.{0}} {sZ : Z ⟶ Sp k} {sA : A ⟶ Sp k}
  {sB : B ⟶ Sp k}

private theorem secTrace_iso (e : A ⟶ B) [IsIso e] (g : B ⟶ Z) [IsFinite g] [Etale g]
    [IsFinite (e ≫ g)] [Etale (e ≫ g)] {U : Z.Opens} (hU : IsAffineOpen U)
    (b : Sec sB (g ⁻¹ᵁ U)) :
    secTrace (f := e ≫ g) sZ sA hU (appSec sB sA e (g ⁻¹ᵁ U) b) =
      secTrace (f := g) sZ sB hU b := by
  letI := secAlg sZ sB g U
  letI := secAlg sZ sA (e ≫ g) U
  haveI := sec_finite (s := sZ) (s' := sB) (f := g) hU
  haveI := sec_etale (s := sZ) (s' := sB) (f := g) hU
  haveI := sec_finite (s := sZ) (s' := sA) (f := e ≫ g) hU
  haveI := sec_etale (s := sZ) (s' := sA) (f := e ≫ g) hU
  haveI := projective_of_etale (Sec sZ U) (Sec sB (g ⁻¹ᵁ U))
  haveI := projective_of_etale (Sec sZ U) (Sec sA ((e ≫ g) ⁻¹ᵁ U))
  have hbij : Function.Bijective (appSec sB sA e (g ⁻¹ᵁ U)) :=
    ConcreteCategory.bijective_of_isIso (e.app (g ⁻¹ᵁ U))
  let E : Sec sB (g ⁻¹ᵁ U) ≃ₐ[Sec sZ U] Sec sA ((e ≫ g) ⁻¹ᵁ U) :=
    AlgEquiv.ofBijective
      { (appSec sB sA e (g ⁻¹ᵁ U)) with
        commutes' := fun u ↦ by
          change (g.app U ≫ e.app (g ⁻¹ᵁ U)).hom u = ((e ≫ g).app U).hom u
          rw [Scheme.Hom.comp_app]
          rfl } hbij
  exact algTrace_algEquiv E b

private theorem omegaTrace_iso (e : A ⟶ B) [IsIso e] (g : B ⟶ Z) [IsFinite g] [Etale g]
    [IsFinite (e ≫ g)] [Etale (e ≫ g)] (he : e ≫ sB = sA) (hg : g ≫ sZ = sB)
    (hga : (e ≫ g) ≫ sZ = sA) (j : ℕ) :
    (Scheme.Modules.pushforward g).map (omegaPull he j) ≫
        (Scheme.Modules.pushforwardComp e g).hom.app _ ≫ omegaTrace hga j = omegaTrace hg j := by
  refine omegaTrace_ext hg j _ fun U hU b' x ↦ ?_
  change (omegaTrace hga j).app U ((omegaPull he j).val.app (Opposite.op (g ⁻¹ᵁ U))
    ((toOmega sB j).app (Opposite.op (g ⁻¹ᵁ U)) (b' • formPull hg U j x))) = _
  rw [omegaPull_toOmega, formPull_smul, formPull_formPull hg he hga]
  refine (omegaTrace_toOm_smul_formPull hga j hU (appSec sB sA e (g ⁻¹ᵁ U) b') x).trans ?_
  rw [secTrace_iso e g hU b']

private theorem hodgeTrace_iso (e : A ⟶ B) [IsIso e] (g : B ⟶ Z) [IsFinite g] [Etale g]
    (g' : A ⟶ Z) [IsFinite g'] [Etale g'] (hgg : g' = e ≫ g) (he : e ≫ sB = sA)
    (hg : g ≫ sZ = sB) (hga : g' ≫ sZ = sA) (j q : ℕ) (x : hodgeH sB j q) :
    hodgeTrace hga j q (hodgePull he j q x) = hodgeTrace hg j q x := by
  subst hgg
  letI := algΓ sZ; letI := algΓ sA; letI := algΓ sB
  obtain ⟨y, rfl⟩ := (coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega sB j) q).surjective x
  have e1 : hodgeTrace hg j q (coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega sB j) q y) =
      cohOn.map k (omegaTrace hg j) ⊤ q y :=
    congrArg (cohOn.map k (omegaTrace hg j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega sB j) q).symm_apply_apply y)
  let ψ := (Scheme.Modules.pushforward g).map (omegaPull he j) ≫
    (Scheme.Modules.pushforwardComp e g).hom.app (Omega sA j)
  have e2 : hodgePull he j q (coh.pushforwardEquiv k (appTop_algebraMap hg) (Omega sB j) q y) =
      coh.pushforwardEquiv k (appTop_algebraMap hga) (Omega sA j) q (cohOn.map k ψ ⊤ q y) := by
    refine Eq.trans ?_ (cohOn.pushforwardEquiv_apply k (appTop_algebraMap hga) _ ⊤ q _).symm
    have s2 := cohOn_pull_pull (appTop_algebraMap hg) (appTop_algebraMap he)
      (appTop_algebraMap hga) (𝟙 _) (omegaPull he j) (le_refl (g ⁻¹ᵁ ⊤)) (le_refl _) (le_refl _) q y
    rw [cohOn.pull_map, Category.comp_id]
    refine Eq.trans ?_ (s2.trans ?_)
    · rfl
    · rw [Category.id_comp]
      rfl
  rw [e2, e1]
  have e3 : hodgeTrace hga j q
      (coh.pushforwardEquiv k (appTop_algebraMap hga) (Omega sA j) q (cohOn.map k ψ ⊤ q y)) =
      cohOn.map k (omegaTrace hga j) ⊤ q (cohOn.map k ψ ⊤ q y) :=
    congrArg (cohOn.map k (omegaTrace hga j) ⊤ q)
      ((coh.pushforwardEquiv k (appTop_algebraMap hga) (Omega sA j) q).symm_apply_apply _)
  have hT : ψ ≫ omegaTrace hga j = omegaTrace hg j :=
    (Category.assoc _ _ _).trans (omegaTrace_iso e g he hg hga j)
  rw [e3, ← hT]
  clear_value ψ
  rw [cohOn.map_comp]
  rfl

end UpperTheory.Cb.TraceBlocks

namespace UpperTheory.Cb.TraceBlocks

private theorem exists_iso_open {Y : Scheme.{0}} (T A : Y.Opens) (hA : A ≤ T) :
    ∃ e : (T.ι ⁻¹ᵁ A).toScheme ⟶ A.toScheme, IsIso e ∧ e ≫ A.ι = (T.ι ⁻¹ᵁ A).ι ≫ T.ι := by
  have hEq : T.ι ''ᵁ (T.ι ⁻¹ᵁ A) = A := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hA
  refine ⟨(T.ι.isoImage (T.ι ⁻¹ᵁ A)).hom ≫ (Y.isoOfEq hEq).hom, inferInstance, ?_⟩
  rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]

private theorem preimage_disjoint {Y : Scheme.{0}} (T : Y.Opens) {M : Type} (W : M → Y.Opens)
    (hd : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (i j : M) (hij : i ≠ j) :
    T.ι ⁻¹ᵁ W i ⊓ T.ι ⁻¹ᵁ W j = ⊥ := by
  have h2 : T.ι ⁻¹ᵁ (W i ⊓ W j) = T.ι ⁻¹ᵁ W i ⊓ T.ι ⁻¹ᵁ W j := rfl
  rw [← h2, hd i j hij]
  rfl

private theorem preimage_iSup_top {Y : Scheme.{0}} (T : Y.Opens) {M : Type} (W : M → Y.Opens)
    (hW : iSup W = T) : iSup (fun m ↦ T.ι ⁻¹ᵁ W m) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hW, Scheme.Opens.ι_preimage_self]

private theorem hodgePull_congr {k : Type} [CommRing k] {X X' : Scheme.{0}} {s : X ⟶ Sp k}
    {s' : X' ⟶ Sp k} {f₁ f₂ : X' ⟶ X} (e : f₁ = f₂) (h₁ : f₁ ≫ s = s') (h₂ : f₂ ≫ s = s')
    (j q : ℕ) (x : hodgeH s j q) : hodgePull h₁ j q x = hodgePull h₂ j q x := by
  subst e
  rfl

end UpperTheory.Cb.TraceBlocks
theorem UpperTheory.Cb.hodgePull_hodgeTrace_eq_sum_restrict_open :
    ∀ (Z Y : Scheme.{0}) (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) [IsFinite c] [Etale c] (h : c ≫ s = s') (V : Z.Opens) (M : Type) [Fintype M] (W : M → Y.Opens), (∀ i j, i ≠ j → W i ⊓ W j = ⊥) → iSup W = c ⁻¹ᵁ V → ∀ (cm : ∀ m, (W m).toScheme ⟶ V.toScheme) (hcm : ∀ m, cm m ≫ V.ι = (W m).ι ≫ c) (hf : ∀ m, IsFinite (cm m)) (he : ∀ m, Etale (cm m)) (a b : ℕ) (w : hodgeH s' a b), hodgePull (f := V.ι) (s' := V.ι ≫ s) rfl a b (hodgeTrace h a b w) = ∑ m, (haveI := hf m; haveI := he m; hodgeTrace (f := cm m) (s := V.ι ≫ s) (s' := (W m).ι ≫ s') (by rw [← Category.assoc, hcm m, Category.assoc, h]) a b (hodgePull (f := (W m).ι) rfl a b w)) := by
  intro Z Y s s' c _ _ h V M _ W hd hW cm hcm hf he a b w
  have hle : ∀ m, W m ≤ c ⁻¹ᵁ V := fun m ↦ hW ▸ le_iSup W m
  choose e hiso hfac using fun m ↦ UpperTheory.Cb.TraceBlocks.exists_iso_open (c ⁻¹ᵁ V) (W m) (hle m)
  have hsq : ∀ m, e m ≫ cm m = ((c ⁻¹ᵁ V).ι ⁻¹ᵁ W m).ι ≫ c ∣_ V := fun m ↦ by
    rw [← cancel_mono V.ι, Category.assoc, hcm m, ← Category.assoc, hfac m, Category.assoc,
      Category.assoc, morphismRestrict_ι]
  have hg : c ∣_ V ≫ V.ι ≫ s = (c ⁻¹ᵁ V).ι ≫ s' := by
    rw [← h, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  have hf' : ∀ m, IsFinite (((c ⁻¹ᵁ V).ι ⁻¹ᵁ W m).ι ≫ c ∣_ V) := fun m ↦ by
    rw [← hsq m]
    haveI := hiso m
    haveI := hf m
    infer_instance
  have he' : ∀ m, Etale (((c ⁻¹ᵁ V).ι ⁻¹ᵁ W m).ι ≫ c ∣_ V) := fun m ↦ by
    rw [← hsq m]
    haveI := hiso m
    haveI := he m
    infer_instance
  rw [hodgePull_hodgeTrace_ι h V a b w]
  refine (UpperTheory.Cb.hodgeTrace_eq_sum_clopen_decomposition V.toScheme (c ⁻¹ᵁ V).toScheme (V.ι ≫ s) ((c ⁻¹ᵁ V).ι ≫ s') (c ∣_ V) hg M
    (fun m ↦ (c ⁻¹ᵁ V).ι ⁻¹ᵁ W m) (UpperTheory.Cb.TraceBlocks.preimage_disjoint _ W hd)
    (UpperTheory.Cb.TraceBlocks.preimage_iSup_top _ W hW) hf' he' a b _).trans ?_
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  haveI := hf m
  haveI := he m
  haveI := hf' m
  haveI := he' m
  haveI := hiso m
  have hes : e m ≫ (W m).ι ≫ s' = ((c ⁻¹ᵁ V).ι ⁻¹ᵁ W m).ι ≫ (c ⁻¹ᵁ V).ι ≫ s' := by
    rw [← Category.assoc, hfac m, Category.assoc]
  have hc₁ : (((c ⁻¹ᵁ V).ι ⁻¹ᵁ W m).ι ≫ (c ⁻¹ᵁ V).ι) ≫ s' =
      ((c ⁻¹ᵁ V).ι ⁻¹ᵁ W m).ι ≫ (c ⁻¹ᵁ V).ι ≫ s' := Category.assoc _ _ _
  have hc₂ : (e m ≫ (W m).ι) ≫ s' = ((c ⁻¹ᵁ V).ι ⁻¹ᵁ W m).ι ≫ (c ⁻¹ᵁ V).ι ≫ s' := by
    rw [Category.assoc, hes]
  have hpull : hodgePull (f := ((c ⁻¹ᵁ V).ι ⁻¹ᵁ W m).ι) rfl a b
        (hodgePull (f := (c ⁻¹ᵁ V).ι) rfl a b w) =
      hodgePull hes a b (hodgePull (f := (W m).ι) rfl a b w) := by
    rw [hodgePull_comp rfl rfl hc₁, hodgePull_comp rfl hes hc₂]
    exact UpperTheory.Cb.TraceBlocks.hodgePull_congr (hfac m).symm hc₁ hc₂ a b w
  rw [hpull]
  exact UpperTheory.Cb.TraceBlocks.hodgeTrace_iso (e m) (cm m) _ (hsq m).symm hes _ _ a b _
