import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CohomZeroEquivContinuous
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct

namespace GlobalTheory.FNC

variable (Λ : Type) [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
variable (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω]

abbrev str (C : Type) [CommRing C] [Algebra K C] : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K C))

abbrev HG (i : ℕ) (C : Type) [CommRing C] [Algebra K C] : Type 1 := GlobalTheory.Et.H Λ i (GlobalTheory.Et.geom Ω (str K C))

def galG (i : ℕ) (C : Type) [CommRing C] [Algebra K C] : Representation Λ (Ω ≃ₐ[K] Ω) (HG Λ K Ω i C) :=
  GlobalTheory.Et.gal Λ Ω (str K C) i

theorem spec_str {C D : Type} [CommRing C] [Algebra K C] [CommRing D] [Algebra K D] (f : C →ₐ[K] D) :
    Spec.map (CommRingCat.ofHom (f : C →+* D)) ≫ str K C = str K D := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact f.comp_algebraMap

def mapG (i : ℕ) {C D : Type} [CommRing C] [Algebra K C] [CommRing D] [Algebra K D] (f : C →ₐ[K] D) :
    HG Λ K Ω i C →ₗ[Λ] HG Λ K Ω i D :=
  GlobalTheory.Et.pull Λ i (GlobalTheory.Et.geomMap Ω (str K D) (Spec.map (CommRingCat.ofHom (f : C →+* D))) (spec_str K f))

theorem geomMap_spec_id (C : Type) [CommRing C] [Algebra K C] :
    GlobalTheory.Et.geomMap Ω (str K C) (Spec.map (CommRingCat.ofHom ((AlgHom.id K C : C →ₐ[K] C) : C →+* C)))
      (spec_str K (AlgHom.id K C)) = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [GlobalTheory.Et.geomMap]
  · simp [GlobalTheory.Et.geomMap]

theorem mapG_id (i : ℕ) (C : Type) [CommRing C] [Algebra K C] :
    mapG Λ K Ω i (AlgHom.id K C) = LinearMap.id := by
  rw [mapG, geomMap_spec_id, GlobalTheory.Et.pull_id]

theorem mapG_comp (i : ℕ) {C D E : Type} [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    [CommRing E] [Algebra K E] (g : D →ₐ[K] E) (f : C →ₐ[K] D) :
    mapG Λ K Ω i (g.comp f) = (mapG Λ K Ω i g).comp (mapG Λ K Ω i f) := by
  have h : GlobalTheory.Et.geomMap Ω (str K E) (Spec.map (CommRingCat.ofHom ((g.comp f : C →ₐ[K] E) : C →+* E)))
      (spec_str K (g.comp f)) =
      GlobalTheory.Et.geomMap Ω (str K E) (Spec.map (CommRingCat.ofHom (g : D →+* E))) (spec_str K g) ≫
      GlobalTheory.Et.geomMap Ω (str K D) (Spec.map (CommRingCat.ofHom (f : C →+* D))) (spec_str K f) := by
    have hs : Spec.map (CommRingCat.ofHom ((g.comp f : C →ₐ[K] E) : C →+* E)) =
        Spec.map (CommRingCat.ofHom (g : D →+* E)) ≫ Spec.map (CommRingCat.ofHom (f : C →+* D)) := by
      rw [← Spec.map_comp]; rfl
    apply pullback.hom_ext
    · rw [GlobalTheory.Et.geomMap, GlobalTheory.Et.geomMap, GlobalTheory.Et.geomMap, pullback.lift_fst, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, Category.assoc, hs]
    · rw [GlobalTheory.Et.geomMap, GlobalTheory.Et.geomMap, GlobalTheory.Et.geomMap, pullback.lift_snd, Category.assoc, pullback.lift_snd,
        pullback.lift_snd]
  rw [mapG, mapG, mapG, h, GlobalTheory.Et.pull_comp]

theorem nonempty_geom (C : Type) [CommRing C] [Algebra K C] (ψ : C →ₐ[K] Ω) :
    Nonempty (GlobalTheory.Et.geom Ω (str K C)) := by
  let pt : Spec (CommRingCat.of Ω) ⟶ GlobalTheory.Et.geom Ω (str K C) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (ψ : C →+* Ω))) (𝟙 _) (by
      rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact ψ.comp_algebraMap)
  exact ⟨pt.base (Classical.arbitrary _)⟩

theorem nontrivial_HG_zero [Nontrivial Λ] (C : Type) [CommRing C] [Algebra K C] (ψ : C →ₐ[K] Ω) :
    Nontrivial (HG Λ K Ω 0 C) := by
  haveI := nonempty_geom K Ω C ψ
  exact GlobalTheory.Et.Model.cohomZero_nontrivial Λ _

section Formal

variable (O : Type) [CommRing O] [Algebra O K]

abbrev H (i : ℕ) (A : Type) [CommRing A] [Algebra O A] : Type 1 := HG Λ K Ω i (K ⊗[O] A)

def gal (i : ℕ) (A : Type) [CommRing A] [Algebra O A] : Representation Λ (Ω ≃ₐ[K] Ω) (H Λ K Ω O i A) :=
  galG Λ K Ω i (K ⊗[O] A)

def map (i : ℕ) {A B : Type} [CommRing A] [Algebra O A] [CommRing B] [Algebra O B] (f : A →ₐ[O] B) :
    H Λ K Ω O i A →ₗ[Λ] H Λ K Ω O i B :=
  mapG Λ K Ω i (Algebra.TensorProduct.map (AlgHom.id K K) f)

theorem map_id (i : ℕ) (A : Type) [CommRing A] [Algebra O A] :
    map Λ K Ω O i (AlgHom.id O A) = LinearMap.id := by
  rw [map, Algebra.TensorProduct.map_id, mapG_id]

theorem map_comp (i : ℕ) {A B D : Type} [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    [CommRing D] [Algebra O D] (g : B →ₐ[O] D) (f : A →ₐ[O] B) :
    map Λ K Ω O i (g.comp f) = (map Λ K Ω O i g).comp (map Λ K Ω O i f) := by
  rw [map, map, map, ← mapG_comp]
  congr 1
  rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

theorem coe_aut_one (A : Type) [CommRing A] [Algebra O A] :
    ((1 : A ≃ₐ[O] A) : A →ₐ[O] A) = AlgHom.id O A := rfl

theorem coe_aut_mul {A : Type} [CommRing A] [Algebra O A] (e e' : A ≃ₐ[O] A) :
    ((e * e' : A ≃ₐ[O] A) : A →ₐ[O] A) = (e : A →ₐ[O] A).comp (e' : A →ₐ[O] A) := rfl

def act (i : ℕ) {G : Type} [Group G] (A : Type) [CommRing A] [Algebra O A] (ρ : G →* (A ≃ₐ[O] A)) :
    Representation Λ G (H Λ K Ω O i A) where
  toFun g := map Λ K Ω O i ((ρ g : A ≃ₐ[O] A) : A →ₐ[O] A)
  map_one' := by
    rw [_root_.map_one, coe_aut_one, map_id]
    rfl
  map_mul' g h := by
    rw [_root_.map_mul, coe_aut_mul, map_comp]
    rfl

theorem nontrivial_H_zero_self [Nontrivial Λ] [IsAlgClosed Ω] : Nontrivial (H Λ K Ω O 0 O) :=
  nontrivial_HG_zero Λ K Ω _ ((Algebra.ofId K Ω).comp (Algebra.TensorProduct.rid O K K).toAlgHom)

theorem subsingleton_geom_self : Subsingleton (GlobalTheory.Et.geom Ω (str K (K ⊗[O] O))) := by
  haveI : IsIso (CommRingCat.ofHom (algebraMap K (K ⊗[O] O))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have : (algebraMap K (K ⊗[O] O) : K → K ⊗[O] O) = (Algebra.TensorProduct.rid O K K).symm := by
      ext x
      exact ((Algebra.TensorProduct.rid O K K).symm.commutes x).symm
    change Function.Bijective (algebraMap K (K ⊗[O] O))
    rw [this]
    exact (Algebra.TensorProduct.rid O K K).symm.bijective
  exact (pullback.snd (str K (K ⊗[O] O)) (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).homeomorph.injective.subsingleton

def ptSelf : GlobalTheory.Et.geom Ω (str K (K ⊗[O] O)) :=
  pullback.lift (Spec.map (CommRingCat.ofHom
      (((Algebra.ofId K Ω).comp (Algebra.TensorProduct.rid O K K).toAlgHom : K ⊗[O] O →ₐ[K] Ω) : K ⊗[O] O →+* Ω)))
    (𝟙 _) (by
      rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact AlgHom.comp_algebraMap _) |>.base (IsLocalRing.closedPoint Ω)

def nearbyCyclesDegreeZeroEquiv : H Λ K Ω O 0 O ≃ₗ[Λ] Λ :=
  haveI := subsingleton_geom_self K Ω O
  (GlobalTheory.Et.H0.e Λ _).trans
    { toFun := fun f => f (ptSelf K Ω O)
      invFun := fun a => ContinuousMap.const _ a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun f => by
        ext y
        exact congrArg f (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }

theorem nonempty_equiv_self : Nonempty (H Λ K Ω O 0 O ≃ₗ[Λ] Λ) := ⟨nearbyCyclesDegreeZeroEquiv Λ K Ω O⟩

theorem gal_self (σ : Ω ≃ₐ[K] Ω) : gal Λ K Ω O 0 O σ = 1 := by
  haveI := subsingleton_geom_self K Ω O
  ext x
  apply (GlobalTheory.Et.H0.e Λ _).injective
  have h := GlobalTheory.Et.H0.e_pull Λ (GlobalTheory.Et.galMap Ω (str K (K ⊗[O] O)) σ) x
  refine h.trans ?_
  ext y
  exact congrArg (GlobalTheory.Et.H0.e Λ _ x) (Subsingleton.elim _ _)

end Formal

section Semilinear

variable {K Ω} {K' : Type} [Field K'] {Ω' : Type} [Field Ω'] [Algebra K' Ω']

def sgeomMap {C D : Type} [CommRing C] [Algebra K C] [CommRing D] [Algebra K' D]
    (κ : K →+* K') (τ : Ω →+* Ω') (hτ : τ.comp (algebraMap K Ω) = (algebraMap K' Ω').comp κ)
    (f : C →+* D) (hf : f.comp (algebraMap K C) = (algebraMap K' D).comp κ) :
    GlobalTheory.Et.geom Ω' (str K' D) ⟶ GlobalTheory.Et.geom Ω (str K C) :=
  pullback.map _ _ _ _ (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom τ))
    (Spec.map (CommRingCat.ofHom κ))
    (by rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hf])
    (by rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hτ])

def smapG (i : ℕ) {C D : Type} [CommRing C] [Algebra K C] [CommRing D] [Algebra K' D]
    (κ : K →+* K') (τ : Ω →+* Ω') (hτ : τ.comp (algebraMap K Ω) = (algebraMap K' Ω').comp κ)
    (f : C →+* D) (hf : f.comp (algebraMap K C) = (algebraMap K' D).comp κ) :
    HG Λ K Ω i C →ₗ[Λ] HG Λ K' Ω' i D :=
  GlobalTheory.Et.pull Λ i (sgeomMap κ τ hτ f hf)

theorem smapG_id (i : ℕ) (C : Type) [CommRing C] [Algebra K C]
    (hτ : (RingHom.id Ω).comp (algebraMap K Ω) = (algebraMap K Ω).comp (RingHom.id K))
    (hf : (RingHom.id C).comp (algebraMap K C) = (algebraMap K C).comp (RingHom.id K)) :
    smapG Λ i (RingHom.id K) (RingHom.id Ω) hτ (RingHom.id C) hf = LinearMap.id := by
  have h : sgeomMap (RingHom.id K) (RingHom.id Ω) hτ (RingHom.id C) hf = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [sgeomMap]
  rw [smapG, h, GlobalTheory.Et.pull_id]

theorem smapG_congr (i : ℕ) {C D : Type} [CommRing C] [Algebra K C] [CommRing D] [Algebra K' D]
    {κ : K →+* K'} {τ : Ω →+* Ω'} {hτ : τ.comp (algebraMap K Ω) = (algebraMap K' Ω').comp κ}
    {f f' : C →+* D} (hf : f.comp (algebraMap K C) = (algebraMap K' D).comp κ) (h : f = f') :
    smapG Λ i κ τ hτ f hf = smapG Λ i κ τ hτ f' (h ▸ hf) := by
  subst h; rfl

theorem smapG_comp (i : ℕ) {K'' Ω'' : Type} [Field K''] [Field Ω''] [Algebra K'' Ω'']
    {C D E : Type} [CommRing C] [Algebra K C] [CommRing D] [Algebra K' D] [CommRing E] [Algebra K'' E]
    (κ : K →+* K') (τ : Ω →+* Ω') (hτ : τ.comp (algebraMap K Ω) = (algebraMap K' Ω').comp κ)
    (f : C →+* D) (hf : f.comp (algebraMap K C) = (algebraMap K' D).comp κ)
    (κ' : K' →+* K'') (τ' : Ω' →+* Ω'') (hτ' : τ'.comp (algebraMap K' Ω') = (algebraMap K'' Ω'').comp κ')
    (g : D →+* E) (hg : g.comp (algebraMap K' D) = (algebraMap K'' E).comp κ') :
    smapG Λ i (κ'.comp κ) (τ'.comp τ)
      (by rw [RingHom.comp_assoc, hτ, ← RingHom.comp_assoc, hτ', RingHom.comp_assoc]) (g.comp f)
      (by rw [RingHom.comp_assoc, hf, ← RingHom.comp_assoc, hg, RingHom.comp_assoc]) =
      (smapG Λ i κ' τ' hτ' g hg).comp (smapG Λ i κ τ hτ f hf) := by
  have h : sgeomMap (κ'.comp κ) (τ'.comp τ)
      (by rw [RingHom.comp_assoc, hτ, ← RingHom.comp_assoc, hτ', RingHom.comp_assoc]) (g.comp f)
      (by rw [RingHom.comp_assoc, hf, ← RingHom.comp_assoc, hg, RingHom.comp_assoc]) =
      sgeomMap κ' τ' hτ' g hg ≫ sgeomMap κ τ hτ f hf := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      simp only [sgeomMap, pullback.map]
      rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, CommRingCat.ofHom_comp,
        Spec.map_comp]
    · rw [Category.assoc]
      simp only [sgeomMap, pullback.map]
      rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, CommRingCat.ofHom_comp,
        Spec.map_comp]
  rw [smapG, smapG, smapG, h, GlobalTheory.Et.pull_comp]

end Semilinear

section SemilinearFormal

variable {K Ω} {K' : Type} [Field K'] {Ω' : Type} [Field Ω'] [Algebra K' Ω']
variable {O : Type} [CommRing O] [Algebra O K] {O' : Type} [CommRing O'] [Algebra O' K']

theorem tensor_ringHom_ext {A B : Type} [CommRing A] [Algebra O A] [Ring B] {f g : K ⊗[O] A →+* B}
    (h : ∀ k a, f (k ⊗ₜ a) = g (k ⊗ₜ a)) : f = g := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k a => exact h k a
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def tmap {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O' A']
    (ο : O →+* O') (κ : K →+* K') (hκ : κ.comp (algebraMap O K) = (algebraMap O' K').comp ο)
    (φ : A →+* A') (hφ : φ.comp (algebraMap O A) = (algebraMap O' A').comp ο) :
    K ⊗[O] A →+* K' ⊗[O'] A' :=
  letI : Algebra O (K' ⊗[O'] A') := ((algebraMap O' (K' ⊗[O'] A')).comp ο).toAlgebra
  (Algebra.TensorProduct.lift (R := O) (S := O)
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom : K' →+* K' ⊗[O'] A').comp κ
      commutes' := fun r => by
        change (κ (algebraMap O K r)) ⊗ₜ[O'] (1 : A') = algebraMap O' (K' ⊗[O'] A') (ο r)
        rw [← RingHom.comp_apply κ, hκ, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply] }
    { toRingHom := (Algebra.TensorProduct.includeRight.toRingHom : A' →+* K' ⊗[O'] A').comp φ
      commutes' := fun r => by
        change (1 : K') ⊗ₜ[O'] (φ (algebraMap O A r)) = algebraMap O' (K' ⊗[O'] A') (ο r)
        rw [← RingHom.comp_apply φ, hφ, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul] }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem tmap_tmul {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O' A']
    (ο : O →+* O') (κ : K →+* K') (hκ : κ.comp (algebraMap O K) = (algebraMap O' K').comp ο)
    (φ : A →+* A') (hφ : φ.comp (algebraMap O A) = (algebraMap O' A').comp ο) (k : K) (a : A) :
    tmap ο κ hκ φ hφ (k ⊗ₜ a) = κ k ⊗ₜ φ a := by
  letI : Algebra O (K' ⊗[O'] A') := ((algebraMap O' (K' ⊗[O'] A')).comp ο).toAlgebra
  change (κ k ⊗ₜ[O'] (1 : A')) * ((1 : K') ⊗ₜ[O'] φ a) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem tmap_algebraMap {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O' A']
    (ο : O →+* O') (κ : K →+* K') (hκ : κ.comp (algebraMap O K) = (algebraMap O' K').comp ο)
    (φ : A →+* A') (hφ : φ.comp (algebraMap O A) = (algebraMap O' A').comp ο) :
    (tmap ο κ hκ φ hφ).comp (algebraMap K (K ⊗[O] A)) = (algebraMap K' (K' ⊗[O'] A')).comp κ := by
  refine RingHom.ext fun k => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.algebraMap_apply, tmap_tmul, map_one]
  rfl

theorem tmap_id {A : Type} [CommRing A] [Algebra O A]
    (hκ : (RingHom.id K).comp (algebraMap O K) = (algebraMap O K).comp (RingHom.id O))
    (hφ : (RingHom.id A).comp (algebraMap O A) = (algebraMap O A).comp (RingHom.id O)) :
    tmap (RingHom.id O) (RingHom.id K) hκ (RingHom.id A) hφ = RingHom.id _ :=
  tensor_ringHom_ext fun k a => by rw [tmap_tmul]; rfl

theorem tmap_comp {K'' : Type} [Field K''] {O'' : Type} [CommRing O''] [Algebra O'' K'']
    {A A' A'' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O' A'] [CommRing A''] [Algebra O'' A'']
    (ο : O →+* O') (κ : K →+* K') (hκ : κ.comp (algebraMap O K) = (algebraMap O' K').comp ο)
    (φ : A →+* A') (hφ : φ.comp (algebraMap O A) = (algebraMap O' A').comp ο)
    (ο' : O' →+* O'') (κ' : K' →+* K'') (hκ' : κ'.comp (algebraMap O' K') = (algebraMap O'' K'').comp ο')
    (φ' : A' →+* A'') (hφ' : φ'.comp (algebraMap O' A') = (algebraMap O'' A'').comp ο') :
    tmap (ο'.comp ο) (κ'.comp κ) (by rw [RingHom.comp_assoc, hκ, ← RingHom.comp_assoc, hκ', RingHom.comp_assoc])
      (φ'.comp φ) (by rw [RingHom.comp_assoc, hφ, ← RingHom.comp_assoc, hφ', RingHom.comp_assoc]) =
      (tmap ο' κ' hκ' φ' hφ').comp (tmap ο κ hκ φ hφ) :=
  tensor_ringHom_ext fun k a => by rw [RingHom.comp_apply, tmap_tmul, tmap_tmul, tmap_tmul]; rfl

def smap (i : ℕ) {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O' A']
    (ο : O →+* O') (κ : K →+* K') (hκ : κ.comp (algebraMap O K) = (algebraMap O' K').comp ο)
    (τ : Ω →+* Ω') (hτ : τ.comp (algebraMap K Ω) = (algebraMap K' Ω').comp κ)
    (φ : A →+* A') (hφ : φ.comp (algebraMap O A) = (algebraMap O' A').comp ο) :
    H Λ K Ω O i A →ₗ[Λ] H Λ K' Ω' O' i A' :=
  smapG Λ i κ τ hτ (tmap ο κ hκ φ hφ) (tmap_algebraMap ο κ hκ φ hφ)

theorem smap_congr (i : ℕ) {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O' A']
    {ο₁ ο₂ : O →+* O'} {κ₁ κ₂ : K →+* K'} {τ₁ τ₂ : Ω →+* Ω'} {φ₁ φ₂ : A →+* A'}
    {hκ₁ : κ₁.comp (algebraMap O K) = (algebraMap O' K').comp ο₁}
    {hτ₁ : τ₁.comp (algebraMap K Ω) = (algebraMap K' Ω').comp κ₁}
    {hφ₁ : φ₁.comp (algebraMap O A) = (algebraMap O' A').comp ο₁}
    {hκ₂ : κ₂.comp (algebraMap O K) = (algebraMap O' K').comp ο₂}
    {hτ₂ : τ₂.comp (algebraMap K Ω) = (algebraMap K' Ω').comp κ₂}
    {hφ₂ : φ₂.comp (algebraMap O A) = (algebraMap O' A').comp ο₂}
    (e₁ : ο₁ = ο₂) (e₂ : κ₁ = κ₂) (e₃ : τ₁ = τ₂) (e₄ : φ₁ = φ₂) :
    smap Λ i ο₁ κ₁ hκ₁ τ₁ hτ₁ φ₁ hφ₁ = smap Λ i ο₂ κ₂ hκ₂ τ₂ hτ₂ φ₂ hφ₂ := by
  subst e₁ e₂ e₃ e₄; rfl

theorem smap_id (i : ℕ) (A : Type) [CommRing A] [Algebra O A]
    (hκ : (RingHom.id K).comp (algebraMap O K) = (algebraMap O K).comp (RingHom.id O))
    (hτ : (RingHom.id Ω).comp (algebraMap K Ω) = (algebraMap K Ω).comp (RingHom.id K))
    (hφ : (RingHom.id A).comp (algebraMap O A) = (algebraMap O A).comp (RingHom.id O)) :
    smap Λ i (RingHom.id O) (RingHom.id K) hκ (RingHom.id Ω) hτ (RingHom.id A) hφ = LinearMap.id := by
  rw [smap, smapG_congr Λ i _ (tmap_id hκ hφ), smapG_id]

theorem smap_comp (i : ℕ) {K'' Ω'' : Type} [Field K''] [Field Ω''] [Algebra K'' Ω''] {O'' : Type} [CommRing O'']
    [Algebra O'' K''] {A A' A'' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O' A'] [CommRing A'']
    [Algebra O'' A'']
    (ο : O →+* O') (κ : K →+* K') (hκ : κ.comp (algebraMap O K) = (algebraMap O' K').comp ο)
    (τ : Ω →+* Ω') (hτ : τ.comp (algebraMap K Ω) = (algebraMap K' Ω').comp κ)
    (φ : A →+* A') (hφ : φ.comp (algebraMap O A) = (algebraMap O' A').comp ο)
    (ο' : O' →+* O'') (κ' : K' →+* K'') (hκ' : κ'.comp (algebraMap O' K') = (algebraMap O'' K'').comp ο')
    (τ' : Ω' →+* Ω'') (hτ' : τ'.comp (algebraMap K' Ω') = (algebraMap K'' Ω'').comp κ')
    (φ' : A' →+* A'') (hφ' : φ'.comp (algebraMap O' A') = (algebraMap O'' A'').comp ο') :
    smap Λ i (ο'.comp ο) (κ'.comp κ) (by rw [RingHom.comp_assoc, hκ, ← RingHom.comp_assoc, hκ', RingHom.comp_assoc])
      (τ'.comp τ) (by rw [RingHom.comp_assoc, hτ, ← RingHom.comp_assoc, hτ', RingHom.comp_assoc])
      (φ'.comp φ) (by rw [RingHom.comp_assoc, hφ, ← RingHom.comp_assoc, hφ', RingHom.comp_assoc]) =
      (smap Λ i ο' κ' hκ' τ' hτ' φ' hφ').comp (smap Λ i ο κ hκ τ hτ φ hφ) := by
  rw [smap, smap, smap, smapG_congr Λ i _ (tmap_comp ο κ hκ φ hφ ο' κ' hκ' φ' hφ'), smapG_comp]

def wrep (i : ℕ) {W : Type} [Group W] (A : Type) [CommRing A] [Algebra O A]
    (ο : W →* (O ≃+* O)) (κ : W →* (K ≃+* K)) (τ : W →* (Ω ≃+* Ω)) (φ : W →* (A ≃+* A))
    (hκ : ∀ w, ((κ w : K ≃+* K) : K →+* K).comp (algebraMap O K) = (algebraMap O K).comp (ο w : O →+* O))
    (hτ : ∀ w, ((τ w : Ω ≃+* Ω) : Ω →+* Ω).comp (algebraMap K Ω) = (algebraMap K Ω).comp (κ w : K →+* K))
    (hφ : ∀ w, ((φ w : A ≃+* A) : A →+* A).comp (algebraMap O A) = (algebraMap O A).comp (ο w : O →+* O)) :
    Representation Λ W (H Λ K Ω O i A) where
  toFun w := smap Λ i (ο w : O →+* O) (κ w : K →+* K) (hκ w) (τ w : Ω →+* Ω) (hτ w) (φ w : A →+* A) (hφ w)
  map_one' := by
    rw [smap_congr Λ i (ο₂ := RingHom.id O) (κ₂ := RingHom.id K) (τ₂ := RingHom.id Ω) (φ₂ := RingHom.id A)
      (hκ₂ := by rw [RingHom.id_comp, RingHom.comp_id]) (hτ₂ := by rw [RingHom.id_comp, RingHom.comp_id])
      (hφ₂ := by rw [RingHom.id_comp, RingHom.comp_id])
      (by rw [_root_.map_one]; rfl) (by rw [_root_.map_one]; rfl) (by rw [_root_.map_one]; rfl)
      (by rw [_root_.map_one]; rfl), smap_id]
    rfl
  map_mul' w w' := by
    rw [smap_congr Λ i (ο₂ := (ο w : O →+* O).comp (ο w' : O →+* O)) (κ₂ := (κ w : K →+* K).comp (κ w' : K →+* K))
      (τ₂ := (τ w : Ω →+* Ω).comp (τ w' : Ω →+* Ω)) (φ₂ := (φ w : A →+* A).comp (φ w' : A →+* A))
      (hκ₂ := by rw [RingHom.comp_assoc, hκ w', ← RingHom.comp_assoc, hκ w, RingHom.comp_assoc])
      (hτ₂ := by rw [RingHom.comp_assoc, hτ w', ← RingHom.comp_assoc, hτ w, RingHom.comp_assoc])
      (hφ₂ := by rw [RingHom.comp_assoc, hφ w', ← RingHom.comp_assoc, hφ w, RingHom.comp_assoc])
      (by rw [_root_.map_mul]; rfl) (by rw [_root_.map_mul]; rfl) (by rw [_root_.map_mul]; rfl)
      (by rw [_root_.map_mul]; rfl), smap_comp]
    rfl

end SemilinearFormal

example : (gal ℤ_[2] ℚ_[3] (AlgebraicClosure ℚ_[3]) ℤ_[3] 2 ℤ_[3]) 1 = 1 := map_one _

example : Nontrivial (H ℤ_[2] ℚ_[3] (AlgebraicClosure ℚ_[3]) ℤ_[3] 0 ℤ_[3]) := nontrivial_H_zero_self _ _ _ _

example : Nonempty (H ℤ_[2] ℚ_[3] (AlgebraicClosure ℚ_[3]) ℤ_[3] 0 ℤ_[3] ≃ₗ[ℤ_[2]] ℤ_[2]) :=
  nonempty_equiv_self _ _ _ _

example (σ : AlgebraicClosure ℚ_[3] ≃ₐ[ℚ_[3]] AlgebraicClosure ℚ_[3]) :
    gal ℤ_[2] ℚ_[3] (AlgebraicClosure ℚ_[3]) ℤ_[3] 0 ℤ_[3] σ = 1 :=
  gal_self _ _ _ _ σ

example : smap ℤ_[2] (K := ℚ_[3]) (Ω := AlgebraicClosure ℚ_[3]) 1 (RingHom.id ℤ_[3]) (RingHom.id ℚ_[3]) rfl
    (RingHom.id _) rfl (RingHom.id ℤ_[3]) rfl = LinearMap.id :=
  smap_id _ _ _ _ _ _

end GlobalTheory.FNC

end
