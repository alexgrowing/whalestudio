import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitRules

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

private lemma splitOn_base {X' X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) (g : X' ⟶ X) {m : ℕ}
    (z : Fin m → (X ⟶ Z)) (H : SplitOn p x z) : SplitOn p (g ≫ x) fun i => g ≫ z i := by
  obtain ⟨h, hI⟩ := H
  have h' : ∀ i, (g ≫ z i) ≫ p = g ≫ x := fun i => by rw [Category.assoc, h i]
  refine ⟨h', ?_⟩
  let t : Fin m → (X ⟶ pullback p x) := fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])
  let t' : Fin m → (X' ⟶ pullback p (g ≫ x)) := fun i =>
    pullback.lift (g ≫ z i) (𝟙 X') (by rw [h' i, Category.id_comp])
  have ht1 : ∀ i, t i ≫ pullback.fst p x = z i := fun i => pullback.lift_fst _ _ _
  have ht2 : ∀ i, t i ≫ pullback.snd p x = 𝟙 X := fun i => pullback.lift_snd _ _ _
  have ht1' : ∀ i, t' i ≫ pullback.fst p (g ≫ x) = g ≫ z i := fun i => pullback.lift_fst _ _ _
  have ht2' : ∀ i, t' i ≫ pullback.snd p (g ≫ x) = 𝟙 X' := fun i => pullback.lift_snd _ _ _
  let f : pullback p (g ≫ x) ⟶ pullback p x :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by
      rw [pullback.condition, Category.assoc])
  have hf1 : f ≫ pullback.fst p x = pullback.fst p (g ≫ x) := pullback.lift_fst _ _ _
  have hf2 : f ≫ pullback.snd p x = pullback.snd p (g ≫ x) ≫ g := pullback.lift_snd _ _ _
  have hsq : IsPullback f (pullback.snd p (g ≫ x)) (pullback.snd p x) g := by
    have outer : IsPullback (pullback.fst p (g ≫ x)) (pullback.snd p (g ≫ x)) p (g ≫ x) :=
      IsPullback.of_hasPullback _ _
    have right : IsPullback (pullback.fst p x) (pullback.snd p x) p x := IsPullback.of_hasPullback _ _
    exact IsPullback.of_right (h₁₂ := pullback.fst p x) (v₁₃ := p) (h₂₂ := x) (by rwa [hf1]) hf2 right
  have hw : ∀ i, t' i ≫ f = g ≫ t i := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hf1, ht1, ht1']
    · rw [Category.assoc, Category.assoc, hf2, ht2, reassoc_of% ht2', Category.comp_id]
  have hleft : ∀ i, IsPullback (t' i) g f (t i) := by
    intro i
    have outer : IsPullback (𝟙 X') g g (𝟙 X) := IsPullback.of_horiz_isIso ⟨by simp⟩
    exact IsPullback.of_right (h₁₂ := pullback.snd p (g ≫ x)) (h₂₂ := pullback.snd p x) (v₁₃ := g)
      (by rwa [ht2, ht2']) (hw i) hsq.flip
  haveI : IsIso (Sigma.desc t) := hI
  let c : Cofan (fun _ : Fin m => X) := Cofan.mk (pullback p x) t
  have hc : IsColimit c := by
    let e : ∐ (fun _ : Fin m => X) ≅ pullback p x := asIso (Sigma.desc t)
    refine IsColimit.ofIsoColimit (coproductIsCoproduct (fun _ : Fin m => X)) (Cocones.ext e ?_)
    rintro ⟨j⟩
    simp [c, e]
  let c' : Cofan (fun _ : Fin m => X') := Cofan.mk (pullback p (g ≫ x)) t'
  let α : Discrete.functor (fun _ : Fin m => X') ⟶ Discrete.functor (fun _ : Fin m => X) :=
    Discrete.natTrans fun _ => g
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts hc
  obtain ⟨hc'⟩ := hu c' α f (by
      ext ⟨j⟩
      simpa [α, c, c'] using (hw j).symm) (by
      intro ⟨a⟩ ⟨b⟩ ⟨⟨e⟩⟩
      obtain rfl : a = b := e
      exact IsPullback.of_horiz_isIso ⟨by simp⟩) (by
      rintro ⟨j⟩
      exact hleft j)
  have e : Sigma.desc t' = (IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct _) hc').hom := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_desc]
    exact ((coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hc' ⟨j⟩).symm
  show IsIso (Sigma.desc t')
  rw [e]
  infer_instance

private lemma splitOn_perm {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) {m : ℕ}
    (z : Fin m → (X ⟶ Z)) (H : SplitOn p x z) (σ : Equiv.Perm (Fin m)) :
    SplitOn p x fun i => z (σ i) := by
  obtain ⟨h, hI⟩ := H
  refine ⟨fun i => h (σ i), ?_⟩
  have e : (Sigma.desc (fun i => pullback.lift (z (σ i)) (𝟙 X) (by rw [h (σ i), Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p x) =
      (Sigma.reindex σ (fun _ : Fin m => X)).hom ≫
        Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])) := by
    apply Sigma.hom_ext
    intro j
    have e1 : Sigma.ι (fun _ : Fin m => X) j ≫ (Sigma.reindex σ (fun _ : Fin m => X)).hom =
        Sigma.ι (fun _ : Fin m => X) (σ j) := Sigma.ι_reindex_hom σ (fun _ : Fin m => X) j
    rw [Sigma.ι_desc]
    refine Eq.symm ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) e1).trans ?_
    exact Sigma.ι_desc _ _
  rw [e]
  infer_instance

private lemma fromSpec_pb {Y Z : Scheme.{0}} (p : Z ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (hS : IsAffineOpen (p ⁻¹ᵁ U)) : IsPullback (Spec.map (p.app U)) hS.fromSpec hU.fromSpec p := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [Scheme.Hom.app_eq_appLE]
    exact (hU.SpecMap_appLE_fromSpec p hS le_rfl).symm
  · rw [hU.opensRange_fromSpec, hS.opensRange_fromSpec]

private lemma splits_of_splitOn {Y Z : Scheme.{0}} (p : Z ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (hS : IsAffineOpen (p ⁻¹ᵁ U)) (C : Type) [CommRing C] [Algebra Γ(Y, U) C] {m : ℕ} :
    letI : Algebra Γ(Y, U) Γ(Z, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
    ∀ ξ : Fin m → (Γ(Z, p ⁻¹ᵁ U) →ₐ[Γ(Y, U)] C),
      SplitOn p (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) C)) ≫ hU.fromSpec)
        (fun i => Spec.map (CommRingCat.ofHom (ξ i).toRingHom) ≫ hS.fromSpec) → Splits ξ := by
  letI : Algebra Γ(Y, U) Γ(Z, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  intro ξ ⟨h, hI⟩
  have pbA := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(Y, U) C Γ(Z, p ⁻¹ᵁ U))
  have P := pbA.flip.paste_horiz (fromSpec_pb p hU hS).flip
  let Φ := Spec.map (CommRingCat.ofHom (splitMap ξ).toRingHom)
  let t : Fin m → (Spec (CommRingCat.of C) ⟶ pullback p (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) C)) ≫ hU.fromSpec)) :=
    fun i => pullback.lift (Spec.map (CommRingCat.ofHom (ξ i).toRingHom) ≫ hS.fromSpec) (𝟙 _) (by rw [h i, Category.id_comp])
  have claim : sigmaSpec (fun _ : Fin m => CommRingCat.of C) ≫ Φ ≫ P.isoPullback.hom = Sigma.desc t := by
    apply Sigma.hom_ext
    intro j
    rw [ι_sigmaSpec_assoc, Sigma.ι_desc]
    let E : CommRingCat.of (C ⊗[Γ(Y, U)] Γ(Z, p ⁻¹ᵁ U)) ⟶ CommRingCat.of C :=
      CommRingCat.ofHom (splitMap ξ).toRingHom ≫ CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => C) j)
    have hE : Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => C) j)) ≫ Φ = Spec.map E :=
      (Spec.map_comp _ _).symm
    have hE1 : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := Γ(Y, U)) (A := C) (B := Γ(Z, p ⁻¹ᵁ U))) ≫ E = 𝟙 _ := by
      ext c
      simpa [E] using (splitMap_tmul ξ c 1 j).trans (by simp)
    have hE2 : CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := Γ(Y, U)) (A := C) (B := Γ(Z, p ⁻¹ᵁ U))).toRingHom ≫ E =
        CommRingCat.ofHom (ξ j).toRingHom := by
      ext s
      simpa [E] using (splitMap_tmul ξ 1 s j).trans (by simp)
    rw [reassoc_of% hE]
    apply pullback.hom_ext
    · rw [Category.assoc, P.isoPullback_hom_fst, pullback.lift_fst, ← Spec.map_comp_assoc, hE2]
    · rw [Category.assoc, P.isoPullback_hom_snd, pullback.lift_snd, ← Spec.map_comp, hE1, Spec.map_id]
  haveI : IsIso (Sigma.desc t) := hI
  haveI : IsIso (sigmaSpec (fun _ : Fin m => CommRingCat.of C) ≫ Φ ≫ P.isoPullback.hom) := by
    rw [claim]; infer_instance
  haveI : IsIso (Φ ≫ P.isoPullback.hom) := IsIso.of_isIso_comp_left (sigmaSpec (fun _ : Fin m => CommRingCat.of C)) _
  haveI : IsIso Φ := IsIso.of_isIso_comp_right Φ P.isoPullback.hom
  exact isIso_SpecMap_iff.mp this

private lemma spec_fac {B : Type} [CommRing B] {X : Scheme.{0}} (w : Spec (CommRingCat.of B) ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (hw : ⊤ ≤ w ⁻¹ᵁ V) :
    w = Spec.map (w.appLE V ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) ≫ hV.fromSpec := by
  rw [Spec.map_comp, Category.assoc, hV.SpecMap_appLE_fromSpec w (isAffineOpen_top _) hw,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

private lemma app_comp_appLE {X Z Y : Scheme.{0}} (z : X ⟶ Z) (p : Z ⟶ Y) (y : X ⟶ Y) (e : z ≫ p = y) (U : Y.Opens)
    (V : X.Opens) (hy : V ≤ y ⁻¹ᵁ U) (hz : V ≤ z ⁻¹ᵁ (p ⁻¹ᵁ U)) :
    p.app U ≫ z.appLE (p ⁻¹ᵁ U) V hz = y.appLE U V hy := by
  subst e
  rw [Scheme.Hom.comp_appLE]

theorem splitRules : SplitRules := by
  refine ⟨fun p x g _ z H => ⟨splitOn_base p x g z H, fun σ => splitOn_perm p x z H σ⟩, ?_⟩
  intro l Y T U hU B _ y hy z hz hzy hsplit
  haveI := T.fin
  have hS : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  letI := T.alg U
  letI : Algebra Γ(Y, U) B := ((y.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom).toAlgebra
  let ζ : Fin T.d → (Γ(T.Z, T.p ⁻¹ᵁ U) →ₐ[Γ(Y, U)] B) := fun i =>
    { ((z i).appLE (T.p ⁻¹ᵁ U) ⊤ (hz i) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom with
      commutes' := fun a => by
        have e := app_comp_appLE (z i) T.p y (hzy i) U ⊤ hy (hz i)
        have e' := congr($(e) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom)
        exact congr($(e').hom a) }
  refine ⟨ζ, ?_, fun i a => rfl⟩
  let C := Localization.Away (l : B)
  have e1 : awayPt l B ≫ y = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) C)) ≫ hU.fromSpec := by
    conv_lhs => rw [spec_fac y hU hy]
    rw [← Spec.map_comp_assoc]
    congr 2
  have e2 : ∀ i, awayPt l B ≫ z i = Spec.map (CommRingCat.ofHom
      ((IsScalarTower.toAlgHom Γ(Y, U) B C).comp (ζ i)).toRingHom) ≫ hS.fromSpec := by
    intro i
    conv_lhs => rw [spec_fac (z i) hS (hz i)]
    rw [← Spec.map_comp_assoc]
    rfl
  rw [e1, show (fun i => awayPt l B ≫ z i) = _ from funext e2] at hsplit
  exact splits_of_splitOn T.p hU hS C _ hsplit

end UpperTheory.Ru.crystallineComparison
