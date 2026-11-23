import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.BijDescent

theorem exists_stage_isIso {K : Type} [SmallCategory K] [IsFiltered K]
    {R₀ A B : CommRingCat.{0}} (P EA EB : K ⥤ CommRingCat.{0}) (β : ∀ k, R₀ ⟶ P.obj k)
    (fA : R₀ ⟶ A) (fB : R₀ ⟶ B) (hA : fA.hom.FinitePresentation)
    (hB : fB.hom.FinitePresentation) (g : A ⟶ B) (hg : fA ≫ g = fB)
    (uA : P ⟶ EA) (vA : (Functor.const K).obj A ⟶ EA) (uB : P ⟶ EB)
    (vB : (Functor.const K).obj B ⟶ EB)
    (hpoA : ∀ k, IsPushout fA (β k) (vA.app k) (uA.app k))
    (hpoB : ∀ k, IsPushout fB (β k) (vB.app k) (uB.app k))
    (cA : Cocone EA) (hcA : IsColimit cA) (cB : Cocone EB) (hcB : IsColimit cB)
    (iA : A ⟶ cA.pt) (iB : B ⟶ cB.pt) (hiA : ∀ k, vA.app k ≫ cA.ι.app k = iA)
    (hiB : ∀ k, vB.app k ≫ cB.ι.app k = iB) (G : cA.pt ⟶ cB.pt) [IsIso G]
    (hG : ∀ k, (hpoA k).desc (g ≫ vB.app k) (uB.app k)
      (by rw [reassoc_of% hg, (hpoB k).w]) ≫ cB.ι.app k = cA.ι.app k ≫ G) :
    ∃ m : K, ∀ (l : K) (_ : m ⟶ l), IsIso ((hpoA l).desc (g ≫ vB.app l) (uB.app l)
      (by rw [reassoc_of% hg, (hpoB l).w])) := by
  let gs : ∀ k, EA.obj k ⟶ EB.obj k := fun k =>
    (hpoA k).desc (g ≫ vB.app k) (uB.app k) (by rw [reassoc_of% hg, (hpoB k).w])
  have gv : ∀ k, vA.app k ≫ gs k = g ≫ vB.app k := fun k => (hpoA k).inl_desc _ _ _
  have gu : ∀ k, uA.app k ≫ gs k = uB.app k := fun k => (hpoA k).inr_desc _ _ _
  have vAn : ∀ {k l} (f : k ⟶ l), vA.app k ≫ EA.map f = vA.app l := fun f =>
    (vA.naturality f).symm.trans (Category.id_comp _)
  have vBn : ∀ {k l} (f : k ⟶ l), vB.app k ≫ EB.map f = vB.app l := fun f =>
    (vB.naturality f).symm.trans (Category.id_comp _)
  have gnat : ∀ {k l} (f : k ⟶ l), EA.map f ≫ gs l = gs k ≫ EB.map f := by
    intro k l f
    apply (hpoA k).hom_ext
    · rw [reassoc_of% (vAn f), gv, reassoc_of% (gv k), vBn]
    · rw [← uA.naturality_assoc, gu, reassoc_of% (gu k), uB.naturality]
  obtain ⟨k₀⟩ := IsFiltered.nonempty (C := K)
  have hAG : iA ≫ G = g ≫ iB := by
    rw [← hiA k₀, Category.assoc, ← hG, reassoc_of% (gv k₀), hiB]
  let αA : (Functor.const K).obj R₀ ⟶ EA := (Functor.const K).map fA ≫ vA
  let αB : (Functor.const K).obj R₀ ⟶ EB := (Functor.const K).map fB ≫ vB
  obtain ⟨m, s, hs⟩ := GlobalTheory.TorsorColim.exists_stage_factor (I := Unit) EA αA fB cA hcA hB
    (fun _ => iB ≫ inv G) (fun _ k => by
      change fB ≫ iB ≫ inv G = (fA ≫ vA.app k) ≫ cA.ι.app k
      rw [Category.assoc, hiA, ← hg, Category.assoc, ← reassoc_of% hAG, IsIso.hom_inv_id,
        Category.comp_id])
  have hs1 : fB ≫ s () = fA ≫ vA.app m := (hs ()).1
  have hs2 : s () ≫ cA.ι.app m = iB ≫ inv G := (hs ()).2
  obtain ⟨m₁, p₁, hp₁⟩ := GlobalTheory.TorsorColim.exists_stage_eq (I := Unit) EA αA fA cA hcA
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hA)) (k := m)
    (fun _ => g ≫ s ()) (fun _ => vA.app m) (fun _ => by rw [reassoc_of% hg, hs1]; rfl)
    (fun _ => rfl) (fun _ => by
      rw [Category.assoc, hs2, hiA, ← reassoc_of% hAG, IsIso.hom_inv_id, Category.comp_id])
  obtain ⟨m₂, p₂, hp₂⟩ := GlobalTheory.TorsorColim.exists_stage_eq (I := Unit) EB αB fB cB hcB
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hB)) (k := m)
    (fun _ => s () ≫ gs m) (fun _ => vB.app m)
    (fun _ => by
      change fB ≫ s () ≫ gs m = fB ≫ vB.app m
      rw [reassoc_of% hs1, gv, reassoc_of% hg])
    (fun _ => rfl) (fun _ => by
      rw [Category.assoc, hG, reassoc_of% hs2, IsIso.inv_hom_id, Category.comp_id, hiB])
  let a := IsFiltered.leftToMax m₁ m₂
  let b := IsFiltered.rightToMax m₁ m₂
  let e := IsFiltered.coeqHom (p₁ ≫ a) (p₂ ≫ b)
  have he : (p₁ ≫ a) ≫ e = (p₂ ≫ b) ≫ e := IsFiltered.coeq_condition _ _
  refine ⟨IsFiltered.coeq (p₁ ≫ a) (p₂ ≫ b), fun l f => ?_⟩
  obtain ⟨F', hF'⟩ : ∃ F' : m ⟶ l, F' = (p₁ ≫ a) ≫ e ≫ f := ⟨_, rfl⟩
  have h₁ : g ≫ s () ≫ EA.map F' = vA.app l := by
    subst hF'
    have := hp₁ ()
    simp only [Category.assoc] at this
    rw [← vAn ((p₁ ≫ a) ≫ e ≫ f)]
    simp only [EA.map_comp, Category.assoc]
    rw [reassoc_of% this]
  have h₂ : s () ≫ gs m ≫ EB.map F' = vB.app l := by
    subst hF'
    have := hp₂ ()
    simp only [Category.assoc] at this
    rw [← Category.assoc (p₁ ≫ a), he, ← vBn ((p₂ ≫ b) ≫ e ≫ f)]
    simp only [EB.map_comp, Category.assoc]
    rw [reassoc_of% this]
  let σ : EB.obj l ⟶ EA.obj l := (hpoB l).desc (s () ≫ EA.map F') (uA.app l)
    (by rw [reassoc_of% hs1, vAn, (hpoA l).w])
  have σv : vB.app l ≫ σ = s () ≫ EA.map F' := (hpoB l).inl_desc _ _ _
  have σu : uB.app l ≫ σ = uA.app l := (hpoB l).inr_desc _ _ _
  refine ⟨σ, ?_, ?_⟩
  · apply (hpoA l).hom_ext
    · change vA.app l ≫ gs l ≫ σ = _
      rw [reassoc_of% (gv l), σv, h₁, Category.comp_id]
    · change uA.app l ≫ gs l ≫ σ = _
      rw [reassoc_of% (gu l), σu, Category.comp_id]
  · apply (hpoB l).hom_ext
    · change vB.app l ≫ σ ≫ gs l = _
      rw [reassoc_of% σv, gnat, h₂, Category.comp_id]
    · change uB.app l ≫ σ ≫ gs l = _
      rw [reassoc_of% σu, gu, Category.comp_id]

end GlobalTheory.BijDescent

namespace GlobalTheory.BijDescent

theorem bijective_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (j : J) (R S : Type) [CommRing R] [CommRing S]
    [Algebra (F.obj j) R] [Algebra (F.obj j) S] [Algebra.FinitePresentation (F.obj j) R]
    [Algebra.FinitePresentation (F.obj j) S] (φ : R →ₐ[F.obj j] S), φ.toRingHom.Finite →
    (letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ)) →
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (f₀ ≫ f)).hom.toAlgebra;
      Function.Bijective (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ) := by
  intro J _ _ F c hc j R S _ _ _ _ _ _ φ _ hbij
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let fR : F.obj j ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap (F.obj j) R)
  let fS : F.obj j ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap (F.obj j) S)
  have hfR : fR.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  have hfS : fS.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  let g : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom φ.toRingHom
  have hg : fR ≫ g = fS := by ext x; exact φ.commutes x
  have sqR := (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt R).flip
  have sqS := (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt S).flip
  obtain ⟨ER, ιR, uR, vR, ⟨hER⟩, hkR⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ fR _ _ sqR
  obtain ⟨ES, ιS, uS, vS, ⟨hES⟩, hkS⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ fS _ _ sqS
  let G : CommRingCat.of (c.pt ⊗[F.obj j] R) ⟶ CommRingCat.of (c.pt ⊗[F.obj j] S) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id c.pt c.pt) φ).toRingHom
  haveI : IsIso G := (ConcreteCategory.isIso_iff_bijective G).2 hbij
  have hGr : g ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := S)).toRingHom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := R)).toRingHom ≫ G := by
    ext x; simp [g, G]
  obtain ⟨m, hm⟩ := exists_stage_isIso (K := Under j) (Under.forget j ⋙ F) ER ES
    (fun k => F.map k.hom) fR fS hfR hfS g hg uR vR uS vS (fun k => (hkR k).1) (fun k => (hkS k).1)
    (Cocone.mk _ ιR) hER (Cocone.mk _ ιS) hES _ _ (fun k => (hkR k).2.1) (fun k => (hkS k).2.1) G
    (fun k => by
      have key : ∀ d : ER.obj k ⟶ ES.obj k, vR.app k ≫ d = g ≫ vS.app k →
          uR.app k ≫ d = uS.app k → d ≫ ιS.app k = ιR.app k ≫ G := by
        intro d hd1 hd2
        apply (hkR k).1.hom_ext
        · rw [reassoc_of% hd1, (hkS k).2.1, reassoc_of% (hkR k).2.1, hGr]
        · change uR.app k ≫ d ≫ ιS.app k = uR.app k ≫ ιR.app k ≫ G
          erw [reassoc_of% hd2, (hkS k).2.2, reassoc_of% (hkR k).2.2]
          ext x
          simp [G]
      exact key _ ((hkR k).1.inl_desc _ _ _) ((hkR k).1.inr_desc _ _ _))
  refine ⟨m.right, m.hom, fun k f => ?_⟩
  let l : Under j := Under.mk (m.hom ≫ f)
  obtain ⟨d, hd1, hd2, hdiso⟩ : ∃ d : ER.obj l ⟶ ES.obj l, vR.app l ≫ d = g ≫ vS.app l ∧
      uR.app l ≫ d = uS.app l ∧ IsIso d :=
    ⟨_, (hkR l).1.inl_desc _ _ _, (hkR l).1.inr_desc _ _ _, hm l (Under.homMk f rfl)⟩
  letI : Algebra (F.obj j) (F.obj k) := (F.map (m.hom ≫ f)).hom.toAlgebra
  have tR := (CommRingCat.isPushout_tensorProduct (F.obj j) (F.obj k) R).flip
  have tS := (CommRingCat.isPushout_tensorProduct (F.obj j) (F.obj k) S).flip
  let M : CommRingCat.of (F.obj k ⊗[F.obj j] R) ⟶ CommRingCat.of (F.obj k ⊗[F.obj j] S) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (F.obj k) (F.obj k)) φ).toRingHom
  have hM : M = ((hkR l).1.isoIsPushout _ _ tR).inv ≫ d ≫ ((hkS l).1.isoIsPushout _ _ tS).hom := by
    apply tR.hom_ext
    · erw [IsPushout.inl_isoIsPushout_inv_assoc _ _ (hkR l).1 tR, reassoc_of% hd1,
        IsPushout.inl_isoIsPushout_hom _ _ (hkS l).1 tS]
      ext x
      simp [M, g]
    · erw [IsPushout.inr_isoIsPushout_inv_assoc _ _ (hkR l).1 tR, reassoc_of% hd2,
        IsPushout.inr_isoIsPushout_hom _ _ (hkS l).1 tS]
      ext x
      simp [M]
  haveI : IsIso M := by rw [hM]; infer_instance
  exact (ConcreteCategory.isIso_iff_bijective M).1 this

end GlobalTheory.BijDescent
