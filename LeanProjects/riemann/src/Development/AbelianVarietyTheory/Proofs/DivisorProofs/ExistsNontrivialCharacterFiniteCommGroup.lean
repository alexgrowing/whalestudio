import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharExists

open TensorProduct WithConv in

theorem pres (K : Type) [Field K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N] (hf : IsFinite N.hom) :
  ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra K B), Coalgebra.IsCocomm K B ∧ Module.Finite K B ∧
    ∃ e : (Spec (CommRingCat.of B)).asOver (Sp K) ≅ N, IsMonHom e.hom := by
  have haff : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (G := Grp.mk N)).2 haff
  let B : Type := A.unop
  letI : HopfAlgebra K B := A.unop.hopfAlgebra
  let G : Over (Spec (CommRingCat.of K)) :=
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of K))
  letI : GrpObj G := instGrpObjSpecAsOverSpec (R := CommRingCat.of K) (A := CommRingCat.of B)
  let i : G ≅ N := (Grp.forget _).mapIso e
  haveI : IsMonHom i.hom := e.hom.hom.isMonHom_hom
  obtain ⟨j, hj, hw⟩ : ∃ j : Spec (CommRingCat.of B) ⟶ N.left, IsIso j ∧
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = j ≫ N.hom :=
    ⟨i.hom.left, inferInstanceAs (IsIso ((Over.forget _).map i.hom)), (Over.w i.hom).symm⟩
  haveI : Module.Finite K B := by
    have h1 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
      rw [hw]; infer_instance
    rw [IsFinite.SpecMap_iff] at h1
    exact RingHom.finite_algebraMap.1 h1
  haveI : Coalgebra.IsCocomm K B := GlobalTheory.FiniteFlatKilled.isCocomm_of_mul_comm fun f g => by
    let φ := (Spec.mapMulEquiv (R := K) (S := B) (T := B ⊗[K] B)).trans
      (Hom.mulEquivCongrRight i _)
    apply φ.injective
    rw [map_mul, map_mul, mul_comm]
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, i, inferInstance⟩

theorem pullTop_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (χ : Γ(Z, ⊤)ˣ) :
    pullTop (f ≫ g) χ = pullTop f (pullTop g χ) := by
  ext; simp [pullTop]; rfl

theorem transfer (S : Scheme.{0}) (N N' T : Over S) [GrpObj N] [GrpObj N'] (e : N' ≅ N) (he : IsMonHom e.hom)
  (χ : Γ((N' ⊗ T).left, ⊤)ˣ) (hχ : IsCharacter χ) (h1 : χ ≠ 1) :
  ∃ χ' : Γ((N ⊗ T).left, ⊤)ˣ, IsCharacter χ' ∧ χ' ≠ 1 := by
  have hinv : IsMonHom e.inv := inferInstance
  refine ⟨pullTop (e.inv ▷ T).left χ, ?_, ?_⟩
  · unfold IsCharacter at hχ ⊢
    have k1 : lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T) ≫ e.inv ▷ T =
        (e.inv ⊗ₘ (e.inv ▷ T)) ≫ lift (fst N' (N' ⊗ T) * (snd N' (N' ⊗ T) ≫ fst N' T)) (snd N' (N' ⊗ T) ≫ snd N' T) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [comp_mul, mul_comp]
    have k2 : lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T) ≫ e.inv ▷ T =
        (e.inv ⊗ₘ (e.inv ▷ T)) ≫ lift (fst N' (N' ⊗ T)) (snd N' (N' ⊗ T) ≫ snd N' T) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have k3 : snd N (N ⊗ T) ≫ e.inv ▷ T = (e.inv ⊗ₘ (e.inv ▷ T)) ≫ snd N' (N' ⊗ T) := by
      simp
    rw [← pullTop_comp, ← Over.comp_left, k1, Over.comp_left, pullTop_comp, hχ, map_mul,
      ← pullTop_comp, ← pullTop_comp, ← Over.comp_left, ← Over.comp_left, ← k2, ← k3, Over.comp_left,
      Over.comp_left, pullTop_comp, pullTop_comp]
  · intro h
    apply h1
    have : pullTop (e.hom ▷ T).left (pullTop (e.inv ▷ T).left χ) = χ := by
      rw [← pullTop_comp, ← Over.comp_left, ← MonoidalCategory.comp_whiskerRight, e.hom_inv_id,
        MonoidalCategory.id_whiskerRight]
      ext; simp [pullTop]
    rw [← this, h, map_one]

open TensorProduct in

noncomputable def secMap (K : Type) [CommRing K] (B D : Type) [CommRing B] [CommRing D] [Algebra K B] [Algebra K D] :
    B ⊗[K] D →+* Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left, ⊤) :=
  (pullbackSpecIso' K B D : ((Spec (CommRingCat.of B)).asOver (Sp K) ⊗
    (Spec (CommRingCat.of D)).asOver (Sp K)).left ≅ Spec (CommRingCat.of (B ⊗[K] D))).hom.appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[K] D))).inv.hom

open TensorProduct in

theorem secMap_injective (K : Type) [CommRing K] (B D : Type) [CommRing B] [CommRing D] [Algebra K B]
    [Algebra K D] : Function.Injective (secMap K B D) := by
  let e : ((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left ≅
      Spec (CommRingCat.of (B ⊗[K] D)) := pullbackSpecIso' K B D
  intro x y hxy
  have h1 : ∀ z, e.inv.appTop.hom (e.hom.appTop.hom z) = z := fun z => by
    change (e.inv ≫ e.hom).appTop.hom z = z
    rw [e.inv_hom_id]; rfl
  have h3 : ∀ z : B ⊗[K] D,
      (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[K] D))).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of (B ⊗[K] D))).inv.hom z) = z :=
    fun z => by rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  have h2 := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[K] D))).hom.hom (e.inv.appTop.hom z)) hxy
  change (Scheme.ΓSpecIso _).hom.hom (e.inv.appTop.hom (e.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom x))) =
    (Scheme.ΓSpecIso _).hom.hom (e.inv.appTop.hom (e.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom y))) at h2
  rwa [h1, h1, h3, h3] at h2

open TensorProduct in

theorem secMap_lift (K : Type) [CommRing K] (B D : Type) [CommRing B] [CommRing D] [Algebra K B] [Algebra K D]
    (Y : Over (Sp K)) (f : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K))
    (h : Y ⟶ (Spec (CommRingCat.of D)).asOver (Sp K)) (b : B) (d : D) :
    (lift f h).left.appTop.hom (secMap K B D (b ⊗ₜ d)) =
      f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
        h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d) := by
  let e : ((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left ≅
      Spec (CommRingCat.of (B ⊗[K] D)) := pullbackSpecIso' K B D
  have hfst : e.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) =
      pullback.fst ((Spec (CommRingCat.of B)).asOver (Sp K)).hom ((Spec (CommRingCat.of D)).asOver (Sp K)).hom :=
    pullbackSpecIso_hom_fst ..
  have hsnd : e.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) =
      pullback.snd ((Spec (CommRingCat.of B)).asOver (Sp K)).hom ((Spec (CommRingCat.of D)).asOver (Sp K)).hom :=
    pullbackSpecIso_hom_snd ..
  have nL := congr(($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[K] D)))).hom b)
  have nR := congr(($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight.toRingHom : D →+* B ⊗[K] D)))).hom d)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nL nR
  have hbd : (b ⊗ₜ[K] d : B ⊗[K] D) = Algebra.TensorProduct.includeLeftRingHom b *
      Algebra.TensorProduct.includeRight.toRingHom d := by simp
  have hf : (lift f h).left ≫ pullback.fst _ _ = f.left := congrArg Over.Hom.left (lift_fst f h)
  have hh : (lift f h).left ≫ pullback.snd _ _ = h.left := congrArg Over.Hom.left (lift_snd f h)
  change (lift f h).left.appTop.hom (e.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom (b ⊗ₜ d))) = _
  simp only [hbd, map_mul]
  rw [nL, nR, ← hf, ← hh, ← hfst, ← hsnd]
  rfl

open TensorProduct in

theorem prodsec (K : Type) [CommRing K] (B D : Type) [CommRing B] [CommRing D] [Algebra K B] [Algebra K D] :
    ∃ Φ : B ⊗[K] D →+* Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left, ⊤),
      Function.Injective Φ ∧
      ∀ (Y : Over (Sp K)) (f : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K))
        (h : Y ⟶ (Spec (CommRingCat.of D)).asOver (Sp K)) (b : B) (d : D),
        (lift f h).left.appTop.hom (Φ (b ⊗ₜ d)) =
          f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) *
            h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d) :=
  ⟨secMap K B D, secMap_injective K B D, secMap_lift K B D⟩

open TensorProduct in

theorem mulsharp (K : Type) [CommRing K] (B : Type) [CommRing B] [HopfAlgebra K B] (Y : Over (Sp K))
    (f g : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) (b : B) {J : Type} (s : Finset J) (x y : J → B)
    (hb : Coalgebra.comul (R := K) b = ∑ i ∈ s, x i ⊗ₜ[K] y i) :
    (f * g).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      ∑ i ∈ s, f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (x i)) *
        g.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (y i)) := by
  have hμ := mul_spec_asOver_spec_left (R := CommRingCat.of K) (A := CommRingCat.of B)
  have nC := congr(($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
    (Bialgebra.comulAlgHom K B).toRingHom))).hom b)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nC
  have h1 : (f * g).left = (lift f g).left ≫ (pullbackSpecIso K B B).hom ≫
      Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom K B).toRingHom) := by
    rw [Hom.mul_def, Over.comp_left, hμ]
    rfl
  rw [h1]
  change (lift f g).left.appTop.hom ((pullbackSpecIso K B B).hom.appTop.hom
    ((Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom K B).toRingHom)).appTop.hom _)) = _
  rw [← nC]
  change (lift f g).left.appTop.hom (secMap K B B (Bialgebra.comulAlgHom K B b)) = _
  rw [Bialgebra.comulAlgHom_apply, hb, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact secMap_lift K B B Y f g (x i) (y i)

theorem algsharp (K : Type) [CommRing K] (A : Type) [CommRing A] [Algebra K A] (Y : Over (Sp K))
    (f : Y ⟶ (Spec (CommRingCat.of A)).asOver (Sp K)) (k : K) :
    f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (algebraMap K A k)) =
      Y.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := by
  have hw : f.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) = Y.hom := Over.w f
  have hn := congr(($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap K A)))).hom k)
  rw [← hw]
  change _ = f.left.appTop.hom ((Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop.hom _)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  rw [← hn]

open TensorProduct in

theorem bridge (K : Type) [Field K] (B D : Type) [CommRing B] [HopfAlgebra K B] [CommRing D] [Algebra K D]
  (u : (B ⊗[K] D)ˣ) (hu : IsGroupLikeElem D (TensorProduct.comm K B D (u : B ⊗[K] D))) (h1 : u ≠ 1) :
  ∃ χ : Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left, ⊤)ˣ,
    IsCharacter χ ∧ χ ≠ 1 := by
  obtain ⟨Φ, hΦ, hΦY⟩ := prodsec K B D
  refine ⟨Units.map Φ.toMonoidHom u, ?_, ?_⟩
  swap
  · intro h; apply h1; ext; apply hΦ; simpa using congrArg Units.val h
  let G : Over (Sp K) := (Spec (CommRingCat.of B)).asOver (Sp K)
  let T : Over (Sp K) := (Spec (CommRingCat.of D)).asOver (Sp K)
  let Y : Over (Sp K) := G ⊗ (G ⊗ T)
  letI : Algebra K Γ(Y.left, ⊤) :=
    (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let sh : ∀ (A : Type) [CommRing A] [Algebra K A] (_ : Y ⟶ (Spec (CommRingCat.of A)).asOver (Sp K)),
      A →ₐ[K] Γ(Y.left, ⊤) := fun A _ _ f =>
    { toRingHom := f.left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      commutes' := fun k => algsharp K A Y f k }
  let α := sh B (fst G (G ⊗ T))
  let β := sh B (snd G (G ⊗ T) ≫ fst G T)
  let δ := sh D (snd G (G ⊗ T) ≫ snd G T)
  let Θ : D ⊗[K] (B ⊗[K] B) →ₐ[K] Γ(Y.left, ⊤) :=
    Algebra.TensorProduct.lift δ (Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _))
      (fun _ _ => Commute.all _ _)
  have key := congrArg Θ ((GlobalTheory.isGroupLikeElem_tensor_iff _).1 hu).2
  rw [map_mul] at key
  have hsnd : snd G (G ⊗ T) = lift (snd G (G ⊗ T) ≫ fst G T) (snd G (G ⊗ T) ≫ snd G T) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp

  have e1 : ∀ x : B ⊗[K] D,
      (lift (fst G (G ⊗ T) * (snd G (G ⊗ T) ≫ fst G T)) (snd G (G ⊗ T) ≫ snd G T)).left.appTop.hom (Φ x) =
        Θ (LinearMap.lTensor D (Coalgebra.comul (R := K) (A := B)) (TensorProduct.comm K B D x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b d =>
      rw [hΦY]
      obtain ⟨S, hS⟩ := TensorProduct.exists_finset (Coalgebra.comul (R := K) b)
      rw [mulsharp K B Y _ _ b S (fun i => i.1) (fun i => i.2) hS, TensorProduct.comm_tmul,
        LinearMap.lTensor_tmul, hS, TensorProduct.tmul_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Θ, Algebra.TensorProduct.lift_tmul]
      exact _root_.mul_comm _ _
  have e2 : ∀ x : B ⊗[K] D,
      (lift (fst G (G ⊗ T)) (snd G (G ⊗ T) ≫ snd G T)).left.appTop.hom (Φ x) =
        Θ (Algebra.TensorProduct.map (AlgHom.id K D) Algebra.TensorProduct.includeLeft (TensorProduct.comm K B D x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b d =>
      rw [hΦY, TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul]
      simp only [Θ, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      exact _root_.mul_comm _ _
  have e3 : ∀ x : B ⊗[K] D,
      (snd G (G ⊗ T)).left.appTop.hom (Φ x) =
        Θ (Algebra.TensorProduct.map (AlgHom.id K D) Algebra.TensorProduct.includeRight (TensorProduct.comm K B D x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b d =>
      conv_lhs => rw [hsnd]
      rw [hΦY, TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul]
      simp only [Θ, AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
      exact _root_.mul_comm _ _
  unfold IsCharacter
  ext
  simp only [pullTop, Units.coe_map, Units.val_mul]
  exact (e1 u).trans (key.trans (congrArg₂ (· * ·) (e2 u).symm (e3 u).symm))
open TensorProduct WithConv GlobalTheory GlobalTheory.CartierDual in

theorem exists_character_ne_one : ∀ (K : Type) [Field K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → (𝟙 N ≠ (1 : N ⟶ N)) → ∃ (T : Over (Sp K)) (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsCharacter χ ∧ χ ≠ 1 := by
  intro K _ N _ _ hf hne
  obtain ⟨B, _, _, hcc, hfin, e, he⟩ := pres K N hf
  let G : Over (Sp K) := (Spec (CommRingCat.of B)).asOver (Sp K)
  have hG : 𝟙 G ≠ 1 := by
    intro h; apply hne
    rw [← cancel_epi e.hom, MonObj.comp_one, Category.comp_id, ← Category.id_comp e.hom, h, MonObj.one_comp]
  have hid : toConv (AlgHom.id K B) ≠ 1 := by
    intro h; apply hG
    have h2 : Spec.mapMulEquiv (R := K) (S := B) (T := B) (toConv (AlgHom.id K B)) = 𝟙 G := by
      ext1
      exact Spec.map_id _
    rw [← h2, h, map_one]
  let D := GlobalTheory.CartierDual K B
  have hcan : canonical K B ≠ 1 := by
    intro h
    apply hid
    have h1 := pairingMap_canonical (R := K) (H := B)
    rw [h, Algebra.TensorProduct.one_def] at h1
    apply ofConv_injective
    ext a
    refine eq_of_forall_apply (R := K) fun φ => ?_
    have h2 := congr(($h1 φ) a)
    rw [pairingMap_tmul, LinearMap.id_apply] at h2
    simp only [ofConv_toConv, AlgHom.id_apply]
    rw [← h2]
    simp [one_apply, Algebra.algebraMap_eq_smul_one, mul_comm, AlgHom.convOne_apply]
  have hgl := (isPerfectBicharacter_canonical K B).left
  have hu : IsUnit (canonical K B) := by
    have := hgl.isUnit
    exact (isUnit_map_iff (Algebra.TensorProduct.comm K B D) _).1 this
  obtain ⟨χ, hχ, hχ1⟩ := bridge K B D hu.unit hgl (fun h => hcan (by simpa using congrArg Units.val h))
  obtain ⟨χ', hχ', hχ'1⟩ := transfer (Sp K) N G _ e he χ hχ hχ1
  exact ⟨_, χ', hχ', hχ'1⟩

end GlobalTheory.CharExists
