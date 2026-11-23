import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialCharacterFiniteCommGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedGroupLikeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfUnitMulComulEqTmulSelfStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.CharKer
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.SymCob
open TensorProduct

def pt (K : Type) [CommRing K] {B A : Type} [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (φ : B →ₐ[K] A) :
    (Spec (CommRingCat.of A)).asOver (Sp K) ⟶ (Spec (CommRingCat.of B)).asOver (Sp K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact φ.comp_algebraMap)

theorem pt_sharp (K : Type) [CommRing K] {B A : Type} [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (φ : B →ₐ[K] A) (b : B) :
    (pt K φ).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (φ b) := by
  have hn := congr(($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))).hom b)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  exact hn.symm

theorem specInv_injective (R : CommRingCat) : Function.Injective (Scheme.ΓSpecIso R).inv.hom := by
  intro x y h
  have := congrArg (Scheme.ΓSpecIso R).hom.hom h
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

theorem secMap_surj (K : Type) [CommRing K] (B D : Type) [CommRing B] [CommRing D] [Algebra K B] [Algebra K D] :
    ∃ Ψ : Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left, ⊤) →+*
      B ⊗[K] D, ∀ x, GlobalTheory.CharExists.secMap K B D (Ψ x) = x := by
  let e : ((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left ≅
      Spec (CommRingCat.of (B ⊗[K] D)) := pullbackSpecIso' K B D
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (B ⊗[K] D))).hom.hom.comp e.inv.appTop.hom, fun x => ?_⟩
  change e.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom ((Scheme.ΓSpecIso _).hom.hom (e.inv.appTop.hom x))) = x
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply]
  change (e.hom ≫ e.inv).appTop.hom x = x
  rw [e.hom_inv_id]; rfl

theorem key (K : Type) [CommRing K] (B A : Type) [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (Y : Over (Sp K)) (f h : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) (φ ψ : B →ₐ[K] A)
    (j : A →+* Γ(Y.left, ⊤))
    (hf : ∀ b, f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (φ b))
    (hh : ∀ b, h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (ψ b))
    (z : B ⊗[K] B) :
    (lift f h).left.appTop.hom (GlobalTheory.CharExists.secMap K B B z) =
      j (Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b d => rw [GlobalTheory.CharExists.secMap_lift, hf, hh, Algebra.TensorProduct.lift_tmul, map_mul]

theorem mulpt (K : Type) [CommRing K] (B A : Type) [CommRing B] [HopfAlgebra K B] [CommRing A] [Algebra K A]
    (Y : Over (Sp K)) (f h : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) (φ ψ : B →ₐ[K] A)
    (j : A →+* Γ(Y.left, ⊤))
    (hf : ∀ b, f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (φ b))
    (hh : ∀ b, h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (ψ b)) (b : B) :
    (f * h).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      j (((Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom K B)) b) := by
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := K) (Coalgebra.comul (R := K) b)
  rw [GlobalTheory.CharExists.mulsharp K B Y f h b S (fun i => i.1) (fun i => i.2) hS, hS, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.lift_tmul, map_mul, hf, hh]

theorem tensor_assoc_comul_placement_eq (K B : Type) [CommRing K] [CommRing B] [Bialgebra K B] :
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : B ⊗[K] B →ₐ[K] (B ⊗[K] B) ⊗[K] B).comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B))
      (((Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.includeRight : B ⊗[K] B →ₐ[K] B ⊗[K] (B ⊗[K] B))).comp
        (Bialgebra.comulAlgHom K B)) (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B)) := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Bialgebra.comulAlgHom_apply, AlgHom.coe_coe]
  have hab : a ⊗ₜ[K] Coalgebra.comul (R := K) b =
      (a ⊗ₜ[K] (1 : B ⊗[K] B)) * ((1 : B) ⊗ₜ[K] Coalgebra.comul (R := K) b) := by simp
  rw [hab, map_mul]
  simp [Algebra.TensorProduct.one_def]

theorem over_comp_appTop {S : Scheme.{0}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) (v : Γ(Z.left, ⊤)) :
    (f ≫ g).left.appTop.hom v = f.left.appTop.hom (g.left.appTop.hom v) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]; rfl

set_option maxHeartbeats 1600000 in

theorem exists_coboundary : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → ∀ c : Γ((N ⊗ N).left, ⊤)ˣ, (∀ (T : Over (Sp K)) (x y z : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c = GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c) → (∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c = GlobalTheory.CharKer.pullTop (lift y x).left c) → ∃ u : Γ(N.left, ⊤)ˣ, ∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (x * y).left u = GlobalTheory.CharKer.pullTop x.left u * GlobalTheory.CharKer.pullTop y.left u := by
  intro K _ _ N _ _ hf c hcoc hsym
  obtain ⟨B, _, _, hcc, hfin, e, he⟩ := GlobalTheory.CharExists.pres K N hf
  obtain ⟨Ψ, hΨ⟩ := secMap_surj K B B
  obtain ⟨cG, hcG⟩ : ∃ cG : Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of B)).asOver (Sp K)).left, ⊤)ˣ,
      cG = pullTop (e.hom ⊗ₘ e.hom).left c := ⟨_, rfl⟩
  have hcB : GlobalTheory.CharExists.secMap K B B (Ψ cG) = cG := hΨ _
  have hcBu : IsUnit (Ψ cG) := cG.isUnit.map Ψ
  have hpull : ∀ (T : Over (Sp K)) (x y : T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)),
      pullTop (lift (x ≫ e.hom) (y ≫ e.hom)).left c = pullTop (lift x y).left cG := by
    intro T x y
    have : lift (x ≫ e.hom) (y ≫ e.hom) = lift x y ≫ (e.hom ⊗ₘ e.hom) := by
      rw [lift_map]
    rw [this, Over.comp_left, GlobalTheory.CharExists.pullTop_comp, hcG]
  have hmul : ∀ (T : Over (Sp K)) (x y : T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)),
      (x ≫ e.hom) * (y ≫ e.hom) = (x * y) ≫ e.hom := by
    intro T x y
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

  let iL : B →ₐ[K] B ⊗[K] B := Algebra.TensorProduct.includeLeft
  let iR : B →ₐ[K] B ⊗[K] B := Algebra.TensorProduct.includeRight
  have hsymB : Algebra.TensorProduct.comm K B B (Ψ cG) = Ψ cG := by
    have h := congrArg Units.val (hsym _ (pt K iL ≫ e.hom) (pt K iR ≫ e.hom))
    rw [hpull, hpull] at h
    simp only [pullTop, Units.coe_map, MonoidHom.coe_coe] at h
    rw [← hcB, key K B _ _ _ _ iL iR _ (pt_sharp K iL) (pt_sharp K iR),
      key K B _ _ _ _ iR iL _ (pt_sharp K iR) (pt_sharp K iL)] at h
    have h' := specInv_injective _ h
    have e1 : Algebra.TensorProduct.lift iL iR (fun _ _ => Commute.all _ _) = AlgHom.id K (B ⊗[K] B) :=
      Algebra.TensorProduct.ext' fun a b => by simp [iL, iR]
    have e2 : Algebra.TensorProduct.lift iR iL (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.comm K B B).toAlgHom :=
      Algebra.TensorProduct.ext' fun a b => by simp [iL, iR]
    rw [e1, e2] at h'
    exact h'.symm

  let ι₁ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeLeft.comp iL
  let ι₂ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeLeft.comp iR
  let ι₃ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeRight
  have hcocB : Ψ cG ⊗ₜ[K] (1 : B) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K B) (AlgHom.id K B) (Ψ cG) =
      (Algebra.TensorProduct.assoc K K K B B B).symm ((1 : B) ⊗ₜ[K] Ψ cG *
        Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B) (Ψ cG)) := by
    have h := congrArg Units.val (hcoc _ (pt K ι₁ ≫ e.hom) (pt K ι₂ ≫ e.hom) (pt K ι₃ ≫ e.hom))
    simp only [hmul, hpull] at h
    simp only [Units.val_mul, pullTop, Units.coe_map, MonoidHom.coe_coe] at h
    have k₁ := key K B _ _ (pt K ι₁) (pt K ι₂) ι₁ ι₂ _ (pt_sharp K ι₁) (pt_sharp K ι₂) (Ψ cG)
    have k₂ := key K B _ _ (pt K ι₁ * pt K ι₂) (pt K ι₃) _ ι₃ _
      (mulpt K B _ _ (pt K ι₁) (pt K ι₂) ι₁ ι₂ _ (pt_sharp K ι₁) (pt_sharp K ι₂)) (pt_sharp K ι₃) (Ψ cG)
    have k₃ := key K B _ _ (pt K ι₂) (pt K ι₃) ι₂ ι₃ _ (pt_sharp K ι₂) (pt_sharp K ι₃) (Ψ cG)
    have k₄ := key K B _ _ (pt K ι₁) (pt K ι₂ * pt K ι₃) ι₁ _ _ (pt_sharp K ι₁)
      (mulpt K B _ _ (pt K ι₂) (pt K ι₃) ι₂ ι₃ _ (pt_sharp K ι₂) (pt_sharp K ι₃)) (Ψ cG)
    rw [hcB] at k₁ k₂ k₃ k₄
    simp only [k₁, k₂, k₃, k₄] at h
    have h' := specInv_injective _ (((map_mul _ _ _).trans h).trans (map_mul _ _ _).symm)
    have E1 : Algebra.TensorProduct.lift ι₁ ι₂ (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.includeLeft : B ⊗[K] B →ₐ[K] (B ⊗[K] B) ⊗[K] B) :=
      Algebra.TensorProduct.ext' fun a b => by simp [ι₁, ι₂, iL, iR]
    have E3 : Algebra.TensorProduct.lift ι₂ ι₃ (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.includeRight : B ⊗[K] B →ₐ[K] B ⊗[K] (B ⊗[K] B)) :=
      Algebra.TensorProduct.ext' fun a b => by simp [ι₂, ι₃, iL, iR]
    have E2 : Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift ι₁ ι₂ (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) ι₃ (fun _ _ => Commute.all _ _) =
        Algebra.TensorProduct.map (Bialgebra.comulAlgHom K B) (AlgHom.id K B) := by
      rw [E1]
      exact Algebra.TensorProduct.ext' fun a b => by simp [ι₃]
    have E4 : Algebra.TensorProduct.lift ι₁ ((Algebra.TensorProduct.lift ι₂ ι₃ (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B)) := by
      rw [E3]
      exact tensor_assoc_comul_placement_eq K B
    rw [E2, E4, E1, E3] at h'
    simpa [map_mul] using h'
  obtain ⟨u₀, hu₀, hcu⟩ := (GlobalTheory.T.exists_twisted_groupLike') K B (Ψ cG) hcBu hcocB hsymB
  have hu := (GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul) K B (Ψ cG) hcBu u₀ hu₀ hcu
  obtain ⟨w, hw⟩ : ∃ w : Γ(((Spec (CommRingCat.of B)).asOver (Sp K)).left, ⊤)ˣ,
      w = Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom hu.unit := ⟨_, rfl⟩
  have hcu' : Ψ cG * Coalgebra.comul (R := K) (hu.unit : B) = (hu.unit : B) ⊗ₜ[K] (hu.unit : B) := by
    rw [IsUnit.unit_spec]; exact hcu
  refine ⟨pullTop e.inv.left w, fun T x y => ?_⟩
  have hc : pullTop (lift x y).left c = pullTop (lift (x ≫ e.inv) (y ≫ e.inv)).left cG := by
    have h := hpull T (x ≫ e.inv) (y ≫ e.inv)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at h
    exact h
  have hxy : (x * y) ≫ e.inv = (x ≫ e.inv) * (y ≫ e.inv) := by
    have h := hmul T (x ≫ e.inv) (y ≫ e.inv)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at h
    simp only [h, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hval : ∀ z : T ⟶ N, ((pullTop z.left (pullTop e.inv.left w) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) =
      (z ≫ e.inv).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (hu.unit : B)) := by
    intro z
    rw [hw]
    exact (over_comp_appTop z e.inv _).symm
  letI : Algebra K Γ(T.left, ⊤) :=
    (T.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let sh : (T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) → (B →ₐ[K] Γ(T.left, ⊤)) := fun f =>
    { toRingHom := f.left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
      commutes' := fun k => GlobalTheory.CharExists.algsharp K B T f k }
  have kc := key K B _ T (x ≫ e.inv) (y ≫ e.inv) (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (RingHom.id _)
    (fun _ => rfl) (fun _ => rfl) (Ψ cG)
  have km := mulpt K B _ T (x ≫ e.inv) (y ≫ e.inv) (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (RingHom.id _)
    (fun _ => rfl) (fun _ => rfl) (hu.unit : B)
  rw [hcB] at kc
  have fin : (Algebra.TensorProduct.lift (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (fun _ _ => Commute.all _ _)) (Ψ cG) *
      ((Algebra.TensorProduct.lift (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) (hu.unit : B) = sh (x ≫ e.inv) (hu.unit : B) * sh (y ≫ e.inv) (hu.unit : B) := by
    rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, ← map_mul, hcu', Algebra.TensorProduct.lift_tmul]
  simp only [hc]
  ext
  simp only [Units.val_mul, hval]
  simp only [hxy]
  simp only [pullTop, Units.coe_map, MonoidHom.coe_coe]
  simp only [kc, km, RingHom.id_apply]
  exact fin
end GlobalTheory.SymCob
