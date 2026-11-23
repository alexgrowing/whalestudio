import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HilbAff.IdealDet
variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem comm_fst {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (a : A) :
    ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a)) =
    ((pullback.snd (str A B) g).app U).hom (secAlg A g U a) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B a) =
      (str A B).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) :=
    congrArg (fun f => f.hom a) h1
  have key : (str A B).appTop ≫ (pullback.fst (str A B) g).appLE ⊤
      ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) =
      g.appLE ⊤ U (by simp) ≫ (pullback.snd (str A B) g).app U := by
    calc _ = (pullback.fst (str A B) g ≫ str A B).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          (Scheme.Hom.comp_appLE _ _ _ _ _).symm
      _ = (pullback.snd (str A B) g ≫ g).appLE ⊤
          ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) :=
          appLE_eq_of_eq (by simp [pullback.condition]) _ _ _ _
      _ = _ := by
          rw [Scheme.Hom.app_eq_appLE]; exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h2, secAlg, RingHom.comp_apply, ← CommRingCat.comp_apply, key, CommRingCat.comp_apply]

def theta {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra
    Γ(T, U) ⊗[A] B →+* Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  (Algebra.TensorProduct.lift
    { toRingHom := ((pullback.snd (str A B) g).app U).hom, commutes' := fun (_ : A) => rfl }
    { toRingHom := (((pullback.fst (str A B) g).appLE ⊤ _ (by simp)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom),
      commutes' := fun a => comm_fst A B g U a }
    (fun _ _ => Commute.all _ _)).toRingHom

theorem theta_tmul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens) (c : Γ(T, U)) (b : B) :
    letI := (secAlg A g U).toAlgebra
    theta A B g U (c ⊗ₜ[A] b) = ((pullback.snd (str A B) g).app U).hom c *
      ((pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) := by
  letI := (secAlg A g U).toAlgebra
  letI : Algebra A Γ(pullback (str A B) g, (pullback.snd (str A B) g) ⁻¹ᵁ U) :=
    (((pullback.snd (str A B) g).app U).hom.comp (secAlg A g U)).toAlgebra
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem kappa_apply {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (U : T.Opens) :
    letI := (secAlg A g U).toAlgebra
    ∀ x : Γ(T, U) ⊗[A] B, kappa A B g I U x =
      (I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U)).hom (theta A B g U x) := by
  letI := (secAlg A g U).toAlgebra
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; rfl
  | tmul c b =>
    rw [kappa_tmul, theta_tmul, map_mul]
    have e : (pullback.fst (str A B) g).appLE ⊤ ((pullback.snd (str A B) g) ⁻¹ᵁ U) (by simp) ≫
        I.subschemeι.app ((pullback.snd (str A B) g) ⁻¹ᵁ U) =
        (I.subschemeι ≫ pullback.fst (str A B) g).appLE ⊤ ((I.subschemeι ≫ pullback.snd (str A B) g) ⁻¹ᵁ U)
          (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    congr 1
    rw [← e]; rfl

theorem theta_surjective {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.Opens)
    (hU : IsAffineOpen U) : Function.Surjective (theta A B g U) := by
  letI := (secAlg A g U).toAlgebra
  have hP := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback (str A B) g)
    inferInstance (isAffineOpen_top _) hU le_top (by simp)
  let R : CommRingCat.{0} := CommRingCat.of (Γ(T, U) ⊗[A] B)
  let k : Γ(T, U) ⟶ R := CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (S := A)).toRingHom
  let h : Γ(Spec (CommRingCat.of B), (str A B) ⁻¹ᵁ ⊤) ⟶ R :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := Γ(T, U))).toRingHom
  have w : (str A B).app ⊤ ≫ h = g.appLE ⊤ U le_top ≫ k := by
    ext x
    obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (CommRingCat.of A)).inv a = x :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom x, by simp⟩
    have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))
    have h2 : (str A B).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap A B a) :=
      (congrArg (fun f => f.hom a) h1).symm
    change (Algebra.TensorProduct.includeRight (R := A) (A := Γ(T, U)))
      ((Scheme.ΓSpecIso (CommRingCat.of B)).hom ((str A B).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      (Algebra.TensorProduct.includeLeft (S := A)) (secAlg A g U a)
    rw [h2, Iso.inv_hom_id_apply]
    exact ((Algebra.TensorProduct.includeRight).commutes a).trans
      ((Algebra.TensorProduct.includeLeft (S := A)).commutes a).symm
  let ψ := hP.desc h k w
  have hθ : ψ ≫ CommRingCat.ofHom (theta A B g U) = 𝟙 _ := by
    apply hP.hom_ext
    · rw [hP.inl_desc_assoc, Category.comp_id]
      ext z
      change theta A B g U ((1 : Γ(T, U)) ⊗ₜ[A] ((Scheme.ΓSpecIso (CommRingCat.of B)).hom z)) = _
      have e : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of B)).hom z) = z :=
        Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of B)) z
      rw [theta_tmul, map_one, one_mul, e]
      rfl
    · rw [hP.inr_desc_assoc, Category.comp_id]
      ext c
      change theta A B g U (c ⊗ₜ[A] (1 : B)) = _
      rw [theta_tmul, map_one, map_one, mul_one]
  intro y
  exact ⟨ψ y, congrArg (fun F => F.hom y) hθ⟩

theorem eq_of_ker_kappa_eq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I₁ I₂ : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData),
    (∀ U : T.affineOpens, RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₁ U) =
      RingHom.ker (GlobalTheory.HilbAff.kappa A B g I₂ U)) → I₁ = I₂ := by
  intro A B _ _ _ T g I₁ I₂ h
  haveI : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback (str A B) g)
      (inferInstance : IsAffineHom (str A B))
  let W : T.affineOpens → (pullback (str A B) g).affineOpens :=
    fun U => ⟨pullback.snd (str A B) g ⁻¹ᵁ U, U.2.preimage _⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W ?_ ?_
  · exact (pullback.snd (str A B) g).iSup_preimage_eq_top (iSup_affineOpens_eq_top T)
  · intro U
    letI := (secAlg A g U).toAlgebra
    have key : ∀ I : (pullback (str A B) g).IdealSheafData,
        I.ideal (W U) = Ideal.map (theta A B g U) (RingHom.ker (kappa A B g I U)) := by
      intro I
      have e : RingHom.ker (kappa A B g I U) = Ideal.comap (theta A B g U) (I.ideal (W U)) := by
        ext x
        rw [RingHom.mem_ker, Ideal.mem_comap, ← I.ker_subschemeι_app (W U), RingHom.mem_ker,
          kappa_apply]
        rfl
      rw [e, Ideal.map_comap_of_surjective _ (theta_surjective A B g U U.2)]
    rw [key, key, h U]

end GlobalTheory.HilbAff.IdealDet
