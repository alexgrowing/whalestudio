import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open FunctorialResolution.Blowup FunctorialResolution.EmbeddedResolution

theorem UpperTheory.surjective_eval_coordBlowupSubst_pushout_of_flat :
    ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {D : ℕ}
        (φ : MvPolynomial (Fin D) A →+* B) (_ : φ.Flat) (j : Fin D) (β : B →+* C) (ρ : MvPolynomial (Fin D) A →+* C)
        (_ : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (coordBlowupSubst A Finset.univ j).toRingHom)
          (CommRingCat.ofHom β) (CommRingCat.ofHom ρ)),
        Function.Surjective (MvPolynomial.eval₂Hom β (fun k : Fin D => if k = j then (1 : C) else ρ (MvPolynomial.X k))) ∧
        RingHom.ker (MvPolynomial.eval₂Hom β (fun k : Fin D => if k = j then (1 : C) else ρ (MvPolynomial.X k))) =
          Ideal.span (insert (MvPolynomial.X j - 1) (Set.range fun k => MvPolynomial.C (φ (MvPolynomial.X k)) -
            MvPolynomial.C (φ (MvPolynomial.X j)) * MvPolynomial.X k)) ∧
        β (φ (MvPolynomial.X j)) ∈ nonZeroDivisors C := by
  intro A B C _ _ _ D φ hφ j β ρ h
  classical
  have hw : ∀ p, β (φ p) = ρ (coordBlowupSubst A Finset.univ j p) := fun p => by
    have := congrArg (fun f => f.hom p) h.w
    simpa using this
  have hσC : ∀ a, coordBlowupSubst A Finset.univ j (MvPolynomial.C a) = MvPolynomial.C a := fun a => by
    simp [coordBlowupSubst]
  have hσX : ∀ k, coordBlowupSubst A Finset.univ j (MvPolynomial.X k) =
      if k ≠ j then MvPolynomial.X k * MvPolynomial.X j else MvPolynomial.X k := fun k => by
    simp [coordBlowupSubst]
  let g : Fin D → C := fun k => if k = j then 1 else ρ (MvPolynomial.X k)
  let e : MvPolynomial (Fin D) B →+* C := MvPolynomial.eval₂Hom β g
  let I : Ideal (MvPolynomial (Fin D) B) := Ideal.span (insert (MvPolynomial.X j - 1)
    (Set.range fun k => MvPolynomial.C (φ (MvPolynomial.X k)) -
      MvPolynomial.C (φ (MvPolynomial.X j)) * MvPolynomial.X k))
  have hIle : ∀ x ∈ I, e x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y (rfl | ⟨k, rfl⟩)
      · simp [e, g]
      · simp only [e, map_sub, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
        rw [hw, hw, hσX, hσX]
        by_cases hk : k = j
        · subst hk; simp [g]
        · simp [g, hk, map_mul]; ring
    · simp
    · intro a b _ _ ha hb; simp [ha, hb]
    · intro a b _ hb; simp [hb]
  let Q := MvPolynomial (Fin D) B ⧸ I
  let mk : MvPolynomial (Fin D) B →+* Q := Ideal.Quotient.mk I
  let γ : MvPolynomial (Fin D) A →+* Q := MvPolynomial.eval₂Hom
    (((mk.comp MvPolynomial.C).comp φ).comp MvPolynomial.C)
    (fun k => mk (if k = j then MvPolynomial.C (φ (MvPolynomial.X j)) else MvPolynomial.X k))
  have hmkXj : mk (MvPolynomial.X j) = 1 := by
    rw [← sub_eq_zero, ← map_one mk, ← map_sub]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span (Set.mem_insert _ _))
  have hmkgen : ∀ k, mk (MvPolynomial.C (φ (MvPolynomial.X k))) =
      mk (MvPolynomial.C (φ (MvPolynomial.X j))) * mk (MvPolynomial.X k) := by
    intro k
    rw [← map_mul, ← sub_eq_zero, ← map_sub]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩))
  have hγ : ∀ p, mk (MvPolynomial.C (φ p)) = γ (coordBlowupSubst A Finset.univ j p) := by
    have key : (mk.comp MvPolynomial.C).comp φ = γ.comp (coordBlowupSubst A Finset.univ j).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [γ, hσC]
      · intro k
        by_cases hk : k = j
        · subst hk; simp [γ, hσX]
        · simp [γ, hσX, hk, hmkgen k]; ring
    intro p; exact RingHom.congr_fun key p
  have hwq : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (mk.comp MvPolynomial.C) =
      CommRingCat.ofHom (coordBlowupSubst A Finset.univ j).toRingHom ≫ CommRingCat.ofHom γ := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro p; simpa using hγ p
  let ψ : CommRingCat.of C ⟶ CommRingCat.of Q := h.desc _ _ hwq
  have hψβ : ∀ b, ψ.hom (β b) = mk (MvPolynomial.C b) := fun b => by
    have := congrArg (fun f => f.hom b) (h.inl_desc _ _ hwq)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hψρ : ∀ p, ψ.hom (ρ p) = γ p := fun p => by
    have := congrArg (fun f => f.hom p) (h.inr_desc _ _ hwq)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hcomp : ∀ x, ψ.hom (e x) = mk x := by
    have key : ψ.hom.comp e = mk := by
      apply MvPolynomial.ringHom_ext
      · intro b; simp [e, hψβ]
      · intro k
        by_cases hk : k = j
        · subst hk; simp [e, g, hmkXj]
        · simp [e, g, hk, hψρ, γ]
    intro x; exact RingHom.congr_fun key x
  let eb : Q →+* C := Ideal.Quotient.lift I e hIle
  have hebmk : ∀ x, eb (mk x) = e x := fun x => Ideal.Quotient.lift_mk _ _ _
  have hebγ : eb.comp γ = ρ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [γ, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [hebmk]; simp only [e, MvPolynomial.eval₂Hom_C]; rw [hw, hσC]
    · intro k
      simp only [γ, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hebmk]
      by_cases hk : k = j
      · subst hk; simp only [if_true, e, MvPolynomial.eval₂Hom_C]; rw [hw, hσX]; simp
      · simp [hk, e, g]
  have hid : ψ ≫ CommRingCat.ofHom eb = 𝟙 _ := by
    apply h.hom_ext
    · apply CommRingCat.hom_ext; apply RingHom.ext; intro b
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply]
      rw [hψβ, hebmk]; simp [e]
    · apply CommRingCat.hom_ext; apply RingHom.ext; intro p
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply]
      rw [hψρ]; exact RingHom.congr_fun hebγ p
  have hsurj : Function.Surjective e := by
    intro c
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (ψ.hom c)
    refine ⟨x, ?_⟩
    have := congrArg (fun f => f.hom c) hid
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply] at this
    rw [← this, ← hx]
    exact (hebmk x).symm
  have hker : RingHom.ker e = I := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      have := hcomp x
      rw [hx, map_zero] at this
      exact (Ideal.Quotient.eq_zero_iff_mem).1 this.symm
    · intro x hx; exact (RingHom.mem_ker).2 (hIle x hx)
  refine ⟨hsurj, hker, ?_⟩
  let P' := MvPolynomial (ULift.{0} (Fin D)) A
  let up : MvPolynomial (Fin D) A →ₐ[A] P' := MvPolynomial.rename ULift.up
  let dn : P' →ₐ[A] MvPolynomial (Fin D) A := MvPolynomial.rename ULift.down
  have hdnup : ∀ p, dn (up p) = p := by
    intro p
    show MvPolynomial.rename ULift.down (MvPolynomial.rename ULift.up p) = p
    rw [MvPolynomial.rename_rename]
    exact congrArg (fun f => f p) (MvPolynomial.rename_id (R := A) (σ := Fin D))
  let σ' : MvPolynomial (Fin D) A →+* P' := up.toRingHom.comp (coordBlowupSubst A Finset.univ j).toRingHom
  letI iB : Algebra (MvPolynomial (Fin D) A) B := φ.toAlgebra
  letI iP : Algebra (MvPolynomial (Fin D) A) P' := σ'.toAlgebra
  haveI : Module.Flat (MvPolynomial (Fin D) A) B := hφ
  letI iC : Algebra (MvPolynomial (Fin D) A) C := (β.comp φ).toAlgebra
  let uL : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[MvPolynomial (Fin D) A] P') :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let uR : CommRingCat.of (MvPolynomial (Fin D) A) ⟶ CommRingCat.of (B ⊗[MvPolynomial (Fin D) A] P') :=
    CommRingCat.ofHom ((Algebra.TensorProduct.includeRight (R := MvPolynomial (Fin D) A) (A := B)
      (B := P')).toRingHom.comp up.toRingHom)
  have hwT : CommRingCat.ofHom φ ≫ uL = CommRingCat.ofHom (coordBlowupSubst A Finset.univ j).toRingHom ≫ uR := by
    apply CommRingCat.hom_ext; apply RingHom.ext; intro p
    change algebraMap _ B p ⊗ₜ[MvPolynomial (Fin D) A] (1 : P') = (1 : B) ⊗ₜ algebraMap _ P' p
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let u := h.desc uL uR hwT
  have huL : CommRingCat.ofHom β ≫ u = uL := h.inl_desc uL uR hwT
  have huR : CommRingCat.ofHom ρ ≫ u = uR := h.inr_desc uL uR hwT
  let fB : B →ₐ[MvPolynomial (Fin D) A] C := { β with commutes' := fun r => rfl }
  have hfP : ∀ r, (ρ.comp dn.toRingHom) (algebraMap (MvPolynomial (Fin D) A) P' r) =
      algebraMap (MvPolynomial (Fin D) A) C r := by
    intro r
    change ρ (dn (up (coordBlowupSubst A Finset.univ j r))) = β (φ r)
    rw [hdnup, hw]
  let fP : P' →ₐ[MvPolynomial (Fin D) A] C := { toRingHom := ρ.comp dn.toRingHom, commutes' := hfP }
  let v : B ⊗[MvPolynomial (Fin D) A] P' →ₐ[MvPolynomial (Fin D) A] C :=
    Algebra.TensorProduct.productMap fB fP
  have hvu : ∀ x, v (u.hom x) = x := by
    have hcat : u ≫ CommRingCat.ofHom v.toRingHom = 𝟙 _ := by
      apply h.hom_ext
      · apply CommRingCat.hom_ext; apply RingHom.ext; intro b
        have := congrArg (fun f => f.hom b) huL
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_id,
          RingHom.id_apply, Category.comp_id]
        rw [this]
        change fB b * fP 1 = β b
        rw [map_one, mul_one]; rfl
      · apply CommRingCat.hom_ext; apply RingHom.ext; intro p
        have := congrArg (fun f => f.hom p) huR
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_id,
          RingHom.id_apply, Category.comp_id]
        rw [this]
        change fB 1 * fP (up p) = ρ p
        rw [map_one, one_mul]
        change ρ (dn (up p)) = ρ p
        rw [hdnup]
    intro x
    have := congrArg (fun f => f.hom x) hcat
    simpa using this
  have hXj : u.hom (β (φ (MvPolynomial.X j))) = (1 : B) ⊗ₜ (MvPolynomial.X (ULift.up j) : P') := by
    have h1 := congrArg (fun f => f.hom (φ (MvPolynomial.X j))) huL
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [h1]
    have h2 := congrArg (fun f => f.hom (MvPolynomial.X j)) hwT
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    rw [h2]
    change uR.hom (coordBlowupSubst A Finset.univ j (MvPolynomial.X j)) = _
    rw [hσX, if_neg (not_not.2 rfl)]
    change (1 : B) ⊗ₜ[MvPolynomial (Fin D) A] (MvPolynomial.rename ULift.up (MvPolynomial.X j) : P') = _
    rw [MvPolynomial.rename_X]
  have hl : ∀ t : B ⊗[MvPolynomial (Fin D) A] P',
      (LinearMap.mulLeft (MvPolynomial (Fin D) A) (MvPolynomial.X (ULift.up j) : P')).lTensor B t =
        t * ((1 : B) ⊗ₜ (MvPolynomial.X (ULift.up j) : P')) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b p => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    | add a b ha hb => rw [map_add, ha, hb, add_mul]
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := B)
    (LinearMap.mulLeft (MvPolynomial (Fin D) A) (MvPolynomial.X (ULift.up j) : P'))
    (fun a b hab => (MvPolynomial.isRegular_X).left hab)
  have key : ∀ x : C, x * β (φ (MvPolynomial.X j)) = 0 → x = 0 := by
    intro x hx
    have hux : u.hom x = 0 := by
      apply hinj
      rw [hl, map_zero, ← hXj, ← map_mul, hx, map_zero]
    rw [← hvu x, hux, map_zero]
  exact (mem_nonZeroDivisors_iff).2 ⟨fun x hx => key x (by rw [mul_comm]; exact hx), key⟩
