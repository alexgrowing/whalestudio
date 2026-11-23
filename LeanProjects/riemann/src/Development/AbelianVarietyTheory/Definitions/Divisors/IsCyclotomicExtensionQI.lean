import Mathlib

noncomputable section

open NumberField Matrix IsDedekindDomain
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.LKTrip

section Sim

variable {S A : Type*} [CommRing S] [CommRing A] {n : ℕ}

def simGroup (j : A →+* S) (σ : S →+* S) (H : Matrix (Fin n) (Fin n) S) :
    Subgroup (GL (Fin n) S × Aˣ) where
  carrier := {x | (x.1 : Matrix (Fin n) (Fin n) S)ᵀ * H * (x.1 : Matrix (Fin n) (Fin n) S).map σ =
    j (x.2 : A) • H}
  mul_mem' := by
    rintro ⟨g, c⟩ ⟨h, d⟩ hg hh
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, Units.val_mul, map_mul] at *
    rw [Matrix.transpose_mul, Matrix.map_mul]
    calc (h : Matrix (Fin n) (Fin n) S)ᵀ * (g : Matrix (Fin n) (Fin n) S)ᵀ * H *
          ((g : Matrix (Fin n) (Fin n) S).map σ * (h : Matrix (Fin n) (Fin n) S).map σ)
        = (h : Matrix (Fin n) (Fin n) S)ᵀ * ((g : Matrix (Fin n) (Fin n) S)ᵀ * H *
          (g : Matrix (Fin n) (Fin n) S).map σ) * (h : Matrix (Fin n) (Fin n) S).map σ := by
          simp only [Matrix.mul_assoc]
      _ = j c • ((h : Matrix (Fin n) (Fin n) S)ᵀ * H * (h : Matrix (Fin n) (Fin n) S).map σ) := by
          rw [hg, Matrix.mul_smul, Matrix.smul_mul]
      _ = (j c * j d) • H := by rw [hh, smul_smul]
  one_mem' := by simp
  inv_mem' := by
    rintro ⟨g, c⟩ hg
    simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv] at *
    have e1 : ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)ᵀ * (g : Matrix (Fin n) (Fin n) S)ᵀ = 1 := by
      rw [← Matrix.transpose_mul]; simp
    have e2 : (g : Matrix (Fin n) (Fin n) S).map σ * ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).map σ = 1 := by
      rw [← Matrix.map_mul]; simp
    have key : H = j (c : A) • (((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)ᵀ * H *
        ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).map σ) := by
      calc H = ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)ᵀ * ((g : Matrix (Fin n) (Fin n) S)ᵀ * H *
            (g : Matrix (Fin n) (Fin n) S).map σ) * ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).map σ := by
            simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
            rw [Matrix.mul_assoc, e2, Matrix.mul_one]
        _ = _ := by rw [hg, Matrix.mul_smul, Matrix.smul_mul]
    have hu : j ((c⁻¹ : Aˣ) : A) * j (c : A) = 1 := by rw [← map_mul]; simp
    calc _ = (j ((c⁻¹ : Aˣ) : A) * j (c : A)) • (((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S)ᵀ * H *
          ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).map σ) := by rw [hu, one_smul]
      _ = _ := by rw [mul_smul, ← key]

theorem mem_simGroup {j : A →+* S} {σ : S →+* S} {H : Matrix (Fin n) (Fin n) S} {x : GL (Fin n) S × Aˣ} :
    x ∈ simGroup j σ H ↔ (x.1 : Matrix (Fin n) (Fin n) S)ᵀ * H * (x.1 : Matrix (Fin n) (Fin n) S).map σ =
      j (x.2 : A) • H := Iff.rfl

variable {S' A' : Type*} [CommRing S'] [CommRing A']

def simMap {j : A →+* S} {σ : S →+* S} {H : Matrix (Fin n) (Fin n) S}
    {j' : A' →+* S'} {σ' : S' →+* S'} {H' : Matrix (Fin n) (Fin n) S'}
    (φ : S →+* S') (ψ : A →+* A') (hσ : ∀ x, φ (σ x) = σ' (φ x)) (hj : ∀ a, φ (j a) = j' (ψ a))
    (hH : H.map φ = H') : simGroup j σ H →* simGroup j' σ' H' :=
  ((MonoidHom.prodMap (Matrix.GeneralLinearGroup.map φ) (Units.map (ψ : A →* A'))).comp
    (simGroup j σ H).subtype).codRestrict _ fun x => by
    obtain ⟨⟨g, c⟩, hx⟩ := x
    rw [mem_simGroup] at hx ⊢
    subst hH
    show ((g : Matrix (Fin n) (Fin n) S).map φ)ᵀ * H.map φ * ((g : Matrix (Fin n) (Fin n) S).map φ).map σ' =
      j' (ψ (c : A)) • H.map φ
    have hc : (φ ∘ σ) = (σ' ∘ φ) := funext hσ
    have h := congrArg (fun M => M.map φ) hx
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h
    rw [Matrix.map_map, ← hc, h, ← hj]
    ext a b; simp

@[simp] theorem simMap_fst {j : A →+* S} {σ : S →+* S} {H : Matrix (Fin n) (Fin n) S}
    {j' : A' →+* S'} {σ' : S' →+* S'} {H' : Matrix (Fin n) (Fin n) S'}
    (φ : S →+* S') (ψ : A →+* A') (hσ : ∀ x, φ (σ x) = σ' (φ x)) (hj : ∀ a, φ (j a) = j' (ψ a))
    (hH : H.map φ = H') (x : simGroup j σ H) :
    ((((simMap φ ψ hσ hj hH x : simGroup j' σ' H') : GL (Fin n) S' × A'ˣ).1 : GL (Fin n) S') :
      Matrix (Fin n) (Fin n) S') = (((x : GL (Fin n) S × Aˣ).1 : GL (Fin n) S) : Matrix (Fin n) (Fin n) S).map φ :=
  rfl

@[simp] theorem simMap_snd {j : A →+* S} {σ : S →+* S} {H : Matrix (Fin n) (Fin n) S}
    {j' : A' →+* S'} {σ' : S' →+* S'} {H' : Matrix (Fin n) (Fin n) S'}
    (φ : S →+* S') (ψ : A →+* A') (hσ : ∀ x, φ (σ x) = σ' (φ x)) (hj : ∀ a, φ (j a) = j' (ψ a))
    (hH : H.map φ = H') (x : simGroup j σ H) :
    ((((simMap φ ψ hσ hj hH x : simGroup j' σ' H') : GL (Fin n) S' × A'ˣ).2 : A'ˣ) : A') =
      ψ (((x : GL (Fin n) S × Aˣ).2 : Aˣ) : A) :=
  rfl

end Sim

section Points

variable (F : Type) [Field F] [NumberField F] [IsCMField F] {n : ℕ} (H : Matrix (Fin n) (Fin n) F)

def conjQ : F →ₐ[ℚ] F := RingHom.toRatAlgHom ((IsCMField.complexConj F).toRingEquiv.toRingHom)

@[simp] theorem conjQ_apply (x : F) : conjQ F x = IsCMField.complexConj F x := rfl

def conjT (R : Type) [CommRing R] [Algebra ℚ R] : R ⊗[ℚ] F →+* R ⊗[ℚ] F :=
  (Algebra.TensorProduct.map (AlgHom.id ℚ R) (conjQ F)).toRingHom

@[simp] theorem conjT_tmul (R : Type) [CommRing R] [Algebra ℚ R] (r : R) (x : F) :
    conjT F R (r ⊗ₜ x) = r ⊗ₜ IsCMField.complexConj F x := rfl

def Gpts (R : Type) [CommRing R] [Algebra ℚ R] : Subgroup (GL (Fin n) (R ⊗[ℚ] F) × Rˣ) :=
  simGroup (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[ℚ] F) (conjT F R)
    (H.map (Algebra.TensorProduct.includeRight : F →ₐ[ℚ] R ⊗[ℚ] F))

def GQpts : Subgroup (GL (Fin n) F × ℚˣ) :=
  simGroup (algebraMap ℚ F) (IsCMField.complexConj F : F →+* F) H

variable {F H}

def bc (R : Type) [CommRing R] [Algebra ℚ R] : GQpts F H →* Gpts F H R :=
  simMap ((Algebra.TensorProduct.includeRight : F →ₐ[ℚ] R ⊗[ℚ] F) : F →+* R ⊗[ℚ] F) (algebraMap ℚ R)
    (fun x => rfl)
    (fun a => by
      simp only [RingHom.coe_coe, AlgHom.commutes, Algebra.TensorProduct.includeLeftRingHom_apply]
      rfl)
    rfl

def bcMap {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R') :
    Gpts F H R →* Gpts F H R' :=
  simMap ((Algebra.TensorProduct.map f (AlgHom.id ℚ F)).toRingHom) (f : R →+* R')
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r y => rfl
      | add x y hx hy => simp only [map_add, hx, hy])
    (fun a => rfl)
    (by rw [Matrix.map_map]; congr 1; funext x; simp [Algebra.TensorProduct.map_tmul])

def simQ : GQpts F H →* ℚˣ := (MonoidHom.snd _ _).comp (GQpts F H).subtype

def simR (R : Type) [CommRing R] [Algebra ℚ R] : Gpts F H R →* Rˣ := (MonoidHom.snd _ _).comp (Gpts F H R).subtype

theorem simR_bc (R : Type) [CommRing R] [Algebra ℚ R] (g : GQpts F H) :
    ((simR R (bc R g) : Rˣ) : R) = algebraMap ℚ R (simQ g : ℚ) := rfl

end Points

section Topology

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ} {H : Matrix (Fin n) (Fin n) F}

instance Gpts.instTop (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] :
    TopologicalSpace (Gpts F H R) :=
  letI : TopologicalSpace (R ⊗[ℚ] F) := moduleTopology R (R ⊗[ℚ] F)
  inferInstance

instance Gpts.instTopGrp (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalGroup (Gpts F H R) :=
  letI : TopologicalSpace (R ⊗[ℚ] F) := moduleTopology R (R ⊗[ℚ] F)
  haveI : IsModuleTopology R (R ⊗[ℚ] F) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[ℚ] F) := IsModuleTopology.isTopologicalRing R (R ⊗[ℚ] F)
  inferInstance

end Topology

section Adeles

def AwayP (p : ℕ) : Type := {v : HeightOneSpectrum ℤ // v.asIdeal ≠ Ideal.span {(p : ℤ)}}

variable (p : ℕ)

def AfP : Type := Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]

instance : CommRing (AfP p) := inferInstanceAs <|
  CommRing <| Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]

instance : TopologicalSpace (AfP p) := inferInstanceAs <|
  TopologicalSpace <| Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]

instance : IsTopologicalRing (AfP p) :=
  haveI : Fact (∀ v : AwayP p,
      IsOpen (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing (fun (v : AwayP p) ↦ v.1.adicCompletion ℚ)

def AfP.restr : FiniteAdeleRing ℤ ℚ →+* AfP p :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ) Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ RingHom.id _) (Filter.Eventually.of_forall fun _ ↦ Set.mapsTo_id _)

def AfP.diag : ℚ →+* AfP p := (AfP.restr p).comp (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))

instance : Algebra ℚ (AfP p) := (AfP.diag p).toAlgebra

def AfP.eval {p : ℕ} (v : AwayP p) : AfP p →ₐ[ℚ] v.1.adicCompletion ℚ :=
  { RestrictedProduct.evalRingHom (fun v : AwayP p ↦ v.1.adicCompletion ℚ) v with
    commutes' := fun k ↦ DFunLike.congr_fun (RingHom.ext_rat
      ((RestrictedProduct.evalRingHom (fun v : AwayP p ↦ v.1.adicCompletion ℚ) v).comp (algebraMap ℚ (AfP p)))
      (algebraMap ℚ (v.1.adicCompletion ℚ))) k }

end Adeles

section Signature

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ} {H : Matrix (Fin n) (Fin n) F}

def gramAt (H : Matrix (Fin n) (Fin n) F) (τ : F →+* ℂ) : Matrix (Fin n) (Fin n) ℂ := (H.map τ)ᵀ

theorem isHermitian_gramAt (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (τ : F →+* ℂ) :
    (gramAt H τ).IsHermitian := by
  have hH' : H.map (IsCMField.complexConj F : F →+* F) = Hᵀ := by
    rw [← Matrix.transpose_transpose (H.map _), hH]
  unfold Matrix.IsHermitian gramAt
  rw [Matrix.conjTranspose, Matrix.transpose_transpose]
  ext i j
  have := congrArg (fun M => τ (M i j)) hH'
  simp only [Matrix.map_apply, Matrix.transpose_apply] at this ⊢
  rw [← this]
  have h2 : τ ((IsCMField.complexConj F : F →+* F) (H i j)) = (starRingEnd ℂ) (τ (H i j)) :=
    IsCMField.complexEmbedding_complexConj F τ (H i j)
  rw [h2]; rfl

def sigPos (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (τ : F →+* ℂ) : ℕ :=
  Fintype.card {i : Fin n // 0 < (isHermitian_gramAt hH τ).eigenvalues i}

def sigNeg (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (τ : F →+* ℂ) : ℕ :=
  Fintype.card {i : Fin n // (isHermitian_gramAt hH τ).eigenvalues i < 0}

end Signature

section Sign

def sigPosH {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : Fin n // 0 < hA.eigenvalues i}

def sigNegH {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : Fin n // hA.eigenvalues i < 0}

theorem sigPos_eq_sigPosH {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}
    {H : Matrix (Fin n) (Fin n) F} (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (τ : F →+* ℂ) :
    sigPos hH τ = sigPosH (isHermitian_gramAt hH τ) := rfl

end Sign

section UGroup

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

def uGroup (σ : S →+* Sᵐᵒᵖ) : Subgroup (Sˣ × Aˣ) where
  carrier := {x | ((x.1 : Sˣ) : S) * (σ ((x.1 : Sˣ) : S)).unop = algebraMap A S ((x.2 : Aˣ) : A)}
  mul_mem' := by
    rintro ⟨g, c⟩ ⟨h, d⟩ hg hh
    change (g : S) * (σ g).unop = algebraMap A S c at hg
    change (h : S) * (σ h).unop = algebraMap A S d at hh
    change ((g * h : Sˣ) : S) * (σ ((g * h : Sˣ) : S)).unop = algebraMap A S ((c * d : Aˣ) : A)
    rw [Units.val_mul, Units.val_mul, map_mul, MulOpposite.unop_mul, map_mul]
    calc (g : S) * h * ((σ h).unop * (σ g).unop) = g * (h * (σ h).unop) * (σ g).unop := by
          simp only [mul_assoc]
      _ = algebraMap A S d * ((g : S) * (σ g).unop) := by
          rw [hh, ← Algebra.commutes, mul_assoc]
      _ = algebraMap A S c * algebraMap A S d := by rw [hg]; exact Algebra.commutes _ _
  one_mem' := by
    change ((1 : Sˣ) : S) * (σ ((1 : Sˣ) : S)).unop = algebraMap A S ((1 : Aˣ) : A)
    simp
  inv_mem' := by
    rintro ⟨g, c⟩ hg
    change (g : S) * (σ g).unop = algebraMap A S c at hg
    change ((g⁻¹ : Sˣ) : S) * (σ ((g⁻¹ : Sˣ) : S)).unop = algebraMap A S ((c⁻¹ : Aˣ) : A)
    have hst : (σ g).unop * (σ ((g⁻¹ : Sˣ) : S)).unop = 1 := by
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    have hcc : algebraMap A S ((c⁻¹ : Aˣ) : A) * algebraMap A S (c : A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have key : algebraMap A S (c : A) * (((g⁻¹ : Sˣ) : S) * (σ ((g⁻¹ : Sˣ) : S)).unop) = 1 := by
      rw [← mul_assoc, Algebra.commutes, ← hg, ← mul_assoc, Units.inv_mul, one_mul, hst]
    calc _ = algebraMap A S ((c⁻¹ : Aˣ) : A) *
          (algebraMap A S (c : A) * (((g⁻¹ : Sˣ) : S) * (σ ((g⁻¹ : Sˣ) : S)).unop)) := by
          rw [← mul_assoc, hcc, one_mul]
      _ = _ := by rw [key, mul_one]

theorem mem_uGroup {σ : S →+* Sᵐᵒᵖ} {x : Sˣ × Aˣ} :
    x ∈ uGroup σ ↔ ((x.1 : Sˣ) : S) * (σ ((x.1 : Sˣ) : S)).unop = algebraMap A S ((x.2 : Aˣ) : A) := Iff.rfl

variable {S' A' : Type*} [Ring S'] [CommRing A'] [Algebra A' S']

def uMap {σ : S →+* Sᵐᵒᵖ} {σ' : S' →+* S'ᵐᵒᵖ} (φ : S →+* S') (ψ : A →+* A')
    (hσ : ∀ x, (σ' (φ x)).unop = φ (σ x).unop) (hj : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (ψ a)) :
    uGroup (A := A) σ →* uGroup (A := A') σ' :=
  ((MonoidHom.prodMap (Units.map (φ : S →* S')) (Units.map (ψ : A →* A'))).comp
    (uGroup (A := A) σ).subtype).codRestrict _ fun x => by
    obtain ⟨⟨g, c⟩, hx⟩ := x
    have hx' : (g : S) * (σ g).unop = algebraMap A S c := hx
    show φ g * (σ' (φ g)).unop = algebraMap A' S' (ψ c)
    rw [hσ, ← map_mul, hx', hj]

@[simp] theorem uMap_fst {σ : S →+* Sᵐᵒᵖ} {σ' : S' →+* S'ᵐᵒᵖ} (φ : S →+* S') (ψ : A →+* A')
    (hσ : ∀ x, (σ' (φ x)).unop = φ (σ x).unop) (hj : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (ψ a))
    (x : uGroup (A := A) σ) :
    (((uMap φ ψ hσ hj x : uGroup (A := A') σ') : S'ˣ × A'ˣ).1 : S') = φ ((x : Sˣ × Aˣ).1 : S) := rfl

@[simp] theorem uMap_snd {σ : S →+* Sᵐᵒᵖ} {σ' : S' →+* S'ᵐᵒᵖ} (φ : S →+* S') (ψ : A →+* A')
    (hσ : ∀ x, (σ' (φ x)).unop = φ (σ x).unop) (hj : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (ψ a))
    (x : uGroup (A := A) σ) :
    (((uMap φ ψ hσ hj x : uGroup (A := A') σ') : S'ˣ × A'ˣ).2 : A') = ψ ((x : Sˣ × Aˣ).2 : A) := rfl

end UGroup

section UPoints

variable {C : Type} [Ring C] [Algebra ℚ C] (star : C →+* Cᵐᵒᵖ)

def starT (R : Type) [CommRing R] [Algebra ℚ R] : R ⊗[ℚ] C →+* (R ⊗[ℚ] C)ᵐᵒᵖ :=
  (Algebra.TensorProduct.lift (Algebra.ofId R (R ⊗[ℚ] C)ᵐᵒᵖ)
    ((RingHom.op ((Algebra.TensorProduct.includeRight : C →ₐ[ℚ] R ⊗[ℚ] C) : C →+* R ⊗[ℚ] C)).comp
      star).toRatAlgHom
    (fun x _ => Algebra.commute_algebraMap_left x _)).toRingHom

theorem starT_tmul (R : Type) [CommRing R] [Algebra ℚ R] (r : R) (x : C) :
    (starT star R (r ⊗ₜ x)).unop = r ⊗ₜ (star x).unop := by
  change MulOpposite.unop (MulOpposite.op (r ⊗ₜ[ℚ] (1 : C)) * MulOpposite.op ((1 : R) ⊗ₜ[ℚ] (star x).unop)) = _
  rw [← MulOpposite.op_mul, MulOpposite.unop_op, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

def UPts (R : Type) [CommRing R] [Algebra ℚ R] : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ) :=
  uGroup (A := R) (starT star R)

def UQpts : Subgroup (Cˣ × ℚˣ) := uGroup (A := ℚ) star

variable {star}

def ubc (R : Type) [CommRing R] [Algebra ℚ R] : UQpts star →* UPts star R :=
  uMap ((Algebra.TensorProduct.includeRight : C →ₐ[ℚ] R ⊗[ℚ] C) : C →+* R ⊗[ℚ] C) (algebraMap ℚ R)
    (fun x => starT_tmul star R 1 x)
    (fun a => by
      simp only [RingHom.coe_coe, AlgHom.commutes]
      exact IsScalarTower.algebraMap_apply ℚ R (R ⊗[ℚ] C) a)

def ubcMap {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R') :
    UPts star R →* UPts star R' :=
  uMap ((Algebra.TensorProduct.map f (AlgHom.id ℚ C)).toRingHom) (f : R →+* R')
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r y =>
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          starT_tmul]
      | add x y hx hy => simp only [map_add, MulOpposite.unop_add, hx, hy])
    (fun a => by simp [Algebra.TensorProduct.algebraMap_apply])

def uSimQ : UQpts star →* ℚˣ := (MonoidHom.snd _ _).comp (UQpts star).subtype

def uSimR (R : Type) [CommRing R] [Algebra ℚ R] : UPts star R →* Rˣ :=
  (MonoidHom.snd _ _).comp (UPts star R).subtype

theorem uSimR_ubc (R : Type) [CommRing R] [Algebra ℚ R] (g : UQpts star) :
    ((uSimR R (ubc R g) : Rˣ) : R) = algebraMap ℚ R (uSimQ g : ℚ) := rfl

theorem ubcMap_ubc {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
    (g : UQpts star) : ubcMap f (ubc R g) = ubc R' g := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    change (Algebra.TensorProduct.map f (AlgHom.id ℚ C)) ((1 : R) ⊗ₜ (((g : Cˣ × ℚˣ).1 : Cˣ) : C)) =
      (1 : R') ⊗ₜ (((g : Cˣ × ℚˣ).1 : Cˣ) : C)
    simp [Algebra.TensorProduct.map_tmul]
  · apply Units.ext
    exact f.commutes _

variable [Module.Finite ℚ C]

instance UPts.instTop (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] :
    TopologicalSpace (UPts star R) :=
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  inferInstance

instance UPts.instTopGrp (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsTopologicalGroup (UPts star R) :=
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[ℚ] C) := IsModuleTopology.isTopologicalRing R (R ⊗[ℚ] C)
  inferInstance

end UPoints

def LiesOver {p : ℕ} [Fact p.Prime] {F : Type} [Field F] (Kq : Subfield F) (u : Kq →+* ℚ_[p])
    (τ : F →+* PadicAlgCl p) : Prop :=
  ∀ x : Kq, τ x = algebraMap ℚ_[p] (PadicAlgCl p) (u x)

section Local

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

def FwOf (τ : F →+* PadicAlgCl p) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] (Set.range τ)

def embOf (τ : F →+* PadicAlgCl p) : F →+* FwOf τ :=
  τ.codRestrict (FwOf τ) (fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)

@[simp] theorem embOf_apply (τ : F →+* PadicAlgCl p) (x : F) : ((embOf τ x : FwOf τ) : PadicAlgCl p) = τ x := rfl

end Local

structure HTGroup (p : ℕ) [Fact p.Prime] where

  F : Type
  [fieldF : Field F]
  [numF : NumberField F]
  [cmF : IsCMField F]

  Kq : Subfield F
  hKq : Module.finrank ℚ Kq = 2 ∧ ∀ τ : F →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0

  u : Kq →+* ℚ_[p]

  n : ℕ
  n_pos : 0 < n

  C : Type
  [ringC : Ring C]
  [algC : Algebra F C]
  [algQC : Algebra ℚ C]
  [towerC : IsScalarTower ℚ F C]
  [finC : FiniteDimensional F C]
  [centralC : Algebra.IsCentral F C]
  [simpleC : IsSimpleRing C]
  rankC : Module.finrank F C = n ^ 2

  star : C →+* Cᵐᵒᵖ
  star_star : ∀ x, (star (star x).unop).unop = x

  star_F : ∀ x : F, (star (algebraMap F C x)).unop = algebraMap F C (IsCMField.complexConj F x)

  psi : InfinitePlace F → (C →+* Matrix (Fin n) (Fin n) ℂ)
  psi_F : ∀ v (x : F), psi v (algebraMap F C x) = Matrix.scalar (Fin n) (v.embedding x)

  gram : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ
  gram_herm : ∀ v, (gram v).IsHermitian
  gram_det : ∀ v, (gram v).det ≠ 0
  psi_star : ∀ v x, psi v (star x).unop = (gram v)⁻¹ * (psi v x)ᴴ * gram v

  sig : ∀ v, (sigPosH (gram_herm v) = 1 ∧ sigNegH (gram_herm v) = n - 1) ∨
    (sigPosH (gram_herm v) = 0 ∧ sigNegH (gram_herm v) = n)

  m : ℕ

  emb : Fin m → (F →+* PadicAlgCl p)
  emb_over : ∀ i, LiesOver Kq u (emb i)
  emb_inj : ∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
    ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i) = emb j → i = j
  emb_all : ∀ τ : F →+* PadicAlgCl p, LiesOver Kq u τ →
    ∃ i, ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      τ = ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i)

  rho : ∀ i : Fin m, C →+* Matrix (Fin n) (Fin n) (FwOf (emb i))
  rho_F : ∀ i (x : F), rho i (algebraMap F C x) = Matrix.scalar (Fin n) (embOf (emb i) x)

  iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p

  iotaC : AlgebraicClosure ℚ →+* ℂ

attribute [instance] HTGroup.fieldF HTGroup.numF HTGroup.cmF HTGroup.ringC HTGroup.algC HTGroup.algQC
  HTGroup.towerC HTGroup.finC HTGroup.centralC HTGroup.simpleC
section BcLemmas

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ} {H : Matrix (Fin n) (Fin n) F}

theorem bcMap_bc {R R' : Type} [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
    (g : GQpts F H) : bcMap f (bc R g) = bc R' g := by
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    ext i j
    change (Algebra.TensorProduct.map f (AlgHom.id ℚ F))
        (Algebra.TensorProduct.includeRight (((g : GL (Fin n) F × ℚˣ).1 : Matrix (Fin n) (Fin n) F) i j)) =
      Algebra.TensorProduct.includeRight (((g : GL (Fin n) F × ℚˣ).1 : Matrix (Fin n) (Fin n) F) i j)
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  · apply Units.ext
    simp only [bcMap, bc, simMap_snd]
    exact f.commutes _

end BcLemmas
namespace HTGroup

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

instance finQ : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C

abbrev GQ : Type := UQpts G.star

abbrev W : Type := Fin G.m

abbrev GR : Type := UPts G.star ℝ

abbrev GAf : Type := UPts G.star (AfP p)

abbrev GQp : Type := UPts G.star ℚ_[p]

abbrev GQbar : Type := UPts G.star (AlgebraicClosure ℚ)

def toAf : G.GQ →* G.GAf := ubc (AfP p)

def toR : G.GQ →* G.GR := ubc ℝ

def sim : G.GQ →* ℚˣ := uSimQ

def a : ℕ := Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1}

abbrev Fw (i : Fin G.m) : IntermediateField ℚ_[p] (PadicAlgCl p) := FwOf (G.emb i)

def embW (i : Fin G.m) : G.F →+* G.Fw i := embOf (G.emb i)

def liftW (i : Fin G.m) : ℚ_[p] ⊗[ℚ] G.F →ₐ[ℚ] G.Fw i :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom ℚ ℚ_[p] (G.Fw i)) (G.embW i).toRatAlgHom
    (fun _ _ => Commute.all _ _)

def locW (i : Fin G.m) : ℚ_[p] ⊗[ℚ] G.C →ₐ[ℚ_[p]] Matrix (Fin G.n) (Fin G.n) (G.Fw i) :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[p] _) (G.rho i).toRatAlgHom (fun x _ => Algebra.commute_algebraMap_left x _)

def localization₂ : G.GQp →* ℚ_[p]ˣ × ((i : Fin G.m) → GL (Fin G.n) (G.Fw i)) :=
  MonoidHom.prod (uSimR ℚ_[p]) (Pi.monoidHom fun i =>
    (Units.map ((G.locW i : ℚ_[p] ⊗[ℚ] G.C →+* Matrix (Fin G.n) (Fin G.n) (G.Fw i)) :
        ℚ_[p] ⊗[ℚ] G.C →* Matrix (Fin G.n) (Fin G.n) (G.Fw i))).comp
      ((MonoidHom.fst _ _).comp (UPts G.star ℚ_[p]).subtype))

def toP : G.GQ →* ℚ_[p]ˣ × ((i : Fin G.m) → GL (Fin G.n) (G.Fw i)) := G.localization₂.comp (ubc ℚ_[p])

theorem toPadic_fst (g : G.GQ) : (((G.toP g).1 : ℚ_[p]ˣ) : ℚ_[p]) = ((G.sim g : ℚ) : ℚ_[p]) := by
  show ((((ubc ℚ_[p] g : UPts G.star ℚ_[p]) : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ).2 : ℚ_[p]ˣ) : ℚ_[p]) = _
  simp only [ubc, uMap_snd]
  rfl

theorem toPadic_snd (g : G.GQ) (w : G.W) :
    ((G.toP g).2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) = G.rho w (((g : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
  change G.locW w ((1 : ℚ_[p]) ⊗ₜ (((g : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) = _
  change (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (1 : ℚ_[p])) *
    (G.rho w).toRatAlgHom (((g : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = _
  rw [map_one, one_mul]
  rfl

def IsSS (γ : G.GQ) : Prop :=
  Module.End.IsSemisimple (LinearMap.mulLeft G.F (((γ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))

def psiR (v : InfinitePlace G.F) : ℝ ⊗[ℚ] G.C →ₐ[ℝ] Matrix (Fin G.n) (Fin G.n) ℂ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℝ _) (G.psi v).toRatAlgHom (fun x _ => Algebra.commute_algebraMap_left x _)

def IsEllR (γ : G.GR) : Prop :=
  ∀ v : InfinitePlace G.F,
    Module.End.IsSemisimple (Matrix.toLin' (G.psiR v (((γ : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : (ℝ ⊗[ℚ] G.C)ˣ) : ℝ ⊗[ℚ] G.C))) ∧
    ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.toLin' (G.psiR v (((γ : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : (ℝ ⊗[ℚ] G.C)ˣ) : ℝ ⊗[ℚ] G.C))) μ →
      ‖μ‖ ^ 2 = (((γ : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ)

def StQ (γ γ' : G.GQ) : Prop := ∃ h : G.GQbar, h * ubc _ γ * h⁻¹ = ubc _ γ'

def StAf (γ₀ : G.GQ) (γ : G.GAf) : Prop :=
  ∀ v : AwayP p, ∃ h : UPts G.star (AlgebraicClosure (v.1.adicCompletion ℚ)),
    h * ubcMap (IsScalarTower.toAlgHom ℚ (v.1.adicCompletion ℚ) (AlgebraicClosure (v.1.adicCompletion ℚ)))
      (ubcMap (AfP.eval v) γ) * h⁻¹ = ubc _ γ₀

def MuIdx : Type := {s : G.F →+* AlgebraicClosure ℚ // LiesOver G.Kq G.u (G.iotaP.comp s)}

def placeOf (s : G.MuIdx) : Fin G.m := (G.emb_all _ s.2).choose

def mu0 : ℤ := 1

def mu (s : G.MuIdx) : Fin G.n → ℤ :=
  if sigPosH (G.gram_herm (InfinitePlace.mk (G.iotaC.comp s.1))) = 1 then Pi.single ⟨0, G.n_pos⟩ 1 else 0

structure Level (G : HTGroup p) where

  K : OpenSubgroup G.GAf
  compact : IsCompact (K : Set G.GAf)

theorem stQ_refl (γ : G.GQ) : G.StQ γ γ := ⟨1, by simp⟩

theorem stQ_symm {γ γ' : G.GQ} (h : G.StQ γ γ') : G.StQ γ' γ := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x⁻¹, by rw [← hx]; group⟩

theorem stQ_trans {γ γ' γ'' : G.GQ} (h : G.StQ γ γ') (h' : G.StQ γ' γ'') : G.StQ γ γ'' := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := h'
  exact ⟨y * x, by rw [← hy, ← hx]; group⟩

theorem stAf_toAf (γ₀ : G.GQ) : G.StAf γ₀ (G.toAf γ₀) := fun v => ⟨1, by simp [toAf, ubcMap_ubc]⟩

theorem isSS_one : G.IsSS 1 := by
  show Module.End.IsSemisimple (LinearMap.mulLeft G.F (1 : G.C))
  rw [LinearMap.mulLeft_one]
  exact Module.End.isSemisimple_id

end HTGroup

namespace HTGroup

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

instance finiteDimensional_Fw (i : Fin G.m) : FiniteDimensional ℚ_[p] (G.Fw i) := by
  let b := Module.finBasis ℚ G.F
  have hle : G.Fw i ≤ IntermediateField.adjoin ℚ_[p] (Set.range (fun k => G.emb i (b k))) := by
    rw [Fw, FwOf, IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun k _ => ?_
    have : G.emb i (b.repr x k • b k) = algebraMap ℚ_[p] (PadicAlgCl p) ((b.repr x k : ℚ) : ℚ_[p]) * G.emb i (b k) := by
      rw [Rat.smul_def, map_mul, map_ratCast, map_ratCast]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨k, rfl⟩)
  have hfin : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (Set.range (fun k => G.emb i (b k)))) := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨k, rfl⟩
    have h1 : IsIntegral ℚ (G.emb i (b k)) :=
      (Algebra.IsIntegral.isIntegral (R := ℚ) (b k)).map (G.emb i).toRatAlgHom
    exact h1.tower_top
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

theorem isEllR_one : G.IsEllR 1 := by
  intro v
  have h1 : Matrix.toLin' (G.psiR v ((((1 : G.GR) : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : (ℝ ⊗[ℚ] G.C)ˣ) : ℝ ⊗[ℚ] G.C)) =
      LinearMap.id := by
    simp
  rw [h1]
  refine ⟨Module.End.isSemisimple_id, fun μ hμ => ?_⟩
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have h2 : x = μ • x := by simpa using hx.apply_eq_smul
  have h3 : μ = 1 := by
    have : (μ - 1) • x = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hx.2)
  simp [h3]

theorem sim_pos_of_isEllR {γ : G.GR} (h : G.IsEllR γ) : 0 < (((γ : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).2 : ℝˣ) : ℝ) := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue
    (Matrix.toLin' (G.psiR v (((γ : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : (ℝ ⊗[ℚ] G.C)ˣ) : ℝ ⊗[ℚ] G.C)))
  have hc := (h v).2 μ hμ
  have hu : IsUnit (G.psiR v (((γ : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : (ℝ ⊗[ℚ] G.C)ˣ) : ℝ ⊗[ℚ] G.C)) :=
    ((γ : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1.isUnit).map (G.psiR v)
  have hdet := ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have h0 : (G.psiR v (((γ : (ℝ ⊗[ℚ] G.C)ˣ × ℝˣ).1 : (ℝ ⊗[ℚ] G.C)ˣ) : ℝ ⊗[ℚ] G.C)) *ᵥ x = 0 := by
      simpa [Matrix.toLin'_apply] using hx.apply_eq_smul
    exact hx.2 (Matrix.eq_zero_of_mulVec_eq_zero hdet h0)
  rw [← hc]
  exact pow_pos (norm_pos_iff.2 hμ0) 2

example : IsTopologicalGroup G.GAf := inferInstance
example : IsTopologicalGroup G.GR := inferInstance
example : IsTopologicalGroup G.GQp := inferInstance

end HTGroup

section Herm

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {n : ℕ}

theorem map_nonsingInv {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) {A : Matrix (Fin n) (Fin n) K}
    (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

def hermStar (H : Matrix (Fin n) (Fin n) F) (hdet : H.det ≠ 0) :
    Matrix (Fin n) (Fin n) F →+* (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ where
  toFun x := MulOpposite.op ((H.map (IsCMField.complexConj F : F →+* F))⁻¹ *
    (x.map (IsCMField.complexConj F : F →+* F))ᵀ * H.map (IsCMField.complexConj F : F →+* F))
  map_one' := by
    have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero _).2 hdet |>.isUnit
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hu, MulOpposite.op_one]
  map_mul' x y := by
    have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero _).2 hdet |>.isUnit
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  map_zero' := by simp
  map_add' x y := by
    apply MulOpposite.unop_injective
    simp [Matrix.map_add, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem hermStar_apply (H : Matrix (Fin n) (Fin n) F) (hdet : H.det ≠ 0) (x : Matrix (Fin n) (Fin n) F) :
    (hermStar H hdet x).unop = (H.map (IsCMField.complexConj F : F →+* F))⁻¹ *
      (x.map (IsCMField.complexConj F : F →+* F))ᵀ * H.map (IsCMField.complexConj F : F →+* F) := rfl

theorem map_conj_conj (x : Matrix (Fin n) (Fin n) F) :
    (x.map (IsCMField.complexConj F : F →+* F)).map (IsCMField.complexConj F : F →+* F) = x := by
  ext i j
  simp [IsCMField.complexConj_apply_apply]

theorem hermStar_hermStar {H : Matrix (Fin n) (Fin n) F} (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H)
    (hdet : H.det ≠ 0) (x : Matrix (Fin n) (Fin n) F) :
    (hermStar H hdet (hermStar H hdet x).unop).unop = x := by
  have hT : H.map (IsCMField.complexConj F : F →+* F) = Hᵀ := by
    rw [← Matrix.transpose_transpose (H.map _), hH]
  have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hdet |>.isUnit
  have huH : IsUnit H.det := (Ne.isUnit hdet)
  rw [hermStar_apply, hermStar_apply, Matrix.map_mul, Matrix.map_mul, map_nonsingInv _ hu, map_conj_conj,
    Matrix.transpose_map, map_conj_conj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, ← hT]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul _ hu,
    Matrix.mul_one]

theorem hermStar_algebraMap (H : Matrix (Fin n) (Fin n) F) (hdet : H.det ≠ 0) (a : F) :
    (hermStar H hdet (algebraMap F (Matrix (Fin n) (Fin n) F) a)).unop =
      algebraMap F (Matrix (Fin n) (Fin n) F) (IsCMField.complexConj F a) := by
  have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hdet |>.isUnit
  have e : ((algebraMap F (Matrix (Fin n) (Fin n) F) a).map (IsCMField.complexConj F : F →+* F))ᵀ =
      algebraMap F (Matrix (Fin n) (Fin n) F) (IsCMField.complexConj F a) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.algebraMap_matrix_apply]
    · simp [Matrix.algebraMap_matrix_apply, h, Ne.symm h]
  rw [hermStar_apply, e, ← Algebra.commutes, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem map_algebraMap_eq_scalar {K L : Type*} [Field K] [CommRing L] (f : K →+* L) (a : K) :
    (algebraMap K (Matrix (Fin n) (Fin n) K) a).map f = Matrix.scalar (Fin n) (f a) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, h]

theorem mul_eq_smul_one_comm {K : Type*} [Field K] {A B : Matrix (Fin n) (Fin n) K} {c : K} (hc : c ≠ 0) :
    A * B = c • 1 ↔ B * A = c • 1 := by
  have key : ∀ A B : Matrix (Fin n) (Fin n) K, A * B = c • 1 → B * A = c • 1 := by
    intro A B h
    have h1 : A * (c⁻¹ • B) = 1 := by rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have h2 := mul_eq_one_comm.1 h1
    rw [Matrix.smul_mul] at h2
    calc B * A = c • (c⁻¹ • (B * A)) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      _ = c • 1 := by rw [h2]
  exact ⟨key A B, key B A⟩

theorem hermStar_mul_eq_iff {H : Matrix (Fin n) (Fin n) F}
    (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (hdet : H.det ≠ 0) {c : F} (hc : c ≠ 0)
    (g : Matrix (Fin n) (Fin n) F) :
    g * (hermStar H hdet g).unop = c • 1 ↔ gᵀ * H * g.map (IsCMField.complexConj F : F →+* F) = c • H := by
  have hT : H.map (IsCMField.complexConj F : F →+* F) = Hᵀ := by
    rw [← Matrix.transpose_transpose (H.map _), hH]
  have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 hdet |>.isUnit
  have e : ∀ M : Matrix (Fin n) (Fin n) F, (H.map (IsCMField.complexConj F : F →+* F))⁻¹ * M = c • 1 ↔
      M = c • H.map (IsCMField.complexConj F : F →+* F) := fun M =>
    ⟨fun h => by rw [← Matrix.mul_nonsing_inv_cancel_left _ M hu, h, Matrix.mul_smul, Matrix.mul_one],
     fun h => by rw [h, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hu]⟩
  rw [hermStar_apply, mul_eq_smul_one_comm hc, Matrix.mul_assoc, Matrix.mul_assoc, e, hT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

theorem mem_UQpts_hermStar_iff {H : Matrix (Fin n) (Fin n) F}
    (hH : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (hdet : H.det ≠ 0)
    (x : (Matrix (Fin n) (Fin n) F)ˣ × ℚˣ) :
    x ∈ UQpts (hermStar H hdet) ↔ ((x.1 : Matrix (Fin n) (Fin n) F))ᵀ * H *
      (x.1 : Matrix (Fin n) (Fin n) F).map (IsCMField.complexConj F : F →+* F) = algebraMap ℚ F (x.2 : ℚ) • H := by
  have hc : algebraMap ℚ F (x.2 : ℚ) ≠ 0 := (map_ne_zero _).2 x.2.ne_zero
  rw [UQpts, mem_uGroup, ← hermStar_mul_eq_iff hH hdet hc, Algebra.algebraMap_eq_smul_one, algebraMap_smul]

end Herm

def ofHerm {p : ℕ} [Fact p.Prime] (F : Type) [Field F] [NumberField F] [IsCMField F] (Kq : Subfield F)
    (hKq : Module.finrank ℚ Kq = 2 ∧ ∀ τ : F →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0) (u : Kq →+* ℚ_[p])
    (n : ℕ) (n_pos : 0 < n) (H : Matrix (Fin n) (Fin n) F)
    (herm : (H.map (IsCMField.complexConj F : F →+* F))ᵀ = H) (det_ne : H.det ≠ 0)
    (sig : ∀ τ : F →+* ℂ, (sigPos herm τ = 1 ∧ sigNeg herm τ = n - 1) ∨ (sigPos herm τ = 0 ∧ sigNeg herm τ = n))
    (m : ℕ) (emb : Fin m → (F →+* PadicAlgCl p)) (emb_over : ∀ i, LiesOver Kq u (emb i))
    (emb_inj : ∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i) = emb j → i = j)
    (emb_all : ∀ τ : F →+* PadicAlgCl p, LiesOver Kq u τ →
      ∃ i, ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        τ = ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i))
    (iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p) (iotaC : AlgebraicClosure ℚ →+* ℂ) : HTGroup p :=
  haveI : NeZero n := ⟨n_pos.ne'⟩
  { F := F
    Kq := Kq
    hKq := hKq
    u := u
    n := n
    n_pos := n_pos
    C := Matrix (Fin n) (Fin n) F
    rankC := by rw [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]; ring
    star := hermStar H det_ne
    star_star := hermStar_hermStar herm det_ne
    star_F := hermStar_algebraMap H det_ne
    psi := fun v => (v.embedding).mapMatrix
    psi_F := fun v x => map_algebraMap_eq_scalar _ x
    gram := fun v => gramAt H v.embedding
    gram_herm := fun v => isHermitian_gramAt herm v.embedding
    gram_det := fun v => by
      rw [gramAt, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (map_ne_zero _).2 det_ne
    psi_star := fun v x => by
      have hu : IsUnit (H.map (IsCMField.complexConj F : F →+* F)).det := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact (map_ne_zero _).2 det_ne |>.isUnit
      have hT : H.map (IsCMField.complexConj F : F →+* F) = Hᵀ := by
        rw [← Matrix.transpose_transpose (H.map _), herm]
      have hg : (H.map (IsCMField.complexConj F : F →+* F)).map v.embedding = gramAt H v.embedding := by
        rw [hT, gramAt, Matrix.transpose_map]
      have hx : ((x.map (IsCMField.complexConj F : F →+* F))ᵀ).map v.embedding = (x.map v.embedding)ᴴ := by
        ext i j
        simp [Matrix.conjTranspose_apply, IsCMField.complexEmbedding_complexConj]
      show (_ : Matrix (Fin n) (Fin n) F).map v.embedding = _
      rw [hermStar_apply, Matrix.map_mul, Matrix.map_mul, map_nonsingInv _ hu, hg, hx]
      rfl
    sig := fun v => sig v.embedding
    m := m
    emb := emb
    emb_over := emb_over
    emb_inj := emb_inj
    emb_all := emb_all
    rho := fun i => (embOf (emb i)).mapMatrix
    rho_F := fun i x => map_algebraMap_eq_scalar _ x
    iotaP := iotaP
    iotaC := iotaC }

namespace Example

abbrev QI : Type := CyclotomicField 4 ℚ

instance isCyclotomicExtension_QI : IsCyclotomicExtension {4} ℚ QI := CyclotomicField.isCyclotomicExtension 4 ℚ

instance isCMField_QI : IsCMField QI := IsCyclotomicExtension.Rat.isCMField (S := {4}) QI ⟨4, rfl, by norm_num⟩

theorem finrank_QI : Module.finrank ℚ QI = 2 := by
  have := IsCyclotomicExtension.finrank (n := 4) QI (Polynomial.cyclotomic.irreducible_rat (by norm_num))
  rw [this]; decide

theorem zeta_sq : (IsCyclotomicExtension.zeta 4 ℚ QI) ^ 2 = -1 :=
  ((IsCyclotomicExtension.zeta_spec 4 ℚ QI).pow (by norm_num) (show 4 = 2 * 2 by norm_num)).eq_neg_one_of_two_right

theorem hK_QI : Module.finrank ℚ (⊤ : Subfield QI) = 2 ∧ ∀ τ : QI →+* ℂ, ∃ x ∈ (⊤ : Subfield QI), (τ x).im ≠ 0 := by
  constructor
  · rw [← finrank_QI]
    exact LinearEquiv.finrank_eq
      { toFun := fun x => (x : QI), invFun := fun x => ⟨x, Subfield.mem_top x⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl,
        map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  · intro τ
    refine ⟨IsCyclotomicExtension.zeta 4 ℚ QI, Subfield.mem_top _, fun h => ?_⟩
    have h3 := congrArg (fun z => (τ z).re) zeta_sq
    simp only [map_pow, map_neg, map_one, pow_two, map_mul, Complex.mul_re, h, Complex.neg_re, Complex.one_re] at h3
    nlinarith [mul_self_nonneg (τ (IsCyclotomicExtension.zeta 4 ℚ QI)).re]

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem exists_sqrt_neg_one : ∃ s : ℤ_[5], s * s = -1 := by
  have h2 : ‖(2 : ℤ_[5])‖ = 1 := by
    have := (PadicInt.norm_natCast_eq_one_iff (p := 5) (n := 2)).2 (by norm_num)
    simpa using this
  have h5 : ‖(5 : ℤ_[5])‖ < 1 := by
    have := PadicInt.norm_p (p := 5)
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num
  have hn : ‖(Polynomial.X ^ 2 + 1 : Polynomial ℤ_[5]).aeval (2 : ℤ_[5])‖ <
      ‖(Polynomial.X ^ 2 + 1 : Polynomial ℤ_[5]).derivative.aeval (2 : ℤ_[5])‖ ^ 2 := by
    have e1 : (Polynomial.X ^ 2 + 1 : Polynomial ℤ_[5]).aeval (2 : ℤ_[5]) = 5 := by
      simp; norm_num
    have e2 : (Polynomial.X ^ 2 + 1 : Polynomial ℤ_[5]).derivative.aeval (2 : ℤ_[5]) = 2 * 2 := by
      simp; norm_num
    rw [e1, e2, norm_mul, h2]; simpa using h5
  obtain ⟨s, hs, -⟩ := hensels_lemma hn
  refine ⟨s, ?_⟩
  simp at hs
  linear_combination hs

def sqrtNegOne : ℚ_[5] := ((exists_sqrt_neg_one.choose : ℤ_[5]) : ℚ_[5])

theorem sqrtNegOne_sq : sqrtNegOne ^ 2 + 1 = 0 := by
  have h := exists_sqrt_neg_one.choose_spec
  have h' := congrArg (fun z : ℤ_[5] => (z : ℚ_[5])) h
  simp only [PadicInt.coe_mul, PadicInt.coe_neg, PadicInt.coe_one] at h'
  unfold sqrtNegOne; rw [pow_two, h']; ring

def gaussianToQFive : QI →+* ℚ_[5] :=
  ((IsCyclotomicExtension.zeta_spec 4 ℚ QI).powerBasis ℚ).lift sqrtNegOne (by
    rw [IsPrimitiveRoot.powerBasis_gen, ← Polynomial.cyclotomic_eq_minpoly_rat
      (IsCyclotomicExtension.zeta_spec 4 ℚ QI) (by norm_num)]
    have : Polynomial.cyclotomic 4 ℚ = Polynomial.X ^ 2 + 1 := by
      rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num, Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℚ) Nat.prime_two]
      simp [Finset.sum_range_succ]; ring
    rw [this]; simpa using sqrtNegOne_sq) |>.toRingHom

def Hc (c : ℚ) : Matrix (Fin 1) (Fin 1) QI := !![(c : QI)]

theorem herm_Hc (c : ℚ) : ((Hc c).map (IsCMField.complexConj QI : QI →+* QI))ᵀ = Hc c := by
  ext i j; fin_cases i; fin_cases j; simp [Hc]

theorem eig_Hc (c : ℚ) (τ : QI →+* ℂ) (i : Fin 1) :
    (isHermitian_gramAt (herm_Hc c) τ).eigenvalues i = c := by
  have h := (isHermitian_gramAt (herm_Hc c) τ).det_eq_prod_eigenvalues
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [Fin.prod_univ_one, gramAt, Hc, Matrix.det_unique, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, map_ratCast] at h
  have h' : ((isHermitian_gramAt (herm_Hc c) τ).eigenvalues 0 : ℂ) = ((c : ℝ) : ℂ) := by
    rw [Complex.ofReal_ratCast]; first | exact h | exact h.symm
  exact_mod_cast h'

theorem sig_Hc (c : ℚ) (hc : c ≠ 0) (τ : QI →+* ℂ) :
    (sigPos (herm_Hc c) τ = 1 ∧ sigNeg (herm_Hc c) τ = 1 - 1) ∨ (sigPos (herm_Hc c) τ = 0 ∧ sigNeg (herm_Hc c) τ = 1) := by
  unfold sigPos sigNeg
  simp only [eig_Hc]
  rcases lt_or_gt_of_ne hc with h | h
  · right
    have h' : (c : ℝ) < 0 := by exact_mod_cast h
    simp [h', not_lt.2 h'.le]
  · left
    have h' : (0 : ℝ) < c := by exact_mod_cast h
    simp [h', not_lt.2 h'.le]

def ex (c : ℚ) (hc : c ≠ 0) : HTGroup 5 :=
  ofHerm QI ⊤ hK_QI (gaussianToQFive.comp (⊤ : Subfield QI).subtype) 1 Nat.one_pos (Hc c) (herm_Hc c) (by simp [Hc, hc])
    (sig_Hc c hc) 1 (fun _ => (algebraMap ℚ_[5] (PadicAlgCl 5)).comp gaussianToQFive) (fun _ _ => rfl)
    (fun i j _ _ => Subsingleton.elim i j)
    (fun τ hτ => ⟨0, AlgEquiv.refl, by ext x; exact hτ ⟨x, Subfield.mem_top x⟩⟩)
    (haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ;
      (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl 5).toRingHom)
    (haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ;
      (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom)

example : (ex 1 one_ne_zero).n = 1 := rfl
example : (ex (-1) (by norm_num)).IsSS 1 := HTGroup.isSS_one _
example (γ : (ex 1 one_ne_zero).GQ) : (ex 1 one_ne_zero).StQ γ γ := HTGroup.stQ_refl _ γ
example : (ex 1 one_ne_zero).IsEllR 1 := HTGroup.isEllR_one _
example : Module.finrank (ex 1 one_ne_zero).F (ex 1 one_ne_zero).C = 1 := (ex 1 one_ne_zero).rankC.trans rfl

end Example

namespace Example

theorem sigPos_Hc (c : ℚ) (τ : QI →+* ℂ) : sigPos (herm_Hc c) τ = if 0 < c then 1 else 0 := by
  unfold sigPos
  simp only [eig_Hc]
  split_ifs with h
  · have h' : (0 : ℝ) < c := by exact_mod_cast h
    simp [h']
  · have h' : ¬ (0 : ℝ) < c := by exact_mod_cast h
    simp [h']

theorem card_infinitePlace_QI : Fintype.card (InfinitePlace QI) = 1 := by
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank QI
  have h2 : NumberField.InfinitePlace.nrRealPlaces QI = 0 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero QI
  rw [finrank_QI, h2] at h1
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h2]
  omega

theorem a_ex_one : (ex 1 one_ne_zero).a = 1 := by
  show Fintype.card {v : InfinitePlace QI // sigPos (herm_Hc 1) v.embedding = 1} = 1
  simp only [sigPos_Hc, zero_lt_one, if_true]
  rw [Fintype.card_subtype_true, card_infinitePlace_QI]

theorem a_ex_neg_one : (ex (-1) (by norm_num)).a = 0 := by
  show Fintype.card {v : InfinitePlace QI // sigPos (herm_Hc (-1)) v.embedding = 1} = 0
  simp [sigPos_Hc]

end Example

end GlobalTheory.LKTrip
