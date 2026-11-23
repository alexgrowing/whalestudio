import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective

noncomputable section

open CategoryTheory Module Matrix

namespace GlobalTheory.VDiv

section Modules

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (S : Type) [CommRing S] [Algebra O S]

structure VarpiDivModule : Type 1 where

  G : PDivGroup p S

  ι : PDivGroup.Action O G

  isNilpotent_p : IsNilpotent (p : S)

  lie_smul : ∀ (a : O) (x : G.Lie), ι.onLie a x = algebraMap O S a • x

namespace VarpiDivModule

variable {p O S}

theorem onLie_eq (H : VarpiDivModule p O S) (a : O) :
    H.ι.onLie a = algebraMap O S a • LinearMap.id :=
  LinearMap.ext fun x => H.lie_smul a x

theorem ι_algebraMap [Algebra ℤ_[p] O] (H : VarpiDivModule p O S) (a : ℤ_[p]) :
    H.ι (algebraMap ℤ_[p] O a) = algebraMap ℤ_[p] (End H.G) a :=
  H.ι.map_algebraMap a

@[ext] structure Hom (H H' : VarpiDivModule p O S) : Type where

  f : H.G ⟶ H'.G

  comm : ∀ a : O, (H.ι a : H.G ⟶ H.G) ≫ f = f ≫ (H'.ι a : H'.G ⟶ H'.G)

instance : Category (VarpiDivModule p O S) where
  Hom := Hom
  id H := ⟨𝟙 _, fun a => by rw [Category.comp_id, Category.id_comp]⟩
  comp f g := ⟨f.f ≫ g.f, fun a => by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, Category.assoc]⟩
  id_comp f := Hom.ext (Category.id_comp f.f)
  comp_id f := Hom.ext (Category.comp_id f.f)
  assoc f g h := Hom.ext (Category.assoc f.f g.f h.f)

@[simp] theorem id_f (H : VarpiDivModule p O S) : Hom.f (𝟙 H) = 𝟙 H.G := rfl

@[simp] theorem comp_f {H H' H'' : VarpiDivModule p O S} (f : H ⟶ H') (g : H' ⟶ H'') :
    Hom.f (f ≫ g) = f.f ≫ g.f := rfl

@[ext] theorem hom_ext {H H' : VarpiDivModule p O S} {f g : H ⟶ H'} (h : f.f = g.f) : f = g :=
  Hom.ext h

def HasDim (H : VarpiDivModule p O S) (d : ℕ) : Prop :=
  Module.Finite S H.G.Lie ∧ Module.Projective S H.G.Lie ∧
    ∀ q : PrimeSpectrum S, rankAtStalk H.G.Lie q = d

def HasOHeight [Algebra ℤ_[p] O] (H : VarpiDivModule p O S) (n : ℕ) : Prop :=
  Module.Free ℤ_[p] O ∧ Module.Finite ℤ_[p] O ∧ H.G.height = n * Module.finrank ℤ_[p] O

def IsOneDimOfHeight [Algebra ℤ_[p] O] (H : VarpiDivModule p O S) (n : ℕ) : Prop :=
  H.HasDim 1 ∧ H.HasOHeight n

theorem hasOHeight_iff [Algebra ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
    (H : VarpiDivModule p O S) (n : ℕ) :
    H.HasOHeight n ↔ H.G.height = n * Module.finrank ℤ_[p] O :=
  ⟨fun h => h.2.2, fun h => ⟨inferInstance, inferInstance, h⟩⟩

theorem padicAction_onLie [Algebra ℤ_[p] S] (G : PDivGroup p S) (a : ℤ_[p]) (x : G.Lie) :
    (PDivGroup.padicAction G).onLie a x = algebraMap ℤ_[p] S a • x := by
  rw [PDivGroup.Action.onLie_apply, PDivGroup.padicAction, Algebra.algebraMap_eq_smul_one,
    PDivGroup.lieMap_smul (algebraMap ℤ_[p] S)]
  simp

variable (p) in

def ofPDiv [Algebra ℤ_[p] S] (G : PDivGroup p S) (h : IsNilpotent (p : S)) :
    VarpiDivModule p ℤ_[p] S :=
  ⟨G, G.padicAction, h, padicAction_onLie G⟩

@[simp] theorem ofPDiv_G [Algebra ℤ_[p] S] (G : PDivGroup p S) (h : IsNilpotent (p : S)) :
    (ofPDiv p G h).G = G := rfl

theorem ofPDiv_hasOHeight [Algebra ℤ_[p] S] (G : PDivGroup p S) (h : IsNilpotent (p : S)) :
    (ofPDiv p G h).HasOHeight G.height :=
  ⟨inferInstance, inferInstance, by rw [Module.finrank_self, mul_one]; rfl⟩

variable (p) in

abbrev ResRing : Type := ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}

theorem natCast_resRing : ((p : ℕ) : ResRing p) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p])}))]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

variable (p) in

def muMod : VarpiDivModule p ℤ_[p] (ResRing p) :=
  ofPDiv p (PDivGroup.mu p (ResRing p)) ⟨1, by rw [pow_one, natCast_resRing]⟩

theorem muMod_hasOHeight : (muMod p).HasOHeight 1 := ofPDiv_hasOHeight _ _

example : ¬ (muMod p).HasOHeight 0 := fun h => by
  exact one_ne_zero (h.2.2.trans (zero_mul _))

end VarpiDivModule

end Modules

section Bset

variable {R : Type} [CommRing R] {n : ℕ} [NeZero n]

def unifDiag (ϖ : R) : Matrix (Fin n) (Fin n) R := diagonal (Function.update 1 0 ϖ)

def coUnifDiag (ϖ : R) : Matrix (Fin n) (Fin n) R := diagonal (Function.update (fun _ => ϖ) 0 1)

theorem unifDiag_apply (ϖ : R) (i j : Fin n) :
    unifDiag ϖ i j = if i = j then (if i = 0 then ϖ else 1) else 0 := by
  by_cases h : i = j
  · subst h; by_cases h0 : i = 0 <;> simp [unifDiag, h0]
  · simp [unifDiag, h]

theorem unifDiag_mul_coUnifDiag (ϖ : R) :
    (unifDiag ϖ : Matrix (Fin n) (Fin n) R) * coUnifDiag ϖ = ϖ • 1 := by
  rw [unifDiag, coUnifDiag, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : i = 0 <;> simp [diagonal, h]
  · simp [diagonal, hij]

theorem coUnifDiag_mul_unifDiag (ϖ : R) :
    (coUnifDiag ϖ : Matrix (Fin n) (Fin n) R) * unifDiag ϖ = ϖ • 1 := by
  rw [unifDiag, coUnifDiag, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : i = 0 <;> simp [diagonal, h]
  · simp [diagonal, hij]

variable (n) in

def BsetInt (ϖ : R) : Set (Matrix (Fin n) (Fin n) R) :=
  {β | ∃ k₁ k₂ : GL (Fin n) R, β = k₁.val * unifDiag ϖ * k₂.val}

variable (n) in

def Bset (K : Type) [Field K] [Algebra R K] (ϖ : R) : Set (GL (Fin n) K) :=
  {g | ∃ β ∈ BsetInt n ϖ, g.val = β.map (algebraMap R K)}

theorem unifDiag_mem (ϖ : R) : unifDiag ϖ ∈ BsetInt n ϖ := ⟨1, 1, by simp⟩

theorem exists_mul_eq_smul {ϖ : R} {β : Matrix (Fin n) (Fin n) R} (hβ : β ∈ BsetInt n ϖ) :
    ∃ γ : Matrix (Fin n) (Fin n) R, β * γ = ϖ • 1 ∧ γ * β = ϖ • 1 := by
  obtain ⟨k₁, k₂, rfl⟩ := hβ
  refine ⟨(k₂⁻¹).val * coUnifDiag ϖ * (k₁⁻¹).val, ?_, ?_⟩
  · calc k₁.val * unifDiag ϖ * k₂.val * ((k₂⁻¹).val * coUnifDiag ϖ * (k₁⁻¹).val)
        = k₁.val * (unifDiag ϖ * ((k₂.val * (k₂⁻¹).val) * coUnifDiag ϖ)) * (k₁⁻¹).val := by
          simp only [Matrix.mul_assoc]
      _ = ϖ • 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
            unifDiag_mul_coUnifDiag, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
            ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · calc (k₂⁻¹).val * coUnifDiag ϖ * (k₁⁻¹).val * (k₁.val * unifDiag ϖ * k₂.val)
        = (k₂⁻¹).val * (coUnifDiag ϖ * (((k₁⁻¹).val * k₁.val) * unifDiag ϖ)) * k₂.val := by
          simp only [Matrix.mul_assoc]
      _ = ϖ • 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
            coUnifDiag_mul_unifDiag, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
            ← Units.val_mul, inv_mul_cancel, Units.val_one]

def sigmaGL (σ : R ≃+* R) : GL (Fin n) R →* GL (Fin n) R :=
  GeneralLinearGroup.map (σ : R →+* R)

@[simp] theorem sigmaGL_val (σ : R ≃+* R) (g : GL (Fin n) R) :
    (sigmaGL σ g).val = (g.val).map σ := rfl

def sigmaConj (σ : R ≃+* R) (g : GL (Fin n) R) (β : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  g.val * β * (sigmaGL σ g⁻¹).val

@[simp] theorem sigmaConj_one (σ : R ≃+* R) (β : Matrix (Fin n) (Fin n) R) :
    sigmaConj σ 1 β = β := by
  simp only [sigmaConj, inv_one, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]

theorem sigmaConj_mul (σ : R ≃+* R) (g h : GL (Fin n) R) (β : Matrix (Fin n) (Fin n) R) :
    sigmaConj σ (g * h) β = sigmaConj σ g (sigmaConj σ h β) := by
  simp only [sigmaConj, _root_.mul_inv_rev, map_mul, Units.val_mul, Matrix.mul_assoc]

theorem sigmaConj_mem (σ : R ≃+* R) (g : GL (Fin n) R) {ϖ : R} {β : Matrix (Fin n) (Fin n) R}
    (hβ : β ∈ BsetInt n ϖ) : sigmaConj σ g β ∈ BsetInt n ϖ := by
  obtain ⟨k₁, k₂, rfl⟩ := hβ
  exact ⟨g * k₁, k₂ * sigmaGL σ g⁻¹, by simp only [sigmaConj, Units.val_mul, Matrix.mul_assoc]⟩

variable (n) in

def sigmaSetoid (σ : R ≃+* R) (ϖ : R) : Setoid (BsetInt n ϖ) where
  r β β' := ∃ g : GL (Fin n) R, β'.1 = sigmaConj σ g β.1
  iseqv := ⟨fun β => ⟨1, (sigmaConj_one σ β.1).symm⟩,
    fun {β β'} ⟨g, h⟩ => ⟨g⁻¹, by rw [h, ← sigmaConj_mul, inv_mul_cancel, sigmaConj_one]⟩,
    fun {β β' β''} ⟨g, h⟩ ⟨g', h'⟩ => ⟨g' * g, by rw [h', h, sigmaConj_mul]⟩⟩

variable (n) in

def BsetClasses (σ : R ≃+* R) (ϖ : R) : Type := Quotient (sigmaSetoid n σ ϖ)

end Bset

section Dieudonne

variable (R : Type) [CommRing R]

structure RelDieudonne (σ : R ≃+* R) (ϖ : R) : Type 1 where

  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  [free : Module.Free R M]
  [finite : Module.Finite R M]

  F : M →ₛₗ[(σ : R →+* R)] M

  V : M →ₛₗ[(σ.symm : R →+* R)] M

  F_V : ∀ x, F (V x) = ϖ • x

  V_F : ∀ x, V (F x) = ϖ • x

attribute [instance] RelDieudonne.addCommGroup RelDieudonne.module RelDieudonne.free
  RelDieudonne.finite

variable {R}

namespace RelDieudonne

variable {σ : R ≃+* R} {ϖ : R}

structure Iso (D D' : RelDieudonne R σ ϖ) : Type where

  e : D.M ≃ₗ[R] D'.M

  F_comm : ∀ x, e (D.F x) = D'.F (e x)

  V_comm : ∀ x, e (D.V x) = D'.V (e x)

def Iso.refl (D : RelDieudonne R σ ϖ) : Iso D D :=
  ⟨LinearEquiv.refl R D.M, fun _ => rfl, fun _ => rfl⟩

def Iso.symm {D D' : RelDieudonne R σ ϖ} (i : Iso D D') : Iso D' D :=
  ⟨i.e.symm, fun x => i.e.injective (by rw [i.F_comm, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]), fun x => i.e.injective (by rw [i.V_comm,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])⟩

def Iso.trans {D D' D'' : RelDieudonne R σ ϖ} (i : Iso D D') (j : Iso D' D'') : Iso D D'' :=
  ⟨i.e.trans j.e, fun x => by simp [i.F_comm, j.F_comm], fun x => by simp [i.V_comm, j.V_comm]⟩

end RelDieudonne

variable {n : ℕ}

def dieuF (σ : R ≃+* R) (β : Matrix (Fin n) (Fin n) R) :
    (Fin n → R) →ₛₗ[(σ : R →+* R)] (Fin n → R) where
  toFun x := β *ᵥ fun i => σ (x i)
  map_add' x y := by
    rw [← mulVec_add]
    congr 1
    funext i
    simp
  map_smul' c x := by
    rw [← mulVec_smul]
    congr 1
    funext i
    simp

def dieuV (σ : R ≃+* R) (γ : Matrix (Fin n) (Fin n) R) :
    (Fin n → R) →ₛₗ[(σ.symm : R →+* R)] (Fin n → R) where
  toFun y i := σ.symm ((γ *ᵥ y) i)
  map_add' x y := by
    funext i
    simp [mulVec_add]
  map_smul' c x := by
    funext i
    simp [mulVec_smul]

@[simp] theorem dieuF_apply (σ : R ≃+* R) (β : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    dieuF σ β x = β *ᵥ fun i => σ (x i) := rfl

@[simp] theorem dieuV_apply (σ : R ≃+* R) (γ : Matrix (Fin n) (Fin n) R) (y : Fin n → R)
    (i : Fin n) : dieuV σ γ y i = σ.symm ((γ *ᵥ y) i) := rfl

variable [NeZero n]

def coMat {ϖ : R} (β : BsetInt n ϖ) : Matrix (Fin n) (Fin n) R :=
  (exists_mul_eq_smul β.2).choose

theorem mul_coMat {ϖ : R} (β : BsetInt n ϖ) : β.1 * coMat β = ϖ • 1 :=
  (exists_mul_eq_smul β.2).choose_spec.1

theorem coMat_mul {ϖ : R} (β : BsetInt n ϖ) : coMat β * β.1 = ϖ • 1 :=
  (exists_mul_eq_smul β.2).choose_spec.2

def dieu (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (β : BsetInt n ϖ) : RelDieudonne R σ ϖ where
  M := Fin n → R
  F := dieuF σ β.1
  V := dieuV σ (coMat β)
  F_V y := by
    have h1 : (fun i => σ (dieuV σ (coMat β) y i)) = coMat β *ᵥ y := by
      funext i; rw [dieuV_apply, RingEquiv.apply_symm_apply]
    rw [dieuF_apply, h1, mulVec_mulVec, mul_coMat, smul_mulVec, one_mulVec]
  V_F x := by
    funext i
    rw [dieuV_apply, dieuF_apply, mulVec_mulVec, coMat_mul, smul_mulVec, one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    rw [show σ.symm ϖ = ϖ from σ.symm_apply_eq.2 hϖ.symm]

@[simp] theorem dieu_F (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (β : BsetInt n ϖ)
    (x : Fin n → R) : (dieu σ hϖ β).F x = β.1 *ᵥ fun i => σ (x i) := rfl

theorem finrank_dieu [Nontrivial R] (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (β : BsetInt n ϖ) :
    Module.finrank R (dieu σ hϖ β).M = n :=
  Module.finrank_fin_fun R

theorem dieu_unifDiag_F_zero (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) :
    (dieu σ hϖ ⟨unifDiag ϖ, unifDiag_mem ϖ⟩).F (Pi.single (0 : Fin n) (1 : R)) = ϖ • Pi.single (0 : Fin n) (1 : R) := by
  funext k
  change _ = ϖ * (Pi.single (0 : Fin n) (1 : R) : Fin n → R) k
  rw [dieu_F]
  simp only [mulVec, dotProduct, unifDiag_apply]
  by_cases hk : k = 0
  · subst hk; simp [Pi.single_apply]
  · simp [Pi.single_apply, hk]

theorem dieu_unifDiag_F_ne (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) {i : Fin n} (hi : i ≠ 0) :
    (dieu σ hϖ ⟨unifDiag ϖ, unifDiag_mem ϖ⟩).F (Pi.single i (1 : R)) = Pi.single i (1 : R) := by
  funext k
  rw [dieu_F]
  simp only [mulVec, dotProduct, unifDiag_apply]
  by_cases hk : k = i
  · subst hk; simp [Pi.single_apply, hi]
  · simp [Pi.single_apply, hk]

theorem dieu_unifDiag_not_surjective (σ : R ≃+* R) {ϖ : R} (hϖ : σ ϖ = ϖ) (hu : ¬ IsUnit ϖ) :
    ¬ Function.Surjective (dieu σ hϖ ⟨unifDiag (n := n) ϖ, unifDiag_mem ϖ⟩).F := by
  intro h
  obtain ⟨x, hx⟩ := h (Pi.single (0 : Fin n) (1 : R))
  have h0 := congrFun hx 0
  change (unifDiag ϖ *ᵥ fun i => σ (x i)) 0 = (Pi.single (0 : Fin n) (1 : R) : Fin n → R) 0 at h0
  simp only [mulVec, dotProduct, unifDiag_apply] at h0
  simp at h0
  exact hu (isUnit_iff_exists_inv.2 ⟨_, h0⟩)

end Dieudonne

section Example

variable (p : ℕ) [Fact p.Prime]

example : ¬ Function.Surjective (dieu (RingEquiv.refl ℤ_[p]) (ϖ := (p : ℤ_[p])) rfl
    ⟨unifDiag (n := 2) (p : ℤ_[p]), unifDiag_mem _⟩).F :=
  dieu_unifDiag_not_surjective _ _
    fun h => by
      have h1 := PadicInt.isUnit_iff.1 h
      rw [PadicInt.norm_p, inv_eq_one, Nat.cast_eq_one] at h1
      exact (Fact.out : p.Prime).one_lt.ne' h1

example : Module.finrank ℤ_[p] (dieu (RingEquiv.refl ℤ_[p]) (ϖ := (p : ℤ_[p])) rfl
    ⟨unifDiag (n := 3) (p : ℤ_[p]), unifDiag_mem _⟩).M = 3 := finrank_dieu _ _ _

end Example

section Conj

variable {R : Type} [CommRing R] {σ : R ≃+* R} {ϖ : R}

theorem RelDieudonne.V_comm_of_F_comm {D D' : RelDieudonne R σ ϖ} (e : D.M ≃ₗ[R] D'.M)
    (hF : ∀ x, e (D.F x) = D'.F (e x)) (hreg : ∀ y : D'.M, ϖ • y = 0 → y = 0) (x : D.M) :
    e (D.V x) = D'.V (e x) := by
  have hinj : ∀ y z : D'.M, D'.F y = D'.F z → y = z := fun y z h => by
    have h1 := congrArg D'.V h
    rw [D'.V_F, D'.V_F, ← sub_eq_zero, ← smul_sub] at h1
    exact sub_eq_zero.1 (hreg _ h1)
  apply hinj
  rw [← hF, D.F_V, D'.F_V, map_smul]

variable {n : ℕ}

def glEquiv (g : GL (Fin n) R) : (Fin n → R) ≃ₗ[R] (Fin n → R) where
  toFun x := g.val *ᵥ x
  invFun y := (g⁻¹).val *ᵥ y
  map_add' x y := mulVec_add _ _ _
  map_smul' c x := mulVec_smul _ _ _
  left_inv x := by
    change (g⁻¹).val *ᵥ (g.val *ᵥ x) = x
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  right_inv y := by
    change g.val *ᵥ ((g⁻¹).val *ᵥ y) = y
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

@[simp] theorem glEquiv_apply (g : GL (Fin n) R) (x : Fin n → R) : glEquiv g x = g.val *ᵥ x := rfl

theorem sigma_mulVec (σ : R ≃+* R) (g : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    (fun i => σ ((g *ᵥ x) i)) = g.map σ *ᵥ fun i => σ (x i) := by
  funext i
  exact RingHom.map_mulVec (σ : R →+* R) g x i

variable [NeZero n]

def dieuIsoOfConj (hϖ : σ ϖ = ϖ) (hreg : ϖ ∈ nonZeroDivisors R) (β β' : BsetInt n ϖ)
    (g : GL (Fin n) R) (h : β'.1 = sigmaConj σ g β.1) :
    RelDieudonne.Iso (dieu σ hϖ β) (dieu σ hϖ β') :=
  have hF : ∀ x : Fin n → R, glEquiv g ((dieu σ hϖ β).F x) = (dieu σ hϖ β').F (glEquiv g x) :=
    fun x => by
    change g.val *ᵥ (β.1 *ᵥ fun i => σ (x i)) = β'.1 *ᵥ fun i => σ ((g.val *ᵥ x) i)
    rw [sigma_mulVec, h, sigmaConj, mulVec_mulVec, mulVec_mulVec, sigmaGL_val, Matrix.mul_assoc,
      Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.mul_one]
  ⟨glEquiv g, hF, RelDieudonne.V_comm_of_F_comm (D := dieu σ hϖ β) (D' := dieu σ hϖ β')
    (glEquiv g) hF fun y hy => funext fun i => by
      have : ϖ * y i = 0 := congrFun hy i
      exact (mem_nonZeroDivisors_iff.1 hreg |>.1) _ this⟩

theorem nonempty_iso_of_rel (hϖ : σ ϖ = ϖ) (hreg : ϖ ∈ nonZeroDivisors R) {β β' : BsetInt n ϖ}
    (h : (sigmaSetoid n σ ϖ) β β') : Nonempty (RelDieudonne.Iso (dieu σ hϖ β) (dieu σ hϖ β')) :=
  let ⟨g, hg⟩ := h
  ⟨dieuIsoOfConj hϖ hreg β β' g hg⟩

end Conj

section BsetField

variable {R : Type} [CommRing R] {n : ℕ} [NeZero n]

theorem det_unifDiag (ϖ : R) : (unifDiag ϖ : Matrix (Fin n) (Fin n) R).det = ϖ := by
  rw [unifDiag, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

theorem exists_mem_Bset (K : Type) [Field K] [Algebra R K] (ϖ : R) (h : algebraMap R K ϖ ≠ 0) :
    ∃ g ∈ Bset n K ϖ, g.val = (unifDiag ϖ).map (algebraMap R K) := by
  have hd : ((unifDiag ϖ : Matrix (Fin n) (Fin n) R).map (algebraMap R K)).det ≠ 0 := by
    have h1 : ((unifDiag ϖ : Matrix (Fin n) (Fin n) R).map (algebraMap R K)).det =
        algebraMap R K ϖ := by
      rw [show ((unifDiag ϖ : Matrix (Fin n) (Fin n) R).map (algebraMap R K)) =
        (algebraMap R K).mapMatrix (unifDiag ϖ) from rfl, ← RingHom.map_det, det_unifDiag]
    rw [h1]
    exact h
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, ⟨_, unifDiag_mem ϖ, rfl⟩, rfl⟩

example (p : ℕ) [Fact p.Prime] : ∃ g ∈ Bset 2 ℚ_[p] (p : ℤ_[p]),
    g.val = (unifDiag (p : ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p]) :=
  exists_mem_Bset _ _ (by simp [(Fact.out : p.Prime).ne_zero])

end BsetField

end GlobalTheory.VDiv
