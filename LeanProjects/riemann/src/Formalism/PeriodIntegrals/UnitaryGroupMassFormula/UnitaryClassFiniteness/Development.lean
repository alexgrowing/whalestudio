import Formalism.PeriodIntegrals.UJClassFin

noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def vinc {M : ℕ} (x : Fin M → E) : Fin M → Af F ⊗[F] E := fun i => inclR (Af F) (x i)

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def abelian₂ (L : Set (Fin M → E)) (h : HA (AF F) σ J) : Set (Fin M → E) :=
  {x | (finMat σ J h⁻¹).mulVec (vinc (F := F) x) ∈ latHat F E L}

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem bc_mem (g : GL (Fin M) E) (hg : g ∈ UJ (σ : E →+* E) J) :
    bc (inclR (AF F)) g ∈ HR (AF F) σ J := by
  have hg' : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  have hc : cT (sigR (AF F) σ) ((g : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) =
      (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)).map (inclR (AF F)) := by
    ext i j
    simp [cT, sigR_inclR]
  show cT (sigR (AF F) σ) ((g : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) * J.map (inclR (AF F)) *
    (g : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) = J.map (inclR (AF F))
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']

def emb : UJ (σ : E →+* E) J →* HA (AF F) σ J where
  toFun g := (⟨bc (inclR (AF F)) g.1, bc_mem σ J g.1 g.2⟩ : HR (AF F) σ J)
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

theorem emb_mem (g : UJ (σ : E →+* E) J) : emb σ J g ∈ GamG σ J := by
  have : (show HR (AF F) σ J from emb σ J g).1 ∈ HFin (AF F) σ J := ⟨g.1, g.2, rfl⟩
  exact this

theorem finMat_emb (g : UJ (σ : E →+* E) J) :
    finMat σ J (emb σ J g) = ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (Af F)) := by
  ext i j
  change (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
      ((1 : AF F) ⊗ₜ[F] ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j) =
    (1 : Af F) ⊗ₜ[F] ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j
  simp [Algebra.TensorProduct.map_tmul]

theorem map_mulVec_vinc (A : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (A.map (inclR (Af F))).mulVec (vinc (F := F) x) = vinc (F := F) (A.mulVec x) := by
  ext i
  simp only [vinc]
  rw [RingHom.map_mulVec]
  rfl

theorem Lam_emb_mul (L : Set (Fin M → E)) (g : UJ (σ : E →+* E) J) (h : HA (AF F) σ J) :
    abelian₂ σ J L (emb σ J g * h) =
      (fun x => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec x) '' abelian₂ σ J L h := by
  ext x
  have hinv : (emb σ J g * h)⁻¹ = h⁻¹ * emb σ J g⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
  have h1 : ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *
      (((g⁻¹ : UJ (σ : E →+* E) J) : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have h2 : (((g⁻¹ : UJ (σ : E →+* E) J) : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *
      ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  simp only [abelian₂, Set.mem_ofPred_eq, Set.mem_image, hinv, finMat_mul, ← Matrix.mulVec_mulVec, finMat_emb,
    map_mulVec_vinc]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

def RatDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∀ (h : HA (AF F) σ J) (y : Fin M → Af F ⊗[F] E),
      (finMat σ J h⁻¹).mulVec y ∈ latHat F E L ↔ y ∈ latHat F E (abelian₂ σ J L h)

def ClassFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, HasSignature (J.map τ) M 0) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∃ S : Set (Set (Fin M → E)), S.Finite ∧ ∀ h : HA (AF F) σ J, ∃ s ∈ S, ∃ g : UJ (σ : E →+* E) J,
      abelian₂ σ J L h = (fun x => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec x) '' s

theorem sfin_of_Lam_eq (L : Set (Fin M → E))
    (hR : ∀ (h : HA (AF F) σ J) (y : Fin M → Af F ⊗[F] E),
      (finMat σ J h⁻¹).mulVec y ∈ latHat F E L ↔ y ∈ latHat F E (abelian₂ σ J L h))
    (h h' : HA (AF F) σ J) (he : abelian₂ σ J L h = abelian₂ σ J L h') : h⁻¹ * h' ∈ SFin σ J L := by
  intro y
  rw [finMat_mul, ← Matrix.mulVec_mulVec]
  have e1 : (finMat σ J h'⁻¹).mulVec ((finMat σ J h').mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one, Matrix.one_mulVec]
  rw [hR h, he, ← hR h', e1]

end PI.UnitaryGroupMassFormula.UJClassFin
