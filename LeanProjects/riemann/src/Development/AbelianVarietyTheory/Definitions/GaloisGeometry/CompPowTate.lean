import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AssocSetApplyOfPointwise
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRankOneIdem

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.Ix (D : Datum p) : Type := by
  letI := D.freeLa
  exact Module.Free.ChooseBasisIndex ℤ D.La

instance (D : Datum p) : Fintype D.Ix := by
  letI := D.freeLa
  letI := D.finLa
  unfold Datum.Ix
  infer_instance

instance (D : Datum p) : DecidableEq D.Ix := Classical.decEq _

def Datum.basis (D : Datum p) : Module.Basis D.Ix ℤ D.La := by
  letI := D.freeLa
  exact Module.Free.chooseBasis ℤ D.La

def Datum.matO (D : Datum p) (c : D.O) : Matrix D.Ix D.Ix ℤ :=
  LinearMap.toMatrix D.basis D.basis (DistribMulAction.toLinearMap ℤ D.La c)

def Datum.gramEF (D : Datum p) : Matrix D.Ix D.Ix ℤ := LinearMap.BilinForm.toMatrix D.basis D.EF

def Datum.gPts (D : Datum p) (Λ : Type) [CommRing Λ] : Subgroup (GL D.Ix Λ) where
  carrier := {g | (∀ c : D.O, (g : Matrix D.Ix D.Ix Λ) * (D.matO c).map (Int.castRingHom Λ) =
      (D.matO c).map (Int.castRingHom Λ) * g) ∧
    ∃ ν : Λˣ, (g : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * g = (ν : Λ) • D.gramEF.map (Int.castRingHom Λ)}
  mul_mem' {g h} hg hh := by
    refine ⟨fun c => ?_, ?_⟩
    · rw [Units.val_mul, Matrix.mul_assoc, hh.1 c, ← Matrix.mul_assoc, hg.1 c, Matrix.mul_assoc]
    · obtain ⟨ν, hν⟩ := hg.2
      obtain ⟨ν', hν'⟩ := hh.2
      refine ⟨ν * ν', ?_⟩
      calc ((g * h : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * (g * h : GL D.Ix Λ)
          = (h : Matrix D.Ix D.Ix Λ)ᵀ * ((g : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * g) * h := by
            simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc]
        _ = ((ν * ν' : Λˣ) : Λ) • D.gramEF.map (Int.castRingHom Λ) := by
            rw [hν, Matrix.mul_smul, Matrix.smul_mul, hν', smul_smul, Units.val_mul, mul_comm]
  one_mem' := ⟨fun c => by simp, ⟨1, by simp⟩⟩
  inv_mem' {g} hg := by
    have h1 : ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) * g = 1 := Units.inv_mul g
    have h2 : (g : Matrix D.Ix D.Ix Λ) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) = 1 := Units.mul_inv g
    refine ⟨fun c => ?_, ?_⟩
    · calc ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) * (D.matO c).map (Int.castRingHom Λ)
          = ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) * (D.matO c).map (Int.castRingHom Λ) *
              ((g : Matrix D.Ix D.Ix Λ) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)) := by rw [h2, Matrix.mul_one]
        _ = ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) * ((g : Matrix D.Ix D.Ix Λ) * (D.matO c).map (Int.castRingHom Λ)) *
              ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) := by rw [hg.1 c]; simp only [Matrix.mul_assoc]
        _ = (D.matO c).map (Int.castRingHom Λ) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) := by
            rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    · obtain ⟨ν, hν⟩ := hg.2
      refine ⟨ν⁻¹, ?_⟩
      have e1 : ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)ᵀ * (g : Matrix D.Ix D.Ix Λ)ᵀ = 1 := by
        rw [← transpose_mul, h2, transpose_one]
      have key : ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)ᵀ *
          ((g : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * g) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ) =
          D.gramEF.map (Int.castRingHom Λ) := by
        calc _ = (((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)ᵀ * (g : Matrix D.Ix D.Ix Λ)ᵀ) * D.gramEF.map (Int.castRingHom Λ) *
              ((g : Matrix D.Ix D.Ix Λ) * ((g⁻¹ : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [e1, h2, Matrix.one_mul, Matrix.mul_one]
      rw [hν, Matrix.mul_smul, Matrix.smul_mul] at key
      conv_rhs => rw [← key]
      rw [smul_smul, Units.inv_mul, one_smul]

def Datum.gPtsMap (D : Datum p) {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') : D.gPts Λ →* D.gPts Λ' :=
  ((Units.map (φ.mapMatrix : Matrix D.Ix D.Ix Λ →+* Matrix D.Ix D.Ix Λ').toMonoidHom).comp
    (D.gPts Λ).subtype).codRestrict _ fun g => by
    have hc : ∀ M : Matrix D.Ix D.Ix ℤ, (M.map (Int.castRingHom Λ)).map φ = M.map (Int.castRingHom Λ') := fun M => by
      rw [Matrix.map_map]; congr 1; funext z; simp
    refine ⟨fun c => ?_, ?_⟩
    · have := congrArg (fun A : Matrix D.Ix D.Ix Λ => A.map φ) (g.2.1 c)
      change ((g : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ).map φ * _ = _ * ((g : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ).map φ
      simpa only [Matrix.map_mul, hc] using this
    · obtain ⟨ν, hν⟩ := g.2.2
      refine ⟨Units.map φ.toMonoidHom ν, ?_⟩
      have := congrArg (fun A : Matrix D.Ix D.Ix Λ => A.map φ) hν
      have hs : ∀ (a : Λ) (A : Matrix D.Ix D.Ix Λ), (a • A).map φ = φ a • A.map φ := fun a A => by
        ext i j; simp
      change (((g : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ).map φ)ᵀ * _ * ((g : GL D.Ix Λ) : Matrix D.Ix D.Ix Λ).map φ = _
      simp only [Matrix.map_mul, Matrix.transpose_map, hc, hs] at this
      exact this

theorem Datum.gPts_dot (D : Datum p) {Λ : Type} [CommRing Λ] (g : GL D.Ix Λ) (ν : Λˣ)
    (hg : (g : Matrix D.Ix D.Ix Λ)ᵀ * D.gramEF.map (Int.castRingHom Λ) * g = (ν : Λ) • D.gramEF.map (Int.castRingHom Λ))
    (v w : D.Ix → Λ) :
    ((g : Matrix D.Ix D.Ix Λ) *ᵥ v) ⬝ᵥ (D.gramEF.map (Int.castRingHom Λ) *ᵥ ((g : Matrix D.Ix D.Ix Λ) *ᵥ w)) =
      (ν : Λ) * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom Λ) *ᵥ w)) := by
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose (g : Matrix D.Ix D.Ix Λ) v,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, Matrix.vecMul_smul, smul_dotProduct, smul_eq_mul,
    ← Matrix.dotProduct_mulVec]

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp R}

def Obj.IsTateL (o : Obj b N s) (ℓ : ℕ) [Fact ℓ.Prime] (T : Over S) (ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T ⟶ o.A)) :
    Prop :=
  (∀ m v w, ev m (v + w) = ev m v * ev m w) ∧
  (∀ m (c : D.O) v, ev m ((D.matO c).map (Int.castRingHom ℤ_[ℓ]) *ᵥ v) = ev m v ≫ o.act.act c) ∧
  (∀ m v, ev m ((ℓ : ℤ_[ℓ]) ^ m • v) = 1) ∧
  (∀ m v, ev (m + 1) v ^ ℓ = ev m v) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (j : Over.mk x ⟶ T),
    ∃ χ : ℕ → AddChar ℤ_[ℓ] kˣ, (∀ m a, χ m a = 1 ↔ (ℓ : ℤ_[ℓ]) ^ m ∣ a) ∧ (∀ m a, χ (m + 1) a ^ ℓ = χ m a) ∧
      (∀ m v, j ≫ ev m v = 1 ↔ ∃ w, v = (ℓ : ℤ_[ℓ]) ^ m • w) ∧
      (∀ m (q : Over.mk x ⟶ o.A), q ^ (ℓ ^ m) = 1 ↔ ∃ v, j ≫ ev m v = q) ∧
      ∀ m v w, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) ((ℓ ^ m : ℕ) : ℤ) (j ≫ ev m v) (j ≫ ev m w)
        (unitOn (χ m (2 * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom ℤ_[ℓ]) *ᵥ w)))))

section
variable {T₀ T : Over S} {A : Over S} [GrpObj A]

theorem comp_pow_tate (u : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) : u ≫ x ^ n = (u ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
end

theorem Obj.IsTateL.comp {o : Obj b N s} {ℓ : ℕ} [Fact ℓ.Prime] {T T' : Over S}
    {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T ⟶ o.A)} (h : o.IsTateL ℓ T ev) (u : T' ⟶ T) :
    o.IsTateL ℓ T' (fun m v => u ≫ ev m v) := by
  obtain ⟨hadd, hlin, hkill, htow, hgeo⟩ := h
  refine ⟨fun m v w => by beta_reduce; rw [hadd, MonObj.comp_mul],
    fun m c v => by beta_reduce; rw [hlin, Category.assoc],
    fun m v => by beta_reduce; rw [hkill, MonObj.comp_one],
    fun m v => by beta_reduce; rw [← comp_pow_tate, htow], ?_⟩
  intro k _ _ x j
  obtain ⟨χ, h1, h2, h3, h4, h5⟩ := hgeo k x (j ≫ u)
  exact ⟨χ, h1, h2, fun m v => by beta_reduce; rw [← Category.assoc]; exact h3 m v,
    fun m q => by beta_reduce; simp only [← Category.assoc]; exact h4 m q,
    fun m v w => by beta_reduce; simp only [← Category.assoc]; exact h5 m v w⟩

theorem Obj.IsTateL.smul {o : Obj b N s} {ℓ : ℕ} [Fact ℓ.Prime] {T : Over S}
    {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T ⟶ o.A)} (h : o.IsTateL ℓ T ev) (g : D.gPts ℤ_[ℓ]) :
    o.IsTateL ℓ T (fun m v => ev m (((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v)) := by
  obtain ⟨hadd, hlin, hkill, htow, hgeo⟩ := h
  obtain ⟨hc, ν, hν⟩ := g.2
  set M : Matrix D.Ix D.Ix ℤ_[ℓ] := ((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) with hM
  set Mi : Matrix D.Ix D.Ix ℤ_[ℓ] := (((g : GL D.Ix ℤ_[ℓ])⁻¹ : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) with hMi
  have hMiM : ∀ v, Mi *ᵥ (M *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hMi, hM, Units.inv_mul, Matrix.one_mulVec]
  have hMMi : ∀ v, M *ᵥ (Mi *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hMi, hM, Units.mul_inv, Matrix.one_mulVec]
  refine ⟨fun m v w => by simp only [Matrix.mulVec_add, hadd], fun m c v => ?_,
    fun m v => by simp only [Matrix.mulVec_smul, hkill], fun m v => htow m _, ?_⟩
  · beta_reduce
    rw [Matrix.mulVec_mulVec, hc c, ← Matrix.mulVec_mulVec, hlin]
  intro k _ _ x j
  obtain ⟨χ, h1, h2, h3, h4, h5⟩ := hgeo k x j
  refine ⟨fun m => (χ m).compAddMonoidHom (AddMonoidHom.mulLeft (ν : ℤ_[ℓ])), fun m a => ?_, fun m a => ?_,
    fun m v => ?_, fun m q => ?_, fun m v w => ?_⟩
  · simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_mulLeft, h1, Units.dvd_mul_left]
  · simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_mulLeft, h2]
  · beta_reduce
    rw [h3]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨Mi *ᵥ w, by rw [← hMiM v, hw, Matrix.mulVec_smul]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨M *ᵥ w, Matrix.mulVec_smul _ _ _⟩
  · beta_reduce
    rw [h4]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨Mi *ᵥ v, by beta_reduce; rw [hMMi]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨M *ᵥ v, rfl⟩
  · have := h5 m (M *ᵥ v) (M *ᵥ w)
    rw [D.gPts_dot _ ν hν] at this
    have e : (2 : ℤ_[ℓ]) * ((ν : ℤ_[ℓ]) * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom ℤ_[ℓ]) *ᵥ w))) =
        (ν : ℤ_[ℓ]) * (2 * (v ⬝ᵥ (D.gramEF.map (Int.castRingHom ℤ_[ℓ]) *ᵥ w))) := by ring
    rw [e] at this
    exact this

def Obj.tateLPre (o : Obj b N s) (ℓ : ℕ) [Fact ℓ.Prime] : (Over S)ᵒᵖ ⥤ Type where
  obj T := {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T.unop ⟶ o.A) // o.IsTateL ℓ T.unop ev}
  map u := ↾fun z => ⟨fun m v => u.unop ≫ z.1 m v, z.2.comp u.unop⟩
  map_id T := by
    ext (z : {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T.unop ⟶ o.A) // o.IsTateL ℓ T.unop ev}) : 3
    apply Subtype.ext
    funext m v
    exact Category.id_comp _
  map_comp {T₁ T₂ T₃} u u' := by
    ext (z : {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T₁.unop ⟶ o.A) // o.IsTateL ℓ T₁.unop ev}) : 3
    apply Subtype.ext
    funext m v
    exact Category.assoc _ _ _

def Obj.tateL (o : Obj b N s) (ℓ : ℕ) [Fact ℓ.Prime] : GlobalTheory.Et.Rel.RActPre S (D.gPts ℤ_[ℓ]) where
  P := o.tateLPre ℓ
  act g :=
    { app := fun T => ↾fun z => ⟨fun m v => z.1 m (((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v), z.2.smul g⟩
      naturality := fun _ _ _ => rfl }
  act_one := by
    apply NatTrans.ext
    funext T
    ext (z : {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T.unop ⟶ o.A) // o.IsTateL ℓ T.unop ev}) : 3
    apply Subtype.ext
    funext m v
    change z.1 m (((1 : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v) = z.1 m v
    rw [Units.val_one, Matrix.one_mulVec]
  act_mul g h := by
    apply NatTrans.ext
    funext T
    ext (z : {ev : ℕ → (D.Ix → ℤ_[ℓ]) → (T.unop ⟶ o.A) // o.IsTateL ℓ T.unop ev}) : 3
    apply Subtype.ext
    funext m v
    change z.1 m (((g * h : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v) =
      z.1 m (((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ (((h : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v))
    rw [Units.val_mul, Matrix.mulVec_mulVec]

def Obj.xiSheaf (o : Obj b N s) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p) (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {κ : Type} [Fintype κ] [DecidableEq κ] (ξ : D.gPts ℤ_[ℓ] →ₜ* GL κ E) :
    GlobalTheory.Et.Rel.Shv E S :=
  GlobalTheory.Et.Rel.assoc E (o.tateL ℓ) ξ.toMonoidHom

def Obj.secXiSheaf (o : Obj b N s) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {κ : Type} [Fintype κ] [DecidableEq κ] (ξ : D.gPts ℤ_[ℓ] →ₜ* GL κ E) (T : Over S) :
    GlobalTheory.Et.Rel.Sec (o.xiSheaf ℓ hℓ E ξ) T ≃ₗ[E] GlobalTheory.Et.Rel.assocSet E (o.tateL ℓ) ξ.toMonoidHom T :=
  GlobalTheory.Et.Rel.secAssoc (o.tateL ℓ) ξ.toMonoidHom T

def Datum.stdRep (D : Datum p) (ℓ : ℕ) [Fact ℓ.Prime] : D.gPts ℤ_[ℓ] →ₜ* GL D.Ix ℤ_[ℓ] where
  toMonoidHom := (D.gPts ℤ_[ℓ]).subtype
  continuous_toFun := continuous_subtype_val

def RepFam.xiSheaf (F₀ : RepFam b N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (E : Type) [CommRing E] [TopologicalSpace E]
    [IsTopologicalRing E] {κ : Type} [Fintype κ] [DecidableEq κ] (ξ : D.gPts ℤ_[ℓ] →ₜ* GL κ E) :
    GlobalTheory.Et.Rel.Shv E F₀.X :=
  F₀.univ.xiSheaf ℓ hℓ E ξ

end GlobalTheory.UPel.HT

namespace GlobalTheory.DrinLev.HT

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {w : Ideal (NumberField.RingOfIntegers D.F)} {m : ℕ} {e : D.O}

def LevRep.xiSheaf (M : LevRep b N w m e) (F₀ : RepFam b N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (E : Type) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] {κ : Type} [Fintype κ] [DecidableEq κ]
    (ξ : D.gPts ℤ_[ℓ] →ₜ* GL κ E) : GlobalTheory.Et.Rel.Shv E M.X :=
  (GlobalTheory.Et.Rel.res E (M.forget F₀)).obj (F₀.xiSheaf ℓ hℓ E ξ)

end GlobalTheory.DrinLev.HT

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

def Datum.gPtsZQ (D : Datum p) (ℓ : ℕ) [Fact ℓ.Prime] : D.gPts ℤ_[ℓ] →ₜ* D.gPts ℚ_[ℓ] where
  toMonoidHom := D.gPtsMap (PadicInt.Coe.ringHom : ℤ_[ℓ] →+* ℚ_[ℓ])
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_map continuous_subtype_val
    · exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map continuous_subtype_val

section Examples

variable (D : Datum p) (ℓ : ℕ) [Fact ℓ.Prime]

example : IsTopologicalGroup (D.gPts ℤ_[ℓ]) := inferInstance

example (Λ : Type) [CommRing Λ] : (-1 : GL D.Ix Λ) ∈ D.gPts Λ :=
  ⟨fun c => by simp, ⟨1, by simp⟩⟩

example (g : D.gPts ℤ_[ℓ]) : D.stdRep ℓ g = g := rfl

example (X : Scheme.{0}) (T : Over X) :
    GlobalTheory.Et.Rel.assocSet ℤ_[ℓ] (GlobalTheory.Et.Rel.trivTorsor X (D.gPts ℤ_[ℓ])) (D.stdRep ℓ).toMonoidHom T ≃ₗ[ℤ_[ℓ]]
      C(T.left, D.Ix → ℤ_[ℓ]) :=
  GlobalTheory.Et.Rel.assocTrivEquiv _ (D.stdRep ℓ).continuous T

example {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s)
    (g : D.gPts ℤ_[ℓ]) (T : Over S) (z : (o.tateL ℓ).P.obj (Opposite.op T)) (m : ℕ) (v : D.Ix → ℤ_[ℓ]) :
    (((o.tateL ℓ).act g).app _ z).1 m v = z.1 m (((g : GL D.Ix ℤ_[ℓ]) : Matrix D.Ix D.Ix ℤ_[ℓ]) *ᵥ v) := rfl

end Examples

end GlobalTheory.UPel.HT
