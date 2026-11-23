import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.SAOpenStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FiniteCovolume

open NumberField Matrix MeasureTheory
open scoped ENNReal ComplexOrder TensorProduct

def conjE (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E).toRingEquiv.toRingHom

theorem conjE_apply (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) :
    conjE E x = IsCMField.complexConj E x := rfl

def unitaryOf {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : R →+* R)
    (J : Matrix ι ι R) : Subgroup (GL ι R) where
  carrier := {g | (g : Matrix ι ι R)ᵀ * J * (g : Matrix ι ι R).map σ = J}
  one_mem' := by
    simp [Matrix.map_one _ (map_zero σ) (map_one σ)]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul] at *
    calc _ = (b : Matrix ι ι R)ᵀ * ((a : Matrix ι ι R)ᵀ * J * (a : Matrix ι ι R).map σ) *
          (b : Matrix ι ι R).map σ := by simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((a⁻¹ : GL ι R) : Matrix ι ι R)ᵀ * (a : Matrix ι ι R)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]
    have h2 : (a : Matrix ι ι R).map σ * ((a⁻¹ : GL ι R) : Matrix ι ι R).map σ = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero σ) (map_one σ)]
    calc _ = ((a⁻¹ : GL ι R) : Matrix ι ι R)ᵀ *
          ((a : Matrix ι ι R)ᵀ * J * (a : Matrix ι ι R).map σ) *
          ((a⁻¹ : GL ι R) : Matrix ι ι R).map σ := by rw [ha]
      _ = (((a⁻¹ : GL ι R) : Matrix ι ι R)ᵀ * (a : Matrix ι ι R)ᵀ) * J *
          ((a : Matrix ι ι R).map σ * ((a⁻¹ : GL ι R) : Matrix ι ι R).map σ) := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

structure HermSpace (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) where

  J : Matrix (Fin N) (Fin N) E
  herm : Jᵀ = J.map (conjE E)
  nondeg : IsUnit J.det

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def HermSpace.h (V : HermSpace E N) (x y : Fin N → E) : E :=
  ReciprocityTheory.ChartRestriction.G.SA.hf (conjE E) V.J x y

def unitaryGroup (V : HermSpace E N) : Subgroup (GL (Fin N) E) := unitaryOf (conjE E) V.J

def IsLattice (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤

theorem h_add_left (V : HermSpace E N) (a b x : Fin N → E) :
    V.h (a + b) x = V.h a x + V.h b x := by
  simp [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, add_mul, Finset.sum_add_distrib]

theorem h_smul_left (V : HermSpace E N) (c : E) (a x : Fin N → E) :
    V.h (c • a) x = c * V.h a x := by
  simp [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, Finset.mul_sum, mul_assoc]

def dual (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) :
    Submodule (𝓞 E) (Fin N → E) where
  carrier := {y | ∀ x ∈ L, IsIntegral ℤ (V.h y x)}
  zero_mem' := by
    intro x _
    simpa [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf] using (isIntegral_zero : IsIntegral ℤ (0 : E))
  add_mem' := by
    intro a b ha hb x hx
    rw [h_add_left]
    exact (ha x hx).add (hb x hx)
  smul_mem' := by
    intro c a ha x hx
    rw [← IsScalarTower.algebraMap_smul E c a, h_smul_left]
    exact (show IsIntegral ℤ (algebraMap (𝓞 E) E c) from c.isIntegral_coe).mul (ha x hx)

def IsDIntegral (V : HermSpace E N) (D : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  IsLattice L ∧ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (V.h x y)) ∧
    L.toAddSubgroup.relIndex (dual V L).toAddSubgroup ≤ D

def linO (g : GL (Fin N) E) : (Fin N → E) →ₗ[𝓞 E] (Fin N → E) :=
  (Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) E)).restrictScalars (𝓞 E)

def act (g : GL (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) (Fin N → E) :=
  L.map (linO g)

def actLine (g : GL (Fin N) E) (l : Submodule E (Fin N → E)) : Submodule E (Fin N → E) :=
  l.map (Matrix.mulVecLin (g : Matrix (Fin N) (Fin N) E))

theorem act_mul (g g' : GL (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) :
    act (g * g') L = act g (act g' L) := by
  rw [act, act, act, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro v
  show ((g * g' : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v =
    (g : Matrix (Fin N) (Fin N) E) *ᵥ ((g' : Matrix (Fin N) (Fin N) E) *ᵥ v)
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem act_one (L : Submodule (𝓞 E) (Fin N → E)) : act 1 L = L := by
  have : linO (1 : GL (Fin N) E) = LinearMap.id := by
    ext v i; simp [linO]
  simp [act, this]

def IsIsotropicLine (V : HermSpace E N) (l : Submodule E (Fin N → E)) : Prop :=
  Module.finrank E l = 1 ∧ ∀ x ∈ l, V.h x x = 0

def stab (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) : Subgroup (unitaryGroup V) where
  carrier := {g | act (g : GL (Fin N) E) L = L}
  one_mem' := act_one L
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, act_mul] at *
    rw [hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← act_mul, Subgroup.coe_inv, inv_mul_cancel, act_one]

def fixVec (V : HermSpace E N) (v : Fin N → E) : Subgroup (unitaryGroup V) where
  carrier := {g | ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Units.val_mul] at *
    rw [← Matrix.mulVec_mulVec, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

def lineIndex (L : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → E) : ℕ :=
  (Submodule.span (𝓞 E) {v}).toAddSubgroup.relIndex
    (L ⊓ (Submodule.span E {v}).restrictScalars (𝓞 E)).toAddSubgroup

def placeJ (V : HermSpace E N) (w : InfinitePlace E) : Matrix (Fin N) (Fin N) ℂ :=
  V.J.map w.embedding

def realPoints (V : HermSpace E N) : Subgroup (InfinitePlace E → GL (Fin N) ℂ) :=
  Subgroup.pi Set.univ (fun w => unitaryOf (starRingEnd ℂ) (placeJ V w))

abbrev RealPts (V : HermSpace E N) : Type := ↥(realPoints V)

instance (V : HermSpace E N) : MeasurableSpace (RealPts V) := borel _

instance (V : HermSpace E N) : BorelSpace (RealPts V) := ⟨rfl⟩

theorem map_conj_map_embedding (w : InfinitePlace E) (A : Matrix (Fin N) (Fin N) E) :
    (A.map (conjE E)).map w.embedding = (A.map w.embedding).map (starRingEnd ℂ) := by
  ext i j
  simp [conjE_apply, IsCMField.complexEmbedding_complexConj]

def toReal (V : HermSpace E N) : unitaryGroup V →* realPoints V where
  toFun g := ⟨fun w => Matrix.GeneralLinearGroup.map w.embedding (g : GL (Fin N) E), by
    rw [realPoints, Subgroup.mem_pi]
    intro w _
    have hg : ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)ᵀ * V.J *
        ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (conjE E) = V.J := g.2
    show ((Matrix.GeneralLinearGroup.map w.embedding (g : GL (Fin N) E) : GL (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)ᵀ * placeJ V w *
        ((Matrix.GeneralLinearGroup.map w.embedding (g : GL (Fin N) E) : GL (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ).map (starRingEnd ℂ) = placeJ V w
    have := congrArg (fun A : Matrix (Fin N) (Fin N) E => A.map w.embedding) hg
    simp only [Matrix.map_mul, Matrix.transpose_map, map_conj_map_embedding] at this
    exact this⟩
  map_one' := by
    ext w : 2
    simp
  map_mul' := by
    intro a b
    ext w : 2
    simp

abbrev gammaInf (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) : Subgroup (RealPts V) :=
  (stab V L).map (toReal V)

abbrev gammaVecInf (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → E) :
    Subgroup (RealPts V) :=
  (stab V L ⊓ fixVec V v).map (toReal V)

def HasFiniteCovolume {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (Γ : Subgroup G) : Prop :=
  ∀ μ : Measure G, μ.IsHaarMeasure → ∃ s : Set G, IsFundamentalDomain Γ s μ ∧ μ s < ⊤

def realVec (v : Fin N → E) : InfinitePlace E → Fin N → ℂ := fun w i => w.embedding (v i)

def gAct {V : HermSpace E N} (g : RealPts V) (x : InfinitePlace E → Fin N → ℂ) :
    InfinitePlace E → Fin N → ℂ :=
  fun w => (((g : InfinitePlace E → GL (Fin N) ℂ) w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) *ᵥ x w

structure Majorant (V : HermSpace E N) where

  H : InfinitePlace E → Matrix (Fin N) (Fin N) ℂ
  posDef : ∀ w, (H w).PosDef
  involution : ∀ w, placeJ V w * (H w)⁻¹ * placeJ V w = H w

def Majorant.norm {V : HermSpace E N} (M : Majorant V) (x : InfinitePlace E → Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ w, (ReciprocityTheory.ChartRestriction.G.SA.hf (starRingEnd ℂ) (M.H w) (x w) (x w)).re)

def maxCompact {V : HermSpace E N} (M : Majorant V) : Set (RealPts V) :=
  {k | ∀ x, M.norm (gAct k x) = M.norm x}

def lineStab (V : HermSpace E N) (v : Fin N → E) : Set (RealPts V) :=
  {p | ∀ w, ∃ a : ℂ, gAct p (realVec v) w = a • realVec v w}

def countBelow {V : HermSpace E N} (M : Majorant V) (VV : Set (Fin N → E)) (t : ℝ)
    (g : RealPts V) : ℝ≥0∞ :=
  (({v | v ∈ VV ∧ M.norm (gAct g⁻¹ (realVec v)) < t} : Set (Fin N → E)).encard : ℝ≥0∞)

def belowInd {V : HermSpace E N} (M : Majorant V) (v : Fin N → E) (t : ℝ) (g : RealPts V) :
    ℝ≥0∞ :=
  if M.norm (gAct g⁻¹ (realVec v)) < t then 1 else 0

section Adelic

def AdE (E : Type) [Field E] [NumberField E] [IsCMField E] : Type :=
  AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) ⊗[maximalRealSubfield E] E

instance : CommRing (AdE E) :=
  inferInstanceAs (CommRing (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))

instance : Algebra (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (AdE E) :=
  inferInstanceAs (Algebra _ (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))

instance : TopologicalSpace (AdE E) :=
  moduleTopology (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) (AdE E)

variable (E) in

def conjA : AdE E →+* AdE E :=
  (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E)
    (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)))
    (IsCMField.complexConj E).toAlgHom).toRingHom

variable (E) in

def inclA : E →+* AdE E :=
  (Algebra.TensorProduct.includeRight : E →ₐ[maximalRealSubfield E]
    (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)).toRingHom

theorem conjA_inclA (x : E) : conjA E (inclA E x) = inclA E (conjE E x) := by
  change Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E)
      (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)))
      (IsCMField.complexConj E).toAlgHom
      ((1 : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ x) =
    (1 : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ
      (IsCMField.complexConj E x)
  rw [Algebra.TensorProduct.map_tmul]
  simp

def adelicPoints (V : HermSpace E N) : Subgroup (GL (Fin N) (AdE E)) :=
  unitaryOf (conjA E) (V.J.map (inclA E))

instance (V : HermSpace E N) : MeasurableSpace (adelicPoints V) := borel _

instance (V : HermSpace E N) : BorelSpace (adelicPoints V) := ⟨rfl⟩

def toAdelic (V : HermSpace E N) : unitaryGroup V →* adelicPoints V where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (inclA E) (g : GL (Fin N) E), by
    have hg : ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)ᵀ * V.J *
        ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (conjE E) = V.J := g.2
    show ((Matrix.GeneralLinearGroup.map (inclA E) (g : GL (Fin N) E) : GL (Fin N) (AdE E)) :
        Matrix (Fin N) (Fin N) (AdE E))ᵀ * V.J.map (inclA E) *
        ((Matrix.GeneralLinearGroup.map (inclA E) (g : GL (Fin N) E) : GL (Fin N) (AdE E)) :
        Matrix (Fin N) (Fin N) (AdE E)).map (conjA E) = V.J.map (inclA E)
    have key : (((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (conjE E)).map (inclA E) =
        (((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (inclA E)).map (conjA E) := by
      ext i j; simp [conjA_inclA]
    have := congrArg (fun A : Matrix (Fin N) (Fin N) E => A.map (inclA E)) hg
    simp only [Matrix.map_mul, Matrix.transpose_map, key] at this
    exact this⟩
  map_one' := by ext : 2; simp
  map_mul' := by intro a b; ext : 2; simp

end Adelic

def fDeg (E : Type) [Field E] [NumberField E] [IsCMField E] : ℕ :=
  Module.finrank ℚ (maximalRealSubfield E)

def VolA.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N) (D : ℕ),
    (∃ S : Set (Submodule (𝓞 E) (Fin N → E)), S.Finite ∧
      ∀ L, IsDIntegral V D L →
        ∃ g : unitaryGroup V, ∃ L₀ ∈ S, L = act (g : GL (Fin N) E) L₀) ∧
    (∃ S : Set (Submodule (𝓞 E) (Fin N → E) × Submodule E (Fin N → E)), S.Finite ∧
      ∀ L l, IsDIntegral V D L → IsIsotropicLine V l →
        ∃ g : unitaryGroup V, ∃ p ∈ S,
          L = act (g : GL (Fin N) E) p.1 ∧ l = actLine (g : GL (Fin N) E) p.2)

def VolB.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N) (D : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)), IsDIntegral V D L → HasFiniteCovolume (gammaInf V L)

def VolC.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N),
    HasFiniteCovolume (toAdelic V).range

def VolD.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V) (D : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (VV : Set (Fin N → E)),
    IsDIntegral V D L → VV ⊆ L → (∀ v ∈ VV, v ≠ 0 ∧ V.h v v = 0) →
    (∀ g : unitaryGroup V, g ∈ stab V L → ∀ v ∈ VV,
      ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v ∈ VV) →
    (∃ C : ℕ, ∀ v ∈ VV, lineIndex L v ≤ C) →
    ∀ μ : Measure (RealPts V), μ.IsHaarMeasure →
    ∀ s : Set (RealPts V), IsFundamentalDomain (gammaInf V L) s μ →
    ∀ t : ℝ, (∫⁻ g in s, countBelow M VV t g ∂μ) < ⊤ ∧
      ∀ θ : ℝ, 0 < θ → (∫⁻ g in s, countBelow M VV (θ * t) g ∂μ) =
        ENNReal.ofReal θ ^ (2 * fDeg E * (N - 1)) * ∫⁻ g in s, countBelow M VV t g ∂μ

def Mahler.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V) (D : ℕ) (t : ℝ), 0 < t →
    ∃ S : Set (Submodule (𝓞 E) (Fin N → E)), S.Finite ∧ ∃ C : Set (RealPts V), IsCompact C ∧
      ∀ (L : Submodule (𝓞 E) (Fin N → E)) (g : RealPts V), IsDIntegral V D L →
        (∀ v ∈ L, v ≠ 0 → t ≤ M.norm (gAct g⁻¹ (realVec v))) →
        ∃ γ : unitaryGroup V, ∃ L₀ ∈ S, ∃ c ∈ C,
          L = act (γ : GL (Fin N) E) L₀ ∧ g = toReal V γ * c

def ShortIsotropic.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V) (D : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (g : RealPts V) (v : Fin N → E),
    IsDIntegral V D L → v ∈ L → M.norm (gAct g⁻¹ (realVec v)) < 1 → V.h v v = 0

def ShortIndex.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V) (D : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (g : RealPts V) (vr : ℝ)
    (v : Fin N → E),
    Submodule.span ℚ {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ vr} = ⊤ →
    IsDIntegral V D L → v ∈ L → v ≠ 0 →
    (∀ u ∈ L, u ≠ 0 → M.norm (gAct g⁻¹ (realVec v)) ≤ M.norm (gAct g⁻¹ (realVec u))) →
    (lineIndex L v : ℝ) ≤ (vr * Real.sqrt (2 * fDeg E)) ^ (2 * fDeg E)

def Unfolding.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V) (D : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (v₀ : Fin N → E),
    IsDIntegral V D L → v₀ ∈ L → v₀ ≠ 0 → V.h v₀ v₀ = 0 →
    ∀ μ : Measure (RealPts V), μ.IsHaarMeasure →
    ∀ s : Set (RealPts V), IsFundamentalDomain (gammaVecInf V L v₀) s μ →
      (∫⁻ g in s, belowInd M v₀ 1 g ∂μ) < ⊤ ∧
      ∀ t : ℝ, 0 < t → (∫⁻ g in s, belowInd M v₀ t g ∂μ) =
        ENNReal.ofReal t ^ (2 * fDeg E * (N - 1)) * ∫⁻ g in s, belowInd M v₀ 1 g ∂μ

def ParabolicCompact.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V) (v₀ : Fin N → E), v₀ ≠ 0 → V.h v₀ v₀ = 0 →
    ∀ g : RealPts V, ∃ p ∈ lineStab V v₀, ∃ k ∈ maxCompact M, g = p * k

def MaxCompactCompact.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (M : Majorant V), IsCompact (maxCompact M)

def Unimodular.Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : HermSpace E N)
    (μ : Measure (RealPts V)), μ.IsHaarMeasure → μ.IsMulRightInvariant

theorem isClosed_unitaryOf_complex (J : Matrix (Fin N) (Fin N) ℂ) :
    IsClosed (unitaryOf (starRingEnd ℂ) J : Set (GL (Fin N) ℂ)) := by
  have h1 : Continuous (fun g : GL (Fin N) ℂ => (g : Matrix (Fin N) (Fin N) ℂ)) :=
    Units.continuous_val
  have hc : Continuous (fun g : GL (Fin N) ℂ =>
      (g : Matrix (Fin N) (Fin N) ℂ)ᵀ * J * (g : Matrix (Fin N) (Fin N) ℂ).map (starRingEnd ℂ)) :=
    (h1.matrix_transpose.matrix_mul continuous_const).matrix_mul
      (h1.matrix_map Complex.continuous_conj)
  exact isClosed_eq hc continuous_const

theorem isClosed_realPoints (V : HermSpace E N) :
    IsClosed (realPoints V : Set (InfinitePlace E → GL (Fin N) ℂ)) := by
  rw [realPoints, Subgroup.coe_pi]
  exact isClosed_set_pi (fun w _ => isClosed_unitaryOf_complex _)

instance (V : HermSpace E N) : LocallyCompactSpace (RealPts V) := by
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → ℂ))
  exact (isClosed_realPoints V).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem haar_isHaarMeasure (V : HermSpace E N) :
    (Measure.haar : Measure (RealPts V)).IsHaarMeasure := inferInstance

def hypPlane (E : Type) [Field E] [NumberField E] [IsCMField E] : HermSpace E 2 where
  J := !![0, 1; 1, 0]
  herm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  nondeg := by simp [Matrix.det_fin_two]

def hypMajorant (E : Type) [Field E] [NumberField E] [IsCMField E] : Majorant (hypPlane E) where
  H _ := 1
  posDef _ := Matrix.PosDef.one
  involution w := by
    rw [inv_one, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [placeJ, hypPlane, Matrix.mul_apply, Fin.sum_univ_two]

def stdLattice (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) :
    Submodule (𝓞 E) (Fin N → E) :=
  Submodule.span (𝓞 E) (Set.range fun i : Fin N => (Pi.single i 1 : Fin N → E))

def intCoords (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) :
    Submodule (𝓞 E) (Fin N → E) where
  carrier := {x | ∀ i, IsIntegral ℤ (x i)}
  zero_mem' := fun _ => isIntegral_zero
  add_mem' := fun ha hb i => (ha i).add (hb i)
  smul_mem' := by
    intro c x hx i
    show IsIntegral ℤ ((c • x) i)
    rw [← IsScalarTower.algebraMap_smul E c x, Pi.smul_apply, smul_eq_mul]
    exact (show IsIntegral ℤ (algebraMap (𝓞 E) E c) from c.isIntegral_coe).mul (hx i)

theorem stdLattice_le_intCoords : stdLattice E N ≤ intCoords E N := by
  rw [stdLattice, Submodule.span_le]
  rintro _ ⟨i, rfl⟩ j
  by_cases h : j = i
  · subst h; simpa using (isIntegral_one : IsIntegral ℤ (1 : E))
  · simpa [Pi.single_apply, h] using (isIntegral_zero : IsIntegral ℤ (0 : E))

theorem isLattice_stdLattice : IsLattice (stdLattice E N) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [stdLattice, Submodule.span_span_of_tower]
  rw [show (Set.range fun i : Fin N => (Pi.single i 1 : Fin N → E)) =
      Set.range (Pi.basisFun E (Fin N)) by ext; simp [Pi.basisFun_apply]]
  exact (Pi.basisFun E (Fin N)).span_eq

theorem isIntegral_h_of_coords (V : HermSpace E N) (hJ : ∀ i j, IsIntegral ℤ (V.J i j))
    {x y : Fin N → E} (hx : ∀ i, IsIntegral ℤ (x i)) (hy : ∀ i, IsIntegral ℤ (y i)) :
    IsIntegral ℤ (V.h x y) := by
  unfold HermSpace.h ReciprocityTheory.ChartRestriction.G.SA.hf
  refine IsIntegral.sum _ (fun i _ => IsIntegral.sum _ (fun j _ => ?_))
  refine ((hx i).mul (hJ i j)).mul ?_
  simpa using (hy j).map (conjE E).toIntAlgHom

theorem stdLattice_isDIntegral :
    IsDIntegral (hypPlane E)
      ((stdLattice E 2).toAddSubgroup.relIndex (dual (hypPlane E) (stdLattice E 2)).toAddSubgroup)
      (stdLattice E 2) := by
  refine ⟨isLattice_stdLattice, fun x hx y hy => ?_, le_rfl⟩
  refine isIntegral_h_of_coords _ (fun i j => ?_) (stdLattice_le_intCoords hx)
    (stdLattice_le_intCoords hy)
  fin_cases i <;> fin_cases j <;> simp [hypPlane, isIntegral_zero, isIntegral_one]

def e₀ (E : Type) [Field E] [NumberField E] [IsCMField E] : Fin 2 → E := Pi.single 0 1

theorem e₀_ne_zero : e₀ E ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [e₀] at this

theorem e₀_isotropic : (hypPlane E).h (e₀ E) (e₀ E) = 0 := by
  simp [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, hypPlane, e₀, Fin.sum_univ_two]

theorem e₀_mem : e₀ E ∈ stdLattice E 2 := Submodule.subset_span ⟨0, rfl⟩

theorem isIsotropicLine_e₀ : IsIsotropicLine (hypPlane E) (Submodule.span E {e₀ E}) := by
  refine ⟨finrank_span_singleton e₀_ne_zero, ?_⟩
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  simp [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, hypPlane, e₀, Fin.sum_univ_two]

theorem exists_vr : ∃ vr : ℝ,
    Submodule.span ℚ {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ vr} = ⊤ := by
  classical
  refine ⟨∑ i, ∑ φ : E →+* ℂ, ‖φ (integralBasis E i)‖, eq_top_iff.2 ?_⟩
  rw [← (integralBasis E).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨?_, fun φ => ?_⟩
  · rw [integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  · calc ‖φ (integralBasis E i)‖ ≤ ∑ φ' : E →+* ℂ, ‖φ' (integralBasis E i)‖ :=
          Finset.single_le_sum (f := fun φ' : E →+* ℂ => ‖φ' (integralBasis E i)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun i' => ∑ φ' : E →+* ℂ, ‖φ' (integralBasis E i')‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem hf_mulVec {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : R →+* R)
    (J g : Matrix ι ι R) (x y : ι → R) :
    ReciprocityTheory.ChartRestriction.G.SA.hf σ J (g *ᵥ x) (g *ᵥ y) =
      ReciprocityTheory.ChartRestriction.G.SA.hf σ (gᵀ * J * g.map σ) x y := by
  have key : ∀ (A : Matrix ι ι R) (u v : ι → R),
      ReciprocityTheory.ChartRestriction.G.SA.hf σ A u v = u ⬝ᵥ (A *ᵥ (σ ∘ v)) := by
    intro A u v
    simp [ReciprocityTheory.ChartRestriction.G.SA.hf, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hσ : (σ ∘ (g *ᵥ y)) = g.map σ *ᵥ (σ ∘ y) := by
    ext i
    exact RingHom.map_mulVec σ g y i
  rw [key, key, hσ]
  conv_rhs => rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  rw [Matrix.mulVec_mulVec]

theorem h_unitary (V : HermSpace E N) (g : unitaryGroup V) (x y : Fin N → E) :
    V.h (((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x)
      (((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ y) = V.h x y := by
  rw [HermSpace.h, hf_mulVec]
  have hg : ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)ᵀ * V.J *
      ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (conjE E) = V.J := g.2
  rw [hg]
  rfl

theorem linO_injective (γ : GL (Fin N) E) : Function.Injective (linO γ) := by
  intro a b hab
  have := congrArg (fun u => ((γ⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ u) hab
  simpa [linO, Matrix.mulVec_mulVec] using this

theorem lineIndex_mulVec (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E))
    (g : unitaryGroup V) (hg : g ∈ stab V L) (v : Fin N → E) :
    lineIndex L (((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v) = lineIndex L v := by
  set γ : GL (Fin N) E := (g : GL (Fin N) E)
  have h1 : Submodule.span (𝓞 E) {(γ : Matrix (Fin N) (Fin N) E) *ᵥ v} =
      (Submodule.span (𝓞 E) {v}).map (linO γ) := by
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  have h2 : (Submodule.span E {(γ : Matrix (Fin N) (Fin N) E) *ᵥ v}).restrictScalars (𝓞 E) =
      ((Submodule.span E {v}).restrictScalars (𝓞 E)).map (linO γ) := by
    ext u
    simp only [Submodule.restrictScalars_mem, Submodule.mem_span_singleton, Submodule.mem_map]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a • v, ⟨a, rfl⟩, by simp [linO]⟩
    · rintro ⟨w, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by simp [linO]⟩
  have hL : L.map (linO γ) = L := hg
  have h3 : L ⊓ ((Submodule.span E {v}).restrictScalars (𝓞 E)).map (linO γ) =
      (L ⊓ (Submodule.span E {v}).restrictScalars (𝓞 E)).map (linO γ) := by
    rw [Submodule.map_inf _ (linO_injective γ), hL]
  unfold lineIndex
  rw [h1, h2, h3, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ (linO_injective γ)]

def orbitSet (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → E) :
    Set (Fin N → E) :=
  {u | ∃ g : unitaryGroup V, g ∈ stab V L ∧ u = ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ v}

theorem orbitSet_hyps (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → E)
    (hv : v ∈ L) (hv0 : v ≠ 0) (hvv : V.h v v = 0) :
    v ∈ orbitSet V L v ∧ orbitSet V L v ⊆ L ∧ (∀ u ∈ orbitSet V L v, u ≠ 0 ∧ V.h u u = 0) ∧
    (∀ g : unitaryGroup V, g ∈ stab V L → ∀ u ∈ orbitSet V L v,
      ((g : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ u ∈ orbitSet V L v) ∧
    (∃ C : ℕ, ∀ u ∈ orbitSet V L v, lineIndex L u ≤ C) := by
  refine ⟨⟨1, (stab V L).one_mem, by simp⟩, ?_, ?_, ?_, ⟨lineIndex L v, ?_⟩⟩
  · rintro _ ⟨g, hg, rfl⟩
    have : linO (g : GL (Fin N) E) v ∈ act (g : GL (Fin N) E) L := Submodule.mem_map_of_mem hv
    rwa [show act (g : GL (Fin N) E) L = L from hg] at this
  · rintro _ ⟨g, hg, rfl⟩
    refine ⟨fun h0 => hv0 ?_, by rw [h_unitary, hvv]⟩
    have := congrArg (fun u => (((g : GL (Fin N) E)⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ u) h0
    simpa [Matrix.mulVec_mulVec] using this
  · rintro g hg _ ⟨g', hg', rfl⟩
    exact ⟨g * g', (stab V L).mul_mem hg hg', by simp [Matrix.mulVec_mulVec]⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [lineIndex_mulVec V L g hg]

theorem hyp_example :
    IsDIntegral (hypPlane E)
      ((stdLattice E 2).toAddSubgroup.relIndex (dual (hypPlane E) (stdLattice E 2)).toAddSubgroup)
      (stdLattice E 2) ∧
    e₀ E ∈ stdLattice E 2 ∧ e₀ E ≠ 0 ∧ (hypPlane E).h (e₀ E) (e₀ E) = 0 ∧
    orbitSet (hypPlane E) (stdLattice E 2) (e₀ E) ⊆ stdLattice E 2 ∧
    (∀ u ∈ orbitSet (hypPlane E) (stdLattice E 2) (e₀ E), u ≠ 0 ∧ (hypPlane E).h u u = 0) ∧
    (∀ g : unitaryGroup (hypPlane E), g ∈ stab (hypPlane E) (stdLattice E 2) →
      ∀ u ∈ orbitSet (hypPlane E) (stdLattice E 2) (e₀ E),
        ((g : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) *ᵥ u ∈
          orbitSet (hypPlane E) (stdLattice E 2) (e₀ E)) ∧
    (∃ C : ℕ, ∀ u ∈ orbitSet (hypPlane E) (stdLattice E 2) (e₀ E),
      lineIndex (stdLattice E 2) u ≤ C) := by
  obtain ⟨-, h2, h3, h4, h5⟩ := orbitSet_hyps (hypPlane E) (stdLattice E 2) (e₀ E) e₀_mem
    e₀_ne_zero e₀_isotropic
  exact ⟨stdLattice_isDIntegral, e₀_mem, e₀_ne_zero, e₀_isotropic, h2, h3, h4, h5⟩

instance : IsCMField (CyclotomicField 4 ℚ) := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact @IsCyclotomicExtension.Rat.isCMField (CyclotomicField 4 ℚ) _ _ {4} ⟨4, rfl, by norm_num⟩
    (CyclotomicField.isCyclotomicExtension 4 ℚ)

example : HermSpace (CyclotomicField 4 ℚ) 2 := hypPlane _
example : Majorant (hypPlane (CyclotomicField 4 ℚ)) := hypMajorant _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FiniteCovolume
