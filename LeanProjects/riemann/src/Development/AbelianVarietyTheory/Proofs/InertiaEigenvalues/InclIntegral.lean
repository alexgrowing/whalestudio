import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJumpProof

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BaseCoef

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

abbrev incl {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥LL.1 →ₐ[ℚ_[l]] ↥LL'.1 :=
  IntermediateField.inclusion h

def IsLatBasis {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : Prop :=
  (∀ i, b i ∈ T.L.T) ∧ ∀ x ∈ T.L.T, ∀ i, b.repr x i ∈ OL LL

def matRep {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL.1 :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp T.ρ

def matRepExt {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL'.1 :=
  ((incl h).mapMatrix : Matrix (Fin k) (Fin k) ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin k) (Fin k) ↥LL'.1).toRingHom.toMonoidHom.comp
    (matRep T b)

def intVec (LL' : FinExt l) (k : ℕ) : Submodule ↥(OL LL') (Fin k → ↥LL'.1) where
  carrier := {v | ∀ i, v i ∈ OL LL'}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun c v hv i => by
    rw [Pi.smul_apply, Subalgebra.smul_def]
    exact mul_mem c.2 (hv i)

theorem incl_integral {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {x : ↥LL.1} (hx : x ∈ OL LL) :
    incl h x ∈ OL LL' := by
  have hx' : IsIntegral ℤ_[l] x := hx
  exact hx'.map ((incl h).restrictScalars ℤ_[l])

theorem rep_apply {F : Type} [Field F] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) F) (g : G) (x : Fin k → F) :
    CJ.rep M g x = (M g).mulVec x := rfl

set_option synthInstance.maxHeartbeats 400000

def intVecEquiv (LL' : FinExt l) (k : ℕ) : ↥(intVec LL' k) ≃ₗ[↥(OL LL')] (Fin k → ↥(OL LL')) where
  toFun v := fun i => ⟨(v : Fin k → ↥LL'.1) i, v.2 i⟩
  invFun w := ⟨fun i => (w i : ↥LL'.1), fun i => (w i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem repr_integral {LL : FinExt l} {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ}
    {b : Module.Basis (Fin k) ↥LL.1 T.V} (hb : IsLatBasis T b) (g : G) (i j : Fin k) :
    matRep T b g i j ∈ OL LL := by
  rw [matRep, MonoidHom.comp_apply]
  change LinearMap.toMatrix b b (T.ρ g) i j ∈ OL LL
  rw [LinearMap.toMatrix_apply]
  exact hb.2 _ (T.L.stable g _ (hb.1 j)) i

abbrev extLat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) : LocLat G ℚ_[l] ↥LL'.1 ↥(OL LL') where
  V := Fin k → ↥LL'.1
  ρ := CJ.rep (matRepExt h T b)
  cont x := by
    refine continuous_pi fun i => ?_
    simp only [rep_apply, Matrix.mulVec, dotProduct]
    refine continuous_finset_sum _ fun j _ => Continuous.mul ?_ continuous_const
    have h1 : Continuous fun g => b.coord i (T.ρ g (b j)) :=
      (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp (T.cont (b j))
    have h2 : Continuous (incl h) := continuous_subtype_val.subtype_mk _
    refine (h2.comp h1).congr fun g => ?_
    simp [matRepExt, matRep, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  L :=
    { T := intVec LL' k
      stable := fun g x hx i => by
        simp only [rep_apply, Matrix.mulVec, dotProduct]
        refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ (hx j)
        exact incl_integral h (repr_integral hb g i j)
      fg := by
        haveI : Module.Finite ↥(OL LL') ↥(intVec LL' k) := Module.Finite.equiv (intVecEquiv LL' k).symm
        exact Module.Finite.iff_fg.1 inferInstance
      free := Module.Free.of_equiv (intVecEquiv LL' k).symm
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL'.1 (Fin k)).span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩ j
        rw [Pi.basisFun_apply]
        by_cases hij : i = j
        · subst hij; simp [one_mem]
        · simp [Pi.single_apply, Ne.symm hij, zero_mem] }

theorem hom_integral {LL : FinExt l} {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (i : Fin k₂) (j : Fin k₁) :
    LinearMap.toMatrix b₁ b₂ F.f i j ∈ OL LL := by
  rw [LinearMap.toMatrix_apply]
  exact hb₂.2 _ (F.T_le _ (hb₁.1 j)) i

def extMat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L) :
    Matrix (Fin k₂) (Fin k₁) ↥LL'.1 :=
  (LinearMap.toMatrix b₁ b₂ F.f).map (incl h)

set_option maxHeartbeats 1000000 in
theorem extMat_comm {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L)
    (g : G) : extMat h b₁ b₂ F * matRepExt h T₁ b₁ g = matRepExt h T₂ b₂ g * extMat h b₁ b₂ F := by
  have e1 : matRepExt h T₁ b₁ g = (LinearMap.toMatrix b₁ b₁ (T₁.ρ g)).map (incl h) := rfl
  have e2 : matRepExt h T₂ b₂ g = (LinearMap.toMatrix b₂ b₂ (T₂.ρ g)).map (incl h) := rfl
  have key : LinearMap.toMatrix b₁ b₂ F.f * LinearMap.toMatrix b₁ b₁ (T₁.ρ g) =
      LinearMap.toMatrix b₂ b₂ (T₂.ρ g) * LinearMap.toMatrix b₁ b₂ F.f := by
    have c1 := LinearMap.toMatrix_comp b₁ b₁ b₂ F.f (T₁.ρ g)
    have c2 := LinearMap.toMatrix_comp b₁ b₂ b₂ (T₂.ρ g) F.f
    have hc : F.f ∘ₗ T₁.ρ g = T₂.ρ g ∘ₗ F.f := LinearMap.ext fun y => F.equiv g y
    rw [← c1, ← c2, hc]
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun M => incl h (M i j)) key
  simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simpa only [e1, e2, Matrix.mul_apply, extMat, Matrix.map_apply] using this

def extHom {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) :
    LatHom (extLat h T₁ b₁ hb₁).L (extLat h T₂ b₂ hb₂).L where
  f := Matrix.toLin' (extMat h b₁ b₂ F)
  equiv g x := by
    change (extMat h b₁ b₂ F).mulVec ((matRepExt h T₁ b₁ g).mulVec x) =
      (matRepExt h T₂ b₂ g).mulVec ((extMat h b₁ b₂ F).mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, extMat_comm]
  cont := LinearMap.continuous_on_pi _
  T_le x hx i := by
    change (extMat h b₁ b₂ F).mulVec x i ∈ OL LL'
    simp only [Matrix.mulVec, dotProduct, extMat, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (incl_integral h (hom_integral hb₁ hb₂ F i j)) (hx j)

def mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL') (Sig : Finset (I →* LLˣ)) :
    Finset (I →* LL'ˣ) := by
  classical
  exact Sig.image fun a => (Units.map (f : LL →* LL')).comp a

end GlobalTheory.BaseCoef
