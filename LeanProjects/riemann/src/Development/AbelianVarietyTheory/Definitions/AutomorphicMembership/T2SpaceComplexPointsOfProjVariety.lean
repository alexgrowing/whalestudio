import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.CxPts
open scoped TensorProduct

namespace GlobalTheory.ProjVar

variable {F : Type} [Field F]

def CxExt (σ : F →+* ℂ) (A : Type) [CommRing A] [Algebra F A] : Type :=
  letI := σ.toAlgebra
  ℂ ⊗[F] A

namespace CxExt

variable (σ : F →+* ℂ) {A A' : Type} [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

def Tensor (F : Type) [Field F] [Algebra F ℂ] (A : Type) [CommRing A] [Algebra F A] : Type := ℂ ⊗[F] A

instance {_ : Algebra F ℂ} : CommRing (Tensor F A) := inferInstanceAs (CommRing (ℂ ⊗[F] A))

instance {_ : Algebra F ℂ} : Algebra ℂ (Tensor F A) := inferInstanceAs (Algebra ℂ (ℂ ⊗[F] A))

instance : CommRing (CxExt σ A) :=
  inferInstanceAs (CommRing (@Tensor F _ σ.toAlgebra A _ _))

instance : Algebra ℂ (CxExt σ A) :=
  inferInstanceAs (Algebra ℂ (@Tensor F _ σ.toAlgebra A _ _))

def of : A →+* CxExt σ A :=
  letI := σ.toAlgebra
  (Algebra.TensorProduct.includeRight (R := F) (A := ℂ) (B := A)).toRingHom

theorem of_algebraMap (a : F) : of σ (algebraMap F A a) = algebraMap ℂ (CxExt σ A) (σ a) := by
  letI := σ.toAlgebra
  first
  | exact (Algebra.TensorProduct.includeRight (R := F) (A := ℂ) (B := A)).commutes a
  | (show (1 : ℂ) ⊗ₜ[F] algebraMap F A a = σ a ⊗ₜ[F] (1 : A)
     rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
     rfl)

theorem of_smul (a : F) (x : A) : of σ (a • x) = σ a • of σ x := by
  rw [Algebra.smul_def, map_mul, of_algebraMap, ← Algebra.smul_def]

theorem of_injective : Function.Injective (of σ : A → CxExt σ A) := by
  letI := σ.toAlgebra
  exact Algebra.TensorProduct.includeRight_injective (R := F) (A := ℂ) (B := A) σ.injective

private theorem complex_smul_of_eq (c : ℂ) (a : A) :
    c • of σ a = (letI := σ.toAlgebra; (c ⊗ₜ[F] a : ℂ ⊗[F] A) : CxExt σ A) := by
  letI := σ.toAlgebra
  first
  | (show c • ((1 : ℂ) ⊗ₜ[F] a) = c ⊗ₜ[F] a
     rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  | (show c • ((1 : ℂ) ⊗ₜ[F] a) = c ⊗ₜ[F] a
     simp [TensorProduct.smul_tmul'])

variable {σ} in

@[elab_as_elim] theorem induction {P : CxExt σ A → Prop} (x : CxExt σ A)
    (smul : ∀ (c : ℂ) (a : A), P (c • of σ a)) (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  letI := σ.toAlgebra
  refine TensorProduct.induction_on (R := F) (M := ℂ) (N := A) (motive := P) x ?_ ?_ ?_
  · have h := smul 0 0
    rw [zero_smul] at h
    exact h
  · intro c a
    exact (complex_smul_of_eq σ c a) ▸ smul c a
  · intro x y hx hy
    exact add x y hx hy

variable {σ} in

def lift {B : Type} [CommRing B] [Algebra ℂ B] (φ : A →+* B)
    (h : ∀ a, φ (algebraMap F A a) = algebraMap ℂ B (σ a)) : CxExt σ A →ₐ[ℂ] B :=
  letI := σ.toAlgebra
  letI : Algebra F B := ((algebraMap ℂ B).comp σ).toAlgebra
  haveI : IsScalarTower F ℂ B := .of_algebraMap_eq fun _ => rfl
  Algebra.TensorProduct.lift (Algebra.ofId ℂ B) ({ φ with commutes' := h } : A →ₐ[F] B)
    fun _ _ => Commute.all _ _

variable {σ} in

@[simp] theorem lift_of {B : Type} [CommRing B] [Algebra ℂ B] (φ : A →+* B)
    (h : ∀ a, φ (algebraMap F A a) = algebraMap ℂ B (σ a)) (a : A) : lift φ h (of σ a) = φ a := by
  first
  | (change (Algebra.ofId ℂ B) 1 * φ a = φ a
     rw [map_one, one_mul])
  | (simp only [lift, of]
     erw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul]
     simp)

def map (f : A →ₐ[F] A') : CxExt σ A →ₐ[ℂ] CxExt σ A' :=
  lift ((of σ).comp f.toRingHom) fun a => (congrArg (of σ) (f.commutes a)).trans (of_algebraMap σ a)

@[simp] theorem map_of (f : A →ₐ[F] A') (a : A) : map σ f (of σ a) = of σ (f a) := by
  first
  | exact lift_of _ _ a
  | simp [map, lift_of]

theorem map_injective {f : A →ₐ[F] A'} (hf : Function.Injective f) :
    Function.Injective (map σ f) := by
  letI := σ.toAlgebra
  have hk : ∀ x : CxExt σ A,
      map σ f x = (LinearMap.lTensor ℂ f.toLinearMap : ℂ ⊗[F] A →ₗ[F] ℂ ⊗[F] A') x := by
    intro x
    refine CxExt.induction (P := fun x =>
      map σ f x = (LinearMap.lTensor ℂ f.toLinearMap : ℂ ⊗[F] A →ₗ[F] ℂ ⊗[F] A') x) x
      (fun c a => ?_) (fun x y hx hy => ?_)
    · rw [map_smul, map_of, complex_smul_of_eq, complex_smul_of_eq, LinearMap.lTensor_tmul]
      rfl
    · rw [map_add, hx, hy]
      exact (map_add (LinearMap.lTensor ℂ f.toLinearMap : ℂ ⊗[F] A →ₗ[F] ℂ ⊗[F] A') x y).symm
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) f.toLinearMap hf
  intro x y hxy
  exact hinj (by rw [← hk, ← hk]; exact hxy)

theorem exists_components (f : A →ₐ[F] A') (x : CxExt σ A) :
    ∃ (ι : Type) (s : Finset ι) (e : ι → ℂ) (π : ι → CxExt σ A → A) (π' : ι → CxExt σ A' → A'),
      x = ∑ i ∈ s, e i • of σ (π i x) ∧ (∀ i y, π' i (map σ f y) = f (π i y)) ∧
      ∀ i y a, π' i (y * of σ a) = π' i y * a := by
  letI := σ.toAlgebra
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Basis.ofVectorSpaceIndex F ℂ) F ℂ) := ⟨Module.Basis.ofVectorSpace F ℂ⟩
  refine ⟨Module.Basis.ofVectorSpaceIndex F ℂ, (TensorProduct.equivFinsuppOfBasisLeft (N := A) b x).support,
    fun i => b i, fun i y => TensorProduct.equivFinsuppOfBasisLeft (N := A) b y i,
    fun i y => TensorProduct.equivFinsuppOfBasisLeft (N := A') b y i, ?_, ?_, ?_⟩
  · have h2 : ∀ v : Module.Basis.ofVectorSpaceIndex F ℂ →₀ A,
        (TensorProduct.equivFinsuppOfBasisLeft (N := A) b).symm v = v.sum fun i n => b i ⊗ₜ[F] n := by
      intro v
      exact TensorProduct.equivFinsuppOfBasisLeft_symm_apply b v
    have h3 := LinearEquiv.symm_apply_apply (TensorProduct.equivFinsuppOfBasisLeft (N := A) b) x
    rw [h2, Finsupp.sum] at h3
    simp only [complex_smul_of_eq]
    exact h3.symm
  · intro i y
    refine CxExt.induction (P := fun y => TensorProduct.equivFinsuppOfBasisLeft (N := A') b (map σ f y) i =
      f (TensorProduct.equivFinsuppOfBasisLeft (N := A) b y i)) y (fun c a => ?_) (fun y z hy hz => ?_)
    · rw [map_smul, map_of, complex_smul_of_eq, complex_smul_of_eq, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      first
      | exact (map_smul f _ _).symm
      | simp
    · have e1 : TensorProduct.equivFinsuppOfBasisLeft (N := A') b (map σ f (y + z)) = TensorProduct.equivFinsuppOfBasisLeft (N := A') b (map σ f y) + TensorProduct.equivFinsuppOfBasisLeft (N := A') b (map σ f z) := by
        rw [map_add]
        exact map_add _ _ _
      have e2 : TensorProduct.equivFinsuppOfBasisLeft (N := A) b (y + z) = TensorProduct.equivFinsuppOfBasisLeft (N := A) b y + TensorProduct.equivFinsuppOfBasisLeft (N := A) b z := map_add _ _ _
      rw [e1, e2, Finsupp.add_apply, Finsupp.add_apply, hy, hz, map_add]
  · intro i y a
    refine CxExt.induction (P := fun y => TensorProduct.equivFinsuppOfBasisLeft (N := A') b (y * of σ a : CxExt σ A') i =
      TensorProduct.equivFinsuppOfBasisLeft (N := A') b y i * a) y (fun c a' => ?_) (fun y z hy hz => ?_)
    · rw [smul_mul_assoc, ← map_mul, complex_smul_of_eq, complex_smul_of_eq,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, smul_mul_assoc]
    · have e1 : TensorProduct.equivFinsuppOfBasisLeft (N := A') b ((y + z) * of σ a : CxExt σ A') = TensorProduct.equivFinsuppOfBasisLeft (N := A') b (y * of σ a : CxExt σ A') + TensorProduct.equivFinsuppOfBasisLeft (N := A') b (z * of σ a : CxExt σ A') := by
        rw [add_mul]
        exact map_add _ _ _
      have e2 : TensorProduct.equivFinsuppOfBasisLeft (N := A') b (y + z) = TensorProduct.equivFinsuppOfBasisLeft (N := A') b y + TensorProduct.equivFinsuppOfBasisLeft (N := A') b z := map_add _ _ _
      rw [e1, e2, Finsupp.add_apply, Finsupp.add_apply, hy, hz, add_mul]

end CxExt

namespace Var

variable (Y : Var F) (σ : F →+* ℂ)

abbrev pts : Type := CxPts Y.str σ

instance compactSpace_pts : CompactSpace (Y.pts σ) := CxPts.compactSpace σ Y.isProjOver

instance secondCountable_pts : SecondCountableTopology (Y.pts σ) :=
  CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver

instance t2Space_complexPointsOfProjVariety : T2Space (Y.pts σ) := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver

abbrev an : AnRead Y.str σ Y.dim := AnRead.all Y.str σ Y.dim

abbrev FnC : Type := CxExt σ Y.Fn

def cx : Y.Fn →+* Y.FnC σ := CxExt.of σ

theorem cx_smul (a : F) (f : Y.Fn) : Y.cx σ (a • f) = σ a • Y.cx σ f :=
  CxExt.of_smul σ a f

theorem cx_injective : Function.Injective (Y.cx σ) :=
  CxExt.of_injective σ

instance nontrivial_FnC : Nontrivial (Y.FnC σ) := (Y.cx_injective σ).nontrivial

instance algebraStalk (x : Y.X) : Algebra F (Y.X.presheaf.stalk x) :=
  ((Y.X.presheaf.germ ⊤ x trivial).hom.comp (algX Y.str ⊤)).toAlgebra

def stalkIncl (x : Y.X) : Y.X.presheaf.stalk x →ₐ[F] Y.Fn :=
  { algebraMap (Y.X.presheaf.stalk x) Y.X.functionField with
    commutes' := fun a => algebraMap_germ (U := ⊤) trivial (algX Y.str ⊤ a) }

variable {Y σ}

def base (y : Y.pts σ) : Y.X := y.1 (IsLocalRing.closedPoint ℂ)

theorem mem_ptsIn_iff {y : Y.pts σ} {U : Y.X.Opens} : y ∈ ptsIn Y.str σ U ↔ base y ∈ U :=
  CxPts.mem_ptsIn

def evStalk (y : Y.pts σ) : Y.X.presheaf.stalk (base y) →+* ℂ := (Scheme.stalkClosedPointTo y.1).hom

theorem evStalk_germ {y : Y.pts σ} {U : Y.X.Opens} (h : base y ∈ U) (a : Γ(Y.X, U)) :
    evStalk y (Y.X.presheaf.germ U _ h a) = ev Y.str σ U a y := by
  have hy : ⊤ ≤ y.1 ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem y.1 h).ge
  have e := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y.1 U h)
  refine e.trans ?_
  show _ = valR y.1 U a
  rw [valR, dif_pos hy]
  rfl

theorem evStalk_ne_zero_iff {y : Y.pts σ} (a : Y.X.presheaf.stalk (base y)) :
    evStalk y a ≠ 0 ↔ IsUnit a := by
  haveI : IsLocalHom (evStalk y) := Scheme.isLocalHom_stalkClosedPointTo y.1
  rw [← isUnit_iff_ne_zero]
  exact isUnit_map_iff (evStalk y) a

def germIncl (y : Y.pts σ) : CxExt σ (Y.X.presheaf.stalk (base y)) →ₐ[ℂ] Y.FnC σ :=
  CxExt.map σ (Y.stalkIncl (base y))

def germEv (y : Y.pts σ) : CxExt σ (Y.X.presheaf.stalk (base y)) →ₐ[ℂ] ℂ :=
  CxExt.lift (evStalk y) fun a => (evStalk_germ (U := ⊤) trivial _).trans (ev_algX mem_ptsIn_top a)

theorem germIncl_injective (y : Y.pts σ) : Function.Injective (germIncl y) :=
  CxExt.map_injective σ (IsFractionRing.injective (Y.X.presheaf.stalk (base y)) Y.X.functionField)

def HasVal (y : Y.pts σ) (f : Y.FnC σ) (c : ℂ) : Prop :=
  ∃ a b, germEv y b ≠ 0 ∧ germIncl y b * f = germIncl y a ∧ germEv y a = germEv y b * c

def RegC (y : Y.pts σ) (f : Y.FnC σ) : Prop := ∃ c, HasVal y f c

open Classical in

def val (y : Y.pts σ) (f : Y.FnC σ) : ℂ := if h : RegC y f then h.choose else 0

variable {y : Y.pts σ} {f f' : Y.FnC σ} {c c' : ℂ}

theorem HasVal.unique (h : HasVal y f c) (h' : HasVal y f c') : c = c' := by
  obtain ⟨a, b, hb, hf, ha⟩ := h
  obtain ⟨a', b', hb', hf', ha'⟩ := h'
  have key : germIncl y (b * a') = germIncl y (b' * a) := by
    simp only [map_mul]
    linear_combination (germIncl y b') * hf - (germIncl y b) * hf'
  have e := congrArg (germEv y) (germIncl_injective y key)
  simp only [map_mul] at e
  rw [ha, ha'] at e
  apply mul_left_cancel₀ (mul_ne_zero hb hb')
  linear_combination -e

theorem HasVal.regC (h : HasVal y f c) : RegC y f := ⟨c, h⟩

theorem RegC.hasVal (h : RegC y f) : HasVal y f (val y f) := by
  rw [val, dif_pos h]
  exact h.choose_spec

theorem HasVal.val_eq (h : HasVal y f c) : val y f = c := h.regC.hasVal.unique h

theorem val_of_not_regC (h : ¬ RegC y f) : val y f = 0 := by
  rw [val, dif_neg h]

theorem regC_of_val_ne_zero (h : val y f ≠ 0) : RegC y f := by
  by_contra h'
  exact h (val_of_not_regC h')

theorem hasVal_germIncl (a) : HasVal y (germIncl y a) (germEv y a) := ⟨a, 1, by simp, by simp, by simp⟩

theorem hasVal_algebraMap (c : ℂ) : HasVal y (algebraMap ℂ _ c) c := ⟨algebraMap ℂ _ c, 1, by simp, by simp, by simp⟩

theorem hasVal_one : HasVal y 1 1 := ⟨1, 1, by simp, by simp, by simp⟩

theorem hasVal_zero : HasVal y 0 0 := ⟨0, 1, by simp, by simp, by simp⟩

theorem HasVal.add (h : HasVal y f c) (h' : HasVal y f' c') : HasVal y (f + f') (c + c') := by
  obtain ⟨a, b, hb, hf, ha⟩ := h
  obtain ⟨a', b', hb', hf', ha'⟩ := h'
  refine ⟨a * b' + a' * b, b * b', by rw [map_mul]; exact mul_ne_zero hb hb', ?_, ?_⟩
  · simp only [map_mul, map_add]
    linear_combination (germIncl y b') * hf + (germIncl y b) * hf'
  · simp only [map_mul, map_add]
    linear_combination (germEv y b') * ha + (germEv y b) * ha'

theorem HasVal.mul (h : HasVal y f c) (h' : HasVal y f' c') : HasVal y (f * f') (c * c') := by
  obtain ⟨a, b, hb, hf, ha⟩ := h
  obtain ⟨a', b', hb', hf', ha'⟩ := h'
  refine ⟨a * a', b * b', by rw [map_mul]; exact mul_ne_zero hb hb', ?_, ?_⟩
  · simp only [map_mul]
    linear_combination (germIncl y b' * f') * hf + (germIncl y a) * hf'
  · simp only [map_mul]
    linear_combination (germEv y a') * ha + (germEv y b * c) * ha'

theorem HasVal.smul (a : ℂ) (h : HasVal y f c) : HasVal y (a • f) (a * c) := by
  rw [Algebra.smul_def]
  exact (hasVal_algebraMap (y := y) a).mul h

theorem HasVal.neg (h : HasVal y f c) : HasVal y (-f) (-c) := by
  have e := h.smul (-1)
  rwa [neg_one_smul, neg_one_mul] at e

theorem HasVal.sub (h : HasVal y f c) (h' : HasVal y f' c') : HasVal y (f - f') (c - c') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h.add h'.neg

theorem HasVal.pow (h : HasVal y f c) (n : ℕ) : HasVal y (f ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact hasVal_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem HasVal.sum {ι : Type*} {s : Finset ι} {f : ι → Y.FnC σ} {c : ι → ℂ}
    (h : ∀ i ∈ s, HasVal y (f i) (c i)) : HasVal y (∑ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact hasVal_zero
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i t)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem HasVal.of_mul {u : Y.FnC σ} {d : ℂ} (hu : HasVal y u d) (hd : d ≠ 0)
    (h : HasVal y (u * f) c) : HasVal y f (c / d) := by
  obtain ⟨p, q, hq, hu1, hp⟩ := hu
  obtain ⟨a, b, hb, h1, ha⟩ := h
  refine ⟨a * q, b * p, ?_, ?_, ?_⟩
  · rw [map_mul, hp]
    exact mul_ne_zero hb (mul_ne_zero hq hd)
  · simp only [map_mul]
    linear_combination (germIncl y q) * h1 - (germIncl y b * f) * hu1
  · simp only [map_mul]
    rw [hp, ha, div_eq_mul_inv]
    linear_combination (germEv y b * germEv y q * c) * (mul_inv_cancel₀ hd).symm

theorem regC_mul_iff {u : Y.FnC σ} (hu : val y u ≠ 0) : RegC y (u * f) ↔ RegC y f := by
  have hU : HasVal y u (val y u) := (regC_of_val_ne_zero hu).hasVal
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c / val y u, hU.of_mul hu h⟩
  · rintro ⟨c, h⟩
    exact ⟨val y u * c, hU.mul h⟩

theorem val_mul (h : RegC y f) (h' : RegC y f') : val y (f * f') = val y f * val y f' := (h.hasVal.mul h'.hasVal).val_eq

theorem val_unit_mul {u : Y.FnC σ} (hu : val y u ≠ 0) (f : Y.FnC σ) :
    val y (u * f) = val y u * val y f := by
  by_cases hf : RegC y f
  · exact val_mul (regC_of_val_ne_zero hu) hf
  · rw [val_of_not_regC hf, mul_zero]
    exact val_of_not_regC fun h => hf ((regC_mul_iff hu).1 h)

theorem hasVal_cx_stalk (a : Y.X.presheaf.stalk (base y)) :
    HasVal y (Y.cx σ (algebraMap _ Y.X.functionField a)) (evStalk y a) := by
  have h := hasVal_germIncl (y := y) (CxExt.of σ a)
  simp only [germIncl, germEv, CxExt.map_of, CxExt.lift_of] at h
  exact h

theorem hasVal_cx_fnOf {U : Y.X.Opens} (h : base y ∈ U) (h' : genericPoint Y.X ∈ U)
    (a : Γ(Y.X, U)) : HasVal y (Y.cx σ (fnOf U h' a)) (ev Y.str σ U a y) := by
  have h₁ := hasVal_cx_stalk (y := y) (Y.X.presheaf.germ U _ h a)
  rw [algebraMap_germ, evStalk_germ h] at h₁
  exact h₁

theorem val_cx_fnOf {U : Y.X.Opens} (h : base y ∈ U) (h' : genericPoint Y.X ∈ U)
    (a : Γ(Y.X, U)) : val y (Y.cx σ (fnOf U h' a)) = ev Y.str σ U a y :=
  (hasVal_cx_fnOf h h' a).val_eq

theorem regC_cx_iff {g : Y.Fn} : RegC y (Y.cx σ g) ↔ RegAt (base y) g := by
  constructor
  · rintro ⟨c, a, b, hb, hab, -⟩
    obtain ⟨ι, s, e, p, p', hx, h₁, h₂⟩ := CxExt.exists_components σ (Y.stalkIncl (base y)) b
    have e₁ : ∀ t, Y.stalkIncl (base y) t = algebraMap _ Y.Fn t := fun _ => rfl
    have key : ∀ i, algebraMap _ Y.Fn (p i b) * g = algebraMap _ Y.Fn (p i a) := by
      intro i
      have hi := congrArg (p' i) hab
      simp only [germIncl, Var.cx] at hi
      rw [h₂, h₁, h₁, e₁, e₁] at hi
      exact hi
    by_contra hg
    apply hb
    have hz : ∀ i, evStalk y (p i b) = 0 := by
      intro i
      by_contra hne
      obtain ⟨u, hu⟩ := (evStalk_ne_zero_iff (p i b)).1 hne
      apply hg
      refine ⟨(↑u⁻¹ : Y.X.presheaf.stalk (base y)) * p i a, ?_⟩
      have hk := key i
      rw [← hu] at hk
      rw [map_mul, ← hk, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    rw [hx, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul]
    simp only [germEv, CxExt.lift_of]
    rw [hz i, smul_zero]
  · rintro ⟨a, rfl⟩
    exact (hasVal_cx_stalk (y := y) a).regC

theorem val_cx_ne_zero_iff {g : Y.Fn} : val y (Y.cx σ g) ≠ 0 ↔ UnitAt (base y) g := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := (regC_cx_iff (y := y)).1 (regC_of_val_ne_zero h)
    rw [(hasVal_cx_stalk (y := y) a).val_eq] at h
    exact ⟨a, (evStalk_ne_zero_iff a).1 h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rw [(hasVal_cx_stalk (y := y) a).val_eq]
    exact (evStalk_ne_zero_iff a).2 ha

theorem exists_spread {x : Y.X} (a : CxExt σ (Y.X.presheaf.stalk x)) :
    ∃ (U : Y.X.Opens) (A : Y.pts σ → ℂ), x ∈ U ∧ (Y.an σ).HoloOn (ptsIn Y.str σ U) A ∧
      ∀ z ∈ ptsIn Y.str σ U, ∃ a', germIncl z a' = CxExt.map σ (Y.stalkIncl x) a ∧
        germEv z a' = A z := by
  refine CxExt.induction a (fun c s => ?_) (fun a₁ a₂ h₁ h₂ => ?_)
  · obtain ⟨U, hx, g, rfl⟩ := Y.X.presheaf.germ_exist s
    refine ⟨U, fun z => c * ev Y.str σ U g z, hx, ?_, fun z hz => ?_⟩
    · exact (show (Y.an σ).HoloOn (ptsIn Y.str σ U) (fun _ => c) from
        fun _ => differentiableOn_const c).mul ((Y.an σ).holoOn_ev U g)
    · have hz' : base z ∈ U := Var.mem_ptsIn_iff.mp hz
      have e : Y.stalkIncl (base z) (Y.X.presheaf.germ U (base z) hz' g) =
          Y.stalkIncl x (Y.X.presheaf.germ U x hx g) :=
        (algebraMap_germ hz' g).trans (algebraMap_germ hx g).symm
      refine ⟨c • CxExt.of σ (Y.X.presheaf.germ U (base z) hz' g), ?_, ?_⟩
      · simp only [germIncl, map_smul, CxExt.map_of, e]
      · simp only [germEv, map_smul, CxExt.lift_of, smul_eq_mul, evStalk_germ hz']
  · obtain ⟨U₁, A₁, hx₁, hA₁, e₁⟩ := h₁
    obtain ⟨U₂, A₂, hx₂, hA₂, e₂⟩ := h₂
    have s₁ : ptsIn Y.str σ (U₁ ⊓ U₂) ⊆ ptsIn Y.str σ U₁ :=
      fun z hz => Var.mem_ptsIn_iff.mpr (Var.mem_ptsIn_iff.mp hz).1
    have s₂ : ptsIn Y.str σ (U₁ ⊓ U₂) ⊆ ptsIn Y.str σ U₂ :=
      fun z hz => Var.mem_ptsIn_iff.mpr (Var.mem_ptsIn_iff.mp hz).2
    refine ⟨U₁ ⊓ U₂, fun z => A₁ z + A₂ z, ⟨hx₁, hx₂⟩, ?_, fun z hz => ?_⟩
    · intro i
      exact ((hA₁.mono s₁) i).add ((hA₂.mono s₂) i)
    · obtain ⟨b₁, f₁, g₁⟩ := e₁ z (s₁ hz)
      obtain ⟨b₂, f₂, g₂⟩ := e₂ z (s₂ hz)
      exact ⟨b₁ + b₂, by rw [map_add, map_add, f₁, f₂], by rw [map_add, g₁, g₂]⟩

def regSet (f : Y.FnC σ) : Set (Y.pts σ) := {y | RegC y f}

theorem RegC.exists_nhds (h : RegC y f) : ∃ N : Set (Y.pts σ), IsOpen N ∧ y ∈ N ∧
    N ⊆ regSet f ∧ (Y.an σ).HoloOn N fun z => val z f := by
  obtain ⟨c, a, b, hb, hab, -⟩ := h
  obtain ⟨U, A, hU, hA, eA⟩ := exists_spread a
  obtain ⟨V, B, hV, hB, eB⟩ := exists_spread b
  have key : ∀ z, z ∈ ptsIn Y.str σ U → z ∈ ptsIn Y.str σ V → B z ≠ 0 →
      HasVal z f (A z / B z) := by
    intro z zU zV hz
    obtain ⟨a', ha', ha''⟩ := eA z zU
    obtain ⟨b', hb', hb''⟩ := eB z zV
    refine ⟨a', b', by rw [hb'']; exact hz, ?_, ?_⟩
    · rw [ha', hb']; exact hab
    · rw [ha'', hb'']; field_simp
  have yV : y ∈ ptsIn Y.str σ V := Var.mem_ptsIn_iff.mpr hV
  have hBy : B y ≠ 0 := by
    obtain ⟨b', hb', hb''⟩ := eB y yV
    have e : b' = b := germIncl_injective y hb'
    rw [← hb'', e]; exact hb
  refine ⟨ptsIn Y.str σ U ∩ (ptsIn Y.str σ V ∩ B ⁻¹' {0}ᶜ),
    (isOpen_ptsIn U).inter ((hB.continuousOn (isOpen_ptsIn V)).isOpen_inter_preimage
      (isOpen_ptsIn V) isOpen_compl_singleton),
    ⟨Var.mem_ptsIn_iff.mpr hU, yV, hBy⟩, fun z hz => ⟨_, key z hz.1 hz.2.1 hz.2.2⟩, ?_⟩
  refine ((hA.mono fun z hz => hz.1).mul ((hB.mono fun z hz => hz.2.1).inv
    fun z hz => hz.2.2)).congr ?_
  intro z hz
  rw [(key z hz.1 hz.2.1 hz.2.2).val_eq, div_eq_mul_inv]

theorem isOpen_regSet (f : Y.FnC σ) : IsOpen (regSet f) := by
  refine isOpen_iff_forall_mem_open.mpr fun z hz => ?_
  obtain ⟨N, hN, hzN, hNs, -⟩ := (show RegC z f from hz).exists_nhds
  exact ⟨N, hNs, hN, hzN⟩

theorem holoOn_val (f : Y.FnC σ) : (Y.an σ).HoloOn (regSet f) fun z => val z f := by
  choose N hN hyN hNs hNh using fun z : regSet f => (show RegC z.1 f from z.2).exists_nhds
  exact AnRead.holoOn_of_cover (R := Y.an σ) hN (fun z hz => ⟨⟨z, hz⟩, hyN ⟨z, hz⟩⟩)
    fun j => (hNh j).mono Set.inter_subset_right

theorem continuousOn_val (f : Y.FnC σ) : ContinuousOn (fun z => val z f) (regSet f) :=
  (holoOn_val f).continuousOn (isOpen_regSet f)

theorem exists_open_regC (f : Y.FnC σ) :
    ∃ U : Y.X.Opens, genericPoint Y.X ∈ U ∧ ptsIn Y.str σ U ⊆ regSet f := by
  refine CxExt.induction f (fun c g => ?_) (fun f₁ f₂ h₁ h₂ => ?_)
  · obtain ⟨U, hU, a, rfl⟩ := (regAt_genericPoint g).exists_fnOf
    refine ⟨U, hU, fun z hz => ?_⟩
    exact ⟨_, (hasVal_cx_fnOf (Var.mem_ptsIn_iff.mp hz) (gen_mem hU) a).smul c⟩
  · obtain ⟨U₁, hU₁, s₁⟩ := h₁
    obtain ⟨U₂, hU₂, s₂⟩ := h₂
    refine ⟨U₁ ⊓ U₂, ⟨hU₁, hU₂⟩, fun z hz => ?_⟩
    have hz' := Var.mem_ptsIn_iff.mp hz
    obtain ⟨c₁, e₁⟩ := s₁ (Var.mem_ptsIn_iff.mpr hz'.1)
    obtain ⟨c₂, e₂⟩ := s₂ (Var.mem_ptsIn_iff.mpr hz'.2)
    exact ⟨_, e₁.add e₂⟩

end Var

end GlobalTheory.ProjVar
