import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulStrictMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL
open scoped Kronecker

namespace PositivityTheory.KB

section Chains

variable {G H K Y : Type} [Group G] [Group H] [Group K]

abbrev Chn (G : Type) (m : ℕ) : Type := (Fin m → G) →₀ ℝ

def bd (G : Type) [Group G] (m : ℕ) : Chn G (m + 1) →ₗ[ℝ] Chn G m :=
  Finsupp.linearCombination ℝ fun g =>
    Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : ℝ) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1

def IsCyc {m : ℕ} (z : Chn G (m + 1)) : Prop := bd G m z = 0

def IsBd {m : ℕ} (z : Chn G m) : Prop := z ∈ LinearMap.range (bd G m)

def cmap (f : G →* H) (m : ℕ) : Chn G m →ₗ[ℝ] Chn H m := Finsupp.lmapDomain ℝ ℝ fun g i => f (g i)

def IsPrim {m : ℕ} (z : Chn G m) : Prop :=
  IsBd (cmap ((MonoidHom.id G).prod (MonoidHom.id G)) m z - cmap (MonoidHom.inl G G) m z -
    cmap (MonoidHom.inr G G) m z)

def dC {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : (Fin (m + 2) → Y) → ℝ :=
  fun y => ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F fun j => y (i.succAbove j)

variable [MulAction H Y]

def Inv (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : Prop := ∀ g y, F (fun j => ρ g • y j) = F y

def ev (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) : ℝ :=
  z.sum fun g r => r * F fun j => ρ (Fin.partialProd g j) • y

def hecke (ρ : G →* K) (τ : K →* H) (q : K) {E : Type} [AddCommGroup E] [Module ℝ E] (f : Y → E) : Y → E :=
  fun y =>
    ((((ρ.range.map (MulAut.conj q⁻¹).toMonoidHom).comap ρ).index : ℝ))⁻¹ •
      ∑ᶠ c : Quotient (QuotientGroup.rightRel ((ρ.range.map (MulAut.conj q⁻¹).toMonoidHom).comap ρ)),
        f (τ (q * ρ c.out) • y)

end Chains

def psi (R : Type) [CommRing R] (d n : ℕ) : GL (Fin n) R →* GL (Fin (d * n)) R :=
  Units.map
    { toFun := fun A => Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) R) ⊗ₖ A)
      map_one' := by simp
      map_mul' := fun A B => by
        simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Matrix.mul_one] }

section Simplex

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

abbrev Form (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (q : ℕ) : Type := V → V [⋀^Fin q]→L[ℝ] ℝ

def intS {q : ℕ} (ω : Form V q) (y : Fin (q + 1) → V) : ℝ :=
  ∫ t in {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1},
    ω (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0

end Simplex

section Cone

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

abbrev Gp : Type := InfinitePlace L → GL (Fin N) ℂ

abbrev Sp : Type := InfinitePlace L → SpecialLinearGroup (Fin N) ℂ

instance : MeasurableSpace (Sp L N) := borel _
instance : BorelSpace (Sp L N) := ⟨rfl⟩

abbrev GK : Type := GL (Fin N) L

def toK : Gm L N →* GK L N := GeneralLinearGroup.map (algebraMap (𝓞 L) L)

def toP : GK L N →* Gp L N := MonoidHom.pi fun w => GeneralLinearGroup.map w.embedding

def emb : Gm L N →* Gp L N := (toP L N).comp (toK L N)

def ofS : Sp L N →* Gp L N := MonoidHom.pi fun w => SpecialLinearGroup.toGL.comp (Pi.evalMonoidHom _ w)

def latS : Subgroup (Sp L N) :=
  (MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w)).range

def scal (s : InfinitePlace L → ℂˣ) : Gp L N := fun w => GeneralLinearGroup.scalar (Fin N) (s w)

variable {L N}

def actM (g : Gp L N) : HS L N →ₗ[ℝ] HS L N where
  toFun h := mkHS (fun w => (((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat h w * ((g w)⁻¹ : GL (Fin N) ℂ))
    (fun w => isHermitian_conjTranspose_mul_mul _ (mat_herm h w))
  map_add' h k := HS_ext fun w => by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c h := HS_ext fun w => by simp

def actL (g : Gp L N) : HS L N →L[ℝ] HS L N := LinearMap.toContinuousLinearMap (actM g)

theorem mat_actL (g : Gp L N) (h : HS L N) (w : InfinitePlace L) :
    mat (actL g h) w =
      (((g w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)ᴴ * mat h w * ((g w)⁻¹ : GL (Fin N) ℂ) := rfl

theorem actL_one (h : HS L N) : actL 1 h = h := HS_ext fun w => by simp [mat_actL]

theorem actL_mul (g k : Gp L N) (h : HS L N) : actL (g * k) h = actL g (actL k h) :=
  HS_ext fun w => by simp [mat_actL, Matrix.mul_assoc]

open ComplexOrder in
theorem actL_pos (g : Gp L N) {h : HS L N} (hh : h ∈ Pos L N) : actL g h ∈ Pos L N := fun w => by
  rw [mat_actL]
  exact (hh w).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (Units.isUnit _))

instance : MulAction (Gp L N) (Pos L N) where
  smul g h := ⟨actL g h.1, actL_pos g h.2⟩
  one_smul h := Subtype.ext (actL_one h.1)
  mul_smul g k h := Subtype.ext (actL_mul g k h.1)

variable (L N)

open ComplexOrder in

def one : Pos L N := ⟨mkHS (fun _ => 1) fun _ => isHermitian_one, fun _ => PosDef.one⟩

variable {L N}

def fr {q : ℕ} (ω : Form (HS L N) q) (x : Gp L N) : HS L N [⋀^Fin q]→L[ℝ] ℝ :=
  (ω (actL x (one L N).1)).compContinuousLinearMap (actL x)

def FInv {q : ℕ} (ω : Form (HS L N) q) (g : Gp L N) : Prop :=
  ∀ h ∈ Pos L N, (ω (actL g h)).compContinuousLinearMap (actL g) = ω h

def intP {q : ℕ} (ω : Form (HS L N) q) (y : Fin (q + 1) → Pos L N) : ℝ := intS ω fun j => (y j).1

def Good {q : ℕ} (ω : Form (HS L N) q) : Prop := ContinuousOn ω (Pos L N) ∧ dC (intP ω) = 0

def lam (h : HS L N) : ℝ := ⨅ y : {y : Lat L N // y ≠ 0}, q h y.1

def dualH (h : HS L N) : HS L N := mkHS (fun w => ((mat h w)⁻¹)ᵀ) fun w => (mat_herm h w).inv.transpose

def ht (x : Gp L N) : ℝ := (lam (actL x (one L N).1) * lam (dualH (actL x (one L N).1)))⁻¹

variable (L N)

def qel (π : 𝓞 L) (hπ : π ≠ 0) : GK L N :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1) (by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    split_ifs
    · exact_mod_cast hπ
    · exact one_ne_zero)

structure Dom where

  μ : Measure (Sp L N)

  D : Set (Sp L N)
  haar : μ.IsHaarMeasure
  right : μ.IsMulRightInvariant
  fund : IsFundamentalDomain (latS L N) D μ
  fin : μ D < ⊤

structure PU (Ht : Gp L N → ℝ) where

  φ : HS L N → ℝ
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) φ (Pos L N)
  locFin : LocallyFinite fun γ : Gm L N => {h : Pos L N | φ (actL (emb L N γ)⁻¹ h.1) ≠ 0}
  sum_one : ∀ h ∈ Pos L N, ∑ᶠ γ : Gm L N, φ (actL (emb L N γ)⁻¹ h) = 1
  overlap : {γ : Gm L N | ∃ h : Pos L N, h ∈ closure {k : Pos L N | φ k.1 ≠ 0} ∧
    (emb L N γ)⁻¹ • h ∈ closure {k : Pos L N | φ k.1 ≠ 0}}.Finite
  homog : ∀ r : ℝ, 0 < r → ∀ h ∈ Pos L N, φ (r • h) = φ h
  bdd : ∃ C, ∀ h ∈ Pos L N, |φ h| ≤ C
  deriv : ∃ C, ∀ x : Gp L N, ‖(fderiv ℝ φ (actL x (one L N).1)).comp (actL x)‖ ≤ C * Ht x

end Cone

end PositivityTheory.KB

end
