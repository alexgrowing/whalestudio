import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.Lit.Geo

def Scale {ι : Type} (q : ι → ℝ) (N : ℕ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∀ s t : ℝ, 0 < s → s ≤ t → (Summable fun i => Real.exp (-Real.pi * (s * q i))) ∧
    ∑' i, Real.exp (-Real.pi * (s * q i)) ≤ (t / s) ^ N * ∑' i, Real.exp (-Real.pi * (t * q i))

section Inf

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def qf (x : Fin a → Cinf E) : ℝ := ∑ i, ∑ w : InfinitePlace E, ‖x i w‖ ^ 2

def euc : (Fin a → Cinf E) ≃ₗ[ℝ] EuclideanSpace ℂ (Fin a × InfinitePlace E) where
  toFun x := WithLp.toLp 2 fun p => x p.1 p.2
  invFun y := fun i w => y.ofLp (i, w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem norm_euc_sq (x : Fin a → Cinf E) : ‖euc x‖ ^ 2 = qf x := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

theorem qf_nonneg (x : Fin a → Cinf E) : 0 ≤ qf x := norm_euc_sq x ▸ sq_nonneg _

def gauss (x : Fin a → Cinf E) : ℝ := Real.exp (-Real.pi * qf x)

def quad (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Fin a → Cinf E) : ℝ :=
  ∑ w : InfinitePlace E, (((x ᵥ* p) ⬝ᵥ star x) w).re

variable (E a) in

def poly : Subalgebra ℂ ((Fin a → Cinf E) → ℂ) :=
  Algebra.adjoin ℂ (Set.range fun l : (Fin a → Cinf E) →ₗ[ℝ] ℂ => (l : (Fin a → Cinf E) → ℂ))

def pg (P : (Fin a → Cinf E) → ℂ) (x : Fin a → Cinf E) : ℂ := P x * (gauss x : ℝ)

def sc (y : Matrix (Fin a) (Fin a) (Cinf E)) : ℝ :=
  Real.exp (-((∑ w : InfinitePlace E, Real.log ‖y.det w‖) / ((a : ℝ) * Fintype.card (InfinitePlace E))))

def msum {ι : Type} (x : ι → Fin a → Cinf E) (P : (Fin a → Cinf E) → ℂ) (y : Lie E a) : ℂ :=
  ∑' i, pg P (x i ᵥ* Matrix.of y)

structure IsLat (L : AddSubgroup (Fin a → Af E)) : Prop where
  isOpen : IsOpen (L : Set (Fin a → Af E))
  isCompact : IsCompact (L : Set (Fin a → Af E))

def vFin (v : Fin a → E) : Fin a → Af E := fun i => algebraMap E (Af E) (v i)

def ptF (g : GA E a) : (Fin a → E) →+ (Fin a → Af E) where
  toFun v := vFin v ᵥ* (GeneralLinearGroup.map (pFin E) g).val
  map_zero' := by
    have h : vFin (0 : Fin a → E) = 0 := funext fun _ => map_zero _
    rw [h, Matrix.zero_vecMul]
  map_add' v v' := by
    have h : vFin (v + v') = vFin v + vFin v' := funext fun _ => map_add _ _ _
    rw [h, Matrix.add_vecMul]

def lat (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : AddSubgroup (Fin a → E) := L.comap (ptF g)

variable [IsTotallyComplex E]

def vInf (v : Fin a → E) : Fin a → Cinf E := fun i => pInf E (algebraMap E (Ad E) (v i))

def pt (g : GA E a) : (Fin a → E) →+ (Fin a → Cinf E) where
  toFun v := vInf v ᵥ* (GeneralLinearGroup.map (pInf E) g).val
  map_zero' := by
    have h : vInf (0 : Fin a → E) = 0 := funext fun _ => by simp [vInf]
    rw [h, Matrix.zero_vecMul]
  map_add' v v' := by
    have h : vInf (v + v') = vInf v + vInf v' := funext fun _ => by simp [vInf]
    rw [h, Matrix.add_vecMul]

def rt (g : GA E a) : GA E a := (retractOne g : KernelIndexFullLattice.G1 E a).1

def gsum {M : Type} [AddCommMonoid M] [TopologicalSpace M] (L : AddSubgroup (Fin a → Af E)) (F : (Fin a → Cinf E) → M)
    (g : GA E a) : M := ∑' v : lat L g, F (pt (rt g) v.1)

def Th (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : ℝ := gsum L gauss g

def fn (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : ℝ := Real.log (Th L g)

def mean (L : AddSubgroup (Fin a → Af E)) (P : (Fin a → Cinf E) → ℂ) (g : GA E a) : ℂ := gsum L (pg P) g / (Th L g : ℝ)

def mom (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : Herm E a :=
  ⟨Matrix.of fun i j w => mean L (fun x => star (x i w) * x j w) g, by
    change star _ = _
    ext i j w
    simp only [Matrix.star_apply, Matrix.of_apply, Pi.star_apply, mean, gsum, pg, star_div₀, tsum_star, star_mul',
      star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_tsum, map_mul, Complex.conj_conj, mul_comm]⟩

def dev (L : AddSubgroup (Fin a → Af E)) (g : GA E a) : Herm E a :=
  mom L g - ell E a (toL (mom L g).1) • (⟨1, IsSelfAdjoint.one _⟩ : Herm E a)

def meanAlg (L : AddSubgroup (Fin a → Af E)) : Subalgebra ℂ (GA E a → ℂ) :=
  Algebra.adjoin ℂ {f | ∃ P ∈ poly E a, f = mean L P}

end Inf

end UpperTheory.V.Lit.Geo
