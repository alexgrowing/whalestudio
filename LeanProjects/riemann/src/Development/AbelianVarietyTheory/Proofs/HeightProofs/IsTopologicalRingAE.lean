import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FockOrthogonalDecomposition

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]

def Sm (ι : R →+ G) (f : G → ℂ) : Prop := ∀ w, ContDiff ℝ ∞ fun x : R => f (w + ι x)

def hD (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (u : R) (f : G → ℂ) : G → ℂ :=
  fun w => deriv (fun t : ℝ =>
    Complex.exp (-(Real.pi * Complex.I) * (om (π w) (t • u) : ℝ)) * f (w + ι (t • u))) 0

def Killed {I M : Type} [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (N : ℕ) (m : M) : Prop :=
  ∀ l : List I, l.length = N → l.foldr (fun i x => a i x) m = 0

end Abstract

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition

structure Chart (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) : Prop where
  inf : IsInfFam θ
  cont : Continuous σ
  fin : ∀ z, finPart D (σ z) = 0
  comp : ∀ z τ, θ τ (infPart D (σ z)) = z τ
  ext : ∀ a : AE D, finPart D a = 0 → (∀ τ, θ τ (infPart D a) = 0) → a = 0

abbrev RW (V W : HSp D) : Type := D.what₂.Tau → Fin V.rank → Fin W.rank → ℂ

def piW (θ : InfFam D) (V W : HSp D) : WA V W →+ RW V W where
  toFun x := fun τ i j => θ τ (infPart D (x i j))
  map_zero' := by funext τ i j; simp
  map_add' x y := by
    funext τ i j
    show θ τ (infPart D (x i j + y i j)) = θ τ (infPart D (x i j)) + θ τ (infPart D (y i j))
    rw [RingHom.map_add, RingHom.map_add]

def iotaW (σ : (D.what₂.Tau → ℂ) →+ AE D) (V W : HSp D) : RW V W →+ WA V W where
  toFun z := Matrix.of fun i j => σ fun τ => z τ i j
  map_zero' := by ext i j; exact σ.map_zero
  map_add' x y := by ext i j; exact σ.map_add (fun τ => x τ i j) (fun τ => y τ i j)

theorem piW_apply (θ : InfFam D) (V W : HSp D) (x : WA V W) (τ : D.what₂.Tau) : piW θ V W x τ = wAt θ V W τ x := rfl

theorem symplC_add_left (V W : HSp D) (τ : D.what₂.Tau) (x x' y : WC V W) :
    symplC V W τ (x + x') y = symplC V W τ x y + symplC V W τ x' y := by
  unfold symplC hC
  split_ifs <;> simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]

theorem symplC_add_right (V W : HSp D) (τ : D.what₂.Tau) (x y y' : WC V W) :
    symplC V W τ x (y + y') = symplC V W τ x y + symplC V W τ x y' := by
  unfold symplC hC
  split_ifs <;> simp only [Matrix.add_apply, mul_add, add_mul, map_add, Finset.sum_add_distrib, Complex.add_re]

theorem hC_smul_right (V W : HSp D) (τ : D.what₂.Tau) (c : ℂ) (x y : WC V W) :
    hC V W τ x (c • y) = c * hC V W τ x y := by
  unfold hC
  split_ifs <;> simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum] <;>
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

theorem hC_smul_left (V W : HSp D) (τ : D.what₂.Tau) (c : ℂ) (x y : WC V W) :
    hC V W τ (c • x) y = starRingEnd ℂ c * hC V W τ x y := by
  unfold hC
  split_ifs <;> simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul] <;>
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

theorem symplC_smul_left (V W : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : WC V W) :
    symplC V W τ (c • x) y = c * symplC V W τ x y := by
  unfold symplC
  rw [← Complex.coe_smul, hC_smul_right, mul_left_comm, Complex.re_ofReal_mul]; ring

theorem symplC_smul_right (V W : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : WC V W) :
    symplC V W τ x (c • y) = c * symplC V W τ x y := by
  unfold symplC
  rw [← Complex.coe_smul, hC_smul_left, Complex.conj_ofReal, mul_left_comm, Complex.re_ofReal_mul]; ring

def omR (V W : HSp D) : RW V W →ₗ[ℝ] RW V W →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ τ, symplC V W τ (x τ) (y τ))
    (fun x x' y => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => symplC_add_left V W τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => symplC_smul_left V W τ c _ _)
    (fun x y y' => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => symplC_add_right V W τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => symplC_smul_right V W τ c _ _)

theorem omR_apply (V W : HSp D) (x y : RW V W) : omR V W x y = ∑ τ, symplC V W τ (x τ) (y τ) := rfl

theorem jAt_add (V W : HSp D) (τ : D.what₂.Tau) (s s') (x y : WC V W) :
    jAt V W τ s s' (x + y) = jAt V W τ s s' x + jAt V W τ s s' y := by
  unfold jAt actC
  split_ifs <;> simp only [Matrix.mul_add, Matrix.add_mul, smul_add]

theorem jAt_smul (V W : HSp D) (τ : D.what₂.Tau) (s s') (c : ℝ) (x : WC V W) :
    jAt V W τ s s' (c • x) = c • jAt V W τ s s' x := by
  unfold jAt actC
  split_ifs <;> simp only [Matrix.mul_smul, Matrix.smul_mul] <;> exact smul_comm _ _ _

def jR (V W : HSp D) (s : InvFam V) (s' : InvFam W) : RW V W →ₗ[ℝ] RW V W where
  toFun x := fun τ => jAt V W τ (s τ) (s' τ) (x τ)
  map_add' x y := by funext τ; exact jAt_add V W τ _ _ _ _
  map_smul' c x := by funext τ; exact jAt_smul V W τ _ _ c _

theorem jR_apply (V W : HSp D) (s : InvFam V) (s' : InvFam W) (x : RW V W) (τ : D.what₂.Tau) :
    jR V W s s' x τ = jAt V W τ (s τ) (s' τ) (x τ) := rfl

variable {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem Chart.pi_iota (h : Chart θ σ) (V W : HSp D) (z : RW V W) : piW θ V W (iotaW σ V W z) = z := by
  funext τ i j; exact h.comp _ τ

theorem Chart.real_iota (h : Chart θ σ) (V W : HSp D) (z : RW V W) : IsRealW V W (iotaW σ V W z) := by
  ext i j; exact h.fin _

theorem Chart.real_ext (h : Chart θ σ) {V W : HSp D} {x y : WA V W} (hx : IsRealW V W x) (hy : IsRealW V W y)
    (e : piW θ V W x = piW θ V W y) : x = y := by
  ext i j
  rw [← sub_eq_zero]
  refine h.ext _ ?_ fun τ => ?_
  · have h1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : finPart D (y i j) = 0 := congrFun (congrFun hy i) j
    rw [RingHom.map_sub, h1, h2, sub_zero]
  · have : θ τ (infPart D (x i j)) = θ τ (infPart D (y i j)) := congrFun (congrFun (congrFun e τ) i) j
    rw [RingHom.map_sub, RingHom.map_sub, this, sub_self]

theorem Chart.iota_pi (h : Chart θ σ) {V W : HSp D} {x : WA V W} (hx : IsRealW V W x) :
    iotaW σ V W (piW θ V W x) = x :=
  h.real_ext (h.real_iota V W _) hx (h.pi_iota V W _)

theorem Chart.continuous_iota (h : Chart θ σ) (V W : HSp D) : Continuous (iotaW σ V W) :=
  continuous_pi fun i => continuous_pi fun j => h.cont.comp (continuous_pi fun τ =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ)))

instance isModuleTopology_AE : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩

instance isTopologicalRing_AE : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)

theorem continuous_comp (hθ : IsInfFam θ) (τ : D.what₂.Tau) : Continuous fun z : AE D => θ τ (infPart D z) := by
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  have he : (fun z : AE D => θ τ (infPart D z)) = fun z => ∑ i,
      θ τ (fstA D.host.F (B.coord i z) ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ (b i) := by
    funext z
    conv_lhs => rw [← B.sum_repr z]
    rw [show ∀ y, θ τ (infPart D y) = ((θ τ).comp (infPart D)).toAddMonoidHom y from fun _ => rfl, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show θ τ (infPart D _) = _
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← (hθ τ).1, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  rw [he]
  refine continuous_finset_sum _ fun i _ => Continuous.mul ?_ continuous_const
  have h1 : Continuous (B.coord i) := IsModuleTopology.continuous_of_linearMap _
  have h2 : Continuous (fstA D.host.F) := continuous_fst
  exact (hθ τ).2.comp (h2.comp h1)

theorem continuous_pi' (hθ : IsInfFam θ) (V W : HSp D) : Continuous (piW θ V W) :=
  continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
    (continuous_comp hθ τ).comp ((continuous_apply j).comp (continuous_apply i))

theorem tauE_star (τ : D.what₂.Tau) (x : D.host.E) : tauE D τ (star x) = starRingEnd ℂ (tauE D τ x) := by
  have := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ x

theorem comp_incA (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) : θ τ (infPart D (incA D e)) = tauE D τ e :=
  (hθ τ).1 e

theorem conj_tmul_one (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : Ainf D.host.F) :
    starRingEnd ℂ (θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E))) = θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
  have h := hθ τ
  refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
    (isClosed_eq (Complex.continuous_conj.comp h.2) h.2) fun f => ?_
  have e : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
      (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
    exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f |>.trans
      ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
  erw [e, h.1, ← tauE_star]
  rw [(D.sp.cm.fixed _).2 ⟨f, rfl⟩]

theorem comp_cA (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : AE D) :
    θ τ (infPart D (cA D z)) = starRingEnd ℂ (θ τ (infPart D z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul a x =>
    have e : ∀ y : D.host.E, fstA D.host.F a ⊗ₜ[D.host.F] y =
        (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      intro y; simp
    have e2 : infPart D (cA D (a ⊗ₜ[D.host.F] x)) = fstA D.host.F a ⊗ₜ[D.host.F] (star x) := rfl
    have e3 : infPart D (a ⊗ₜ[D.host.F] x) = fstA D.host.F a ⊗ₜ[D.host.F] x := rfl
    rw [e2, e3, e (star x), e x, map_mul, map_mul, map_mul, conj_tmul_one hθ, (hθ τ).1, (hθ τ).1, tauE_star]

def IsCart {n : ℕ} (G t : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  t * t = 1 ∧ tᴴ * G * t = G ∧ (G * t).PosDef

def Rel (V : HSp D) (τ : D.what₂.Tau) (A : Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (s : Module.End D.host.E V.V) : Prop :=
  Aᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A = gramAt D V τ ∧
    Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A = A * thAt V τ s

def Adapted (V : HSp D) (b : Module.Basis (Fin V.rank) D.host.E V.V) (s : InvFam V) : Prop :=
  (∀ i j, i ≠ j → V.hT (b i) (b j) = 0) ∧ ∀ τ i, s τ (b i) = b i ∨ s τ (b i) = -b i

end GlobalTheory.FockCompare

end
