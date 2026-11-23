import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt

noncomputable section

open scoped Matrix NNReal TensorProduct ComplexConjugate
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.LocIntw

section Slices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)

def sliceFin (v : HeightOneSpectrum (𝓞 F)) (g₀ : GAd σ Q) (f : GAd σ Q → ℂ) : GLoc σ Q v → ℂ :=
  fun g => f (emb σ Q v g * g₀)

def sliceArch (w : InfinitePlace F) (g₀ : GAd σ Q) (f : GAd σ Q → ℂ) : GArch σ Q w → ℂ :=
  fun g => f (embArch σ Q w g * g₀)

def AlmostSph (φf : ∀ v, GLoc σ Q v → ℂ) : Prop := ∀ᶠ v in Filter.cofinite, ∀ k ∈ KUpFin σ Q v, φf v k = 1

def IsProdSec (f : GAd σ Q → ℂ) (φi : ∀ w, GArch σ Q w → ℂ) (φf : ∀ v, GLoc σ Q v → ℂ) : Prop :=
  f = prodFun σ Q φi φf ∧ AlmostSph σ Q φf

variable {σ Q}

theorem AlmostSph.finite {φf : ∀ v, GLoc σ Q v → ℂ} (h : AlmostSph σ Q φf) (g : GAd σ Q) :
    (Function.mulSupport fun v => φf v (proj σ Q v g)).Finite :=
  (Filter.eventually_cofinite.1 (h.and (eventually_proj_mem_KUpFin g))).subset fun _ hv h' => hv (h'.1 _ h'.2)

variable (hc : IsCMExt F E σ) (hI : ∀ g : GAd σ Q, ∃ p : upperParabolic (AF F) σ Q, ∃ k ∈ KUpAd σ Q, g = p * k)
include hc hI

end Slices

section SlicesDatum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

variable {D : D7} {n : ℕ}

end SlicesDatum

section FiniteProducts

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ)

def intMat (v : HeightOneSpectrum (𝓞 F)) : Set (Fin m → Fin n → Fv F v ⊗[F] E) := {x | ∀ i j, x i j ∈ intLoc F E v}

variable {F E m n}

def AlmostInt (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin m → Fin n → Fv F v ⊗[F] E) → ℂ) : Prop :=
  ∀ᶠ v in Filter.cofinite, φ v = Set.indicator (intMat F E m n v) 1

def finProd (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin m → Fin n → Fv F v ⊗[F] E) → ℂ) (y : Fin m → Fin n → Af F ⊗[F] E) : ℂ :=
  ∏ᶠ v, φ v fun i j => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i j)

theorem AlmostInt.finite {φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin m → Fin n → Fv F v ⊗[F] E) → ℂ} (h : AlmostInt φ)
    (y : Fin m → Fin n → Af F ⊗[F] E) : (Function.mulSupport fun v => φ v fun i j =>
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i j)).Finite :=
  (Filter.eventually_cofinite.1 (h.and (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    eventually_map_evalV_mem_intLoc (y i j)))).subset fun v hv h' => hv (by
      beta_reduce
      rw [h'.1, Set.indicator_of_mem (s := intMat F E m n v) h'.2, Pi.one_apply])

theorem indicator_intMat_mem_SB (v : HeightOneSpectrum (𝓞 F)) :
    (Set.indicator (intMat F E m n v) 1 : _ → ℂ) ∈ WeilM.SB (Fin m → Fin n → Fv F v ⊗[F] E) := by
  haveI := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := Fv F v)
  obtain ⟨hc, ho⟩ := ThK.isCompact_isOpen_intLoc (F := F) (E := E) v
  have e : intMat F E m n v = Set.univ.pi fun _ => Set.univ.pi fun _ => (intLoc F E v : Set (Fv F v ⊗[F] E)) := by
    ext x; simp [intMat]
  have h1 : IsCompact (intMat F E m n v) := e ▸ isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
  have h2 : IsOpen (intMat F E m n v) :=
    e ▸ isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => ho
  exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨h1.isClosed, h2⟩).isLocallyConstant,
    HasCompactSupport.intro h1 fun x hx => Set.indicator_of_notMem hx _⟩

omit [NumberField F] [NumberField E] in

def matCoord {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : (Fin m → Fin n → R ⊗[F] E) ≃ₜ (Fin m × Fin n × Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { toFun := fun x k => (Algebra.TensorProduct.basis R b).repr (x k.1 k.2.1) k.2.2
    invFun := fun y i j => ∑ k, y (i, j, k) • Algebra.TensorProduct.basis R b k
    left_inv := fun x => funext fun i => funext fun j => (Algebra.TensorProduct.basis R b).sum_repr (x i j)
    right_inv := fun y => funext fun k => congrFun ((Algebra.TensorProduct.basis R b).repr_sum_self fun t => y (k.1, k.2.1, t)) k.2.2
    continuous_toFun := continuous_pi fun k =>
      (IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k.2.2)).comp
        ((continuous_apply k.2.1).comp (continuous_apply k.1))
    continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
      continuous_finsetSum _ fun k _ => (continuous_apply (i, j, k)).smul continuous_const }

omit [NumberField F] [NumberField E] in

theorem matCoord_map {d : ℕ} (b : Module.Basis (Fin d) F E) {R R' : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing R'] [Algebra F R'] [TopologicalSpace R'] [IsTopologicalRing R'] (φ : R →ₐ[F] R')
    (x : Fin m → Fin n → R ⊗[F] E) :
    matCoord b R' (fun i j => Algebra.TensorProduct.map φ (AlgHom.id F E) (x i j)) = fun k => φ (matCoord b R x k) := by
  funext k
  change (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) (x k.1 k.2.1)) k.2.2 =
    φ ((Algebra.TensorProduct.basis R b).repr (x k.1 k.2.1) k.2.2)
  induction x k.1 k.2.1 using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem eventually_mem_intMat_iff {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x, x ∈ intMat F E m n v ↔
      ∀ k, matCoord b (Fv F v) x k ∈ v.adicCompletionIntegers F :=
  (Cofinite.eventually_mem_intLoc_iff_repr b).mono fun _ h _ =>
    ⟨fun hx k => (h _).1 (hx k.1 k.2.1) k.2.2, fun hx i j => (h _).2 fun k => hx (i, j, k)⟩

theorem finProd_mem_SB {φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin m → Fin n → Fv F v ⊗[F] E) → ℂ}
    (hφ : ∀ v, φ v ∈ WeilM.SB (Fin m → Fin n → Fv F v ⊗[F] E)) (h : AlmostInt φ) :
    finProd φ ∈ WeilM.SB (Fin m → Fin n → Af F ⊗[F] E) := by
  let b := Module.finBasis F E
  have h1 := AdelicCoordSB.finprod_mem_SB F _ (fun v => φ v ∘ (matCoord b (Fv F v)).symm)
    (fun v => ⟨(hφ v).1.comp_continuous (matCoord b (Fv F v)).symm.continuous, (hφ v).2.comp_homeomorph _⟩) (by
      filter_upwards [h, eventually_mem_intMat_iff (m := m) (n := n) b] with v hv hv'
      funext y
      rw [hv, Function.comp_apply]
      refine Set.indicator_eq_indicator ?_ rfl
      rw [hv', Homeomorph.apply_symm_apply]; rfl)
  have e : finProd φ = (fun y => ∏ᶠ v, (φ v ∘ (matCoord b (Fv F v)).symm) fun k => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y k)) ∘
      matCoord b (Af F) := funext fun y => finprod_congr fun v => by
    rw [Function.comp_apply, ← matCoord_map, Homeomorph.symm_apply_apply]
  rw [e]
  exact ⟨h1.1.comp_continuous (matCoord b (Af F)).continuous, h1.2.comp_homeomorph _⟩

theorem finProd_indicator : finProd (fun v => Set.indicator (intMat F E m n v) 1) =
    Set.indicator {y | ∀ v i j, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i j) ∈
      intLoc F E v} 1 := by
  funext y
  by_cases hy : ∀ v i j, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i j) ∈ intLoc F E v
  · rw [Set.indicator_of_mem (by exact hy)]
    exact finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (s := intMat F E m n v) (hy v) _
  · rw [Set.indicator_of_notMem (by exact hy)]
    obtain ⟨v, hv⟩ := not_forall.1 hy
    exact finprod_eq_zero _ v (Set.indicator_of_notMem (s := intMat F E m n v) hv _)
      (AlmostInt.finite (φ := fun v => Set.indicator (intMat F E m n v) 1) (.of_forall fun _ => rfl) y)

omit [NumberField E] in

theorem compFin_eq_map_sndA (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) : compFin F E v z =
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  rfl

end FiniteProducts

section Factorizable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum

variable {D : D7} {n : ℕ}

def evalPolyAt {m : ℕ} (p : MvPolynomial (Fin m × Fin n × Bool) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (fun k => if k.2.2 then conj (z k.1 k.2.1) else z k.1 k.2.1) p

def gaussAt (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    (z : Matrix (Fin V.rank) (Fin n) ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi) * (((|l τ| : ℝ) : ℂ) * Matrix.trace (zᴴ * (gramAt D V τ * s τ) * z)))

theorem gauss_eq_prod (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) : StdUnn.gauss V l s z = ∏ τ, gaussAt V l s τ (z τ) := by
  rw [StdUnn.gauss, Finset.mul_sum, Complex.exp_sum]; rfl

theorem evalPoly_rename {m : ℕ} (τ : D.what₂.Tau) (p : MvPolynomial (Fin m × Fin n × Bool) ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    StdUnn.evalPoly (MvPolynomial.rename (Prod.mk τ) p) z = evalPolyAt p (z τ) := MvPolynomial.eval_rename _ _ _

def pureFun (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (p : D.what₂.Tau → MvPolynomial (Fin V.rank × Fin n × Bool) ℂ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin V.rank → Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ)
    (x : Mx D V.rank n) : ℂ :=
  (∏ τ, evalPolyAt (p τ) (compAt θ τ x) * gaussAt V l s τ (compAt θ τ x)) *
    ∏ᶠ v, φ v fun i j => AdelicU.compFin D.host.F D.host.E v (x i j)

def IsFactorizable (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (Φ : Mx D V.rank n → ℂ) : Prop :=
  ∃ (p : D.what₂.Tau → MvPolynomial (Fin V.rank × Fin n × Bool) ℂ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin V.rank → Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ),
    (∀ v, φ v ∈ WeilM.SB (Fin V.rank → Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E)) ∧ AlmostInt φ ∧
      Φ = pureFun θ V l s p φ

theorem compFin_eq (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) : AdelicU.compFin D.host.F D.host.E v z =
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (finPart D z) := by
  exact compFin_eq_map_sndA v z

variable {θ : InfFam D} {V : HSp D} {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem pureFun_eq (p : D.what₂.Tau → MvPolynomial (Fin V.rank × Fin n × Bool) ℂ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin V.rank → Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) → ℂ)
    (x : Mx D V.rank n) : pureFun θ V l s p φ x =
      StdUnn.evalPoly (∏ τ, MvPolynomial.rename (Prod.mk τ) (p τ)) (fun τ => compAt θ τ x) *
        StdUnn.gauss V l s (fun τ => compAt θ τ x) * finProd φ fun i j => finPart D (x i j) := by
  rw [pureFun, Finset.prod_mul_distrib, gauss_eq_prod, StdUnn.evalPoly, map_prod, finProd]
  simp only [compFin_eq]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (evalPoly_rename τ (p τ) fun τ => compAt θ τ x).symm

theorem IsFactorizable.mem_fockA {Φ : Mx D V.rank n → ℂ} (h : IsFactorizable θ V n l s Φ) :
    Φ ∈ StdUnn.fockA θ V n l s := by
  obtain ⟨p, φ, h1, h2, rfl⟩ := h
  exact Submodule.subset_span ⟨_, _, finProd_mem_SB h1 h2, funext (pureFun_eq p φ)⟩

def vacFun (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Mx D V.rank n → ℂ := fun x => StdUnn.gauss V l s (fun τ => compAt θ τ x) *
  Set.indicator {x : Mx D V.rank n | ∀ v i j, AdelicU.compFin D.host.F D.host.E v (x i j) ∈ intLoc D.host.F D.host.E v} 1 x

theorem isFactorizable_vacFun : IsFactorizable θ V n l s (vacFun θ V n l s) := by
  refine ⟨1, fun v => Set.indicator (intMat _ _ _ _ v) 1, indicator_intMat_mem_SB, .of_forall fun _ => rfl,
    funext fun x => ?_⟩
  rw [pureFun_eq, finProd_indicator, vacFun]
  simp only [Pi.one_apply, map_one, Finset.prod_const_one, StdUnn.evalPoly, one_mul, compFin_eq]
  rfl

theorem vacFun_zero : vacFun θ V n l s 0 = 1 := by
  have h : ∀ τ, compAt θ τ (0 : Mx D V.rank n) = 0 := fun τ => by ext i j; simp [compAt]
  rw [vacFun, Set.indicator_of_mem (fun v i j => by simp)]
  simp [StdUnn.gauss, h]

example : ∃ Φ ∈ StdUnn.fockA θ V n l s, IsFactorizable θ V n l s Φ ∧ Φ 0 = 1 :=
  ⟨_, isFactorizable_vacFun.mem_fockA, isFactorizable_vacFun, vacFun_zero⟩

example {m : ℕ} (z : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    evalPolyAt (MvPolynomial.X (i, j, false)) z = z i j ∧ evalPolyAt (MvPolynomial.X (i, j, true)) z = conj (z i j) := by
  simp [evalPolyAt]

end Factorizable

end GlobalTheory.LocIntw

end
