import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitCoord

section General

variable {R T : Type} [CommRing R] [CommRing T] [Algebra R T]

theorem trace_mul_idem (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0) (x y : T) :
    Algebra.trace R T (e * (x * y)) = Algebra.trace R T (e * x) * Algebra.trace R T (e * y) := by
  apply hi
  have hc : c e * c e = c e := by rw [← map_mul, h1]
  rw [RingHom.map_mul, ht, ht, ht]
  simp only [map_mul]
  linear_combination (-(x * y)) * h1 - (c x * c y) * hc - (x * c y + c x * y) * h2

theorem idem_mul_trace (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0)
    {α : R} (h3 : e + c e = algebraMap R T α) (x : T) :
    e * algebraMap R T (α * Algebra.trace R T (e * x)) = e * x := by
  rw [map_mul, ht, ← h3, map_mul]
  linear_combination ((e + 1) * x) * h1 + (e * x + e * c x + c e * c x) * h2

theorem trace_idem_mul (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T}
    {α : R} (h3 : e + c e = algebraMap R T α) (b : R) :
    Algebra.trace R T (e * algebraMap R T b) = b * α := by
  have : Algebra.trace R T e = α := hi (by rw [ht, h3])
  rw [mul_comm, ← Algebra.smul_def, map_smul, this, smul_eq_mul]

theorem exists_hom (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0)
    {α : R} (h3 : e + c e = algebraMap R T α) {S K : Type} [CommRing S] [CommRing K] [Algebra S R] [Algebra S K]
    (φ : R →ₐ[S] K) (hα : φ α = 1) :
    ∃ π : T →+* K, ∀ x, π x = φ (Algebra.trace R T (e * x)) :=
  ⟨{ toFun := fun x => φ (Algebra.trace R T (e * x))
     map_one' := by
       have := trace_idem_mul hi c ht h3 1
       rw [RingHom.map_one, one_mul] at this
       rw [this, hα]
     map_mul' := fun x y => by rw [trace_mul_idem hi c ht h1 h2, map_mul]
     map_zero' := by rw [mul_zero, map_zero, map_zero]
     map_add' := fun x y => by rw [mul_add, map_add, map_add] }, fun _ => rfl⟩

end General

section Single

variable {F : Type} [Field F] [NumberField F]

theorem evalV_single (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : evalV F v (singleV F v a) = a := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v a

theorem evalV_single_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (a : Fv F v) : evalV F w (singleV F v a) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) a h

theorem single_evalV {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h1 : evalV F v α = 1)
    (h2 : ∀ w, w ≠ v → evalV F w α = 0) (b : Af F) : singleV F v (evalV F v b) = α * b := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV F w (singleV F v (evalV F v b)) = evalV F w (α * b)
  by_cases hw : w = v
  · subst hw
    rw [evalV_single, map_mul, h1, one_mul]
  · rw [evalV_single_ne hw, map_mul, h2 w hw, zero_mul]

theorem single_mem {v : HeightOneSpectrum (𝓞 F)} {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    singleV F v a ∈ intAf F := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [evalV_single]; exact ha
  · rw [evalV_single_ne hw]; exact zero_mem _

end Single

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def finT : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

variable (F E) in

def intT : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

theorem alg_inj (R : Type) [CommRing R] [Algebra F R] : Function.Injective (algebraMap R (R ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

theorem finT_sig (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) : finT F E (sigR (AF F) σ z) = sigR (Af F) σ (finT F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul a e => rfl

theorem finT_alg (a : AF F) : finT F E (algebraMap (AF F) _ a) = algebraMap (Af F) _ (sndA F a) := rfl

theorem mul_mem_intT {x y : Af F ⊗[F] E} (hx : x ∈ intT F E) (hy : y ∈ intT F E) : x * y ∈ intT F E := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intT F E) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem trace_mem (v : HeightOneSpectrum (𝓞 F)) {x : Af F ⊗[F] E} (hx : x ∈ intT F E) :
    evalV F v (Algebra.trace (Af F) (Af F ⊗[F] E) x) ∈ v.adicCompletionIntegers F := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    have h1 : a ⊗ₜ[F] (y : E) = a • ((1 : Af F) ⊗ₜ[F] (y : E)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace (Af F) (Af F ⊗[F] E) (a ⊗ₜ[F] (y : E)) = a * algebraMap F _ (Algebra.trace F E y) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    rw [h3, map_mul, AlgHom.commutes]
    refine mul_mem (ha v) ?_
    have hi : IsIntegral ℤ (Algebra.trace F E y) := Algebra.isIntegral_trace y.isIntegral_coe
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨_, hi⟩ : 𝓞 F)
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add, map_add]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg, map_neg]; exact neg_mem h

theorem exists_coord_field (hd : Module.finrank F E = 2) (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e) (hI : ∀ z : Af F ⊗[F] E, z * z = z → z ∈ intT F E)
    (e : AF F ⊗[F] E) (h1 : e * e = e) (h2 : e * sigR (AF F) σ e = 0) (v : HeightOneSpectrum (𝓞 F)) (α : Af F)
    (hv : evalV F v α = 1) (hv' : ∀ w, w ≠ v → evalV F w α = 0)
    (h3 : e + sigR (AF F) σ e = algebraMap (AF F) _ (pairA F 0 α)) :
    ∃ (π : Af F ⊗[F] E →+* Fv F v) (s : Fv F v → AF F ⊗[F] E), (∀ x, s (π (finT F E x)) = e * x) ∧
      (∀ a, π (finT F E (s a)) = a) ∧ (∀ x, finT F E (s (π x)) = finT F E e * x) ∧
      (∀ x, finT F E e * x ∈ intT F E ↔ π x ∈ Formalism.UG.Ov F v) ∧
      ∀ x : F, π (finT F E (inclR (F := F) (AF F) (algebraMap F E x))) = algebraMap F (Fv F v) x := by
  have tA := GlobalTheory.FockCompare.SymplVal.trace_tensor hd σ hσ hf (AF F)
  have tf := GlobalTheory.FockCompare.SymplVal.trace_tensor hd σ hσ hf (Af F)
  have tt : ∀ z, Algebra.trace (Af F) (Af F ⊗[F] E) (finT F E z) = sndA F (Algebra.trace (AF F) _ z) := fun z => by
    apply alg_inj (F := F) (E := E)
    rw [tf, ← finT_alg, tA, RingHom.map_add, finT_sig]
  have g1 : finT F E e * finT F E e = finT F E e := by rw [← RingHom.map_mul, h1]
  have g2 : finT F E e * sigR (Af F) σ (finT F E e) = 0 := by
    rw [← finT_sig, ← RingHom.map_mul, h2, RingHom.map_zero]
  have g3 : finT F E e + sigR (Af F) σ (finT F E e) = algebraMap (Af F) _ α := by
    rw [← finT_sig, ← RingHom.map_add, h3]; rfl
  have k := fun b => trace_idem_mul (alg_inj _) _ tf g3 b
  obtain ⟨π, hπ⟩ := exists_hom (alg_inj _) _ tf g1 g2 g3 (evalV F v) hv
  have p3 : ∀ x, finT F E e * algebraMap (Af F) _ (singleV F v (π x)) = finT F E e * x := fun x => by
    rw [hπ, single_evalV hv hv']
    exact idem_mul_trace _ tf g1 g2 g3 x
  refine ⟨π, fun a => e * algebraMap (AF F) _ (pairA F 0 (singleV F v a)), fun x => ?_,
    fun a => ?_, fun x => ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · refine Eq.trans ?_ (idem_mul_trace _ tA h1 h2 h3 x)
    beta_reduce
    rw [hπ, single_evalV hv hv', ← RingHom.map_mul, tt]
    congr 2
    exact Prod.ext (zero_mul _).symm rfl
  · rw [hπ, RingHom.map_mul, ← mul_assoc, g1, finT_alg, k, map_mul, hv, mul_one]
    exact evalV_single v a
  · rw [RingHom.map_mul, finT_alg]
    exact p3 x
  · rw [hπ]; exact trace_mem v h
  · rw [← p3]
    exact mul_mem_intT (hI _ g1) (AddSubgroup.subset_closure ⟨_, single_mem h, 1, rfl⟩)
  · have : finT F E (inclR (F := F) (AF F) (algebraMap F E x)) = algebraMap (Af F) _ (algebraMap F (Af F) x) := by
      change (sndA F 1) ⊗ₜ[F] (algebraMap F E x) = (algebraMap F (Af F) x) ⊗ₜ 1
      rw [map_one, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [this, hπ, k, map_mul, hv, mul_one, AlgHom.commutes]

end Field

theorem exists_coord : ∀ {D : D7} (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v) (s : Fv D.host.F v → Formalism.L2.Theta.AE D), (∀ x, s (π (finPart D x)) = e * x) ∧ (∀ a, π (finPart D (s a)) = a) ∧ (∀ x, finPart D (s (π x)) = finPart D e * x) ∧ (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) ∧ ∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) = algebraMap D.host.F (Fv D.host.F v) x := by
  rintro D e ⟨h1, h2, v, ε, ⟨α, rfl, hv, hv'⟩, h3⟩
  exact ⟨v, exists_coord_field D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e) (fun e he => (D.sp.cm.fixed e).1 he)
    (GlobalTheory.AdIdem.idempotent_mem_intAE D) e h1 h2 v α hv hv' h3⟩

end GlobalTheory.SplitCoord

end
