import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomVal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

namespace GlobalTheory.TamCnt.LocLift

open MassDataLevelSSteps.EvalVW MassDataLevelSSteps.EvalVSpec

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] {j : R' →ₗ[F] R} {n : ℕ}

def glue (hj : ∀ x y, j (x * y) = j x * j y) : (R' ⊗[F] E) × (R ⊗[F] E) →+* R ⊗[F] E where
  toFun p := Jt j p.1 + (1 - eps (E := E) j) * p.2
  map_one' := by simp [eps]
  map_zero' := by simp
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Jt_mul hj]
    have h1 := eps_mul_Jt (E := E) hj p.1
    have h2 := eps_mul_Jt (E := E) hj q.1
    have h3 := eps_mul_eps (E := E) hj
    linear_combination q.2 * h1 + p.2 * h2 - p.2 * q.2 * h3

theorem det_secM (hj : ∀ x y, j (x * y) = j x * j y) (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) (hA : A.det = 1) :
    (secM j A).det = 1 := by
  let P : Matrix (Fin n) (Fin n) ((R' ⊗[F] E) × (R ⊗[F] E)) :=
    Matrix.of fun a b => (A a b, (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b)
  have h0 : secM j A = (glue hj).mapMatrix P := by
    ext a b
    simp [secM, glue, P]
  have h1 : P.det = 1 := by
    refine Prod.ext ?_ ?_
    · have := (RingHom.fst (R' ⊗[F] E) (R ⊗[F] E)).map_det P
      refine this.trans ?_
      exact hA
    · have := (RingHom.snd (R' ⊗[F] E) (R ⊗[F] E)).map_det P
      refine this.trans ?_
      exact Matrix.det_one
  rw [h0, ← RingHom.map_det, h1, map_one]

theorem Jt_mul_right (φ : R →ₐ[F] R') (hφ : ∀ x y, j x * y = j (x * φ y)) (x : R' ⊗[F] E) (y : R ⊗[F] E) :
    Jt j x * y = Jt j (x * Algebra.TensorProduct.map φ (AlgHom.id F E) y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, Jt_tmul, Jt_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, hφ]
      rfl
    | add y z hy hz => rw [mul_add, hy, hz, map_add, mul_add, map_add]
  | add x z hx hz => rw [add_mul, map_add, add_mul, hx, hz, map_add]

theorem secM_sub_one (hj : ∀ x y, j (x * y) = j x * j y) (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) :
    secM j A - 1 = (A - 1).map (Jt j) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [secM, eps]
    ring
  · simp [secM, h]

theorem secM_sub_one_mulVec (hj : ∀ x y, j (x * y) = j x * j y) (φ : R →ₐ[F] R')
    (hφ : ∀ x y, j x * y = j (x * φ y)) (A : Matrix (Fin n) (Fin n) (R' ⊗[F] E)) (y : Fin n → R ⊗[F] E) :
    (secM j A - 1) *ᵥ y =
      fun a => Jt j (((A - 1) *ᵥ fun b => Algebra.TensorProduct.map φ (AlgHom.id F E) (y b)) a) := by
  rw [secM_sub_one hj]
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, Jt_mul_right φ hφ]

theorem genLat_map (f : R' →ₗ[F] R) (S' : Set R') (S : Set R) (hS : ∀ a ∈ S', f a ∈ S) (L : Set (Fin n → E))
    {y : Fin n → R' ⊗[F] E} (hy : y ∈ genLat F R' S' L) : (fun a => Jt f (y a)) ∈ genLat F R S L := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨f a, hS a ha, x, hx, rfl⟩
  | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, map_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx

theorem map_eq_Jt (φ : R →ₐ[F] R') (y : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) y = Jt φ.toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x z hx hz => rw [map_add, map_add, hx, hz]

end Gen

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

open Classical in
theorem singleL_mul_right (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) (y : Af F) :
    singleL v x * y = singleL v (x * evalV F v y) := by
  rw [mul_comm, mul_comm x]
  exact (RestrictedProduct.mul_single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x y).symm

open Classical in
theorem singleL_mem (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) (hx : x ∈ v.adicCompletionIntegers F) :
    singleL v x ∈ intAf F := by
  intro w
  by_cases h : w = v
  · subst h
    rw [evalV_singleL]; exact hx
  · have : evalV F w (singleL v x) = 0 :=
      RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) x h
    rw [this]; exact zero_mem _

def singleA (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F :=
  (LinearMap.inr F (Ainf F) (Af F)).comp (singleL v)

theorem singleA_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    singleA v (x * y) = singleA v x * singleA v y :=
  Prod.ext (mul_zero (0 : Ainf F)).symm (singleL_mul v x y)

theorem snd_Jt (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (Jt (singleA v) x) = Jt (singleL v) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x z hx hz => rw [map_add, map_add, hx, hz, map_add]

theorem map_snd_secM (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) :
    (secM (singleA v) A).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) = secM (singleL v) A := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [secM, eps, snd_Jt]
  · simp [secM, h, snd_Jt]

theorem map_eval_secM (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) :
    (secM (singleL v) A).map (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) = A := by
  have h0 : ∀ x : Fv F v ⊗[F] E,
      Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Jt (singleL v) x) = x :=
    fun x => tensMap_Jt (evalV F v) (evalV_singleL v) x
  ext a b
  by_cases h : a = b
  · subst h
    simp [secM, eps, h0]
  · simp [secM, h, h0]

theorem secM_sub_one_mem (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
    (L L' : Set (Fin M → E)) (hA : ∀ y ∈ compLat v L, (A - 1) *ᵥ y ∈ compLat v L') :
    ∀ y ∈ latHat F E L, (secM (singleL v) A - 1) *ᵥ y ∈ latHat F E L' := by
  intro y hy
  rw [secM_sub_one_mulVec (singleL_mul v) (evalV F v) (singleL_mul_right v)]
  refine genLat_map (singleL v) _ (intAf F) (singleL_mem v) L' (hA _ ?_)
  simp only [map_eq_Jt]
  exact genLat_map (evalV F v).toLinearMap (intAf F) _ (fun a ha => ha v) L hy

theorem secM_mem (v : HeightOneSpectrum (𝓞 F)) (A : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E))
    (L : Set (Fin M → E)) (hA : ∀ y ∈ compLat v L, A *ᵥ y ∈ compLat v L) :
    ∀ y ∈ latHat F E L, secM (singleL v) A *ᵥ y ∈ latHat F E L := by
  intro y hy
  have h := secM_sub_one_mem v A L L (fun z hz => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; exact sub_mem (hA z hz) hz) y hy
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h
  simpa using add_mem h hy

end Adelic

end GlobalTheory.TamCnt.LocLift

namespace GlobalTheory.TamCnt

open MassDataLevelSSteps.EvalVW MassDataLevelSSteps.EvalVSpec LocLift

theorem exists_congG_locHom_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (g : GL (Fin M) (Fv F v ⊗[F] E)) (hg : g ∈ locCong σ J Λ v k) :
    ∃ h ∈ congG σ J Λ v k, locHom σ J v h = g := by
  let h0 : HA (AF F) σ J := secHA σ J (singleA_mul v) (⟨g, hg.1⟩ : HR (Fv F v) σ J)
  have hdet : h0 ∈ SUAdelic σ J := by
    refine MonoidHom.mem_ker.2 (Units.ext ?_)
    exact det_secM (singleA_mul v) _ hg.2.1
  have hfin : finMat σ J h0 = secM (singleL v) (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) :=
    map_snd_secM v _
  refine ⟨⟨h0, hdet⟩, ⟨fun y => ⟨fun hy => ?_, fun hy => ?_⟩, ?_⟩, Units.ext ?_⟩
  · change finMat σ J h0 *ᵥ y ∈ _
    rw [hfin]
    exact secM_mem v _ _ (fun z hz => (hg.2.2.1 z).1 hz) y hy
  · change finMat σ J h0 *ᵥ y ∈ _ at hy
    rw [hfin] at hy
    have := secM_mem v _ _ (fun z hz => ((inv_mem hg : g⁻¹ ∈ locCong σ J Λ v k).2.2.1 z).1 hz) _ hy
    rwa [Matrix.mulVec_mulVec, ← secM_mul (singleL_mul v), Units.inv_mul, secM_one (singleL_mul v),
      Matrix.one_mulVec] at this
  · change ∀ y ∈ _, (finMat σ J h0 - 1) *ᵥ y ∈ _
    rw [hfin]
    exact secM_sub_one_mem v _ _ _ hg.2.2.2
  · rw [locHom_val]
    change (finMat σ J h0).map _ = _
    rw [hfin, map_eval_secM]

end GlobalTheory.TamCnt
