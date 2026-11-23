import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeElementaryDivisors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfValued

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix Formalism.L2.Theta
  Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.SplitHeckeLabel

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" F => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F

theorem evalV_singleV_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_singleV_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem af_ext {a b : 𝔸 F} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  RestrictedProduct.ext _ _ h

theorem singleV_mem_intAf (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletionIntegers F) :
    singleV F v (y : Fv F v) ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_singleV_same]; exact y.2
  · rw [evalV_singleV_ne v _ hw]; exact zero_mem _

variable (F E) in

def intA : AddSubgroup ((𝔸 F) ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

theorem mul_mem_intAf {a b : 𝔸 F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun w => by
  rw [map_mul]; exact mul_mem (ha w) (hb w)

theorem one_mem_intAf : (1 : 𝔸 F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _

theorem tmul_mem_intA {a : 𝔸 F} (ha : a ∈ intAf F) (x : 𝓞 E) : a ⊗ₜ[F] (x : E) ∈ intA F E :=
  AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩

theorem mul_mem_intA {x y : (𝔸 F) ⊗[F] E} (hx : x ∈ intA F E) (hy : y ∈ intA F E) : x * y ∈ intA F E := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intA F E) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact tmul_mem_intA (mul_mem_intAf ha hb) (u * v)
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem smul_mem_latHat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {x : (𝔸 F) ⊗[F] E} {y : Fin n → (𝔸 F) ⊗[F] E}
    (hx : x ∈ intA F E) (hy : y ∈ latHat F E (L : Set (Fin n → E))) :
    x • y ∈ latHat F E (L : Set (Fin n → E)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, w, hw, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, mul_mem_intAf ha hb, u • w, L.smul_mem u hw, ?_⟩
      funext i
      rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_smul]; exact neg_mem h

theorem trace_field (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  obtain ⟨a, ha⟩ := hf (e + σ e) (by rw [map_add, hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h2, map_add, h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

theorem trace_tmul (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem trace_tensor (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e)
    (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]; ring
  | tmul a e =>
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [trace_tmul, h4, ← TensorProduct.tmul_add, ← trace_field h2 σ hσ hf, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]

theorem trace_mem_intAf {z : (𝔸 F) ⊗[F] E} (hz : z ∈ intA F E) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (Algebra.trace (𝔸 F) ((𝔸 F) ⊗[F] E) z) ∈ v.adicCompletionIntegers F := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    rw [trace_tmul, map_mul, AlgHom.commutes]
    refine mul_mem (ha v) ?_
    have hi : IsIntegral ℤ (Algebra.trace F E (u : E)) := Algebra.isIntegral_trace u.isIntegral_coe
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨_, hi⟩ : 𝓞 F)
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [map_add, map_add]; exact add_mem h1 h2
  | neg y _ h => rw [map_neg, map_neg]; exact neg_mem h

theorem exists_component (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e)
    (v : HeightOneSpectrum (𝓞 F)) (e : (𝔸 F) ⊗[F] E) (α : 𝔸 F) (h1 : e * e = e) (h0 : e * sigR (𝔸 F) σ e = 0)
    (hs : e + sigR (𝔸 F) σ e = algebraMap (𝔸 F) _ α) (hv : evalV F v α = 1)
    (hw : ∀ w, w ≠ v → evalV F w α = 0) :
    ∃ φ : (𝔸 F) ⊗[F] E →+* Fv F v, (∀ x y, e * x = e * y ↔ φ x = φ y) ∧
      (∀ a : 𝔸 F, φ (algebraMap (𝔸 F) _ a) = evalV F v a) ∧
      ∀ x, e * x ∈ intA F E → φ x ∈ v.adicCompletionIntegers F := by
  set c := sigR (𝔸 F) σ with hc
  set tr := Algebra.trace (𝔸 F) ((𝔸 F) ⊗[F] E) with htr
  have inj : Function.Injective (algebraMap (𝔸 F) ((𝔸 F) ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  have ht : ∀ x, algebraMap (𝔸 F) _ (tr (e * x)) = e * x + c e * c x := fun x => by
    rw [htr, trace_tensor h2 σ hσ hf, map_mul]
  have hcc : c e * c e = c e := by rw [← map_mul, h1]
  have hca : ∀ a : 𝔸 F, c (algebraMap (𝔸 F) _ a) = algebraMap (𝔸 F) _ a := fun a => by
    change a ⊗ₜ[F] σ 1 = a ⊗ₜ[F] 1
    rw [map_one]
  have halg : ∀ a : 𝔸 F, tr (e * algebraMap (𝔸 F) _ a) = α * a := fun a => inj (by
    rw [ht, hca, map_mul, ← hs, add_mul])
  have hsupp : ∀ x, tr (e * x) = α * tr (e * x) := fun x => inj (by
    rw [RingHom.map_mul, ht, ← hs]
    linear_combination (-x) * h1 - (c x) * hcc - (x + c x) * h0)
  let φ : (𝔸 F) ⊗[F] E →+* Fv F v :=
    { toFun := fun x => evalV F v (tr (e * x))
      map_one' := by
        have := halg 1
        rw [map_one] at this
        rw [this, mul_one, hv]
      map_mul' := fun x y => by
        rw [← map_mul]
        congr 1
        apply inj
        rw [RingHom.map_mul, ht, ht, ht, map_mul]
        linear_combination (-(x * y)) * h1 - (c x * c y) * hcc - (x * c y + c x * y) * h0
      map_zero' := by rw [mul_zero, map_zero, map_zero]
      map_add' := fun x y => by rw [mul_add, map_add, map_add] }
  refine ⟨φ, fun x y => ⟨fun h => ?_, fun h => ?_⟩, fun a => ?_, fun x hx => trace_mem_intAf hx v⟩
  · change evalV F v (tr (e * x)) = evalV F v (tr (e * y))
    rw [h]
  · have h3 : tr (e * x) = tr (e * y) := af_ext fun w => by
      by_cases hwv : w = v
      · subst hwv; exact h
      · rw [hsupp x, hsupp y, map_mul (evalV F w), map_mul (evalV F w), hw w hwv, zero_mul, zero_mul]
    have h4 := (ht x).symm.trans ((congrArg _ h3).trans (ht y))
    linear_combination e * h4 - (x - y) * h1 - (c x - c y) * h0
  · change evalV F v (tr (e * _)) = _
    rw [halg, map_mul, hv, one_mul]

theorem exists_local_lattice {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F))
    (φ : (𝔸 F) ⊗[F] E →+* Fv F v) (hφa : ∀ a : 𝔸 F, φ (algebraMap (𝔸 F) _ a) = evalV F v a)
    (hφi : ∀ x ∈ intA F E, φ x ∈ v.adicCompletionIntegers F) :
    ∃ Λ : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v), Λ.FG ∧
      Submodule.span (Fv F v) (Λ : Set (Fin n → Fv F v)) = ⊤ ∧
      ∀ w, w ∈ Λ ↔ ∃ y ∈ latHat F E (L : Set (Fin n → E)), w = φ ∘ y := by
  classical
  set ψ : E →+* Fv F v := φ.comp (inclR (𝔸 F)) with hψ
  have hψi : ∀ x : 𝓞 E, ψ (x : E) ∈ v.adicCompletionIntegers F := fun x => hφi _ (tmul_mem_intA one_mem_intAf x)
  have htm : ∀ (a : 𝔸 F) (x : E), φ (a ⊗ₜ[F] x) = evalV F v a * ψ x := fun a x => by
    rw [← hφa]
    change _ = φ (a ⊗ₜ[F] 1) * φ (1 ⊗ₜ[F] x)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  obtain ⟨T, hT⟩ := hfg
  set Λ := Submodule.span (v.adicCompletionIntegers F) ((fun x : Fin n → E => ψ ∘ x) '' (T : Set (Fin n → E)))
    with hΛ
  have hL : ∀ x ∈ L, ψ ∘ x ∈ Λ := by
    intro x hx
    rw [← hT] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : ψ ∘ (0 : Fin n → E) = 0 := funext fun i => map_zero ψ
      rw [this]; exact zero_mem _
    | add x y _ _ h1 h2 =>
      have : ψ ∘ (x + y) = ψ ∘ x + ψ ∘ y := funext fun i => map_add ψ _ _
      rw [this]; exact add_mem h1 h2
    | smul r x _ h =>
      have : ψ ∘ (r • x) = (⟨ψ r, hψi r⟩ : v.adicCompletionIntegers F) • (ψ ∘ x) := funext fun i => map_mul ψ _ _
      rw [this]; exact Λ.smul_mem _ h
  refine ⟨Λ, Submodule.fg_span (T.finite_toSet.image _), ?_, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have key : ∀ x : Fin n → E, ψ ∘ x ∈ Submodule.span (Fv F v) (Λ : Set (Fin n → Fv F v)) := by
      intro x
      have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hsp ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (hL x hx)
      | zero =>
        have : ψ ∘ (0 : Fin n → E) = 0 := funext fun i => map_zero ψ
        rw [this]; exact zero_mem _
      | add x y _ _ h1 h2 =>
        have : ψ ∘ (x + y) = ψ ∘ x + ψ ∘ y := funext fun i => map_add ψ _ _
        rw [this]; exact add_mem h1 h2
      | smul r x _ h =>
        have : ψ ∘ (r • x) = ψ r • (ψ ∘ x) := funext fun i => map_mul ψ _ _
        rw [this]; exact Submodule.smul_mem _ _ h
    rw [eq_top_iff, ← (Pi.basisFun (Fv F v) (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : Pi.basisFun (Fv F v) (Fin n) i = ψ ∘ (Pi.single i 1 : Fin n → E) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [this]
    exact key _
  · induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      exact ⟨fun i => (1 : 𝔸 F) ⊗ₜ[F] x i,
        AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, hT ▸ Submodule.subset_span hx, rfl⟩, rfl⟩
    | zero => exact ⟨0, zero_mem _, funext fun i => (map_zero φ).symm⟩
    | add x y _ _ h1 h2 =>
      obtain ⟨x', hx', rfl⟩ := h1
      obtain ⟨y', hy', rfl⟩ := h2
      exact ⟨x' + y', add_mem hx' hy', funext fun i => (map_add φ _ _).symm⟩
    | smul r x _ h =>
      obtain ⟨x', hx', rfl⟩ := h
      refine ⟨(singleV F v (r : Fv F v) ⊗ₜ[F] ((1 : 𝓞 E) : E)) • x',
        smul_mem_latHat L (tmul_mem_intA (singleV_mem_intAf v r) 1) hx', funext fun i => ?_⟩
      change (r : Fv F v) * φ (x' i) = φ ((singleV F v (r : Fv F v) ⊗ₜ[F] (1 : E)) * x' i)
      rw [map_mul, htm, map_one, mul_one, evalV_singleV_same]
  · rintro ⟨y, hy, rfl⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have : (φ ∘ fun i => a ⊗ₜ[F] x i) = (⟨evalV F v a, ha v⟩ : v.adicCompletionIntegers F) • (ψ ∘ x) :=
        funext fun i => htm a (x i)
      rw [this]; exact Λ.smul_mem _ (hL x hx)
    | zero =>
      have : φ ∘ (0 : Fin n → (𝔸 F) ⊗[F] E) = 0 := funext fun i => map_zero φ
      rw [this]; exact zero_mem _
    | add x y _ _ h1 h2 =>
      have : φ ∘ (x + y) = φ ∘ x + φ ∘ y := funext fun i => map_add φ _ _
      rw [this]; exact add_mem h1 h2
    | neg x _ h =>
      have : φ ∘ (-x) = -(φ ∘ x) := funext fun i => map_neg φ _
      rw [this]; exact neg_mem h

theorem comp_mulVec {n : ℕ} {A K : Type} [CommRing A] [CommRing K] (φ : A →+* K) (m : Matrix (Fin n) (Fin n) A)
    (y : Fin n → A) : φ ∘ m.mulVec y = (m.map φ).mulVec (φ ∘ y) :=
  funext fun i => RingHom.map_mulVec φ m y i

theorem exists_divisor_basis (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e)
    (v : HeightOneSpectrum (𝓞 F)) (e : (𝔸 F) ⊗[F] E) (α : 𝔸 F) (h1 : e * e = e) (h0 : e * sigR (𝔸 F) σ e = 0)
    (hs : e + sigR (𝔸 F) σ e = algebraMap (𝔸 F) _ α) (hv : evalV F v α = 1)
    (hw : ∀ w, w ≠ v → evalV F w α = 0) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ e * inclR (𝔸 F) ((x : E)⁻¹) ∉ intA F E))
    (ϖ : 𝓞 E) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) {n k : ℕ} (hk : k ≤ n)
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (m m' : Matrix (Fin n) (Fin n) ((𝔸 F) ⊗[F] E)) (hm : m * m' = 1)
    (hin : ∀ y ∈ latHat F E (L : Set (Fin n → E)), (fun a => e * m.mulVec y a) ∈ latHat F E (L : Set (Fin n → E)))
    (hout : ∀ y ∈ latHat F E (L : Set (Fin n → E)), ∃ z ∈ latHat F E (L : Set (Fin n → E)),
      (fun a => e * (inclR (𝔸 F) (ϖ : E) * y a)) = fun a => e * m.mulVec z a)
    (u u' : (𝔸 F) ⊗[F] E) (hu : u ∈ intA F E) (hu' : u' ∈ intA F E) (huu : e * u * u' = e)
    (hdet : e * m.det = e * inclR (𝔸 F) (ϖ : E) ^ k * u) (d : Fin n → ℤ)
    (hd : ∀ i, d i = if i.1 < n - k then 0 else -1) :
    ∃ B : Matrix (Fin n) (Fin n) ((𝔸 F) ⊗[F] E),
      (∀ z : Fin n → (𝔸 F) ⊗[F] E, (∀ i, z i ∈ intA F E) →
        (fun a => e * B.mulVec z a) ∈ latHat F E (L : Set (Fin n → E))) ∧
      (∀ y ∈ latHat F E (L : Set (Fin n → E)), ∃ z : Fin n → (𝔸 F) ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
        (fun a => e * y a) = fun a => e * B.mulVec z a) ∧
      (∀ y ∈ latHat F E (L : Set (Fin n → E)), ∃ z : Fin n → (𝔸 F) ⊗[F] E, (∀ i, z i ∈ intA F E) ∧
        (fun a => e * m'.mulVec y a) = fun a => e * B.mulVec (fun i => inclR (𝔸 F) ((ϖ : E) ^ d i) * z i) a) ∧
      (∀ z : Fin n → (𝔸 F) ⊗[F] E, (∀ i, z i ∈ intA F E) → ∃ y ∈ latHat F E (L : Set (Fin n → E)),
        (fun a => e * m'.mulVec y a) = fun a => e * B.mulVec (fun i => inclR (𝔸 F) ((ϖ : E) ^ d i) * z i) a) := by
  classical
  obtain ⟨φ, hφ, hφa, hφe⟩ := exists_component h2 σ hσ hf v e α h1 h0 hs hv hw
  have he : e ∈ intA F E := by
    have := (hP 1 one_ne_zero).not.1 ((Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
    simpa using this
  have hφi : ∀ x ∈ intA F E, φ x ∈ v.adicCompletionIntegers F := fun x hx => hφe x (mul_mem_intA he hx)
  have hφv : ∀ x y : Fin n → (𝔸 F) ⊗[F] E, ((fun a => e * x a) = fun a => e * y a) ↔ φ ∘ x = φ ∘ y := fun x y => by
    simp only [funext_iff, hφ, Function.comp_apply]
  let s : Fv F v → (𝔸 F) ⊗[F] E := fun t => algebraMap (𝔸 F) _ (singleV F v t)
  have hs1 : ∀ t, φ (s t) = t := fun t => by rw [hφa, evalV_singleV_same]
  have hsi : ∀ t : v.adicCompletionIntegers F, s t ∈ intA F E := fun t =>
    tmul_mem_intA (singleV_mem_intAf v t) 1
  have hφe' : ∀ x, φ x ∈ v.adicCompletionIntegers F → e * x ∈ intA F E := fun x hx => by
    rw [(hφ x (s (φ x))).2 (hs1 _).symm]
    exact mul_mem_intA he (hsi ⟨_, hx⟩)
  have hφ1 : φ e = 1 := by rw [← map_one φ, ← hφ, h1, mul_one]
  set ψ : E →+* Fv F v := φ.comp (inclR (𝔸 F)) with hψ
  obtain ⟨π, hπ, hπϖ⟩ := GlobalTheory.DegreeOneUniformiser.exists_irreducible_eq F E v P ψ
    (fun a => by
      have : inclR (𝔸 F) (algebraMap F E a) = algebraMap (𝔸 F) ((𝔸 F) ⊗[F] E) (algebraMap F _ a) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : E →ₐ[F] (𝔸 F) ⊗[F] E).commutes a
      rw [hψ, RingHom.comp_apply, this, hφa, AlgHom.commutes])
    (fun x => hφi _ (tmul_mem_intA one_mem_intAf x))
    (fun x hx => (hP x hx).trans (not_congr ⟨hφe _, hφe' _⟩)) ϖ hϖ hϖ2
  obtain ⟨Λ, hΛfg, hΛsp, hΛ⟩ := exists_local_lattice L hfg hsp v φ hφa hφi
  have hlat : ∀ x : Fin n → (𝔸 F) ⊗[F] E, φ ∘ x ∈ Λ → (fun a => e * x a) ∈ latHat F E (L : Set (Fin n → E)) :=
    fun x hx => by
      obtain ⟨y, hy, hxy⟩ := (hΛ _).1 hx
      rw [(hφv x y).2 hxy]
      exact smul_mem_latHat L he hy
  have huu' : φ u * φ u' = 1 := by
    have := congrArg φ huu
    rwa [map_mul, map_mul, hφ1, one_mul] at this
  let U : (v.adicCompletionIntegers F)ˣ :=
    ⟨⟨φ u, hφi u hu⟩, ⟨φ u', hφi u' hu'⟩, Subtype.ext huu', Subtype.ext ((mul_comm _ _).trans huu')⟩
  have hπ' : algebraMap (v.adicCompletionIntegers F) (Fv F v) π = ψ (ϖ : E) := hπϖ
  obtain ⟨B, hB1, hB2⟩ := GlobalTheory.LatticeMinuscule.lattice_elementary_divisors (v.adicCompletionIntegers F) (Fv F v) π hπ n k hk Λ hΛfg hΛsp
    (m.map φ) (m'.map φ) (by rw [← Matrix.map_mul, hm, Matrix.map_one _ (map_zero φ) (map_one φ)])
    (fun w hw => by
      obtain ⟨y, hy, rfl⟩ := (hΛ _).1 hw
      refine (hΛ _).2 ⟨_, hin y hy, ?_⟩
      rw [← comp_mulVec, ← hφv]
      funext a
      rw [← mul_assoc, h1])
    (fun w hw => by
      obtain ⟨y, hy, rfl⟩ := (hΛ _).1 hw
      obtain ⟨z, hz, hyz⟩ := hout y hy
      refine ⟨_, (hΛ _).2 ⟨z, hz, rfl⟩, ?_⟩
      rw [← comp_mulVec, ← (hφv _ _).1 hyz, hπ']
      funext a
      exact (map_mul φ _ _).symm)
    U (by
      have := congrArg φ hdet
      rw [map_mul, map_mul, map_mul, hφ1, one_mul, one_mul, map_pow, RingHom.map_det] at this
      rw [hπ']
      exact this)
  have hBφ : (B.map s).map φ = B := Matrix.ext fun i j => hs1 _
  have hz1 : ∀ z : Fin n → (𝔸 F) ⊗[F] E, φ ∘ (B.map s).mulVec z = B.mulVec (φ ∘ z) := fun z => by
    rw [comp_mulVec, hBφ]
  have hz2 : ∀ z : Fin n → (𝔸 F) ⊗[F] E, (φ ∘ fun i => inclR (𝔸 F) ((ϖ : E) ^ d i) * z i) = fun i =>
      algebraMap (v.adicCompletionIntegers F) (Fv F v) π ^ (if i.1 < n - k then (0 : ℤ) else -1) * φ (z i) :=
    fun z => funext fun i => by
      rw [hπ', ← hd, ← map_zpow₀]
      exact map_mul φ _ _
  refine ⟨B.map s, fun z hz => hlat _ ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · rw [hz1]
    exact (hB1 _).2 ⟨fun i => ⟨φ (z i), hφi _ (hz i)⟩, rfl⟩
  · obtain ⟨z, hz⟩ := (hB1 _).1 ((hΛ _).2 ⟨y, hy, rfl⟩)
    refine ⟨fun i => s (z i), fun i => hsi _, (hφv _ _).2 ?_⟩
    rw [hz1, hz]
    congr 1
    funext i
    exact (hs1 _).symm
  · obtain ⟨z, hz⟩ := (hB2 _).1 ⟨_, (hΛ _).2 ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨fun i => s (z i), fun i => hsi _, (hφv _ _).2 ?_⟩
    rw [hz1, comp_mulVec, hz, hz2]
    congr 1
    funext i
    rw [hs1]
    rfl
  · obtain ⟨x, hx, hxz⟩ := (hB2 _).2 ⟨fun i => ⟨φ (z i), hφi _ (hz i)⟩, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (hΛ _).1 hx
    refine ⟨y, hy, (hφv _ _).2 ?_⟩
    rw [hz1, comp_mulVec, hz2, ← hxz]
    rfl

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitLab_getD {n k i : ℕ} (hk : k ≤ n) (hi : i < n) :
    (splitLab n k).getD i 0 = if i < n - k then 0 else -1 := by
  unfold splitLab
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using h)]
    have : i - (n - k) < k := by omega
    simp [this]

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise (fun a b => b ≤ a) := by
  unfold splitLab
  rw [List.pairwise_append]
  refine ⟨List.pairwise_replicate.2 (Or.inr le_rfl), List.pairwise_replicate.2 (Or.inr le_rfl), fun a ha b hb => ?_⟩
  rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  norm_num

theorem suppF_inv {D : D7} (V : HSp D) (f : Formalism.L2.Theta.AE D) (g : GA D V) (hg : SuppF V f g) : SuppF V f g⁻¹ := by
  have h1 : f • (mt V g - 1) = mt V g - 1 := Matrix.ext hg
  have h2 : mt V g⁻¹ * mt V g = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h3 : mt V g⁻¹ - 1 = -(mt V g⁻¹ * (mt V g - 1)) := by rw [mul_sub, h2, mul_one, neg_sub]
  have h4 : f • (mt V g⁻¹ - 1) = mt V g⁻¹ - 1 := by rw [h3, smul_neg, ← Matrix.mul_smul, h1]
  exact fun i j => congrFun (congrFun h4 i) j

theorem exists_coord_lattice {D : D7} (V : HSp D) : ∃ L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
    (L : Set (Fin V.rank → D.host.E)) = L0c D V ∧ L.FG ∧
      Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
  let ι := V.frame.equivFun
  refine ⟨V.L0.map (ι.restrictScalars (𝓞 D.host.E)).toLinearMap, ?_, V.standardTuple_isLattice.fg.map _, ?_⟩
  · ext x
    rw [SetLike.mem_coe, Submodule.mem_map_equiv]
    change ι.symm x ∈ V.L0 ↔ ∑ i, x i • V.frame i ∈ V.L0
    rw [Module.Basis.equivFun_symm_apply]
  · have : ((V.L0.map (ι.restrictScalars (𝓞 D.host.E)).toLinearMap : Submodule _ _) : Set _) =
        ι.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem finPart_cA (D : D7) (x : Formalism.L2.Theta.AE D) :
    finPart D (cA D x) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul a e => rfl

theorem finPart_det {D : D7} (V : HSp D) (α : GA D V) (e u : Formalism.L2.Theta.AE D) (p : D.host.E) (k : ℕ)
    (h : e * (mt V α).det = e * incA D p ^ k * u) :
    finPart D e * (finMat D.sp.cm.sig V.gram α).det =
      finPart D e * inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) p ^ k * finPart D u := by
  have hinc : finPart D (incA D p) = inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) p := rfl
  have hd : finPart D (mt V α).det = (finMat D.sp.cm.sig V.gram α).det := RingHom.map_det (finPart D) (mt V α)
  rw [← hd, ← hinc, ← RingHom.map_pow, ← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_mul, h]

theorem divAt_inv {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (P : HeightOneSpectrum (𝓞 D.host.E))
    (he : Formalism.L2.NTheta.IsIdemAt e P) (ϖ : 𝓞 D.host.E) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (k : ℕ)
    (hk : k ≤ V.rank) (α : GA D V) (hα : Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α) :
    DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ := by
  obtain ⟨⟨h1, h0, v, ε, ⟨a, rfl, hv, hw⟩, hs⟩, hP⟩ := he
  obtain ⟨-, -, hin, hout, u, u', hu, hu', huu, hdet⟩ := hα
  obtain ⟨L, hL, hfg, hsp⟩ := exists_coord_lattice V
  refine ⟨by simp [splitLab, hk], ?_⟩
  have hm : finMat D.sp.cm.sig V.gram α * finMat D.sp.cm.sig V.gram α⁻¹ = 1 := by
    change (finHom V α).1 * (finHom V α⁻¹).1 = 1
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hinc : ∀ x, finPart D (incA D x) = inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) x := fun x => rfl
  have key := exists_divisor_basis D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e)
    (fun e he => (D.sp.cm.fixed e).1 he) v (finPart D e) a (by rw [← RingHom.map_mul, h1])
    (by rw [← finPart_cA, ← RingHom.map_mul, h0, RingHom.map_zero])
    (by rw [← finPart_cA, ← RingHom.map_add, hs]; rfl) hv hw P
    (fun x hx => by rw [hP x hx, RingHom.map_mul, hinc]; rfl) ϖ hϖ hϖ2 hk L hfg hsp _ _ hm
    (by rw [hL]; exact hin) (by rw [hL]; exact hout) (finPart D u) (finPart D u') hu hu'
    (by rw [← RingHom.map_mul, ← RingHom.map_mul, huu])
    (finPart_det V α e u _ k hdet)
    (fun i => (splitLab V.rank k).getD i.1 0) (fun i => splitLab_getD hk i.2)
  rw [hL] at key
  exact key

theorem splitDict : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SplitDict (V := V) J χ Sb := by
  intro D V J χ Sb P k R h
  obtain ⟨e, ϖ, α, hS, he, hϖ, hϖ2, hk, hJ, hχ, hα, hR, hC⟩ := h
  exact ⟨e, e + cA D e, ϖ, α⁻¹, hS, Or.inl ⟨he, rfl⟩, hϖ, hϖ2, splitLab_pairwise _ _, hJ, hχ,
    suppF_inv V _ α hα.2.1, divAt_inv V e P he ϖ hϖ hϖ2 k hk α hα, hR, hC⟩

end GlobalTheory.SplitHeckeLabel
