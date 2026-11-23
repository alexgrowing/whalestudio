import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.GoodLat
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.GlobalFields.Adele.Approximation
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualB

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

namespace LatRepA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {nS nT : ℕ}

set_option linter.unusedSectionVars false

theorem exists_dualBasis {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} (h : GoodLat Λ) :
    ∃ (k : ℕ) (y : Fin k → Matrix (Fin nT) (Fin nS) E) (l : Fin k → Matrix (Fin nT) (Fin nS) E →ₗ[F] F),
      (∀ j, y j ∈ Λ) ∧ (∀ j, ∀ x ∈ Λ, ∃ o : 𝓞 F, l j x = o) ∧ ∀ x, x = ∑ j, l j x • y j := by
  have : IsScalarTower (𝓞 F) (𝓞 E) (Matrix (Fin nT) (Fin nS) E) := inferInstance
  let M : Submodule (𝓞 F) (Matrix (Fin nT) (Fin nS) E) := Λ.restrictScalars (𝓞 F)
  have hfin : Module.Finite (𝓞 F) M := by
    have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 h.fg
    have : Module.Finite (𝓞 F) Λ := Module.Finite.trans (𝓞 E) Λ
    exact this
  have htf : Module.IsTorsionFree (𝓞 F) (Matrix (Fin nT) (Fin nS) E) :=
    inferInstanceAs (Module.IsTorsionFree (𝓞 F) (Fin nT → Fin nS → E))
  have : Module.FinitePresentation (𝓞 F) M := Module.finitePresentation_of_finite _ _
  obtain ⟨k, f, g, e⟩ := Module.Flat.exists_factorization_of_finitePresentation (LinearMap.id (R := 𝓞 F) (M := M))
  have hu : ∀ (V : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
      (s : nonZeroDivisors (𝓞 F)), IsUnit (algebraMap (𝓞 F) (Module.End (𝓞 F) V) s) := by
    intro V _ _ _ _ s
    rw [Module.End.isUnit_iff]
    have hs : ((s : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
    have e : ∀ v : V, algebraMap (𝓞 F) (Module.End (𝓞 F) V) s v = ((s : 𝓞 F) : F) • v := fun v =>
      (algebraMap_smul F (s : 𝓞 F) v).symm
    refine ⟨fun a b hab => ?_, fun v => ⟨((s : 𝓞 F) : F)⁻¹ • v, by rw [e, smul_smul, mul_inv_cancel₀ hs, one_smul]⟩⟩
    rw [e, e] at hab
    exact smul_right_injective V hs hab
  have hloc : IsLocalizedModule (nonZeroDivisors (𝓞 F)) M.subtype := by
    refine ⟨hu _, fun x => ?_, fun hx => ⟨1, by rw [Subtype.ext hx]⟩⟩
    obtain ⟨m, hm, hx⟩ := h.den x
    refine ⟨(⟨_, hx⟩, ⟨(m : 𝓞 F), mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hm.ne')⟩), ?_⟩
    show (m : 𝓞 F) • x = m • x
    rw [Nat.cast_smul_eq_nsmul]
  let l₀ : Fin k → Matrix (Fin nT) (Fin nS) E →ₗ[𝓞 F] F := fun j => IsLocalizedModule.lift (nonZeroDivisors (𝓞 F)) M.subtype
    ((Algebra.linearMap (𝓞 F) F) ∘ₗ (Finsupp.lapply j) ∘ₗ f) (hu F)
  have hl₀ : ∀ j (x : M), l₀ j x = f x j := fun j x =>
    IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 F)) M.subtype _ (hu F) x
  let l : Fin k → Matrix (Fin nT) (Fin nS) E →ₗ[F] F := fun j => (l₀ j).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 F)) F
  refine ⟨k, fun j => (g (Finsupp.single j 1) : M), l, fun j => (g (Finsupp.single j 1)).2,
    fun j x hx => ⟨f ⟨x, hx⟩ j, hl₀ j ⟨x, hx⟩⟩, fun x => ?_⟩
  have hM : ∀ x : M, (x : Matrix (Fin nT) (Fin nS) E) = ∑ j, l j x • ((g (Finsupp.single j 1) : M) : Matrix (Fin nT) (Fin nS) E) := by
    intro x
    have h1 : x = g (f x) := LinearMap.congr_fun e x
    conv_lhs => rw [h1, ← (f x).univ_sum_single, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show l j x = f x j from hl₀ j x, ← Finsupp.smul_single_one, map_smul, Submodule.coe_smul]
    exact (algebraMap_smul F _ _).symm
  obtain ⟨m, hm, hx⟩ := h.den x
  have h2 := hM ⟨_, hx⟩
  have e2 : m • x = (m : F) • x := by rw [Nat.cast_smul_eq_nsmul]
  simp only [e2, map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum] at h2
  exact smul_right_injective _ (Nat.cast_ne_zero.2 hm.ne' : (m : F) ≠ 0) h2

section coord

variable (R : Type) [CommRing R] [Algebra F R]

def cE (f : E →ₗ[F] F) : R ⊗[F] E →ₗ[R] R :=
  (Algebra.TensorProduct.rid F R R).toLinearMap ∘ₗ f.baseChange R

variable {R}

theorem cE_tmul (f : E →ₗ[F] F) (a : R) (e : E) : cE R f (a ⊗ₜ[F] e) = f e • a := by
  simp [cE]

def sngG {X : Type} [Zero X] (i : Fin nT) (k : Fin nS) (x : X) : Matrix (Fin nT) (Fin nS) X :=
  Matrix.of fun a b => if a = i ∧ b = k then x else 0

theorem sum_sngG {X : Type} [AddCommMonoid X] (z : Matrix (Fin nT) (Fin nS) X) :
    ∑ i, ∑ k, sngG i k (z i k) = z := by
  ext a b
  simp [sngG, Matrix.sum_apply, ite_and]

theorem sngG_add {X : Type} [AddCommMonoid X] (i : Fin nT) (k : Fin nS) (x y : X) :
    sngG i k (x + y) = sngG i k x + sngG i k y := by
  ext a b
  simp only [sngG, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem sngG_zero {X : Type} [AddCommMonoid X] (i : Fin nT) (k : Fin nS) : sngG i k (0 : X) = 0 := by
  ext a b
  simp [sngG]

def sng (i : Fin nT) (k : Fin nS) : E →ₗ[F] Matrix (Fin nT) (Fin nS) E where
  toFun e := sngG i k e
  map_add' x y := sngG_add i k x y
  map_smul' c x := by
    ext a b
    simp only [sngG, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

variable (F) in

def tm (a : R) (γ : Matrix (Fin nT) (Fin nS) E) : Matrix (Fin nT) (Fin nS) (R ⊗[F] E) :=
  γ.map fun e => a ⊗ₜ[F] e

theorem tm_add_left (a b : R) (γ : Matrix (Fin nT) (Fin nS) E) : tm F (a + b) γ = tm F a γ + tm F b γ := by
  ext i k
  simp [tm, TensorProduct.add_tmul]

theorem tm_sub_left (a b : R) (γ : Matrix (Fin nT) (Fin nS) E) : tm F (a - b) γ = tm F a γ - tm F b γ := by
  ext i k
  simp [tm, TensorProduct.sub_tmul]

theorem tm_zero_left (γ : Matrix (Fin nT) (Fin nS) E) : tm F (0 : R) γ = 0 := by
  ext i k
  simp [tm]

theorem tm_sum_right {ι : Type} (s : Finset ι) (a : R) (γ : ι → Matrix (Fin nT) (Fin nS) E) :
    tm F a (∑ j ∈ s, γ j) = ∑ j ∈ s, tm F a (γ j) := by
  ext i k
  simp [tm, Matrix.sum_apply, TensorProduct.tmul_sum]

theorem tm_smul_right (a : R) (c : F) (γ : Matrix (Fin nT) (Fin nS) E) : tm F a (c • γ) = tm F (c • a) γ := by
  ext i k
  simp [tm, TensorProduct.smul_tmul]

theorem tm_nsmul (n : ℕ) (a : R) (γ : Matrix (Fin nT) (Fin nS) E) : n • tm F a γ = tm F (n • a) γ := by
  induction n with
  | zero => simp [tm_zero_left]
  | succ n ih => rw [succ_nsmul, ih, succ_nsmul, tm_add_left]

variable (R) in

def coordM (l : Matrix (Fin nT) (Fin nS) E →ₗ[F] F) (z : Matrix (Fin nT) (Fin nS) (R ⊗[F] E)) : R :=
  ∑ i, ∑ k, cE R (l ∘ₗ sng i k) (z i k)

theorem coordM_add (l : Matrix (Fin nT) (Fin nS) E →ₗ[F] F) (x y : Matrix (Fin nT) (Fin nS) (R ⊗[F] E)) :
    coordM R l (x + y) = coordM R l x + coordM R l y := by
  simp [coordM, Finset.sum_add_distrib]

theorem coordM_zero (l : Matrix (Fin nT) (Fin nS) E →ₗ[F] F) : coordM R l 0 = 0 := by
  simp [coordM]

theorem coordM_neg (l : Matrix (Fin nT) (Fin nS) E →ₗ[F] F) (x : Matrix (Fin nT) (Fin nS) (R ⊗[F] E)) :
    coordM R l (-x) = -coordM R l x := by
  simp [coordM]

theorem coordM_tm (l : Matrix (Fin nT) (Fin nS) E →ₗ[F] F) (a : R) (γ : Matrix (Fin nT) (Fin nS) E) :
    coordM R l (tm F a γ) = l γ • a := by
  have h : l γ = ∑ i, ∑ k, l (sng (F := F) i k (γ i k)) := by
    conv_lhs => rw [← sum_sngG γ]
    simp only [map_sum]
    rfl
  rw [h, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [tm, Matrix.map_apply, cE_tmul, LinearMap.comp_apply]

theorem mat_induction {P : Matrix (Fin nT) (Fin nS) (R ⊗[F] E) → Prop} (h0 : P 0)
    (h1 : ∀ (a : R) (γ : Matrix (Fin nT) (Fin nS) E), P (tm F a γ)) (h2 : ∀ x y, P x → P y → P (x + y))
    (z : Matrix (Fin nT) (Fin nS) (R ⊗[F] E)) : P z := by
  rw [← sum_sngG z]
  refine Finset.sum_induction _ P h2 h0 fun i _ => Finset.sum_induction _ P h2 h0 fun k _ => ?_
  induction z i k using TensorProduct.induction_on with
  | zero => rw [sngG_zero]; exact h0
  | tmul a e =>
    convert h1 a (sngG i k e) using 1
    ext p q
    simp only [sngG, tm, Matrix.of_apply, Matrix.map_apply]
    split_ifs <;> simp
  | add a b ha hb => rw [sngG_add]; exact h2 _ _ ha hb

theorem eq_sum_coordM {m : ℕ} {y : Fin m → Matrix (Fin nT) (Fin nS) E} {l : Fin m → Matrix (Fin nT) (Fin nS) E →ₗ[F] F}
    (h : ∀ x, x = ∑ j, l j x • y j) (z : Matrix (Fin nT) (Fin nS) (R ⊗[F] E)) :
    z = ∑ j, tm F (coordM R (l j) z) (y j) := by
  induction z using mat_induction with
  | h0 => simp [coordM_zero, tm_zero_left]
  | h1 a x =>
    conv_lhs => rw [h x, tm_sum_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coordM_tm, tm_smul_right]
  | h2 a b ha hb =>
    conv_lhs => rw [ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coordM_add, tm_add_left]

theorem map_coordM {S : Type} [CommRing S] [Algebra F S] (f : R →ₐ[F] S) (l : Matrix (Fin nT) (Fin nS) E →ₗ[F] F)
    (z : Matrix (Fin nT) (Fin nS) (R ⊗[F] E)) :
    f (coordM R l z) = coordM S l (z.map (Algebra.TensorProduct.map f (AlgHom.id F E))) := by
  induction z using mat_induction with
  | h0 =>
    rw [coordM_zero, map_zero, Matrix.map_zero _ (map_zero _), coordM_zero]
  | h1 a γ =>
    have : (tm F a γ).map (Algebra.TensorProduct.map f (AlgHom.id F E)) = tm F (f a) γ := by
      ext i k
      simp [tm]
    rw [this, coordM_tm, coordM_tm, map_smul]
  | h2 a b ha hb =>
    rw [coordM_add, map_add, ha, hb, Matrix.map_add _ (map_add _), coordM_add]

end coord

theorem smul_ratWF (c : AF F) (γ : Matrix (Fin nT) (Fin nS) E) :
    algebraMap (AF F) (AEF F E) c • ratWF (F := F) γ = tm F c γ := by
  ext i k
  simp [ratWF, tm, Matrix.smul_apply, Matrix.map_apply, incAF, inclR, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul]

theorem intAf_eq : Formalism.MainNotions.StandardLattice.intAf F = (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (Af F)) := rfl

theorem tm_mem_latOF {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {β : Af F}
    (hβ : β ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F) {γ : Matrix (Fin nT) (Fin nS) E} (hγ : γ ∈ Λ) :
    tm F (pairA F 0 β) γ ∈ latOF F E nS nT Λ :=
  AddSubgroup.subset_closure ⟨β, hβ, γ, hγ, (smul_ratWF _ _).symm⟩

theorem fin_coord {l : Matrix (Fin nT) (Fin nS) E →ₗ[F] F} {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) :
    coordM (AF F) l u = pairA F 0 (coordM (AF F) l u).2 := by
  have h := map_coordM (fstA F) l u
  have h' : u.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 0 := hu
  rw [h', coordM_zero] at h
  exact Prod.ext h rfl

theorem pair_add (a b : Af F) : pairA F 0 a + pairA F 0 b = pairA F 0 (a + b) := Prod.ext (add_zero 0) rfl

theorem pair_nsmul (n : ℕ) (a : Af F) : n • pairA F 0 a = pairA F 0 (n • a) := by
  induction n with
  | zero => simp only [zero_nsmul]; rfl
  | succ n ih => rw [succ_nsmul, ih, pair_add, succ_nsmul]

theorem pair_sub (a b : Af F) : pairA F 0 a - pairA F 0 b = pairA F 0 (a - b) := Prod.ext (sub_zero 0) rfl

theorem pair_neg (a : Af F) : -pairA F 0 a = pairA F 0 (-a) := Prod.ext neg_zero rfl

theorem smul_pair (c : F) (a : Af F) : c • pairA F 0 a = pairA F 0 (algebraMap F (Af F) c * a) :=
  Prod.ext (smul_zero c) (Algebra.smul_def c a)

theorem algebraMap_int_mem (o : 𝓞 F) :
    algebraMap F (Af F) (o : F) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F :=
  fun v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v o

theorem coord_latOF {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {l : Matrix (Fin nT) (Fin nS) E →ₗ[F] F}
    (hl : ∀ x ∈ Λ, ∃ o : 𝓞 F, l x = o) {z : WOF F E nS nT} (hz : z ∈ latOF F E nS nT Λ) :
    ∃ β ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, coordM (AF F) l z = pairA F 0 β := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, γ, hγ, rfl⟩ := hy
    obtain ⟨o, ho⟩ := hl γ hγ
    refine ⟨algebraMap F (Af F) (o : F) * α, Subring.mul_mem _ (algebraMap_int_mem o) hα, ?_⟩
    rw [smul_ratWF, coordM_tm, ho, smul_pair]
  | zero => exact ⟨0, zero_mem _, by rw [coordM_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ea⟩ := hx
    obtain ⟨b, hb, eb⟩ := hy
    exact ⟨a + b, add_mem ha hb, by rw [coordM_add, ea, eb, pair_add]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, ea⟩ := hx
    exact ⟨-a, neg_mem ha, by rw [coordM_neg, ea, pair_neg]⟩

theorem nat_mul_mem (β : Af F) : ∃ N : ℕ, 0 < N ∧ N • β ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F := by
  obtain ⟨f, hf⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) β
  obtain ⟨m, hm, o, ho⟩ := Formalism.IndefR.Fin.PDB.exists_nat_mul_mem f
  refine ⟨m, hm, ?_⟩
  have e : m • β = m • (β - algebraMap F (Af F) f) + algebraMap F (Af F) ((o : 𝓞 F) : F) := by
    have : ((o : 𝓞 F) : F) = (m : F) * f := ho
    rw [this, map_mul, map_natCast, smul_sub, nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [e]
  exact add_mem (nsmul_mem hf m) (algebraMap_int_mem o)

section topo

attribute [local instance] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.topTens

theorem cont_coord (l : Matrix (Fin nT) (Fin nS) E →ₗ[F] F) :
    Continuous fun u : WOF F E nS nT => coordM (AF F) l u := by
  have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
  exact (IsModuleTopology.continuous_of_linearMap _).comp (continuous_id.matrix_elem i k)

theorem cont_sum {m : ℕ} (y : Fin m → Matrix (Fin nT) (Fin nS) E) :
    Continuous fun a : Fin m → AF F => ∑ j, algebraMap (AF F) (AEF F E) (a j) • ratWF (F := F) (y j) := by
  have : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  have : ContinuousAdd (AEF F E) := IsModuleTopology.toContinuousAdd (AF F) (AEF F E)
  have : ContinuousSMul (AF F) (AEF F E) := IsModuleTopology.toContinuousSMul (AF F) (AEF F E)
  refine continuous_finsetSum _ fun j _ => ?_
  refine continuous_matrix fun i k => ?_
  show Continuous fun a : Fin m → AF F => algebraMap (AF F) (AEF F E) (a j) * ratWF (F := F) (y j) i k
  simp only [← Algebra.smul_def]
  exact (continuous_apply j : Continuous fun a : Fin m → AF F => a j).smul
    (continuous_const : Continuous fun _ : Fin m → AF F => ratWF (F := F) (y j) i k)

end topo

end LatRepA

open LatRepA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {nS nT : ℕ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

theorem lat_fin {u : WOF F E nS nT} (hu : u ∈ latOF F E nS nT Λ) : u.map (infPartF F E) = 0 := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, _, γ, _, rfl⟩ := hz
    rw [smul_ratWF]
    ext i k
    show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) ((pairA F 0 α) ⊗ₜ[F] γ i k) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  | zero => exact Matrix.map_zero _ (map_zero _)
  | add x y _ _ hx hy => rw [Matrix.map_add _ (map_add _), hx, hy, add_zero]
  | neg x _ hx => rw [Matrix.map_neg _ (map_neg _), hx, neg_zero]

theorem lat_nhds (h : GoodLat Λ) :
    ∃ V ∈ 𝓝 (0 : WOF F E nS nT), ∀ u ∈ V, u.map (infPartF F E) = 0 → u ∈ latOF F E nS nT Λ := by
  obtain ⟨m, y, l, hy, _, e⟩ := exists_dualBasis (F := F) h
  refine ⟨⋂ j, (fun u : WOF F E nS nT => (coordM (AF F) (l j) u).2) ⁻¹'
    (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (Af F)), ?_, fun u hu hf => ?_⟩
  · refine IsOpen.mem_nhds (isOpen_iInter_of_finite fun j =>
      GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_snd.comp (cont_coord (l j)))) ?_
    simp only [Set.mem_iInter, Set.mem_preimage, coordM_zero]
    exact fun _ => zero_mem _
  · rw [Set.mem_iInter] at hu
    rw [eq_sum_coordM e u]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    rw [fin_coord hf]
    exact tm_mem_latOF (hu j) (hy j)

theorem lat_compact (h : GoodLat Λ) : IsCompact (latOF F E nS nT Λ : Set (WOF F E nS nT)) := by
  obtain ⟨m, y, l, hy, hl, e⟩ := exists_dualBasis (F := F) h
  let S : Set (AF F) := (fun β => pairA F 0 β) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (Af F))
  have hS : IsCompact S := (GroundTheory.Global.isCompact_integralFiniteAdeles (K := F)).image
    (continuous_const.prodMk continuous_id)
  have him : (latOF F E nS nT Λ : Set (WOF F E nS nT)) =
      (fun a : Fin m → AF F => ∑ j, algebraMap (AF F) (AEF F E) (a j) • ratWF (F := F) (y j)) '' Set.univ.pi fun _ => S := by
    ext z
    constructor
    · intro hz
      choose β hβ hβ' using fun j => coord_latOF (hl j) hz
      refine ⟨fun j => coordM (AF F) (l j) z, fun j _ => ⟨β j, hβ j, (hβ' j).symm⟩, ?_⟩
      simp only [smul_ratWF]
      exact (eq_sum_coordM e z).symm
    · rintro ⟨a, ha, rfl⟩
      refine AddSubgroup.sum_mem _ fun j _ => ?_
      obtain ⟨β, hβ, hβ'⟩ := ha j trivial
      rw [← hβ', smul_ratWF]
      exact tm_mem_latOF hβ (hy j)
  rw [him]
  exact (isCompact_univ_pi fun _ => hS).image (cont_sum y)

theorem lat_den (h : GoodLat Λ) (x : WOF F E nS nT) (hx : x.map (infPartF F E) = 0) :
    ∃ N : ℕ, 0 < N ∧ N • x ∈ latOF F E nS nT Λ := by
  obtain ⟨m, y, l, hy, _, e⟩ := exists_dualBasis (F := F) h
  choose N hN hN' using fun j => nat_mul_mem (coordM (AF F) (l j) x).2
  refine ⟨∏ j, N j, Finset.prod_pos fun j _ => hN j, ?_⟩
  rw [eq_sum_coordM e x, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ j)
  rw [fin_coord hx, tm_nsmul, pair_nsmul, hc, mul_comm, mul_smul]
  exact tm_mem_latOF (nsmul_mem (hN' j) c) (hy j)

theorem lat_approx (h : GoodLat Λ) (x : WOF F E nS nT) (hx : x.map (infPartF F E) = 0) :
    ∃ γ : Matrix (Fin nT) (Fin nS) E,
      x - algebraMap (AF F) (AEF F E) (pairA F 0 1) • ratWF (F := F) γ ∈ latOF F E nS nT Λ := by
  obtain ⟨m, y, l, hy, _, e⟩ := exists_dualBasis (F := F) h
  choose f hf using fun j => GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (R := 𝓞 F) (coordM (AF F) (l j) x).2
  refine ⟨∑ j, f j • y j, ?_⟩
  rw [smul_ratWF, tm_sum_right]
  nth_rewrite 1 [eq_sum_coordM e x]
  rw [← Finset.sum_sub_distrib]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  rw [tm_smul_right, ← tm_sub_left, fin_coord hx, smul_pair, mul_one, pair_sub]
  exact tm_mem_latOF (hf j) (hy j)

end PositivityTheory.ThKW

end
