import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwasawaDecompositionSmoothNearOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalSum

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open scoped ContDiff

namespace GlobalTheory.DiscSMO

theorem exists_tensorOp {ι : Type} [Fintype ι] {X : ι → Type} (T : ∀ i, Module.End ℂ (X i → ℂ)) :
    ∃ Θ : Module.End ℂ ((∀ i, X i) → ℂ), ∀ f : ∀ i, X i → ℂ,
      Θ (fun m => ∏ i, f i (m i)) = fun m => ∏ i, T i (f i) (m i) := by
  classical
  have key : ∀ s : Finset ι, ∃ Θ : Module.End ℂ ((∀ i, X i) → ℂ), ∀ f : ∀ i, X i → ℂ,
      Θ (fun m => ∏ i, f i (m i)) = fun m => ∏ i, (if i ∈ s then T i (f i) else f i) (m i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, fun f => by simp⟩
    | insert i s hi ih =>
      obtain ⟨Θ, hΘ⟩ := ih
      let Θi : Module.End ℂ ((∀ i, X i) → ℂ) :=
        { toFun := fun F m => T i (fun x => F (Function.update m i x)) (m i)
          map_add' := fun F G => funext fun m => congrFun (map_add (T i) _ _) (m i)
          map_smul' := fun z F => funext fun m => congrFun (map_smul (T i) z _) (m i) }
      refine ⟨Θi * Θ, fun f => funext fun m => ?_⟩
      rw [Module.End.mul_apply, hΘ]
      have e : (fun x => ∏ j, (if j ∈ s then T j (f j) else f j) (Function.update m i x j)) =
          (∏ j ∈ Finset.univ.erase i, (if j ∈ s then T j (f j) else f j) (m j)) • f i := by
        funext x
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self, if_neg hi, Pi.smul_apply, smul_eq_mul]
        congr 1
        exact Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      change T i (fun x => ∏ j, (if j ∈ s then T j (f j) else f j) (Function.update m i x j)) (m i) = _
      rw [e, map_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos (Finset.mem_insert_self i s), Pi.smul_apply,
        smul_eq_mul]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  obtain ⟨Θ, hΘ⟩ := key Finset.univ
  exact ⟨Θ, fun f => by simpa using hΘ f⟩

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a c N : ℕ} {n : Fin c → ℕ}
  {π π' : ∀ i, CuspSub E (n i)}

variable (E a) in

def cptFin : Subgroup (GA E a) :=
  (Unitary.toUnits (R := Matrix (Fin a) (Fin a) (Cinf E))).range.comap (Matrix.GeneralLinearGroup.map (pInf E))

theorem mul_mem_cptFin (k : Kinf E a) (g : GL (Fin a) (Af E)) :
    infGL E a (Unitary.toUnits k) * finGL E a g ∈ cptFin E a := ⟨k, by simp⟩

theorem exists_of_mem_cptFin {y : GA E a} (hy : y ∈ cptFin E a) :
    ∃ (k : Kinf E a) (g : GL (Fin a) (Af E)), y = infGL E a (Unitary.toUnits k) * finGL E a g := by
  obtain ⟨k, hk⟩ := hy
  exact ⟨k, _, by rw [hk]; exact (infGL_mul_finGL y).symm⟩

def prodForm (φ : ∀ i, (π i).V) : (∀ i, GA E (n i)) → ℂ := fun m => ∏ i, (φ i).1.1 (m i)

theorem prodForm_mem (φ : ∀ i, (π i).V) : prodForm φ ∈ tensorForms π := Submodule.subset_span ⟨φ, rfl⟩

structure IsTensorOf (T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V) (Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)) : Prop where
  comm : ∀ i o φ, T i ((π i).op o φ) = (π' i).op o (T i φ)
  prod : ∀ φ, Θ (prodForm φ) = prodForm fun i => T i (φ i)

theorem isTensorOf_id : IsTensorOf (π := π) (fun _ => LinearMap.id) 1 := ⟨fun _ _ _ => rfl, fun _ => rfl⟩

theorem exists_isTensorOf (T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V) (hT : ∀ i o φ, T i ((π i).op o φ) = (π' i).op o (T i φ)) :
    ∃ Θ, IsTensorOf T Θ := by
  choose g hg using fun i => LinearMap.exists_leftInverse_of_injective ((Sm E (n i)).subtype ∘ₗ (π i).V.subtype)
    (LinearMap.ker_eq_bot.2 (Subtype.val_injective.comp Subtype.val_injective))
  obtain ⟨Θ, hΘ⟩ := exists_tensorOp fun i => ((Sm E (n i)).subtype ∘ₗ (π' i).V.subtype) ∘ₗ T i ∘ₗ g i
  refine ⟨Θ, hT, fun φ => (hΘ fun i => (φ i).1.1).trans (funext fun m => Finset.prod_congr rfl fun i _ => ?_)⟩
  exact congrArg (fun v => (T i v).1.1 (m i)) (LinearMap.congr_fun (hg i) (φ i))

theorem hasDerivAt_prodForm (γ : ∀ i, ℝ → GL (Fin (n i)) (Cinf E)) (Z : ∀ i, Lie E (n i)) (h0 : ∀ i, γ i 0 = 1)
    (hγ : ∀ i, HasDerivAt (fun t => toL (γ i t).val) (Z i) 0) (φ : ∀ i, (π i).V) (m : ∀ i, GA E (n i)) :
    HasDerivAt (fun t => prodForm φ fun i => m i * infGL E (n i) (γ i t))
      ((∑ i, prodForm (Function.update φ i ((π i).op (.lie (Z i)) (φ i)))) m) 0 := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    fun i _ => hasDerivAt_curve (φ i).1 (m i) (γ i) (Z i) (h0 i) (hγ i)
  refine h.congr_deriv (Eq.symm ?_)
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prodForm, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self, smul_eq_mul]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj), h0, map_one, mul_one]

theorem contDiffAt_tensorForms {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {y₀ : P}
    (b : P → ∀ i, GL (Fin (n i)) (Cinf E)) (hb : ∀ i, ContDiffAt ℝ ∞ (fun y => toL (b y i).val) y₀)
    {F : (∀ i, GA E (n i)) → ℂ} (hF : F ∈ tensorForms π) (m : ∀ i, GA E (n i)) :
    ContDiffAt ℝ ∞ (fun y => F fun i => m i * infGL E (n i) (b y i)) y₀ := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ, rfl⟩ := hF
    refine contDiffAt_prod fun i _ => ?_
    have := (contDiffAt_chart (φ i).1.2 (m i) (val_mem_invSet (b y₀ i))).comp y₀ (hb i)
    simpa only [Function.comp_def, chart_val] using this
  | zero => exact contDiffAt_const
  | add F F' _ _ hF hF' => exact hF.add hF'
  | smul z F _ hF => exact contDiffAt_const.mul hF

namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}

theorem mem (h : IsTensorOf T Θ) {F : (∀ i, GA E (n i)) → ℂ} (hF : F ∈ tensorForms π) : Θ F ∈ tensorForms π' := by
  refine (Submodule.span_le (p := (tensorForms π').comap Θ)).2 ?_ hF
  rintro _ ⟨φ, rfl⟩
  change Θ (prodForm φ) ∈ tensorForms π'
  rw [h.prod]
  exact prodForm_mem _

theorem inv (h : IsTensorOf T Θ) {T' : ∀ i, (π' i).V →ₗ[ℂ] (π i).V} {Θ' : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}
    (h' : IsTensorOf T' Θ') (e : ∀ i v, T' i (T i v) = v) {F : (∀ i, GA E (n i)) → ℂ} (hF : F ∈ tensorForms π) :
    Θ' (Θ F) = F := by
  refine (Submodule.span_le (p := LinearMap.eqLocus (Θ' * Θ) 1)).2 ?_ hF
  rintro _ ⟨φ, rfl⟩
  change Θ' (Θ (prodForm φ)) = prodForm φ
  simp only [h.prod, h'.prod, e]

theorem translate (h : IsTensorOf T Θ) {x : ∀ i, GA E (n i)} (hx : ∀ i, x i ∈ cptFin E (n i))
    {F : (∀ i, GA E (n i)) → ℂ} (hF : F ∈ tensorForms π) : Θ (fun m => F (m * x)) = fun m => Θ F (m * x) := by
  choose k g e using fun i => exists_of_mem_cptFin (hx i)
  refine (Submodule.span_le (p := LinearMap.eqLocus (Θ * LinearMap.funLeft ℂ ℂ (· * x))
    (LinearMap.funLeft ℂ ℂ (· * x) * Θ))).2 ?_ hF
  rintro _ ⟨φ, rfl⟩
  have key : ∀ {π : ∀ i, CuspSub E (n i)} (φ : ∀ i, (π i).V), (fun m => prodForm φ (m * x)) =
      prodForm fun i => (π i).op (.cpt (k i)) ((π i).op (.fin (g i)) (φ i)) := fun φ => funext fun m =>
    Finset.prod_congr rfl fun i _ => by
      rw [Pi.mul_apply, e, ← mul_assoc]
      rfl
  change Θ (fun m => prodForm φ (m * x)) = fun m => Θ (prodForm φ) (m * x)
  simp only [key, h.prod, h.comm]

theorem deriv (h : IsTensorOf T Θ) (γ : ∀ i, ℝ → GL (Fin (n i)) (Cinf E)) (Z : ∀ i, Lie E (n i)) (h0 : ∀ i, γ i 0 = 1)
    (hγ : ∀ i, HasDerivAt (fun t => toL (γ i t).val) (Z i) 0) {F : (∀ i, GA E (n i)) → ℂ} (hF : F ∈ tensorForms π) :
    ∃ G, (∀ m, HasDerivAt (fun t => F fun i => m i * infGL E (n i) (γ i t)) (G m) 0) ∧
      ∀ m, HasDerivAt (fun t => Θ F fun i => m i * infGL E (n i) (γ i t)) (Θ G m) 0 := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ, rfl⟩ := hF
    refine ⟨_, hasDerivAt_prodForm γ Z h0 hγ φ, fun m => ?_⟩
    have := hasDerivAt_prodForm γ Z h0 hγ (fun i => T i (φ i)) m
    rw [← h.prod] at this
    refine this.congr_deriv (congrFun (Eq.symm ?_) m)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h.prod, ← h.comm]
    congr 1
    funext j
    exact Function.apply_update (fun i v => T i v) φ i _ j
  | zero => exact ⟨0, fun m => hasDerivAt_const _ _, fun m => by simpa using hasDerivAt_const _ _⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨G, h1, h2⟩ := hF
    obtain ⟨G', h1', h2'⟩ := hF'
    exact ⟨G + G', fun m => (h1 m).add (h1' m), fun m => by rw [map_add, map_add]; exact (h2 m).add (h2' m)⟩
  | smul z F _ hF =>
    obtain ⟨G, h1, h2⟩ := hF
    exact ⟨z • G, fun m => (h1 m).const_mul z, fun m => by rw [map_smul, map_smul]; exact (h2 m).const_mul z⟩

end IsTensorOf

theorem leviProj_mem_cptFin (e : (Σ i, Fin (n i)) ≃ Fin N) (p : parab (Ad E) e) (hp : p.1 ∈ cptFin E N) (i : Fin c) :
    leviProj (Ad E) e p i ∈ cptFin E (n i) := by
  obtain ⟨k, hk⟩ := hp
  set y := Matrix.GeneralLinearGroup.map (pInf E) (leviProj (Ad E) e p i) with hy
  have h1 : ∀ a b, y.val a b = k.1 (e ⟨i, a⟩) (e ⟨i, b⟩) := fun a b =>
    (congrArg (fun z : GL (Fin N) (Cinf E) => z.val (e ⟨i, a⟩) (e ⟨i, b⟩)) hk).symm
  have h2 : ∀ a b, (y⁻¹).val a b = star k.1 (e ⟨i, a⟩) (e ⟨i, b⟩) := fun a b => by
    have hk' : (Unitary.toUnits k)⁻¹ = Matrix.GeneralLinearGroup.map (pInf E) (p⁻¹).1 := by
      rw [hk, ← map_inv]; rfl
    rw [hy, ← map_inv, ← Pi.inv_apply, ← map_inv]
    exact (congrArg (fun z : GL (Fin N) (Cinf E) => z.val (e ⟨i, a⟩) (e ⟨i, b⟩)) hk').symm
  have h3 : star y.val = (y⁻¹).val := by
    ext a b : 2
    rw [h2, Matrix.star_apply, Matrix.star_apply, h1]
  exact ⟨⟨y.val, by rw [h3, Units.inv_mul], by rw [h3, Units.mul_inv]⟩, Units.ext rfl⟩

variable {h : ∑ i, n i = N}

variable (h) in

def res (y : GA E N) : (GA E N → ℂ) →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun m => leviEmb (Ad E) (stdBlocks n h) m * y

theorem res_mem {φ : Sm E N} (hφ : φ ∈ indForms h π) {y : GA E N} (hy : y ∈ cptFin E N) :
    res h y φ.1 ∈ tensorForms π := by
  obtain ⟨k, g, rfl⟩ := exists_of_mem_cptFin hy
  exact hφ.2.2.2 k g

theorem cpt_mem_indForms {φ : Sm E N} (hφ : φ ∈ indForms h π) (k : Kinf E N) : cptRep E N k φ ∈ indForms h π := by
  refine ⟨fun u hu g => ?_, ?_, ?_, fun k' g => ?_⟩
  · change φ.1 (u * g * _) = φ.1 (g * _)
    rw [mul_assoc, hφ.1 u hu]
  · have ho : IsOpen {x | finRep E N x φ = φ} := hφ.2.1
    refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
    have hx' : finRep E N x φ = φ := hx
    refine Subtype.ext (funext fun g => ?_)
    have := congrArg (fun ψ : Sm E N => ψ.1 (g * infGL E N (Unitary.toUnits k))) hx'
    change φ.1 (g * infGL E N _ * finGL E N x) = _ at this
    change φ.1 (g * finGL E N x * infGL E N _) = _
    rw [mul_assoc, ← infGL_comm, ← mul_assoc]
    exact this
  · have hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k φ)) := hφ.2.2.1
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => cptRep E N k φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k', rfl⟩
    exact Submodule.subset_span ⟨k' * k, by simp only [map_mul]; rfl⟩
  · have := res_mem hφ (mul_mem (mul_mem_cptFin k' g) (mul_mem_cptFin k 1))
    convert this using 2 with m
    change φ.1 (_ * infGL E N _) = φ.1 _
    simp only [map_one, mul_one, mul_assoc]

theorem rt_mem_indForms {φ : Sm E N} (hφ : φ ∈ indForms h π) {y : GA E N} (hy : y ∈ cptFin E N) :
    rt E N y φ ∈ indForms h π := by
  obtain ⟨k, g, rfl⟩ := exists_of_mem_cptFin hy
  rw [map_mul]
  exact cpt_mem_indForms (fin_mem_indForms hφ g) k

variable (h) in
theorem exists_iw (x : GA E N) : ∃ q : (∀ i, GA E (n i)) × GA E N, q.2 ∈ cptFin E N ∧
    ∃ u ∈ unipRad (Ad E) (stdBlocks n h), x = u * leviEmb (Ad E) (stdBlocks n h) q.1 * q.2 := by
  obtain ⟨u, hu, m, k, g, e⟩ := GlobalTheory.IwasawaAdelic.iwasawa E n h x
  exact ⟨(m, _), mul_mem_cptFin k g, u, hu, e⟩

variable (h) in

def indOp (Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)) : Module.End ℂ (GA E N → ℂ) :=
  LinearMap.pi fun x => LinearMap.proj (exists_iw h x).choose.1 ∘ₗ Θ ∘ₗ res h (exists_iw h x).choose.2

namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}

theorem indOp_apply (H : IsTensorOf T Θ) {φ : Sm E N} (hφ : φ ∈ indForms h π) {u y : GA E N}
    (hu : u ∈ unipRad (Ad E) (stdBlocks n h)) (hy : y ∈ cptFin E N) (m : ∀ i, GA E (n i)) :
    indOp h Θ φ.1 (u * leviEmb (Ad E) (stdBlocks n h) m * y) = Θ (res h y φ.1) m := by
  set x := u * leviEmb (Ad E) (stdBlocks n h) m * y with hx
  obtain ⟨hy', u', hu', e'⟩ := (exists_iw h x).choose_spec
  change Θ (res h (exists_iw h x).choose.2 φ.1) (exists_iw h x).choose.1 = _
  generalize (exists_iw h x).choose = q at hy' e'
  obtain ⟨m', y'⟩ := q
  simp only at hy' e' ⊢
  let e := stdBlocks n h
  let U : parab (Ad E) e := ⟨u, unipRad_le_parab _ _ hu⟩
  let U' : parab (Ad E) e := ⟨u', unipRad_le_parab _ _ hu'⟩
  let M : parab (Ad E) e := ⟨_, leviEmb_mem_parab _ e m⟩
  let M' : parab (Ad E) e := ⟨_, leviEmb_mem_parab _ e m'⟩
  let p := (U' * M')⁻¹ * (U * M)
  have hp : p.1 = y' * y⁻¹ := by
    change (u' * leviEmb (Ad E) e m')⁻¹ * (u * leviEmb (Ad E) e m) = _
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
    exact e'
  have hl : leviProj (Ad E) e p = m'⁻¹ * m := by
    simp only [p, map_mul, map_inv, (coe_mem_unipRad _ U).1 hu, (coe_mem_unipRad _ U').1 hu', M, M', leviProj_leviEmb, one_mul]
  obtain ⟨v, hv, ev⟩ := exists_levi_mul_unip _ e p
  have hm : ∀ i, (m'⁻¹ * m) i ∈ cptFin E (n i) := fun i =>
    hl ▸ leviProj_mem_cptFin e p (hp ▸ mul_mem hy' (inv_mem hy)) i
  have hr : res h y' φ.1 = fun z => res h y φ.1 (z * (m'⁻¹ * m)) := funext fun z => by
    change φ.1 (leviEmb _ e z * y') = φ.1 (leviEmb _ e _ * y)
    set L := leviEmb (Ad E) e (z * (m'⁻¹ * m)) with hL
    have hv' := (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer _ e (z * (m'⁻¹ * m))) v).1 hv
    rw [← hφ.1 _ hv' (L * y), ← hL]
    rw [hp, hl, mul_inv_eq_iff_eq_mul] at ev
    rw [ev, mul_assoc (L * v), inv_mul_cancel_left, hL, map_mul _ z]
    simp only [mul_assoc]
  rw [hr, H.translate hm (res_mem hφ hy)]
  simp

theorem indOp_levi (H : IsTensorOf T Θ) {φ : Sm E N} (hφ : φ ∈ indForms h π) {y : GA E N} (hy : y ∈ cptFin E N) :
    res h y (indOp h Θ φ.1) = Θ (res h y φ.1) := funext fun m => by
  have := H.indOp_apply hφ (one_mem _) hy m
  rwa [one_mul] at this

theorem indOp_left (H : IsTensorOf T Θ) {φ : Sm E N} (hφ : φ ∈ indForms h π) {u : GA E N}
    (hu : u ∈ unipRad (Ad E) (stdBlocks n h)) (x : GA E N) : indOp h Θ φ.1 (u * x) = indOp h Θ φ.1 x := by
  obtain ⟨⟨m, y⟩, hy, v, hv, rfl⟩ := exists_iw h x
  rw [← mul_assoc, ← mul_assoc, H.indOp_apply hφ (mul_mem hu hv) hy, H.indOp_apply hφ hv hy]

theorem indOp_rt (H : IsTensorOf T Θ) {φ : Sm E N} (hφ : φ ∈ indForms h π) {z : GA E N} (hz : z ∈ cptFin E N)
    (x : GA E N) : indOp h Θ (rt E N z φ).1 x = indOp h Θ φ.1 (x * z) := by
  obtain ⟨⟨m, y⟩, hy, v, hv, rfl⟩ := exists_iw h x
  rw [mul_assoc _ y, H.indOp_apply hφ hv (mul_mem hy hz), H.indOp_apply (rt_mem_indForms hφ hz) hv hy]
  exact congrFun (congrArg Θ (funext fun m => congrArg φ.1 (mul_assoc _ _ _))) m

end IsTensorOf

theorem ext_res {f f' : GA E N → ℂ} (hf : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ x, f (u * x) = f x)
    (hf' : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ x, f' (u * x) = f' x)
    (e : ∀ y ∈ cptFin E N, res h y f = res h y f') : f = f' := funext fun x => by
  obtain ⟨⟨m, y⟩, hy, v, hv, rfl⟩ := exists_iw h x
  rw [mul_assoc, hf v hv, hf' v hv]
  exact congrFun (e y hy) m

theorem mem_Sm_of_one {f : GA E a → ℂ} (hf : ∀ g, ContDiffAt ℝ ∞ (chart f g) (oneL E a)) : f ∈ Sm E a := by
  rintro g x ⟨y, hy⟩
  obtain rfl : x = toL y.val := hy.symm
  have e : chart f g = chart f (g * infGL E a y) ∘ lmul (toL (y⁻¹).val) := by
    rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have e1 : lmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.inv_mul
  rw [e]
  refine (ContDiffAt.comp _ ?_ (lmul (toL (y⁻¹).val)).contDiff.contDiffAt).contDiffWithinAt
  rw [e1]
  exact hf _

theorem contDiffAt_chart_mul {f : GA E a → ℂ} {g : GA E a} {y : GL (Fin a) (Cinf E)}
    (hf : ContDiffAt ℝ ∞ (chart (fun x => f (x * infGL E a y)) g) (oneL E a)) :
    ContDiffAt ℝ ∞ (chart f (g * infGL E a y)) (oneL E a) := by
  have e : chart f g = chart (fun x => f (x * infGL E a y)) g ∘ rmul (toL (y⁻¹).val) := by
    rw [← chart_rt_inf]
    simp only [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  have e1 : rmul (toL (y⁻¹).val) (toL y.val) = oneL E a := y.mul_inv
  have e2 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  rw [chart_mul, e]
  refine ContDiffAt.comp _ ?_ (lmul (toL y.val)).contDiff.contDiffAt
  rw [e2]
  refine ContDiffAt.comp _ ?_ (rmul (toL (y⁻¹).val)).contDiff.contDiffAt
  rw [e1]
  exact hf

variable (h) in

theorem exists_expansion {φ : Sm E N} (hφ : φ ∈ indForms h π) :
    ∃ (r : ℕ) (F : Fin r → (∀ i, GA E (n i)) → ℂ) (C : Fin r → Lie E N → ℂ) (b : Lie E N → ∀ i, GL (Fin (n i)) (Cinf E)),
      (∀ j, F j ∈ tensorForms π) ∧ (∀ j, ContDiffAt ℝ ∞ (C j) (oneL E N)) ∧
      (∀ i, ContDiffAt ℝ ∞ (fun y => toL (b y i).val) (oneL E N)) ∧ b (oneL E N) = 1 ∧
      ∀ {π' : ∀ i, CuspSub E (n i)} {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)},
        IsTensorOf T Θ → ∀ m, chart (indOp h Θ φ.1) (leviEmb (Ad E) (stdBlocks n h) m) =ᶠ[nhds (oneL E N)]
          fun y => ∑ j, C j y * Θ (F j) fun i => m i * infGL E (n i) (b y i) := by
  obtain ⟨p, k, hp, hk, hp1, hk1, hpk⟩ := GlobalTheory.T.iwasawa_decomposition_smooth_near_one E n (stdBlocks n h)
  obtain ⟨r, ψ, C, hψ, hC, e⟩ := GlobalTheory.KFinExp.exists_expansion E N φ hφ.2.2.1
  have hψ' : ∀ j, ψ j ∈ indForms h π := fun j => Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact cpt_mem_indForms hφ k) (hψ j)
  refine ⟨r, fun j => res h 1 (ψ j).1, fun j y => C j (toL (k y).1), fun y => leviProj _ _ (p y),
    fun j => res_mem (hψ' j) (one_mem _), fun j => ContDiffAt.comp _ (by rw [hk1]; exact hC j) hk, fun i =>
      contDiffAt_pi.2 fun s => contDiffAt_pi.2 fun t => contDiffAt_pi.1 (contDiffAt_pi.1 hp _) _,
    by simp only [hp1, map_one], fun H m => ?_⟩
  filter_upwards [hpk] with y hy
  obtain ⟨u, hu, eu⟩ := exists_levi_mul_unip _ _ (p y)
  have hy' : y = toL ((p y).1 * Unitary.toUnits (k y)).val := hy
  have hky : infGL E N (Unitary.toUnits (k y)) ∈ cptFin E N := by simpa using mul_mem_cptFin (k y) 1
  set L := leviEmb (Ad E) (stdBlocks n h) fun i => m i * infGL E (n i) (leviProj _ _ (p y) i) with hL
  have hu' := (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer _ _ _) _).1
    (GlobalTheory.IwasawaAdelic.infGL_mem_unipRad E n h u hu) |> (hL ▸ ·)
  have ex : leviEmb (Ad E) (stdBlocks n h) m * infGL E N ((p y).1 * Unitary.toUnits (k y)) =
      L * infGL E N u * L⁻¹ * L * infGL E N (Unitary.toUnits (k y)) := by
    rw [inv_mul_cancel_right, map_mul]
    conv_lhs => rw [eu]
    rw [map_mul, GlobalTheory.LieTensor.infGL_leviEmb, ← mul_assoc, ← mul_assoc, ← map_mul]
    rfl
  have er : res h (infGL E N (Unitary.toUnits (k y))) φ.1 = ∑ j, C j (toL (k y).1) • res h 1 (ψ j).1 := by
    have : res h (infGL E N (Unitary.toUnits (k y))) φ.1 = res h 1 (cptRep E N (k y) φ).1 :=
      funext fun m => congrArg (fun z => φ.1 (z * infGL E N (Unitary.toUnits (k y)))) (mul_one _).symm
    rw [this, e]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  conv_lhs => rw [hy', chart_val, ex, hL, H.indOp_apply hφ hu' hky, er]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem indOp_one {φ : Sm E N} (hφ : φ ∈ indForms h π) : indOp h 1 φ.1 = φ.1 :=
  ext_res (fun _ hu => isTensorOf_id.indOp_left hφ hu) hφ.1 fun _ hy => isTensorOf_id.indOp_levi hφ hy

namespace IsTensorOf

variable {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}

theorem indOp_mem_Sm (H : IsTensorOf T Θ) {φ : Sm E N} (hφ : φ ∈ indForms h π) : indOp h Θ φ.1 ∈ Sm E N := by
  have key : ∀ {φ : Sm E N}, φ ∈ indForms h π → ∀ m,
      ContDiffAt ℝ ∞ (chart (indOp h Θ φ.1) (leviEmb (Ad E) (stdBlocks n h) m)) (oneL E N) := fun hφ m => by
    obtain ⟨r, F, C, b, hF, hC, hb, -, e⟩ := exists_expansion h hφ
    exact ContDiffAt.congr_of_eventuallyEq (ContDiffAt.sum fun j _ =>
      (hC j).mul (contDiffAt_tensorForms b hb (H.mem (hF j)) m)) (e H m)
  refine mem_Sm_of_one fun x => ?_
  obtain ⟨⟨m, y⟩, hy, v, hv, rfl⟩ := exists_iw h x
  obtain ⟨k, g, e⟩ := exists_of_mem_cptFin hy
  simp only at e ⊢
  rw [e, infGL_comm, ← mul_assoc]
  refine contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  convert key (rt_mem_indForms hφ hy) m using 1
  funext z
  simp only [chart, H.indOp_rt hφ hy]
  simp only [mul_assoc, H.indOp_left hφ hv, e]
  rw [← infGL_comm (Unitary.toUnits k) g]

variable (h) in

def indMap (H : IsTensorOf T Θ) : indForms h π →ₗ[ℂ] Sm E N :=
  (indOp h Θ ∘ₗ (Sm E N).subtype ∘ₗ (indForms h π).subtype).codRestrict _ fun φ => H.indOp_mem_Sm φ.2

theorem indMap_rt (H : IsTensorOf T Θ) (φ : indForms h π) {z : GA E N} (hz : z ∈ cptFin E N) :
    H.indMap h ⟨_, rt_mem_indForms φ.2 hz⟩ = rt E N z (H.indMap h φ) :=
  Subtype.ext (funext (H.indOp_rt φ.2 hz))

theorem indMap_mem (H : IsTensorOf T Θ) (φ : indForms h π) : H.indMap h φ ∈ indForms h π' := by
  have hf : ∀ g, finGL E N g ∈ cptFin E N := fun g => by simpa using mul_mem_cptFin 1 g
  have hk : ∀ k : Kinf E N, infGL E N (Unitary.toUnits k) ∈ cptFin E N := fun k => by simpa using mul_mem_cptFin k 1
  refine ⟨fun u hu => H.indOp_left φ.2 hu, ?_, ?_, fun k g => ?_⟩
  · have ho : IsOpen {x | finRep E N x φ.1 = φ.1} := φ.2.2.1
    refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
    exact (H.indMap_rt φ (hf x)).symm.trans (congrArg _ (Subtype.ext hx))
  · have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1)) := φ.2.2.2.1
    have : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1)).comap (indForms h π).subtype) :=
      (Submodule.comapSubtypeEquivOfLe (Submodule.span_le.2 (by
        rintro _ ⟨k, rfl⟩
        exact cpt_mem_indForms φ.2 k))).symm.finiteDimensional
    refine Submodule.finiteDimensional_of_le (S₂ := ((Submodule.span ℂ (Set.range fun k => cptRep E N k φ.1)).comap
      (indForms h π).subtype).map (H.indMap h)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨_, rt_mem_indForms φ.2 (hk k)⟩, Submodule.subset_span ⟨k, rfl⟩, H.indMap_rt φ (hk k)⟩
  · have := H.mem (res_mem φ.2 (mul_mem_cptFin k g))
    rw [← H.indOp_levi φ.2 (mul_mem_cptFin k g)] at this
    exact this

theorem res_lie (H : IsTensorOf T Θ) (φ : indForms h π) (X : Lie E N) :
    res h 1 (lie E N X (H.indMap h φ)).1 = Θ (res h 1 (lie E N X φ.1).1) := by
  obtain ⟨r, F, C, b, hF, hC, hb, hb1, e⟩ := exists_expansion h φ.2
  let l : ℝ → Lie E N := fun t => oneL E N + t • X
  have l0 : l 0 = oneL E N := by simp [l]
  have hl : HasDerivAt l X 0 := (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E N)).congr_deriv (one_smul _ _)
  have hd : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : Lie E N → Y}, ContDiffAt ℝ ∞ f (oneL E N) →
      HasDerivAt (fun t => f (l t)) (fderiv ℝ f (oneL E N) X) 0 := fun hf =>
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) (by rw [l0]; exact (hf.differentiableAt (by simp)).hasFDerivAt) hl
  choose G h1 h2 using fun j => H.deriv (fun i t => b (l t) i) _ (fun i => by simp only [l0, hb1]; rfl)
    (fun i => hd (hb i)) (hF j)
  have key : ∀ {π' : ∀ i, CuspSub E (n i)} {T : ∀ i, (π i).V →ₗ[ℂ] (π' i).V} {Θ : Module.End ℂ ((∀ i, GA E (n i)) → ℂ)}
      (H : IsTensorOf T Θ), (∀ j m, HasDerivAt (fun t => Θ (F j) fun i => m i * infGL E (n i) (b (l t) i)) (Θ (G j) m) 0) →
      res h 1 (lie E N X (H.indMap h φ)).1 =
        Θ (∑ j, (fderiv ℝ (C j) (oneL E N) X • F j + C j (oneL E N) • G j)) := fun H h2 => funext fun m => by
    have a1 := hd (contDiffAt_chart (H.indOp_mem_Sm φ.2) (leviEmb (Ad E) (stdBlocks n h) m) isUnit_one)
    have a2 := (HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hd (hC j)).mul (h2 j m)).congr_of_eventuallyEq
      (f₁ := fun t => chart (indOp h _ φ.1.1) (leviEmb (Ad E) (stdBlocks n h) m) (l t))
      ((l0 ▸ hl.continuousAt.tendsto :).eventually (e H m))
    change lieD X _ (_ * 1) = _
    rw [mul_one]
    refine (a1.unique a2).trans ?_
    simp [l0, hb1]
  have e1 := key isTensorOf_id h1
  rw [show isTensorOf_id.indMap h φ = φ.1 from Subtype.ext (indOp_one φ.2)] at e1
  rw [key H h2, e1]
  rfl

theorem indMap_lie (H : IsTensorOf T Θ) (φ : indForms h π) (X : Lie E N) :
    H.indMap h ⟨_, GlobalTheory.SpehInfChar.lie_mem_indForms n h π X φ.1 φ.2⟩ = lie E N X (H.indMap h φ) := by
  refine Subtype.ext (ext_res (H.indMap_mem _).1
    (GlobalTheory.SpehInfChar.lie_mem_indForms n h π' X _ (H.indMap_mem φ)).1 fun y hy => ?_)
  obtain ⟨X', hX⟩ : ∃ X', rt E N y * lie E N X = lie E N X' * rt E N y := by
    obtain ⟨k, g, rfl⟩ := exists_of_mem_cptFin hy
    refine ⟨toL ((Unitary.toUnits k).val * Matrix.of X * ((Unitary.toUnits k)⁻¹).val), ?_⟩
    rw [map_mul, mul_assoc, ← lie_rt_fin, ← mul_assoc, ← mul_assoc]
    exact congrArg (· * _) (GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits k) (Matrix.of X))
  have e : ∀ ψ : Sm E N, res h y (lie E N X ψ).1 = res h 1 (lie E N X' (rt E N y ψ)).1 := fun ψ => funext fun m => by
    have := congrArg (fun f : Module.End ℂ (Sm E N) => (f ψ).1 (leviEmb (Ad E) (stdBlocks n h) m * 1)) hX
    simp only [Module.End.mul_apply, rt_apply, mul_one] at this
    change _ = (lie E N X' (rt E N y ψ)).1 (_ * 1)
    rw [mul_one]
    exact this
  rw [e, ← H.indMap_rt φ hy, H.res_lie, ← e]
  exact H.indOp_levi (GlobalTheory.SpehInfChar.lie_mem_indForms n h π X φ.1 φ.2) hy

end IsTensorOf

theorem isQuotOf_of_iso (hi : ∀ i, (π i).Iso (π' i)) {V : Submodule ℂ (Sm E N)} (hV : IsQuotOf V (indForms h π)) :
    IsQuotOf V (indForms h π') := by
  choose T hT using hi
  obtain ⟨Θ, H⟩ := exists_isTensorOf (fun i => (T i).toLinearMap) hT
  obtain ⟨Θ', H'⟩ := exists_isTensorOf (fun i => (T i).symm.toLinearMap) fun i o φ =>
    (T i).injective (by rw [hT]; simp)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (H'.indMap h)
  have hg' : ∀ φ (hφ : φ ∈ indForms h π'), g φ = H'.indMap h ⟨φ, hφ⟩ := fun φ hφ => LinearMap.congr_fun hg ⟨φ, hφ⟩
  obtain ⟨f, hf, hc⟩ := hV
  refine ⟨f ∘ₗ g, ?_, fun o φ hφ => ?_⟩
  · rw [Submodule.map_comp, ← hf]
    congr 1
    refine le_antisymm ?_ fun φ hφ => ⟨_, H.indMap_mem ⟨φ, hφ⟩, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      exact hg' φ hφ ▸ H'.indMap_mem _
    · rw [hg' _ (H.indMap_mem ⟨φ, hφ⟩)]
      refine Subtype.ext (ext_res (H'.indMap_mem _).1 hφ.1 fun y hy => ?_)
      refine (H'.indOp_levi (H.indMap_mem ⟨φ, hφ⟩) hy).trans ((congrArg Θ' (H.indOp_levi hφ hy)).trans ?_)
      exact H.inv H' (fun i => (T i).symm_apply_apply) (res_mem hφ hy)
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hg' φ hφ, ← hc o _ (H'.indMap_mem _)]
    congr 1
    cases o with
    | fin x =>
      have hx : finGL E N x ∈ cptFin E N := by simpa using mul_mem_cptFin 1 x
      exact (hg' _ (rt_mem_indForms hφ hx)).trans (H'.indMap_rt ⟨φ, hφ⟩ hx)
    | cpt k =>
      have hx : infGL E N (Unitary.toUnits k) ∈ cptFin E N := by simpa using mul_mem_cptFin k 1
      exact (hg' _ (rt_mem_indForms hφ hx)).trans (H'.indMap_rt ⟨φ, hφ⟩ hx)
    | lie X => exact (hg' _ (GlobalTheory.SpehInfChar.lie_mem_indForms n h π' X φ hφ)).trans (H'.indMap_lie ⟨φ, hφ⟩ X)

theorem isSpehOf_of_iso {d : ℕ} {V : Submodule ℂ (Sm E N)} {π π' : CuspSub E a} (hi : π.Iso π') (e : IsSpehOf V π d) :
    IsSpehOf V π' d := by
  obtain ⟨h, ν, hν, hq⟩ := e
  exact ⟨h, ν, hν, isQuotOf_of_iso (fun i => hi.twist (ν i)) hq⟩

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
open GlobalTheory.Published GlobalTheory.LFun GlobalTheory.SpehPair in

theorem eq_of_isLocCompGL : DiscreteSpectrumGL → JacquetShalikaRigidity → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N → ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → (∀ w : HeightOneSpectrum (𝓞 E), ∃ σ : SmIrr (GL (Fin N) (w.adicCompletion E)), IsLocCompGL V w σ ∧ IsLocCompGL V' w σ) → V = V' := by
  intro hD hJ E _ _ _ N hN V V' hV hV' hloc
  obtain ⟨h1, h2, -, -, h5⟩ := hD E N hN
  obtain ⟨a, d, π, hu, hn, e⟩ := h1 V hV
  obtain ⟨a', d', π', hu', hn', e'⟩ := h1 V' hV'
  have p := e.mul_eq
  have p' := e'.mul_eq
  have hd : 1 ≤ d := Nat.pos_of_mul_pos_right (p ▸ hN : 0 < d * a)
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_left (p ▸ hN : 0 < d * a)
  have hd' : 1 ≤ d' := Nat.pos_of_mul_pos_right (p' ▸ hN : 0 < d' * a')
  have ha' : 1 ≤ a' := Nat.pos_of_mul_pos_left (p' ▸ hN : 0 < d' * a')
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E
  have hc := h5 V hV a d π hn e
  have hc' := h5 V' hV' a' d' π' hn' e'
  obtain ⟨s, hs⟩ := hJ.unitary (ι := Fin d) (κ := Fin d') (fun _ => CG.mk π) (fun _ => CG.mk π') (fun _ => ha)
    (fun _ => ha') (fun _ => (CG.isUnitary_mk _).2 hu) (fun _ => (CG.isUnitary_mk _).2 hu') _ hν
    (fun i => -spehExp d i) (fun i => -spehExp d' i) (by
      filter_upwards [eventually_spherical hV] with w hw
      obtain ⟨τ, hτ, hτ'⟩ := hloc w
      obtain ⟨σ, -, hσ, -⟩ := hc.exLoc w
      obtain ⟨σ', -, hσ', -⟩ := hc'.exLoc w
      obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible τ.smooth τ.irred (hw τ hτ)
      obtain ⟨B, hB, eB⟩ := exists_sat_twist hd hσ (hc.loc w σ τ hσ hτ) hT _ hν
      obtain ⟨B', hB', eB'⟩ := exists_sat_twist hd' hσ' (hc'.loc w σ' τ hσ' hτ') hT _ hν
      exact ⟨B, B', hB, hB', eB.trans eB'.symm⟩)
  obtain rfl : d = d' := by simpa using Fintype.card_congr s
  have e2 := (hs ⟨0, hd⟩).1
  obtain rfl : a = a' := (Sigma.mk.inj e2).1
  have hi : π.Iso π' := Quotient.exact (eq_of_heq (Sigma.mk.inj e2).2)
  exact (h2 a d π' p hn').unique ⟨hV, isSpehOf_of_iso hi e⟩ ⟨hV', e'⟩

end GlobalTheory.DiscSMO

end
