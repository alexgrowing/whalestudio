import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.SliceArch
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatFinite

noncomputable section

namespace PositivityTheory.ThKCT.Ad

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField.mixedEmbedding
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA PositivityTheory.ThKCT.Arch

variable {F : Type} [Field F] [NumberField F] {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]

variable (F) in

def qI : AF F →+* mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1

theorem qI_eq (a : AF F) : qI F a = evI F a := rfl

theorem continuous_qI : Continuous (qI F) := by
  have : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  exact this.comp continuous_fst

def pt (x : mixedSpace F) (y : Af F) : AF F := mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x) y

theorem qI_pt (x : mixedSpace F) (y : Af F) : qI F (pt x y) = x :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply x

theorem finite_projection_mixed_point (x : mixedSpace F) (y : Af F) : p2 (pt x y) = y := rfl

theorem pureA_pt (f : (κ → mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (x : κ → mixedSpace F) (y : κ → Af F) :
    pureA F f g (fun i => pt (x i) (y i)) = f x * g y := by
  change f (fun i => qI F (pt (x i) (y i))) * g y = _
  simp only [qI_pt]

theorem pureA_cancel {f f' : SInf F κ} {g : (κ → Af F) → ℂ} (hg : g ≠ 0) (h : pureA F f g = pureA F f' g) : f = f' := by
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hg
  ext x
  have := congrFun h fun i => pt (x i) (y i)
  rw [pureA_pt, pureA_pt] at this
  exact mul_right_cancel₀ hy this

theorem pureA_smul_left (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) : pureA F (c • f : SInf F κ) g = c • pureA F f g :=
  funext fun _ => mul_assoc _ _ _

theorem pureA_mem (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem psi_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AF F) : ψ a =
    Complex.exp (Complex.I * ((-(2 * Real.pi) * Algebra.trace ℝ (mixedSpace F) (qI F a) : ℝ) : ℂ)) * finChar ψ (p2 a) := by
  rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
  congr 2
  change _ * ((Algebra.trace ℝ (mixedSpace F) (qI F a) : ℝ) : ℂ) = _
  push_cast
  ring

variable (F κ) in

def aw0 : ((κ → mixedSpace F) × (κ → mixedSpace F)) →ₗ[ℝ] (κ → mixedSpace F) × ((κ → mixedSpace F) →L[ℝ] ℝ) :=
  LinearMap.prodMap LinearMap.id
    { toFun := fun c => -(2 * Real.pi) • trL c
      map_add' := fun c c' => by ext y; simp [trL_apply, mul_add]; ring
      map_smul' := fun r c => by ext y; simp [trL_apply]; ring }

def ev2 (w : (κ → AF F) × (κ → AF F)) : (κ → mixedSpace F) × (κ → mixedSpace F) := (fun i => qI F (w.1 i), fun i => qI F (w.2 i))

def fn2 (w : (κ → AF F) × (κ → AF F)) : (κ → Af F) × (κ → Af F) := (fun i => p2 (w.1 i), fun i => p2 (w.2 i))

theorem pairEvaluation_linear_combination {m : ℕ} (y : Fin m → AF F) (c : Fin m → (κ → AF F) × (κ → AF F)) :
    ev2 (∑ j, y j • c j) = ∑ j, qI F (y j) • ev2 (c j) := by
  ext i <;> simp [ev2, Prod.fst_sum, Prod.snd_sum]

theorem pairFunctional_linear_combination {m : ℕ} (y : Fin m → AF F) (c : Fin m → (κ → AF F) × (κ → AF F)) :
    fn2 (∑ j, y j • c j) = ∑ j, p2 (y j) • fn2 (c j) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [fn2, Prod.fst_sum, Prod.snd_sum]

theorem pairEvaluation_smul (y : AF F) (c : (κ → AF F) × (κ → AF F)) : ev2 (y • c) = qI F y • ev2 c := by
  ext i <;> simp [ev2]

theorem pairFunctional_smul (y : AF F) (c : (κ → AF F) × (κ → AF F)) : fn2 (y • c) = p2 y • fn2 c := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp [fn2]

def fw (ψ : AddChar (AF F) ℂ) (b : (κ → Af F) × (κ → Af F)) (g : (κ → Af F) → ℂ) : (κ → Af F) → ℂ :=
  finS ψ g b.2 b.1 (p2 (⅟(2 : AF F)) * (b.1 ⬝ᵥ b.2))

theorem fw_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (b : (κ → Af F) × (κ → Af F)) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) :
    fw ψ b g ∈ SB _ := finS_mem ψ hψ.1 hg _ _ _

theorem fw_zero (ψ : AddChar (AF F) ℂ) (g : (κ → Af F) → ℂ) : fw ψ 0 g = g := by
  funext x
  simp [fw, finS]

theorem schr_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    schr ψ w (pureA F f g) = pureA F (S (aw0 F κ (ev2 w)) f) (fw ψ (fn2 w) g) := by
  funext x
  have h2 : qI F (⅟(2 : AF F)) = algebraMap ℝ _ (1 / 2 : ℝ) := by
    have e : qI F (⅟(2 : AF F)) * 2 = 1 := by rw [← map_ofNat (qI F) 2, ← map_mul, invOf_mul_self, map_one]
    have e' : algebraMap ℝ (mixedSpace F) (1 / 2 : ℝ) * 2 = 1 := by
      rw [← map_ofNat (algebraMap ℝ (mixedSpace F)) 2, ← map_mul, ← map_one (algebraMap ℝ (mixedSpace F))]; norm_num
    linear_combination (algebraMap ℝ (mixedSpace F) (1 / 2 : ℝ)) * e - qI F (⅟(2 : AF F)) * e'
  change ψ _ * (f (fun i => qI F ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    S (aw0 F κ (ev2 w)) f (fun i => qI F (x i)) * (finChar ψ ((fun i => p2 (x i)) ⬝ᵥ (fn2 w).2 + _) * g ((fun i => p2 (x i)) + (fn2 w).1))
  rw [S_apply, psi_eq hψ, ph]
  have e1 : (fun i => qI F ((x + w.1) i)) = (fun i => qI F (x i)) + (aw0 F κ (ev2 w)).1 := funext fun i => map_add _ _ _
  have e2 : (fun i => p2 ((x + w.1) i)) = (fun i => p2 (x i)) + (fn2 w).1 := funext fun i => map_add _ _ _
  have e3 : p2 (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) =
      (fun i => p2 (x i)) ⬝ᵥ (fn2 w).2 + p2 (⅟(2 : AF F)) * ((fn2 w).1 ⬝ᵥ (fn2 w).2) := by
    rw [map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct]; rfl
  have e4 : -(2 * Real.pi) * Algebra.trace ℝ (mixedSpace F) (qI F (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2))) =
      (aw0 F κ (ev2 w)).2 (fun i => qI F (x i)) + (aw0 F κ (ev2 w)).2 (aw0 F κ (ev2 w)).1 / 2 := by
    rw [map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct, h2, ← Algebra.smul_def, map_add, map_smul]
    change _ = -(2 * Real.pi) * Algebra.trace ℝ (mixedSpace F) ((qI F ∘ x) ⬝ᵥ (qI F ∘ w.2)) +
      -(2 * Real.pi) * Algebra.trace ℝ (mixedSpace F) ((qI F ∘ w.1) ⬝ᵥ (qI F ∘ w.2)) / 2
    rw [smul_eq_mul]; ring
  rw [e1, e2, e3, e4]
  ring

theorem schr_comm {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct]
  rw [add_right_comm x w.1]
  congr 2
  ring

theorem fw_lc {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) :
    IsLocallyConstant fun b => fw ψ b g := by
  haveI := nonarch_finiteAdeleRing (F := F)
  haveI := nonarch_pi (G := fun _ : κ => Af F)
  obtain ⟨U, hU⟩ := GlobalTheory.WeilM.HaarUniq.exists_invariant hg
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun b₀ => ?_
  have hc : IsLocallyConstant fun z : ((κ → Af F) × (κ → Af F)) × (κ → Af F) =>
      finChar ψ (z.2 ⬝ᵥ z.1.2 + p2 (⅟(2 : AF F)) * (z.1.1 ⬝ᵥ z.1.2)) :=
    (finChar_isLocallyConstant ψ hψ.1).comp_continuous ((continuous_snd.dotProduct continuous_fst.snd).add
      (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd)))
  have hK : IsCompact (tsupport fun x => g (x + b₀.1)) := hg.2.comp_homeomorph (Homeomorph.addRight b₀.1)
  have h1 := hK.eventually_forall_of_forall_eventually (x₀ := b₀)
    (P := fun b x => finChar ψ (x ⬝ᵥ b.2 + p2 (⅟(2 : AF F)) * (b.1 ⬝ᵥ b.2)) =
      finChar ψ (x ⬝ᵥ b₀.2 + p2 (⅟(2 : AF F)) * (b₀.1 ⬝ᵥ b₀.2))) fun x _ => by
      filter_upwards [hc.eventually_eq (b₀, x),
        (hc.comp_continuous (continuous_const.prodMk continuous_snd :
          Continuous fun z : ((κ → Af F) × (κ → Af F)) × (κ → Af F) => (b₀, z.2))).eventually_eq (b₀, x)] with z h h'
      exact h.trans h'.symm
  have h2 : ∀ᶠ b : (κ → Af F) × (κ → Af F) in 𝓝 b₀, b.1 - b₀.1 ∈ U :=
    (continuous_fst.sub continuous_const).continuousAt.eventually_mem (by simpa using U.mem_nhds_zero)
  filter_upwards [h1, h2] with b hb hb'
  funext x
  have e : g (x + b.1) = g (x + b₀.1) := by rw [← hU _ hb' (x + b₀.1)]; congr 1; abel
  simp only [fw, finS, e]
  by_cases hx : x ∈ tsupport fun x => g (x + b₀.1)
  · rw [hb x hx]
  · rw [show g (x + b₀.1) = 0 from image_eq_zero_of_notMem_tsupport (f := fun x => g (x + b₀.1)) hx, mul_zero, mul_zero]

open GroundTheory.Global in

theorem annih {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {U : Set (Af F)} (hU : U ∈ 𝓝 0) :
    ∃ C : Set (Af F), IsCompact C ∧ ∀ b, (∀ a ∈ U, finChar ψ (a * b) = 1) → b ∈ C := by
  let χ : AddChar (AF F) Circle :=
    { toFun := fun x => ⟨ψ x, by simpa [Submonoid.unitSphere] using GlobalTheory.StdCharFromIsStd.norm_psi hψ x⟩
      map_zero_eq_one' := Subtype.ext ψ.map_zero_eq_one
      map_add_eq_mul' := fun a b => Subtype.ext (ψ.map_add_eq_mul a b) }
  obtain ⟨ξ, hξ, -⟩ := existsUnique_eq_adelicChar_mul χ (hψ.1.subtype_mk _) fun k => Subtype.ext (hψ.2.1 k)
  have h0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one hψ
    have := hξ x
    rw [map_zero, zero_mul, AddChar.map_zero_eq_one] at this
    exact hx (congrArg Subtype.val this)
  obtain ⟨d, hd, hd'⟩ := exists_forall_mul_mem_of_mem_nhds hU
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 := fun h => hd (RingOfIntegers.coe_injective (h.trans (map_zero _).symm))
  refine ⟨_, (isCompact_idealFiniteAdeles (traceDualIdeal F 1)).image
    (continuous_const_mul (algebraMap F (Af F) (ξ * algebraMap (𝓞 F) F d)⁻¹)), fun b hb =>
    ⟨algebraMap F (Af F) (ξ * algebraMap (𝓞 F) F d) * b, ?_, ?_⟩⟩
  · refine (forall_finiteAdelicChar_mul_eq_one_iff 1 _).1 fun x hx => ?_
    have h1 := hb _ (hd' x (by rw [← SetLike.mem_coe, ← idealFiniteAdeles_one]; exact hx))
    have h2 := hξ (finiteAdeleInr (algebraMap F (Af F) (algebraMap (𝓞 F) F d) * x * b))
    rw [algebraMap_mul_finiteAdeleInr, ← finiteAdelicChar_apply] at h2
    rw [show x * (algebraMap F (Af F) (ξ * algebraMap (𝓞 F) F d) * b) =
      algebraMap F (Af F) ξ * (algebraMap F (Af F) (algebraMap (𝓞 F) F d) * x * b) by rw [map_mul]; ring, ← h2]
    exact Subtype.ext h1
  · beta_reduce
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (mul_ne_zero h0 hd0), map_one, one_mul]

theorem trace_nondeg (b : mixedSpace F) (h : ∀ y, Algebra.trace ℝ (mixedSpace F) (b * y) = 0) : b = 0 := by
  refine (latticeBasis F).ext_elem fun j => ?_
  have := h (mixedEmbedding F ((integralBasis F).traceDual j))
  rw [← (latticeBasis F).sum_repr b] at this
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, latticeBasis_apply, ← map_mul,
    GlobalTheory.ThK.Dbl.Dense.trace_emb, Module.Basis.trace_mul_traceDual] at this
  simpa [apply_ite] using this

theorem exists_half_trace : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : mixedSpace F, x ≠ 0 → ∃ a, ‖a‖ * ‖x‖ ≤ K ∧
    Algebra.trace ℝ (mixedSpace F) (x * a) = 1 / 2 :=
  exists_half ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := mixedSpace F) (F' := ℝ)).toLinearMap ∘ₗ
    Algebra.traceForm ℝ (mixedSpace F)) fun x hx => trace_nondeg x fun y => DFunLike.congr_fun hx y

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}
  {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem ev_pure {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {ι ι' I e}
    (he : IsEv B M M₁ ι ι' I e) : ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
      (ef : ((Fin n × Fin d → Af F) → ℂ) → (Fin n₁ × Fin d₁ → Af F) → ℂ), ei ≠ 0 ∧
      ∀ φ ∈ SB (Fin n × Fin d → Af F), ef φ ∈ SB _ ∧ ∀ f : SInf F _, e (pureA F f φ) = pureA F (ei f) (ef φ) := by
  obtain ⟨ei, ev, h0, h1, h2⟩ := he.loc
  have : ∀ φ, φ ∈ SB (Fin n × Fin d → Af F) → ∃ φ₁ ∈ SB (Fin n₁ × Fin d₁ → Af F),
      ∀ f : SInf F _, e (pureA F f φ) = pureA F (ei f) φ₁ := fun g hg => by
    have := GlobalTheory.ThK.Dbl.Dense.mem_span_pf hg
    clear hg
    induction this using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, rfl⟩ := hx
      have hv : ∀ᶠ v in cofinite, φ v = M.vac v := by
        filter_upwards [hφ.2, hM.std] with v a b using a.trans b.symm
      refine ⟨GlobalTheory.ThK.Dbl.Dense.pf fun v => ev v (φ v), GlobalTheory.ThK.Dbl.Dense.pf_mem ⟨fun v => (h1 v).2 ▸ ⟨_, hφ.1 v, rfl⟩, ?_⟩,
        fun f => h2 f φ hφ.1 hv⟩
      filter_upwards [hv, hM₁.std] with v a b
      rw [a, (h1 v).1, b]; rfl
    | zero => exact ⟨0, zero_mem _, fun f => by simp only [GlobalTheory.ThK.Dbl.Dense.pureA_zero, map_zero]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, add_mem ha hb, fun f => by simp only [GlobalTheory.ThK.Dbl.Dense.pureA_add, map_add, ha', hb']⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, ha'⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, fun f => by simp only [GlobalTheory.ThK.Dbl.Dense.pureA_smul, map_smul, ha']⟩
  choose! ef h using this
  exact ⟨ei, ef, h0, h⟩

end PositivityTheory.ThKCT.Ad

end
