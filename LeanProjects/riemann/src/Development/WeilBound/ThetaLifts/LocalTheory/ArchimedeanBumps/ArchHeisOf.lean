import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.TracePiReal
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.DictIrr
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval

noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKG.Loc.Cone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open scoped Classical

variable {κ : Type} [Fintype κ]

def evR : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst (Ainf F) (Af F))

theorem evR_eq (a : AF F) : evI F a = evR a := rfl

def lf : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] Module.Dual ℝ (κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.mk₂ ℝ (fun b y => -(2 * Real.pi) * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ b))
    (fun a b y => by rw [dotProduct_add, map_add, mul_add]) (fun c b y => by rw [dotProduct_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring)
    (fun b x y => by rw [add_dotProduct, map_add, mul_add]) (fun c b y => by rw [smul_dotProduct, map_smul, smul_eq_mul, smul_eq_mul]; ring)

theorem lf_surj [IsTotallyReal F] : Function.Surjective (lf (F := F) (κ := κ)) := by
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (IsTotallyReal.isReal w.1)⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm, injective_iff_map_eq_zero]
  intro b hb
  have h1 : -(2 * Real.pi) * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (b ⬝ᵥ b) = 0 := LinearMap.congr_fun hb b
  have h2 := (mul_eq_zero.1 h1).resolve_left (neg_ne_zero.2 (by positivity))
  rw [Algebra.trace_prod_apply, Subsingleton.elim (b ⬝ᵥ b).2 0, map_zero, add_zero, trace_pi_real] at h2
  simp only [dotProduct, Prod.fst_sum, Finset.sum_apply, Prod.fst_mul, Pi.mul_apply] at h2
  funext i
  refine Prod.ext (funext fun w => ?_) (Subsingleton.elim _ _)
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => Finset.sum_nonneg fun i _ => mul_self_nonneg _).1 h2 w (Finset.mem_univ _)
  exact mul_self_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg _).1 h3 i (Finset.mem_univ _))

theorem schr_acts {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a b : κ → AF F) (ha : At (evI F) a) (hb : At (evI F) b) (f : SInf F κ) :
    Acts (evI F) (schr ψ (a, b)) f ⇑(ψ (⅟(2 : AF F) * (a ⬝ᵥ b)) • SchwartzMap.smulLeftCLM ℂ
      (ex (LinearMap.toContinuousLinearMap (lf fun i => evI F (b i)))) (SchwartzMap.compSubConstCLM ℂ (-fun i => evI F (a i)) f)) := by
  intro r hr
  funext x
  have hz : At (evI F) (x ⬝ᵥ b) := fun s hs => by
    rw [← dotProduct_smul, hb s hs, dotProduct_zero]
  have e1 : evI F (x ⬝ᵥ b) = (fun i => evI F (x i)) ⬝ᵥ fun i => evI F (b i) := by
    simp only [evR_eq, dotProduct, map_sum, map_mul]
  have e2 : (fun i => evI F ((x + a) i)) = (fun i => evI F (x i)) - -fun i => evI F (a i) := by
    funext i
    simp [evR_eq]
  simp only [schr, tens, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply (ex_temp _), SchwartzMap.compSubConstCLM_apply,
    smul_eq_mul]
  rw [AddChar.map_add_eq_mul, hψ.2.2 _ hz, e1, e2, hr.1 x a ha]
  have e3 : ex (LinearMap.toContinuousLinearMap (lf fun i => evI F (b i))) (fun i => evI F (x i)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        ((fun i => evI F (x i)) ⬝ᵥ fun i => evI F (b i)) : ℝ)) := by
    change Complex.exp (Complex.I * ((-(2 * Real.pi) * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        ((fun i => evI F (x i)) ⬝ᵥ fun i => evI F (b i)) : ℝ) : ℂ)) = _
    congr 1; push_cast; ring
  rw [e3]; ring

theorem at_lin {M N : Type} [AddCommGroup M] [Module (AF F) M] [AddCommGroup N] [Module (AF F) N] (T : M →ₗ[AF F] N) {z : M}
    (h : At (evI F) z) : At (evI F) (T z) := fun u hu => by rw [← map_smul, h u hu, map_zero]

theorem std_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ψ ≠ 1 := by
  intro h
  have hd : (0 : ℝ) < Module.finrank ℝ (mixedEmbedding.mixedSpace F) := by
    rw [mixedEmbedding.finrank]; exact_mod_cast Module.finrank_pos
  set d : ℝ := ((Module.finrank ℝ (mixedEmbedding.mixedSpace F) : ℕ) : ℝ) with hd'
  have e0 : evI F (realAd F (2 * d)⁻¹) = algebraMap ℝ _ (2 * d)⁻¹ := RingEquiv.apply_symm_apply _ _
  have := hψ.2.2 (realAd F (2 * d)⁻¹) (fun s hs => Prod.ext (by
    change s.1 * _ = 0
    rw [evI_eq_zero.1 hs, zero_mul]) (mul_zero s.2))
  rw [h, e0, Algebra.trace_algebraMap, nsmul_eq_mul, ← hd', AddChar.one_apply] at this
  have e : -(2 * Real.pi * Complex.I) * ((d * (2 * d)⁻¹ : ℝ) : ℂ) = -(Real.pi * Complex.I) := by
    rw [show d * (2 * d)⁻¹ = 2⁻¹ by field_simp]; push_cast; ring
  rw [e, Complex.exp_neg, Complex.exp_pi_mul_I] at this
  norm_num at this

theorem archHeis_of : ArchHeis := by
  intro F E _ _ _ _ _ σ B n d X W M hB
  refine ⟨fun u => (GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F _ B.ψ hB.std.1 (std_ne_one hB.std) hB.std.2.1).1 _, fun u hu f => ?_⟩
  exact ⟨_, schr_acts hB.std _ _ (at_lin ((LinearMap.fst _ _ _).comp M.co.e.toLinearMap) hu)
    (at_lin ((LinearMap.snd _ _ _).comp M.co.e.toLinearMap) hu) f⟩

theorem rest_pure (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h1 : ∀ v, φ v ∈ SB _)
    (h2 : ∀ᶠ u in cofinite, φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1) :
    Rest (evI F) f (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · refine finprod_congr fun v => congrArg (φ v) (funext fun i => ?_)
    have : z i = realAd F 1 * z i := (congrFun (at_iff.1 hz) i).symm
    rw [Pi.add_apply, map_add, this, map_mul, show evFin F v (realAd F 1) = 0 from map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v),
      zero_mul, add_zero]
  · exact Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
      ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ h1 h2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h2⟩, rfl⟩

theorem pure_inj (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (h2 : ∀ᶠ u in cofinite, φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1) {f g : SInf F κ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) : f = g := by
  have := PositivityTheory.ThKF.tensInj F κ φ h0 h2 ∅ 1 (fun _ => 1) (fun _ => f - g) (fun _ => φ) (fun _ _ _ => rfl) (by
    funext x
    have := congrFun h x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure] at this
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul, this])
  have h3 := congrArg (TensorProduct.rid ℂ (SInf F κ) ∘ LinearMap.lTensor (SInf F κ) (PiTensorProduct.isEmptyEquiv _).toLinearMap) this
  simpa [sub_eq_zero] using h3

theorem eiDense_of (hS : WeakInt) : EiDense := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ H H' e u ei ev hc hl l hne
  by_contra hn
  push Not at hn
  haveI := hc.base.cm.1
  obtain ⟨f₀, hf₀⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push Not at h
    exact hl.ne (ContinuousLinearMap.ext h)
  have hh : ∀ z, ∀ Φ ∈ schA F _, e (M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (e Φ) :=
    hc.ev.elim (fun h => h.1.Heisenberg₂) fun h => h.1.Heisenberg₂
  have hv : ∀ v, M.vac v ∈ SB _ := fun v => (hc.good.vac v).1
  have hv₁ : ∀ v, M₁.vac v ∈ SB _ := fun v => (hc.good₁.vac v).1
  have hp : ∀ f, e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) M₁.vac := fun f => by
    rw [hl.pure f M.vac hv (Eventually.of_forall fun _ => rfl), funext fun v => (hl.vac v).1]
  refine hne (irr hS l (ei f₀) hf₀ fun L A => ?_)
  obtain ⟨b₀, hb₀⟩ := lf_surj (F := F) (L : (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ)
  let up : mixedEmbedding.mixedSpace F → AF F := fun y =>
    LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y)
  have hup : ∀ y, evI F (up y) = y := fun y => RingEquiv.apply_symm_apply _ _
  have hat : ∀ y : Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F, At (evI F) fun i => up (y i) := fun y s hs => funext fun i =>
    Prod.ext (by
      change s.1 * _ = 0
      rw [evI_eq_zero.1 hs, zero_mul]) (mul_zero s.2)
  let z := M₁.co.e.symm (fun i => up (-A i), fun i => up (b₀ i))
  have hz : At (evI F) z := at_lin M₁.co.e.symm.toLinearMap fun s hs => Prod.ext (hat (-A) s hs) (hat b₀ s hs)
  have hu : At (evI F) (incM F H.ι * z * (incM F H'.ι)ᵀ) := fun s hs => by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz s hs, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨f₁, hf₁⟩ := (archHeis_of F E σ B n d X W M hc.base).2 _ hu f₀
  have a1 : M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ M.vac :=
    hf₁ _ (rest_pure f₀ M.vac hv hc.good.std)
  have a2 := schr_acts hc.base.std _ _ (hat (-A)) (hat b₀) (ei f₀) _ (rest_pure (ei f₀) M₁.vac hv₁ hc.good₁.std)
  have a3 := hh z _ (rest_pure f₀ M.vac hv hc.good.std).2
  change e (M.co.rho B.ψ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ M.vac)) = M₁.co.rho B.ψ z (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ M.vac)) at a3
  rw [a1, hp, hp, Darboux.rho, LinearEquiv.apply_symm_apply] at a3
  have a4 := pure_inj M₁.vac (fun v => (hc.good₁.vac v).2.1) hc.good₁.std (a3.trans a2)
  have a5 := hn f₁
  rw [a4, map_smul, smul_eq_mul, mul_eq_zero] at a5
  have e1 : (-fun i => evI F (up ((-A) i))) = A := by funext i; simp [hup]
  have e2 : LinearMap.toContinuousLinearMap (lf fun i => evI F (up (b₀ i))) = L := by
    simp only [hup]
    ext1 x
    exact LinearMap.congr_fun hb₀ x
  rw [e1, e2] at a5
  exact a5.resolve_left ((B.ψ.val_isUnit _).ne_zero)

end PositivityTheory.ThKG.Loc.Bump

end
