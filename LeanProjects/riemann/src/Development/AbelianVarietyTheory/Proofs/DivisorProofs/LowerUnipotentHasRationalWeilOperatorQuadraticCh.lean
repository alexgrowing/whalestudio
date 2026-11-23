import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

noncomputable section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

def mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) :
    ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun φ x := χ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulQ_apply {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) (x : κ → R) : mulQ χ h A φ x = χ (quad h A x) * φ x := rfl

theorem mulQ_neg_mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) : mulQ χ h (-A) (mulQ χ h A φ) = φ := by
  funext x
  rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

theorem mulQ_schr {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (χ : AddChar R ℂ) (B : Matrix κ κ R)
    (hB : Bᵀ = B) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    mulQ χ (⅟2) (-B) (schr χ w φ) = schr χ (w.1, B *ᵥ w.1 + w.2) (mulQ χ (⅟2) (-B) φ) := by
  have hB' : (-B)ᵀ = -B := by rw [Matrix.transpose_neg, hB]
  funext x
  have key := quad_add (-B) hB' x w.1 w.2
  rw [Matrix.neg_mulVec, neg_neg] at key
  simp only [mulQ_apply, schr]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key]

theorem act_unip {F R κ : Type} [Field F] [CommRing R] [Algebra F R] [Fintype κ] [DecidableEq κ] (b : Matrix κ κ F)
    (w : (κ → R) × (κ → R)) :
    act ((Matrix.fromBlocks 1 0 b 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) w =
      (w.1, b.map (algebraMap F R) *ᵥ w.1 + w.2) := by
  rw [Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), act_fromBlocks]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def qI (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem eventually_integral (x : κ → AF F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
  eventually_all.2 fun i => (x i).2.2

theorem finite_mulSupport {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
  refine (Filter.eventually_cofinite.1 (hφ.2.and (eventually_integral x))).subset fun v hv => ?_
  intro h
  apply hv
  change φ v _ = 1
  rw [h.1, ind, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
    from h.2), Pi.one_apply]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mulQ_mem_SB {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) {φ : (κ → K) → ℂ} (hφ : φ ∈ SB (κ → K)) :
    mulQ χ h A φ ∈ SB (κ → K) :=
  ⟨((GlobalTheory.SchrSBFin.isLocallyConstant_addChar χ hχ).comp_continuous (continuous_quad h A)).mul hφ.1, hφ.2.mul_left⟩

theorem mulQ_bijOn {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) :
    Set.BijOn (mulQ χ h A) (SB (κ → K) : Set _) (SB (κ → K) : Set _) := by
  refine Set.InvOn.bijOn (f' := mulQ χ h (-A)) ⟨fun φ _ => mulQ_neg_mulQ χ h A φ, fun φ _ => ?_⟩
    (fun φ hφ => mulQ_mem_SB χ hχ h A hφ) (fun φ hφ => mulQ_mem_SB χ hχ h (-A) hφ)
  have := mulQ_neg_mulQ χ h (-A) φ
  rwa [neg_neg] at this

theorem quad_mem {v : Pl F} {h : Fv F v} (hh : h ∈ v.adicCompletionIntegers F) {A : Matrix κ κ (Fv F v)}
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F) {x : κ → Fv F v} (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) :
    quad h A x ∈ v.adicCompletionIntegers F := by
  unfold quad
  refine mul_mem hh (sum_mem fun i _ => mul_mem (hx i) (sum_mem fun j _ => mul_mem (hA i j) (hx j)))

theorem invOf_two_eq (v : Pl F) : ⅟(2 : Fv F v) = algebraMap F (Fv F v) (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem eventually_mulQ_ind (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (b : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (ind κ v) = ind κ v := by
  filter_upwards [GlobalTheory.psiLoc_eventually_trivial_integers ψ hψ, eventually_algebraMap_mem_integers (2⁻¹ : F),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_algebraMap_mem_integers (b i j)] with v h1 h2 h3
  funext x
  rw [mulQ_apply]
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have hq : quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) x ∈ v.adicCompletionIntegers F :=
      quad_mem (show ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F by rw [invOf_two_eq]; exact h2) (fun i j => neg_mem (h3 i j)) hx
    rw [GlobalTheory.LatVac.psiAt_apply, h1 _ hq, one_mul]
  · rw [ind, Set.indicator_of_notMem (show x ∉ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), mul_zero]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem invOf_two_eq' (R : Type) [CommRing R] [Algebra F R] [Invertible (2 : R)] : ⅟(2 : R) = algebraMap F R (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem evFin_quad (b : Matrix κ κ F) (v : Pl F) (x : κ → AF F) :
    evFin F v (quad (⅟2) (-(b.map (algebraMap F (AF F)))) x) =
      quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) (fun i => evFin F v (x i)) := by
  simp [quad, dotProduct, Matrix.mulVec, map_sum, GlobalTheory.VacAny.evFin_invOf_two]

theorem psi_quad_rat (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (ξ : κ → F) :
    ψ (quad (⅟2) (-(b.map (algebraMap F (AF F)))) (fun i => algebraMap F (AF F) (ξ i))) = 1 := by
  have h := map_quad (algebraMap F (AF F)) (2⁻¹ : F) (-b) ξ
  rw [Matrix.map_neg _ (map_neg _), ← invOf_two_eq'] at h
  rw [← h]
  exact hψ.2.1 _

theorem thetaSum_mulQ (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) Φ) = thetaSum F Φ := by
  unfold thetaSum
  congr 1
  funext ξ
  rw [mulQ_apply, psi_quad_rat ψ hψ b ξ, one_mul]

theorem archMul_neg_mul (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F))
    (y : κ → mixedEmbedding.mixedSpace F) : archMul h A y * archMul h (-A) y = 1 := by
  unfold archMul
  rw [← AddChar.map_add_eq_mul, quad_neg, map_neg, neg_neg, neg_add_cancel, AddChar.map_zero_eq_one]

theorem surjective_arch (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    Function.Surjective (SchwartzMap.smulLeftCLM ℂ (archMul h A) : SInf F κ →L[ℂ] SInf F κ) := by
  intro f
  refine ⟨SchwartzMap.smulLeftCLM ℂ (archMul h (-A)) f, ?_⟩
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul, smul_eq_mul, ← mul_assoc,
    archMul_neg_mul, one_mul]

theorem at_pairA (a : AF F) : At (evI F) (pairA F (fstA F a) 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem mulQ_pure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (f : SInf F κ)
    {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) :
    mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (SchwartzMap.smulLeftCLM ℂ
                   (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
        (fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (φ v)) := by
  funext x
  set Q := quad (⅟2) (-(b.map (algebraMap F (AF F)))) x with hQ
  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.adelicAddChar_eq_archimedean_mul_finprod_local F ψ hψ.1 Q
  simp only [hQ, evFin_quad] at hfin hprod
  have harch : ψ (pairA F (fstA F Q) 0) =
      archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) := by
    rw [hψ.2.2 _ (at_pairA Q)]
    have e1 : evI F (pairA F (fstA F Q) 0) =
        quad (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) :=
      map_quad (qI F) _ _ x
    rw [e1, archMul, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [← hQ] at hprod
  change ψ Q * (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) =
    (SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
      (fun i => evI F (x i)) * ∏ᶠ v, (GlobalTheory.LatVac.psiAt ψ v (quad (⅟2) (-(b.map (algebraMap F (Fv F v))))
        (fun i => evFin F v (x i))) * φ v fun i => evFin F v (x i))
  rw [finprod_mul_distrib hfin (finite_mulSupport hφ x), SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    smul_eq_mul, hprod, harch]
  ring

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad archMul)

open scoped Classical in

theorem hasOp_unip : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (b : Matrix κ κ F), bᵀ = b → HasOp ψ (Matrix.fromBlocks 1 0 b 1) := by
  intro F _ _ ψ hψ κ _ _ b hb
  have hB : ∀ (R : Type) [CommRing R] [Algebra F R], (b.map (algebraMap F R))ᵀ = b.map (algebraMap F R) :=
    fun R _ _ => by rw [← Matrix.transpose_map, hb]
  refine ⟨mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))), 1,
    SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))),
    fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))), one_ne_zero,
    surjective_arch _ _, fun v => mulQ_bijOn _ (GlobalTheory.VacAny.continuous_psiV hψ.1 v) _ _, fun v w φ _ => ?_,
    eventually_mulQ_ind ψ hψ.1 b, fun f φ hφ => ⟨mulQ_pure ψ hψ b f hφ, fun w => ?_, ?_⟩⟩
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [thetaSum_mulQ ψ hψ b, one_mul]

end GlobalTheory.RatWeilUnip

end
