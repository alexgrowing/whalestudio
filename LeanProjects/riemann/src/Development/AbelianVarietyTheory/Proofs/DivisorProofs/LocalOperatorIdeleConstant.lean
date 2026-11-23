import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.SchrLocConst

open scoped GlobalTheory.VacAny

theorem locallyCompact_Fv {F : Type} [Field F] [NumberField F] (v : Pl F) : LocallyCompactSpace (Fv F v) := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hC : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup hC (x := 0) (hO.mem_nhds (zero_mem _))

theorem isLocallyConstant_schr {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    (v : Pl F) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) :
    IsLocallyConstant fun w : (κ → Fv F v) × (κ → Fv F v) => schr (GlobalTheory.LatVac.psiAt ψ v) w φ := by
  haveI := locallyCompact_Fv v
  set f : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) → ℂ := fun p => schr (GlobalTheory.LatVac.psiAt ψ v) p.1 φ p.2 with hf
  have hloc : IsLocallyConstant f := by
    have hlin : Continuous fun p : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) =>
        p.2 ⬝ᵥ p.1.2 + ⅟(2 : Fv F v) * (p.1.1 ⬝ᵥ p.1.2) := by fun_prop
    exact ((GlobalTheory.SchrSB.isLocallyConstant_addChar _ (GlobalTheory.SchrSB.continuous_psiAt ψ hψ v)).comp_continuous hlin).mul
      (hφ.1.comp_continuous (by fun_prop))
  rw [IsLocallyConstant.iff_eventually_eq] at hloc ⊢
  intro w₀
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds w₀.1
  set K : Set (κ → Fv F v) := (fun p : (κ → Fv F v) × (κ → Fv F v) => p.1 - p.2) '' (tsupport φ ×ˢ C) with hKdef
  have hK : IsCompact K := (hφ.2.isCompact.prod hCc).image (by fun_prop)
  have h1 : ∀ᶠ w in 𝓝 w₀, ∀ x ∈ K, f (w, x) = f (w₀, x) := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have ha := hloc (w₀, x)
    have hb : Tendsto (fun q : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) => (w₀, q.2)) (𝓝 (w₀, x)) (𝓝 (w₀, x)) :=
      ((continuous_const.prodMk continuous_snd).tendsto (w₀, x))
    filter_upwards [ha, hb.eventually ha] with q hq hq'
    rw [hq, ← hq']
  have h2 : ∀ᶠ w in 𝓝 w₀, w.1 ∈ C := continuous_fst.continuousAt.preimage_mem_nhds hC
  have hz : ∀ w : (κ → Fv F v) × (κ → Fv F v), w.1 ∈ C → ∀ x ∉ K, f (w, x) = 0 := by
    intro w hw x hx
    have : φ (x + w.1) = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ⟨(x + w.1, w.1), ⟨h, hw⟩, by simp⟩
    simp only [hf, schr, this, mul_zero]
  filter_upwards [h1, h2] with w hw hwC
  funext x
  by_cases hx : x ∈ K
  · exact hw x hx
  · exact (hz w hwC x hx).trans (hz w₀ (mem_of_mem_nhds hC) x hx).symm

theorem locCo_smul {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module (AF F) V]
    {Bf : V → V → AF F} {κ : Type} [Fintype κ] (co : Darboux Bf κ) (v : Pl F) (a : AF F) (w : V) :
    GlobalTheory.LatVac.locCo co v (a • w) = evFin F v a • GlobalTheory.LatVac.locCo co v w := by
  ext k <;> simp [GlobalTheory.LatVac.locCo, map_smul]

theorem exists_linear_locCo_shift (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (H : Plane E n n₁)
    (H' : Plane E d d₁) (v : Pl F) : ∃ L : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
      ∀ z : AE F E, GlobalTheory.LatVac.locCo M.co v (cA σ z • Matrix.vecMulVec (incV F H.y) (incV F H'.x)) = L (compFin F E v z) := by
  set m := Matrix.vecMulVec (incV F H.y) (incV F H'.x)
  let g₀ : E →ₗ[F] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun e => GlobalTheory.LatVac.locCo M.co v (((1 : AF F) ⊗ₜ[F] σ e : AE F E) • m)
      map_add' := fun e e' => by rw [map_add, TensorProduct.tmul_add, add_smul, map_add]
      map_smul' := fun c e => by
        have h1 : (((1 : AF F) ⊗ₜ[F] σ (c • e) : AE F E) • m) =
            algebraMap F (AF F) c • ((((1 : AF F) ⊗ₜ[F] σ e : AE F E)) • m) := by
          rw [AlgHom.map_smul_of_tower, TensorProduct.tmul_smul, smul_assoc, algebraMap_smul]
        rw [h1, locCo_smul, AlgHom.commutes, algebraMap_smul, RingHom.id_apply] }
  let L := TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton (Fv F v) _ g₀)
  refine ⟨L, fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, add_smul, map_add, map_add, map_add, hx, hy]
  | tmul a e =>
    have e1 : cA σ (a ⊗ₜ[F] e) = a • ((1 : AF F) ⊗ₜ[F] σ e : AE F E) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
    have e2 : compFin F E v (a ⊗ₜ[F] e) = evFin F v a ⊗ₜ[F] e := rfl
    rw [e1, smul_assoc, locCo_smul, e2, TensorProduct.AlgebraTensorModule.lift_tmul]
    rfl

theorem shiftB_locOp_locallyConstant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (H : Plane E n n₁)
    (H' : Plane E d d₁), Continuous B.ψ → ∀ (v : Pl F), ∀ ψ ∈ SB (Fin n × Fin d → Fv F v),
    ∃ g : (Fv F v ⊗[F] E) → (Fin n × Fin d → Fv F v) → ℂ, IsLocallyConstant g ∧
      ∀ l ∈ idelesAt E (evFin F v), locOp v (M.co.rho B.ψ (partFin v (shiftB σ H H' l))) ψ =
        g ((GlobalTheory.Doubling.unitFin F E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W M H H' hψ v ψ hψs
  obtain ⟨L, hL⟩ := exists_linear_locCo_shift F E σ M H H' v
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  refine ⟨fun x => schr (GlobalTheory.LatVac.psiAt B.ψ v) (L x) ψ,
    (isLocallyConstant_schr B.ψ hψ v hψs).comp_continuous (IsModuleTopology.continuous_of_linearMap L), fun l _ => ?_⟩
  rw [(locOp_rho M.co hψ v _ hψs).2, shiftB, hL]
  rfl

end GlobalTheory.SchrLocConst
