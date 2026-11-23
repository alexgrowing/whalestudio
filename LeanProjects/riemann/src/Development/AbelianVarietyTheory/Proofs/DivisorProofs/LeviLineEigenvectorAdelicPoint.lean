import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchUnipotentRadicalMem
open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Orb (archMat)

noncomputable section
namespace GlobalTheory.TorFin

open scoped Matrix.Norms.Operator in

theorem exp_mulVec_eigen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (l : ℂ) (h : A *ᵥ v = l • v) :
    ∃ c : ℂ, NormedSpace.exp A *ᵥ v = c • v := by
  have hp : ∀ k : ℕ, A ^ k *ᵥ v = l ^ k • v := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M *ᵥ v
        map_add' := fun a b => Matrix.add_mulVec a b v
        map_smul' := fun a b => Matrix.smul_mulVec a b v }
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL L
  have hcl : IsClosed ((Submodule.span ℂ {v} : Submodule ℂ (Fin n → ℂ)) : Set (Fin n → ℂ)) :=
    Submodule.closed_of_finiteDimensional _
  have h2 : L (NormedSpace.exp A) ∈ Submodule.span ℂ {v} := by
    refine hcl.mem_of_tendsto h1 (Filter.Eventually.of_forall fun s => ?_)
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    change A ^ k *ᵥ v ∈ _
    rw [hp]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h2
  exact ⟨c, hc.symm⟩

theorem line_mulVec_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (w : InfinitePlace F) (τ : EmbOver E w)
      (Y : Matrix (Fin n) (Fin n) ℂ) (l : ℂ), Y *ᵥ (fun i => τ.1 (x i)) = l • (fun i => τ.1 (x i)) →
      ∀ β : ℝ → GAd σ J, GlobalTheory.LeviHC.IsLineOf σ J τ Y β → ∀ s, ∃ t : AF F ⊗[F] E,
        (matHom _ σ J (β s)).1 *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = t • fun i => inclR (F := F) (AF F) (x i) := by
  intro F E _ _ _ _ _ σ hσ n J x w τ Y l hY β hβ s
  classical
  obtain ⟨y, hg, hy⟩ := hβ s
  obtain ⟨c, hc⟩ := exp_mulVec_eigen (s • Y) (fun i => τ.1 (x i)) (s • l) (by
    rw [Matrix.smul_mulVec, hY, smul_assoc])
  rw [← hy] at hc
  set g := β s
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom (AF F) σ J g).1 with hM
  have hinf : ∀ u, M.map (compInf F E u) = (matHom _ σ J (projArch σ J u g)).1 := fun u =>
    (congrArg Units.val (matHom_projArch σ J u g)).symm
  have hinf_ne : ∀ u, u ≠ w → M.map (compInf F E u) = 1 := fun u hu => by
    rw [hinf u, hg, projArch_embArch_ne σ J hu, map_one]; rfl
  have hfin : ∀ v, M.map (compFin F E v) = 1 := fun v => by
    have h := matHom_proj σ J v g
    rw [hg, proj_embArch, map_one, ← hg] at h
    exact (congrArg Units.val h).symm
  let Φ : AF F ⊗[F] E →+* ℂ := (infEmb τ).comp (compInf F E w)
  have hΦM : M.map Φ = archMat σ J τ y := by
    rw [GlobalTheory.Orb.archMat_apply, ← projArch_embArch_self σ J w y, ← hg, ← hinf w, Matrix.map_map]; rfl
  have hΦi : ∀ e : E, Φ (inclR (F := F) (AF F) e) = τ.1 e := fun e => by
    change infEmb τ ((1 : w.Completion) ⊗ₜ[F] e) = τ.1 e
    rw [infEmb_tmul, map_one, one_mul]
  have key : ∀ z : AF F ⊗[F] E, (∀ u, u ≠ w → compInf F E u z = 0) → (∀ v, compFin F E v z = 0) → Φ z = 0 → z = 0 :=
    fun z h1 h2 h3 => GlobalTheory.AdelicU.Supp.adTens_ext (fun u => by
      by_cases hu : u = w
      · subst hu
        rw [map_zero]
        exact (GlobalTheory.AdelicU.infEmb_bijective hσ τ).1 (h3.trans (map_zero _).symm)
      · rw [h1 u hu, map_zero]) fun v => by rw [h2 v, map_zero]
  obtain ⟨e, he⟩ := (GlobalTheory.AdelicU.infEmb_bijective hσ τ).2 (c - 1)
  refine ⟨1 + extZeroArch w e, funext fun i => sub_eq_zero.1 (key _ (fun u hu => ?_) (fun v' => ?_) ?_)⟩
  · rw [map_sub, RingHom.map_mulVec, hinf_ne u hu, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_add,
      compInf_extZeroArch_ne hu e, map_one, add_zero, one_mul, Function.comp_apply, sub_self]
  · rw [map_sub, RingHom.map_mulVec, hfin v', Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_add,
      compFin_extZeroArch w v' e, map_one, add_zero, one_mul, Function.comp_apply, sub_self]
  · have hΦe : Φ (extZeroArch w e) = c - 1 := by
      change infEmb τ (compInf F E w (extZeroArch w e)) = c - 1
      rw [compInf_extZeroArch_self, he]
    have h1 : (Φ ∘ fun j => inclR (F := F) (AF F) (x j)) = fun j => τ.1 (x j) := funext fun j => hΦi (x j)
    rw [map_sub, RingHom.map_mulVec, hΦM, h1, hc, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
      map_add, hΦe, map_one, hΦi]
    ring

end GlobalTheory.TorFin
