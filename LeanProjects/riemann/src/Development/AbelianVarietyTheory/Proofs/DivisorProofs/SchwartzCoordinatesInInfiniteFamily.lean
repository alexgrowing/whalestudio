import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem repr_map {R : Type} [CommRing R] [Algebra D.host.F R] (π : AF D.host.F →ₐ[D.host.F] R) {d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    π ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k) =
      (Algebra.TensorProduct.basis R ε).repr (Algebra.TensorProduct.map π (AlgHom.id D.host.F D.host.E) z) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul, Finsupp.mapRange_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord
variable {D : D7}
theorem finPart_eq (z : AE D) : finPart D z = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
theorem infPart_eq (z : AE D) : infPart D z = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
theorem snd_eq (a : AF D.host.F) : a.2 = sndA D.host.F a := rfl
theorem fin_coord {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k).2 =
      (Algebra.TensorProduct.basis (Af D.host.F) ε).repr (finPart D z) k := by
  rw [snd_eq, finPart_eq]
  exact repr_map (sndA D.host.F) ε z k
end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

def finCoord {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (Fin m × Fin n × Fin d → Af D.host.F) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  let b := Algebra.TensorProduct.basis (Af D.host.F) ε
  exact
  { toFun := fun y p => b.equivFun (y p.1 p.2.1) p.2.2
    invFun := fun c i j => b.equivFun.symm fun k => c (i, j, k)
    left_inv := fun y => by
      funext i j
      simp only
      conv_rhs => rw [← b.equivFun.symm_apply_apply (y i j)]
    right_inv := fun c => by
      funext p
      simp only [LinearEquiv.apply_symm_apply]
    continuous_toFun := continuous_pi fun p =>
      ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)).comp
        ((continuous_apply p.2.1).comp (continuous_apply p.1))
    continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
      (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap).comp
        (continuous_pi fun k => continuous_apply (i, j, k)) }

theorem finCoord_apply {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (y : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) (p : Fin m × Fin n × Fin d) :
    finCoord ε y p = (Algebra.TensorProduct.basis (Af D.host.F) ε).repr (y p.1 p.2.1) p.2.2 := by
  simp [finCoord]

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem continuous_mixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
      fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

def realCoord (σ : (D.what₂.Tau → ℂ) →+ AE D) {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →+ (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F) where
  toFun c p := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
    (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => c τ p.1 p.2.1) p.2.2))
  map_zero' := by
    funext p
    have : (σ fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ p.1 p.2.1) = 0 := σ.map_zero
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (fstA D.host.F
      ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ p.1 p.2.1)
        p.2.2)) = 0
    rw [this, map_zero, Finsupp.zero_apply, map_zero, map_zero]
  map_add' c c' := by
    funext p
    have : (σ fun τ => (c + c') τ p.1 p.2.1) = σ (fun τ => c τ p.1 p.2.1) + σ (fun τ => c' τ p.1 p.2.1) :=
      σ.map_add _ _
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (fstA D.host.F
      ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => (c + c') τ p.1 p.2.1) p.2.2)) = _
    rw [this, map_add, Finsupp.add_apply, map_add, map_add]
    rfl

theorem continuous_realCoord {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Continuous σ) {m n d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) : Continuous (realCoord σ (m := m) (n := n) ε) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine continuous_pi fun p => (continuous_mixed D.host.F).comp (continuous_fst.comp ?_)
  exact ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.toLinearMap)).comp
    (hσ.comp (continuous_pi fun τ => (continuous_apply p.2.1).comp ((continuous_apply p.1).comp (continuous_apply τ))))

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem finCoord_coord {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) :
    (fun p => (coord ε x p).2) = finCoord ε (fun i j => finPart D (x i j)) := by
  funext p
  rw [finCoord_apply]
  exact fin_coord ε (x p.1 p.2.1) p.2.2

theorem inf_coord {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k).1 =
      (Algebra.TensorProduct.basis (Ainf D.host.F) ε).repr (infPart D z) k := by
  rw [infPart_eq]
  exact repr_map (fstA D.host.F) ε z k

theorem realCoord_compAt {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D} (hsf : ∀ a, finPart D (s a) = a) (hsi : ∀ a, infPart D (s a) = 0)
    {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) :
    (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) =
      realCoord σ ε (fun τ i j => compAt θ τ x i j) := by
  funext p
  have hx : x p.1 p.2.1 = s (finPart D (x p.1 p.2.1)) + σ (fun τ => compAt θ τ x p.1 p.2.1) :=
    congrFun (congrFun (GlobalTheory.SchwartzBruhatTensor.decomp hσ hsf hsi x) p.1) p.2.1
  have h0 : fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (s (finPart D (x p.1 p.2.1))) p.2.2) = 0 :=
    (inf_coord ε _ _).trans (by rw [hsi, map_zero, Finsupp.zero_apply])
  show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
      (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (x p.1 p.2.1) p.2.2)) =
    InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
      (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => compAt θ τ x p.1 p.2.1) p.2.2))
  conv_lhs => rw [hx]
  rw [map_add, Finsupp.add_apply, map_add (fstA D.host.F), h0, zero_add]

end GlobalTheory.SchwartzCoord

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

theorem injective_realCoord {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) : Function.Injective (realCoord σ (m := m) (n := n) ε) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  funext τ i j
  have h0 : infPart D (σ fun τ => c τ i j) = 0 := by
    apply (Algebra.TensorProduct.basis (Ainf D.host.F) ε).repr.injective
    ext k
    rw [map_zero, Finsupp.zero_apply]
    have e : InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
        (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => c τ i j) k)) = 0 :=
      congrFun hc (i, j, k)
    have e2 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective).1 e
    rw [← e2, repr_map (fstA D.host.F) ε]
    rfl
  have h1 := hσ.comp (fun τ => c τ i j) τ
  rw [h0, map_zero] at h1
  exact h1.symm

theorem mem_schwartzA_comp_coord : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n d : ℕ)
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (φ : WeilM.schA D.host.F (Fin m × Fin n × Fin d)),
    φ.1 ∘ coord ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  intro D θ hθ m n d ε φ
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, -, hsf, hsi⟩ := GlobalTheory.SchwartzBruhatTensor.exists_finSection D
  obtain ⟨M, hM⟩ : ∃ M : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F),
      ⇑M = ⇑(realCoord σ ε) := ⟨(realCoord σ ε).toRealLinearMap (continuous_realCoord hσ.cont ε), rfl⟩
  have hMi : Function.Injective M.toLinearMap := by
    intro a b h
    have h' : M a = M b := h
    rw [hM] at h'
    exact injective_realCoord hσ ε h'
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz _).1 hMi
  have hbound : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖M x‖) ^ k := ⟨1, K, fun x => by
    have h := hK.le_mul_dist x 0
    rw [dist_zero_right, map_zero, dist_zero_right] at h
    have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
    calc ‖x‖ ≤ K * ‖M x‖ := h
      _ ≤ K * (1 + ‖M x‖) ^ 1 := by rw [pow_one]; exact mul_le_mul_of_nonneg_left (by linarith) hK0⟩
  obtain ⟨φ, hφ⟩ := φ
  induction hφ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let f' : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ := SchwartzMap.compCLM ℂ M.hasTemperateGrowth hbound f
    have hf' : ∀ c, f' c = f (M c) := fun c => rfl
    let g' : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := g ∘ finCoord ε
    have hg' : g' ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
      ⟨hg.1.comp_continuous (finCoord ε).continuous, hg.2.comp_homeomorph _⟩
    have heq : WeilM.pureA D.host.F f g ∘ coord ε =
        fun x => f' (fun τ i j => compAt θ τ x i j) * g' (fun i j => finPart D (x i j)) := by
      funext x
      rw [hf']
      show f (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) * g (fun p => (coord ε x p).2) =
        f (M (fun τ i j => compAt θ τ x i j)) * g (finCoord ε (fun i j => finPart D (x i j)))
      rw [realCoord_compAt hσ hsf hsi ε x, finCoord_coord ε x, ← hM]
    rw [heq]
    exact Submodule.subset_span ⟨f', g', hg', rfl⟩
  | zero =>
    have e : (0 : (Fin m × Fin n × Fin d → AdeleRing (𝓞 D.host.F) D.host.F) → ℂ) ∘ coord ε = 0 := rfl
    rw [e]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    have e : (Φ + Ψ) ∘ coord ε = Φ ∘ coord ε + Ψ ∘ coord ε := rfl
    rw [e]
    exact Submodule.add_mem _ h1 h2
  | smul a Φ _ h =>
    have e : (a • Φ) ∘ coord ε = a • (Φ ∘ coord ε) := rfl
    rw [e]
    exact Submodule.smul_mem _ a h

end GlobalTheory.SchwartzCoord
