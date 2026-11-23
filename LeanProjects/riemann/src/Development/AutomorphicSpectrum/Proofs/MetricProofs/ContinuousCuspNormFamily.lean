import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NzCont

section Emb

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)

def charVec (a : 𝓞 E) : (E →+* ℂ) → ℂ := fun s => s (algebraMap (𝓞 E) E a)

def toChar (s : E →+* ℂ) : 𝓞 E →* ℂ := (s.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ)

theorem toChar_injective : Function.Injective (toChar (E := E)) := by
  intro s s' h
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  exact DFunLike.congr_fun h a

theorem span_charVec : Submodule.span ℂ (Set.range (charVec (E := E))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ (toChar_injective (E := E))
  rw [Fintype.linearIndependent_iff] at li
  have hl := li (fun s => f fun j => if s = j then 1 else 0) (by
    funext a
    have h1 : f (charVec a) = 0 := hf (Submodule.subset_span ⟨a, rfl⟩)
    rw [LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, smul_eq_mul, Pi.zero_apply]
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_mul]
    exact mul_comm (_ : ℂ) _)
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ f v, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun s _ => (congrArg (v s • ·) (hl s)).trans (smul_zero _)

open Classical in

theorem exists_coeff (s : E →+* ℂ) : ∃ c : 𝓞 E →₀ ℂ, ∀ s' : E →+* ℂ,
    ∑ a ∈ c.support, c a * s' (algebraMap (𝓞 E) E a) = if s' = s then 1 else 0 := by
  have h : (Pi.single s 1 : (E →+* ℂ) → ℂ) ∈ Submodule.span ℂ (Set.range (charVec (E := E))) := by
    rw [span_charVec]
    trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h
  refine ⟨c, fun s' => ?_⟩
  have h2 := congrFun hc s'
  simpa [Finsupp.sum, Finset.sum_apply, charVec, Pi.single_apply] using h2

end Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem mem_eigSp_iff (R : RiemLat E g Λ) {s : 𝓞 E →+* ℂ} {x : Fin g → ℂ} :
    x ∈ eigSp R.B s ↔ ∀ a, R.B a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

open Classical in

theorem eigComp_eq (R : RiemLat E g Λ) (s : E →+* ℂ) (c : 𝓞 E →₀ ℂ)
    (hc : ∀ s' : E →+* ℂ, ∑ a ∈ c.support, c a * s' (algebraMap (𝓞 E) E a) = if s' = s then 1 else 0)
    (u : Λ) :
    eigComp R.B (s.comp (algebraMap (𝓞 E) E)) (R.P u) = ∑ a ∈ c.support, c a • R.P (a • u) := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hy : ∀ a : 𝓞 E, R.P (a • u) = ∑ s' : E →+* ℂ, s' (algebraMap (𝓞 E) E a) •
      eigComp R.B (s'.comp (algebraMap (𝓞 E) E)) (R.P u) := by
    intro a
    rw [R.act]
    conv_lhs => rw [← h4 (R.P u)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    exact (mem_eigSp_iff R).1 ((h3 _).1 _) a
  simp_rw [hy, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hc]
  simp [ite_smul]

variable {X : Type} [TopologicalSpace X]

theorem continuous_eigComp (R : X → RiemLat E g Λ) (hP : ∀ v, Continuous fun x => (R x).P v)
    (s : 𝓞 E →+* ℂ) (u : Λ) : Continuous fun x => eigComp (R x).B s ((R x).P u) := by
  classical
  obtain ⟨c, hc⟩ := exists_coeff (extEmb s)
  have h : ∀ x, eigComp (R x).B s ((R x).P u) = ∑ a ∈ c.support, c a • (R x).P (a • u) := by
    intro x
    have h1 := eigComp_eq (R x) (extEmb s) c hc u
    rwa [extEmb_comp] at h1
  simp_rw [h]
  exact continuous_finset_sum _ fun a _ => (hP (a • u)).const_smul (c a)

theorem continuous_ip (R : X → RiemLat E g Λ) (hH : Continuous fun x => (R x).Hm) {p q : X → Fin g → ℂ}
    (hp : Continuous p) (hq : Continuous q) : Continuous fun x => (R x).ip (p x) (q x) := by
  unfold RiemLat.ip
  exact hq.dotProduct (hH.matrix_mulVec (continuous_star.comp hp))

theorem continuous_nzOf {Ψ : Type} [Fintype Ψ] (R : X → RiemLat E g Λ)
    (hP : ∀ v, Continuous fun x => (R x).P v) (hH : Continuous fun x => (R x).Hm)
    (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) {r : ℕ} (v : Fin r → Λ) :
    Continuous fun x => (R x).nzOf σ I v := by
  unfold RiemLat.nzOf
  refine Continuous.div_const (continuous_finset_prod _ fun τ _ => ?_) _
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_matrix fun a b => ?_
  exact continuous_ip R hH (continuous_eigComp R hP _ _) (continuous_eigComp R hP _ _)

theorem continuous_nz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ)
    (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), (∀ v, Continuous fun x => (R x).P v) →
    (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ I hP hH
  by_cases h : ∃ r v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsNzFamily I r v
  · have e : (fun x => (R x).nz σ I) = fun x => (R x).nzOf σ I h.choose_spec.choose := by
      funext x
      simp only [RiemLat.nz, dif_pos h]
    rw [e]
    exact continuous_nzOf R hP hH σ I _
  · have e : (fun x => (R x).nz σ I) = fun _ => 1 := by
      funext x
      simp only [RiemLat.nz, dif_neg h]
    rw [e]
    exact continuous_const

end GlobalTheory.CompanionTheory.Ar.Cusp.NzCont
