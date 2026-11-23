import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid.Sep

theorem density {G H ι : Type} [Group G] [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (hn : ∀ g v, ‖π g v‖ = ‖v‖)
    (hi : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (L : ι → (H →L[ℂ] ℂ)) (v : ι → H) (h : ∀ g, ∑ i, L i (π g (v i)) = 0) (A : H →ₗ[ℂ] H) :
    ∑ i, L i (A (v i)) = 0 := by
  classical
  have key : ∀ T : H →L[ℂ] H, ∑ i, L i (T (v i)) = 0 := by
    intro T
    let e := PiLp.continuousLinearEquiv (p := 2) (𝕜 := ℂ) (β := fun _ : ι => H)
    let amp : (H →L[ℂ] H) → (PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) := fun B =>
      e.symm.toContinuousLinearMap ∘L
        (ContinuousLinearMap.pi fun i => B ∘L ContinuousLinearMap.proj i) ∘L e.toContinuousLinearMap
    have hamp : ∀ B x i, (amp B x).ofLp i = B (x.ofLp i) := fun _ _ _ => rfl
    let ξ : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 v
    have hξ : ∀ i, ξ.ofLp i = v i := fun _ => rfl
    let S0 : Submodule ℂ (PiLp 2 (fun _ : ι => H)) := Submodule.span ℂ (Set.range fun g => amp (π g) ξ)
    let S := S0.topologicalClosure
    have : CompleteSpace S := S0.isClosed_topologicalClosure.completeSpace_coe
    have hmul : ∀ g g' x, amp (π (g * g')) x = amp (π g) (amp (π g') x) := by
      intro g g' x
      refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
      simp only [hamp, map_mul, ContinuousLinearMap.mul_apply]
    have hone : ∀ x, amp (π 1) x = x := by
      intro x
      refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
      simp only [hamp, map_one, ContinuousLinearMap.one_apply]
    have hS0 : ∀ g, S0 ≤ S0.comap (amp (π g)).toLinearMap := by
      intro g
      rw [Submodule.span_le]
      rintro _ ⟨g', rfl⟩
      show amp (π g) (amp (π g') ξ) ∈ S0
      rw [← hmul]
      exact Submodule.subset_span ⟨g * g', rfl⟩
    have hS : ∀ g, ∀ x ∈ S, amp (π g) x ∈ S := by
      intro g x hx
      have h1 : S0 ≤ S.comap (amp (π g)).toLinearMap := fun y hy => S0.le_topologicalClosure (hS0 g hy)
      have h2 : IsClosed ((S.comap (amp (π g)).toLinearMap : Submodule ℂ _) : Set (PiLp 2 (fun _ : ι => H))) :=
        S0.isClosed_topologicalClosure.preimage (amp (π g)).continuous
      exact Submodule.topologicalClosure_minimal S0 h1 h2 hx
    have hinH : ∀ g (a b : H), ⟪π g a, π g b⟫_ℂ = ⟪a, b⟫_ℂ := fun g a b =>
      ({ toLinearMap := (π g).toLinearMap, norm_map' := hn g } : H →ₗᵢ[ℂ] H).inner_map_map a b
    have hin : ∀ g (x y : PiLp 2 (fun _ : ι => H)), ⟪amp (π g) x, amp (π g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
      intro g x y
      simp only [PiLp.inner_apply, hamp, hinH]
    have hback : ∀ g x, amp (π g) (amp (π g⁻¹) x) = x := by
      intro g x
      rw [← hmul, mul_inv_cancel, hone]
    have hP : ∀ g x, S.starProjection (amp (π g) x) = amp (π g) (S.starProjection x) := by
      intro g x
      have h1 : amp (π g) (S.starProjection x) ∈ S := hS g _ (S.starProjection_apply_mem x)
      have h2 : amp (π g) (x - S.starProjection x) ∈ Sᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        rw [← hback g u, hin]
        exact Submodule.inner_right_of_mem_orthogonal (hS _ u hu) (S.sub_starProjection_mem_orthogonal x)
      have h3 : amp (π g) x = amp (π g) (S.starProjection x) + amp (π g) (x - S.starProjection x) := by
        rw [← map_add, add_sub_cancel]
      rw [h3, map_add, Submodule.starProjection_eq_self_iff.2 h1,
        (Submodule.starProjection_apply_eq_zero_iff S).2 h2, add_zero]
    have hcomp : ∀ i j, ∃ c : ℂ, ∀ y : H,
        (S.starProjection (WithLp.toLp 2 (Pi.single j y))).ofLp i = c • y := by
      intro i j
      let Q : H →L[ℂ] H := (PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : ι => H) i) ∘L S.starProjection ∘L
        e.symm.toContinuousLinearMap ∘L ContinuousLinearMap.single (R := ℂ) (φ := fun _ : ι => H) j
      have hQ : ∀ y, Q y = (S.starProjection (WithLp.toLp 2 (Pi.single j y))).ofLp i := fun _ => rfl
      obtain ⟨c, hc⟩ := GlobalTheory.hilbert_schur H G π hn hi Q (by
        intro g
        refine ContinuousLinearMap.ext fun y => ?_
        simp only [ContinuousLinearMap.mul_apply, hQ]
        have h4 : WithLp.toLp 2 (Pi.single j (π g y)) = amp (π g) (WithLp.toLp 2 (Pi.single j y)) := by
          refine (WithLp.ext_iff 2).2 (funext fun k => ?_)
          rw [hamp]
          by_cases hk : k = j
          · subst hk; simp
          · simp [hk]
        rw [h4, hP, hamp])
      exact ⟨c, fun y => by rw [← hQ, hc]; simp⟩
    choose c hc using hcomp
    have hPz : ∀ (z : PiLp 2 (fun _ : ι => H)) i, (S.starProjection z).ofLp i = ∑ j, c i j • z.ofLp j := by
      intro z i
      have hz : z = ∑ j, WithLp.toLp 2 (Pi.single j (z.ofLp j)) := by
        refine (WithLp.ext_iff 2).2 (funext fun k => ?_)
        rw [WithLp.ofLp_sum, Finset.sum_apply]
        simp [Pi.single_apply]
      conv_lhs => rw [hz]
      rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => hc i j _
    have hPT : ∀ z, S.starProjection (amp T z) = amp T (S.starProjection z) := by
      intro z
      refine (WithLp.ext_iff 2).2 (funext fun i => ?_)
      rw [hPz, hamp, hPz, map_sum]
      simp only [hamp, map_smul]
    have hξS : ξ ∈ S := S0.le_topologicalClosure (Submodule.subset_span ⟨1, hone ξ⟩)
    have hTξ : amp T ξ ∈ S := by
      rw [← Submodule.starProjection_eq_self_iff.2 hξS, ← hPT]
      exact S.starProjection_apply_mem _
    let Φ : PiLp 2 (fun _ : ι => H) →L[ℂ] ℂ := ∑ i, (L i) ∘L (PiLp.proj (p := 2) (𝕜 := ℂ) (β := fun _ : ι => H) i)
    have hΦ : ∀ z, Φ z = ∑ i, L i (z.ofLp i) := by
      intro z
      simp only [Φ, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_comp',
        Function.comp_apply]
      rfl
    have hker : S ≤ LinearMap.ker (Φ : PiLp 2 (fun _ : ι => H) →ₗ[ℂ] ℂ) := by
      refine Submodule.topologicalClosure_minimal S0 ?_ Φ.isClosed_ker
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      show Φ (amp (π g) ξ) = 0
      rw [hΦ]
      simpa only [hamp, hξ] using h g
    have h5 : Φ (amp T ξ) = 0 := hker hTξ
    rw [hΦ] at h5
    simpa only [hamp, hξ] using h5
  let Wv : Submodule ℂ H := Submodule.span ℂ (Set.range v)
  have : FiniteDimensional ℂ Wv := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  have : CompleteSpace Wv := FiniteDimensional.complete ℂ Wv
  let B : H →L[ℂ] H := (LinearMap.toContinuousLinearMap (A ∘ₗ Wv.subtype)) ∘L Wv.orthogonalProjectionOnto
  have hB : ∀ i, B (v i) = A (v i) := by
    intro i
    have hv : v i ∈ Wv := Submodule.subset_span ⟨i, rfl⟩
    show A (Wv.subtype (Wv.orthogonalProjectionOnto (v i))) = A (v i)
    rw [show v i = ((⟨v i, hv⟩ : Wv) : H) from rfl, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    rfl
  simpa only [hB] using key B

theorem exists_umat {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ k : Formalism.REAL.UJ ε, umat k = g := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    have h1 : Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) = 1 := by rw [hg']; exact hJ
    simpa only [Matrix.mul_assoc] using h1
  have hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp hl
  exact ⟨⟨⟨g, _, hr, hl⟩, hg⟩, rfl⟩

theorem density_sob {n : ℕ} {ε : Fin n → Bool} {H ι : Type} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ) (ℓ : ι → (H →ₗ[ℂ] ℂ))
    (hℓ : ∀ i, Sobolev₂ (lieG G) (trRep σ P) (ℓ i)) (v : ι → H) (hv : ∀ i, v i ∈ smSub G (trRep σ P))
    (h0 : ∀ g ∈ UJset ε, ∑ i, ℓ i (σ g (v i)) = 0) (A : H →ₗ[ℂ] H) (hA : ∀ i, A (v i) ∈ smSub G (trRep σ P)) :
    ∑ i, ℓ i (A (v i)) = 0 := by
  classical
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hsg := fun i => GlobalTheory.SobGarding.sobCont_gard n ε H σ P G hP hG hσ (ℓ i) (hℓ i)
  have hmul : ∀ (g g' : Formalism.REAL.UJ ε) (x : H), σ (umat g) (σ (umat g') x) = σ (umat (g * g')) x := by
    intro g g' x
    rw [show umat (g * g') = umat g * umat g' from rfl, hσ.1.2 _ (hmem g) _ (hmem g'),
      ContinuousLinearMap.comp_apply]
  let π : Formalism.REAL.UJ ε →* (H →L[ℂ] H) :=
    { toFun := fun g => σ (umat g)
      map_one' := hσ.1.1
      map_mul' := fun g g' => by
        refine ContinuousLinearMap.ext fun x => ?_
        rw [ContinuousLinearMap.mul_apply]
        exact (hmul g g' x).symm }
  have hπ : ∀ g x, π g x = σ (umat g) x := fun _ _ => rfl
  have hn : ∀ g x, ‖π g x‖ = ‖x‖ := fun g x => hσ.2.1 _ (hmem g) x
  have hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ x ∈ S, π g x ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hinv
    refine hi S hS fun g hg x hx => ?_
    obtain ⟨k, rfl⟩ := exists_umat hg
    exact hinv k x hx
  have hgard : ∀ φ, IsTest φ → ∑ i, ℓ i (gard ε σ φ (A (v i))) = 0 := by
    intro φ hφ
    have hint : ∀ w : H, MeasureTheory.Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • σ (umat g) w)
        (Formalism.REAL.muG ε) := fun w => hφ.integrable (continuous_orbit hσ w)
    let Gl : H →ₗ[ℂ] H :=
      { toFun := gard ε σ φ
        map_add' := fun w w' => by
          simp only [gard, map_add, smul_add]
          exact MeasureTheory.integral_add (hint w) (hint w')
        map_smul' := fun c w => by
          simp only [gard, map_smul, RingHom.id_apply]
          rw [← MeasureTheory.integral_smul]
          congr 1
          funext g
          exact smul_comm _ _ _ }
    choose Cs hCs using fun i => (hsg i).1 φ hφ
    let Lc : ι → (H →L[ℂ] ℂ) := fun i => LinearMap.mkContinuous ((ℓ i).comp Gl) (Cs i) (fun w => hCs i w)
    have hLc : ∀ i w, Lc i w = ℓ i (gard ε σ φ w) := fun _ _ => rfl
    have hrel : ∀ g, ∑ i, Lc i (π g (v i)) = 0 := by
      intro g
      simp only [hLc, hπ]
      have hsm : ∀ i, σ (umat g) (v i) ∈ smSub G (trRep σ P) := fun i => sigma_mem hP hG hσ (hv i) (hmem g)
      rw [Finset.sum_congr rfl fun i _ => ((hsg i).2 _ (hsm i)).2 φ hφ]
      rw [← MeasureTheory.integral_finsetSum _ fun i _ => hφ.integrable ((hsg i).2 _ (hsm i)).1]
      have h1 : ∀ g' : Formalism.REAL.UJ ε,
          ∑ i, φ (umat g') • ℓ i (σ (umat g') (σ (umat g) (v i))) = 0 := by
        intro g'
        rw [← Finset.smul_sum]
        simp only [hmul]
        rw [h0 _ (hmem (g' * g)), smul_zero]
      simp only [h1, MeasureTheory.integral_zero]
    have h2 := density π hn hirr Lc v hrel A
    simpa only [hLc] using h2
  have hcont : ∀ i, Continuous fun g : Formalism.REAL.UJ ε => ℓ i (σ (umat g) (A (v i))) :=
    fun i => ((hsg i).2 _ (hA i)).1
  have hF : Continuous fun g : Formalism.REAL.UJ ε => ∑ i, ℓ i (σ (umat g) (A (v i))) :=
    continuous_finsetSum _ fun i _ => hcont i
  have h1 := eq_zero_of_forall_test hF (fun φ hφ => by
    simp only [Finset.smul_sum]
    rw [MeasureTheory.integral_finsetSum _ fun i _ => hφ.integrable (hcont i)]
    rw [Finset.sum_congr rfl fun i _ => (((hsg i).2 _ (hA i)).2 φ hφ).symm]
    exact hgard φ hφ)
  have h2 : ∀ x : H, σ (umat (1 : Formalism.REAL.UJ ε)) x = x := fun x => by
    rw [show umat (1 : Formalism.REAL.UJ ε) = 1 from rfl, hσ.1.1, ContinuousLinearMap.one_apply]
  simpa only [h2] using h1

private theorem sum_smul_T_update_eq_zero_of_sum_eq_zero {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : MMap M} (heq : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v))
    (hct : ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x)
    (τ : D.what₂.Tau) (A : M.sm τ →ₗ[ℂ] M.sm τ) {ι : Type} [Fintype ι]
    (c : ι → ℂ) (v : ι → M.Vec) (h : ∑ i, c i • T (v i) = 0) :
    ∑ i, c i • T (Function.update (v i) τ (A (v i τ))) = 0 := by
  classical
  have : CompleteSpace (M.H τ) := (M.ds τ).1
  have hsm : M.sm τ = smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := sm_eq M τ
  have hσ : IsURepOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.1
  have hirr : IsIrredOn (UJset (M.ε τ)) (M.σ τ) := (M.ds τ).2.2.2.1
  funext x
  choose ℓ hℓ hℓT using fun i => hct τ (v i) x
  obtain ⟨A', hA'⟩ := LinearMap.exists_extend ((M.sm τ).subtype ∘ₗ A)
  have hA'' : ∀ w : M.sm τ, A' (w : M.H τ) = (A w : M.H τ) := fun w => LinearMap.congr_fun hA' w
  have hvs : ∀ i, c i • ((v i τ : M.sm τ) : M.H τ) ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by
    intro i
    rw [← hsm]
    exact (M.sm τ).smul_mem _ (v i τ).2
  have hAs : ∀ i, A' (c i • ((v i τ : M.sm τ) : M.H τ)) ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by
    intro i
    rw [map_smul, hA'', ← hsm]
    exact (M.sm τ).smul_mem _ (A (v i τ)).2
  have hrel : ∀ g ∈ UJset (M.ε τ), ∑ i, ℓ i (M.σ τ g (c i • ((v i τ : M.sm τ) : M.H τ))) = 0 := by
    intro g hg
    have hg' : (M.fr τ)⁻¹ * g * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg
    have hrep : ∀ w, M.σ τ g w = M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) w := fun w => by
      rw [show M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = trRep (M.σ τ) (M.fr τ) ((M.fr τ)⁻¹ * g * M.fr τ) from rfl,
        trRep_conj (M.fr_unit τ)]
    have hmemw : ∀ i, M.σ τ g (v i τ) ∈ M.sm τ := fun i => by
      have h2 := sigma_mem (M.fr_unit τ) (M.fr_gram τ) hσ (by rw [← hsm]; exact (v i τ).2) hg
      rwa [← hsm] at h2
    have hT1 : ∀ i, ℓ i (M.σ τ g (v i τ)) = T (v i) (x * atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)) := fun i =>
      (hℓT i ⟨_, hmemw i⟩).trans (congrFun (heq τ _ hg' (v i) ⟨_, hmemw i⟩ (hrep _)) x)
    simp only [map_smul, hT1]
    have h1 := congrFun h (x * atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ))
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using h1
  have key := density_sob (M.fr_unit τ) (M.fr_gram τ) hσ hirr ℓ (fun i => hℓ i)
    (fun i => c i • ((v i τ : M.sm τ) : M.H τ)) hvs hrel A' hAs
  have e : ∀ i, c i • T (Function.update (v i) τ (A (v i τ))) x =
      ℓ i (A' (c i • ((v i τ : M.sm τ) : M.H τ))) := by
    intro i
    rw [map_smul, map_smul, hA'', hℓT i]
  rw [Finset.sum_apply, Pi.zero_apply]
  simp only [Pi.smul_apply]
  rw [Finset.sum_congr rfl fun i _ => e i]
  exact key

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}

theorem intersection_update_fsHerm_neg_one {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (A : M.sm τ →ₗ[ℂ] M.sm τ) {ι : Type} [Fintype ι]
    (c : ι → ℂ) (v : ι → M.Vec) (h : ∑ i, c i • T (v i) = 0) :
    ∑ i, c i • T (Function.update (v i) τ (A (v i τ))) = 0 := by
  exact sum_smul_T_update_eq_zero_of_sum_eq_zero hT.equiv hT.cont τ A c v h

private theorem sum_smul_T_map_eq_zero_of_sum_eq_zero {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : MMap M} (heq : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v))
    (hct : ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x)
    (A : ∀ τ, M.sm τ →ₗ[ℂ] M.sm τ) {ι : Type} [Fintype ι]
    (c : ι → ℂ) (v : ι → M.Vec) (h : ∑ i, c i • T (v i) = 0) : ∑ i, c i • T (fun τ => A τ (v i τ)) = 0 := by
  classical
  have step : ∀ s : Finset D.what₂.Tau,
      ∑ i, c i • T (fun τ => if τ ∈ s then A τ (v i τ) else v i τ) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h
    | @insert a s ha ih =>
      have h1 := sum_smul_T_update_eq_zero_of_sum_eq_zero heq hct a (A a) c (fun i τ => if τ ∈ s then A τ (v i τ) else v i τ) ih
      have hva : ∀ i, (if a ∈ s then A a (v i a) else v i a) = v i a := fun i => by simp [ha]
      have hv : ∀ i, (fun τ => if τ ∈ insert a s then A τ (v i τ) else v i τ) =
          Function.update (fun τ => if τ ∈ s then A τ (v i τ) else v i τ) a (A a (v i a)) := by
        intro i
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · rw [Function.update_of_ne hτ]
          simp [hτ]
      simp only [hva] at h1
      simp only [hv]
      exact h1
  simpa using step Finset.univ

theorem slots {T : MMap M} (hT : IsMultMap θ M J χ T) (A : ∀ τ, M.sm τ →ₗ[ℂ] M.sm τ) {ι : Type} [Fintype ι]
    (c : ι → ℂ) (v : ι → M.Vec) (h : ∑ i, c i • T (v i) = 0) : ∑ i, c i • T (fun τ => A τ (v i τ)) = 0 := by
  exact sum_smul_T_map_eq_zero_of_sum_eq_zero hT.equiv hT.cont A c v h

private theorem sobCont_zero_twisted_operators {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Lie : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Sobolev₂ Lie σ (0 : H →ₗ[ℂ] ℂ) :=
  ⟨[], 0, by simp, fun w _ => by simp⟩

private theorem sobCont_add_twisted_operators {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ ℓ' : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ Lie σ ℓ) (h' : Sobolev₂ Lie σ ℓ') : Sobolev₂ Lie σ (ℓ + ℓ') := by
  obtain ⟨S, C, hS, hC⟩ := h
  obtain ⟨S', C', hS', hC'⟩ := h'
  refine ⟨S ++ S', |C| + |C'|, fun l hl => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.1 hl with hl | hl
    · exact hS l hl
    · exact hS' l hl
  · have e1 := hC w hw
    have e2 := hC' w hw
    have p1 : 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum := List.sum_nonneg fun y hy => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.1 hy
      exact norm_nonneg _
    have p2 : 0 ≤ (S'.map fun l => ‖l.foldr (dRep σ) w‖).sum := List.sum_nonneg fun y hy => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.1 hy
      exact norm_nonneg _
    rw [List.map_append, List.sum_append, LinearMap.add_apply]
    have e3 := norm_add_le (ℓ w) (ℓ' w)
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) p1, mul_le_mul_of_nonneg_right (le_abs_self C') p2,
      mul_nonneg (abs_nonneg C) p2, mul_nonneg (abs_nonneg C') p1]

private theorem sobCont_smul_twisted_operators {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ Lie σ ℓ) (c : ℂ) : Sobolev₂ Lie σ (c • ℓ) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  rw [LinearMap.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg c)

private theorem equivariant_and_sobCont_slice {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) ∧
    (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact ⟨hT.equiv, hT.cont⟩
  | zero =>
    refine ⟨fun τ g _ v w _ => ?_, fun τ v y => ⟨0, sobCont_zero_twisted_operators _ _, fun w => ?_⟩⟩
    · simp only [MultilinearMap.zero_apply]
      rfl
    · simp
  | add T T' _ _ hT hT' =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v y => ?_⟩
    · rw [MultilinearMap.add_apply, MultilinearMap.add_apply, hT.1 τ g hg v w hw, hT'.1 τ g hg v w hw]
      rfl
    · obtain ⟨ℓ, h1, h2⟩ := hT.2 τ v y
      obtain ⟨ℓ', h1', h2'⟩ := hT'.2 τ v y
      exact ⟨ℓ + ℓ', sobCont_add_twisted_operators h1 h1', fun w => by simp [h2, h2']⟩
  | smul c T _ hT =>
    refine ⟨fun τ g hg v w hw => ?_, fun τ v y => ?_⟩
    · rw [MultilinearMap.smul_apply, MultilinearMap.smul_apply, hT.1 τ g hg v w hw]
      rfl
    · obtain ⟨ℓ, h1, h2⟩ := hT.2 τ v y
      exact ⟨c • ℓ, sobCont_smul_twisted_operators h1 c, fun w => by simp [h2]⟩

theorem multT_eq_zero {u : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)} (hu : u ∈ MultT θ M J χ) {x : ⨂[ℂ] τ, M.sm τ}
    (hx : x ≠ 0) (h : u x = 0) : u = 0 := by
  classical
  obtain ⟨T, rfl⟩ : ∃ T : MMap M, u = PiTensorProduct.lift T :=
    ⟨PiTensorProduct.lift.symm u, (LinearEquiv.apply_symm_apply _ u).symm⟩
  have hTm : T ∈ Mult θ M J χ := by
    have h1 := (mem_multT θ M J χ _).1 hu
    rwa [LinearEquiv.symm_apply_apply] at h1
  have hw := equivariant_and_sobCont_slice hTm
  have huT : ∀ w : M.Vec, PiTensorProduct.lift T (PiTensorProduct.tprod ℂ w) = T w :=
    fun w => PiTensorProduct.lift.tprod w
  have hxs : x ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ)) := by
    rw [PiTensorProduct.span_tprod_eq_top]
    trivial
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hxs
  have hxsum : x = ∑ a : f.support, f a • PiTensorProduct.tprod ℂ (a : M.Vec) := by
    rw [← hf, Finsupp.sum, ← Finset.sum_coe_sort]
  have h0 : ∑ a : f.support, f a • T a = 0 := by
    rw [hxsum, map_sum] at h
    simpa only [map_smul, huT] using h
  obtain ⟨w', hw'⟩ : ∃ w' : M.Vec, tprodInnerFun w' x ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx (eq_zero_of_tprodInnerFun x hne)
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro w
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
  rw [huT]
  let A : ∀ τ, M.sm τ →ₗ[ℂ] M.sm τ := fun τ => (innerSL ℂ (w' τ)).toLinearMap.smulRight (w τ)
  have h1 := sum_smul_T_map_eq_zero_of_sum_eq_zero hw.1 hw.2 A (fun a : f.support => f a) (fun a => (a : M.Vec)) h0
  have hA : ∀ a : f.support, T (fun τ => A τ ((a : M.Vec) τ)) =
      (∏ τ, ⟪w' τ, (a : M.Vec) τ⟫_ℂ) • T w := fun a =>
    MultilinearMap.map_smul_univ T (fun τ => ⟪w' τ, (a : M.Vec) τ⟫_ℂ) w
  simp only [hA, smul_smul, ← Finset.sum_smul] at h1
  have hs : ∑ a : f.support, f a * ∏ τ, ⟪w' τ, (a : M.Vec) τ⟫_ℂ = tprodInnerFun w' x := by
    rw [hxsum, map_sum]
    simp only [map_smul, tprodInnerFun_tprod, smul_eq_mul]
  rw [hs] at h1
  exact (smul_eq_zero.1 h1).resolve_left hw'

end GlobalTheory.Grid.Sep

end
