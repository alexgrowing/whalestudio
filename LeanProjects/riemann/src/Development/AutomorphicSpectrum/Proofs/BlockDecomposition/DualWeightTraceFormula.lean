import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMemOfStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEuclideanModelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactLieActionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightAntitoneOfFiniteDimensionalStableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualOperatorCommutesLieStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightInInvariantSubmoduleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightOfUnitaryDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerEqZeroOfVanishOnHighestStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightIntegralOfUnitaryStatement

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.CharDec

variable {n : ℕ}

theorem core (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H)
    (hg : Formalism.REAL.GlRel G) (hh : ∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ)
    (hd : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
      (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H,
        HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) :
    ∃ F : Finset (Fin n → ℤ), (∀ ν ∈ F, Antitone ν) ∧ (∀ ν : Fin n → ℤ, Antitone ν → ν ∉ F → hwOf G (wtR ν) = ⊥) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S) = ∑ ν ∈ F, trOn (hwOf G (wtR ν)) S * weylChar ν z := by
  classical
  have hp : ∀ ν : Fin n → ℤ, Antitone ν → ∃ p : H →ₗ[ℂ] H, (∀ a b w, p (G a b w) = G a b (p w)) ∧
      (∀ v ∈ hwOf G (wtR ν), p v = v) ∧
      (∀ (μ : Fin n → ℝ) (v : H), μ ≠ wtR ν → Formalism.REAL.KHighest (fun _ => true) G μ v → p v = 0) ∧
      ∀ S : H →ₗ[ℂ] H, (∀ a b w, S (G a b w) = G a b (S w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
          LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p) = trOn (hwOf G (wtR ν)) S * weylChar ν z :=
    fun ν hν => GlobalTheory.T.highest_weight_integral_of_unitary H ρ G ν hg hh hd hν
  choose! p hpG hpid hpkill hptr using hp
  obtain ⟨Fs, hFs⟩ : ∃ Fs : Set (Fin n → ℤ), ∀ ν, ν ∈ Fs ↔ Antitone ν ∧ hwOf G (wtR ν) ≠ ⊥ :=
    ⟨{ν | Antitone ν ∧ hwOf G (wtR ν) ≠ ⊥}, fun ν => Iff.rfl⟩
  have hfin : Fs.Finite := by
    have hv : ∀ ν ∈ Fs, ∃ v ∈ hwOf G (wtR ν), v ≠ 0 := fun ν hν =>
      Submodule.exists_mem_ne_zero_of_ne_bot ((hFs ν).1 hν).2
    choose! v hvmem hvne using hv
    have hli : LinearIndependent ℂ (fun ν : Fs => v ν) := by
      rw [linearIndependent_iff']
      intro s g hs i hi
      have hia : Antitone (i : Fin n → ℤ) := ((hFs i).1 i.2).1
      have h1 := congrArg (p i) hs
      rw [map_sum, map_zero, Finset.sum_eq_single i] at h1
      · rw [map_smul, hpid i hia (v i) (hvmem i i.2)] at h1
        exact (smul_eq_zero.mp h1).resolve_right (hvne i i.2)
      · intro j _ hji
        rw [map_smul, hpkill i hia (wtR j) (v j) (fun heq => hji (Subtype.ext (wtR_injective heq)))
          (hvmem j j.2), smul_zero]
      · intro hi'
        exact absurd hi hi'
    exact Set.finite_coe_iff.mp hli.finite
  have hF : ∀ ν, ν ∈ hfin.toFinset ↔ Antitone ν ∧ hwOf G (wtR ν) ≠ ⊥ := fun ν => by
    rw [Set.Finite.mem_toFinset, hFs]
  have hcomm : ∀ a b w, (LinearMap.id - ∑ ν ∈ hfin.toFinset, p ν : H →ₗ[ℂ] H) (G a b w) =
      G a b ((LinearMap.id - ∑ ν ∈ hfin.toFinset, p ν : H →ₗ[ℂ] H) w) := by
    intro a b w
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply, map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun ν hν => hpG ν ((hF ν).1 hν).1 a b w
  have hhigh : ∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v →
      (LinearMap.id - ∑ ν ∈ hfin.toFinset, p ν : H →ₗ[ℂ] H) v = 0 := by
    intro μ v hK
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    obtain ⟨ν₀, rfl⟩ := GlobalTheory.T.highest_weight_of_unitary_derivative H ρ G hd μ v hv0 hK.1
    have hanti : Antitone ν₀ := by
      have h := GlobalTheory.T.highest_weight_antitone_alt H G ⊤ (wtR ν₀) v hg inferInstance (fun _ _ _ _ => Submodule.mem_top)
        Submodule.mem_top hv0 hK
      intro i j hij
      have := h hij
      simp only [wtR] at this
      exact_mod_cast this
    have hmem : v ∈ hwOf G (wtR ν₀) := hK
    have hin : ν₀ ∈ hfin.toFinset := (hF ν₀).2 ⟨hanti, fun hbot => hv0 (by
      rw [hbot] at hmem
      exact (Submodule.mem_bot ℂ).1 hmem)⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply]
    rw [Finset.sum_eq_single ν₀, hpid ν₀ hanti v hmem, sub_self]
    · intro ν hν hne
      exact hpkill ν ((hF ν).1 hν).1 (wtR ν₀) v (fun heq => hne (wtR_injective heq).symm) hK
    · intro h
      exact absurd hin h
  have hsum : ∑ ν ∈ hfin.toFinset, p ν = LinearMap.id :=
    (sub_eq_zero.mp (GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest H H G G hg hh _ hcomm hhigh)).symm
  refine ⟨hfin.toFinset, fun ν hν => ((hF ν).1 hν).1, fun ν hν hνF => ?_, ?_⟩
  · by_contra hne
    exact hνF ((hF ν).2 ⟨hν, hne⟩)
  · intro S hS k z hk hz
    calc LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S)
        = LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ ∑ ν ∈ hfin.toFinset, p ν) := by
          rw [hsum, LinearMap.comp_id]
      _ = ∑ ν ∈ hfin.toFinset, LinearMap.trace ℂ H ((ρ k : H →ₗ[ℂ] H) ∘ₗ S ∘ₗ p ν) := by
          rw [← map_sum]
          congr 1
          ext w
          simp [LinearMap.sum_apply, map_sum]
      _ = _ := Finset.sum_congr rfl fun ν hν => hptr ν ((hF ν).1 hν).1 S hS k z hk hz

theorem sum_single' {M : Type*} [AddCommGroup M] [Module ℂ M] (x : Fin n → Fin n → M) (a b : Fin n) (c : ℂ) :
    ∑ i, ∑ j, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) i j • x i j = c • x a b := by
  classical
  rw [Finset.sum_eq_single a (fun i _ hi => Finset.sum_eq_zero fun j _ => by
        simp [Matrix.single_apply, Ne.symm hi]) (by simp),
      Finset.sum_eq_single b (fun j _ hj => by simp [Matrix.single_apply, Ne.symm hj]) (by simp)]
  simp [Matrix.single_apply]

theorem eq_zero_of_skew {M : Type*} [AddCommGroup M] [Module ℂ M] (x : Fin n → Fin n → M)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ i, ∑ j, X i j • x i j = 0) (a b : Fin n) : x a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    rw [Matrix.conjTranspose_sub, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT,
      star_one, neg_sub])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    rw [Matrix.conjTranspose_add, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT, GlobalTheory.CompanionTheory.RealCount.InjHw.single_conjT,
      Complex.star_def, Complex.conj_I, GlobalTheory.CompanionTheory.RealCount.InjHw.single_negI, GlobalTheory.CompanionTheory.RealCount.InjHw.single_negI,
      neg_add, add_comm])
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single', one_smul] at h1 h2
  rw [sub_eq_zero] at h1
  rw [← h1, ← two_smul ℂ, smul_smul] at h2
  exact (smul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)

theorem trOn_transport {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (e : M ≃ₗ[ℂ] N)
    (D : Submodule ℂ M) (D' : Submodule ℂ N) (hD : ∀ x, x ∈ D ↔ e x ∈ D') (f : M →ₗ[ℂ] M) (g : N →ₗ[ℂ] N)
    (hfg : ∀ x, e (f x) = g (e x)) (hf : ∀ x ∈ D, f x ∈ D) : trOn D f = trOn D' g := by
  have hg : ∀ y ∈ D', g y ∈ D' := by
    intro y hy
    have hx : e.symm y ∈ D := (hD _).2 (by simpa using hy)
    have := (hD _).1 (hf _ hx)
    rwa [hfg, LinearEquiv.apply_symm_apply] at this
  have hmap : D.map (e : M →ₗ[ℂ] N) = D' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hD x).1 hx
    · intro hy
      exact ⟨e.symm y, (hD _).2 (by simpa using hy), by simp⟩
  unfold trOn
  rw [dif_pos hf, dif_pos hg, ← LinearMap.trace_conj' (f.restrict hf) (e.ofSubmodules D D' hmap)]
  congr 1
  ext y
  simp [LinearEquiv.conj_apply, hfg]

theorem main : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) →
    ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G →
    ∃ F : Finset (Fin n → ℤ), (∀ ν ∈ F, Antitone ν) ∧ (∀ ν : Fin n → ℤ, Antitone ν → ν ∉ F → hwOf G (wtR ν) = ⊥) ∧
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z →
        LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
          ∑ ν ∈ F, trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) * weylChar ν z := by
  intro n E T hT G hG
  obtain ⟨e, ρ', hρc, hρn, he⟩ := GlobalTheory.T.unitary_euclidean_model E
  obtain ⟨G', hg', hh', hd'⟩ :=
    GlobalTheory.T.exists_compact_lie_action (EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V))) ρ' hρc hρn
  haveI : FiniteDimensional ℂ (E.V →L[ℂ] ℂ) := LinearEquiv.finiteDimensional e.symm
  have hint : ∀ a b ξ, e (G a b ξ) = G' a b (e ξ) := by
    intro a b ξ
    have hx : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X →
        ∑ i, ∑ j, X i j • (e (G i j ξ) - G' i j (e ξ)) = 0 := by
      intro X hX
      obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ,
          ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X) :=
        ⟨GlobalTheory.CompanionTheory.RealCount.InjHw.expU X hX, fun t => rfl⟩
      have h1 := hG.2 X γ hX hγ ξ
      have h2 := hd' X γ hX hγ (e ξ)
      have h3 : HasDerivAt (fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹)) (e (∑ a, ∑ b, X a b • G a b ξ)) 0 := by
        have := (e.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
          (0 : ℝ) h1
        simpa [Function.comp_def] using this
      have h4 : (fun t : ℝ => e (ξ ∘L E.ρ (γ t)⁻¹)) = fun t => ρ' (γ t) (e ξ) := funext fun t => he (γ t) ξ
      rw [h4] at h3
      have h5 := h3.unique h2
      simp only [map_sum, map_smul] at h5
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [h5, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_skew (fun i j => e (G i j ξ) - G' i j (e ξ)) hx a b)
  have hint2 : ∀ a b w, e.symm (G' a b w) = G a b (e.symm w) := fun a b w =>
    e.injective (by rw [hint, e.apply_symm_apply, e.apply_symm_apply])
  have hcommT : ∀ a b ξ, dualT E T (G a b ξ) = G a b (dualT E T ξ) := GlobalTheory.T.dual_operator_commutes_lie E T hT G hG
  obtain ⟨S', hS'⟩ : ∃ S' : EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)), ∀ w, S' w = e (dualT E T (e.symm w)) :=
    ⟨e.conj (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)), fun w => by simp [LinearEquiv.conj_apply]⟩
  have hS'comm : ∀ a b w, S' (G' a b w) = G' a b (S' w) := by
    intro a b w
    rw [hS', hS', hint2, hcommT, hint]
  have hmem : ∀ (μ : Fin n → ℝ) (v : E.V →L[ℂ] ℂ), v ∈ hwOf G μ ↔ e v ∈ hwOf G' μ := by
    intro μ v
    change Formalism.REAL.KHighest (fun _ => true) G μ v ↔ Formalism.REAL.KHighest (fun _ => true) G' μ (e v)
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun a => by rw [← hint, h1 a, map_smul], fun a b hab hε => by rw [← hint, h2 a b hab hε, map_zero]⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun a => e.injective ?_, fun a b hab hε => e.injective ?_⟩
      · rw [hint, h1 a, map_smul]
      · rw [hint, h2 a b hab hε, map_zero]
  have hpres : ∀ μ : Fin n → ℝ, ∀ x ∈ hwOf G μ, dualT E T x ∈ hwOf G μ := by
    intro μ x hx
    change Formalism.REAL.KHighest (fun _ => true) G μ x at hx
    change Formalism.REAL.KHighest (fun _ => true) G μ (dualT E T x)
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight at hx ⊢
    exact ⟨fun a => by rw [← hcommT, hx.1 a, map_smul],
      fun a b hab hε => by rw [← hcommT, hx.2 a b hab hε, map_zero]⟩
  have hfg : ∀ x, e ((dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) x) = S' (e x) := fun x => by
    simp [hS']
  obtain ⟨F, hFa, hFbot, htr⟩ := core _ ρ' G' hg' hh' hd'
  refine ⟨F, hFa, fun ν hν hνF => ?_, ?_⟩
  · rw [eq_bot_iff]
    intro v hv
    have h' : e v ∈ hwOf G' (wtR ν) := (hmem _ v).1 hv
    rw [hFbot ν hν hνF, Submodule.mem_bot] at h'
    exact (Submodule.mem_bot ℂ).2 (e.map_eq_zero_iff.mp h')
  · intro k z hk hz
    have hconj : e.conj (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) =
        (ρ' k : _ →ₗ[ℂ] _) ∘ₗ S' := by
      apply LinearMap.ext
      intro w
      rw [LinearMap.comp_apply, hS', ContinuousLinearMap.coe_coe, ← he]
      show e (dualT E (E.ρ k⁻¹ * T) (e.symm w)) = _
      congr 1
      simp only [dualT, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
      rw [← hT k⁻¹, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    rw [← LinearMap.trace_conj' (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) e, hconj,
      htr S' hS'comm k z hk hz]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [trOn_transport e (hwOf G (wtR ν)) (hwOf G' (wtR ν)) (hmem _) _ S' hfg (hpres _)]

end GlobalTheory.CompanionTheory.RealCountG.CharDec
