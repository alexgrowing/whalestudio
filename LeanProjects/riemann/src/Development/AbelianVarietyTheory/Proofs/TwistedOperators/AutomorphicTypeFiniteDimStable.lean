import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.FiniteGKSum

open GlobalTheory.SeriesToClosure Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open Matrix Filter
open scoped InnerProductSpace Topology

section Sums

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)

def gkSums : Submodule ℂ (GA D V → ℂ) where
  carrier := {ψ | ∃ (m : ℕ) (T : Fin m → (kFin ε σ →ₗ[ℂ] (GA D V → ℂ))) (p : Fin m → kFin ε σ),
    (∀ j, IsGKMap θ V τ ε σ P (T j)) ∧ ψ = ∑ j, T j (p j)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, T, p, hT, rfl⟩ ⟨m', T', p', hT', rfl⟩
    refine ⟨m + m', Fin.append T T', Fin.append p p', fun j => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa using hT j
      · simpa using hT' j
    · simp [Fin.sum_univ_add]
  smul_mem' := by
    rintro c _ ⟨m, T, p, hT, rfl⟩
    exact ⟨m, T, fun j => c • p j, hT, by simp [Finset.smul_sum]⟩

end Sums

section Closure

variable {D : D7} {V : HSp D}

theorem mem_of_approx {E : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ E] {φ : GA D V → ℂ}
    (h : ∀ C : Set (GA D V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ ψ ∈ E, ∀ x ∈ C, ‖φ x - ψ x‖ < δ) : φ ∈ E := by
  have hE : IsClosed (E : Set (GA D V → ℂ)) := Submodule.closed_of_finiteDimensional E
  have key : ∀ p : Finset (GA D V) × ℕ, ∃ ψ ∈ E, ∀ x ∈ p.1, ‖φ x - ψ x‖ < 1 / ((p.2 : ℝ) + 1) :=
    fun p => h _ p.1.finite_toSet.isCompact _ (by positivity)
  choose u hu hu' using key
  refine hE.mem_of_tendsto (f := u) (b := (atTop : Filter (Finset (GA D V) × ℕ))) ?_
    (Filter.Eventually.of_forall hu)
  refine tendsto_pi_nhds.2 fun x => Metric.tendsto_atTop.2 fun δ hδ => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨({x}, N), fun p hp => ?_⟩
  have h1 : x ∈ p.1 := hp.1 (Finset.mem_singleton_self x)
  have h2 : (N : ℝ) ≤ p.2 := by exact_mod_cast hp.2
  rw [dist_comm, dist_eq_norm]
  calc ‖φ x - u p x‖ < 1 / ((p.2 : ℝ) + 1) := hu' p x h1
    _ ≤ 1 / ((N : ℝ) + 1) := by gcongr
    _ < δ := hN

end Closure

section Avg

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {ε : Fin V.rank → Bool} {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem avg_mem (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {W : Submodule ℂ (GA D V → ℂ)} [FiniteDimensional ℂ W]
    (hW : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), P * g * P⁻¹ ∈ Formalism.REAL.Kset ε →
      ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W)
    {φ : GA D V → ℂ} (hφc : Continuous φ) (hφ : φ ∈ W) {e : KG ε → ℂ} (he : KFinFun ε e) :
    avg θ V τ ε P e φ ∈ W := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hk : Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have cc : ∀ g : Matrix (Fin V.rank) (Fin V.rank) ℂ, P * (P⁻¹ * g * P) * P⁻¹ = g := fun g => by
    calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  have hmem : ∀ k : KG ε, rTr V (atTau θ V τ (P⁻¹ * toMK k * P)) φ ∈ W := fun k =>
    hW _ (conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))) (by rw [cc]; exact toMK_mem_K k) φ hφ
  let f : KG ε → W := fun k => ⟨_, hmem k⟩
  have hf : Continuous f := (continuous_pi fun x => hφc.comp (continuous_const.mul hk)).subtype_mk _
  let b := Module.finBasis ℂ W
  have hc : ∀ i, Continuous fun k => b.coord i (f k) := fun i =>
    (LinearMap.continuous_of_finiteDimensional (b.coord i)).comp hf
  have he' : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hint : ∀ i, Integrable (fun k => e k * b.coord i (f k)) (muK ε) := fun i =>
    integrableOn_univ.mp ((he'.mul (hc i)).continuousOn.integrableOn_compact isCompact_univ)
  have hrep : ∀ k, (f k : GA D V → ℂ) = ∑ i, b.coord i (f k) • (b i : GA D V → ℂ) := fun k => by
    nth_rw 1 [← b.sum_repr (f k)]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  have key : avg θ V τ ε P e φ = ∑ i, (∫ k, e k * b.coord i (f k) ∂(muK ε)) • (b i : GA D V → ℂ) := by
    funext x
    have hx : ∀ k, φ (x * atTau θ V τ (P⁻¹ * toMK k * P)) = ∑ i, b.coord i (f k) * (b i : GA D V → ℂ) x :=
      fun k => by
        have := congrFun (hrep k) x
        simpa [f, rTr, Finset.sum_apply] using this
    simp only [avg, hx, Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finset_sum _ fun i _ => ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_mul_const]
      congr 1
      funext k
      ring
    · simpa [mul_assoc] using (hint i).mul_const ((b i : GA D V → ℂ) x)
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

end Avg

end GlobalTheory.FiniteGKSum

namespace GlobalTheory.FiniteGKSum
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.SeriesToClosure
  GlobalTheory.FiniteGKSum in

theorem finite_sum_of_gkMaps : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (m : ℕ) (T : Fin m → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T j)) ∧ φ = ∑ j, T j (p j) := by
  intro hPr D θ V S M hθ τ φ hφ hT ⟨W, hWf, hφW, hWK⟩
  haveI := hWf
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨H', i1, i2, σ', lam', ε', P', hE', hD', hP', hJ', hx⟩ := hT
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) hE'
  obtain ⟨U, hU⟩ := hPr.discreteSeriesHermitianUnique _ (M.ε τ) (M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) P' (M.fr_unit τ) hP'
    (M.fr_gram τ) hJ' _ _ (M.σ τ) σ' (M.ds τ) hD'
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hPr.harishChandraModules (M.ds τ)
  have hP := M.fr_unit τ
  have hJ := M.fr_gram τ
  have hx' : ∀ x, HasTypeAll (lieSet (M.ε τ)) (UJset (M.ε τ)) (M.σ τ) (res θ V τ (M.fr τ) φ x) := fun x =>
    hasTypeAll_transport _ H' (M.H τ) _ (M.σ τ) (gramAt D V τ) (Jm (M.ε τ)) (M.fr τ) (isUnit_gram hP' hJ') hP hJ U
      hU (fun g => φ (x * atTau θ V τ g)) (hasTypeAll_iff.2 (hx x))
  choose Sx hS hc v ℓ C h using hx'
  have hZ : ∀ e, KFinFun (M.ε τ) e →
      avg θ V τ (M.ε τ) (M.fr τ) e φ ∈ gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) := by
    intro e he
    obtain ⟨m, a, c, ha, hQ, hA⟩ := exists_rank_one hθ hP hJ hσ he
    choose T hT hTv using fun j => exists_gkMap hθ hP hJ hσ hφ hS hc h (hA j)
    refine ⟨m, T, fun j => ⟨a j, mem_kFin_iff.2 (ha j)⟩, hT, funext fun x => ?_⟩
    have h1 := (moves_avg hθ hP hJ hσ he φ x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 1 (one_mem_UJ _)
    simp only [res_one hθ hP, sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
    have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (ha j))).hasSum)
    simp only [Finset.sum_apply, hTv]
    exact h2
  have hk : Continuous fun k : KG (M.ε τ) => atTau θ V τ ((M.fr τ)⁻¹ * toMK k * M.fr τ) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hmem : φ ∈ gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) ⊓ W := by
    haveI : FiniteDimensional ℂ (gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) ⊓ W : Submodule ℂ _) :=
      Submodule.finiteDimensional_of_le inf_le_right
    refine mem_of_approx fun K hK δ hδ => ?_
    obtain ⟨e, he, hap⟩ := GlobalTheory.T.exists_compactFinite_approxIdentity _ (M.ε τ) (GA D V)
      (fun x k => φ (x * atTau θ V τ ((M.fr τ)⁻¹ * toMK k * M.fr τ)))
      (hφ.cont.comp (continuous_fst.mul (hk.comp continuous_snd))) K hK δ hδ
    refine ⟨avg θ V τ (M.ε τ) (M.fr τ) e φ, ⟨hZ e he, avg_mem hθ hP hJ hWK hφ.cont hφW he⟩, fun x hxK => ?_⟩
    have h4 : φ (x * atTau θ V τ ((M.fr τ)⁻¹ * toMK (1 : KG (M.ε τ)) * M.fr τ)) = φ x := res_one hθ hP φ x
    have h3 := hap x hxK
    rw [h4] at h3
    exact h3
  obtain ⟨m, T, p, hT, hsum⟩ := hmem.1
  exact ⟨m, T, p, hT, hsum⟩

end GlobalTheory.FiniteGKSum
