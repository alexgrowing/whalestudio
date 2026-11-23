import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLw
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IntegrableOfIsAniso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero

noncomputable section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelFormula.Model

variable {D : D7}

theorem two_mul_finrank_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) (W : Submodule E B.V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0) : 2 * Module.finrank E W ≤ B.rank := by
  let b := Module.finBasis E W
  have hl : LinearIndependent E fun i => B.hT (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h1 : B.hT ((∑ i, star (c i) • b i : W) : B.V) = 0 := by
      rw [← hc]; simp [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply]
    have h2 : (∑ i, star (c i) • b i : W) = 0 := Subtype.ext (B.nondeg.1 _ fun y => by rw [h1]; rfl)
    simpa using Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 i
  have h3 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range fun i => B.hT (b i)))
  rw [finrank_span_eq_card hl, Fintype.card_fin, B.rank_eq] at h3
  have h4 : W ≤ (Submodule.span E (Set.range fun i => B.hT (b i))).dualCoannihilator := fun y hy => by
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; exact hW _ (b i).2 _ hy
    | zero => rfl
    | add _ _ _ _ h h' => rw [LinearMap.add_apply, h, h', add_zero]
    | smul _ _ _ h => rw [LinearMap.smul_apply, h, smul_zero]
  have := Submodule.finrank_mono h4
  omega

theorem bddAbove_witt {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    BddAbove {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0} :=
  ⟨B.rank, by rintro _ ⟨W, rfl, hW⟩; have := two_mul_finrank_le B W hW; omega⟩

theorem two_mul_wittIdx_le {E : Type} [Field E] [NumberField E] [StarRing E] (B : HSpace E) :
    2 * Formalism.MainNotions.SchurIrreducible.wittIdx B ≤ B.rank := by
  obtain ⟨W, h, hW⟩ := Nat.sSup_mem (s := {k | ∃ W : Submodule E B.V, Module.finrank E W = k ∧
    ∀ x ∈ W, ∀ y ∈ W, B.hT x y = 0}) ⟨_, ⊥, rfl, by simp⟩ (bddAbove_witt B)
  rw [Formalism.MainNotions.SchurIrreducible.wittIdx, ← h]
  exact two_mul_finrank_le B W hW

theorem range_of_two_mul_lt {A B : HSp D} (h : 2 * A.rank < B.rank) : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
  have := two_mul_wittIdx_le B
  omega

abbrev pos (D : D7) (n : ℕ) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n

theorem wittIdx_pos (n : ℕ) : Formalism.MainNotions.SchurIrreducible.wittIdx (pos D n) = 0 :=
  Formalism.MainNotions.J.wittIdx_zero _ (Formalism.MainNotions.J.aniso_of_definite _ D.host.φ₀ (D.sp.cm.cmUnram.2.1 D.host.φ₀)
    (Examples₂.posSpace_sigOK _ _) fun _ => .inl rfl)

theorem wittIdx_dblSp (V : HSp D) : Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) = V.rank := by
  have h1 : 2 * Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) ≤ V.rank + V.rank := two_mul_wittIdx_le (dblSp V)
  let f : V.V →ₗ[D.host.E] (dblSp V).V := LinearMap.prod LinearMap.id LinearMap.id
  have hf : Function.Injective f := fun x y h => congrArg Prod.fst h
  have h2 : V.rank ≤ Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) := le_csSup (bddAbove_witt _)
    ⟨LinearMap.range f, (LinearMap.finrank_range_of_inj hf).trans V.rank_eq, by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      change V.hT x y + -V.hT x y = 0
      exact add_neg_cancel _⟩
  omega

theorem data_exist (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (A B : HSp D) :
    ∃ (m : Measure (GA D B)) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (f : WO (dblSp A) B → ℂ)
      (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)),
      m.IsHaarMeasure ∧ IsWeilDatumO ψ (dblSp A) B 1 χ ω ∧ IsThetaFunO ψ (dblSp A) B f ∧ f ≠ 0 ∧
        IsCovolOne (ratL B A) ν 𝓖 := by
  obtain ⟨ψ, A', B', χ, ω', -, -, -, -, hA, hB, -, h', -⟩ := GlobalTheory.ThetaMean.Model.hypotheses_inhabited H D A.rank B.rank
  obtain ⟨ω, hω⟩ := H D ψ (dblSp A) B 1 χ h'.std h'.hecS h'.hecT
    (by have := h'.resS; change ResEta D 1 (A'.rank + A'.rank) at this; rwa [hA] at this) (hB ▸ h'.resT)
  obtain ⟨f, hf, h0⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hω.std (dblSp A) B
  obtain ⟨ν, 𝓖, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D B.rank A.rank
  exact ⟨Measure.haar, ψ, χ, ω, f, ν, 𝓖, inferInstance, hω, hf, h0, hν⟩

theorem ranges_inhabited (D : D7) :
    (∃ A B : HSp D, 1 ≤ A.rank ∧ Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∧ 2 * A.rank < B.rank) ∧
    (∃ A B : HSp D, 1 ≤ A.rank ∧ Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∧ 1 ≤ B.rank ∧ B.rank ≤ A.rank) ∧
    (∃ A B : HSp D, 1 ≤ A.rank ∧ 0 < Formalism.MainNotions.SchurIrreducible.wittIdx B ∧ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank ∧
      2 * A.rank < B.rank) :=
  ⟨⟨pos D 1, pos D 3, le_rfl, wittIdx_pos 3, show 2 * 1 < 3 by decide⟩, ⟨pos D 1, pos D 1, le_rfl, wittIdx_pos 1, le_rfl, le_rfl⟩,
    ⟨pos D 1, dblSp (pos D 2), le_rfl, by rw [wittIdx_dblSp]; exact show 0 < 2 by decide,
      by rw [wittIdx_dblSp]; exact show 1 + 2 < 2 + 2 by decide, show 2 * 1 < 2 + 2 by decide⟩⟩

theorem plane_excluded (D : D7) : ¬ (Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp (pos D 1)) = 0 ∨
    (pos D 1).rank + Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp (pos D 1)) < (dblSp (pos D 1)).rank) := by
  rw [wittIdx_dblSp]; exact show ¬ (1 = 0 ∨ 1 + 1 < 1 + 1) by decide

theorem swSection_eq (A B : HSp D) (ν 𝓖 ω f) : swSection A B ν 𝓖 ω f = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec A B ω ν 𝓖 f := rfl

theorem integrableOn_valZero {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f : WO (dblSp A) B → ℂ} {ν 𝓖}
    (hν : IsCovolOne (ratL B A) ν 𝓖) (hf : IsThetaFunO ψ (dblSp A) B f) : IntegrableOn (fun y => f (lagr A B y)) 𝓖 ν :=
  GlobalTheory.ThetaMean.integrableOn_lagr hν hf

theorem exists_evalSeminorm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AdeleRing (𝓞 F) F)
    (c : NNReal) : ∃ ν : Seminorm ℂ (WeilM.schA F κ), IsContSeminorm ν ∧ ∀ φ, ν φ = c * ‖φ.1 x‖ := by
  refine ⟨c • (normSeminorm ℂ ℂ).comp ((LinearMap.proj x).comp (WeilM.schA F κ).subtype), fun g => ?_, fun φ => rfl⟩
  have h := (continuous_eval_const (F := BoundedContinuousFunction (κ → mixedEmbedding.mixedSpace F) ℂ)
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ).continuous
  exact continuous_const.mul (h.mul continuous_const).norm

theorem first_clause_rank_zero (A B : HSp D) (hB : B.rank = 0) (m : Measure (GA D B)) [m.IsHaarMeasure] (d : ℕ)
    (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧
      ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d),
        absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) := by
  have : IsEmpty (Fin B.rank) := by rw [hB]; infer_instance
  obtain ⟨ν, h1, h2⟩ := exists_evalSeminorm (F := D.host.F) (κ := Fin B.rank × Fin A.rank × Fin d) 0
    (autMeasure B m Set.univ).toNNReal
  refine ⟨ν, h1, fun φ => le_of_eq ?_⟩
  have h3 : descend (GQ B) (absTheta B (φ.1 ∘ coord ε)) = fun _ => ‖φ.1 0‖ₑ := funext fun q => by
    have hs : Subsingleton (Matrix (Fin B.rank) (Fin A.rank) D.host.E) := ⟨fun x y => Matrix.ext fun i => isEmptyElim i⟩
    rw [AutomorphicL2Unitary.descend, absTheta, tsum_eq_single 0 fun b hb => (hb (Subsingleton.elim _ _)).elim]
    exact congrArg (fun z => ‖φ.1 z‖ₑ) (funext fun p => isEmptyElim p.1)
  rw [absThetaInt, h3, lintegral_const, h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_toNNReal (measure_ne_top _ _), ofReal_norm, mul_comm]

theorem absThetaInt_lt_top (H : GlobalTheory.Published.WeilSiegelFormulaUnitary) (A B : HSp D) (m : Measure (GA D B)) [m.IsHaarMeasure]
    (hA : 1 ≤ A.rank) (h : 2 * A.rank < B.rank) {d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)) : absThetaInt B m (φ.1 ∘ coord ε) < ⊤ :=
  let ⟨_, _, e⟩ := (H D A B m inferInstance hA (.inr (range_of_two_mul_lt h))).1 d ε
  (e φ).trans_lt ENNReal.ofReal_lt_top

theorem formula (H : GlobalTheory.Published.WeilSiegelFormulaUnitary) {A B : HSp D} (m : Measure (GA D B)) [m.IsHaarMeasure]
    (hA : 1 ≤ A.rank) (h : 2 * A.rank < B.rank) {ψ χ ω f} (hω : IsWeilDatumO ψ (dblSp A) B 1 χ ω)
    (hf : IsThetaFunO ψ (dblSp A) B f) {ν 𝓖} (hν : IsCovolOne (ratL B A) ν 𝓖) (g : GA D (dblSp A)) :
    EisConv A (swSection A B ν 𝓖 ω f) g ∧ eis A (swSection A B ν 𝓖 ω f) g = GlobalTheory.ThetaMean.thetaMean ω m f g :=
  (((H D A B m inferInstance hA (.inr (range_of_two_mul_lt h))).2 ψ χ ω hω f hf).2 h ν 𝓖 hν).2 g

end GlobalTheory.SiegelFormula.Model

end
