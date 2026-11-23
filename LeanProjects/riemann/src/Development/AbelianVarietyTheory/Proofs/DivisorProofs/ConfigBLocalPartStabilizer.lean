import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLocallyConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorIdeleConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelePowerIntegrableCompactStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.LemF

theorem coneFinInt_finSum : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ z : ℕ, 1 ≤ z → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      ∃ (N : ℕ) (f : Fin N → (Fin b × Fin (a + b) → Fv F v) → ℂ) (c : Fin N → KAt K (evFin F v) → idelesAt E (evFin F v) → ℂ),
        (∀ i, f i ∈ SB (Fin b × Fin (a + b) → Fv F v)) ∧ (∀ i k, Integrable (c i k) μ) ∧
        (∀ i, Integrable (fun k => ∫ l, c i k l ∂μ) μK) ∧
        ∀ k l y, coneFinInt B G.M' om' v (ev' v) (shiftB σ H H') X.ν z φ k.1 l.1 y = ∑ i, c i k l * f i y := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' hE ei' ev' hL K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ z hz φ hφ
  classical
  obtain ⟨hKc, hloc⟩ := GlobalTheory.T.local_stabilizer_locally_constant hP F E σ B a (b + 2) G X om om' hT K hK v
  have hψc : Continuous B.ψ := hT.base.std.1
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI := hKc
  haveI : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  let val : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) → (AE F E)ˣ → (Fin b × Fin (a + b) → Fv F v) → ℂ :=
    fun ψ l => ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) ψ)
  let w : (AE F E)ˣ → ℂ := fun l => (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z
  let ψk : KAt K (evFin F v) → (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ := fun k => locOp v (om' (k.1, 1)) φ
  have hψk : IsLocallyConstant ψk := hloc φ hφ
  have hψkSB : ∀ k, ψk k ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) := fun k => locOp_mem v _ φ
  have hevSB : ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ev' v ψ ∈ SB (Fin b × Fin (a + b) → Fv F v) :=
    fun ψ hψ => (hL.2.1 v).2 ▸ Submodule.mem_map_of_mem hψ
  have hvalSB : ∀ ψ l, val ψ l ∈ SB (Fin b × Fin (a + b) → Fv F v) := fun ψ l => hevSB _ (locOp_mem v _ ψ)
  have hwc : Continuous fun l : idelesAt E (evFin F v) => w l.1 := by
    have hα := hT.chars.heckeα.1
    have hβ := hT.chars.heckeβ.1
    have hν : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) :=
      continuous_subtype_val.comp (show Continuous fun l => X.α l / X.β l from hα.div' hβ)
    exact ((hν.comp continuous_subtype_val).mul
      ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
        (GlobalTheory.Doubling.continuous_absE.comp continuous_subtype_val))).pow z))
  have hwn : ∀ l : (AE F E)ˣ, ‖w l‖ = ((absE F E l : ℝ)) ^ z := fun l => by
    simp [w, Circle.norm_coe]
  have key : ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧
      (∀ l ∈ idelesAt E (evFin F v), val ψ l ≠ 0 →
        ((GlobalTheory.Doubling.unitFin F E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C) ∧
      IsLocallyConstant (fun l : idelesAt E (evFin F v) => val ψ l.1) ∧
      {f | ∃ l ∈ idelesAt E (evFin F v), val ψ l = f ∧ f ≠ 0}.Finite := by
    intro ψ hψ
    obtain ⟨g, hg, hgeq⟩ := GlobalTheory.T.local_operator_idele_locallyConstant F E σ B G.M' H H' hψc v ψ hψ
    obtain ⟨C, hCc, hCs⟩ := GlobalTheory.T.config_B_local_part_place hP F E σ B a b G G₁ H H' hC e' hE ei' ev' hL X om om' hT v ψ hψ
    have hCs' : ∀ l ∈ idelesAt E (evFin F v), val ψ l ≠ 0 →
        ((GlobalTheory.Doubling.unitFin F E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ C :=
      fun l hl h => by_contra fun hn => h (hCs l hl hn)
    have hveq : ∀ l ∈ idelesAt E (evFin F v),
        val ψ l = ev' v (g ((GlobalTheory.Doubling.unitFin F E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)) :=
      fun l hl => congrArg (ev' v) (hgeq l hl)
    refine ⟨C, hCc, hCs', ?_, ?_⟩
    · have hc : Continuous fun l : idelesAt E (evFin F v) =>
          ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) :=
        Units.continuous_val.comp ((GlobalTheory.Doubling.continuous_unitFin v).comp continuous_subtype_val)
      have e : (fun l : idelesAt E (evFin F v) => val ψ l.1) = (fun x => ev' v (g x)) ∘ fun l : idelesAt E (evFin F v) =>
          ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) :=
        funext fun l => hveq l.1 l.2
      rw [e]
      exact (hg.comp fun f => ev' v f).comp_continuous hc
    · haveI : CompactSpace C := isCompact_iff_compactSpace.1 hCc
      refine (((hg.comp fun f => ev' v f).comp_continuous continuous_subtype_val :
        IsLocallyConstant fun x : C => ev' v (g x.1)).range_finite).subset ?_
      rintro f ⟨l, hl, rfl, hf⟩
      exact ⟨⟨_, hCs' l hl hf⟩, (hveq l hl).symm⟩
  choose! Cf hCf hCsf hlcf hfinf using key
  let S : Set (((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) × ((Fin b × Fin (a + b) → Fv F v) → ℂ)) :=
    {p | p.1 ∈ Set.range ψk ∧ ∃ l ∈ idelesAt E (evFin F v), val p.1 l = p.2 ∧ p.2 ≠ 0}
  have hS : S.Finite := by
    refine (hψk.range_finite.biUnion fun ψ hψ => (hfinf ψ ?_).image fun f => (ψ, f)).subset ?_
    · obtain ⟨k, rfl⟩ := hψ
      exact hψkSB k
    · rintro ⟨ψ, f⟩ ⟨h1, h2⟩
      exact Set.mem_biUnion h1 ⟨f, h2, rfl⟩
  let T := hS.toFinset
  let eT := T.equivFin
  let P : Fin T.card → ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) × ((Fin b × Fin (a + b) → Fv F v) → ℂ) :=
    fun i => (eT.symm i).1
  have hP : ∀ i, P i ∈ S := fun i => hS.mem_toFinset.1 (eT.symm i).2
  have hPSB : ∀ i, (P i).1 ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) := fun i => by
    obtain ⟨⟨k₀, hk₀⟩, -⟩ := hP i
    exact hk₀ ▸ hψkSB k₀
  refine ⟨T.card, fun i => (P i).2,
    fun i k l => if ψk k = (P i).1 ∧ val (P i).1 l.1 = (P i).2 then w l.1 else 0, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨-, l, -, h, -⟩ := hP i
    show (P i).2 ∈ _
    rw [← h]
    exact hvalSB _ _
  · intro i k
    obtain ⟨-, -, -, -, hne⟩ := hP i
    by_cases hk : ψk k = (P i).1
    · let A : Set (idelesAt E (evFin F v)) := {l | val (P i).1 l.1 = (P i).2}
      have hA : MeasurableSet A := ((hlcf _ (hPSB i)).isOpen_fiber _).measurableSet
      have hAsub : A ⊆ {l | ((GlobalTheory.Doubling.unitFin F E v l.1 : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ Cf (P i).1} :=
        fun l hl => hCsf _ (hPSB i) l.1 l.2 (by rw [show val (P i).1 l.1 = (P i).2 from hl]; exact hne)
      have hw : IntegrableOn (fun l : idelesAt E (evFin F v) => w l.1) A μ :=
        ((GlobalTheory.T.idele_power_integrable_compact F E v μ hμ _ (hCf _ (hPSB i)) z hz).mono_set hAsub).mono' hwc.aestronglyMeasurable
          (ae_of_all _ fun l => (hwn l.1).le)
      have e : (fun l : idelesAt E (evFin F v) => if ψk k = (P i).1 ∧ val (P i).1 l.1 = (P i).2 then w l.1 else 0) =
          A.indicator fun l => w l.1 := by
        funext l
        simp only [Set.indicator, A, Set.mem_setOf_eq, hk, true_and]
      beta_reduce
      rw [e]
      exact (integrable_indicator_iff hA).2 hw
    · simp only [hk, false_and, if_false]
      exact integrable_zero _ _ _
  · intro i
    have e : (fun k : KAt K (evFin F v) => ∫ l, (if ψk k = (P i).1 ∧ val (P i).1 l.1 = (P i).2 then w l.1 else 0) ∂μ) =
        {k | ψk k = (P i).1}.indicator
          (fun _ => ∫ l, (if val (P i).1 l.1 = (P i).2 then w l.1 else 0) ∂μ) := by
      funext k
      by_cases hk : ψk k = (P i).1 <;> simp [Set.indicator, hk]
    beta_reduce
    rw [e]
    exact (integrable_indicator_iff ((hψk.isOpen_fiber _).measurableSet)).2 (integrable_const _).integrableOn
  · intro k l y
    let p0 := (ψk k, val (ψk k) l.1)
    have hterm : ∀ q : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) × ((Fin b × Fin (a + b) → Fv F v) → ℂ),
        (if ψk k = q.1 ∧ val q.1 l.1 = q.2 then w l.1 else 0) * q.2 y = if q = p0 then w l.1 * p0.2 y else 0 := by
      rintro ⟨ψ, f⟩
      by_cases h : ψk k = ψ ∧ val ψ l.1 = f
      · obtain ⟨rfl, rfl⟩ := h
        simp [p0]
      · rw [if_neg h, zero_mul, if_neg]
        intro hq
        exact h ⟨(Prod.mk.inj hq).1.symm, by rw [(Prod.mk.inj hq).1, (Prod.mk.inj hq).2]⟩
    have h1 : ∑ i, (if ψk k = (P i).1 ∧ val (P i).1 l.1 = (P i).2 then w l.1 else 0) * (P i).2 y =
        ∑ q ∈ T, (if ψk k = q.1 ∧ val q.1 l.1 = q.2 then w l.1 else 0) * q.2 y :=
      (Equiv.sum_comp eT.symm (fun j : T => (if ψk k = j.1.1 ∧ val j.1.1 l.1 = j.1.2 then w l.1 else 0) * j.1.2 y)).trans
        (Finset.sum_coe_sort T fun q => (if ψk k = q.1 ∧ val q.1 l.1 = q.2 then w l.1 else 0) * q.2 y)
    rw [h1, Finset.sum_congr rfl fun q _ => hterm q, Finset.sum_ite_eq' T p0 fun _ => w l.1 * p0.2 y]
    show val (ψk k) l.1 y * (X.ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z = _
    by_cases h0 : val (ψk k) l.1 = 0
    · have h0' : p0.2 = 0 := h0
      rw [h0, h0']
      simp
    · rw [if_pos (hS.mem_toFinset.2 ⟨⟨k, rfl⟩, l.1, l.2, rfl, h0⟩)]
      simp only [p0, w]
      ring

end GlobalTheory.ThK.LemF

end
