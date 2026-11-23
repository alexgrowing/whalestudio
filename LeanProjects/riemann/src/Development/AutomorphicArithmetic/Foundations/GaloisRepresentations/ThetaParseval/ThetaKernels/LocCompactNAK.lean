import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LocCompactNA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousCjK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentFirstMatrix

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isClosed_nA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsClosed (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have e : (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) =
      {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))} := Set.ext fun β => kunf.mem_nA_iff hε β
  rw [e]
  exact isClosed_eq continuous_id.matrix_transpose (((continuous_id.matrix_map hc).const_smul (((ε : ℤ) : AE F E))).neg)
instance locCompact_nA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : LocallyCompactSpace (nA σ d.Y d.b) :=
  haveI : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AE F E))
  (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.isClosed_nA_k d).isClosedEmbedding_subtypeVal.locallyCompactSpace
theorem coef_periodic_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb) (φ : d.G → ℂ)
    (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) (β₀ : nF σ d.Y d.b)
    (β : nA σ d.Y d.b) :
    φ (nb (β₀ +ᵥ β) * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β₀ +ᵥ β).1)))) =
      φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add hN, mul_assoc, hφ _ (kunf.nb_rat hN β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add, neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d}
theorem cj_mp_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    MeasurePreserving (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 v) lam lam := by
  have := h.2.1
  refine ⟨(_root_.PositivityTheory.SiegelWeilFormula.Act.C1.continuous_cj_k hU h.1 v).measurable, ?_⟩
  have hl := latHaar (nA σ d.Y d.b) lam (nF σ d.Y d.b) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 v) (fun x => ⟨fun hx => ?_, fun hx => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 hv hx⟩)
    𝓖 h.2.2.1 (by rw [h.2.2.2]; exact one_ne_zero) (by rw [h.2.2.2]; exact ENNReal.one_ne_top)
  · exact hl
  · have := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 (neg_mem hv) hx
    rwa [show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-v) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 v x) = x from _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 v x] at this
theorem fc_conj_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * g) = fc d.B.ψ d.b nb lam 𝓖 φ T g := by
  have := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  let H : nA σ d.Y d.b → ℂ := fun β =>
    φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have e1 : ∀ β, φ (nb β * (uM u * g)) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      H (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u β) := by
    intro β
    have e : nb β * (uM u * g) = uM u * (nb (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u β) * g) := by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.nb_cj_k hU h.1 u β]; group
    simp only [H]
    rw [e, hφ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.uM_rat_k hU hu), _root_.PositivityTheory.SiegelWeilFormula.Act.C1.trace_cj_k hU h.1 hT]
  have hme : MeasurableEmbedding (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u) := (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cjE_k hU h.1 u).toHomeomorph.measurableEmbedding
  have himg : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u) '' 𝓖 = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u)) ⁻¹' 𝓖 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u x) ∈ 𝓖
      rwa [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k]
    · intro hy
      refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) y, hy, ?_⟩
      simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 (-u) y
  have hfd : IsAddFundamentalDomain (nF σ d.Y d.b) ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u)) ⁻¹' 𝓖) lam := by
    refine h.2.2.1.preimage_of_equiv (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mp_k h hU (neg_mem hu)).quasiMeasurePreserving
      (e := fun γ => ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u γ.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 hu γ.2⟩) ⟨fun γ γ' hγ => ?_, fun γ => ?_⟩ fun γ x => ?_
    · have := congrArg (fun y : nF σ d.Y d.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) y.1) hγ
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k] at this
      exact Subtype.ext this
    · refine ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) γ.1, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_rat_k hU h.1 (neg_mem hu) γ.2⟩, Subtype.ext ?_⟩
      simpa using _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k hU h.1 (-u) γ.1
    · show _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 u γ.1) + x) = γ.1 + _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU h.1 (-u) x
      rw [map_add, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_inv_k]
  unfold fc
  simp_rw [e1]
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_mp_k h hU hu).setIntegral_image_emb hme H 𝓖, himg,
    hfd.setIntegral_eq h.2.2.1 (fun β₀ β => _root_.PositivityTheory.SiegelWeilFormula.Act.C1.coef_periodic_k d h.1 φ hφ T g β₀ β)]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
