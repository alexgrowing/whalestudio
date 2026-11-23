import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.Bounds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PAscAll
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PChord
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ProjOf
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTens
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSlice
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopNeg
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag

noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def Gap {N : ℕ} (ε : ℝ) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))

variable (E) in

def RepAll : Prop :=
  ∀ (M : ℕ) [MeasurableSpace (GA E M)] [BorelSpace (GA E M)] (ν : Measure (GA E M)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin M) (Af E))) (W' : Submodule ℂ (Kinf E M → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin M) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R'

def Concl {N : ℕ} (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))))
    (V : ℕ → Submodule ℂ (Sm E N)) : Prop :=
  ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E N) (t₀ : Tr E N), StrictMono φ ∧ Tr.Pos t₀ ∧ (∀ z ∈ t₀.twists, z.re = 0) ∧
    (∀ k, Tr.Pos (t k)) ∧ (∀ k, (t k).strip = t₀.strip) ∧
    t₀.AllLeaves (fun M V => ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (t₀.twists.getD i 0))) ∧
    ∀ k, Emb (V (φ k)) (· ∈ (t k).space)

def Seq (N : ℕ) (W : Submodule ℂ (Kinf E N → ℂ)) (K : Subgroup (GL (Fin N) (Af E)))
    (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ R : ℝ, 0 < N → RepAll E → ∀ V : ℕ → Submodule ℂ (Sm E N), (∀ k, IsDiscrete (V k)) → (∀ k, HasType K W (V k)) →
    (∀ k, InfBdd R (V k)) → Concl Ω Θ V

theorem concl_subseq {N : ℕ} {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))}
    {Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))} {V : ℕ → Submodule ℂ (Sm E N)} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (h : Concl Ω Θ (V ∘ ψ)) : Concl Ω Θ V := by
  obtain ⟨φ, t, t₀, hφ, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨ψ ∘ φ, t, t₀, hψ.comp hφ, h1, h2, h3, h4, h5, h6, h7⟩

theorem seq_mono {N : ℕ} {W : Submodule ℂ (Kinf E N → ℂ)} {K : Subgroup (GL (Fin N) (Af E))}
    {Ω Ω' : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ Θ' : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (h : Seq N W K Ω Θ) (hΩ : ∀ M, Ω M ⊆ Ω' M) (hΘ : ∀ M, Θ M ⊆ Θ' M) : Seq N W K Ω' Θ' := by
  intro R hN hRep V hVd hVt hVb
  obtain ⟨φ, t, t₀, hφ, h1, h2, h3, h4, h5, h6, h7⟩ := h R hN hRep V hVd hVt hVb
  exact ⟨φ, t, t₀, hφ, h1, h2, h3, h4, allLeaves_mono (fun M U ⟨K', hK', W', hW', hT⟩ =>
    ⟨K', hΘ M hK', W', hΩ M hW', hT⟩) h5, h6, h7⟩

theorem caseA (hFD : FinDisc) {N : ℕ} (hN : 0 < N) {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (hW : FiniteDimensional ℂ W)
    {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hWΩ : W ∈ Ω N) (hKΘ : K ∈ Θ N) {R : ℝ} (hRep : RepAll E) {V : ℕ → Submodule ℂ (Sm E N)}
    (hVd : ∀ k, IsDiscrete (V k)) (hVt : ∀ k, HasType K W (V k)) (hVb : ∀ k, InfBdd R (V k)) {ε : ℝ} (hε : 0 < ε)
    (hfr : ∃ᶠ k in atTop, Gap ε (V k)) : Concl Ω Θ V := by
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨V₀, hV₀⟩ := hFD E N Measure.haar K W R ε hK hW hε (hRep N Measure.haar K W R hK hW)
  have hfr' : ∃ᶠ k in atTop, ∃ V' ∈ V₀, IsoV (V k) V' :=
    hfr.mono fun k hk => hV₀ (V k) (hVd k) (hVt k) (hVb k) hk
  have : ∃ V' ∈ V₀, ∃ᶠ k in atTop, IsoV (V k) V' := by
    by_contra hcon
    have hall : ∀ᶠ k in atTop, ∀ V' ∈ V₀, ¬ IsoV (V k) V' :=
      (Filter.eventually_all_finset V₀).2 fun V' hV' => Filter.not_frequently.1 fun h => hcon ⟨V', hV', h⟩
    obtain ⟨k, ⟨V', hV', hk⟩, hk'⟩ := (hfr'.and_eventually hall).exists
    exact hk' V' hV' hk
  obtain ⟨V', -, hfrV⟩ := this
  obtain ⟨ψ, hψ, hψV⟩ := Filter.extraction_of_frequently_atTop hfrV
  refine ⟨ψ, fun _ => .leaf (V (ψ 0)) 0, .leaf (V (ψ 0)) 0, hψ, ⟨hN, hVd _⟩, ?_, fun _ => ⟨hN, hVd _⟩,
    fun _ => rfl, ⟨K, hKΘ, W, hWΩ, hVt _⟩, fun i => tendsto_const_nhds, fun k => ?_⟩
  · intro z hz
    simp only [Tr.twists, List.mem_singleton] at hz
    simp [hz]
  · show Emb (V (ψ k)) (· ∈ tw (V (ψ 0)) 0)
    rw [tw_zero]
    exact emb_of_isoV (hVd _).stable (isoV_of_common (hVd _).stable (hψV k) (hψV 0))

theorem gap_of_le {N : ℕ} {V : Submodule ℂ (Sm E N)} {lam ε : ℝ} (h : Gap lam V) (hle : ε ≤ lam) : Gap ε V := by
  intro r hr hrN c hc
  have hpos : (0 : ℝ) < r * ((N : ℝ) - r) :=
    mul_pos (by exact_mod_cast hr) (sub_pos.2 (by exact_mod_cast hrN))
  have := h r hr hrN c hc
  nlinarith

theorem re_twists {r s : ℕ} (hr : 0 < r) (hs : 0 < s) {c : ℂ} {lam : ℝ}
    (h : pE E (r + s) r c = -lam * (r * s)) :
    (c / (r * (Module.finrank ℚ E : ℂ)) - (s : ℂ) / 2).re = -(s * lam) ∧
      (-c / (s * (Module.finrank ℚ E : ℂ)) + (r : ℂ) / 2).re = r * lam := by
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold pE at h
  push_cast at h
  have hc : c.re = (Module.finrank ℚ E : ℝ) * ((r : ℝ) * s / 2 - lam * (r * s)) := by
    field_simp at h ⊢; linarith
  have e1 : (r : ℂ) * (Module.finrank ℚ E : ℂ) = (((r : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have e2 : (s : ℂ) * (Module.finrank ℚ E : ℂ) = (((s : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((s : ℂ) / 2).re = (s : ℝ) / 2 := by simp
  have h3 : ((r : ℂ) / 2).re = (r : ℝ) / 2 := by simp
  constructor
  · rw [Complex.sub_re, e1, Complex.div_ofReal_re, h2, hc]
    field_simp; ring
  · rw [Complex.add_re, e2, Complex.div_ofReal_re, h3, Complex.neg_re, hc]
    field_simp; ring

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
