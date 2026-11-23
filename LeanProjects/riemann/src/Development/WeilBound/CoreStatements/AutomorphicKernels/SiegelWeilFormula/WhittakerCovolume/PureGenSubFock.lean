import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps
import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' f g := by funext x; simp only [schr, Pi.add_apply]; ring
  map_smul' c f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem T_eq_lin (d : SD σ) (Φ : d.Fn) (X : Mx F E d.m d.n) :
    d.T Φ X = (d.l ∘ₗ schrL d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ))) Φ := rfl

theorem T_sum (d : SD σ) {k : ℕ} (c : Fin k → ℂ) (Φs : Fin k → d.Fn) :
    d.T (∑ i, c i • Φs i) = ∑ i, c i • d.T (Φs i) := by
  funext X
  simp only [T_eq_lin, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]

theorem T_sub (d : SD σ) (Φ Ψ : d.Fn) : d.T (Φ - Ψ) = d.T Φ - d.T Ψ := by
  funext X
  simp only [T_eq_lin, map_sub, Pi.sub_apply]

def genF {d : SD σ} (R : RD d) (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
    (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2

def genL {d : SD σ} (R : RD d) (P : InfinitePlace F → PX d.m d.n) :
    ((Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := genF R P
  map_add' f g := by funext X; simp only [genF, Pi.add_apply]; ring
  map_smul' c f := by funext X; simp only [genF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def pureGen {d : SD σ} (R : RD d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ P φ, Dense.Good φ ∧ f = genF R P (Dense.pf φ)}

theorem pureGen_sub_fock {d : SD σ} (R : RD d) : pureGen R ⊆ R.fock := by
  rintro f ⟨P, φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨P, Dense.pf φ, Dense.pf_mem hφ, rfl⟩

theorem fock_le_span {d : SD σ} (R : RD d) : R.fock ≤ Submodule.span ℂ (pureGen R) := by
  show Submodule.span ℂ _ ≤ _
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hg, rfl⟩
  have hg' := Dense.mem_span_pf hg
  have hmap : genL R P g ∈ Submodule.span ℂ (genL R P '' {h | ∃ φ, Dense.Good φ ∧ h = Dense.pf φ}) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map_of_mem hg'
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨h, ⟨φ, hφ, rfl⟩, rfl⟩
  exact ⟨P, φ, hφ, rfl⟩

theorem isPureT_of {d : SD σ} (R : RD d) (P : InfinitePlace F → PX d.m d.n)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = genF R P (Dense.pf φ)) : IsPureT R Φ := by
  refine ⟨P, φ, fun v => hφ.1 v, ?_, ?_⟩
  · filter_upwards [hφ.2] with v hv
    rw [hv]
    rfl
  · rw [h]
    rfl

theorem pureSpan : PureSpan := by
  intro hT hF hP F E _ _ _ _ _ σ d R Φ hK hfock
  have hspan := fock_le_span R hfock
  obtain ⟨k, c, gs, hgs⟩ := Submodule.mem_span_set'.1 hspan
  have hmem : ∀ i, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) ∧ IsPureT R Ψ := by
    intro i
    obtain ⟨P, φ, hφ, hg⟩ := (gs i).2
    have hfk : (gs i : Mx F E d.m d.n → ℂ) ∈ R.fock := pureGen_sub_fock R (gs i).2
    obtain ⟨Ψ, hΨ, hTΨ⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 hfk)
    exact ⟨Ψ, hΨ, hTΨ, isPureT_of R P φ hφ Ψ (hTΨ.trans hg)⟩
  choose Ψ hΨ hTΨ hpure using hmem
  refine ⟨k, c, Ψ, fun i => ⟨hP F E σ d R (Ψ i) (hΨ i) (by rw [hTΨ i]; exact pureGen_sub_fock R (gs i).2), hpure i⟩, ?_⟩
  have hsum : ∑ i, c i • Ψ i ∈ d.sch := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΨ i)
  have hzero : d.T (Φ - ∑ i, c i • Ψ i) = 0 := by
    rw [T_sub, T_sum]
    simp only [hTΨ]
    rw [hgs, sub_self]
  exact sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (Submodule.sub_mem _ hK.1 hsum) hzero)

end PositivityTheory.SiegelWeilFormula.KWhit

end
