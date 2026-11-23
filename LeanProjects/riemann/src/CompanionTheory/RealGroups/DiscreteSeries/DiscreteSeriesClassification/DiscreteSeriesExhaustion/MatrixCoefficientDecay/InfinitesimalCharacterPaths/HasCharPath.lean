import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp

noncomputable section

namespace CompanionTheory.RgExh.Dec.J

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem nset_congr (ε : Fin n → Bool) {V : Type} [AddCommGroup V] [Module ℂ V] {ι κ : Type}
    (c : ι → V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (d : κ → V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))
    (h1 : ∀ i, ∃ k, c i = d k) (h2 : ∀ k, ∃ i, d k = c i) (A : Matrix (Fin n) (Fin n) ℂ)
    (μ : MeasureTheory.Measure (ReciprocityTheory.ChartRestriction.DS.S7.UJ ε)) (s : ℝ) : NSet ε c A μ s = NSet ε d A μ s := by
  ext u
  constructor
  · intro hu k
    obtain ⟨i, hi⟩ := h2 k
    rw [hi]; exact hu i
  · intro hu i
    obtain ⟨k, hk⟩ := h1 i
    rw [hk]; exact hu k

set_option maxHeartbeats 1000000 in

theorem along (hT : Transport) (hSC : StepChar) (hTD : TensDecomp) (hFF : FamFilt) (hSF : StepFam)
    (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (μ : MeasureTheory.Measure (ReciprocityTheory.ChartRestriction.DS.S7.UJ ε))
    (hA : IsGrad ε A) (hμ : IsParHaar ε A μ) (B : GradBasis A) :
    ∀ (ss : List (Fin n)) (X : GMod n) (ι : Type) (c : ι → X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))
      (χ : Fin n → ℂ) (Λ : Set (Fin n → Fin 3)) (F : Filt X A),
      IsCoefFam ε X c → (∀ s u, u ∈ F.N s ↔ u ∈ NSet ε c A μ s) → HasChar X χ → GoodPath χ ss → PP F B χ Λ →
      ∃ F' : Filt (path X χ ss) A,
        (∀ s u, u ∈ F'.N s ↔ u ∈ NSet ε (fun p : ι × List (Fin n) => pathCoef X (c p.1) χ ss p.2) A μ s) ∧
        PP F' B (pathEnd χ ss) (moveIter χ Λ ss) := by
  intro ss
  induction ss with
  | nil =>
    intro X ι c χ Λ F _ hF _ _ hP
    refine ⟨F, fun s u => (hF s u).trans ?_, hP⟩
    exact Set.ext_iff.1 (nset_congr ε c (fun p : ι × List (Fin n) => pathCoef X (c p.1) χ [] p.2)
      (fun i => ⟨(i, []), rfl⟩) (fun k => ⟨k.1, rfl⟩) A μ s) u
  | cons s ss ih =>
    intro X ι c χ Λ F hc hF hX hG hP
    obtain ⟨hc', hsand⟩ := hSF n ε X ι c (χ s) A μ hc hA
    obtain ⟨s0, hs0⟩ := F.top
    have htop : ∃ t, ∀ u, u ∈ NSet ε (fun p : ι × Fin n => stepCoef X (χ s) (c p.1) p.2) A μ t :=
      ⟨s0 + 1, fun u => (hsand (s0 + 1) u).1 fun i => by
        rw [← hF]; simp [add_sub_cancel_right, hs0]⟩
    obtain ⟨F1, hF1⟩ := hFF n ε (step X (χ s)) (ι × Fin n) _ A μ hc' hA hμ htop
    have hSS : SandStep F (χ s) F1 := fun t u =>
      ⟨fun h => (hF1 t u).2 ((hsand t u).1 fun i => (hF (t - 1) _).1 (h i)),
        fun h i => (hF (t + 1) _).2 ((hsand t u).2 ((hF1 t u).1 h) i)⟩
    have hP1 := hT hSC hTD n X A F B χ s F1 Λ hX hG.1 hSS hP
    obtain ⟨F', hF', hP'⟩ := ih (step X (χ s)) (ι × Fin n) _ (χ + Pi.single s 1) (move χ Λ s) F1 hc' hF1
      (hSC n X χ s hX) hG.2 hP1
    refine ⟨F', fun t u => ?_, hP'⟩
    have e := Set.ext_iff.1 (nset_congr (V := (path X χ (s :: ss)).V) ε
      (fun p : (ι × Fin n) × List (Fin n) =>
        pathCoef (step X (χ s)) (stepCoef X (χ s) (c p.1.1) p.1.2) (χ + Pi.single s 1) ss p.2)
      (fun p : ι × List (Fin n) => pathCoef X (c p.1) χ (s :: ss) p.2)
      (fun k => ⟨(k.1.1, k.1.2 :: k.2), rfl⟩) (fun k => ⟨((k.1, k.2.headD s), k.2.tail), rfl⟩) A μ t) u
    exact (hF' t u).trans e

theorem hasChar_path (hSC : StepChar) : ∀ (ss : List (Fin n)) (X : GMod n) (χ : Fin n → ℂ), HasChar X χ →
    HasChar (path X χ ss) (pathEnd χ ss) := by
  intro ss
  induction ss with
  | nil => intro X χ h; exact h
  | cons s ss ih => intro X χ h; exact ih _ _ (hSC n X χ s h)

theorem labels_of (hLF : LocFin) (hTD : TensDecomp) (hT : Transport) (hFF : FamFilt) (hSF : StepFam) (hBF : BaseFam)
    (hS1 : Start1) (hD : Degree) (hB : Basis) (hLT : LabelTrack) : Labels := by
  intro hSC n
  refine ⟨1, fun ε H _ _ _ σ D E hK χ ss hU hC hG hFL A μ hA hμ h0 => ?_⟩
  obtain ⟨B⟩ := hB n ε A hA
  have hc := hBF n ε H σ D E hK hU
  obtain ⟨F0, hF0⟩ := hFF n ε ⟨D, E, hK.gl⟩ D (fun ξ : D => baseCoef σ D (ξ : H)) A μ hc hA hμ ⟨-rhoA A, h0⟩
  have htop : F0.N (-rhoA A) = ⊤ := by
    ext u; simp only [Submodule.mem_top, iff_true]; exact (hF0 _ u).2 (h0 u)
  have hP0 := hS1 n ⟨D, E, hK.gl⟩ A F0 B χ (hLF n ε _ A F0 χ hA hC) hC htop
  obtain ⟨F', hF', hP'⟩ := along hT hSC hTD hFF hSF ε A μ hA hμ B ss ⟨D, E, hK.gl⟩ D
    (fun ξ : D => baseCoef σ D (ξ : H)) χ _ F0 hc hF0 hC hG hP0
  have hlab : ∀ L ∈ moveIter χ {L | IsLabel B.j L ∧ (deg χ L).re < 0} ss,
      (deg (pathEnd χ ss) L).re < (-rhoA A - 1) + rhoA A := by
    intro L hL
    have := hLT n χ ss 1 B.j hG hFL L hL
    linarith
  have hN := hD n _ A F' B (pathEnd χ ss) _ (-rhoA A - 1) (hLF n ε _ A F' _ hA (hasChar_path hSC ss _ χ hC)) (hasChar_path hSC ss _ χ hC) hP' hlab
  intro u
  have hu : u ∈ F'.N (-rhoA A - 1) := by rw [hN]; exact Submodule.mem_top
  exact (hF' _ u).1 hu

end CompanionTheory.RgExh.Dec.J
