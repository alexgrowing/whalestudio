import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

noncomputable section

namespace Formalism.L2.Pj

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct Pointwise

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem volPair_of_tie (hT : VolTieG D) (V : HSp D) (hs : V.SigOK) : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2 := by
  have h := hT V hs
  clear hT
  obtain ⟨⟨μ, hμ⟩, hb⟩ := h
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := hb μ hμ
  refine ⟨(μ, 𝓕), ?_⟩
  exact ⟨hμ, h𝓕⟩

theorem quotSupp_of (V : HSp D) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2) :
    QuotSupp V := by
  intro φ hφc hφinv hae g0
  by_contra hg0
  haveI : Countable (GQ V) := by
    unfold GQ
    exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have hvp : IsVolPair D V (volPair V).1 (volPair V).2 := by
    have e : volPair V = hP.choose := by
      unfold volPair
      rw [dif_pos hP]
    rw [e]
    exact hP.choose_spec
  haveI : (volPair V).1.IsHaarMeasure := hvp.1.1
  haveI : BorelSpace (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : MeasurableMul (GA D V) := by
    first
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA
    | exact Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA _ _
  haveI : MeasurableConstSMul (GQ V) (GA D V) := ⟨fun c => measurable_const_mul (c : GA D V)⟩
  haveI : SMulInvariantMeasure (GQ V) (GA D V) (volPair V).1 :=
    ⟨fun c s _ => measure_preimage_mul (volPair V).1 (c : GA D V) s⟩
  let O : Set (GA D V) := {g | φ g ≠ 0}
  have hO : IsOpen O := isOpen_ne_fun hφc continuous_const
  have hOinv : ∀ γ : GQ V, γ • O = O := by
    intro γ
    ext g
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show φ ((γ : GA D V) * x) ≠ 0
      rw [hφinv _ γ.2]
      exact hx
    · intro hg
      refine ⟨((γ⁻¹ : GQ V) : GA D V) * g, ?_, ?_⟩
      · show φ (((γ⁻¹ : GQ V) : GA D V) * g) ≠ 0
        rw [hφinv _ (γ⁻¹).2]
        exact hg
      · show (γ : GA D V) * (((γ⁻¹ : GQ V) : GA D V) * g) = g
        rw [← mul_assoc, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, one_mul]
  have hpos : 0 < (volPair V).1 O := hO.measure_pos _ ⟨g0, hg0⟩
  have hOF : (volPair V).1 (O ∩ (volPair V).2) ≠ 0 := fun h =>
    hpos.ne' (hvp.2.measure_zero_of_invariant O hOinv h)
  let S : Set (AutQ V) := {q | ¬ onQ V φ q = (0 : AutQ V → ℂ) q}
  have h0 : muQ1 V S = 0 := ae_iff.mp hae
  have hS : muQ V S = 0 := by
    unfold muQ1 at h0
    rw [if_pos (show muQ V Set.univ ≠ 0 ∧ muQ V Set.univ ≠ ⊤ from hV), Measure.smul_apply,
      smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (ENNReal.inv_eq_zero.mp h) hV.2
    · exact h
  have hmeas : AEMeasurable (autMk V) ((volPair V).1.restrict (volPair V).2) := by
    by_contra hnm
    apply hV.1
    unfold muQ
    simp [Measure.map_of_not_aemeasurable hnm]
  have hpre : autMk V ⁻¹' S = O := by
    ext g
    have hrel := Quotient.mk_out (s := QuotientGroup.rightRel (GQ V)) g
    rw [QuotientGroup.rightRel_apply] at hrel
    have hv : φ (autMk V g).out = φ g := by
      have e : g = (g * (autMk V g).out⁻¹) * (autMk V g).out := by group
      conv_rhs => rw [e]
      rw [hφinv _ hrel]
    show ¬ φ (autMk V g).out = 0 ↔ φ g ≠ 0
    rw [hv]
  have hle := Measure.le_map_apply hmeas S
  rw [hpre, Measure.restrict_apply hO.measurableSet] at hle
  have e2 : muQ V S = Measure.map (autMk V) ((volPair V).1.restrict (volPair V).2) S := rfl
  rw [← e2, hS] at hle
  exact hOF (le_antisymm hle (zero_le))

section Dom

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem aeDom_of {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {σ : c.F →+* ℂ} {V : HSp D}
    {dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r} {mu : GA D V → ℂ} {Kf : Subgroup (GA D V)}
    {th : ∀ k, ((U σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hA : AdelAut V dict mu) (hV : FinVol V) (hP : ∃ p : Measure (GA D V) × Set (GA D V), IsVolPair D V p.1 p.2)
    (hmu : MuUnit V dict mu) (hd : DictIsUnif V dict Kf th hr) : AeDom U σ V dict mu := by
  intro la P hPm hae k x hx
  have key : ∀ Q ∈ holSub (U σ).X la,
      ((∀ γ ∈ GQ V, ∀ g, adel V dict mu Q (γ * g) = adel V dict mu Q g) ∧
        Continuous (adel V dict mu Q)) ∧
      ∀ k, (∀ x ∈ ((U σ).X k).dom, ∀ b ∈ Bor ((U σ).X k).Ψ r, Q k (rmul x b) = bchar (la k) b * Q k x) ∧
        ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Q k (lact γ x) = ((U σ).X k).χ (la k) γ * Q k x := by
    intro Q hQ
    unfold holSub at hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      refine ⟨hA la Q hQ, fun k => ?_⟩
      have hs := (hQ k).1.1
      exact ⟨hs.2.1, hs.2.2⟩
    | zero =>
      refine ⟨⟨fun γ _ g => by simp, by rw [map_zero]; exact continuous_zero⟩,
        fun k => ⟨fun x _ b _ => by simp, fun γ _ x _ => by simp⟩⟩
    | add Q₁ Q₂ _ _ h1 h2 =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_add, Pi.add_apply, Pi.add_apply, h1.1.1 γ hγ g, h2.1.1 γ hγ g]
      · rw [map_add]
        exact h1.1.2.add h2.1.2
      · simp only [Pi.add_apply]
        rw [(h1.2 k).1 x hx b hb, (h2.2 k).1 x hx b hb, mul_add]
      · simp only [Pi.add_apply]
        rw [(h1.2 k).2 γ hγ x hx, (h2.2 k).2 γ hγ x hx, mul_add]
    | smul a Q _ h =>
      refine ⟨⟨fun γ hγ g => ?_, ?_⟩, fun k => ⟨fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩⟩
      · rw [map_smul, Pi.smul_apply, Pi.smul_apply, h.1.1 γ hγ g]
      · rw [map_smul]
        exact h.1.2.const_smul a
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).1 x hx b hb]
        ring
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [(h.2 k).2 γ hγ x hx]
        ring
  obtain ⟨⟨hinv, hcont⟩, hlaw⟩ := key P hPm
  have hz := quotSupp_of V hV hP (adel V dict mu P) hcont hinv hae
  obtain ⟨-, -, -, hd4, hd5, -⟩ := hd
  obtain ⟨g, γ, hγ, b, hb, hg⟩ := hd5 k x hx
  have h0 : P (dict g).1 (dict g).2 = 0 := by
    have e : mu g * P (dict g).1 (dict g).2 = 0 := hz g
    have hmu0 : mu g ≠ 0 := by
      intro h
      have h1 := hmu.2.1 g
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    exact (mul_eq_zero.mp e).resolve_left hmu0
  have hdom := hd4 g
  rw [hg] at h0 hdom
  exact eq_zero_of_orbit _ (la k) (P k) (hlaw k).1 (hlaw k).2 hx hγ hb hdom h0

end Dom

end Formalism.L2.Pj
