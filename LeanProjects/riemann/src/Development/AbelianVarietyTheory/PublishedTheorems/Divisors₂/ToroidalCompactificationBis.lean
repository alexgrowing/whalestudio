import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotHasChartOfOfMinEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsPolarizedModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.LogKS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

theorem smooth_gen_iff {d : ℕ} : SmoothOfRelativeDimension d (genStr Y) ↔ SmoothOfRelativeDimension d Y.s := by
  have := isIso_fst Y
  have h : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have e : genStr Y = genι Y ≫ Y.s :=
    ((Category.comp_id _).symm.trans (congrArg (genStr Y ≫ ·) h.symm)).trans pullback.condition.symm
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · have h' := smoothOfRelativeDimension_comp 0 d (inv (genι Y)) (genStr Y)
    rwa [Nat.zero_add, e, IsIso.inv_hom_id_assoc] at h'
  · have h' := smoothOfRelativeDimension_comp 0 d (genι Y) Y.s
    rwa [Nat.zero_add, ← e] at h'

theorem snc_gen_iff : FinalTheorems.Snc (genBdIdeal Y) ↔ FinalTheorems.Snc (boundary Y) := by
  refine ⟨fun h => ?_, GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary⟩
  have := isIso_fst Y
  refine GlobalTheory.SncIso.snc_vanishingIdeal_of_isIso (inv (genι Y)) (genBd Y) (interior Y).compl (fun a => ?_) h
  rw [mem_genBd_iff, ← coe_interior, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

end GlobalTheory.LogKS

namespace GlobalTheory.Published

open GlobalTheory.LogKS GlobalTheory.MumfordChart

def ToroidalForFanKS : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ →
      ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l),
        ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧
          SmoothOfRelativeDimension Dw.dim (genStr Y) ∧ FinalTheorems.Snc (genBdIdeal Y) ∧
          (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) ∧
          (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) ∧
          ((GlobalTheory.FlagMod.detOm Y).IsLB → GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf Y k BD)) ∧
          GlobalTheory.LogKS.HasLogKS Y.t Y.s (GlobalTheory.LogKS.interior Y)

theorem SiegelToroidalIntegral.exists_fan (h : SiegelToroidalIntegral) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (q : ℕ) :
    ∃ φ : InvFun (𝓞 E), IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ ∧ GlobalTheory.TorRef.IsPosFn H φ := by
  obtain ⟨φs, hs, -⟩ := h (max 1 (Module.finrank ℚ E * q)) (le_max_left _ _)
  obtain ⟨φ, h₁, h₂, -, h₃, -⟩ := exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)
  exact ⟨φ, h₁, h₂, h₃⟩

namespace ToroidalForFanKS

theorem toroidalChartsForFan (h : ToroidalForFanKS) : ToroidalChartsForFan := by
  intro E _ _ _ H Dw hr φ h₁ h₂ l Xo c
  obtain ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, -⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  exact ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem exists_model_of_fan (h : ToroidalForFanKS) (hr : 1 ≤ Dw.p + Dw.q) {φ : InvFun (𝓞 E)}
    (h₁ : IsPolFan H.bar (min Dw.p Dw.q) φ) (h₂ : NoSelfInt H.bar (min Dw.p Dw.q) φ) {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧
      SmoothOfRelativeDimension Dw.dim Y.s ∧ FinalTheorems.Snc (boundary Y) ∧ HasLogKS Y.t Y.s (interior Y) ∧
      (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) ∧ (∀ x ∈ genBd Y, genι Y x ∈ BD.idealSheaf.support) ∧
      (∀ x ∈ genBd Y, HasChartOf φ Y BD d x) ∧
      (GlobalTheory.FlagMod.detOm Y).IsLB ∧ GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf Y k BD) := by
  obtain ⟨Y, BD, d, k, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h E H Dw hr φ h₁ h₂ l Xo c
  have hL := GlobalTheory.FanTheta.isLB_detOm_of_smooth Y hr a₃
  exact ⟨Y, BD, d, k, a₁, a₂, smooth_gen_iff.1 a₃, snc_gen_iff.1 a₄, a₈, a₅,
    fun x hx => (mem_support_iff_stalkId _ _).2 (GlobalTheory.FanChartTest.idlAlong_ne_top h₁ a₁ hx (a₆ x hx)), a₆, hL, a₇ hL⟩

theorem exists_model (hS : SiegelToroidalIntegral) (h : ToroidalForFanKS) (hr : 1 ≤ Dw.p + Dw.q) {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d k : ℕ),
      IsPolFan H.bar (min Dw.p Dw.q) φ ∧ NoSelfInt H.bar (min Dw.p Dw.q) φ ∧ GlobalTheory.TorRef.IsPosFn H φ ∧ 1 ≤ d ∧ 1 ≤ k ∧
      SmoothOfRelativeDimension Dw.dim Y.s ∧ FinalTheorems.Snc (boundary Y) ∧ HasLogKS Y.t Y.s (interior Y) ∧
      (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) ∧ (∀ x ∈ genBd Y, genι Y x ∈ BD.idealSheaf.support) ∧
      (∀ x ∈ genBd Y, HasChartOf φ Y BD d x) ∧
      (GlobalTheory.FlagMod.detOm Y).IsLB ∧ GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf Y k BD) := by
  obtain ⟨φ, h₁, h₂, h₃⟩ := hS.exists_fan H (min Dw.p Dw.q)
  obtain ⟨Y, BD, d, k, a⟩ := h.exists_model_of_fan hr h₁ h₂ Xo c
  exact ⟨φ, Y, BD, d, k, h₁, h₂, h₃, a⟩

theorem exists_model_charts (hS : SiegelToroidalIntegral) (h : ToroidalForFanKS) (hr : 1 ≤ Dw.p + Dw.q)
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ Y : Model Xo c (RingHom.id c.F), SmoothOfRelativeDimension Dw.dim Y.s ∧ FinalTheorems.Snc (boundary Y) ∧
      HasLogKS Y.t Y.s (interior Y) ∧ ∀ x ∈ genBd Y, HasChart Y x := by
  obtain ⟨φ, Y, BD, d, k, -, -, -, -, -, a₁, a₂, a₃, -, -, a₄, -⟩ := h.exists_model hS hr Xo c
  exact ⟨Y, a₁, a₂, a₃, fun x hx => (a₄ x hx).hasChart⟩

theorem exists_torModel (hS : SiegelToroidalIntegral) (h : ToroidalForFanKS) (hr : 1 ≤ Dw.p + Dw.q)
    {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ (Y : Model Xo c (RingHom.id c.F)) (T : TorModel Y), T.Z = Y ∧
      SmoothOfRelativeDimension Dw.dim T.Z.s ∧ FinalTheorems.Snc (boundary T.Z) ∧ HasLogKS T.Z.t T.Z.s (interior T.Z) ∧
      (GlobalTheory.FlagMod.detOm T.Z).IsLB ∧ GlobalTheory.IsAmpleLB (GlobalTheory.TorRef.polOf T.Z T.m0 T.BD) := by
  obtain ⟨φ, Y, BD, d, k, -, -, -, -, hk, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := h.exists_model hS hr Xo c
  exact ⟨Y, GlobalTheory.TorRef.selfTor Y (smooth_gen_iff.2 a₁) (snc_gen_iff.2 a₂)
    (fun x hx => (hasChart_iff Y x).1 (a₆ x hx).hasChart) BD a₄ a₅ k hk, rfl, a₁, a₂, a₃, a₇, a₈⟩

theorem toroidalCompactification (hS : SiegelToroidalIntegral) (h : ToroidalForFanKS) : ToroidalCompactification :=
  fun _ _ _ _ _ _ hr _ Xo c => (h.exists_model_charts hS hr Xo c).imp fun _ a => ⟨a.1, a.2.1, a.2.2.1⟩

theorem toroidalCharts (hS : SiegelToroidalIntegral) (h : ToroidalForFanKS) : ToroidalCharts :=
  fun _ _ _ _ _ _ hr _ Xo c =>
    (h.exists_model_charts hS hr Xo c).imp fun _ a => ⟨smooth_gen_iff.2 a.1, snc_gen_iff.2 a.2.1, a.2.2.2⟩

end ToroidalForFanKS

end GlobalTheory.Published
