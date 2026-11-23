import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SettingNormaliser
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LevNorm

open Formalism.BasicNotions.TH

theorem embA_injective {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) :
    Function.Injective (embA d o) := fun _ _ h =>
  congrArg Prod.fst (o.emb_injective (d.wittDecomp_anisotropicEmbedding_injective h))

theorem finf_sand {D : D7} {k n : ℕ} (p : Mx D k n) (m : Mx D n n) (j : Mx D n k) (hm : m.map (CenAct.finf D) = 1)
    (h : p ⬝ j = 1) : (p ⬝ (m ⬝ j)).map (CenAct.finf D) = 1 := by
  rw [← Matrix.mul_assoc, CenAct.map_sand p m j hm, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_GfC_of_embA {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {a : GA D A}
    (h : embA d o a ∈ GfC S) : a ∈ GfC A := by
  rw [embA_apply, CenAct.mem_GfC_iff] at h
  have h1 := finf_sand d.p0 _ d.j0 h d.p0_j0
  rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul] at h1
  have h2 := finf_sand o.pA _ o.jA h1 o.pA_jA
  rw [o.emb_jA, cancel₂ o.pA_jA, Matrix.one_mul] at h2
  exact (CenAct.mem_GfC_iff _ _).2 h2

theorem matches_differ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hρ : 1 ≤ D.R.rS)
    (u : D.what₂.Word) {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)
    {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {t t' : GA D (D.sp.Y 0)} (ht : Matches X h J χ t) (ht' : Matches X h J χ t') :
    ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ k ∈ J,
      t = ((iotaX X h).symm (1, X.xu u))⁻¹ * embA B.d B.o a * (iotaX X h).symm (1, X.xu u) * z * t' * k := by
  let j : X.B.I.Gf →* GA D (D.sp.Y 0) := ((iotaX X h).symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : ∀ x, iotaX X h (j x) = (1, x) := fun x => (iotaX X h).apply_symm_apply _
  have hjG : ∀ x, j x ∈ GfC (D.sp.Y 0) := fun x => (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h _).1 (by rw [hj])
  have hjJ : ∀ x, j x ∈ rowJ X h ↔ x ∈ X.K2 := fun x => by
    show (iotaX X h (j x)).1 = 1 ∧ (iotaX X h (j x)).2 ∈ X.K2 ↔ _
    rw [hj]
    exact and_iff_right rfl
  have hjχ : ∀ x, rowChi X h (j x) = star (X.chi2 x) := fun x => by
    show star (X.chi2 (iotaX X h (j x)).2) = _
    rw [hj]
  obtain ⟨y, hy⟩ : ∃ y, j y = t * t'⁻¹ := ⟨_, GlobalTheory.SeeConjRead.eq_symm_one X h _
    ((GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h _).2 (mul_mem ht.1 (inv_mem ht'.1)))⟩
  have e1 : ∀ x, t'⁻¹⁻¹ * (t'⁻¹ * j x * t') * t'⁻¹ = j x := fun x => by group
  have e2 : ∀ x, t⁻¹⁻¹ * (t'⁻¹ * j x * t') * t⁻¹ = j (y * x * y⁻¹) := fun x => by
    rw [map_mul, map_mul, map_inv, hy]; group
  have hJ : ∀ x, t'⁻¹ * j x * t' ∈ J ↔ x ∈ X.K2 := fun x => by rw [(ht'.2 _).1, e1, hjJ]
  obtain ⟨z, hz, w, hw, hw', k, hk, e⟩ := setting_normaliser X h hρ u y fun x =>
    ⟨by rw [← hJ, (ht.2 _).1, e2, hjJ], fun hx => by
      rw [← hjχ, ← hjχ, ← e2, (ht.2 _).2 ((hJ x).2 hx), ← (ht'.2 _).2 ((hJ x).2 hx), e1]⟩
  obtain ⟨a, ha⟩ := (B.tieH (j w)).2 (by rw [hj]; exact ⟨one_mem _, hw⟩)
  refine ⟨j z, hjG z, Subgroup.mem_center_iff.2 fun g => (iotaX X h).injective ?_, a,
    mem_GfC_of_embA B.d B.o (ha ▸ hjG w), Subgroup.mem_center_iff.2 fun b => embA_injective B.d B.o ((iotaX X h).injective ?_),
    t'⁻¹ * j k * t', (hJ k).2 hk, ?_⟩
  · rw [map_mul, map_mul, hj]
    exact Prod.ext (by simp) (Subgroup.mem_center_iff.1 hz _)
  · rw [map_mul, map_mul, map_mul, map_mul, ha, hj]
    exact Prod.ext (by simp) (hw' _ ((B.tieH _).1 ⟨b, rfl⟩).2).symm
  · show t = (j (X.xu u))⁻¹ * embA B.d B.o a * j (X.xu u) * j z * t' * (t'⁻¹ * j k * t')
    rw [ha]
    have e3 := congrArg j e
    rw [hy, map_mul, map_mul, map_mul, map_mul, map_inv] at e3
    calc t = t * t'⁻¹ * t' := by group
      _ = _ := by rw [e3]; group

end GlobalTheory.LevNorm

theorem GlobalTheory.MiTop.matches_differ_central : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → 1 ≤ D.R.rS → ∀ (u : D.what₂.Word) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ t ∈ GfC (D.sp.Y 0), ∀ t' ∈ GfC (D.sp.Y 0), Matches W.S.X W.Q.instEq (rJ W) (rChi W) t → Matches W.S.X W.Q.instEq (rJ W) (rChi W) t' → ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC (D.sp.X 0), a ∈ Subgroup.center (GA D (D.sp.X 0)) ∧ ∃ k ∈ rJ W, t = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o a * (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * z * t' * k := by
  intro D L hT Gi Gl Kc Yd cX ex W _ hρ u B t _ t' _ ht ht'
  exact GlobalTheory.LevNorm.matches_differ W.S.X W.Q.instEq hρ u B ht ht'

end
