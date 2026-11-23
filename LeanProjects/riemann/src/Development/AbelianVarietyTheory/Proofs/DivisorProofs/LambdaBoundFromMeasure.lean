import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeMaxSquaredBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqFieldExtensionLeComparableNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearEmbSupLatticeOntoRealisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.EqZeroOfPnorm

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.LamAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem totallyComplex_core : IsTotallyComplex p.T.Q.c.F :=
  ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => CompHt.conj_comp_ne (c := p.T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩

theorem goodOf_conj' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}
    (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c ((starRingEnd ℂ).comp σ) = goodOf c σ := by
  have e : (starRingEnd ℂ).comp σ = ComplexEmbedding.conjugate σ := by
    ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [e]; exact goodOf_conj (c := c) σ

theorem nrmK_conj (σ : p.T.Q.c.F →+* ℂ) (x : VK p.fw i) :
    nrmK p.fw i ((starRingEnd ℂ).comp σ) x = nrmK p.fw i σ x := by
  simp only [nrmK, normW, petW]
  rw [goodOf_conj']

theorem slopeMax_all_le (Cm : ℝ) (hG : GramAt p i) (hM : MeasAt p i Cm) :
    slopeMax_sq (nrmR p.R.toRealDat i) (latAll p.R.toRealDat i) ≤
      slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) + 2 * (Cm * unitE p) := by
  haveI := totallyComplex_core p
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation D _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  choose c hc0 hcB hcE using hM
  have hAll : latAll p.R.toRealDat i =
      Submodule.span (𝓞 D.what₂.LL) (ι '' (latW (p.T.U ((i : ℕ) + 1)) (Gk p i) : Set (VK p.fw i))) := by
    unfold latAll; rw [h3]
  have hne : latW (p.T.U ((i : ℕ) + 1)) (Gk p i) ≠ ⊥ := by
    intro h0
    apply hG.2.2.1
    refine le_bot_iff.1 ((latGood_le _ _ _).trans ((inf_le_left : latType p.R.toRealDat p.F.lv2 i ≤ latAll p.R.toRealDat i).trans ?_))
    change latAll p.R.toRealDat i ≤ ⊥
    rw [hAll, h0]
    simp
  have key := GlobalTheory.T.maxSlope_sq_fieldExtension_le_comparable_norms p.T.Q.c.F D.what₂.LL (VK p.fw i) (Fin (p.R.toRealDat.nW i) → D.what₂.LL) (nrmK p.fw i)
    (nrmR p.R.toRealDat i) ι (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) c (Cm * unitE p) hG.2.2.2.1 hG.1 (nrmK_conj p i) h2
    hG.2.2.2.2.1 hne (fun σ => ⟨hc0 σ, hcB σ⟩) (fun σ x => by
      obtain ⟨h, e⟩ := h1 x
      rw [e]
      exact hcE σ ⟨x, h⟩)
  rw [hAll]
  exact key

theorem unitE_le {PP A M : ℝ} (hH : HostNum D L PP A M) (hW : WtNum p i PP) :
    unitE p ≤ L.sc.x ^ (A + 1) * L.sc.b := by
  rw [hW.unit]
  have hX : 10 ≤ L.sc.x := hH.big.2.1.trans hH.big.2.2.1
  have hX0 : 0 < L.sc.x := by linarith
  have hL0 : 0 ≤ L.sc.L := by linarith [hH.big.2.1]
  have hb : 0 ≤ L.sc.b := le_trans (by positivity) hH.room
  have hlog : Real.log L.sc.x ≤ L.sc.x - 1 := Real.log_le_sub_one_of_pos hX0
  have hlogpos : 0 < Real.log L.sc.x := Real.log_pos (by linarith)
  have hll : Real.log (Real.log L.sc.x) ≤ L.sc.x := by
    have := Real.log_le_sub_one_of_pos hlogpos
    linarith
  have hll0 : 0 ≤ Real.log (Real.log L.sc.x) := by linarith [hH.big.2.2.2]
  have hmr : D.R.m ≤ D.R.r * D.R.nV := by
    have h1 : D.R.m ≤ D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
    have h2 : 1 ≤ D.R.nV := by have := D.R.two_le_m; unfold Ranks.nV; omega
    exact h1.trans (Nat.le_mul_of_pos_right _ h2)
  have hmr' : (D.R.m : ℝ) ≤ (D.R.r : ℝ) * D.R.nV := by exact_mod_cast hmr
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hfm : (D.R.f : ℝ) * D.R.m * L.sc.L ≤ (D.R.f : ℝ) * D.R.r * D.R.nV * L.sc.L := by
    have := mul_le_mul_of_nonneg_left hmr' hf
    have := mul_le_mul_of_nonneg_right this hL0
    linarith
  have hpoly := hH.poly.2.2
  have hfm0 : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.L := by positivity
  calc (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x)
        = ((D.R.f : ℝ) * D.R.m * L.sc.L) * (L.sc.b * Real.log (Real.log L.sc.x)) := by ring
    _ ≤ L.sc.x ^ A * (L.sc.b * L.sc.x) :=
        mul_le_mul (hfm.trans hpoly) (mul_le_mul_of_nonneg_left hll hb) (by positivity) (by positivity)
    _ = L.sc.x ^ (A + 1) * L.sc.b := by rw [Real.rpow_add_one hX0.ne']; ring

theorem le_rpow_of_add {X b A1 A Cm u s : ℝ} (hX : 10 ≤ X) (hb : 0 ≤ b) (hA1 : 0 ≤ A1) (hA : 0 ≤ A) (hCm : 0 ≤ Cm)
    (hu : u ≤ X ^ (A + 1) * b) (hs : s ≤ X ^ A1 * b + 2 * (Cm * u)) :
    s ≤ X ^ (A1 + (A + 1) + (⌈2 * Cm⌉₊ : ℝ)) * b := by
  have hX0 : 0 < X := by linarith
  have hP : 1 ≤ X ^ A1 := Real.one_le_rpow (by linarith) hA1
  have hQ : 1 ≤ X ^ (A + 1) := Real.one_le_rpow (by linarith) (by linarith)
  have hK : 1 + 2 * Cm ≤ X ^ (⌈2 * Cm⌉₊ : ℝ) := by
    rw [Real.rpow_natCast]
    have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ X - 1 by linarith) ⌈2 * Cm⌉₊
    have h2 : 2 * Cm ≤ (⌈2 * Cm⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈2 * Cm⌉₊ : ℝ) ≤ (⌈2 * Cm⌉₊ : ℝ) * (X - 1) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
    have h4 : (1 : ℝ) + (X - 1) = X := by ring
    rw [h4] at h1
    linarith
  rw [Real.rpow_add hX0, Real.rpow_add hX0]
  set P := X ^ A1
  set Q := X ^ (A + 1)
  set K := X ^ (⌈2 * Cm⌉₊ : ℝ)
  have e1 : P * b ≤ P * Q * b := by
    have : P ≤ P * Q := le_mul_of_one_le_right (by linarith) hQ
    exact mul_le_mul_of_nonneg_right this hb
  have e2 : 2 * (Cm * u) ≤ 2 * Cm * (P * Q * b) := by
    have : u ≤ P * Q * b := hu.trans (by
      have : Q ≤ P * Q := le_mul_of_one_le_left (by linarith) hP
      exact mul_le_mul_of_nonneg_right this hb)
    nlinarith
  have e3 : P * Q * b * (1 + 2 * Cm) ≤ P * Q * b * K :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  nlinarith

theorem lam : Hypotheses2 → Gram → Meas → abelian₂ := by
  intro hP hG hM
  have hc := GlobalTheory.T.slope_max_squared_bound hP hG
  have hH : HostN 1 := GlobalTheory.CovTop.Sizes.hostN 1
  have hW : WtN := GlobalTheory.T.weight_bound_holds
  refine Closed.imp ((((hc.and hM).and hH).and hG).and hW) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨⟨⟨⟨A1, hA1, hc⟩, ⟨Cm, hCm, hm⟩⟩, ⟨Ah, hAh, hh⟩⟩, ⟨Cg, -, hg⟩⟩, ⟨Cw, -, hw⟩⟩ := h
  refine ⟨A1 + (Ah + 1) + (⌈2 * Cm⌉₊ : ℝ), by have := Nat.cast_nonneg (α := ℝ) ⌈2 * Cm⌉₊; linarith, ?_⟩
  obtain ⟨x0, H⟩ := (((hc.and hm).and hh).and hg).and hw
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := H x hx hle ι p hp
  have hH1 := c i
  have hX : 10 ≤ (Fm.L x ι).sc.x := hH1.big.2.1.trans hH1.big.2.2.1
  have hb : 0 ≤ (Fm.L x ι).sc.b := le_trans (by positivity) hH1.room
  exact le_rpow_of_add hX hb hA1 (by linarith [hH1.poly.1]) hCm (unitE_le p i hH1 (e i))
    ((slopeMax_all_le p i Cm (d i) (b i)).trans (by linarith [a i]))

end GlobalTheory.CovTop.LamAll
