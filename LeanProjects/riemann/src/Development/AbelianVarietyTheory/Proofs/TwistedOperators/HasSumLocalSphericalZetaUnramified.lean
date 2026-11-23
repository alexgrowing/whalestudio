import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosetsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumUnramifiedZetaSumUnitaryInertStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalZetaKernelGLRightInvariantIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedQuadraticCharSignSplitEqOneInertEqNegStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjLocalTwistedLFactorRatioSplitEqZetaSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjLocalTwistedLFactorRatioInertEqZetaSumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitarySatakeTransformStarParameterEqOfUnitarisaStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSatVecUOfDiag
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocZeta

theorem hasSum_quot_of_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) {K : Subgroup G} {K' : Subgroup H}
    (hK : ∀ g, g ∈ K ↔ e g ∈ K') {f : G → ℂ} (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) {s : ℂ}
    (h : HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s) : HasSum (fun a : G ⧸ K => f a.out) s :=
  GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient G H e K K' hK f hf s h

theorem kerGL_mul_right {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r N : ℕ} {z : ℂˣ}
    {φ : GL (Fin r) (w.adicCompletion E) → ℂ} (hφ : KerGL w N z φ) (g k : GL (Fin r) (w.adicCompletion E))
    (hk : k ∈ KGL w r) : φ (g * k) = φ g :=
  GlobalTheory.T.sphericalZetaKernelGL_right_invariant_integral E w r N z φ hφ g k hk

theorem kerU_mul_right {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    {σ : w.adicCompletion E →+* w.adicCompletion E} {ϖ : w.adicCompletion E} {q r N : ℕ} (hU : IsUnramInv ϖ σ q)
    {z : ℂˣ} {φ : GU σ r → ℂ} (hφ : KerU ϖ q N z φ) (g k : GU σ r) (hk : k ∈ KU σ r) : φ (g * k) = φ g := by
  obtain ⟨d, t, -, ht, k₁, h₁, k₂, h₂, rfl⟩ := cartanU hU g
  rw [mul_assoc (k₁ * t), hφ d t ht k₁ h₁ _ (mul_mem h₂ hk), hφ d t ht k₁ h₁ k₂ h₂]

theorem conj_qpow (q : ℕ) (x : ℝ) : starRingEnd ℂ ((q : ℂ) ^ (x : ℂ)) = (q : ℂ) ^ (x : ℂ) := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.conj_ofReal]

theorem kerGL_conj {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r N : ℕ} {z : ℂˣ}
    {φ : GL (Fin r) (w.adicCompletion E) → ℂ} (hφ : KerGL w N z φ) :
    KerGL w N (star z) (fun g => starRingEnd ℂ (φ g)) := by
  intro ϖ hϖ d t ht k₁ h₁ k₂ h₂
  show starRingEnd ℂ (φ (k₁ * t * k₂)) = _
  rw [hφ ϖ hϖ d t ht k₁ h₁ k₂ h₂, map_mul, map_zpow₀]
  have := conj_qpow (qV E w) (-((N : ℝ) / 2) * ((∑ i, |d i| : ℤ) : ℝ))
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_intCast, Complex.ofReal_ofNat] at this
  rw [this]
  rfl

theorem kerU_conj {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ} {ϖ : L}
    {q N : ℕ} {z : ℂˣ} {φ : GU σ r → ℂ} (hφ : KerU ϖ q N z φ) :
    KerU ϖ q N (star z) (fun g => starRingEnd ℂ (φ g)) := by
  intro d t ht k₁ h₁ k₂ h₂
  show starRingEnd ℂ (φ (k₁ * t * k₂)) = _
  rw [hφ d t ht k₁ h₁ k₂ h₂]
  simp [map_zpow₀]

theorem quadSign_eq (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w ≠ w' → (∀ u, u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') →
      quadSign D v = 1) ∧
    (∀ w : HeightOneSpectrum (𝓞 D.host.E), (∀ u, u.under (𝓞 D.host.F) = v ↔ u = w) → quadSign D v = -1) :=
  GlobalTheory.T.unramifiedQuadraticCharSign_split_eq_one_inert_eq_neg D v

theorem value_split (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hne : w ≠ w')
    (hall : ∀ u, u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') (hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal)
    (hN' : Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal) (hB' : B w' = (B w).map (·⁻¹))
    (hs : (B w).map star = (B w).map (·⁻¹)) (hm : m w * m w' = 1) (hm1 : ‖(m w : ℂ)‖ = 1) (hq : quadSign D v = 1) :
    starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) =
      eulerFac ((B w).map (star (m w) * ·)) (npow w (-((1 + (D.R.t : ℂ)) / 2))) *
        eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) (npow w (-((1 + (D.R.t : ℂ)) / 2))) *
        ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹) :=
  GlobalTheory.T.conj_localTwistedLFactor_ratio_split_eq_zetaSum D B m v w w' hne hall hN hN' hB' hs hm hm1 hq

theorem value_inert (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hall : ∀ u, u.under (𝓞 D.host.F) = v ↔ u = w) (hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2)
    (hs : (B w).map star = B w) (hm : (m w : ℂ) = (-1) ^ D.R.nV) (hq : quadSign D v = -1) :
    starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) =
      eulerFac (B w) (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.t + 1))⁻¹) *
        ∏ j ∈ Finset.range D.R.r,
          (1 - (-(qV D.host.F v : ℂ)) ^ j * (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.r + D.R.t))⁻¹)) :=
  GlobalTheory.T.conj_localTwistedLFactor_ratio_inert_eq_zetaSum D B m v w hall hN hs hm hq

set_option maxHeartbeats 1000000 in

theorem hasSum_localZeta : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (χ : (AE D)ˣ →* Circle), Formalism.L2.Theta.ResEta D χ D.R.nV → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ φ : Gv V v → ℂ, IsLocKer V D.R.nV (val χ) v φ → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gv V v) X), IsUnitarisable ρ → ∀ (x : X) (B : Fam D.host.E), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsParamVec D.sp.cm.sig V.gram (frameLat V) h ρ x (B w) ∧ ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) → ∀ ℓ : X →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : Gv V v ⧸ Kv V v => φ a.out * starRingEnd ℂ (ℓ (ρ a.out x))) (LvTw B (val χ) v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ) * starRingEnd ℂ (ℓ x)) := by
  intro hG D V hr χ hχ v hU φ hφ X _ _ ρ hρu x B hB ℓ hℓ
  classical
  have hc := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hc.2.2.1
  have hχ' := (resEta_iff χ _).1 hχ
  have hJ := GlobalTheory.Mem.VolExists.isHermND D.sp.cm V
  have hd := SelfDual.isSelfDualAt_frameLat D V v
  have hrt : V.rank ≤ D.R.t := by
    have := D.R.rank_add_five_le
    rw [hr]
    unfold Ranks.r
    omega
  have hnV : D.R.nV = V.rank + D.R.t := by rw [hr]; rfl
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  obtain ⟨C, hC⟩ := hℓ
  have hfix : ∀ k ∈ Kv V v, ρ k x = x := GlobalTheory.LGrp.mem_fixed.1 (hB w h).1.mem_fixed
  have hnz : ‖(((star (val χ w) : ℂˣ)) : ℂ)‖ = 1 := by
    rw [Units.coe_star]
    simpa using norm_val χ w
  suffices H : HasSum (fun a : Gv V v ⧸ Kv V v => starRingEnd ℂ (φ a.out) * ℓ (ρ a.out x))
      (starRingEnd ℂ (LvTw B (val χ) v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) * ℓ x) by
    have := H.map (starRingEnd ℂ) Complex.continuous_conj
    simpa [Function.comp_def] using this
  rcases (hB w h).1 with ⟨hv, e, he, hsat⟩ | ⟨hw, c, ϖ, e, α, hUI, he, hsat, hBw⟩
  · obtain ⟨w', hne, hall, hN, hN', -⟩ := SplitChart.exists_conj_place hc h hv
    have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
    have hB' : B w' = (B w).map (·⁻¹) :=
      ConjPlace.eq_map_inv_of_isParamVec hc hJ hd hne (hB w h).1 (hB w' h').1
    have hm : val χ w * val χ w' = 1 := ResEta.val_mul_val h2 hχ' hne h h' (hU w h) (hU w' h')
    have hs : (B w).map star = (B w).map (·⁻¹) :=
      GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable _ w _ _ _ x (B w) (hρu.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat
    have hk := kerGL_conj ((hφ w h).1 hv e he)
    rw [hnV] at hk
    have hbd : ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ (((V.rank : ℝ) - 1) / 2) ∧
        ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
      intro β hβ
      rw [hr]
      refine ⟨(hB w h).2 β hβ, ?_⟩
      have := (hB w' h').2 β⁻¹ (hB' ▸ Multiset.mem_map_of_mem _ hβ)
      have e2 : (qV D.host.E w : ℝ) = ((Ideal.absNorm w'.asIdeal : ℕ) : ℝ) := by
        rw [hN', ← hN]; rfl
      rw [e2]
      exact this
    have hsum := GlobalTheory.T.unramified_zeta_sum_GL_cosets hG D.host.E w V.rank D.R.t hrt (star (val χ w)) _ hnz hk X
      (ρ.comp e.symm.toMonoidHom) x (B w) hsat hbd ℓ ⟨C, fun g => hC _⟩
    rw [value_split D B (val χ) v w w' hne hall hN hN' hB' hs hm (norm_val χ w) ((quadSign_eq D v).1 w w' hne hall),
      ← hr]
    refine hasSum_quot_of_equiv e he.2 (f := fun g => starRingEnd ℂ (φ g) * ℓ (ρ g x)) ?_ hsum
    intro g k hk'
    have e1 : φ (g * k) = φ g := by
      have := kerGL_mul_right ((hφ w h).1 hv e he) (e g) (e k) ((he.2 k).1 hk')
      simpa using this
    show starRingEnd ℂ (φ (g * k)) * ℓ (ρ (g * k) x) = starRingEnd ℂ (φ g) * ℓ (ρ g x)
    rw [e1, map_mul, Module.End.mul_apply, hfix k hk']
  · have hall := InertChart.under_eq_iff hw
    have hNw := InertChart.absNorm_eq h2 hw
    have hval : val χ w = (-1) ^ D.R.nV := ResEta.val_of_isInertAt h2 hχ' hw (hU w h)
    have hk := kerU_conj ((hφ w h).2 hw c ϖ e hUI he)
    rw [hnV] at hk
    have hstarB : (B w).map star = B w := by
      rw [hBw]
      have := bcParam_eq_of_satU_eq (α := fun i => star (α i)) hUI
        (GlobalTheory.T.unitarySatakeTransform_star_parameter_eq_of_unitarisable _ ϖ c _ _ hUI _ _ x α (hρu.imp fun _ hb => ⟨hb.1, hb.2.1, fun g => hb.2.2 (e.symm g)⟩) hsat)
      conv_rhs => rw [← this]
      simp [bcParam, star_inv, Function.comp_def]
    have htb : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound (qV D.host.F v) V.rank α := by
      have hq : ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) = (qV D.host.F v : ℝ) ^ 2 := by
        rw [hNw]; push_cast; rfl
      have hQ : (0 : ℝ) < (qV D.host.F v : ℝ) ^ 2 := by
        have := one_lt_absNorm v
        have : (0 : ℝ) < (qV D.host.F v : ℝ) := by
          show (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)
          exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)
        positivity
      intro i
      have h1 := (hB w h).2 (α i) (by rw [hBw]; simp [bcParam])
      have h3 := (hB w h).2 (α i)⁻¹ (by rw [hBw]; simp [bcParam])
      rw [hq, ← hr] at h1 h3
      refine ⟨?_, h1⟩
      rw [Real.rpow_neg hQ.le]
      rw [Units.val_inv_eq_inv_val, norm_inv] at h3
      exact inv_le_of_inv_le₀ (norm_pos_iff.2 (α i).ne_zero) h3
    have hsum := GlobalTheory.T.hasSum_unramifiedZetaSum_unitary_inert _ ϖ c (qV D.host.F v) V.rank D.R.t hUI hrt (star (val χ w)) _ hnz hk X
      (ρ.comp e.symm.toMonoidHom) x α hsat htb ℓ ⟨C, fun g => hC _⟩
    rw [value_inert D B (val χ) v w hall hNw hstarB (by rw [hval]; push_cast; rfl) ((quadSign_eq D v).2 w hall), hBw, ← hr]
    refine hasSum_quot_of_equiv e he.2.2 (f := fun g => starRingEnd ℂ (φ g) * ℓ (ρ g x)) ?_ hsum
    intro g k hk'
    have e1 : φ (g * k) = φ g := by
      have := kerU_mul_right hUI ((hφ w h).2 hw c ϖ e hUI he) (e g) (e k) ((he.2.2 k).1 hk')
      simpa using this
    show starRingEnd ℂ (φ (g * k)) * ℓ (ρ (g * k) x) = starRingEnd ℂ (φ g) * ℓ (ρ g x)
    rw [e1, map_mul, Module.End.mul_apply, hfix k hk']

end GlobalTheory.LocZeta

end
