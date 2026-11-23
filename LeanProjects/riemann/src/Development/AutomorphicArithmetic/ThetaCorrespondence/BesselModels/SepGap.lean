import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.BurGapOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.GapArith
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeparationLineOfBessel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsBesselFrameOfBesselDatumRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharTraceSingleRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCharacterRealPlaceUnipotentEqTraceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopLineFromSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisationFromTopLine
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace UpperTheory.Lit.Bur

def IsPosCfg {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (z : Fin n → ℂ) : Prop :=
  1 ≤ m ∧ (Formalism.QuantumDeterminants.herm J z z).re < 0 ∧ ∀ x : Fin m → ℂ, x ≠ 0 → 0 < (Formalism.QuantumDeterminants.herm J₀ x x).re

def HasGap {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Prop :=
  ∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ h : ℝ, 120 * (V.rank : ℝ) ^ 3 ≤ h ∧ Formalism.QuantumDeterminants.GapAtLeast (M.ε τ) (M.lam τ) h

section Model

open Matrix GlobalTheory.RealBessel

theorem burGap_model (hB : BurGapPos) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) {m r : ℕ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin V.rank) (Fin m) ℂ}
    {e : Matrix (Fin V.rank) (Fin r) ℂ} {z : Fin V.rank → ℂ} (hf : IsFrame (gramAt D V τ) J₀ F e z)
    (hc : IsPosCfg (gramAt D V τ) J₀ z)
    {χ : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ} (hχ : IsGeneric (gramAt D V τ) e z χ)
    (hP : Formalism.QuantumDeterminants.IsHCParam (M.lam τ)) {h : ℝ} (hh : 120 * (V.rank : ℝ) ^ 3 ≤ h)
    (hg : Formalism.QuantumDeterminants.GapAtLeast (M.ε τ) (M.lam τ) h)
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W} (hπ : IsContIrred (Formalism.QuantumDeterminants.UH J₀) π₀) :
    Module.rank ℂ (besselForms (gramAt D V τ) J₀ F e χ (M.rep τ) π₀ (M.sm τ)) ≤ 1 := by
  have hds := M.ds τ
  obtain ⟨hc', -, hU, hI, -⟩ := id hds
  rw [GlobalTheory.SmVec.sm_eq M τ]
  have hgap : IsGapDS (gramAt D V τ) (M.rep τ) h := by
    refine ⟨M.ε τ, M.lam τ, M.fr τ, M.fr_unit τ, M.fr_gram τ, hP, hg, ?_⟩
    have e1 : (fun g => M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ)) = M.σ τ := by
      funext g
      have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      show M.σ τ (M.fr τ * ((M.fr τ)⁻¹ * g * M.fr τ) * (M.fr τ)⁻¹) = M.σ τ g
      congr 1
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
        ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rw [e1]
    exact hds
  exact hB _ _ _ _ _ _ _ _ hf hc.1 hc.2.1 hc.2.2 χ hχ _ _ (GlobalTheory.SmVec.isURepOn_trRep (M.fr_unit τ) (M.fr_gram τ) hU)
    (GlobalTheory.SmVec.isIrredOn_trRep (M.fr_unit τ) (M.fr_gram τ) hI) h hh hgap W π₀ hπ

end Model

theorem sepLine_gap (hB : BurGapPos) (D : D7) (V A : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (r : ℕ)
    (F : D.what₂.Tau → Matrix (Fin V.rank) (Fin A.rank) ℂ) (e : D.what₂.Tau → Matrix (Fin V.rank) (Fin r) ℂ)
    (z : D.what₂.Tau → Fin V.rank → ℂ) (χ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (Wt : D.what₂.Tau → Type)
    [∀ τ, AddCommGroup (Wt τ)] [∀ τ, Module ℂ (Wt τ)] [∀ τ, FiniteDimensional ℂ (Wt τ)]
    (π : ∀ τ, Matrix (Fin A.rank) (Fin A.rank) ℂ → Module.End ℂ (Wt τ))
    (h : ∀ τ, GlobalTheory.RealBessel.IsFrame (gramAt D V τ) (gramAt D A τ) (F τ) (e τ) (z τ) ∧
      GlobalTheory.RealBessel.IsGeneric (gramAt D V τ) (e τ) (z τ) (χ τ) ∧
      GlobalTheory.RealBessel.IsContIrred (Formalism.QuantumDeterminants.UH (gramAt D A τ)) (π τ))
    (hc : ∀ τ, IsPosCfg (gramAt D V τ) (gramAt D A τ) (z τ)) (hg : HasGap M) :
    ∃ ℓ : (∀ τ, Wt τ) → M.Vec → ℂ, ∀ β, SepBes M F e χ π β → ∃ l : ℂ, ∀ x v, β x v = ℓ x v * l := by
  classical
  have hr := fun τ => burGap_model hB M τ (h τ).1 (hc τ) (h τ).2.1 (hg τ).1 (hg τ).2.choose_spec.1 (hg τ).2.choose_spec.2
    (h τ).2.2
  choose b hb using fun τ => rank_le_one_iff.1 (hr τ)
  refine ⟨fun x v => ∏ τ, (b τ).1 (x τ) (v τ), fun β hβ => ?_⟩
  obtain ⟨l, hl⟩ := mul_prod_of_separately (X := fun τ => Wt τ × M.sm τ) (fun τ p => (b τ).1 p.1 p.2)
    (fun p => β (fun τ => (p τ).1) fun τ => (p τ).2) fun τ p => by
      obtain ⟨b', hb', e'⟩ := hβ τ (fun τ => (p τ).1) fun τ => (p τ).2
      obtain ⟨c, hc⟩ := hb τ ⟨b', hb'⟩
      refine ⟨c, fun y => ?_⟩
      have e1 := e' y.1 y.2
      have e2 : b' = c • (b τ).1 := (congrArg Subtype.val hc).symm
      rw [e2] at e1
      refine Eq.trans ?_ e1
      congr 1 <;> funext ρ <;> by_cases hρ : ρ = τ
      · subst hρ; simp
      · simp [Function.update, hρ]
      · subst hρ; simp
      · simp [Function.update, hρ]
  exact ⟨l, fun x v => hl fun τ => (x τ, v τ)⟩

section Cfg

open Matrix
open scoped ComplexOrder

variable {D : D7}

theorem posDef_of_hasSignature_zero_negative {n p : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G p 0) : G.PosDef := by
  have hp : p = n := by
    obtain ⟨e, _, _⟩ := h
    simpa using (Fintype.card_congr e).symm
  subst hp
  exact Formalism.IndefR.Fin.Lifts.posDef_of_sig G h

theorem besselDatum_middleVector_norm_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (hε : ε ≠ 0) (ρ : ℕ)
    (h : c = 2 * ρ + 1) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.herm (gramAt D B τ) (fun k => tauE D τ ((d.besDat hε ρ h).z k))
      (fun k => tauE D τ ((d.besDat hε ρ h).z k)) = tauE D τ ε := by
  have h1 := congrFun (congrFun d.gram ⟨ρ, by omega⟩) ⟨ρ, by omega⟩
  have h2 : antiDiagonalSignGramMatrix c ε ⟨ρ, by omega⟩ ⟨ρ, by omega⟩ = ε := by
    simp only [antiDiagonalSignGramMatrix, if_true]
    rw [if_pos (by omega)]
  rw [h2] at h1
  refine Eq.trans ?_ (congrArg (tauE D τ) h1)
  show star _ ⬝ᵥ _ = _
  simp only [dotProduct, mulVec, gramAt, Matrix.mul_apply, Formalism.UG.cT, transpose_apply, map_apply, map_sum, map_mul,
    Pi.star_apply, HermitianOrthogonalExtensionData.besDat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (D.sp.cm.sig : D.host.E →+* D.host.E) (d.a j ⟨ρ, by omega⟩) = star (d.a j ⟨ρ, by omega⟩) from rfl,
    Formalism.IndefR.Eqv.tauE_star]
  simp only [RCLike.star_def]
  ring

theorem topCfg {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (τ : D.what₂.Tau) :
    IsPosCfg (gramAt D (G.V (.grid D.R.m 0)) τ) (gramAt D (G.V (.top 0)) τ) (fun k => tauE D τ (G.besTop.z k)) := by
  have hv := G.sp.P_is D.R.m le_rfl
  refine ⟨?_, ?_, ?_⟩
  · show 1 ≤ (G.sp.P D.R.m).sp.rank
    rw [hv.rank]
    simp only [rankP, nRk]
    omega
  · have e := besselDatum_middleVector_norm_eq (G.rowDec 0 (by have := D.R.two_le_m; omega)) (neg_ne_zero.2 one_ne_zero) ((D.R.m - 2) / 2)
      (by have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; omega) τ
    have e' : (fun k => tauE D τ (G.besTop.z k)) = fun k => tauE D τ
        (((G.rowDec 0 (by have := D.R.two_le_m; omega)).besDat (neg_ne_zero.2 one_ne_zero) ((D.R.m - 2) / 2)
          (by have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; omega)).z k) := rfl
    rw [e', e]
    simp
  · intro x hx
    have hs := hv.sigOK (tauE D τ)
    rw [hv.sig] at hs
    have hP : (gramAt D (G.V (.top 0)) τ).PosDef := posDef_of_hasSignature_zero_negative _ (by
      have e0 : (D.R.m - D.R.m + 1) / 2 = 0 := by omega
      rw [e0] at hs
      exact hs)
    exact hP.re_dotProduct_pos hx

end Cfg

theorem lastVertex_besselDatum_isFrame_isGeneric {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (τ : D.what₂.Tau) :
    GlobalTheory.RealBessel.IsFrame (gramAt D (G.V (.grid D.R.m 0)) τ) (gramAt D (G.V (.top 0)) τ)
      ((frameMat _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι).map (tauE D τ)) (G.besTop.e.map (tauE D τ))
      (fun k => tauE D τ (G.besTop.z k)) ∧
    GlobalTheory.RealBessel.IsGeneric (gramAt D (G.V (.grid D.R.m 0)) τ) (G.besTop.e.map (tauE D τ)) (fun k => tauE D τ (G.besTop.z k))
      fun u => besChar W.ψ G.besTop (atTau W.θ _ τ u) := by
  refine ⟨GlobalTheory.T.isBesselFrame_of_besselDatum_realPlace D _ _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom G.besTop τ, ?_⟩
  refine ⟨fun j => -(4 * Real.pi : ℂ) * tauE D τ (G.besTop.c j), fun j => ?_, fun u hu a ha => ?_⟩
  · refine mul_ne_zero (neg_ne_zero.2 (by exact_mod_cast (by positivity : (4 * Real.pi : ℝ) ≠ 0))) ?_
    exact (map_ne_zero _).2 (G.besTop.c_ne j)
  · obtain ⟨t, h1, h2, h3, h4⟩ := GlobalTheory.T.besselCharacter_realPlace_unipotent_eq_trace D W.θ W.θ_is W.ψ _ _ _ G.besTop τ u hu a ha
    show besChar W.ψ G.besTop (atTau W.θ _ τ u) = _
    rw [h4, GlobalTheory.T.standardChar_trace_single_realPlace D W.ψ W.ψ_std W.θ W.θ_is τ t h1 h2, h3, Finset.mul_sum]
    simp only [mul_assoc]

set_option maxHeartbeats 1600000 in

theorem topLine_gap (hB : BurGapPos) (hCT : CoefTensor) (hTS : TopSep) :
    All fun {D} _ _ _ {G} W M => ∀ (S : D.what₂.Tau → SPar) (MB : DSModel (G.V (.grid D.R.m 0)) S), HasGap MB →
      ∃ ℓ : Module.Dual ℂ (coefPlus G W.θ).W → SmT MB → ℂ, ∀ F' ∈ MultT W.θ MB ∅ 1, ∀ Ψ ∈ Cols G W.θ, ∃ l : ℂ,
        ∀ ξ v, Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ) (F' v) = ℓ ξ v * l := by
  intro D hOff T L μ0 hL sc G W M hM S MB hgap
  classical
  have hθ : IsInfFam W.θ := W.θ_is
  obtain ⟨Wt, _, _, _, π, e, hirr, heq⟩ := hCT D (G.V (.top 0)) W.θ (coefPlus G W.θ) hθ (GlobalTheory.TopLineProof.coefPlus_is G hθ)
  obtain ⟨ℓ₀, hℓ₀⟩ := sepLine_gap hB D (G.V (.grid D.R.m 0)) (G.V (.top 0)) S MB _ _ _
    (fun τ k => tauE D τ (G.besTop.z k)) _ Wt π (fun τ => ⟨(lastVertex_besselDatum_isFrame_isGeneric W τ).1, (lastVertex_besselDatum_isFrame_isGeneric W τ).2, hirr τ⟩)
    (fun τ => topCfg G τ) hgap
  have hx : Submodule.span ℂ (Set.range fun x : ∀ τ, Wt τ => e (PiTensorProduct.tprod ℂ x)) = ⊤ := by
    have h1 : (Set.range fun x : ∀ τ, Wt τ => e (PiTensorProduct.tprod ℂ x)) =
        (e : (⨂[ℂ] τ, Wt τ) →ₗ[ℂ] Module.Dual ℂ (coefPlus G W.θ).W) '' Set.range (PiTensorProduct.tprod ℂ) :=
      Set.range_comp _ _
    rw [h1, Submodule.span_image, PiTensorProduct.span_tprod_eq_top, Submodule.map_top, LinearEquiv.range]
  have hy : Submodule.span ℂ (Set.range fun v : MB.Vec => PiTensorProduct.tprod ℂ v) = ⊤ :=
    PiTensorProduct.span_tprod_eq_top
  by_cases h : ∃ F₀ ∈ MultT W.θ MB ∅ 1, ∃ Ψ₀ ∈ Cols G W.θ, ∃ ξ v, Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ₀) (F₀ v) ≠ 0
  · obtain ⟨F₀, hF₀, Ψ₀, hΨ₀, ξ₀, v₀, hne⟩ := h
    refine ⟨fun ξ v => Bplus W M (pairVec (coefPlus G W.θ) ξ Ψ₀) (F₀ v), fun F' hF' Ψ hΨ => ?_⟩
    obtain ⟨⟨b₀, hb₀⟩, hs₀⟩ := hTS D hOff T L μ0 hL sc G W M hM S MB F₀ hF₀ Ψ₀ hΨ₀
    obtain ⟨⟨b, hb⟩, hs⟩ := hTS D hOff T L μ0 hL sc G W M hM S MB F' hF' Ψ hΨ
    obtain ⟨l₀, hl₀⟩ := hℓ₀ _ (hs₀ Wt π e heq)
    obtain ⟨l, hl⟩ := hℓ₀ _ (hs Wt π e heq)
    have key := GlobalTheory.TopLineProof.bilin_prop _ _ hx hy b b₀ ℓ₀ l l₀ (fun x v => (hb _ _).symm.trans (hl x v))
      (fun x v => (hb₀ _ _).symm.trans (hl₀ x v)) fun h0 => hne (by rw [hb₀, h0]; rfl)
    refine ⟨l / l₀, fun ξ v => ?_⟩
    rw [hb]
    beta_reduce
    rw [hb₀, key, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  · push_neg at h
    exact ⟨0, fun F' hF' Ψ hΨ => ⟨0, fun ξ v => by rw [h F' hF' Ψ hΨ ξ v, mul_zero]⟩⟩

theorem factor_gap (hB : BurGapPos) (hCT : CoefTensor) (hTS : TopSep) (hT : RowTower) (D : D7) (large₂ : SizeData₂ D)
    (hsz : SizeRows large₂) (q : OffQ D) (s : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (T : Type) (L : LevCh D T) (μ0 : T) (hμ : L.Is μ0)
    (sc : Consts) (hc : sc.cGap = 1) (G : GridData L sc) (W : G.Weil) (M : Vol G) (hM : M.IsRow)
    (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0)) (h₀ : cart M₀ = W.cart (.grid 0 0)) (w : SmT M₀) :
    ∃ a : G.RealVec → Module.Dual ℂ (coefPlus G W.θ).W → ℂ, ∀ t ∈ Rows L W.θ M₀, ∀ Ψ ∈ Cols G W.θ, ∀ Φ,
      ∃ l : ℂ, ∀ ρ ξ, fPsiPhi W M ρ ξ Ψ Φ (t w) = a ρ ξ * l := by
  obtain ⟨S, MB, rfl, -, vec, hv⟩ := hT D q s T L μ0 hμ sc hc G W M hM M₀ h₀ D.R.m le_rfl
  obtain ⟨ℓ, hℓ⟩ := topLine_gap hB hCT hTS D q T L μ0 hμ sc G W M hM _ MB fun τ => Gap.fit_gap large₂ hsz hμ hc G MB τ
  refine ⟨fun ρ ξ => ℓ ξ (vec ρ w), fun t ht Ψ hΨ Φ => ?_⟩
  have ht' : t ∈ MultT W.θ M₀ ∅ 1 := factor_multT_le_empty _ _ _ _ ht
  obtain ⟨F', hF, hF'⟩ := hv t ht' Φ
  obtain ⟨l, hl⟩ := hℓ F' hF Ψ hΨ
  refine ⟨l, fun ρ ξ => ?_⟩
  have e : thetaChi W M ρ Φ (t w) = F' (vec ρ w) := (part_m W M ρ Φ (t w)).symm.trans (hF' ρ w).2
  rw [← hl, ← e]
  rfl

theorem separate_of_burGapPos (hB : BurGapPos) (hCT : CoefTensor) (hTS : TopSep) (hT : RowTower) :
    SizeGap → GoodRows → RowConv → WeakSep → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  intro hS hG hC hW ε CF hCF
  obtain ⟨x₁, hx₁⟩ := hS ε
  obtain ⟨x₂, hx₂⟩ := hW ε CF hCF
  refine ⟨max x₁ x₂, ?_⟩
  intro D large₂ he hx hsz _ Γ _ _ Pl0 T A Ks _ _ _ R hL _ G W hO M hM w hw
  have hSz : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D := hx₁ D large₂ he (le_of_max_le_left hx) hsz
  have hQ : OffQ D := offQ_of_sizeRows hsz
  have hm : 0 < D.R.m := by have := hsz.2.2.2.1; omega
  let M₀ : DSModel (Yc D 0) (parB (Ptw D) 0) := R.MY 0
  have hc : cart M₀ = W.cart (.grid 0 0) := (eq_of_heq (hO.cartY 0 hm)).symm
  have hWS := hx₂ D large₂ he (le_of_max_le_right hx) hsz T R.toLevCh A.μ0 hL G W M hM M₀ hc
  obtain ⟨a, ha⟩ := factor_gap hB hCT hTS hT D large₂ hsz hQ hSz T R.toLevCh A.μ0 hL ⟨1, CF, large₂.sc.b⟩ rfl G W M hM M₀ hc w
  have hCo := hC D hQ hSz T R.toLevCh A.μ0 hL ⟨1, CF, large₂.sc.b⟩ rfl G W M hM M₀ hc
  have hrow : ∀ t ∈ R.EEat R.triv, PiTensorProduct.lift t ∈ Rows R.toLevCh W.θ M₀ := by
    intro t ht
    rw [hO.θ]
    exact hG D Γ Pl0 T A Ks R hL t ht
  have hlift : ∀ t : Mult.MMap (R.MY 0), t ≠ 0 → PiTensorProduct.lift t ≠ 0 := fun t hne h =>
    hne (PiTensorProduct.lift.injective (h.trans (map_zero _).symm))
  by_cases h0 : ∃ t ∈ R.EEat R.triv, t ≠ 0
  · obtain ⟨t₀, ht₀, hne⟩ := h0
    obtain ⟨ρ₀, ξ₀, Ψ₀, hΨ₀, Φ₀, hf₀⟩ := hWS _ (hrow t₀ ht₀) (hlift t₀ hne) w hw
    obtain ⟨l₀, hl₀⟩ := ha _ (hrow t₀ ht₀) Ψ₀ hΨ₀ Φ₀
    have ha0 : a ρ₀ ξ₀ ≠ 0 := fun h => hf₀ (by rw [hl₀, h, zero_mul])
    refine ⟨ρ₀, ξ₀, fun t ht htne => ?_⟩
    obtain ⟨ρ, ξ, Ψ, hΨ, Φ, hf⟩ := hWS _ (hrow t ht) (hlift t htne) w hw
    obtain ⟨l, hl⟩ := ha _ (hrow t ht) Ψ hΨ Φ
    have hl' : l ≠ 0 := fun h => hf (by rw [hl, h, mul_zero])
    refine ⟨Ψ, hΨ, Φ, hCo _ (hrow t ht) w ρ₀ ξ₀ Ψ hΨ Φ, ?_⟩
    intro h
    exact mul_ne_zero ha0 hl' ((hl ρ₀ ξ₀).symm.trans h)
  · push_neg at h0
    exact ⟨Classical.arbitrary _, 0, fun t ht htne => absurd (h0 t ht) htne⟩

end UpperTheory.Lit.Bur

end
