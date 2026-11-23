import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatHalfSpanModulatedTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor

noncomputable section

namespace GlobalTheory.ThetaOrth

variable {D : D7}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) :
    (starRingEnd ℂ) (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 x)]

theorem symplO_nsmul (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := GlobalTheory.SplitScalar.symplO_smul S T (N : AE D) x y
  rw [map_natCast] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) :
    symplO S T x (-y) = -symplO S T x y := by
  simp only [symplO, hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem isHalf_nsmul {m n : ℕ} {b : AE D} {y : Mx D m n} (hy : IsHalf b y) (N : ℕ) : IsHalf b (N • y) := by
  intro i j
  have e : (N • y) i j = N • y i j := rfl
  rw [e, nsmul_eq_mul, mul_left_comm, hy i j]

theorem isHalf_neg {m n : ℕ} {b : AE D} {y : Mx D m n} (hy : IsHalf b y) : IsHalf b (-y) := by
  intro i j
  have e : (-y) i j = -y i j := rfl
  rw [e, mul_neg, hy i j]

theorem isHalf_add {m n : ℕ} {b : AE D} {x y : Mx D m n} (hx : IsHalf b x) (hy : IsHalf b y) : IsHalf b (x + y) := by
  intro i j
  have e : (x + y) i j = x i j + y i j := rfl
  rw [e, mul_add, hx i j, hy i j]

theorem nsmul_add_neg {A : Type} [AddCommGroup A] (N k : ℕ) (t u v : A) (h : N • t = u + (N * k) • v) :
    N • (t + k • (-v)) = u := by
  rw [smul_add, h, smul_neg, mul_smul, smul_neg, add_neg_cancel_right]

theorem nsmul_add_mul {A : Type} [AddCommGroup A] (N k : ℕ) (t v : A) :
    N • (t + k • v) = N • t + (N * k) • v := by
  rw [smul_add, mul_smul]

theorem nsmul_inj {m n : ℕ} {N : ℕ} (hN : 0 < N) {x y : Mx D m n} (h : N • x = N • y) : x = y := by
  have hu : IsUnit (N : AE D) := by
    have h1 : IsUnit (N : D.host.E) := (Nat.cast_ne_zero.2 hN.ne').isUnit
    simpa only [map_natCast] using h1.map (incA D)
  refine Matrix.ext fun i j => ?_
  have e : N • x i j = N • y i j := congrFun (congrFun h i) j
  rw [nsmul_eq_mul, nsmul_eq_mul] at e
  exact hu.mul_left_cancel e

def charSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : AE D) : Submodule ℂ (WO S T → ℂ) :=
  Submodule.span ℂ {p | ∃ y : WO S T, IsHalf b y ∧ p = fun t => ψ (symplO S T t y)}

open Classical in

theorem exists_char_of_wave {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {a : AE D} {Λ : AddSubgroup (WO S T)} (N : ℕ)
    {Ψ : WO S T → ℂ}
    (hΨ : Ψ ∈ Submodule.span ℂ {Ψ : WO S T → ℂ | ∃ x y : WO S T, IsHalf a x ∧ IsHalf (cA D a) y ∧
      Ψ = fun t => ψ (symplO S T t y) * halfInd a Λ (t + x)}) :
    ∃ q ∈ charSpan ψ S T (cA D a), ∀ t : WO S T, IsHalf a t → N • t ∈ Λ → Ψ (N • t) = q t := by
  induction hΨ using Submodule.span_induction with
  | mem Ψ h =>
    obtain ⟨x, y, hx, hy, rfl⟩ := h
    by_cases hxΛ : x ∈ Λ
    · refine ⟨fun t => ψ (symplO S T t (N • y)), Submodule.subset_span ⟨N • y, isHalf_nsmul hy N, rfl⟩, fun t ht htΛ => ?_⟩
      have h1 : halfInd a Λ (N • t + x) = 1 :=
        if_pos ⟨Λ.add_mem htΛ hxΛ, isHalf_add (isHalf_nsmul ht N) hx⟩
      show ψ (symplO S T (N • t) y) * halfInd a Λ (N • t + x) = _
      rw [h1, mul_one, symplO_nsmul]
    · refine ⟨0, Submodule.zero_mem _, fun t ht htΛ => ?_⟩
      have h1 : halfInd a Λ (N • t + x) = 0 := if_neg fun h => hxΛ (by
        have := Λ.sub_mem h.1 htΛ
        rwa [add_sub_cancel_left] at this)
      show ψ (symplO S T (N • t) y) * halfInd a Λ (N • t + x) = 0
      rw [h1, mul_zero]
  | zero => exact ⟨0, Submodule.zero_mem _, fun _ _ _ => rfl⟩
  | add Ψ₁ Ψ₂ _ _ h₁ h₂ =>
    obtain ⟨q₁, m₁, e₁⟩ := h₁
    obtain ⟨q₂, m₂, e₂⟩ := h₂
    exact ⟨q₁ + q₂, Submodule.add_mem _ m₁ m₂, fun t ht hΛ => by
      rw [Pi.add_apply, Pi.add_apply, e₁ t ht hΛ, e₂ t ht hΛ]⟩
  | smul c Ψ _ h =>
    obtain ⟨q, m, e⟩ := h
    exact ⟨c • q, Submodule.smul_mem _ c m, fun t ht hΛ => by
      rw [Pi.smul_apply, Pi.smul_apply, e t ht hΛ]⟩

theorem pairing_charSpan {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hw : IsWeilDatumO ψ S T χS χT om)
    {a : AE D} {Λ : AddSubgroup (WO S T)} {f₀ Φ f : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a Λ 1 f₀ Tm) (hΦ : IsSBHalf a Λ Φ) (hfT : f = Tm Φ)
    (hf : IsThetaFunO ψ S T f) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (g : GA D T) {p : WO S T → ℂ} (hp : p ∈ charSpan ψ S T (cA D a)) :
    IsThetaFunO ψ S T (Tm fun t => p t * Φ t) ∧
      IsThetaFunO ψ S T (Tm fun t => (starRingEnd ℂ) (p (actO S T 1 g t)) * Φ t) ∧
      ipO μ 𝓕 (om (1, g) f) (Tm fun t => p t * Φ t) =
        ipO μ 𝓕 (om (1, g) (Tm fun t => (starRingEnd ℂ) (p (actO S T 1 g t)) * Φ t)) f := by
  have hψ := hw.std
  have hF := hw.om_pres (1, g) f hf
  have laws := fun {u v : WO S T → ℂ} (hu : IsThetaFunO ψ S T u) (hv : IsThetaFunO ψ S T v) =>
    GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 hψ hμ u v hu hv
  have hzero : IsThetaFunO ψ S T (0 : WO S T → ℂ) := by
    have := GlobalTheory.WeilVacMove.isTheta_smul (0 : ℂ) hf
    rwa [zero_smul] at this
  induction hp using Submodule.span_induction with
  | mem p h =>
    obtain ⟨y, hy, rfl⟩ := h
    have hθ := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
    set w : WO S T := actO S T 1⁻¹ g⁻¹ (-y) with hwdef
    have hact : actO S T 1 g w = -y := GlobalTheory.AdelicLatMove.actO_actO_inv S T 1 g (-y)
    have hwh : IsHalf (cA D a) w := GlobalTheory.SplitHecke.isHalf_actO _ _ (isHalf_neg hy)
    have e1 : (Tm fun t => ψ (symplO S T t y) * Φ t) = heisO ψ S T y f := by
      rw [hfT]; exact hTm.modul Φ hΦ y hy
    have e2 : (fun t => (starRingEnd ℂ) (ψ (symplO S T (actO S T 1 g t) y)) * Φ t) =
        fun t => ψ (symplO S T t w) * Φ t := by
      funext t
      rw [conj_psi hψ, ← GlobalTheory.SymplOInv.symplO_actO D S T 1 g t w, hact, symplO_neg_right]
    have e3 : (Tm fun t => ψ (symplO S T t w) * Φ t) = heisO ψ S T w f := by
      rw [hfT]; exact hTm.modul Φ hΦ w hwh
    show IsThetaFunO ψ S T (Tm fun t => ψ (symplO S T t y) * Φ t) ∧
      IsThetaFunO ψ S T (Tm fun t => (starRingEnd ℂ) (ψ (symplO S T (actO S T 1 g t) y)) * Φ t) ∧
      ipO μ 𝓕 (om (1, g) f) (Tm fun t => ψ (symplO S T t y) * Φ t) =
        ipO μ 𝓕 (om (1, g) (Tm fun t => (starRingEnd ℂ) (ψ (symplO S T (actO S T 1 g t) y)) * Φ t)) f
    rw [e2, e1, e3]
    refine ⟨hθ y f hf, hθ w f hf, ?_⟩
    rw [hw.om_heis 1 g w f hf, hact]
    have := ((laws hF hf).2.2.2.2.2.2.1 (-y)).2
    rw [neg_neg] at this
    exact this.symm
  | zero =>
    have e1 : (Tm fun t => (0 : WO S T → ℂ) t * Φ t) = 0 := by
      have : (fun t => (0 : WO S T → ℂ) t * Φ t) = 0 := by funext t; simp
      rw [this, map_zero]
    have e2 : (Tm fun t => (starRingEnd ℂ) ((0 : WO S T → ℂ) (actO S T 1 g t)) * Φ t) = 0 := by
      have : (fun t => (starRingEnd ℂ) ((0 : WO S T → ℂ) (actO S T 1 g t)) * Φ t) = 0 := by funext t; simp
      rw [this, map_zero]
    rw [e1, e2, map_zero]
    refine ⟨hzero, hzero, ?_⟩
    simp [ipO]
  | add p₁ p₂ _ _ h₁ h₂ =>
    obtain ⟨a₁, b₁, c₁⟩ := h₁
    obtain ⟨a₂, b₂, c₂⟩ := h₂
    have e1 : (Tm fun t => (p₁ + p₂) t * Φ t) = (Tm fun t => p₁ t * Φ t) + Tm fun t => p₂ t * Φ t := by
      rw [← map_add]; congr 1; funext t; simp [add_mul]
    have e2 : (Tm fun t => (starRingEnd ℂ) ((p₁ + p₂) (actO S T 1 g t)) * Φ t) =
        (Tm fun t => (starRingEnd ℂ) (p₁ (actO S T 1 g t)) * Φ t) +
          Tm fun t => (starRingEnd ℂ) (p₂ (actO S T 1 g t)) * Φ t := by
      rw [← map_add]; congr 1; funext t; simp [add_mul]
    rw [e1, e2, map_add]
    refine ⟨GlobalTheory.WeilVacMove.isTheta_add a₁ a₂, GlobalTheory.WeilVacMove.isTheta_add b₁ b₂, ?_⟩
    rw [((laws a₁ hF).2.2.2.1 _ a₂).2, ((laws (hw.om_pres _ _ b₁) hf).2.2.2.1 _ (hw.om_pres _ _ b₂)).1, c₁, c₂]
  | smul c p _ h =>
    obtain ⟨a₁, b₁, c₁⟩ := h
    have e1 : (Tm fun t => (c • p) t * Φ t) = c • Tm fun t => p t * Φ t := by
      rw [← map_smul]; congr 1; funext t; simp [mul_assoc]
    have e2 : (Tm fun t => (starRingEnd ℂ) ((c • p) (actO S T 1 g t)) * Φ t) =
        (starRingEnd ℂ) c • Tm fun t => (starRingEnd ℂ) (p (actO S T 1 g t)) * Φ t := by
      rw [← map_smul]; congr 1; funext t; simp [mul_assoc]
    rw [e1, e2, map_smul]
    refine ⟨GlobalTheory.WeilVacMove.isTheta_smul _ a₁, GlobalTheory.WeilVacMove.isTheta_smul _ b₁, ?_⟩
    rw [((laws hF a₁).2.2.1 c).2, ((laws (hw.om_pres _ _ b₁) hf).2.2.1 _).1, c₁]

theorem orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (f₀ Φ f : WO S T → ℂ), IsSBHalf (cA D e) (latO S T ΛS ΛT fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f → IsThetaFunO ψ S T f → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g ∈ GfC T, (∀ x, Φ x ≠ 0 → Φ (actO S T 1 g x) = 0) → l2 μ 𝓕 (om (1, g) f) f = 0 := by
  classical
  intro D ψ S T χS χT om hw ΛS ΛT hS hT Z e he f₀ Φ f hΦ hth hf μ 𝓕 hμ g hg hsupp
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hfT := hall Tm hTm
  have ho := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).conj
  have hψ := hw.std
  have hac : cA D e * cA D (cA D e) = 0 := by rw [cA_cA, mul_comm, he.2]
  obtain ⟨k, hk, hinv, hsup⟩ := hΦ.2
  obtain ⟨M, hM, hMact⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 1 g
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  set N : ℕ := M * k with hN
  have hNpos : 0 < N := Nat.mul_pos hM hk

  let Ψ : WO S T → ℂ := fun u => if ∃ t, Φ t ≠ 0 ∧ N • t = u then 1 else 0
  have hNt : ∀ t, Φ t ≠ 0 → N • t ∈ Λ := fun t ht => by
    rw [hN, mul_smul]; exact Λ.nsmul_mem (hsup t ht) M
  have hΨ : IsSBHalf (cA D e) Λ Ψ := by
    refine ⟨fun u hu => ?_, N * k, Nat.mul_pos hNpos hk, fun v hv hvh u => ?_, fun u hu => ?_⟩
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact isHalf_nsmul (hΦ.1 t ht) N
    · have key : (∃ t, Φ t ≠ 0 ∧ N • t = u + (N * k) • v) ↔ ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        constructor
        · rintro ⟨t, ht, h⟩
          refine ⟨t + k • (-v), by rwa [hinv (-v) (Λ.neg_mem hv) (isHalf_neg hvh) t], ?_⟩
          exact nsmul_add_neg N k t u v h
        · rintro ⟨t, ht, rfl⟩
          refine ⟨t + k • v, by rwa [hinv v hv hvh t], ?_⟩
          exact nsmul_add_mul N k t v
      show (if _ then _ else _) = (if _ then _ else _)
      simp only [key]
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact Λ.nsmul_mem (hNt t ht) _
  have hspan := (GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT hψ hS hT (cA D e) ho.idem hac ho.infPart_eq).2 Ψ hΨ
  obtain ⟨q, hq, hqΨ⟩ := exists_char_of_wave N hspan
  obtain ⟨-, -, hip⟩ := pairing_charSpan hw hTm hΦ hfT hf hμ g hq
  have hq1 : ∀ t, Φ t ≠ 0 → q t = 1 := fun t ht => by
    rw [← hqΨ t (hΦ.1 t ht) (hNt t ht)]
    exact if_pos ⟨t, ht, rfl⟩
  have hq0 : ∀ t, Φ t ≠ 0 → q (actO S T 1 g t) = 0 := fun t ht => by
    have h1 : N • actO S T 1 g t ∈ Λ := by
      have := hMact (k • t) (hsup t ht)
      have e : actO S T 1 g (k • t) = k • actO S T 1 g t := map_nsmul (GlobalTheory.LatLevel.actHom S T 1 g) k t
      rwa [e, ← mul_smul] at this
    rw [← hqΨ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ (hΦ.1 t ht)) h1]
    refine if_neg ?_
    rintro ⟨t', ht', h⟩
    have : t' = actO S T 1 g t := nsmul_inj hNpos h
    exact ht' (this ▸ hsupp t ht)
  have e1 : (fun t => q t * Φ t) = Φ := by
    funext t
    by_cases h : Φ t = 0
    · rw [h, mul_zero]
    · rw [hq1 t h, one_mul]
  have e2 : (fun t => (starRingEnd ℂ) (q (actO S T 1 g t)) * Φ t) = 0 := by
    funext t
    by_cases h : Φ t = 0
    · simp [h]
    · simp [hq0 t h]
  rw [e1, e2, map_zero, map_zero, ← hfT] at hip
  show ipO μ 𝓕 (om (1, g) f) f = 0
  rw [hip]
  simp [ipO]

end GlobalTheory.ThetaOrth
