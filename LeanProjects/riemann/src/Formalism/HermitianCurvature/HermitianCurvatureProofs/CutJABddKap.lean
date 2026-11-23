import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCont

open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP
open Formalism.QuantumDeterminants
open scoped ComplexConjugate Matrix

section gen

variable (P : M.Par)

theorem kap_toSm_smul (c : ℂ) (u : MA.Qp P.r P.TT → ℂ) :
    MA.toSm P (fun q => c * u q) = c • MA.toSm P u := by
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · have hcu : (fun q => c * u q) ∈ MA.smSub P.r P.TT := by
      have := Subalgebra.smul_mem (MA.smSub P.r P.TT) hu c
      exact this
    unfold MA.toSm
    rw [dif_pos hcu, dif_pos hu]
    rfl
  · by_cases hc : c = 0
    · subst hc
      have h0 : (fun q : MA.Qp P.r P.TT => (0 : ℂ) * u q) = 0 := by funext q; simp
      rw [h0, zero_smul]
      unfold MA.toSm
      rw [dif_pos (Subalgebra.zero_mem _)]
      rfl
    · have hcu : (fun q => c * u q) ∉ MA.smSub P.r P.TT := by
        intro h
        apply hu
        have := Subalgebra.smul_mem (MA.smSub P.r P.TT) h c⁻¹
        convert this using 1
        funext q
        show u q = c⁻¹ * (c * u q)
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      unfold MA.toSm
      rw [dif_neg hcu, dif_neg hu, smul_zero]

theorem actA_kap (κ : M.Ty P → ℂ) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.kap P (MA.DQ P) κ) f = fun ρ => κ ρ • f ρ := by
  funext ρ
  show ∑ π', ((MA.kap P (MA.DQ P) κ) ρ π').1 (f π') = κ ρ • f ρ
  rw [Finset.sum_eq_single ρ (fun π' _ h => ?_) (fun h => absurd (Finset.mem_univ ρ) h)]
  · show ((Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (κ π)) ρ ρ).1 (f ρ) = κ ρ • f ρ
    rw [Matrix.diagonal_apply_eq]
    rfl
  · show ((Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (κ π)) ρ π').1 (f π') = 0
    rw [Matrix.diagonal_apply_ne _ (Ne.symm h)]
    rfl

end gen

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def KapBigCell (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (κ : M.Ty (D.parOf S v) → ℂ)
    (c : B.Mat S.G.k S.G.r → ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))) : Prop :=
  ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, ∀ ρ (A : Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
    inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (c (B.gq (T v).base x) A)) = κ ρ * inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec A)

theorem trJ_kap_of_bigCell (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (κ : M.Ty (D.parOf S v) → ℂ)
    (c : B.Mat S.G.k S.G.r → ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v))))
    (hc : KapBigCell S T v e κ c) (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    MA.actA (D.parOf S v) (MA.kap (D.parOf S v) (MA.DQ (D.parOf S v)) κ) (trJ S T v e J) =
      trJ S T v e (fun g => c g (J g)) := by
  rw [actA_kap]
  funext ρ
  unfold trJ
  rw [← kap_toSm_smul]
  congr 1
  funext q
  rw [hc q.1 q.2 ρ]
  ring

end defs

section fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev FMap (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Type :=
  (Fin (2 * S.G.r + S.G.k + 1) → ℂ) → (Fin (2 * S.G.r + S.G.k + 1) → ℂ) → B.Mat S.G.k S.G.r →
    ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))

def FibreMapOK (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Φ Φa : FMap S v) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r =>
      Φ x.1 x.2.1 x.2.2) ∧
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r =>
      Φa x.1 x.2.1 x.2.2) ∧
  (∀ a a' ι A B', B.hsInner (Φ a a' ι A) B' = B.hsInner A (Φa a a' ι B')) ∧
  (∀ h ∈ Formalism.QuantumDeterminants.UWset S.G.k S.G.r (T v).base.z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset S.G.k S.G.r (T v).base.z', ∀ a a' ι X,
    Φ (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹) (((T v).base.π h).comp (X.comp ((T v).base.π' h'⁻¹))) =
      ((T v).base.π h).comp ((Φ a a' ι X).comp ((T v).base.π' h'⁻¹)) ∧
    Φa (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹) (((T v).base.π h).comp (X.comp ((T v).base.π' h'⁻¹))) =
      ((T v).base.π h).comp ((Φa a a' ι X).comp ((T v).base.π' h'⁻¹)))

def KapFibre (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (κ : M.Ty (D.parOf S v) → ℂ)
    (Φ : FMap S v) : Prop :=
  ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, ∀ ρ (A : Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
    inner ℂ (B.hsVec (e ρ x.2))
      (B.hsVec (Φ (SSn.phD x.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2)
        (conj (SSn.phD x.1) • SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2)
        (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2) A)) =
      κ ρ * inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec A)

def KapRealC (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (Bg : ℝ) (κ : M.Ty (D.parOf S v) → ℂ)
    (c ca : SSn.Coef S v) : Prop :=
  (∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')) ∧
    B.CkOn ⊤ (B.GPos (T v).base) c ∧ B.CkOn ⊤ (B.GPos (T v).base) ca ∧
    SSn.EqvC S T v c ∧ SSn.EqvC S T v ca ∧ SSn.CoefBd S T v c Bg ∧ SSn.CoefBd S T v ca Bg ∧ KapBigCell S T v e κ c

end fibre

def KapRealiser : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc Cb : ℝ, K ≤ Cc → K ≤ Cb → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → IsGauge S T v e →
      IsGaugeQQ S T v e → ∀ κ : M.Ty (D.parOf S v) → ℂ, ∃ c ca : SSn.Coef S v,
        KapRealC S T v e (Cb * ((S.G.r : ℝ) + 1)) κ c ca

def KapRep : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → IsGauge S T v e →
      IsGaugeQQ S T v e → ∀ κ : M.Ty (D.parOf S v) → ℂ, ∃ Φ Φa : FMap S v, FibreMapOK S T v Φ Φa ∧ KapFibre S T v e κ Φ

def DatumCompose : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (Bg : ℝ) (a a' : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ)) (ι : B.Mat S.G.k S.G.r → B.Mat S.G.k S.G.r)
    (Φ Φa : FMap S v),
    0 ≤ Bg → SSn.IsDatum S T v Bg a a' ι → FibreMapOK S T v Φ Φa →
    ∃ c ca : SSn.Coef S v, (∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')) ∧
      B.CkOn ⊤ (B.GPos (T v).base) c ∧ B.CkOn ⊤ (B.GPos (T v).base) ca ∧
      SSn.EqvC S T v c ∧ SSn.EqvC S T v ca ∧ SSn.CoefBd S T v c Bg ∧ SSn.CoefBd S T v ca Bg ∧
      ∀ g ∈ B.GPos (T v).base, c g = Φ (a g) (a' g) (ι g)

theorem kapRealiser_of (hC : DatumCompose) (hG : SSn.SSnGeom) (hR : KapRep) : KapRealiser := by
  obtain ⟨K1, hK1, hG⟩ := hG
  obtain ⟨K2, hK2, hR⟩ := hR
  refine ⟨max K1 K2, le_max_of_le_left hK1, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ
  obtain ⟨a, a', ι, hD⟩ := hG Cc Cb (le_trans (le_max_left _ _) hCc) (le_trans (le_max_left _ _) hCb)
    E Wp Wq S T f χ ν' m₀ top A₀ hB v
  obtain ⟨Φ, Φa, hΦ, hK⟩ := hR Cc (le_trans (le_max_right _ _) hCc) E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ
  have hBg : 0 ≤ Cb * ((S.G.r : ℝ) + 1) :=
    mul_nonneg (le_trans (le_trans hK1 (le_max_left _ _)) hCb) (by positivity)
  obtain ⟨c, ca, h1, h2, h3, h4, h5, h6, h7, hval⟩ := hC E Wp Wq S T v _ a a' ι Φ Φa hBg hD hΦ
  refine ⟨c, ca, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  intro x hx ρ A
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hxq : x ∈ Formalism.FourierDecayAlt.JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hxq
  have hpos : B.gq (T v).base x ∈ B.GPos (T v).base := ⟨hgq.1, hgq.2.2⟩
  obtain ⟨e1, e2, e3⟩ := hD.2.2.2.2.2.2.2 x hx
  rw [hval _ hpos, e1, e2, e3]
  exact hK x hx ρ A

section compose

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Classical in

def datumCoef (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Φ : FMap S v) (a a' : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ))
    (ι : B.Mat S.G.k S.G.r → B.Mat S.G.k S.G.r) : SSn.Coef S v :=
  fun g => if g ∈ B.GPos (T v).base then Φ (a g) (a' g) (ι g) else 0

variable (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
  (v : Fin S.f) (a a' : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ))
  (ι : B.Mat S.G.k S.G.r → B.Mat S.G.k S.G.r)

theorem datumCoef_pos (Φ : FMap S v) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GPos (T v).base) :
    datumCoef S T v Φ a a' ι g = Φ (a g) (a' g) (ι g) := by
  unfold datumCoef; rw [if_pos hg]

theorem datumCoef_neg (Φ : FMap S v) {g : B.Mat S.G.k S.G.r} (hg : g ∉ B.GPos (T v).base) :
    datumCoef S T v Φ a a' ι g = 0 := by
  unfold datumCoef; rw [if_neg hg]

theorem kap_hsVec_zero : B.hsVec (0 : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) = 0 := by
  unfold B.hsVec; ext i; simp

theorem datumCoef_adj (Φ Φa : FMap S v) (hΦ : FibreMapOK S T v Φ Φa) (x : B.Mat S.G.k S.G.r)
    (A B' : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    B.hsInner (datumCoef S T v Φ a a' ι x A) B' = B.hsInner A (datumCoef S T v Φa a a' ι x B') := by
  by_cases hx : x ∈ B.GPos (T v).base
  · rw [datumCoef_pos S T v a a' ι Φ hx, datumCoef_pos S T v a a' ι Φa hx]
    exact hΦ.2.2.1 _ _ _ _ _
  · rw [datumCoef_neg S T v a a' ι Φ hx, datumCoef_neg S T v a a' ι Φa hx]
    simp [B.hsInner, kap_hsVec_zero]

theorem kap_gpos_sgs {p : B.SS S.G.k S.G.r} (hp : (T v).base.inSS p) {g : B.Mat S.G.k S.G.r}
    (hg : g ∈ B.GV S.G.k S.G.r) : B.sgs p g ∈ B.GPos (T v).base ↔ g ∈ B.GPos (T v).base := by
  have e := Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.gf_sgs (T v).base hp g
  constructor
  · intro h; exact ⟨hg, e ▸ h.2⟩
  · intro h; exact ⟨Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.sgs_mem (T v).base hp hg, e.symm ▸ h.2⟩

theorem datumCoef_eqv {Bg : ℝ} (hD : SSn.IsDatum S T v Bg a a' ι) (Ψ : FMap S v)
    (hΨ : ∀ h ∈ Formalism.QuantumDeterminants.UWset S.G.k S.G.r (T v).base.z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset S.G.k S.G.r (T v).base.z', ∀ a0 a0' ι0 X,
      Ψ (h *ᵥ a0) (h' *ᵥ a0') (h * ι0 * h'⁻¹) (((T v).base.π h).comp (X.comp ((T v).base.π' h'⁻¹))) =
        ((T v).base.π h).comp ((Ψ a0 a0' ι0 X).comp ((T v).base.π' h'⁻¹))) :
    SSn.EqvC S T v (datumCoef S T v Ψ a a' ι) := by
  intro p hp g hg X
  by_cases hpos : g ∈ B.GPos (T v).base
  · have hpos' : B.sgs p g ∈ B.GPos (T v).base := (kap_gpos_sgs S T v hp hg).2 hpos
    rw [datumCoef_pos S T v a a' ι Ψ hpos, datumCoef_pos S T v a a' ι Ψ hpos']
    obtain ⟨e1, e2, e3⟩ := hD.2.2.2.1 p hp g hpos
    rw [e1, e2, e3]
    exact hΨ _ hp.1 _ hp.2.2.1 _ _ _ X
  · have hpos' : B.sgs p g ∉ B.GPos (T v).base := fun h => hpos ((kap_gpos_sgs S T v hp hg).1 h)
    rw [datumCoef_neg S T v a a' ι Ψ hpos, datumCoef_neg S T v a a' ι Ψ hpos']
    simp

theorem datumCoef_ckOn {Bg : ℝ} (hD : SSn.IsDatum S T v Bg a a' ι) (Ψ : FMap S v)
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r =>
        Ψ x.1 x.2.1 x.2.2)) :
    B.CkOn ⊤ (B.GPos (T v).base) (datumCoef S T v Ψ a a' ι) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, h1, hf1, e1⟩ := hD.1 g₀ hg₀
  obtain ⟨U2, f2, hU2, h2, hf2, e2⟩ := hD.2.1 g₀ hg₀
  obtain ⟨U3, f3, hU3, h3, hf3, e3⟩ := hD.2.2.1 g₀ hg₀
  have hGc : Continuous (fun g : B.Mat S.G.k S.G.r => Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf _ _).continuous
  refine ⟨U1 ∩ U2 ∩ U3 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g},
    fun g => Ψ (f1 g) (f2 g) (f3 g), ((hU1.inter hU2).inter hU3).inter (isOpen_lt continuous_const hGc),
    ⟨⟨⟨h1, h2⟩, h3⟩, hg₀.2⟩, ?_, ?_⟩
  · have hp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (f1 g, f2 g, f3 g))
        (U1 ∩ U2 ∩ U3 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g}) :=
      (hf1.mono fun g hg => hg.1.1.1).prodMk ((hf2.mono fun g hg => hg.1.1.2).prodMk (hf3.mono fun g hg => hg.1.2))
    exact hΨ.comp_contDiffOn hp
  · intro g hg hgv
    rw [datumCoef_pos S T v a a' ι Ψ ⟨hgv, hg.2⟩, e1 g hg.1.1.1 hgv, e2 g hg.1.1.2 hgv, e3 g hg.1.2 hgv]

end compose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def DatumBd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (Bg : ℝ) (a a' : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ)) (ι : B.Mat S.G.k S.G.r → B.Mat S.G.k S.G.r)
    (Ψ : FMap S v),
    0 ≤ Bg → SSn.IsDatum S T v Bg a a' ι →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r =>
        Ψ x.1 x.2.1 x.2.2) →
    SSn.CoefBd S T v (datumCoef S T v Ψ a a' ι) Bg

theorem datumCompose_of (h : DatumBd) : DatumCompose := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v Bg a a' ι Φ Φa hBg hD hΦ
  refine ⟨datumCoef S T v Φ a a' ι, datumCoef S T v Φa a a' ι, datumCoef_adj S T v a a' ι Φ Φa hΦ,
    datumCoef_ckOn S T v a a' ι hD Φ hΦ.1, datumCoef_ckOn S T v a a' ι hD Φa hΦ.2.1,
    datumCoef_eqv S T v a a' ι hD Φ (fun h hh h' hh' a0 a0' ι0 X => (hΦ.2.2.2 h hh h' hh' a0 a0' ι0 X).1),
    datumCoef_eqv S T v a a' ι hD Φa (fun h hh h' hh' a0 a0' ι0 X => (hΦ.2.2.2 h hh h' hh' a0 a0' ι0 X).2),
    h E Wp Wq S T v Bg a a' ι Φ hBg hD hΦ.1, h E Wp Wq S T v Bg a a' ι Φa hBg hD hΦ.2.1,
    fun g hg => datumCoef_pos S T v a a' ι Φ hg⟩

theorem kapRealiser_of_bd (hB : DatumBd) (hG : SSn.SSnGeom) (hR : KapRep) : KapRealiser :=
  kapRealiser_of (datumCompose_of hB) hG hR

def TypeProj : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → IsGauge S T v e →
      IsGaugeQQ S T v e →
      ∃ Pr : M.Ty (D.parOf S v) → (Fin (2 * S.G.r + S.G.k + 1) → ℂ) →
          ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
        (∀ σ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Pr σ)) ∧
        (∀ σ a A B', B.hsInner (Pr σ a A) B' = B.hsInner A (Pr σ a B')) ∧
        (∀ σ, ∀ h ∈ Formalism.QuantumDeterminants.UWset S.G.k S.G.r (T v).base.z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset S.G.k S.G.r (T v).base.z', ∀ a X,
          Pr σ (h *ᵥ a) (((T v).base.π h).comp (X.comp ((T v).base.π' h'⁻¹))) =
            ((T v).base.π h).comp ((Pr σ a X).comp ((T v).base.π' h'⁻¹))) ∧
        ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, ∀ σ ρ,
          Pr σ (SSn.phD x.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2) (e ρ x.2) =
            if σ = ρ then e ρ x.2 else 0

section tp

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem kap_hsVec_add (A A' : Wq →L[ℂ] Wp) : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
  unfold B.hsVec; ext i; simp

theorem kap_hsVec_sum {ι : Type*} (s : Finset ι) (A : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, A i) = ∑ i ∈ s, B.hsVec (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold B.hsVec; ext i; simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, kap_hsVec_add, ih]

theorem kap_hsInner_sum_left {ι : Type*} (s : Finset ι) (A : ι → (Wq →L[ℂ] Wp)) (B' : Wq →L[ℂ] Wp) :
    B.hsInner (∑ i ∈ s, A i) B' = ∑ i ∈ s, B.hsInner (A i) B' := by
  unfold B.hsInner; rw [kap_hsVec_sum, inner_sum]

theorem kap_hsInner_sum_right {ι : Type*} (s : Finset ι) (A : Wq →L[ℂ] Wp) (B' : ι → (Wq →L[ℂ] Wp)) :
    B.hsInner A (∑ i ∈ s, B' i) = ∑ i ∈ s, B.hsInner A (B' i) := by
  unfold B.hsInner; rw [kap_hsVec_sum, sum_inner]

theorem kap_hsInner_smul_left (c : ℂ) (A B' : Wq →L[ℂ] Wp) : B.hsInner (c • A) B' = c * B.hsInner A B' := by
  unfold B.hsInner; rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right]

theorem kap_hsInner_smul_right (c : ℂ) (A B' : Wq →L[ℂ] Wp) :
    B.hsInner A (c • B') = (starRingEnd ℂ) c * B.hsInner A B' := by
  unfold B.hsInner; rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_left]

end tp

theorem kapRep_of_typeProj (h : TypeProj) : KapRep := by
  obtain ⟨K, hK, h⟩ := h
  refine ⟨K, hK, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ
  obtain ⟨Pr, hs, hadj, heq, hline⟩ := h Cc hCc E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  refine ⟨fun a _ _ => ∑ σ, κ σ • Pr σ a, fun a _ _ => ∑ σ, (starRingEnd ℂ) (κ σ) • Pr σ a, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have h1 : ∀ σ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r =>
          κ σ • Pr σ x.1) := fun σ => ((hs σ).comp contDiff_fst).const_smul _
    exact ContDiff.sum fun σ _ => h1 σ
  · have h1 : ∀ σ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r =>
          (starRingEnd ℂ) (κ σ) • Pr σ x.1) := fun σ => ((hs σ).comp contDiff_fst).const_smul _
    exact ContDiff.sum fun σ _ => h1 σ
  · intro a a' ι A B'
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rw [kap_hsInner_sum_left, kap_hsInner_sum_right]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [kap_hsInner_smul_left, kap_hsInner_smul_right, hadj, Complex.conj_conj]
  · intro h hh h' hh' a a' ι X
    constructor
    · simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, heq _ h hh h' hh']
      ext w
      simp [map_sum, map_smul]
    · simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, heq _ h hh h' hh']
      ext w
      simp [map_sum, map_smul]
  · intro x hx ρ A
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rw [kap_hsVec_sum, inner_sum, Finset.sum_eq_single ρ]
    · rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right]
      congr 1
      have := hadj ρ (SSn.phD x.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2) A (e ρ x.2)
      unfold B.hsInner at this
      rw [this, hline x hx ρ ρ, if_pos rfl]
    · intro σ _ hσ
      rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right]
      have := hadj σ (SSn.phD x.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2) A (e ρ x.2)
      unfold B.hsInner at this
      rw [this, hline x hx σ ρ, if_neg hσ, kap_hsVec_zero, inner_zero_left, mul_zero]
    · intro h; exact absurd (Finset.mem_univ ρ) h

theorem kapRealiser_of_typeProj (hB : DatumBd) (hG : SSn.SSnGeom) (hP : TypeProj) : KapRealiser :=
  kapRealiser_of_bd hB hG (kapRep_of_typeProj hP)

end Formalism.FourierDecayAlt.P.CutMP.JA
