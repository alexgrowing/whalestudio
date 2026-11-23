import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizedLatticeEqOfAdelicMatricesAgreeAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeUnderLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainChartFramesBadPrimeCongruentOneOfAdelicAgreStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelLevelCharEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCharDetEqOneOfCongrOneModPowStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

noncomputable section

namespace GlobalTheory.AwayMat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levOne_of_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := GlobalTheory.T.congruentOne_mem_stepLevel_levelChar_eq_one

theorem muAt_det_of_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := GlobalTheory.T.localChar_det_eq_one_of_congr_one_mod_pow

theorem xiAt_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ), i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i)) (k' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1))),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N i)) l))) →
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k' (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N (i + 1))) l))) →
    ∀ x, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr k k' x) = XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hCh hsel hL i hi al be P k k' hk hk' x
  obtain ⟨r, hr, hrk, hc⟩ := levOne_of_cong Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi.le al P k hk
  obtain ⟨r', hr', hrk', hc'⟩ := levOne_of_cong Ch sel mu cst L G m2 hX hPr hCh hsel hL (i + 1) hi be P k' hk'
  have h := GlobalTheory.UnfoldTwoSided.xiAt_two_sided Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi al be P r r' k k' hr hr' hrk hrk' x
  rw [hc, hc', muAt_det_of_cong Ch sel mu cst L G m2 hX hPr hsel hL i P _ k hk, muAt_det_of_cong Ch sel mu cst L G m2 hX hPr hsel hL i P _ k' hk'] at h
  simpa only [one_mul] using h

theorem decoAtT_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    p₁.deco.1.at P.1 = p.deco.1.at P.1 ∧ ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := fun A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv => ⟨GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv, GlobalTheory.T.chartFunctional_eq_of_agree_under_levelPrime A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv⟩

theorem frames_cong : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := GlobalTheory.T.chainChart_frames_badPrime_congruent_one_of_adelic_agree

theorem inFr_mul {E : Type} [Field E] {n n' : ℕ} (f k : Sp E n ≃ₗ[E] Sp E n) (f' k' : Sp E n' ≃ₗ[E] Sp E n') (z : HomE E n n') :
    inFr (f * k) (f' * k') z = inFr k k' (inFr f f' z) := LinearMap.ext fun _ => rfl

theorem ptAway_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i < t.m2 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi him
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h1 h2 h3 h4 hag
  classical
  have hSS : (t.rd u μ).SS = Sall t.sel (t.tup μ) (t.word u) := ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 T.isChainTop).1
  have hv : ∀ Q, Q ∈ Sall t.sel (t.tup μ) (t.word u) → ∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam Q) →
      bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧ bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1 :=
    fun Q hQ v hvQ => hag v ⟨seamP t.seam Q, (mem_ssRec t u μ Q).2 (hSS ▸ hQ), hvQ⟩
  have hX : t.X.AbelianUnramifiedExtensionConditions := H.fields
  have hCh : t.Ch.Ok := H.ch.ch_ok
  have hL := t.idx_ok μ
  funext z
  unfold xiPt
  rw [dif_pos him, dif_pos him]
  unfold XiEntry
  refine congrArg₂ (· * ·) ?_ ?_
  · have eA := fun P : t.Pr.vT (t.word u) => decoAtT_eq A dtU a H T i _ β x x₁ p p₁ h1 h3 P
      (fun v hv' => (hv P.1 (Finset.mem_union_left _ P.2) v hv').1)
    have eA' := fun P : t.Pr.vT (t.word u) => decoAtT_eq A dtU a H T (i + 1) hi β' x' x₁' p' p₁' h2 h4 P
      (fun v hv' => (hv P.1 (Finset.mem_union_left _ P.2) v hv').2)
    have key : (∀ P : t.Pr.vT (t.word u), ∀ y ∈ p₁.deco.1.at P.1, z y ∈ p₁'.deco.1.at P.1 ∧ p₁'.deco.1.f P (z y) = p₁.deco.1.f P y) ↔
        (∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, z y ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y) := by
      refine forall_congr' fun P => ?_
      obtain ⟨a1, f1⟩ := eA P
      obtain ⟨a2, f2⟩ := eA' P
      rw [a1, a2]
      refine forall₂_congr fun y hy => and_congr_right fun hzy => ?_
      rw [f1 y hy, f2 _ hzy]
    unfold phiT
    by_cases hc : ∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, z y ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y
    · rw [if_pos hc, if_pos (key.2 hc)]
    · rw [if_neg hc, if_neg (fun h => hc (key.1 h))]
  · refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨k, hk, hkc⟩ := frames_cong A dtU a H T i _ β x x₁ p p₁ h1 h3 P
      (fun v hv' => (hv P.1 (Finset.mem_union_right _ P.2) v hv').1)
    obtain ⟨k', hk', hkc'⟩ := frames_cong A dtU a H T (i + 1) hi β' x' x₁' p' p₁' h2 h4 P
      (fun v hv' => (hv P.1 (Finset.mem_union_right _ P.2) v hv').2)
    rw [hk, hk', inFr_mul]
    exact xiAt_cong t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hX t.pr_ok hCh H.sel hL i him _ _ P k k' hkc hkc' _

end GlobalTheory.AwayMat
