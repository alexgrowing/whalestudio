import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicPointsSameBadComponentsSameLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllStepsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsFramesCongrAwayFromBadPrimesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelsCharacterOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameLocalCharacterDetCongruentOneEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedResiduesInFramesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoupledStepLocalDatumInvariantCosetMoveStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section
namespace GlobalTheory.TwV.AwayCpl
theorem frames_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : SB t μ, ∃ k : GLint t.X.E (D.R.N j) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l))) := GlobalTheory.T.chartPoints_frames_congr_away_from_badPrimes

theorem levAt_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.Ok → Pr.Ok → ChIdx.Ok Ch sel mu cst L G m2 → ∀ j (b : L.β j) (P : rowSG Pr sel mu) (k : GLint X.E (R.N j) P.1), j ≤ m2 + 1 →
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N j)) l))) →
    GlobalTheory.TopLaw.LevAt (L.levG j b) (L.levQ j b) P k 1 := GlobalTheory.T.congruent_one_mem_step_levels_character_one

theorem rhoS_det_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (i n : ℕ) (P : rowSG Pr sel mu) (k : GLint X.E n P.1),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E n) l))) →
    rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := GlobalTheory.T.tameLocalCharacter_det_congruent_one_eq_one

theorem exists_approx : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := GlobalTheory.T.exists_vector_prescribed_residues_in_frames

theorem psiAt_coset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    ChIdx.Ok Ch sel mu cst L G m2 → ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (k : GLint X.E (R.N (m2 + 1)) P.1)
    (w w₁ : Sp X.E (R.N (m2 + 1))),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) l))) →
    SameCoset sel mu cst P (k.1.symm w₁) w →
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w₁ = PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w := GlobalTheory.T.coupledStep_localDatum_invariant_coset_move

theorem lat_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := GlobalTheory.T.adelicPoints_same_badComponents_same_localization

theorem fnl_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := GlobalTheory.T.chartFunctional_eq_of_agree_badPlaces_allSteps

theorem intAt_sub {E : Type} [Field E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  obtain ⟨r₁, s₁, hs₁, e₁⟩ := ha
  obtain ⟨r₂, s₂, hs₂, e₂⟩ := hb
  refine ⟨s₂ * r₁ - s₁ * r₂, s₁ * s₂, fun hm => (P.isPrime.mem_or_mem hm).elim hs₁ hs₂, ?_⟩
  rw [map_sub, map_mul, map_mul, map_mul, ← e₁, ← e₂]
  ring

theorem phiT_data_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 ∧ ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTi j hj β x x₁ p p₁ h h₁ hag P
  have e := lat_away A dtU a hP hTi j hj β x x₁ p p₁ h h₁ hag P
  exact ⟨e, fnl_away A dtU a hP hTi j hj β x x₁ p p₁ h h₁ hag P e⟩

set_option maxHeartbeats 1000000 in
open Classical in

theorem ptAway_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i = t.m2 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTi i hi hi2
  subst hi2
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h h' h₁ h₁' hag
  have hX := hP.fields.ok
  have hPr := t.pr_ok
  have hL := t.idx_ok μ
  funext z
  unfold xiPt
  simp only [dif_neg (lt_irrefl _), if_pos rfl]
  unfold XiCpl1
  refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun P _ => ?_)

  · have H := phiT_data_away A dtU a hP hTi t.m2 _ β x x₁ p p₁ h h₁ (fun v hv => (hag v hv).1)
    have H' := phiT_data_away A dtU a hP hTi (t.m2 + 1) hi β' x' x₁' p' p₁' h' h₁' (fun v hv => (hag v hv).2)
    have e : ∀ P : t.Pr.vT (t.word u), (∀ y ∈ (p₁.deco.1).at P.1, z y ∈ (p₁'.deco.1).at P.1 ∧ p₁'.deco.1.f P (z y) = p₁.deco.1.f P y) ↔
        (∀ y ∈ (p.deco.1).at P.1, z y ∈ (p'.deco.1).at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y) := by
      intro P
      rw [(H P).1, (H' P).1]
      refine forall₂_congr fun y hy => and_congr_right fun hz => ?_
      rw [(H P).2 y hy, (H' P).2 _ hz]
    unfold phiT
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((forall_congr' e).1 h1) h2
    · exact absurd ((forall_congr' e).2 h2) h1
    · rfl

  · obtain ⟨k, hk, hkc⟩ := frames_away A dtU a hP hTi t.m2 _ β x x₁ p p₁ h h₁ (fun v hv => (hag v hv).1) P
    obtain ⟨k', hk', hkc'⟩ := frames_away A dtU a hP hTi (t.m2 + 1) hi β' x' x₁' p' p₁' h' h₁' (fun v hv => (hag v hv).2) P
    have hne : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
        repY (cosetOf A (t.m2 + 1) hi β' q) ∈ cosetOf A (t.m2 + 1) hi β' q := by
      intro q
      obtain ⟨y, hy⟩ := exists_approx t.X.E (D.R.N (t.m2 + 1)) (SB t μ) (frsF t.sel (t.tup μ) q) (y0At A (t.m2 + 1) hi β')
        (fun P => if P.1 ∈ t.Pr.vGs then 0 else (t.cst μ).M)
      exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β' q) ⟨y, fun P l => hy P l⟩
    obtain ⟨bL, -⟩ := hL.last_uniq
    have hc1 := hne p₁' P
    have hc0 := hne p' P
    rw [hk'] at hc1
    rw [hk, hk']
    generalize repY (cosetOf A (t.m2 + 1) hi β' p₁') = Y₁ at hc1 ⊢
    generalize repY (cosetOf A (t.m2 + 1) hi β' p') = Y₀ at hc0 ⊢
    generalize frsF t.sel (t.tup μ) p P = f at ⊢
    generalize frsF t.sel (t.tup μ) p' P = f' at hc0 hc1 ⊢
    rw [show (f' * k'.1).symm Y₁ = k'.1.symm (f'.symm Y₁) from rfl] at hc1
    have lawS := GlobalTheory.CoupledLaw.psiAt_source hX hPr hL (al := A.ib t.m2 hi β) (P := P) (κ := k) (a := 1)
      (levAt_one _ _ _ _ _ _ _ _ _ _ _ hX hPr hL t.m2 (A.ib t.m2 hi β) P k (Nat.le_succ _) hkc) (inFr f f' z) (f'.symm Y₁)
    have lawT := GlobalTheory.CoupledLaw.psiAt_target hX hPr hL (b := bL) (P := P) (κ := k') (a := 1)
      (levAt_one _ _ _ _ _ _ _ _ _ _ _ hX hPr hL (t.m2 + 1) bL P k' le_rfl hkc') ((t.idx μ).h t.m2 (A.ib t.m2 hi β) P)
      (k'.1.symm.toLinearMap ∘ₗ (inFr f f' z ∘ₗ k.1.toLinearMap)) (k'.1.symm (f'.symm Y₁))
    have hrS := rhoS_det_one t.X t.Pr D.R t.Ch t.sel t.S (t.tup μ) (t.cst μ) hL.cst_ok t.m2 _ P k hkc
    have hrT := rhoS_det_one t.X t.Pr D.R t.Ch t.sel t.S (t.tup μ) (t.cst μ) hL.cst_ok t.m2 _ P k' hkc'
    have hsc : SameCoset t.sel (t.tup μ) (t.cst μ) P (k'.1.symm (f'.symm Y₁)) (f'.symm Y₀) := fun l => by
      have := intAt_sub (hc1 l) (hc0 l)
      convert this using 1
      simp only [Pi.sub_apply]
      ring
    have hpsi := psiAt_coset _ _ _ _ _ _ _ _ _ _ _ hL (A.ib t.m2 hi β) P (inFr f f' z) k' (f'.symm Y₀) (f'.symm Y₁) hkc' hsc
    have e1 : inFr (f * k.1) (f' * k'.1) z = k'.1.symm.toLinearMap ∘ₗ (inFr f f' z ∘ₗ k.1.toLinearMap) := LinearMap.ext fun v => rfl
    have e2 : (f' * k'.1).symm Y₁ = k'.1.symm (f'.symm Y₁) := rfl
    have e3 : k'.1.toLinearMap ∘ₗ (k'.1.symm.toLinearMap ∘ₗ (inFr f f' z ∘ₗ k.1.toLinearMap)) = inFr f f' z ∘ₗ k.1.toLinearMap :=
      LinearMap.ext fun v => LinearEquiv.apply_symm_apply _ _
    have e4 : k'.1 (k'.1.symm (f'.symm Y₁)) = f'.symm Y₁ := LinearEquiv.apply_symm_apply _ _
    rw [e3, e4, hrT, mul_one, Units.val_one, one_mul] at lawT
    rw [hrS, mul_one, Units.val_one, one_mul] at lawS
    rw [e1, e2, ← lawT, lawS, hpsi]

end GlobalTheory.TwV.AwayCpl
