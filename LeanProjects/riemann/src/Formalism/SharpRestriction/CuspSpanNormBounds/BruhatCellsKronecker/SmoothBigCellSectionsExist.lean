import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TopsChoicePartA
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalVolumePositivity

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.LocalBesselAndTopKernel Formalism.QuantumDeterminants NumberField IsDedekindDomain ValuativeRel
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ThA_congr {CA : ℝ} {u u' : D.what₂.Word} {x : D.what₂.Tau → LocalDataRealPlace D} {L L0 : LatticeDataWithDual D}
    (h : IsLatGLOB D L) (h0 : IsLatGLOB D L0) : ThA D CA u u' x L = ThA D CA u u' x L0 := by
  have hV : L.aaV = L0.aaV := funext fun i => funext fun s => (h i s).1.trans (h0 i s).1.symm
  have hP : L.aaP = L0.aaP := funext fun i => funext fun s => (h i s).2.1.trans (h0 i s).2.1.symm
  have hr : L.ρ = L0.ρ := funext fun i => funext fun s => (h i s).2.2.trans (h0 i s).2.2.symm
  unfold ThA ThS ThInvF
  simp only [hV, hP, hr]

theorem rho_eq {L : LatticeDataWithDual D} (h : IsLatGLOB D L) : L.ρ = rhoReal D := by
  funext i s
  exact (h i s).2.2

theorem gE_ne (D : D7) : gE D ≠ 0 := by
  unfold gE
  exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem plEmb_gE (D : D7) (v : D.what₂.Tau) : plEmb D v (gE D) = ((D.host.g 0 * D.host.g 1 : ℕ) : ℂ) := by
  unfold gE
  simp

theorem psiAx_gE (D : D7) : PsiAx D (gE D) :=
  ⟨gE_ne D, Or.inr fun v => by rw [plEmb_gE]; exact Complex.natCast_im _⟩

theorem frame_axioms_bessel_datum {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {Cw : ℝ} (Y : LoopTie D large₂ X u u' Cw)
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') {L : LatticeDataWithDual D} (h : IsLatGLOB D L) :
    FrameAx D (gE D) L (fun v => localBesselDatumAtRealPlace Y hT hT' v) := by
  refine ⟨D.host.rdE, ⟨rdE_pos D, fun i s _ => (h i s).2.2⟩, fun v => ?_⟩
  have hr : (D.host.rdE : ℂ) ≠ 0 := by exact_mod_cast (rdE_pos D).ne'
  have h0 : ((D.host.g 0 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero
  have h1 : ((D.host.g 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero
  show (((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)) = cPsi D (gE D) v / (D.host.rdE : ℂ)
  unfold cPsi
  rw [plEmb_gE]
  unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
  push_cast
  field_simp
  ring

theorem local_match_bessel_datum {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {Cw : ℝ} (Y : LoopTie D large₂ X u u' Cw)
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') {x : D.what₂.Tau → LocalDataRealPlace D} (hx : IsLocA D u u' x) (v : D.what₂.Tau) :
    LocMatch D (Tr D u) (Tr D u') (x v) (localBesselDatumAtRealPlace Y hT hT' v) := by
  obtain ⟨h1, h2, h3⟩ := hx v
  obtain ⟨_, _, _, _, h5, h6, _⟩ := Y.goodW v
  exact ⟨h1.symm, h2.symm, h3.symm, h5, h6, rfl⟩

theorem interlace_cast {k n n' : ℕ} (e : n' = n) (hk : k ≤ n) (hk' : k ≤ n') (u : Fin k → ℝ) (lam : Fin n → ℝ)
    (h : InterlaceS hk u lam) : InterlaceS hk' u (fun i => lam (Fin.cast e i)) := by
  subst e
  exact h

section Steps

variable (D) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
  (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS)

def AmplitudeIsBesselCoefficient : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u'),
    ∃ f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp),
      IsAmpCoef (Y u u') hT hT' f

def SmoothBigCellSectionsExist : Prop :=
  ∀ (u u' : D.what₂.Word) (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (v : D.what₂.Tau),
    ∃ μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      IsSection D.R.k D.R.rS (localBesselDatumAtRealPlace (Y u u') hT hT' v).z (localBesselDatumAtRealPlace (Y u u') hT hT' v).z' μsec

def DensityBound (Ce : ℝ) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word),
    ∃ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (Dsup : ℝ), (∀ p, Irreducible (ϖ p)) ∧ 1 ≤ Dsup ∧ Dsup ≤ 2 ∧
      Dsup ≤ 1 + eSum D Ce ∧
      ∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
        densT (Z δ M hA u u') ϖ γ ≤ Dsup

def ColumnDominationBound : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp)),
    IsAmpCoef (Y u u') hT hT' f →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p), (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    GLOB.G2 δ M (Z δ M hA) cN → GLOB.CNT (Z δ M hA u u') (cN u u') →
  ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (Dsup : ℝ), (∀ p, Irreducible (ϖ p)) → 0 ≤ Dsup →
    (∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
      densT (Z δ M hA u u') ϖ γ ≤ Dsup) →
  ∀ (L : LatticeDataWithDual D) (Kd : KernelData D), IsLatGLOB D L → PSDK (Kd.K (D.R.rS + 1)) →
    (∀ h h', Kd.K (D.R.rS + 1) h h' = KA δ M (D.mem u).A.T (D.mem u').A.T Dsup (D.R.rS + 1) h h') →
  ∀ cW : ℝ, 0 < cW →
    (∀ w : Point D.host.E (D.R.rS + 1), TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) →
      n0 (cN u u') (D.mem u).A.T (D.mem u').A.T w * phiA δ M (D.mem u).A.T (D.mem u').A.T w ^ 2 =
        cW * ptWeightG D L.ρ (Tr D u) (Tr D u') w.1) →
  ∃ (ι : Type) (_ : Countable ι) (c : ι → Point D.host.E (D.R.rS + 1) → ℂ),
    RowsAx (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsInner)
      (Kd.K (D.R.rS + 1)) (fun h => ptWeightG D L.ρ (Tr D u) (Tr D u') h.1) c
      (fun v h => Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D L.ρ v h.1)) ∧
    ENNReal.ofReal (∑' q, formTerm (Y u u') hT hT' Vm f q).re ≤
      ENNReal.ofReal cW *
        SRowForm (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsInner)
          (fun h => ptWeightG D L.ρ (Tr D u) (Tr D u') h.1) c
          (fun v h => Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D L.ρ v h.1))

def qS : ℝ := ∑' p : PlF D, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-(D.R.k : ℤ))

def ConstantBoundAlt : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp)),
    IsAmpCoef (Y u u') hT hT' f →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p), GLOB.CNT (Z δ M hA u u') (cN u u') →
  ∀ L : LatticeDataWithDual D, IsLatGLOB D L → LatAx D (gE D) L →
    (∀ i s, IsBlockSL2Embedding D i s → (L.La i s : Set D.host.E) = La M δ (nu D.R.rS i (i + s - 1)) s ∧
      (L.La' i s : Set D.host.E) = LaP (D := D) (nu D.R.rS i (i + s - 1)) s) →
  ∀ cW : ℝ, 0 < cW →
    (∀ w : Point D.host.E (D.R.rS + 1), TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) →
      n0 (cN u u') (D.mem u).A.T (D.mem u').A.T w * phiA δ M (D.mem u).A.T (D.mem u').A.T w ^ 2 =
        cW * ptWeightG D L.ρ (Tr D u) (Tr D u') w.1) →
  ∀ μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
    (∀ v, IsSection D.R.k D.R.rS (localBesselDatumAtRealPlace (Y u u') hT hT' v).z (localBesselDatumAtRealPlace (Y u u') hT hT' v).z' (μsec v)) →
    ENNReal.ofReal ((D.duS u : ℝ) / dimPi (hc := D.hcW) u * cW) *
        jNorm2One (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsNormSq)
          D.R.k D.R.rS (Tr D u) (Tr D u') L.κ
          (fun v p => (localBesselDatumAtRealPlace (Y u u') hT hT' v).J (f v) (bigCell D.R.k D.R.rS p.1 (μsec v p.2))) ≤
      ENNReal.ofReal (Real.exp (8 * qS D) * ((D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar))

end Steps

theorem Nlet_five (D : D7) : Nlet D 5 = NA D := by
  rfl

theorem k_ge_of_hyp {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hH : hyp D large₂ C0 C' Cl Cg cb Cu cT CT) :
    4 * D.R.rS + 8 ≤ D.R.k := by
  obtain ⟨_, _, h3, h4, _⟩ := hH.2.1
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hr : 4 * D.R.rS + 8 = 2 * D.R.m + 4 := by
    simp only [Ranks.rS]; omega
  have h5 : 2 * D.R.m + 4 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left h2 2, Nat.pow_le_pow_left h2 3, sq_nonneg (D.R.m : ℤ)]
  omega

theorem typed_places_factor_nonneg (D : D7) : 0 ≤ ∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ)) := finprod_nonneg fun _ => finprod_nonneg fun _ => by positivity

theorem dimPi_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ dimPi (hc := D.hcW) u := by
  unfold dimPi
  positivity

theorem Dstar_pos (D : D7) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos

theorem theorem_S_of_estimates {large₂ : SizeData₂ D} {X : TermTie D} {Cw : ℝ} {Y : ∀ u u', LoopTie D large₂ X u u' Cw} {Z : TermLocs D X}
    {cN : D.what₂.Word → D.what₂.Word → ℝ} {Vm : ValMap D.R.k D.R.rS} {CA CA' Ce₀ Ce C0 C' Cl Cg cb Cu cT CT : ℝ}
    (hCA : 0 ≤ CA) (hForm : SpectralWeightsCM D large₂ X Cw Y Vm) (hThA : admA D CA CA' 5 Vm) (hG : GlobalLatticeMajorantHypothesis D Z cN)
    (hC : ColumnSpaceRanks D Z cN) (hAr : ArithmeticGlobalModelCondition D cN) (hH : hyp D large₂ C0 C' Cl Cg cb Cu cT CT)
    (hgap : ∀ τ, GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ))
      (CA * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D 5 * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)))
    (s1 : AmplitudeIsBesselCoefficient D large₂ X Cw Y) (s2 : SmoothBigCellSectionsExist D large₂ X Cw Y) (s3 : DensityBound D X Z Ce₀) (s4 : ColumnDominationBound D large₂ X Cw Y Z cN Vm)
    (s5 : ConstantBoundAlt D large₂ X Cw Y Z cN) (hAl : (1 + eSum D Ce₀) * Real.exp (8 * qS D) ≤ 1 + eSum D Ce) : Conclusion1 D CA CA' Ce := by
  intro u u' hne
  have hT : 0 < Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hT' : 0 < Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  obtain ⟨f, hf⟩ := s1 u u' hne hT hT'
  obtain ⟨hS1, _, hEq⟩ := hForm u u' hne hT hT' f hf
  refine ⟨hS1.of_norm, ?_⟩
  intro x L hx hL hcut hsm hTh
  have hk := k_ge_of_hyp hH
  obtain ⟨_, _, _, _, _, _, hI, hne', hmod, _, _, _, _, hTg⟩ := hH.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, _⟩ := hH.2.1
  obtain ⟨δ, M, hA, hG1, hG2, hG3, hG4⟩ := hG hk
  obtain ⟨L0, hL0, hLat, hLa, hrest⟩ := hAr hk δ M hA hG1 hG3 hG4
  have hmd : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] :=
    ((hmod u).2 : _ = _).trans ((hmod u').2 : _ = _).symm
  have hcop : ∀ w : D.what₂.Word, Nat.Coprime (D.mem w).A.T (Lat.gS D) := fun w =>
    Nat.Coprime.mul_right
      ((Nat.coprime_primes (D.mem w).A.T_prime (D.host.g_prime 0)).2 (hTg w).1)
      ((Nat.coprime_primes (D.mem w).A.T_prime (D.host.g_prime 1)).2 (hTg w).2)
  obtain ⟨hKd, hcW⟩ := hrest u u' (D.mem u).A.T_prime.pos (D.mem u').A.T_prime.pos hmd (hcop u) (hcop u')
  have hcnt := hC hk δ M hA u u' hmd
  obtain ⟨cW, hcW0, hcWid⟩ := hcW hcnt.1
  obtain ⟨ϖ, Dsup, hϖ, hD1, hD2, hDe, hDb⟩ := s3 δ M hA u u'
  obtain ⟨Kd, hAx, hK, he0, he1⟩ := hKd Dsup hD1 hD2
  obtain ⟨ι, hι, c, hRows, hle⟩ := s4 u u' hne hT hT' f hf δ M hA hmd hG2 hcnt ϖ Dsup hϖ (by linarith) hDb L0 Kd hL0
    (hAx.2.1 _ le_rfl) (hK _ le_rfl) cW hcW0 hcWid
  choose μsec hsec using s2 u u' hT hT'
  have hN : Nlet D 5 = NA D := Nlet_five D
  have hN0 : 0 ≤ NA D := by
    unfold NA; positivity
  have hThe : ThS D CA CA (Nlet D 5) (Tr D u) (Tr D u') (gE D) x L0 = ThA D CA u u' x L := by
    rw [ThA_congr hL hL0, hN]; rfl
  have hA' := hThA (gE D) (Tr D u) (Tr D u') x L0 Kd (fun v => localBesselDatumAtRealPlace (Y u u') hT hT' v) f μsec ι c (by norm_num) hv
    (psiAx_gE D) hLat (frame_axioms_bessel_datum (Y u u') hT hT' hL0) hAx.toF
    (fun v => ⟨local_match_bessel_datum (Y u u') hT hT' hx v, (hf v).1, hsec v⟩)
    (fun v => by
      rw [(hx v).1, (hx v).2.1, (hx v).2.2]
      exact ⟨interlace_cast (dimS_eq D.R) _ _ _ _ (hI u v), interlace_cast (dimS_eq D.R) _ _ _ _ (hI u' v)⟩)
    (fun v => by rw [(hx v).2.1, (hx v).2.2]; exact hne' u u' hne v)
    (fun v => by rw [(hx v).1]; exact hgap v)
    (fun v => by rw [(hx v).2.1, (hx v).2.2]; exact (hcut v).1)
    (fun v => by
      obtain ⟨_, _, h3, h4, h5⟩ := hcut v
      rw [hN]
      refine ⟨h3, ?_, h4, h5⟩
      have : 0 ≤ NA D ^ 3 / 2 := by positivity
      linarith)
    (fun v => by rw [hN]; exact (hcut v).2.1)
    (by rw [hThe, ← Real.rpow_natCast]; exact hsm)
    (by rw [hThe]; exact hTh) hRows
  rw [hThe] at hA'
  have hprod : ∏ i ∈ Finset.Icc 1 (D.R.rS + 1), (1 + Kd.e i) = Dsup := by
    rw [Finset.prod_Icc_succ_top (by omega), he1, Finset.prod_eq_one, one_mul]
    intro i hi
    rw [he0 i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2, add_zero]
  rw [hprod] at hA'
  have h5 := s5 u u' hne hT hT' f hf δ M hA hcnt L0 hL0 hLat hLa cW hcW0 hcWid μsec hsec

  set Th := ThA D CA u u' x L with hThdef
  have hpow : 0 ≤ (CA / Th) ^ D.R.f := by
    have : Even D.R.f := ⟨D.R.n, by unfold Ranks.f; ring⟩
    exact this.pow_nonneg _
  have hr0 : (0 : ℝ) ≤ (D.R.rS : ℝ) + 1 := by positivity
  set A : ℝ := (1 + CA * ((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f) * Dsup with hAdef
  have hA1 : 0 ≤ 1 + CA * ((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f := by positivity
  have hA0 : 0 ≤ A := mul_nonneg hA1 (by linarith)
  set dd : ℝ := (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar with hdd
  have hdd0 : 0 ≤ dd := div_nonneg (by positivity) (Dstar_pos D).le
  set q : ℝ := (D.duS u : ℝ) / dimPi (hc := D.hcW) u with hq
  have hq0 : 0 ≤ q := div_nonneg (Nat.cast_nonneg _) (dimPi_nonneg D u)
  set S : ℝ := (∑' q, formTerm (Y u u') hT hT' Vm f q).re with hSdef
  set E : ℝ := Real.exp (8 * qS D) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hchain : ENNReal.ofReal (q * S) ≤ ENNReal.ofReal (A * (E * dd)) := by
    rw [ENNReal.ofReal_mul hq0, ENNReal.ofReal_mul hA0]
    calc ENNReal.ofReal q * ENNReal.ofReal S
        ≤ ENNReal.ofReal q * (ENNReal.ofReal cW * (ENNReal.ofReal A * _)) :=
          mul_le_mul' le_rfl (hle.trans (mul_le_mul' le_rfl hA'))
      _ = ENNReal.ofReal A * (ENNReal.ofReal (q * cW) * _) := by
          rw [ENNReal.ofReal_mul hq0]; ring
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (E * dd) := mul_le_mul' le_rfl h5
  have hreal : q * S ≤ A * (E * dd) := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA0 (mul_nonneg hE0 hdd0))).1 hchain
  have hDal : Dsup * E ≤ 1 + eSum D Ce := le_trans (mul_le_mul_of_nonneg_right hDe hE0) hAl
  have hreal' : q * S ≤ (1 + CA * ((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f) * (1 + eSum D Ce) * dd := by
    calc q * S ≤ A * (E * dd) := hreal
      _ = (1 + CA * ((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f) * (Dsup * E) * dd := by rw [hAdef]; ring
      _ ≤ (1 + CA * ((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f) * (1 + eSum D Ce) * dd := by
          apply mul_le_mul_of_nonneg_right _ hdd0
          exact mul_le_mul_of_nonneg_left hDal hA1
  have hre : gaG D * (∑' P, gsFam D u u' P).re = q * S := by
    have := congrArg Complex.re hEq
    rwa [Complex.re_ofReal_mul, Complex.re_ofReal_mul] at this
  have hgs : genScal D u u' =
      (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) * (gaG D * (∑' P, gsFam D u u' P).re) := by
    unfold genScal gsFam
    rw [mul_assoc]
  rw [hgs, hre, Real.rpow_natCast]
  have hf3 := typed_places_factor_nonneg D
  calc (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) * (q * S)
      ≤ (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) *
          ((1 + CA * ((D.R.rS : ℝ) + 1) * (CA / Th) ^ D.R.f) * (1 + eSum D Ce) * dd) :=
        mul_le_mul_of_nonneg_left hreal' hf3
    _ = _ := by rw [hdd]; ring

theorem section_exists : ∀ (k r : ℕ) (L : LocBessel k r), 1 ≤ k → ∃ μsec, IsSection k r L.z L.z' μsec
  | 0, _, _, h => absurd h (by norm_num)
  | _ + 1, _, L, _ => Formalism.MainNotions.S.Inh.big_cell_section_of_local_bessel L

theorem smooth_big_cell_sections_exist (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) :
    SmoothBigCellSectionsExist D large₂ X Cw Y := fun u u' hT hT' v =>
  section_exists D.R.k D.R.rS (localBesselDatumAtRealPlace (Y u u') hT hT' v) (by have := D.R.m_add_three_le_k; omega)

theorem gap_of_hyp {large₂ : SizeData₂ D} {CA C0 C' Cl Cg cb Cu cT CT : ℝ} (hH : hyp D large₂ C0 C' Cl Cg cb Cu cT CT)
    (hCl : 8 ≤ Cl) (hm8 : (8 : ℝ) ≤ D.R.m) (hCA : 128 * |CA| ≤ D.R.m) (τ : D.what₂.Tau) :
    GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ))
      (CA * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D 5 * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)) := by
  have H : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 := ⟨hH.2.1, hH.1, hH.2.2⟩
  have h1 := std_ncgap H τ
  obtain ⟨_, _, h3, h4, _⟩ := hH.2.1
  have hmN : 8 ≤ D.R.m := by exact_mod_cast hm8
  have hm4 : 8 * D.R.m ≤ D.R.m ^ 4 := by
    have : 8 ≤ D.R.m ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) D.R.m)
    calc 8 * D.R.m ≤ D.R.m ^ 3 * D.R.m := Nat.mul_le_mul_right _ this
      _ = D.R.m ^ 4 := by ring
  have hkm : 8 * D.R.m ≤ D.R.k := le_trans hm4 (le_trans h3 h4)
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.m ≤ D.R.r)
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) h3
    exact_mod_cast this
  have hNl : Nlet D 5 = 10 * (D.R.m : ℝ) := by
    rw [← std_castM D]; unfold Nlet; push_cast; ring
  have hN2 : Nlet D 5 ≤ 2 * (D.R.r : ℝ) := by
    rw [hNl]
    have : 10 * D.R.m ≤ 2 * D.R.r := by omega
    exact_mod_cast this
  have hnum := std_num_nc CA Cl D.R.m D.R.r D.R.f large₂.sc.L (Nlet D 5) hm8 hmr hCA hCl hf1 (std_L_ge D large₂)
    (by rw [hNl]; positivity) hN2
  intro a b hab
  exact le_trans hnum (h1 a b hab)

theorem theorem_S_of_column_estimates {large₂ : SizeData₂ D} {X : TermTie D} {Cw : ℝ} {Y : ∀ u u', LoopTie D large₂ X u u' Cw} {Z : TermLocs D X}
    {cN : D.what₂.Word → D.what₂.Word → ℝ} {Vm : ValMap D.R.k D.R.rS}
    {Ca Cq C0 C' Cl Cg cb Cu cT CT CA CA' Ce₀ Ce : ℝ}
    (hCA : 0 ≤ CA) (hCl : 8 ≤ Cl) (hm8 : (8 : ℝ) ≤ D.R.m) (hCAm : 128 * |CA| ≤ D.R.m)
    (s1 : AmplitudeIsBesselCoefficient D large₂ X Cw Y) (s3 : DensityBound D X Z Ce₀) (s4 : ColumnDominationBound D large₂ X Cw Y Z cN Vm)
    (s5 : ConstantBoundAlt D large₂ X Cw Y Z cN) (hAl : (1 + eSum D Ce₀) * Real.exp (8 * qS D) ≤ 1 + eSum D Ce) :
    IntegralityFromMetric D large₂ X Cw Y Z cN Vm Ca Cq C0 C' Cl Cg cb Cu cT CT CA CA' Ce := by
  unfold IntegralityFromMetric
  intro _ hA hH
  unfold Adm1 at hA
  obtain ⟨-, -, -, -, -, -, -, -, -, hThA, -, hG, hC, hForm, hAr, -, -, -⟩ := hA
  exact theorem_S_of_estimates hCA hForm hThA hG hC hAr hH (fun τ => gap_of_hyp hH hCl hm8 hCAm τ) s1
    (smooth_big_cell_sections_exist D large₂ X Cw Y) s3 s4 s5 hAl

open Formalism.FourierDecayAlt.S3 in

theorem massData_const {P : Type} [Fintype P] (B : MassData P) (hP : B.Pos) (hI : 0 ≤ B.IntN) (h1 : B.InMass) (h2 : B.InJacMod)
    (h3 : B.InNu) (h4 : B.InInfinity) (h5 : B.InVolumes) (h6 : B.InLevelS) (h7 : B.InMasses) (h8 : B.InColumns)
    (h9 : B.InOrdinary) (h10 : B.InTyped) (h11 : B.InIndices) :
    B.d / B.dimπ * (B.n0c * (B.IntN / (B.c0 * B.c0'))) ≤ B.d * B.d' / B.Dstar := by
  obtain ⟨hp, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23,
    q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, _, _⟩ := hP
  have hc0 : 0 < B.c0 := div_pos (mul_pos q23 q21) q27
  have hc0' : 0 < B.c0' := div_pos (mul_pos q24 q22) q28
  let B' : MassData P := { B with
    δ := 0, supdens := 1, e1 := 1, KtopV := B.IntN / (B.c0 * B.c0'), KV := B.n0c * (B.IntN / (B.c0 * B.c0')),
    Sig := B.ρ0 * (B.n0c * (B.IntN / (B.c0 * B.c0'))),
    Kgs2 := B.tt * B.Gam1 * (B.ρ0 * (B.n0c * (B.IntN / (B.c0 * B.c0')))) }
  have hK0 : 0 ≤ B.IntN / (B.c0 * B.c0') := div_nonneg hI (mul_pos hc0 hc0').le
  have hmain := Formalism.FourierDecayAlt.P.mass_formula_constant_one P B'
    ⟨hp, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23,
      q24, q25, q26, q27, q28, q29, q30, q31, q32, q33, zero_le_one, le_rfl⟩
    (le_refl _) rfl
    ⟨by show B.n0c * (B.IntN / (B.c0 * B.c0')) ≤ 1 * B.n0c * (B.IntN / (B.c0 * B.c0')); rw [one_mul], hK0⟩
    h1 (le_refl _)
    (by
      show B.c0 * B.c0' * (B.IntN / (B.c0 * B.c0')) ≤ (1 + 0) * B.IntN
      rw [mul_div_cancel₀ _ (mul_pos hc0 hc0').ne']; linarith)
    h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  have h := hmain.2.1
  have htt : 0 < B.tt := Finset.prod_pos fun p _ => by
    have := (hp p).1
    positivity
  have h' : B.tt * (B.d / B.dimπ) * (B.n0c * (B.IntN / (B.c0 * B.c0'))) ≤
      (1 + 0) * 1 * B.tt * (B.d * B.d' / B.Dstar) := h
  have h'' : B.tt * (B.d / B.dimπ * (B.n0c * (B.IntN / (B.c0 * B.c0')))) ≤ B.tt * (B.d * B.d' / B.Dstar) := by
    calc _ = B.tt * (B.d / B.dimπ) * (B.n0c * (B.IntN / (B.c0 * B.c0'))) := by ring
      _ ≤ _ := h'
      _ = _ := by ring
  exact le_of_mul_le_mul_left h'' htt

section MassDataStep

variable (D) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
  (cN : D.what₂.Word → D.what₂.Word → ℝ)

open Formalism.FourierDecayAlt.S3 in

def ParamsBound : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp)),
    IsAmpCoef (Y u u') hT hT' f →
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p), GLOB.CNT (Z δ M hA u u') (cN u u') →
  ∀ L : LatticeDataWithDual D, IsLatGLOB D L → LatAx D (gE D) L →
    (∀ i s, IsBlockSL2Embedding D i s → (L.La i s : Set D.host.E) = La M δ (nu D.R.rS i (i + s - 1)) s ∧
      (L.La' i s : Set D.host.E) = LaP (D := D) (nu D.R.rS i (i + s - 1)) s) →
  ∀ cW : ℝ, 0 < cW →
    (∀ w : Point D.host.E (D.R.rS + 1), TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) →
      n0 (cN u u') (D.mem u).A.T (D.mem u').A.T w * phiA δ M (D.mem u).A.T (D.mem u').A.T w ^ 2 =
        cW * ptWeightG D L.ρ (Tr D u) (Tr D u') w.1) →
  ∀ μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
    (∀ v, IsSection D.R.k D.R.rS (localBesselDatumAtRealPlace (Y u u') hT hT' v).z (localBesselDatumAtRealPlace (Y u u') hT hT' v).z' (μsec v)) →
    ∃ (P : Type) (_ : Fintype P) (B : MassData P), B.Pos ∧ 0 ≤ B.IntN ∧ B.InMass ∧ B.InJacMod ∧ B.InNu ∧ B.InInfinity ∧
      B.InVolumes ∧ B.InLevelS ∧ B.InMasses ∧ B.InColumns ∧ B.InOrdinary ∧ B.InTyped ∧ B.InIndices ∧ B.al⁻¹ ≤ Real.exp (8 * qS D) ∧
      B.d = (D.duS u : ℝ) ∧ B.d' = (D.duS u' : ℝ) ∧ B.Dstar = D.what₂.Dstar ∧ B.dimπ = dimPi (hc := D.hcW) u ∧
      ENNReal.ofReal cW *
        jNorm2One (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsNormSq)
          D.R.k D.R.rS (Tr D u) (Tr D u') L.κ
          (fun v p => (localBesselDatumAtRealPlace (Y u u') hT hT' v).J (f v) (bigCell D.R.k D.R.rS p.1 (μsec v p.2))) =
        ENNReal.ofReal (B.n0c / B.al * (B.IntN / (B.c0 * B.c0')))

theorem constant_bound_of_massDataBound (h : ParamsBound D large₂ X Cw Y Z cN) : ConstantBoundAlt D large₂ X Cw Y Z cN := by
  intro u u' hne hT hT' f hf δ M hA hcnt L hL hLat hLa cW hcW hid μsec hsec
  obtain ⟨P, _, B, hP, hI, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hal, ed, ed', eD, eπ, eJ⟩ :=
    h u u' hne hT hT' f hf δ M hA hcnt L hL hLat hLa cW hcW hid μsec hsec
  have hb := massData_const B hP hI h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [ed, ed', eD, eπ] at hb
  have hal0 : 0 < B.al := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hP
    exact h
  have hq0 : 0 ≤ (D.duS u : ℝ) / dimPi (hc := D.hcW) u := div_nonneg (Nat.cast_nonneg _) (dimPi_nonneg D u)
  have hdd0 : 0 ≤ (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar := div_nonneg (by positivity) (Dstar_pos D).le
  rw [ENNReal.ofReal_mul hq0, mul_assoc, eJ, ← ENNReal.ofReal_mul hq0]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (D.duS u : ℝ) / dimPi (hc := D.hcW) u * (B.n0c / B.al * (B.IntN / (B.c0 * B.c0')))
      = B.al⁻¹ * ((D.duS u : ℝ) / dimPi (hc := D.hcW) u * (B.n0c * (B.IntN / (B.c0 * B.c0')))) := by
        rw [div_eq_mul_inv B.n0c]; ring
    _ ≤ B.al⁻¹ * ((D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hal0.le)
    _ ≤ Real.exp (8 * qS D) * ((D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar) :=
        mul_le_mul_of_nonneg_right hal hdd0

end MassDataStep

theorem family_theorem_S_of_pointwise {eps : ℝ} (Fm : FamP eps) {C0 Cg cb Cu cT CT CA CA' Ce₀ Ce : ℝ} (hCA : 0 ≤ CA)
    (hCl : 8 ≤ sCl Fm)
    (H : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x,
      hyp (Fm.D x i) (Fm.L x i) C0 (sC' Fm) (sCl Fm) Cg cb Cu cT CT →
      ∃ (X : TermTie (Fm.D x i)) (Cw : ℝ) (Y : ∀ u u', LoopTie (Fm.D x i) (Fm.L x i) X u u' Cw)
        (Z : TermLocs (Fm.D x i) X) (cN : (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ)
        (Vm : ValMap (Fm.D x i).R.k (Fm.D x i).R.rS),
        SpectralWeightsCM (Fm.D x i) (Fm.L x i) X Cw Y Vm ∧ admA (Fm.D x i) CA CA' 5 Vm ∧ GlobalLatticeMajorantHypothesis (Fm.D x i) Z cN ∧
        ColumnSpaceRanks (Fm.D x i) Z cN ∧ ArithmeticGlobalModelCondition (Fm.D x i) cN ∧ AmplitudeIsBesselCoefficient (Fm.D x i) (Fm.L x i) X Cw Y ∧
        DensityBound (Fm.D x i) X Z Ce₀ ∧ ColumnDominationBound (Fm.D x i) (Fm.L x i) X Cw Y Z cN Vm ∧
        ConstantBoundAlt (Fm.D x i) (Fm.L x i) X Cw Y Z cN ∧ (1 + eSum (Fm.D x i) Ce₀) * Real.exp (8 * qS (Fm.D x i)) ≤ 1 + eSum (Fm.D x i) Ce) :
    ConclusionF1 Fm C0 Cg cb Cu cT CT CA CA' Ce := by
  obtain ⟨x0, H⟩ := H
  obtain ⟨x2, _, hm⟩ := ev_m Fm (max 8 (128 * |CA|))
  unfold ConclusionF1 UnderF
  refine ownEv_intro Fm (max x0 x2) fun x hx hx1 i => ?_
  intro hH
  obtain ⟨X, Cw, Y, Z, cN, Vm, a1, a2, a3, a4, a5, s1, s3, s4, s5, hAl⟩ := H x (le_trans (le_max_left _ _) hx) hx1 i hH
  have hmx := hm x (le_trans (le_max_right _ _) hx) i
  exact theorem_S_of_estimates hCA a1 a2 a3 a4 a5 hH
    (gap_of_hyp hH hCl (le_trans (le_max_left _ _) hmx) (le_trans (le_max_right _ _) hmx)) s1 (smooth_big_cell_sections_exist _ _ X Cw Y) s3 s4 s5 hAl

section RowsLemmas

open Finset
open scoped ComplexOrder

theorem quad_rows {J : Type} [Fintype J] (Kt Kg C0 : J → J → ℂ) (Dsup : ℝ) (n0 φ : J → ℝ) (hn0 : ∀ x, 0 ≤ n0 x)
    (h1 : ((Dsup : ℂ) • (Matrix.of fun x y => Kt x y) -
      Matrix.of fun x y => Kg x y / ((Real.sqrt (n0 x * n0 y) : ℝ) : ℂ)).PosSemidef)
    (h2 : (Matrix.of fun x y => Kg x y - C0 x y).PosSemidef) (a : J → ℂ) :
    0 ≤ ∑ x, ∑ y, star (a x) * ((Dsup : ℂ) * Kt x y / ((φ x * φ y : ℝ) : ℂ) -
      C0 x y * ((((Real.sqrt (n0 x) * φ x)⁻¹ * (Real.sqrt (n0 y) * φ y)⁻¹ : ℝ)) : ℂ)) * a y := by
  have hs : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => Complex.conj_ofReal r
  have hsq : ∀ x y, (((Real.sqrt (n0 x * n0 y) : ℝ) : ℂ))⁻¹ * (((φ x)⁻¹ : ℝ) : ℂ) * (((φ y)⁻¹ : ℝ) : ℂ) =
      (((Real.sqrt (n0 x) * φ x)⁻¹ : ℝ) : ℂ) * (((Real.sqrt (n0 y) * φ y)⁻¹ : ℝ) : ℂ) := by
    intro x y
    rw [Real.sqrt_mul (hn0 x)]
    push_cast
    ring
  have H1 := h1.dotProduct_mulVec_nonneg (fun x => a x * (((φ x)⁻¹ : ℝ) : ℂ))
  have H2 := h2.dotProduct_mulVec_nonneg (fun x => a x * (((Real.sqrt (n0 x) * φ x)⁻¹ : ℝ) : ℂ))
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, Finset.mul_sum] at H1 H2
  have H := add_nonneg H1 H2
  rw [← Finset.sum_add_distrib] at H
  convert H using 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e := hsq x y
  rw [star_mul', star_mul', hs, hs]
  push_cast at e ⊢
  simp only [div_eq_mul_inv]
  linear_combination (star (a x) * a y * Kg x y) * e

theorem sum_split {α : Type} [DecidableEq α] (X : Finset α) (p : α → Prop) [DecidablePred p] (F : α → α → ℂ)
    (h1 : ∀ x y, p x → ¬ p y → F x y = 0) (h2 : ∀ x y, ¬ p x → p y → F x y = 0) :
    ∑ x ∈ X, ∑ y ∈ X, F x y =
      ∑ x ∈ X.filter p, ∑ y ∈ X.filter p, F x y + ∑ x ∈ X.filter (fun x => ¬ p x), ∑ y ∈ X.filter (fun x => ¬ p x), F x y := by
  have e : ∀ x, ∑ y ∈ X, F x y = ∑ y ∈ X.filter p, F x y + ∑ y ∈ X.filter (fun x => ¬ p x), F x y :=
    fun x => (Finset.sum_filter_add_sum_filter_not X p (F x)).symm
  have z1 : ∑ x ∈ X.filter p, ∑ y ∈ X.filter (fun x => ¬ p x), F x y = 0 :=
    Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy =>
      h1 x y (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hy).2
  have z2 : ∑ x ∈ X.filter (fun x => ¬ p x), ∑ y ∈ X.filter p, F x y = 0 :=
    Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy =>
      h2 x y (Finset.mem_filter.1 hx).2 (Finset.mem_filter.1 hy).2
  rw [← Finset.sum_filter_add_sum_filter_not X p]
  simp only [e, Finset.sum_add_distrib]
  rw [z1, z2, add_zero, zero_add]

theorem nMod_nonneg (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ)
    (a s : ℕ) (t : D.host.E) : 0 ≤ nMod δ M T T' a s t := by
  unfold nMod
  refine finprod_nonneg fun p => inv_nonneg.mpr ?_
  first
  | (unfold Loc.Model.modK; positivity)
  | (simp only [Loc.Model.modK]; positivity)
  | skip

theorem phiFrom_nonneg (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (T T' i : ℕ) : ∀ (l : List (D.host.E × ℕ)) (a : ℕ), 0 ≤ phiFrom δ M T T' i a l
  | [], _ => zero_le_one
  | (t, s) :: rest, a => mul_nonneg (pow_nonneg (nMod_nonneg δ M T T' a s t) _) (phiFrom_nonneg δ M T T' i rest (a + s))

theorem local_norm_nonneg_alt {c : ℝ} (hc : 0 ≤ c) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : 0 ≤ n0 c T T' w := by
  unfold n0
  positivity

theorem good_of_kind (hdet : ∀ w : Point D.host.E (D.R.rS + 1), Dmin w (D.R.rS + 1) ≠ 0) (T T' : ℕ)
    {w w' : Point D.host.E (D.R.rS + 1)} (hk : kind w = kind w') (hw : Gpt T T' w ≠ 0) : Gpt T T' w' ≠ 0 := by
  have hc : ∀ x : D.host.E, x ≠ 0 → D.conjF x ≠ 0 := fun x hx => (map_ne_zero D.conjF).2 hx
  unfold kind at hk
  by_cases h0 : Dmin w D.R.rS = 0
  · rw [if_pos h0] at hk
    by_cases h0' : Dmin w' D.R.rS = 0
    · unfold Gpt
      rw [h0', zero_mul, mul_zero, sub_zero]
      exact mul_ne_zero (hdet w') (hc _ (hdet w'))
    · rw [if_neg h0'] at hk; exact absurd hk (by simp)
  · rw [if_neg h0] at hk
    by_cases h0' : Dmin w' D.R.rS = 0
    · rw [if_pos h0'] at hk; exact absurd hk (by simp)
    · rw [if_neg h0'] at hk
      have hz : zetaOf w = zetaOf w' := Option.some.inj hk
      have e : ∀ v : Point D.host.E (D.R.rS + 1), Dmin v D.R.rS ≠ 0 →
          Gpt T T' v = Dmin v D.R.rS * D.conjF (Dmin v D.R.rS) *
            (zetaOf v * D.conjF (zetaOf v) - (T : D.host.E) * T') := by
        intro v hv
        unfold Gpt zetaOf
        rw [map_div₀]
        have := hc _ hv
        field_simp
      rw [e w h0] at hw
      rw [e w' h0', ← hz]
      exact mul_ne_zero (mul_ne_zero h0' (hc _ h0')) (right_ne_zero_of_mul hw)

end RowsLemmas

section RowsAbstract

open Finset
open scoped ComplexOrder

theorem phiA_nonneg (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (T T' : ℕ) {i : ℕ} (h : Point D.host.E i) : 0 ≤ phiA δ M T T' h := by
  unfold phiA
  first
  | exact phiFrom_nonneg _ _ _ _ _ _ _
  | skip

variable {P ι : Type}

theorem good_abstract (good : P → Prop) (K Kt Kg : P → P → ℂ) (c0 c : ι → P → ℂ) (R : Finset ι) (Dsup : ℝ)
    (n0 φ e : P → ℝ) (hn0 : ∀ w, 0 ≤ n0 w)
    (hKe : ∀ p q, K p q = (Dsup : ℂ) * Kt p q / ((φ p * φ q : ℝ) : ℂ))
    (hc : ∀ ρ w, c ρ w = c0 ρ w * ((e w : ℝ) : ℂ))
    (hde : ∀ ρ w, c0 ρ w ≠ 0 → (Real.sqrt (n0 w) * φ w)⁻¹ = e w)
    (h1 : ∀ (J : Type) [Fintype J] (w : J → P), (∀ x, good (w x)) →
      ((Dsup : ℂ) • (Matrix.of fun x y => Kt (w x) (w y)) -
        Matrix.of fun x y => Kg (w x) (w y) / ((Real.sqrt (n0 (w x) * n0 (w y)) : ℝ) : ℂ)).PosSemidef)
    (h2 : ∀ (J : Type) [Fintype J] (w : J → P), (∀ x, good (w x)) →
      (Matrix.of fun x y => Kg (w x) (w y) - ∑ ρ ∈ R, c0 ρ (w x) * star (c0 ρ (w y))).PosSemidef)
    (Xg : Finset P) (a : P → ℂ) (hX : ∀ p ∈ Xg, good p) :
    0 ≤ ∑ p ∈ Xg, ∑ q ∈ Xg, star (a p) * (K p q - ∑ ρ ∈ R, c ρ p * star (c ρ q)) * a q := by
  have hs : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => Complex.conj_ofReal r
  have hw : ∀ x : Xg, good x.1 := fun x => hX x.1 x.2
  have Q := quad_rows (fun x y : Xg => Kt x.1 y.1) (fun x y : Xg => Kg x.1 y.1)
    (fun x y : Xg => ∑ ρ ∈ R, c0 ρ x.1 * star (c0 ρ y.1)) Dsup (fun x : Xg => n0 x.1) (fun x : Xg => φ x.1)
    (fun x => hn0 x.1) (h1 Xg Subtype.val hw) (h2 Xg Subtype.val hw) (fun x : Xg => a x.1)
  have term : ∀ ρ p q, c ρ p * star (c ρ q) =
      c0 ρ p * star (c0 ρ q) * ((((Real.sqrt (n0 p) * φ p)⁻¹ * (Real.sqrt (n0 q) * φ q)⁻¹ : ℝ)) : ℂ) := by
    intro ρ p q
    by_cases hp : c0 ρ p = 0
    · simp [hc, hp]
    by_cases hq : c0 ρ q = 0
    · simp [hc, hq]
    rw [hc, hc, star_mul', hs, ← hde ρ p hp, ← hde ρ q hq]
    push_cast
    ring
  rw [← Finset.sum_coe_sort Xg]
  convert Q using 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_coe_sort Xg]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [hKe, Finset.sum_mul, term]

theorem dom_abstract (good : P → Prop) (K : P → P → ℂ) (c : ι → P → ℂ) (R : Finset ι)
    (hbad : ∀ ρ w, ¬ good w → c ρ w = 0) (hmix : ∀ p q, good p → ¬ good q → K p q = 0 ∧ K q p = 0) (hPSD : PSDK K)
    (hgood : ∀ (Xg : Finset P) (a : P → ℂ), (∀ p ∈ Xg, good p) →
      0 ≤ ∑ p ∈ Xg, ∑ q ∈ Xg, star (a p) * (K p q - ∑ ρ ∈ R, c ρ p * star (c ρ q)) * a q) :
    KLE (fun h h' => ∑ ρ ∈ R, c ρ h * star (c ρ h')) K := by
  classical
  unfold KLE PSDK at *
  intro X a
  show 0 ≤ ∑ p ∈ X, ∑ q ∈ X, star (a p) * (K p q - ∑ ρ ∈ R, c ρ p * star (c ρ q)) * a q
  have hs := sum_split X good (fun p q => star (a p) * (K p q - ∑ ρ ∈ R, c ρ p * star (c ρ q)) * a q)
    (fun p q hp hq => by
      have h0 : ∀ ρ, c ρ q = 0 := fun ρ => hbad ρ q hq
      simp [(hmix p q hp hq).1, h0])
    (fun p q hp hq => by
      have h0 : ∀ ρ, c ρ p = 0 := fun ρ => hbad ρ p hp
      simp [(hmix q p hq hp).2, h0])
  rw [hs]
  refine add_nonneg (hgood _ a fun p hp => (Finset.mem_filter.1 hp).2) ?_
  have hz : ∀ p ∈ X.filter (fun x => ¬ good x), ∀ q,
      star (a p) * (K p q - ∑ ρ ∈ R, c ρ p * star (c ρ q)) * a q = star (a p) * K p q * a q := by
    intro p hp q
    have h0 : ∀ ρ, c ρ p = 0 := fun ρ => hbad ρ p (Finset.mem_filter.1 hp).2
    simp [h0]
  have e2 : ∑ p ∈ X.filter (fun x => ¬ good x), ∑ q ∈ X.filter (fun x => ¬ good x),
      star (a p) * (K p q - ∑ ρ ∈ R, c ρ p * star (c ρ q)) * a q =
      ∑ p ∈ X.filter (fun x => ¬ good x), ∑ q ∈ X.filter (fun x => ¬ good x), star (a p) * K p q * a q :=
    Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q _ => hz p hp q
  rw [e2]
  exact hPSD _ a

variable {Tau : Type} [Fintype Tau] (HSv : Tau → Type) (ip : ∀ v, HSv v → HSv v → ℂ) (n : P → ℝ) (c c0 : ι → P → ℂ)
  (V : ∀ v, P → HSv v) (cW : ℝ)

theorem summ_abstract
    (hA1 : ∀ ρ w, c ρ w * ((Real.sqrt (n w) : ℝ) : ℂ) = c0 ρ w * (((Real.sqrt cW)⁻¹ : ℝ) : ℂ)) (ρ : ι)
    (hsum : Summable fun w => ‖c0 ρ w‖ * ∏ v, Real.sqrt (ip v (V v w) (V v w)).re) :
    Summable fun h => ‖c ρ h‖ * Real.sqrt (n h) * ∏ v, Real.sqrt (ip v (V v h) (V v h)).re := by
  refine (hsum.mul_left (Real.sqrt cW)⁻¹).congr fun h => ?_
  have e : ‖c ρ h * ((Real.sqrt (n h) : ℝ) : ℂ)‖ = ‖c0 ρ h * (((Real.sqrt cW)⁻¹ : ℝ) : ℂ)‖ := by
    rw [hA1]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))] at e
  rw [e]
  ring

theorem form_abstract (hcW : 0 < cW)
    (hA1 : ∀ ρ w, c ρ w * ((Real.sqrt (n w) : ℝ) : ℂ) = c0 ρ w * (((Real.sqrt cW)⁻¹ : ℝ) : ℂ)) :
    ∑' ρ, ENNReal.ofReal (∑' q : P × P, c0 ρ q.1 * star (c0 ρ q.2) * ∏ v, ip v (V v q.1) (V v q.2)).re =
      ENNReal.ofReal cW * SRowForm HSv ip n c V := by
  have hsq : (((Real.sqrt cW)⁻¹ : ℝ) : ℂ) * (((Real.sqrt cW)⁻¹ : ℝ) : ℂ) = ((cW⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hcW.le]
  have hs : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => Complex.conj_ofReal r
  have key : ∀ ρ (q : P × P), c ρ q.1 * star (c ρ q.2) * ((Real.sqrt (n q.1) * Real.sqrt (n q.2) : ℝ) : ℂ) =
      ((cW⁻¹ : ℝ) : ℂ) * (c0 ρ q.1 * star (c0 ρ q.2)) := by
    intro ρ q
    have e1 := hA1 ρ q.1
    have e2 := congrArg star (hA1 ρ q.2)
    rw [star_mul', star_mul', hs, hs] at e2
    rw [← hsq, Complex.ofReal_mul]
    calc c ρ q.1 * star (c ρ q.2) * ((Real.sqrt (n q.1) : ℂ) * (Real.sqrt (n q.2) : ℂ))
        = (c ρ q.1 * (Real.sqrt (n q.1) : ℂ)) * (star (c ρ q.2) * (Real.sqrt (n q.2) : ℂ)) := by ring
      _ = _ := by rw [e1, e2]; ring
  unfold SRowForm
  simp_rw [key, mul_assoc, tsum_mul_left, Complex.re_ofReal_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hcW.le),
    ENNReal.tsum_mul_left]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hcW.le, mul_inv_cancel₀ hcW.ne', ENNReal.ofReal_one, one_mul]

end RowsAbstract

theorem ptEntry_col {K : Type} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ j, j < (bs.map Prod.snd).sum → ∃ i, i < (bs.map Prod.snd).sum ∧ ∃ t : K, t ≠ 0 ∧
      ∀ j', ptEntry bs i j' = if j' = j then t else 0
  | [], _, j, hj => absurd hj (by simp)
  | (t, s) :: rest, h, j, hj => by
    simp only [List.map_cons, List.sum_cons] at hj ⊢
    by_cases hjs : j < s
    · refine ⟨s - 1 - j, by omega, t, (h (t, s) (by simp)).1, fun j' => ?_⟩
      simp only [ptEntry]
      by_cases hj' : j' = j
      · subst hj'
        rw [if_pos ⟨by omega, hjs⟩, if_pos (by omega), if_pos rfl]
      · rw [if_neg hj']
        by_cases h2 : j' < s
        · rw [if_pos ⟨by omega, h2⟩, if_neg (by omega)]
        · rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => by omega)]
    · obtain ⟨i0, hi0, t0, ht0, h0⟩ := ptEntry_col rest (fun b hb => h b (by simp [hb])) (j - s) (by omega)
      refine ⟨i0 + s, by omega, t0, ht0, fun j' => ?_⟩
      simp only [ptEntry]
      rw [if_neg (fun hh => by omega)]
      by_cases h2 : s ≤ j'
      · rw [if_pos ⟨by omega, h2⟩, Nat.add_sub_cancel, h0]
        by_cases hj' : j' = j
        · rw [if_pos (by omega), if_pos hj']
        · rw [if_neg (by omega), if_neg hj']
      · rw [if_neg (fun hh => h2 hh.2), if_neg (by omega)]

theorem ptMat_det_ne {K : Type} [Field K] {n : ℕ} (p : Point K n) : (ptMat p).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hv
  funext j
  obtain ⟨i, hi, t, ht, hcol⟩ := ptEntry_col p.1 p.2.1 j.val (by rw [p.2.2]; exact j.2)
  have h1 := congrFun h0 ⟨i, by rw [← p.2.2]; exact hi⟩
  simp only [Matrix.mulVec, dotProduct, ptMat, hcol, Pi.zero_apply] at h1
  rw [Finset.sum_eq_single j (fun b _ hb => by rw [if_neg (fun hh => hb (Fin.ext hh)), zero_mul])
    (fun hh => absurd (Finset.mem_univ j) hh), if_pos rfl] at h1
  exact (mul_eq_zero.1 h1).resolve_left ht

theorem Dmin_top_ne (w : Point D.host.E (D.R.rS + 1)) : LocalSplitGroups.Dmin w (D.R.rS + 1) ≠ 0 := by
  unfold LocalSplitGroups.Dmin
  rw [dif_pos le_rfl]
  have : (ptMat w).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))) = ptMat w := by
    ext a b; rfl
  rw [this]
  exact ptMat_det_ne w

section RowsStep

open Finset
open scoped ComplexOrder

variable (D) (large₂ : SizeData₂ D) (X : TermTie D) (Cw : ℝ) (Y : ∀ u u', LoopTie D large₂ X u u' Cw) (Z : TermLocs D X)
  (cN : D.what₂.Word → D.what₂.Word → ℝ) (Vm : ValMap D.R.k D.R.rS)

def ColumnDecomposition : Prop :=
  ∀ (u u' : D.what₂.Word), u ≠ u' → ∀ (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (f : ∀ v, MatKR D.R.k D.R.rS → ((localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp)),
    IsAmpCoef (Y u u') hT hT' f →
  ∃ (ι : Type) (_ : Countable ι) (c0 : ι → Point D.host.E (D.R.rS + 1) → ℂ),
    (∀ ρ w, c0 ρ w ≠ 0 → Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 ∧ TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) ∧
      0 < ptWeightG D (rhoReal D) (Tr D u) (Tr D u') w.1) ∧
    (∀ (R : Finset ι) (J : Type) [Fintype J] (w : J → Point D.host.E (D.R.rS + 1)),
      (∀ x, Gpt (D.mem u).A.T (D.mem u').A.T (w x) ≠ 0) →
      (Matrix.of fun x y => Kgs D.s u u' (w x) (w y) - ∑ ρ ∈ R, c0 ρ (w x) * star (c0 ρ (w y))).PosSemidef) ∧
    (∀ ρ, Summable fun w : Point D.host.E (D.R.rS + 1) => ‖c0 ρ w‖ *
      ∏ v, Real.sqrt (hsInner (Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v w.1))
        (Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v w.1))).re) ∧
    ENNReal.ofReal (∑' q, formTerm (Y u u') hT hT' Vm f q).re ≤
      ∑' ρ, ENNReal.ofReal (∑' q : Point D.host.E (D.R.rS + 1) × Point D.host.E (D.R.rS + 1),
        c0 ρ q.1 * star (c0 ρ q.2) *
          ∏ v, hsInner (Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v q.1.1))
            (Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v q.2.1))).re

theorem column_bound_of_decomposition (h : ColumnDecomposition D large₂ X Cw Y Vm) : ColumnDominationBound D large₂ X Cw Y Z cN Vm := by
  intro u u' hne hT hT' f hf δ M hA hmd hG2 hcnt ϖ Dsup hϖ hD0 hDb L Kd hL hPSD hK cW hcW hid
  obtain ⟨ι, hι, c0, hsupp, hdom, hsum, hform⟩ := h u u' hne hT hT' f hf
  have hρ : L.ρ = rhoReal D := rho_eq hL
  rw [hρ] at hid ⊢
  obtain ⟨n, hn⟩ : ∃ n : Point D.host.E (D.R.rS + 1) → ℝ,
      n = fun h => ptWeightG D (rhoReal D) (Tr D u) (Tr D u') h.1 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Point D.host.E (D.R.rS + 1) → ℝ, e = fun w => (Real.sqrt cW * Real.sqrt (n w))⁻¹ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ι → Point D.host.E (D.R.rS + 1) → ℂ, c = fun ρ w => c0 ρ w * ((e w : ℝ) : ℂ) := ⟨_, rfl⟩
  have hc' : ∀ ρ w, c ρ w = c0 ρ w * ((e w : ℝ) : ℂ) := fun ρ w => by rw [hc]
  have he' : ∀ w, e w = (Real.sqrt cW * Real.sqrt (n w))⁻¹ := fun w => by rw [he]
  have hn' : ∀ w : Point D.host.E (D.R.rS + 1), n w = ptWeightG D (rhoReal D) (Tr D u) (Tr D u') w.1 := fun w => by rw [hn]
  have hc0 : ∀ ρ w, c0 ρ w = 0 → c ρ w = 0 := fun ρ w h0 => by rw [hc', h0, zero_mul]
  have hA1 : ∀ ρ w, c ρ w * ((Real.sqrt (n w) : ℝ) : ℂ) = c0 ρ w * (((Real.sqrt cW)⁻¹ : ℝ) : ℂ) := by
    intro ρ w
    by_cases h0 : c0 ρ w = 0
    · rw [hc0 ρ w h0, h0, zero_mul, zero_mul]
    · have hn0 : 0 < Real.sqrt (n w) := Real.sqrt_pos.2 (by rw [hn' w]; exact (hsupp ρ w h0).2.2)
      rw [hc', he' w, mul_assoc, ← Complex.ofReal_mul, mul_inv, mul_assoc, inv_mul_cancel₀ hn0.ne', mul_one]
  have hde : ∀ ρ w, c0 ρ w ≠ 0 →
      (Real.sqrt (n0 (cN u u') (D.mem u).A.T (D.mem u').A.T w) * phiA δ M (D.mem u).A.T (D.mem u').A.T w)⁻¹ = e w := by
    intro ρ w hw
    have e1 := congrArg Real.sqrt (hid w (hsupp ρ w hw).2.1)
    rw [Real.sqrt_mul (local_norm_nonneg_alt hcnt.1.le _ _ _), Real.sqrt_sq (phiA_nonneg δ M _ _ _), Real.sqrt_mul hcW.le] at e1
    rw [he' w, hn' w, e1]
  have hKe : ∀ p q, Kd.K (D.R.rS + 1) p q = (Dsup : ℂ) * KtopG M δ (D.mem u).A.T (D.mem u').A.T p q /
      ((phiA δ M (D.mem u).A.T (D.mem u').A.T p * phiA δ M (D.mem u).A.T (D.mem u').A.T q : ℝ) : ℂ) := by
    intro p q
    rw [hK]
    simp [KA, Kglob]
  have hmix : ∀ p q, Gpt (D.mem u).A.T (D.mem u').A.T p ≠ 0 → ¬ Gpt (D.mem u).A.T (D.mem u').A.T q ≠ 0 →
      Kd.K (D.R.rS + 1) p q = 0 ∧ Kd.K (D.R.rS + 1) q p = 0 := by
    intro p q hp hq
    have hk : kind p ≠ kind q := fun hk => hq (good_of_kind Dmin_top_ne _ _ hk hp)
    rw [hKe, hKe]
    unfold KtopG
    rw [if_neg hk, if_neg (Ne.symm hk)]
    simp
  have hbad : ∀ ρ w, ¬ Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 → c ρ w = 0 := fun ρ w hw =>
    hc0 ρ w (by_contra fun h0 => hw (hsupp ρ w h0).1)
  refine ⟨ι, hι, c, ⟨fun R => ?_, fun ρ => ?_⟩, ?_⟩
  · exact dom_abstract (fun w => Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0) _ c R hbad hmix hPSD
      (good_abstract (fun w => Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0) _
        (KtopG M δ (D.mem u).A.T (D.mem u').A.T) (Kgs D.s u u') c0 c R Dsup
        (n0 (cN u u') (D.mem u).A.T (D.mem u').A.T) (phiA δ M (D.mem u).A.T (D.mem u').A.T) e
        (fun w => local_norm_nonneg_alt hcnt.1.le _ _ _) hKe hc' hde
        (fun J _ w hw => (hG2 u u' hmd ϖ hϖ Dsup hD0 hDb J w hw).2) (fun J _ w hw => hdom R J w hw))
  · have := summ_abstract (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsInner) n c c0
      (fun v h => Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v h.1)) cW hA1 ρ (hsum ρ)
    rw [hn] at this
    exact this
  · have := form_abstract (fun v => (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wq →L[ℂ] (localBesselDatumAtRealPlace (Y u u') hT hT' v).Wp) (fun _ => hsInner) n c c0
      (fun v h => Vm.V (localBesselDatumAtRealPlace (Y u u') hT hT' v) (f v) (locBlocks D (rhoReal D) v h.1)) cW hcW hA1
    rw [hn] at this
    exact hform.trans (le_of_eq this)

end RowsStep

section Dens

variable (D) (X : TermTie D) (Z : TermLocs D X)

def PrimeSumStep (Ce : ℝ) : Prop :=
  Summable (fun p : PlF D => (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2))) ∧
  Real.exp (4 * ∑' p : PlF D, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2))) ≤ 2 ∧
  Real.exp (4 * ∑' p : PlF D, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2))) ≤ 1 + eSum D Ce

theorem density_bound_of_local_density {Ce : ℝ} (hk : 4 * D.R.rS + 8 ≤ D.R.k) (hd : ExactLocalDensityAllModels D) (hp : PrimeSumStep D Ce) : DensityBound D X Z Ce := by
  intro δ M hA u u'
  have hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := fun p => by
    have := (hA p).1.loc
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ using hex
  have hb0 : ∀ p : PlF D, 0 ≤ (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2)) :=
    fun p => zpow_nonneg (Nat.cast_nonneg _) _
  have hS0 : 0 ≤ 4 * ∑' p : PlF D, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2)) :=
    mul_nonneg (by norm_num) (tsum_nonneg hb0)
  refine ⟨ϖ, _, hϖ, Real.one_le_exp hS0, hp.2.1, hp.2.2, fun γ hg hG => ?_⟩
  have hGt := ((Z δ M hA u u').G_pt γ).2 hG
  have hloc := ((Z δ M hA u u').generic_iff γ hGt.1).1 hg
  unfold densT
  refine tprod_le_of_prod_le' (Real.one_le_exp hS0) fun s => ?_
  calc _ ≤ ∏ p ∈ s, Real.exp (4 * (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2))) :=
        Finset.prod_le_prod
          (fun p _ => div_nonneg (Nat.cast_nonneg _) (zpow_nonneg (Nat.cast_nonneg _) _))
          (fun p _ => (hd hk _ _ (M p) (hA p).1 (ϖ p) (hϖ p) _ ((Z δ M hA u u').H p) ((Z δ M hA u u').rank p)
            ((Z δ M hA u u').loc γ p) (hloc p)).1)
    _ = Real.exp (4 * ∑ p ∈ s, (Nat.card 𝓀[(D.s.atP p).Fp] : ℝ) ^ (-((D.R.k : ℤ) - 2 * D.R.rS - 2))) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hp.1.sum_le_tsum s fun p _ => hb0 p) (by norm_num))

end Dens

theorem theorem_S_of_refined_estimates {large₂ : SizeData₂ D} {X : TermTie D} {Cw : ℝ} {Y : ∀ u u', LoopTie D large₂ X u u' Cw} {Z : TermLocs D X}
    {cN : D.what₂.Word → D.what₂.Word → ℝ} {Vm : ValMap D.R.k D.R.rS}
    {Ca Cq C0 C' Cl Cg cb Cu cT CT CA CA' Ce₀ Ce : ℝ}
    (hCA : 0 ≤ CA) (hCl : 8 ≤ Cl) (hm8 : (8 : ℝ) ≤ D.R.m) (hCAm : 128 * |CA| ≤ D.R.m)
    (s1 : AmplitudeIsBesselCoefficient D large₂ X Cw Y) (s3 : PrimeSumStep D Ce₀) (s4 : ColumnDecomposition D large₂ X Cw Y Vm) (s5 : ParamsBound D large₂ X Cw Y Z cN)
    (hAl : (1 + eSum D Ce₀) * Real.exp (8 * qS D) ≤ 1 + eSum D Ce) :
    IntegralityFromMetric D large₂ X Cw Y Z cN Vm Ca Cq C0 C' Cl Cg cb Cu cT CT CA CA' Ce := by
  unfold IntegralityFromMetric
  intro hT hA hH
  have hA' := hA
  unfold Adm1 at hA'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hd, -, -, -, -, -, -, -⟩ := hA'
  exact theorem_S_of_column_estimates hCA hCl hm8 hCAm s1 (density_bound_of_local_density D X Z (k_ge_of_hyp hH) hd s3)
    (column_bound_of_decomposition D large₂ X Cw Y Z cN Vm s4) (constant_bound_of_massDataBound D large₂ X Cw Y Z cN s5) hAl hT hA hH

theorem family_theorem_S_of_estimates {eps : ℝ} (Fm : FamP eps) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Cw : ℝ)
    (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) u u', LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' Cw)
    (Z : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), TermLocs (Fm.D x i) (X x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ) (Vm : ∀ k r, ValMap k r)
    {C0 Cg cb Cu cT CT Ca Cq CA CA' Ce₀ Ce : ℝ} (hCA : 0 ≤ CA) (hCl : 8 ≤ sCl Fm)
    (S : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      hyp (Fm.D x i) (Fm.L x i) C0 (sC' Fm) (sCl Fm) Cg cb Cu cT CT →
        AmplitudeIsBesselCoefficient (Fm.D x i) (Fm.L x i) (X x hx i) Cw (Y x hx i) ∧ PrimeSumStep (Fm.D x i) Ce₀ ∧ (1 + eSum (Fm.D x i) Ce₀) * Real.exp (8 * qS (Fm.D x i)) ≤ 1 + eSum (Fm.D x i) Ce ∧
        ColumnDecomposition (Fm.D x i) (Fm.L x i) (X x hx i) Cw (Y x hx i) (Vm _ _) ∧
        ParamsBound (Fm.D x i) (Fm.L x i) (X x hx i) Cw (Y x hx i) (Z x hx i) (cN x i)) :
    PeriodFamilyStatement Fm X Cw Y Z cN Vm C0 Cg cb Cu cT CT Ca Cq CA CA' Ce := by
  intro _ hA
  obtain ⟨_, _, _, _, _, _, _, _, _, hThA, hDens, ⟨xG, hG⟩, ⟨xC, hC⟩, ⟨xF, hF⟩, ⟨xA, hAr⟩, _⟩ := hA
  obtain ⟨xS, hS⟩ := S
  refine family_theorem_S_of_pointwise (Ce₀ := Ce₀) Fm hCA hCl
    ⟨max (max xG xC) (max (max xF xA) xS), fun x hx hx1 i hH => ?_⟩
  have h1 : xG ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have h2 : xC ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have h3 : xF ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have h4 : xA ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have h5 : xS ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨s1, s3, hAl, s4, s5⟩ := hS x h5 hx1 i hH
  exact ⟨X x hx1 i, Cw, Y x hx1 i, Z x hx1 i, cN x i, Vm _ _, hF x h3 i hx1 hH, hThA x i, hG x h1 i hx1, hC x h2 i hx1,
    hAr x h4 i hH, s1, density_bound_of_local_density _ _ _ (k_ge_of_hyp hH) (hDens x i) s3, column_bound_of_decomposition _ _ _ _ _ _ _ _ s4, constant_bound_of_massDataBound _ _ _ _ _ _ _ s5,
    hAl⟩

end Formalism.MainNotions.BridgeLemma

end
