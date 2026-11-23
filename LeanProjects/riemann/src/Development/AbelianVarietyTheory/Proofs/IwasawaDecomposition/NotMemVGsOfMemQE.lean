import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNormalFormLattice
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeNormalFormCoordinates
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedBoxSumAtPrimeEqOfBoundedSchwartz
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingBoundedIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentRadicalsActAffineUnfoldingSpaces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnfoldingAffineSpaceMemIffIntrinsic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParahoricLeIntegralGl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqOfSplitFactor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleRepresentativesFiniteLevelCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormModuloUnipotentSemidirectStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLatticeNormalFormOfBetweenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnLevelAtTwistPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnSymmetricLevelAtTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepDatumBoundedAtTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineEigenvalueEqOneOfBoxSumNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingCharArgMulLeftUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneDetEqOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupModTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionStepZeroTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterStepZeroTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelStepZeroAtTwistPrimeFullStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjConjLevelLeIntegralGLAtTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeNormalFormViaMatrixStatement

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm (NF)
open GlobalTheory.Proof.NormalFormAtPrime

section General

theorem exists_reps {G ι : Type} [Finite ι] (s : Setoid G) (T : Set G) (Good : G → Prop) (f : G → ι)
    (hf : ∀ h ∈ T, ∀ h' ∈ T, f h = f h' → s h h') (hg : ∀ h ∈ T, ∃ h', s h' h ∧ Good h') :
    ∃ F : Set G, F.Finite ∧ (∀ h ∈ F, Good h) ∧ (∀ h ∈ F, ∀ h' ∈ F, s h h' → h = h') ∧ ∀ h ∈ T, ∃ h' ∈ F, s h' h := by
  classical
  have hfin : (Quotient.mk s '' T).Finite := by
    refine (Set.finite_range fun i : ι =>
      if h : ∃ a ∈ T, f a = i then some (Quotient.mk s h.choose) else none).preimage
        (Option.some_injective _).injOn |>.subset ?_
    rintro _ ⟨a, ha, rfl⟩
    have h : ∃ b ∈ T, f b = f a := ⟨a, ha, rfl⟩
    refine ⟨f a, ?_⟩
    simp only [dif_pos h]
    exact congrArg some (Quotient.sound (hf _ h.choose_spec.1 _ ha h.choose_spec.2))
  have key : ∀ c : Quotient.mk s '' T, ∃ h', Quotient.mk s h' = c.1 ∧ Good h' := by
    rintro ⟨_, a, ha, rfl⟩
    obtain ⟨h', h1, h2⟩ := hg a ha
    exact ⟨h', Quotient.sound h1, h2⟩
  choose ρ h1 h2 using key
  have := hfin.to_subtype
  refine ⟨Set.range ρ, Set.finite_range _, ?_, ?_, fun h hh => ⟨_, ⟨⟨_, h, hh, rfl⟩, rfl⟩, Quotient.exact (h1 _)⟩⟩
  · rintro _ ⟨c, rfl⟩
    exact h2 c
  · rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩ h
    rw [Subtype.ext ((h1 c).symm.trans ((Quotient.sound h).trans (h1 c')))]

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem intHom_pow_smul {a b : ℕ} {y : (Fin a → E) →ₗ[E] (Fin b → E)} (k : ℕ) (hy : IntHom P y) :
    IntHom P (((qOf P : E) ^ k) • y) := fun v hv l => intAt_pow_mul k (hy v hv l)

theorem homBdd_mono {N N' a b : ℕ} (h : N ≤ N') {Psi : Loc.SF E K a b} (H : HomBdd P N Psi) : HomBdd P N' Psi := by
  refine ⟨fun x hx => (H.1 x hx).pow_mono h, fun x y hy => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_smul]
  exact H.2 x _ (intHom_pow_smul k hy)

theorem homBdd_add {N B a b : ℕ} (h : N ≤ B) {Psi : Loc.SF E K a b} (H : HomBdd P N Psi) (x y : (Fin a → E) →ₗ[E] (Fin b → E))
    (hy : IntHom P (((qOf P : E) ^ B)⁻¹ • y)) : Psi (x + y) = Psi x := by
  have := (homBdd_mono h H).2 x _ hy
  rwa [smul_inv_smul₀ (pow_ne_zero _ (qOf_ne_zero P))] at this

open GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz in
theorem integrand_funBdd {n' c' n c : ℕ} {psi : E → K} {D N : ℕ} {Psi : Loc.SF E K (n' + c') (n + c)}
    (hpsi : CharTo P D psi) (hPsi : HomBdd P N Psi) (hch : ∀ x, Psi x ≠ 0 → IntAt P ((qOf P : E) ^ D * Loc.chArg x))
    (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : FunBdd P N (integrand psi Psi xj) := by
  refine ⟨fun t ht i => ?_, fun t u hu => ?_⟩
  · obtain ⟨⟨l, s⟩, hf⟩ := i
    have h := (intHom_iff _).1 (hPsi.1 _ (left_ne_zero_of_mul ht)) s l
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, linearMap_unfolding_apply_single, dif_pos hf] at h
    exact h
  · unfold integrand
    rw [periodXX1_add_smul, hPsi.2 _ _ (intHom_freeMap hu)]
    by_cases h0 : Psi (Loc.xx1 xj t) = 0
    · rw [h0, zero_mul, zero_mul]
    · have hb : IntAt P (-((qOf P : E) ^ N * Loc.chArg (freeMap u))) :=
        IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (intAt_pow_mul N (GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.intAt_chArg (intHom_freeMap hu)))
      have ha : IntAt P ((qOf P : E) ^ D * -Loc.chArg (Loc.xx1 xj t)) := by
        rw [mul_neg]
        exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (hch _ h0)
      rw [chArg_add, chArg_smul, neg_add, hpsi.1 _ _ ha (intAt_pow_mul D hb), hpsi.2 _ hb, mul_one]

theorem psi_mul_neg {psi : E → K} {D : ℕ} (hpsi : CharTo P D psi) {a : E} (ha : IntAt P ((qOf P : E) ^ D * a)) :
    psi a * psi (-a) = 1 := by
  rw [← hpsi.1 a (-a) ha (by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg ha), add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)]

theorem intHom_joinCol {n' c' n c : ℕ} {x₀ : HomE E n' n} {y : Sp E n} (hx : IntHom P x₀) (hy : IntV P y) :
    IntHom P (joinCol (c' := c') (c := c) x₀ y) := by
  intro v hv l
  have h1 : IntV P (x₀ (LinearMap.funLeft E E (Fin.castAdd c') v) + atNL E (n' + c') n' v • y) := by
    refine (hx _ fun i => hv _).add (IntV.smul ?_ hy)
    unfold atNL
    split_ifs
    · exact hv _
    · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  change IntAt P (Loc.inX E n c (x₀ (LinearMap.funLeft E E (Fin.castAdd c') v) + atNL E (n' + c') n' v • y) l)
  rw [inX_apply]
  split_ifs
  · exact h1 _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem of_intHom_joinCol {n' c' n c : ℕ} (hc' : 1 ≤ c') {x₀ : HomE E n' n} {y : Sp E n} {u : E}
    (h : IntHom P (u • joinCol (c' := c') (c := c) x₀ y)) : IntHom P (u • x₀) ∧ IntV P (u • y) := by
  have hn : n' < n' + c' := by omega
  refine ⟨fun v hv l => ?_, fun l => ?_⟩
  · have h1 : IntV P (Loc.inX E n' c' v) := fun i => by
      rw [inX_apply]
      split_ifs
      · exact hv _
      · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
    have h2 := h _ h1 (Fin.castAdd c l)
    have e : atNL E (n' + c') n' (Loc.inX E n' c' v) = 0 := by
      unfold atNL
      rw [dif_pos hn, LinearMap.proj_apply, inX_apply, dif_neg (lt_irrefl _)]
    change IntAt P (u * Loc.inX E n c (x₀ (LinearMap.funLeft E E (Fin.castAdd c') (Loc.inX E n' c' v)) +
      atNL E (n' + c') n' (Loc.inX E n' c' v) • y) (Fin.castAdd c l)) at h2
    rwa [inX_castAdd, e, zero_smul, add_zero, LastSteps.funLeft_inX] at h2
  · have h2 := h _ (intV_single P ⟨n', hn⟩) (Fin.castAdd c l)
    have e : atNL E (n' + c') n' (Pi.single ⟨n', hn⟩ 1) = 1 := by
      unfold atNL
      rw [dif_pos hn, LinearMap.proj_apply, Pi.single_eq_same]
    have e' : LinearMap.funLeft E E (Fin.castAdd c') (Pi.single (⟨n', hn⟩ : Fin (n' + c')) (1 : E)) = 0 := by
      funext i
      refine Pi.single_eq_of_ne (fun h => ?_) _
      have := congrArg Fin.val h
      have := i.2
      simp at *
      omega
    change IntAt P (u * Loc.inX E n c (x₀ (LinearMap.funLeft E E (Fin.castAdd c') (Pi.single ⟨n', hn⟩ 1)) +
      atNL E (n' + c') n' (Pi.single ⟨n', hn⟩ 1) • y) (Fin.castAdd c l)) at h2
    rwa [inX_castAdd, e, e', map_zero, zero_add, one_smul] at h2

end General

section Local

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {P : rowSG Pr sel mu}

theorem charTo (hc : cst.Ok) (P : rowSG Pr sel mu) : CharTo P.1 (cst.D P) (cst.psi P) := ⟨hc.psi_add P, hc.psi_int P⟩

theorem omPhi_bdd' (hc : cst.Ok) (hD : P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P) {i : ℕ} (hi : i + 2 ≤ R.m)
    {hal : AutY X R i} {h : AutY X R (i + 1)} (h1 : admitted Pr i P.1 hal) (h2 : admitted Pr (i + 1) P.1 h) :
    HomBdd P.1 R.m (omPhi Ch sel mu cst i P hal h) ∧
      ∀ x, omPhi Ch sel mu cst i P hal h x ≠ 0 → IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * Loc.chArg x) := by
  by_cases hP : P.1 ∈ Pr.vGs
  · obtain ⟨a, b⟩ := GlobalTheory.T.stepDatum_bounded_at_typePrime Ch sel mu cst i P hi hP hal h (h1.1 hP) (h2.1 hP)
    exact ⟨a, fun x hx => intAt_pow_mono (hc.D_pos P) (by rw [pow_one]; exact b x hx)⟩
  · have a := omPhi_bdd (Ch := Ch) (cst := cst) hP (h1.2 hP) (h2.2 hP)
    have := hD hP
    exact ⟨homBdd_mono (by omega) a, fun x hx => intAt_pow_mono (by omega) (QNormal.intAt_chArg (a.1 x hx))⟩

theorem conj_mem {j : ℕ} {h r : AutY X R j} (hr : r ∈ CAt sel mu cst j P h) : h⁻¹ * r * h ∈ Jat (Pr := Pr) cst.sharp j P.1 := by
  have hκ : (MulAut.conj h⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) cst.sharp j P.1 := hr.2
  simpa using hκ

theorem intAt_n1Arg_of_mem (hc : cst.Ok) (hD : P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P) {j : ℕ} (hj : j < R.m)
    {h r : AutY X R j} (hh : admitted Pr j P.1 h) (hr : r ∈ CAt sel mu cst j P h) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * Loc.n1Arg r) := by
  have hκ := conj_mem hr
  unfold Jat at hκ
  by_cases hP : P.1 ∈ Pr.vGs
  · have hs := hh.1 hP
    unfold lamYat at hs
    rw [if_pos hP] at hs hκ
    have hκ' : h⁻¹ * r * h ∈ stabL X.E _ (LocE.lamY P.1 (qOf P.1) (R.N j) (cOf R j) fun i => i + 1) := by
      split_ifs at hκ
      · exact hκ.1
      · exact hκ.1
    have hr' := mul_mem (mul_mem hs hκ') (inv_mem hs)
    rw [show h * (h⁻¹ * r * h) * h⁻¹ = r by group] at hr'
    exact intAt_pow_mono (hc.D_pos P) (by rw [pow_one]; exact LevFin.intAt_n1Arg_G (qOf_ne_zero _) r hr')
  · rw [if_neg hP] at hκ
    have hb := hh.2 hP
    have := hD hP
    refine intAt_pow_mono (A := j) (by omega) (GO.ChRoot.intAt_n1Arg _ r fun x hx => ?_)
    have h1 := hb.2 _ ((mem_stdAt_iff _).1 ((hκ.1 _).2 ((mem_stdAt_iff _).2 (hb.1 x ((mem_stdAt_iff _).1 hx)))))
    have h2 : h ((h⁻¹ * r * h) (h⁻¹ x)) = r x := by
      change (h * (h⁻¹ * r * h) * h⁻¹) x = r x
      congr 1
      group
    rw [← h2]
    exact (mem_stdAt_iff _).2 h1

theorem lamRow_mul (hs : cst.sharp = true) {j : ℕ} (hj : j < R.m) {g g' : AutY X R j}
    (hg : g ∈ Jat (Pr := Pr) cst.sharp j P.1) (hg' : g' ∈ Jat (Pr := Pr) cst.sharp j P.1) :
    lamRow Ch mu cst.sharp j P.1 (g * g').toLinearMap =
      lamRow Ch mu cst.sharp j P.1 g.toLinearMap * lamRow Ch mu cst.sharp j P.1 g'.toLinearMap := by
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [hs] at hg hg' ⊢
    exact GlobalTheory.T.rowType_mul_on_symmetricLevel_at_typePrime Ch mu j P.1 hj hP g hg g' hg'
  · exact GlobalTheory.T.rowType_mul_on_level_at_twistPrime Ch mu _ j P.1 hP g hg g' hg'

theorem lamRow_one {j : ℕ} (hj : j < R.m) : lamRow Ch mu cst.sharp j P.1 (1 : AutY X R j).toLinearMap = 1 := by
  have := GlobalTheory.T.rowType_one_add_prime_smul_eq_one Ch mu cst.sharp j P.1 hj 0 fun _ _ => zero_mem _
  rwa [smul_zero, add_zero] at this

theorem chiMul (hc : cst.Ok) (hs : cst.sharp = true) (hD : P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P) {j : ℕ} (hj : j < R.m)
    {h : AutY X R j} (hh : admitted Pr j P.1 h) : ChiMul Ch sel mu cst j P h := by
  refine ⟨fun r hr => mul_ne_zero (inv_ne_zero ?_) ?_, fun r hr r' hr' => ?_⟩
  · exact left_ne_zero_of_mul ((psi_mul_neg (charTo hc P) (intAt_n1Arg_of_mem hc hD hj hh hr)).trans_ne one_ne_zero)
  · have := lamRow_mul (Ch := Ch) hs hj (conj_mem hr) (inv_mem (conj_mem hr))
    rw [mul_inv_cancel, lamRow_one hj] at this
    exact left_ne_zero_of_mul (this.symm.trans_ne one_ne_zero)
  · unfold chiInv
    rw [unipotentCharacterArgument_mul_stabilizer hr.1.1 hr'.1.1, hc.psi_add P _ _ (intAt_n1Arg_of_mem hc hD hj hh hr) (intAt_n1Arg_of_mem hc hD hj hh hr'),
      show h⁻¹ * (r * r') * h = (h⁻¹ * r * h) * (h⁻¹ * r' * h) by group, lamRow_mul hs hj (conj_mem hr) (conj_mem hr')]
    ring

theorem chiTriv_last {j : ℕ} (hj : cOf R j = 0) {h : AutY X R j} (H : ChiMul Ch sel mu cst j P h) :
    ChiTriv Ch sel mu cst j P h := by
  intro r _ hr
  obtain rfl : r = 1 := by
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ Loc.Ufl X.E (R.N j) (cOf R j) 0 := mem_Ufl.2 fun l hl => by
      have := l.2
      omega
    rw [← inX_of_mem_Ufl hv]
    exact hr _
  have h1 := H.2 1 (one_mem _) 1 (one_mem _)
  rw [mul_one] at h1
  exact (mul_eq_left₀ (H.1 1 (one_mem _))).1 h1.symm

theorem muAt_one (i : ℕ) : muAt Ch sel mu cst i P 1 = 1 := by
  have h1 : IsUnit (redP P.1 (1 : X.E)) := by
    rw [TopStep.reduction_one₂]
    exact isUnit_one
  unfold muAt
  rw [LastSteps.locChar_unit _ _ h1]
  unfold LocE.unitV
  rw [dif_pos h1, show h1.unit = 1 from Units.ext (TopStep.reduction_one₂), map_one, Units.val_one]

theorem chiTriv_mid (hc : cst.Ok) (hs : cst.sharp = true) (hd : DegOneUnram P.1)
    (hD : P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P) {i : ℕ} (hi : i + 3 ≤ R.m)
    {hal : AutY X R i} {h : AutY X R (i + 1)} (h1 : admitted Pr i P.1 hal) (h2 : admitted Pr (i + 1) P.1 h)
    (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h) : ChiTriv Ch sel mu cst (i + 1) P h := by
  intro r hr hfix
  have hκ := conj_mem hr
  have hdet : LinearEquiv.det (h⁻¹ * r * h) = 1 := by
    rw [map_mul, map_mul, GlobalTheory.T.norm_one_det_eq_one X.E _ _ r ⟨hr.1, hfix⟩, map_inv, mul_one, inv_mul_cancel]
  have hphi : ∀ x, PhiAt Ch mu cst.sharp i P.1 ((h⁻¹ * r * h).toLinearMap ∘ₗ x) =
      lamRow Ch mu cst.sharp (i + 1) P.1 (h⁻¹ * r * h).toLinearMap * PhiAt Ch mu cst.sharp i P.1 x := by
    intro x
    have : PhiAt Ch mu cst.sharp i P.1 ((h⁻¹ * r * h).toLinearMap ∘ₗ x) *
        muAt Ch sel mu cst i P ((LinearEquiv.det (h⁻¹ * r * h) : X.Eˣ) : X.E) =
        lamRow Ch mu cst.sharp (i + 1) P.1 (h⁻¹ * r * h).toLinearMap * PhiAt Ch mu cst.sharp i P.1 x :=
      GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst _ (by omega) P hκ x
    rwa [hdet, Units.val_one, muAt_one, mul_one] at this
  have hom : ∀ x, omPhi Ch sel mu cst i P hal h (r.toLinearMap ∘ₗ x) =
      lamRow Ch mu cst.sharp (i + 1) P.1 (h⁻¹ * r * h).toLinearMap * omPhi Ch sel mu cst i P hal h x := by
    intro x
    rw [omPhi_eq, omPhi_eq, mul_left_comm, ← hphi]
    congr 2
    refine LinearMap.ext fun v => ?_
    change h.symm (r (x (hal v))) = h.symm (r (h (h.symm (x (hal v)))))
    rw [h.apply_symm_apply]
  obtain ⟨b1, b2⟩ := omPhi_bdd' (Ch := Ch) hc hD (by omega) h1 h2
  obtain ⟨A₀, B₀, H⟩ := (localUnfoldingNonvanishing_iff_eventuallyNonzero Ch sel mu cst i P hal h).1 H
  obtain ⟨xj, hx⟩ := Function.ne_iff.1 (H (max A₀ R.m) (max B₀ R.m) (le_max_left _ _) (le_max_left _ _))
  have I := integrand_funBdd (charTo hc P) b1 b2 xj
  have hc1 : 1 ≤ cOf R (i + 1) := by unfold cOf; omega
  have hc2 : cOf R i = cOf R (i + 1) + 1 := by unfold cOf; omega
  obtain ⟨xj', T, b, hT⟩ := GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic X.E _ _ _ _ hc1 hc2 r hr.1 1 (one_mem _) xj
  obtain rfl : xj' = xj := by
    refine LinearMap.ext fun v => inX_injective (c := cOf R (i + 1)) ?_
    have := LinearMap.congr_fun (hT 0) (Loc.inX X.E _ _ v)
    rw [unfoldingAffinePointMap_apply_inclusion] at this
    rw [← this]
    change _ = r (Loc.xx1 xj' 0 (Loc.inX X.E _ _ v))
    rw [unfoldingAffinePointMap_apply_inclusion, hfix]
  have hn := intAt_n1Arg_of_mem hc hD (by omega) h2 hr
  refine GlobalTheory.T.affine_eigenvalue_eq_one_of_boxSum_ne_zero X.E X.K P.1 hd _ _ R.m I T b _ (fun t => ?_) ?_
  · have hT' : Loc.xx1 xj' (T t + b) = r.toLinearMap ∘ₗ Loc.xx1 xj' t := (hT t).symm
    unfold integrand chiInv
    rw [hT', hom, GlobalTheory.T.unfoldingCharArg_mul_left_unipotent X.E _ _ _ _ hc1 hc2 r hr.1]
    by_cases h0 : omPhi Ch sel mu cst i P hal h (Loc.xx1 xj' t) = 0
    · simp [h0]
    · rw [neg_add, hc.psi_add P _ _ (by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (b2 _ h0)) (by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg hn),
        eq_inv_of_mul_eq_one_right (psi_mul_neg (charTo hc P) hn)]
      ring
  · rw [← GlobalTheory.boxSum_eq_of_funBdd X.E X.K P.1 hd.1 _ _ _ I (max A₀ R.m) (max B₀ R.m) (le_max_right _ _) (le_max_right _ _)]
    exact hx

theorem exists_levQ {j : ℕ} {h : AutY X R j} (H : ChiMul Ch sel mu cst j P h) (H' : ChiTriv Ch sel mu cst j P h) :
    ∃ lev : LevI X.E X.K (R.N j) P.1, GrpQ sel mu cst j P h lev ∧ ChrQ Ch sel mu cst j P h lev := by
  obtain ⟨lam, hl⟩ := exists_char (H := (prCat (Pr := Pr) cst.sharp j P.1 h).subgroupOf (GLint X.E (R.N j) P.1))
    (CAt sel mu cst j P h) (chiInv Ch sel mu cst j P h)
    (fun r g => ∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) H.1 H.2
    (fun g => Subgroup.mem_subgroupOf.1 g.2) (fun r g r' g' a b x => by
      change r (r' _) = _
      rw [b, a]
      rfl) (fun g r hr r' hr' a b => by
      have h1 := H.2 r hr _ (mul_mem (inv_mem hr) hr')
      rw [mul_inv_cancel_left, H' _ (mul_mem (inv_mem hr) hr') (fun x => by
        change r.symm (r' _) = _
        rw [b, ← a, r.symm_apply_apply]), mul_one] at h1
      exact h1.symm)
  exact ⟨⟨_, lam⟩, rfl, hl⟩

variable (Pr) in

def Rep (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop := admitted Pr j P h ∧ (P ∉ Pr.vGs → NF Pr j P h)

theorem rep_one (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : Rep Pr j P (1 : AutY X R j) :=
  ⟨isAdmissibleIntegralBasisChange_one j P, IndefiniteRowSideFullHecke.SandwichNormalForm.nf_one j⟩

theorem Rep.int {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h : AutY X R j} (H : Rep Pr j P h) (sharp : Bool) :
    prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  by_cases hP : P ∈ Pr.vGs
  · exact GlobalTheory.T.projConjLevel_le_integralGL_at_typePrime X Pr R sharp j P hP h (H.1.1 hP)
  · exact GlobalTheory.Proof.parahoric_le_integral_gl.prCat_le_GLint X Pr R sharp j P hP h (H.2 hP)

theorem exists_step (hc : cst.Ok) (hd : DegOneUnram P.1) (hD : P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P) {i : ℕ}
    (hi : i + 3 ≤ R.m) (hm : P.1 ∉ Pr.vGs → cst.muq (i + 1) P ≠ 0) (A : Set (AutY X R i)) (hA : ∀ a ∈ A, Rep Pr i P.1 a) :
    ∃ F : Set (AutY X R (i + 1)), F.Finite ∧ (∀ h ∈ F, Rep Pr (i + 1) P.1 h ∧ ∃ a ∈ A, FiniteSumNonzeroLargeDepth Ch sel mu cst i P a h) ∧
      (∀ h ∈ F, ∀ h' ∈ F, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' → h = h') ∧
      ∀ h, admitted Pr (i + 1) P.1 h → (∃ a ∈ A, FiniteSumNonzeroLargeDepth Ch sel mu cst i P a h) →
        ∃ h' ∈ F, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h' h := by
  obtain ⟨ι, _, f, hf⟩ := GlobalTheory.T.admissibleRepresentatives_finite_level_cosets X Pr R cst.sharp (i + 1) P.1
  obtain ⟨F, a1, a2, a3, a4⟩ := exists_reps
    ⟨SameDC (Pr := Pr) cst.sharp (i + 1) P.1, sameDC_refl _ _ _, sameDC_symm, sameDC_trans⟩
    {h | admitted Pr (i + 1) P.1 h ∧ ∃ a ∈ A, FiniteSumNonzeroLargeDepth Ch sel mu cst i P a h}
    (fun h => Rep Pr (i + 1) P.1 h ∧ ∃ a ∈ A, FiniteSumNonzeroLargeDepth Ch sel mu cst i P a h) f
    (fun h hh h' hh' e => ⟨1, one_mem _, _, hf h h' hh.1 hh'.1 e, by group⟩) (by
      rintro h ⟨hh, a, ha, hE⟩
      by_cases hP : P.1 ∈ Pr.vGs
      · exact ⟨h, sameDC_refl _ _ _ _, ⟨hh, fun e => (e hP).elim⟩, a, ha, hE⟩
      · obtain ⟨ρ, hρ, e, z, hz⟩ := GlobalTheory.QNormalShape.exists_shape
          (GlobalTheory.Proof.lattice_normal_form_coordinates.latticeNormalFormCoord_of GlobalTheory.T.latticeNormalForm_modulo_unipotentSemidirect) X.E P.1 hd _ _ h
        have hn := GlobalTheory.T.hasLatticeNormalForm_of_between X Pr R _ P.1 hP h ρ e z hρ (hh.2 hP) hz
        have := hD hP
        refine ⟨ρ * h, sameDC_symm (sameDC_mul _ _ _ hρ), ⟨⟨fun e => (hP e).elim, fun _ => between_of_nf hP hn⟩, fun _ => hn⟩,
          a, ha, ?_⟩
        exact first_unipotent_class_transfer hc (by omega) hP hd (hm hP) (by omega) (one_mem _) hρ (one_mul _).symm rfl ((hA a ha).1.2 hP)
          ((hA a ha).1.2 hP) (hh.2 hP) (between_of_nf hP hn) hE)
  exact ⟨F, a1, a2, a3, fun h h1 h2 => a4 h ⟨h1, h2⟩⟩

theorem exists_sets (hc : cst.Ok) (hd : DegOneUnram P.1) (hD : P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P) {m2 : ℕ}
    (hm2 : R.m = m2 + 2) (hm : ∀ i, i < R.m → P.1 ∉ Pr.vGs → cst.muq (i + 1) P ≠ 0) :
    ∃ F : ∀ j, Set (AutY X R j), (∀ j, (F j).Finite ∧ ∀ h ∈ F j, Rep Pr j P.1 h) ∧ F 0 = {1} ∧ F (m2 + 1) = {1} ∧
      (∀ j, m2 + 1 < j → F j = ∅) ∧ ∀ i, i < m2 →
        (∀ h ∈ F (i + 1), ∃ a ∈ F i, FiniteSumNonzeroLargeDepth Ch sel mu cst i P a h) ∧
        (∀ h ∈ F (i + 1), ∀ h' ∈ F (i + 1), SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' → h = h') ∧
        ∀ h, admitted Pr (i + 1) P.1 h → (∃ a ∈ F i, FiniteSumNonzeroLargeDepth Ch sel mu cst i P a h) →
          ∃ h' ∈ F (i + 1), SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h' h := by
  have key : ∀ (i : ℕ) (A : Set (AutY X R i)), ∃ F : Set (AutY X R (i + 1)),
      (i < m2 → (∀ a ∈ A, Rep Pr i P.1 a) →
        F.Finite ∧ (∀ h ∈ F, Rep Pr (i + 1) P.1 h ∧ ∃ a ∈ A, FiniteSumNonzeroLargeDepth Ch sel mu cst i P a h) ∧
        (∀ h ∈ F, ∀ h' ∈ F, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h h' → h = h') ∧
        ∀ h, admitted Pr (i + 1) P.1 h → (∃ a ∈ A, FiniteSumNonzeroLargeDepth Ch sel mu cst i P a h) →
          ∃ h' ∈ F, SameDC (Pr := Pr) cst.sharp (i + 1) P.1 h' h) ∧ (i = m2 → F = {1}) ∧ (m2 < i → F = ∅) := by
    intro i A
    rcases lt_trichotomy i m2 with h | h | h
    · by_cases hA : ∀ a ∈ A, Rep Pr i P.1 a
      · obtain ⟨F, hF⟩ := exists_step (Ch := Ch) hc hd hD (by omega) (hm i (by omega)) A hA
        exact ⟨F, fun _ _ => hF, fun _ => by omega, fun _ => by omega⟩
      · exact ⟨∅, fun _ e => (hA e).elim, fun _ => by omega, fun _ => by omega⟩
    · exact ⟨{1}, fun _ => by omega, fun _ => rfl, fun _ => by omega⟩
    · exact ⟨∅, fun _ => by omega, fun _ => by omega, fun _ => rfl⟩
  choose st h1 h2 h3 using key
  let F : ∀ j, Set (AutY X R j) := fun j => Nat.rec (motive := fun j => Set (AutY X R j)) {1} st j
  have hF : ∀ i, F (i + 1) = st i (F i) := fun _ => rfl
  have hone : ∀ j, ({1} : Set (AutY X R j)).Finite ∧ ∀ h ∈ ({1} : Set (AutY X R j)), Rep Pr j P.1 h :=
    fun j => ⟨Set.finite_singleton _, fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact rep_one j _⟩
  have hR : ∀ j, (F j).Finite ∧ ∀ h ∈ F j, Rep Pr j P.1 h := by
    intro j
    induction j with
    | zero => exact hone 0
    | succ i ih =>
      rw [hF]
      rcases lt_trichotomy i m2 with h | h | h
      · exact ⟨(h1 i _ h ih.2).1, fun a ha => ((h1 i _ h ih.2).2.1 a ha).1⟩
      · rw [h2 i _ h]
        exact hone _
      · rw [h3 i _ h]
        simp
  refine ⟨F, hR, rfl, h2 m2 _ rfl, fun j hj => ?_, fun i hi => ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact h3 i _ (by omega)
  · obtain ⟨-, a, b, c⟩ := h1 i _ hi (hR i).2
    exact ⟨fun h hh => (a h hh).2, b, c⟩

end Local

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem notMem_vGs_of_mem_QE (hX : X.Ok) (hPr : Pr.Ok) {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hsel : IsSel X sel) {S : Set ℕ} (hS : ∀ i, Pr.g i ∈ S) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) : P ∉ Pr.vGs := by
  classical
  intro hG
  obtain ⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by
    unfold Primes.vGs at hG
    rcases Finset.mem_union.1 hG with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  unfold QE at hP
  split_ifs at hP with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    rw [Set.Finite.mem_toFinset] at hv
    have hg : GoodPl X.E S v := by_contra fun hg => hv
      (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 mu.2).2 v) hg)
    have h3 := (ColPeriod.absNorm_eq_of_splitAt hX.rankE hg.1 hg.2.1 (hsel v)).1
    apply hg.2.2
    rw [ColPeriod.plc_eq_absNorm hg.2.1.1, ← h3, hPr.vG_norm i _ hi]
    exact hS i
  · simp at hP

variable {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem psiAt_add {m2 : ℕ} {P : rowSG Pr sel mu} {hal : AutY X R m2} {N B : ℕ} (hB : N ≤ B)
    (H : HomBdd P.1 N (omPhi Ch sel mu cst m2 P hal 1)) (x₀ z : HomE X.E (R.N m2) (R.N (m2 + 1))) (y l : Sp X.E (R.N (m2 + 1)))
    (hz : IntHom P.1 (((qOf P.1 : X.E) ^ B)⁻¹ • z)) (hl : IntV P.1 (((qOf P.1 : X.E) ^ B)⁻¹ • l)) :
    PsiAt Ch sel mu cst m2 P hal (x₀ + z) (y + l) = PsiAt Ch sel mu cst m2 P hal x₀ y := by
  have hq := pow_ne_zero B (qOf_ne_zero P.1)
  have := (homBdd_mono hB H).2 (joinCol x₀ y) _ (intHom_joinCol hz hl)
  rw [← LastSteps.joinCol_add, smul_inv_smul₀ hq, smul_inv_smul₀ hq] at this
  exact this

open Classical in

theorem exists_chIdx_of_cst {G : ChGlob X R.m} (hd : ∀ P : rowSG Pr sel mu, DegOneUnram P.1)
    (hdis : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hc : cst.Ok) (hs : cst.sharp = true) (hM : R.m ≤ cst.M)
    (hxi : XiUnitAt (rowSG Pr sel mu) G.xi0) (hW : cst.WeilTied G.σ₀ G.xi0)
    (hmuQ : ∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
      cst.muq (i + 1) P = (((Ch.muVal ⟨i, h⟩ P.1)⁻¹ * (qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ) : X.K))
    (hmuG : ∀ (i : ℕ) (h : i < R.m) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ qu : X.Eˣ, (qu : X.E) = (qOf P.1 : X.E) →
      G.σ₀ (cst.muq (i + 1) P) =
        (((G.mu0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ)⁻¹ * G.σ₀ ((((qValC (mu : Chr X.F X.E X.K) P.1)⁻¹ : X.Kˣ)) : X.K))
    (hmu0 : ∀ (j : Fin R.m) (w : {w // w ∈ Pr.vGs}) (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (x : X.E) = (y : X.E) →
      (c : 𝓞 X.E ⧸ w.1.asIdeal) = Ideal.Quotient.mk w.1.asIdeal y →
      (((G.mu0 j).locK w.1 x : ℂˣ) : ℂ) = G.σ₀ (((Ch.chi j w c)⁻¹ : X.Kˣ) : X.K))
    (hpsi : ∀ (P : rowSG Pr sel mu) (a : X.E), P.1 ∈ Pr.vGs → IntAt P.1 a →
      cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a))
    (hDG : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → cst.D P = 1)
    (hDQ : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P)
    (hD : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * (R.m - 1) + 1 ≤ cst.D P) :
    ∃ L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)), L.Ok Ch sel mu cst G (R.m - 2) ∧
      ∀ j (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → NF Pr j P.1 (L.h j b P) := by
  obtain ⟨m2, hm2⟩ : ∃ m2, R.m = m2 + 2 := ⟨R.m - 2, by have := R.two_le_m; omega⟩
  rw [show R.m - 2 = m2 by omega]
  have hA : R.m ≤ cst.A := hM.trans hc.M_le_A
  have hB : R.m ≤ cst.B := hM.trans hc.M_le_B
  choose F hR h0 hlast hbig hmid using fun P : rowSG Pr sel mu =>
    exists_sets (Ch := Ch) hc (hd P) (hD P) hm2 fun i hi hP => by
      rw [hmuQ i hi P hP]
      exact Units.ne_zero _
  have hle : ∀ P j, ∀ h ∈ F P j, j ≤ m2 + 1 := fun P j h hh => by
    by_contra e
    rw [hbig P j (by omega)] at hh
    exact hh
  have hmul : ∀ P j, ∀ h ∈ F P j, ChiMul Ch sel mu cst j P h := fun P j h hh =>
    chiMul hc hs (hD P) (by have := hle P j h hh; omega) ((hR P j).2 h hh).1
  have htriv : ∀ P i, ∀ h ∈ F P (i + 1), ChiTriv Ch sel mu cst (i + 1) P h := fun P i h hh => by
    rcases (Nat.le_of_succ_le_succ (hle P _ h hh)).lt_or_eq with e | e
    · obtain ⟨a, ha, hE⟩ := (hmid P i e).1 h hh
      exact chiTriv_mid hc hs (hd P) (hD P) (by omega) ((hR P i).2 a ha).1 ((hR P _).2 h hh).1 hE
    · exact chiTriv_last (by unfold cOf; omega) (hmul P _ h hh)
  have hlG : ∀ j (w : {w // w ∈ Pr.vGs}), ∀ h ∈ F ⟨w.1, Finset.mem_union_left _ w.2⟩ j,
      ∃ lev : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N j), GrpG sel mu cst j ⟨w.1, Finset.mem_union_left _ w.2⟩ h lev ∧
        ChrG Ch sel mu cst j ⟨w.1, Finset.mem_union_left _ w.2⟩ h lev ∧ (j = 0 → lev = colLev Ch j w) := by
    intro j w h hh
    cases j with
    | zero =>
      rw [h0] at hh
      obtain rfl : h = 1 := hh
      exact ⟨_, GlobalTheory.T.levelGroupReduction_stepZero_typePrime Ch sel mu cst ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2 hs (hd _),
        GlobalTheory.T.levelCharacter_stepZero_typePrime Ch sel mu cst ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2 hs fun a => hpsi _ a w.2, fun _ => rfl⟩
    | succ i =>
      have hr := (hR _ _).2 h hh
      obtain ⟨lev, a, b⟩ := GlobalTheory.T.exists_levelGroup_mod_typePrime Ch sel mu cst _ ⟨w.1, Finset.mem_union_left _ w.2⟩ h hc w.2 (hd _) (hr.1.1 w.2)
        (hr.int _) (GlobalTheory.T.rowType_one_add_prime_smul_eq_one Ch mu _ _ _ (by have := hle _ _ h hh; omega)) (hmul _ _ h hh) (htriv _ _ h hh)
      exact ⟨lev, a, b, fun e => by omega⟩
  have hlQ : ∀ j (w : {w // w ∈ QE sel (mu : Chr X.F X.E X.K)}), ∀ h ∈ F ⟨w.1, Finset.mem_union_right _ w.2⟩ j,
      ∃ lev : LevI X.E X.K (R.N j) w.1, GrpQ sel mu cst j ⟨w.1, Finset.mem_union_right _ w.2⟩ h lev ∧
        ChrQ Ch sel mu cst j ⟨w.1, Finset.mem_union_right _ w.2⟩ h lev ∧ (j = 0 → lev = ⟨⊤, 1⟩) := by
    intro j w h hh
    cases j with
    | zero =>
      rw [h0] at hh
      obtain rfl : h = 1 := hh
      obtain ⟨a, b⟩ := GlobalTheory.T.level_stepZero_at_twistPrime_full Ch sel mu cst ⟨w.1, Finset.mem_union_right _ w.2⟩ (hdis _ w.2) hc
      exact ⟨_, a, b, fun _ => rfl⟩
    | succ i =>
      obtain ⟨lev, a, b⟩ := exists_levQ (hmul _ _ h hh) (htriv _ _ h hh)
      exact ⟨lev, a, b, fun e => by omega⟩
  choose lG lG1 lG2 lG3 using hlG
  choose lQ lQ1 lQ2 lQ3 using hlQ
  have hfin : ∀ j, Finite (∀ P : rowSG Pr sel mu, F P j) := fun j => by
    have := fun P => (hR P j).1.to_subtype
    infer_instance
  let L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)) :=
    { β := fun j => ∀ P : rowSG Pr sel mu, F P j
      finβ := fun j => @Fintype.ofFinite _ (hfin j)
      decβ := fun _ => Classical.decEq _
      h := fun _ b P => (b P).1
      levG := fun j b w => lG j w _ (b _).2
      levQ := fun j b w => lQ j w _ (b _).2 }
  have rep : ∀ j (b : L.β j) (P : rowSG Pr sel mu), Rep Pr j P.1 (L.h j b P) := fun j b P => (hR P j).2 _ (b P).2
  have one : ∀ j, (∀ P, F P j = {1}) → (∃ b : L.β j, ∀ b', b' = b) ∧ ∀ b P, L.h j b P = 1 := fun j hj => by
    have h1 : ∀ (b : L.β j) P, L.h j b P = 1 := fun b P => by
      have := (b P).2
      exact (Set.ext_iff.1 (hj P) _).1 this
    exact ⟨⟨fun P => ⟨1, by rw [hj]; rfl⟩, fun b' => funext fun P => Subtype.ext (h1 b' P)⟩, h1⟩
  have bdd := fun i (hi : i + 2 ≤ R.m) (al : L.β i) (P : rowSG Pr sel mu) (h : AutY X R (i + 1)) (hh : admitted Pr (i + 1) P.1 h) =>
    omPhi_bdd' (Ch := Ch) hc (hD P) hi (rep i al P).1 hh
  have bl := fun (al : L.β m2) (P : rowSG Pr sel mu) => (bdd m2 (by omega) al P 1 (isAdmissibleIntegralBasisChange_one _ _)).1
  have c1 : 1 ≤ cOf R m2 := by unfold cOf; omega
  refine ⟨L, ?_, fun j b P => (rep j b P).2⟩
  exact
    { hm := hm2
      cst_ok := hc
      xiUnitAtPrime := hxi
      weil := hW
      muqQ := hmuQ
      muqG := hmuG
      mu0G := hmu0
      psi0 := hpsi
      deep := fun A B h1 h2 i hi al be P => by
        funext xj
        obtain ⟨b1, b2⟩ := bdd i (by omega) al P _ (rep _ be P).1
        have I := integrand_funBdd (charTo hc P) b1 b2 xj
        exact (GlobalTheory.boxSum_eq_of_funBdd X.E X.K P.1 (hd P).1 _ _ _ I A B (hA.trans h1) (hB.trans h2)).trans
          (GlobalTheory.boxSum_eq_of_funBdd X.E X.K P.1 (hd P).1 _ _ _ I cst.A cst.B hA hB).symm
      zero_uniq := (one 0 h0).1
      zero_h := (one 0 h0).2
      zero_G := fun b => funext fun w => lG3 0 w _ (b _).2 rfl
      zero_Q := fun b => funext fun w => lQ3 0 w _ (b _).2 rfl
      last_uniq := (one _ hlast).1
      last_h := (one _ hlast).2
      nonvan := fun i hi b P => by
        choose a ha hE using fun P => (hmid P i hi).1 _ (b P).2
        exact ⟨fun P => ⟨a P, ha P⟩, hE P⟩
      inj := fun i hi b b' hb => funext fun P => Subtype.ext ((hmid P i hi).2.1 _ (b P).2 _ (b' P).2 (hb P))
      surj := fun i hi hh h1 h2 h3 => by
        choose a ha hE using fun P => (hmid P i hi).2.2 (hh P) ⟨h1 P, fun hP => (between_iff hP _).1 (h2 P hP)⟩ (by
          obtain ⟨al, hal⟩ := h3 P
          exact ⟨_, (al P).2, hal⟩)
        exact ⟨fun P => ⟨a P, ha P⟩, hE⟩
      stabG := fun j b P => (rep j b P).1.1
      depthG := hDG
      depthQ := hDQ
      depthQ' := hD
      boundQ := fun j b P hP => (between_iff hP _).2 ((rep j b P).1.2 hP)
      psiSupp := fun al P x₀ y' hx => by
        by_cases hP : P.1 ∈ Pr.vGs
        · rw [if_pos hP, pow_one]
          exact (mem_stdAt_iff _).1 ((LastSteps.joinCol_mem (LastSteps.cOf_pen hm2) (LastSteps.cOf_top hm2) _ _).1
            ((LastSteps.good_omPhi Ch sel mu cst hm2 P hP ((rep _ al P).1.1 hP)).1 _ hx)).2
        · rw [if_neg hP]
          exact (of_intHom_joinCol c1 ((homBdd_mono hM (bl al P)).1 _ hx)).2
      psiInv := fun al P x₀ y' z hz => by
        by_cases hP : P.1 ∈ Pr.vGs
        · have hq := qOf_ne_zero P.1
          simp only [if_pos hP, pow_zero, inv_one, one_mul] at hz
          have := (LastSteps.good_omPhi Ch sel mu cst hm2 P hP ((rep _ al P).1.1 hP)).2.1 (joinCol x₀ y')
            (joinCol 0 ((qOf P.1 : X.E)⁻¹ • z)) ((LastSteps.joinCol_mem (LastSteps.cOf_pen hm2) (LastSteps.cOf_top hm2) _ _).2
              ⟨fun _ _ => zero_mem _, by rw [smul_inv_smul₀ hq]; exact (mem_stdAt_iff _).2 hz⟩)
          rw [← LastSteps.joinCol_add, smul_zero, add_zero, smul_inv_smul₀ hq] at this
          exact this
        · rw [if_neg hP] at hz
          have := psiAt_add hM (bl al P) x₀ 0 y' z (fun _ _ => by simpa using IntV.zero P.1) hz
          rwa [add_zero] at this
      xiSupp := fun i hi al be P x hx =>
        (intHom_iff _).1 (((GlobalTheory.Proof.unfolding_bounded_integral.unfold_bdd X.E X.K P.1 _ _ _ _ (cst.psi P) _ cst.A cst.B _
          (bdd i (by omega) al P _ (rep _ be P).1).1).1 x (right_ne_zero_of_mul hx)).pow_mono hA)
      xiInv := fun i hi al be P x z hz => by
        have := (GlobalTheory.Proof.unfolding_bounded_integral.unfold_bdd X.E X.K P.1 _ _ _ _ (cst.psi P) _ cst.A cst.B _
          (homBdd_mono hB (bdd i (by omega) al P _ (rep _ be P).1).1)).2 x _
          ((intHom_iff (((qOf P.1 : X.E) ^ cst.B)⁻¹ • z)).2 hz)
        rw [smul_inv_smul₀ (pow_ne_zero _ (qOf_ne_zero P.1))] at this
        unfold XiAt
        exact congrArg _ this
      psiSuppX := fun al P x₀ y' hx => (intHom_iff _).1 (of_intHom_joinCol c1 ((homBdd_mono hA (bl al P)).1 _ hx)).1
      psiInvX := fun al P x₀ z y' hz => by
        have := psiAt_add hB (bl al P) x₀ z y' 0 ((intHom_iff _).2 hz) (by simpa using IntV.zero P.1)
        rwa [add_zero] at this
      int := fun j b P => (rep j b P).int _
      grpQ := fun j b P => lQ1 j P _ (b _).2
      chrQ := fun j b P => lQ2 j P _ (b _).2
      grpG := fun j b w => lG1 j w _ (b _).2
      chrG := fun j b w => lG2 j w _ (b _).2 }

end Main

end GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

theorem exists_chIdx {X : Fields} {Pr : Primes X} {R : Ranks} (hX : X.Ok) (hPr : Pr.Ok) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (hsel : IsSel X sel) {S : Set ℕ} (hS : ∀ i, Pr.g i ∈ S)
    (mu : Tup X.F X.E X.K S) (G : ChGlob X R.m) (e : Fin R.m → X.Tau → ℚ) (he : ∀ j τ, ∃ z : ℤ, e j τ = z)
    (eta : Formalism.L2.Host.HChar X.E) (hT : Ch.Tied G.σ₀ e G.mu0 eta)
    (hW : Ch.WeilTied G.σ₀ G.xi0) (hxi : XiUnitAt (rowSG Pr sel mu) G.xi0)
    (M A B Dq : ℕ) (hM : R.m ≤ M) (hA : M ≤ A) (hB : M ≤ B) (hD : 2 * M ≤ Dq)
    (hsq : ∀ P : rowSG Pr sel mu, ∃ s : X.K, s ^ 2 = (qOf P.1 : X.K))
    (hroot : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → ∃ ζ : X.K, IsPrimitiveRoot ζ (qOf P.1 ^ Dq)) :
    ∃ (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))),
      cst.sharp = true ∧ cst.M = M ∧ cst.A = A ∧ cst.B = B ∧ (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → cst.D P = Dq) ∧
      L.Ok Ch sel mu cst G (R.m - 2) ∧
      (∀ j (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P.1 (L.h j b P)) ∧
      ∀ j (b : L.β j) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
        ∃ (nn : Fin (cOf R j) → ℤ) (z : Fin (R.N j) → X.E), (∀ i, -(j : ℤ) ≤ nn i ∧ nn i ≤ 0) ∧
          (fun l : Fin (R.N j + cOf R j) => if hl : l.1 < R.N j then z ⟨l.1, hl⟩ else 0) ∈ lamYat (Pr := Pr) (R := R) j P.1 ∧
          (lamYat (Pr := Pr) (R := R) j P.1).map ((L.h j b P).toLinearMap.restrictScalars (𝓞 X.E)) =
            (lamYat (Pr := Pr) (R := R) j P.1).map
              ((Matrix.toLin' (IdxEx.nfMat (R.N j) (cOf R j) (qOf P.1 : X.E) nn z)).restrictScalars (𝓞 X.E)) := by
  have h2 := R.two_le_m
  obtain ⟨cst, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := exists_locCst hX hPr Ch sel hsel mu G e he eta hT hW hxi
    M A B Dq (by omega) hA hB hD (by omega) hsq hroot
  obtain ⟨L, b1, b2⟩ := IdxEx.exists_chIdx_of_cst (degOneUnram_rowSG hX hPr hsel mu)
    (fun P hP => IdxEx.notMem_vGs_of_mem_QE hX hPr hsel hS mu hP) a1 a3 (a4 ▸ hM) hxi a2 a7 a8 (tameHeckeCharLocal_eq_inv_typeCharacter hT) a9 a10 a11 a12
  exact ⟨cst, L, a3, a4, a5, a6, a13, b1, b2, fun j b P hP => GlobalTheory.T.latticeNormalForm_via_matrix X Pr R j P.1 hP _ (b2 j b P hP)⟩

end GlobalTheory.Mem.Col2

end
