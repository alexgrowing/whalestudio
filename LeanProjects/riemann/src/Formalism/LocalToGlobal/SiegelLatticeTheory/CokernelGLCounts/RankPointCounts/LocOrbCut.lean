import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumPf

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbCut

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf
open Classical ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def FiniteIntegralOrbitSumFormula (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : Prop :=
  ∃ S : Finset (Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)),
    (∀ O ∈ S, IsZO M a O) ∧
    (∀ O, IsZO M a O → O ∉ S → ∀ xy, zAt a xy ∈ O → M.bbIntegrand a c xy * (wtZ M a O : ℂ) = 0) ∧
    ∀ g : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E) → (Loc.IL (m + 1) → E) × (Loc.IN a → E),
      (∀ O ∈ S, zAt a (g O) ∈ O) → ∑ O ∈ S, M.bbIntegrand a c (g O) * (wtZ M a O : ℂ) = M.BB a c

theorem orbCut_of (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) (h : FiniteIntegralOrbitSumFormula M a c) :
    OrbCut M a c := by
  intro k V hV0 hV
  obtain ⟨S, hSZ, hoff, hsum⟩ := h
  choose! g hg hgV using hV
  have hne : ∀ O ∉ S, V O = 0 := by
    intro O hO
    by_cases hZ : IsZO M a O
    · rw [hgV O hZ, mul_assoc, hoff O hZ hO (g O) (hg O hZ), mul_zero]
    · exact hV0 O hZ
  have hsumV : ∑ O ∈ S, V O = k * M.BB a c := by
    rw [← hsum g (fun O hO => hg O (hSZ O hO)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun O hO => ?_
    rw [hgV O (hSZ O hO), mul_assoc]
  refine ⟨hsumV ▸ hasSum_sum_of_ne_finset_zero hne, ?_⟩
  exact summable_of_ne_finset_zero (s := S) fun O hO => by rw [hne O hO, norm_zero]

section Orb

theorem int_mul (R : Subring E) {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, A i j ∈ R)
    (hB : ∀ i j, B i j ∈ R) (i j : Fin n) : (A * B) i j ∈ R := by
  rw [Matrix.mul_apply]
  exact R.sum_mem fun k _ => R.mul_mem (hA i k) (hB k j)

theorem adj_int (R : Subring E) {n : ℕ} (l : Matrix (Fin n) (Fin n) E) (h : ∀ a b, l a b ∈ R) (i j : Fin n) :
    l.adjugate i j ∈ R := by
  have e : l = R.subtype.mapMatrix (Matrix.of fun a b => (⟨l a b, h a b⟩ : R)) := by ext; rfl
  rw [e, ← RingHom.map_adjugate, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact Subtype.property _

theorem inv_int (R : Subring E) {n : ℕ} (l : Matrix (Fin n) (Fin n) E) (h : ∀ a b, l a b ∈ R) (hd : l.det = 1)
    (i j : Fin n) : l⁻¹ i j ∈ R := by
  rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
  exact adj_int R l h i j

theorem lowUni_of (M : Loc.Model F E) {n : ℕ} {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow M l) :
    Formalism.DoubleCosetMeasures.IsLowUni l := ⟨fun i j hij => h.2.1 i j hij, h.1⟩

theorem upUni_of (M : Loc.Model F E) {n : ℕ} {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp M l) :
    Formalism.DoubleCosetMeasures.IsUpUni l := ⟨fun i j hij => h.2.1 i j hij, h.1⟩

theorem intLow_one (M : Loc.Model F E) {n : ℕ} : Formalism.MainNotions.S.TieN.IntLow M (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_lt h), fun a b => by
    by_cases h : a = b <;> simp [Matrix.one_apply, h, M.R.one_mem, M.R.zero_mem]⟩

theorem intUp_one (M : Loc.Model F E) {n : ℕ} : Formalism.MainNotions.S.TieN.IntUp M (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_gt h), fun a b => by
    by_cases h : a = b <;> simp [Matrix.one_apply, h, M.R.one_mem, M.R.zero_mem]⟩

theorem intLow_mul (M : Loc.Model F E) {n : ℕ} {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow M l)
    (h' : Formalism.MainNotions.S.TieN.IntLow M l') : Formalism.MainNotions.S.TieN.IntLow M (l * l') := by
  have u := Formalism.DoubleCosetMeasures.isLowUni_mul E (lowUni_of M h) (lowUni_of M h')
  exact ⟨u.2, fun a b hab => u.1 hab, int_mul M.R h.2.2 h'.2.2⟩

theorem intUp_mul (M : Loc.Model F E) {n : ℕ} {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp M l)
    (h' : Formalism.MainNotions.S.TieN.IntUp M l') : Formalism.MainNotions.S.TieN.IntUp M (l * l') := by
  have u := Formalism.DoubleCosetMeasures.isUpUni_mul E (upUni_of M h) (upUni_of M h')
  exact ⟨u.2, fun a b hab => u.1 hab, int_mul M.R h.2.2 h'.2.2⟩

theorem intLow_inv (M : Loc.Model F E) {n : ℕ} {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow M l) :
    Formalism.MainNotions.S.TieN.IntLow M l⁻¹ := by
  have u := Formalism.DoubleCosetMeasures.isLowUni_inv E (lowUni_of M h)
  exact ⟨u.2, fun a b hab => u.1 hab, inv_int M.R l h.2.2 (Formalism.DoubleCosetMeasures.isLowUni_det E (lowUni_of M h))⟩

theorem intUp_inv (M : Loc.Model F E) {n : ℕ} {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp M l) :
    Formalism.MainNotions.S.TieN.IntUp M l⁻¹ := by
  have u := Formalism.DoubleCosetMeasures.isUpUni_inv E (upUni_of M h)
  exact ⟨u.2, fun a b hab => u.1 hab, inv_int M.R l h.2.2 (Formalism.DoubleCosetMeasures.isUpUni_det E (upUni_of M h))⟩

theorem mem_orbR (M : Loc.Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) : Z ∈ orbR M Z :=
  ⟨1, 1, intLow_one M, intUp_one M, by simp⟩

theorem orbR_eq (M : Loc.Model F E) {n : ℕ} {Z Z' : Matrix (Fin n) (Fin n) E} (h : Z' ∈ orbR M Z) :
    orbR M Z' = orbR M Z := by
  obtain ⟨l, ρ, hl, hρ, rfl⟩ := h
  have hlu : IsUnit l.det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det E (lowUni_of M hl)]; exact isUnit_one
  have hρu : IsUnit ρ.det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det E (upUni_of M hρ)]; exact isUnit_one
  ext Y
  constructor
  · rintro ⟨l', ρ', hl', hρ', rfl⟩
    exact ⟨l' * l, ρ * ρ', intLow_mul M hl' hl, intUp_mul M hρ hρ', by simp only [Matrix.mul_assoc]⟩
  · rintro ⟨l', ρ', hl', hρ', rfl⟩
    refine ⟨l' * l⁻¹, ρ⁻¹ * ρ', intLow_mul M hl' (intLow_inv M hl), intUp_mul M (intUp_inv M hρ) hρ', ?_⟩
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc l⁻¹ l, Matrix.nonsing_inv_mul _ hlu, Matrix.one_mul, ← Matrix.mul_assoc ρ ρ⁻¹,
      Matrix.mul_nonsing_inv _ hρu, Matrix.one_mul]

theorem int_of_mem (M : Loc.Model F E) {n : ℕ} {Z Z' : Matrix (Fin n) (Fin n) E} (hZ : ∀ i j, Z i j ∈ M.R)
    (h : Z' ∈ orbR M Z) : ∀ i j, Z' i j ∈ M.R := by
  obtain ⟨l, ρ, hl, hρ, rfl⟩ := h
  exact int_mul M.R (int_mul M.R hl.2.2 hZ) hρ.2.2

theorem isZO_eq (M : Loc.Model F E) {m : ℕ} {a : Loc.Pt E (m + 1)} {O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)}
    (hO : IsZO M a O) {Z : Matrix (Fin (m + 1)) (Fin (m + 1)) E} (hZ : Z ∈ O) : orbR M Z = O := by
  obtain ⟨xy, _, rfl⟩ := hO
  exact orbR_eq M hZ

theorem isZO_int (M : Loc.Model F E) {m : ℕ} {a : Loc.Pt E (m + 1)} {O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)}
    (hO : IsZO M a O) {Z : Matrix (Fin (m + 1)) (Fin (m + 1)) E} (hZ : Z ∈ O) : ∀ i j, Z i j ∈ M.R := by
  obtain ⟨xy, hi, rfl⟩ := hO
  exact int_of_mem M hi hZ

end Orb

section Core

variable [IsTopologicalRing E]

def zQ {m : ℕ} (R : Subring E) (a : Loc.Pt E (m + 1)) (q : Formalism.FourierDecayAlt.A5.Cos R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
  (Formalism.FourierDecayAlt.A5.orbZ (Formalism.MainNotions.LocalModelPeriodLattices.tr a) (Formalism.FourierDecayAlt.A5.rep R q)).submatrix
    (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a).symm) (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a).symm)

def phQ {m : ℕ} (R : Subring E) (a : Loc.Pt E (m + 1)) (q : Formalism.FourierDecayAlt.A5.Cos R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) : E :=
  Formalism.DoubleCosetMeasures.sLow (((Formalism.FourierDecayAlt.A5.rep R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
            Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) +
    Formalism.DoubleCosetMeasures.sUp (((Formalism.FourierDecayAlt.A5.rep R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
      Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)

def valQ (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m)
    (q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) : ℂ :=
  Formalism.MainNotions.LocalOrbitGerms.Cls.GG M c (zQ M.R a q) (phQ M.R a q)

theorem bb_eq_sum (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) :
    (Function.support (valQ M a c)).Finite ∧ M.BB a c = ∑ᶠ q, valQ M a c q := by
  obtain ⟨μ₁, μ₂, hi1, hi2, hs1, hs2, hv1, hv2, hint⟩ := Formalism.MainNotions.LocalOrbitGerms.ctAll F E M hOK (m + 1) a
  have hψ : ∀ x ∈ M.R, M.psiR x = 1 := fun r hr => by
    simpa using (Formalism.MainNotions.LocalModelPeriodLattices.selfDual_of_core M hOK 1).2 M.R.one_mem r hr
  have hD := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK M hOK
  haveI := hD.t2
  haveI := hi1
  haveI := hi2
  haveI := hs1
  haveI := hs2
  have hcs := Formalism.DoubleCosetMeasures.Final.suppCompact E M.R hD.isOpen hD.isCompact (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1
    (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 M.psiR (M.Cok (Quotient.out c)) (M.eCls (Quotient.out c))
    (Formalism.MainNotions.LocalOrbitGerms.Cls.lamK M (Quotient.out c))
  have hval : ∀ q, valQ M a c q = Formalism.DoubleCosetMeasures.phi M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 M.psiR
      (M.Cok (Quotient.out c)) (M.eCls (Quotient.out c)) (Formalism.MainNotions.LocalOrbitGerms.Cls.lamK M (Quotient.out c))
      (q.1.out, q.2.out) := fun q => Formalism.MainNotions.LocalOrbitGerms.Cls.GG_eq_phi M a c _
  refine ⟨?_, ?_⟩
  · have h := (Formalism.DoubleCosetMeasures.Final.bbFinite E M.R hD.isOpen _ _ M.psiR hψ μ₁ μ₂ _ _ _ hcs).1
    have e : valQ M a c = fun q => Formalism.DoubleCosetMeasures.phi M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 M.psiR
      (M.Cok (Quotient.out c)) (M.eCls (Quotient.out c)) (Formalism.MainNotions.LocalOrbitGerms.Cls.lamK M (Quotient.out c))
      (q.1.out, q.2.out) := funext hval
    rw [e]
    exact h
  · rw [Formalism.MainNotions.LocalOrbitGerms.Cls.BB_eq M a μ₁ μ₂ hint c,
      Formalism.DoubleCosetMeasures.Final.bbNorm E M.R hD.isOpen _ _ M.psiR hψ μ₁ μ₂ hv1 hv2 _ _ _ hcs]
    exact finsum_congr fun q => (hval q).symm

end Core

section Assembly

variable [IsTopologicalRing E]

def OrbitMeasureCosetCount (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) : Prop :=
  ∀ O, IsZO M a O →
    (Function.support (fun q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) =>
      if zQ M.R a q ∈ O then (1 : ℂ) else 0)).Finite ∧
    (wtZ M a O : ℂ) = ∑ᶠ q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a), if zQ M.R a q ∈ O then (1 : ℂ) else 0

def IntegralOrbitOfCoset (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) : Prop :=
  ∀ q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a), (∀ i j, zQ M.R a q i j ∈ M.R) → IsZO M a (orbR M (zQ M.R a q))

def IntegrandConstantOnOrbit (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : Prop :=
  ∀ (q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) xy, (∀ i j, zAt a xy i j ∈ M.R) →
    zQ M.R a q ∈ orbR M (zAt a xy) → valQ M a c q = M.bbIntegrand a c xy

theorem int_of_valQ (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m)
    (q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) (h : valQ M a c q ≠ 0) : ∀ i j, zQ M.R a q i j ∈ M.R := by
  unfold valQ Formalism.MainNotions.LocalOrbitGerms.Cls.GG at h
  split_ifs at h with hI
  · exact hI.1
  · exact absurd rfl h

theorem int_of_bb (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) xy
    (h : M.bbIntegrand a c xy ≠ 0) : ∀ i j, zAt a xy i j ∈ M.R := by
  unfold Loc.Model.bbIntegrand at h
  dsimp only at h
  split_ifs at h with hI
  · exact hI.1
  · exact absurd rfl h

theorem orbFin_of (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m)
    (hW : OrbitMeasureCosetCount M a) (hR : IntegralOrbitOfCoset M a) (hV : IntegrandConstantOnOrbit M a c) : FiniteIntegralOrbitSumFormula M a c := by
  obtain ⟨hfin, hBB⟩ := bb_eq_sum M hOK a c
  set T := hfin.toFinset with hT
  have memT : ∀ q, q ∈ T ↔ valQ M a c q ≠ 0 := fun q => by simp [hT]
  refine ⟨T.image (fun q => orbR M (zQ M.R a q)), ?_, ?_, ?_⟩
  · intro O hO
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hO
    exact hR q (int_of_valQ M a c q ((memT q).1 hq))
  · intro O hO hOS xy hxy
    by_contra hne
    have hF : M.bbIntegrand a c xy ≠ 0 := left_ne_zero_of_mul hne
    have hw : (wtZ M a O : ℂ) ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨q, hq⟩ : ∃ q, zQ M.R a q ∈ O := by
      by_contra hno
      push Not at hno
      apply hw
      rw [(hW O hO).2]
      exact finsum_eq_zero_of_forall_eq_zero fun q => if_neg (hno q)
    have hxyO := isZO_eq M hO hxy
    have hv := hV q xy (int_of_bb M a c xy hF) (hxyO ▸ hq)
    apply hOS
    refine Finset.mem_image.2 ⟨q, (memT q).2 (hv ▸ hF), isZO_eq M hO hq⟩
  · intro g hg
    rw [hBB]
    have hsum : ∀ O ∈ T.image (fun q => orbR M (zQ M.R a q)),
        M.bbIntegrand a c (g O) * (wtZ M a O : ℂ) =
          ∑ᶠ q, M.bbIntegrand a c (g O) * (if zQ M.R a q ∈ O then (1 : ℂ) else 0) := by
      intro O hO
      obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.1 hO
      have hZO := hR q0 (int_of_valQ M a c q0 ((memT q0).1 hq0))
      rw [(hW _ hZO).2, mul_finsum]
    rw [Finset.sum_congr rfl hsum, ← finsum_sum_comm]
    · refine finsum_congr fun q => ?_
      by_cases hex : ∃ O ∈ T.image (fun q => orbR M (zQ M.R a q)), zQ M.R a q ∈ O
      · obtain ⟨O, hO, hqO⟩ := hex
        obtain ⟨q0, hq0, hOe⟩ := Finset.mem_image.1 hO
        have hZO : IsZO M a O := hOe ▸ hR q0 (int_of_valQ M a c q0 ((memT q0).1 hq0))
        rw [Finset.sum_eq_single O]
        · rw [if_pos hqO, mul_one]
          have hgO := hg O hO
          refine (hV q (g O) (isZO_int M hZO hgO) ?_).symm
          rw [isZO_eq M hZO hgO]
          exact hqO
        · intro O' hO' hne
          obtain ⟨q1, hq1, hOe'⟩ := Finset.mem_image.1 hO'
          have hZO' : IsZO M a O' := hOe' ▸ hR q1 (int_of_valQ M a c q1 ((memT q1).1 hq1))
          rw [if_neg, mul_zero]
          intro hqO'
          exact hne ((isZO_eq M hZO' hqO').symm.trans (isZO_eq M hZO hqO))
        · intro h
          exact absurd hO h
      · push Not at hex
        rw [Finset.sum_eq_zero fun O hO => by rw [if_neg (hex O hO), mul_zero]]
        by_contra hne
        exact hex _ (Finset.mem_image.2 ⟨q, (memT q).2 (Ne.symm hne), rfl⟩) (mem_orbR M _)
    · intro O hO
      obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.1 hO
      have hZO := hR q0 (int_of_valQ M a c q0 ((memT q0).1 hq0))
      exact (hW _ hZO).1.subset (Function.support_mul_subset_right _ _)

theorem orbitDecomposition_of_three (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m)
    (hW : OrbitMeasureCosetCount M a) (hR : IntegralOrbitOfCoset M a) (hV : IntegrandConstantOnOrbit M a c) : OrbCut M a c :=
  orbCut_of M a c (orbFin_of M hOK a c hW hR hV)

end Assembly

section Wt

open Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P.Supp Matrix Topology in

theorem isCompact_intLocus (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (R : Subring K) (hRc : IsCompact (R : Set K)) (s : List ℕ) (t : ℕ → Kˣ) :
    IsCompact {p : lowW K s t × upUniG K s.sum | IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
      pt s t * ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))} ∧
    IsClosed {p : lowW K s t × upUniG K s.sum | IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
      pt s t * ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))} := by
  obtain ⟨Ph, Pu, hPh, hPu, hP⟩ := lu_rec (K := K) (n := s.sum)
  obtain ⟨wi, h1, h2⟩ : ∃ wi : Matrix (Fin s.sum) (Fin s.sum) K,
      wi * Formalism.DoubleCosetMeasures.pt s t = 1 ∧ Formalism.DoubleCosetMeasures.pt s t * wi = 1 :=
    ⟨Formalism.DoubleCosetMeasures.pt s (fun b => (t b)⁻¹), pt_mul_pt s _ _ (fun b => by simp),
      pt_mul_pt s _ _ (fun b => by simp)⟩
  have hV : Continuous fun Z : Matrix (Fin s.sum) (Fin s.sum) K => Formalism.DoubleCosetMeasures.pt s t * Ph (wi * Z) * wi :=
    (continuous_const.mul (hPh.comp (continuous_const.mul continuous_id))).mul continuous_const
  have hU : Continuous fun Z : Matrix (Fin s.sum) (Fin s.sum) K => Pu (wi * Z) :=
    hPu.comp (continuous_const.mul continuous_id)
  let Φ : Matrix (Fin s.sum) (Fin s.sum) K →
      (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) ×
        (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) :=
    fun Z => ((Formalism.DoubleCosetMeasures.pt s t * Ph (wi * Z) * wi, MulOpposite.op (Formalism.DoubleCosetMeasures.pt s t * Ph (wi * Z) * wi).adjugate),
      (Pu (wi * Z), MulOpposite.op (Pu (wi * Z)).adjugate))
  have hΦ : Continuous Φ :=
    (hV.prodMk (MulOpposite.continuous_op.comp hV.matrix_adjugate)).prodMk
      (hU.prodMk (MulOpposite.continuous_op.comp hU.matrix_adjugate))
  let ι : Formalism.DoubleCosetMeasures.lowW K s t × Formalism.DoubleCosetMeasures.upUniG K s.sum →
      (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) ×
        (Matrix (Fin s.sum) (Fin s.sum) K × (Matrix (Fin s.sum) (Fin s.sum) K)ᵐᵒᵖ) :=
    fun p => (Units.embedProduct _ (p.1 : GL (Fin s.sum) K),
      Units.embedProduct _ (p.2 : GL (Fin s.sum) K))
  have hι : IsClosedEmbedding ι :=
    (Units.isClosedEmbedding_embedProduct.comp
      (isClosed_lowW s t wi h1 h2).isClosedEmbedding_subtypeVal).prodMap
      (Units.isClosedEmbedding_embedProduct.comp
        (isClosed_upUniG (K := K) s.sum).isClosedEmbedding_subtypeVal)
  let Mset : Set (Matrix (Fin s.sum) (Fin s.sum) K) := {Z | Formalism.DoubleCosetMeasures.IsInt R Z}
  have hMc : IsCompact Mset := by
    have key : Mset = Set.univ.pi fun _ => Set.univ.pi fun _ => (R : Set K) := by
      ext Z
      show (∀ a b, Z a b ∈ R) ↔ _
      constructor
      · intro h
        exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => h i j
      · intro h a b
        exact Set.mem_univ_pi.1 (Set.mem_univ_pi.1 h a) b
    rw [key]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  let S : Set (Formalism.DoubleCosetMeasures.lowW K s t × Formalism.DoubleCosetMeasures.upUniG K s.sum) :=
    {p | Formalism.DoubleCosetMeasures.IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * Formalism.DoubleCosetMeasures.pt s t *
      ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))}
  have hScl : IsClosed S :=
    hMc.isClosed.preimage (((Units.continuous_val.comp (continuous_subtype_val.comp
      continuous_fst)).mul continuous_const).mul
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)))
  have hSsub : S ⊆ ι ⁻¹' (Φ '' Mset) := by
    intro p hp
    refine ⟨_, hp, ?_⟩
    obtain ⟨hv1, hv2⟩ := (mem_lowW_iff s t wi h1 h2 p.1.1).1 p.1.2
    have hu : Formalism.DoubleCosetMeasures.IsUpUni ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := p.2.2
    obtain ⟨e1, e2⟩ := hP _ _ hv2 hu
    have eY : wi * (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * Formalism.DoubleCosetMeasures.pt s t *
        ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) =
        (wi * ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * Formalism.DoubleCosetMeasures.pt s t) *
        ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by
      simp only [Matrix.mul_assoc]
    have eV : Formalism.DoubleCosetMeasures.pt s t * (wi * ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
        Formalism.DoubleCosetMeasures.pt s t) * wi = ((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]
    simp only [Φ, ι, eY, e1, e2, eV, Units.embedProduct_apply]
    rw [coe_inv_of_det _ (isLowUni_det K hv1), coe_inv_of_det _ (isUpUni_det K hu)]
  have hS : IsCompact S := (hι.isCompact_preimage (hMc.image hΦ)).of_isClosed_subset hScl hSsub
  exact ⟨hS, hScl⟩

theorem isClosed_intLow [T2Space E] (M : Loc.Model F E) (hRcl : IsClosed (M.R : Set E)) {n : ℕ} :
    IsClosed {l : Matrix (Fin n) (Fin n) E | Formalism.MainNotions.S.TieN.IntLow M l} := by
  have e : {l : Matrix (Fin n) (Fin n) E | Formalism.MainNotions.S.TieN.IntLow M l} =
      (⋂ a, {l | l a a = 1}) ∩ (⋂ a, ⋂ b, {l | a < b → l a b = 0}) ∩ ⋂ a, ⋂ b, {l | l a b ∈ M.R} := by
    ext l
    simp [Formalism.MainNotions.S.TieN.IntLow, and_assoc]
  have hmid : ∀ a b : Fin n, IsClosed {l : Matrix (Fin n) (Fin n) E | a < b → l a b = 0} := by
    intro a b
    by_cases hab : a < b
    · simp only [hab, true_implies]
      exact isClosed_eq (continuous_id.matrix_elem a b) continuous_const
    · simp only [hab, false_implies, Set.setOf_true]
      exact isClosed_univ
  rw [e]
  exact ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const).inter
    (isClosed_iInter fun a => isClosed_iInter fun b => hmid a b)).inter
    (isClosed_iInter fun a => isClosed_iInter fun b => hRcl.preimage (continuous_id.matrix_elem a b))

theorem isClosed_intUp [T2Space E] (M : Loc.Model F E) (hRcl : IsClosed (M.R : Set E)) {n : ℕ} :
    IsClosed {l : Matrix (Fin n) (Fin n) E | Formalism.MainNotions.S.TieN.IntUp M l} := by
  have e : {l : Matrix (Fin n) (Fin n) E | Formalism.MainNotions.S.TieN.IntUp M l} =
      (⋂ a, {l | l a a = 1}) ∩ (⋂ a, ⋂ b, {l | b < a → l a b = 0}) ∩ ⋂ a, ⋂ b, {l | l a b ∈ M.R} := by
    ext l
    simp [Formalism.MainNotions.S.TieN.IntUp, and_assoc]
  have hmid : ∀ a b : Fin n, IsClosed {l : Matrix (Fin n) (Fin n) E | b < a → l a b = 0} := by
    intro a b
    by_cases hab : b < a
    · simp only [hab, true_implies]
      exact isClosed_eq (continuous_id.matrix_elem a b) continuous_const
    · simp only [hab, false_implies, Set.setOf_true]
      exact isClosed_univ
  rw [e]
  exact ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const).inter
    (isClosed_iInter fun a => isClosed_iInter fun b => hmid a b)).inter
    (isClosed_iInter fun a => isClosed_iInter fun b => hRcl.preimage (continuous_id.matrix_elem a b))

theorem isClosed_orbR [T2Space E] [IsTopologicalRing E] (M : Loc.Model F E) (hRc : IsCompact (M.R : Set E)) {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) E) : IsClosed (orbR M Z) := by
  have hRcl := hRc.isClosed
  have hB : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (M.R : Set E)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  have hL : IsCompact {l : Matrix (Fin n) (Fin n) E | Formalism.MainNotions.S.TieN.IntLow M l} :=
    hB.of_isClosed_subset (isClosed_intLow M hRcl) fun l hl =>
      Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hl.2.2 i j
  have hU : IsCompact {l : Matrix (Fin n) (Fin n) E | Formalism.MainNotions.S.TieN.IntUp M l} :=
    hB.of_isClosed_subset (isClosed_intUp M hRcl) fun l hl =>
      Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => hl.2.2 i j
  have e : orbR M Z = (fun p : Matrix (Fin n) (Fin n) E × Matrix (Fin n) (Fin n) E => p.1 * Z * p.2) ''
      ({l | Formalism.MainNotions.S.TieN.IntLow M l} ×ˢ {ρ | Formalism.MainNotions.S.TieN.IntUp M ρ}) := by
    ext Y
    constructor
    · rintro ⟨l, ρ, hl, hρ, rfl⟩
      exact ⟨(l, ρ), ⟨hl, hρ⟩, rfl⟩
    · rintro ⟨⟨l, ρ⟩, ⟨hl, hρ⟩, rfl⟩
      exact ⟨l, ρ, hl, hρ, rfl⟩
  rw [e]
  exact ((hL.prod hU).image ((continuous_fst.matrix_mul continuous_const).matrix_mul continuous_snd)).isClosed

variable [IsTopologicalRing E]

theorem continuous_zAt {m : ℕ} (a : Loc.Pt E (m + 1)) : Continuous (zAt (E := E) a) := by
  have h1 : Continuous fun xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E) => Loc.uLow xy.1 := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Loc.uLow]
    split_ifs with h h'
    · exact continuous_const
    · exact (continuous_apply _).comp continuous_fst
    · exact continuous_const
  have h2 : Continuous fun xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E) => Loc.uUp a xy.2 := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Loc.uUp]
    split_ifs with h h'
    · exact continuous_const
    · exact (continuous_apply _).comp continuous_snd
    · exact continuous_const
  exact (h1.matrix_mul continuous_const).matrix_mul h2

theorem sub_intLow (M : Loc.Model F E) {k n : ℕ} (h : k = n) {A : Matrix (Fin n) (Fin n) E}
    (hA : Formalism.DoubleCosetMeasures.IsLowUni A) (hI : Formalism.DoubleCosetMeasures.IsInt M.R A) :
    Formalism.MainNotions.S.TieN.IntLow M (A.submatrix (finCongr h) (finCongr h)) :=
  ⟨fun i => hA.2 _, fun i j hij => hA.1 hij, fun i j => hI _ _⟩

theorem sub_intUp (M : Loc.Model F E) {k n : ℕ} (h : k = n) {A : Matrix (Fin n) (Fin n) E}
    (hA : Formalism.DoubleCosetMeasures.IsUpUni A) (hI : Formalism.DoubleCosetMeasures.IsInt M.R A) :
    Formalism.MainNotions.S.TieN.IntUp M (A.submatrix (finCongr h) (finCongr h)) :=
  ⟨fun i => hA.2 _, fun i j hij => hA.1 hij, fun i j => hI _ _⟩

theorem mem_iff_orb (M : Loc.Model F E) {n : ℕ} (Z0 : Matrix (Fin n) (Fin n) E) {l ρ Z : Matrix (Fin n) (Fin n) E}
    (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ) : l * Z * ρ ∈ orbR M Z0 ↔ Z ∈ orbR M Z0 := by
  constructor
  · intro h
    have e2 : orbR M (l * Z * ρ) = orbR M Z := orbR_eq M ⟨l, ρ, hl, hρ, rfl⟩
    rw [← orbR_eq M h, e2]
    exact mem_orbR M Z
  · intro h
    rw [← orbR_eq M h]
    exact ⟨l, ρ, hl, hρ, rfl⟩

theorem wt_gen (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (Z0 : Matrix (Fin (m + 1)) (Fin (m + 1)) E)
    (hZ0 : ∀ i j, Z0 i j ∈ M.R) :
    (Function.support (fun q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) =>
      if zQ M.R a q ∈ orbR M Z0 then (1 : ℂ) else 0)).Finite ∧
    (wtZ M a (orbR M Z0) : ℂ) =
      ∑ᶠ q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a), if zQ M.R a q ∈ orbR M Z0 then (1 : ℂ) else 0 := by
  set O := orbR M Z0 with hOdef
  obtain ⟨μ₁, μ₂, hi1, hi2, hs1, hs2, hv1, hv2, hint⟩ := Formalism.MainNotions.LocalOrbitGerms.ctAll F E M hOK (m + 1) a
  have hD := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK M hOK
  haveI := hD.t2
  haveI := hi1
  haveI := hi2
  haveI := hs1
  haveI := hs2
  haveI := hOK.borel
  haveI := Formalism.MainNotions.LocalOrbitGerms.secondCountable_of_OK M hOK
  let e := finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a).symm
  let f : Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 ×
      Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum → ℂ :=
    fun p => if (Formalism.FourierDecayAlt.A5.orbZ (Formalism.MainNotions.LocalModelPeriodLattices.tr a) p).submatrix e e ∈ O then 1 else 0
  have hinv : ∀ x ∈ Formalism.DoubleCosetMeasures.intSub M.R (Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2),
      ∀ y ∈ Formalism.DoubleCosetMeasures.intSub M.R (Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum), ∀ v u, f (x * v, u * y) = f (v, u) := by
    intro x hx y hy v u
    have e1 : Formalism.FourierDecayAlt.A5.orbZ (Formalism.MainNotions.LocalModelPeriodLattices.tr a) (x * v, u * y) =
        ((x : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
          Formalism.FourierDecayAlt.A5.orbZ (Formalism.MainNotions.LocalModelPeriodLattices.tr a) (v, u) *
          ((y : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := by
      simp only [Formalism.FourierDecayAlt.A5.orbZ, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    simp only [f]
    rw [e1, ← Matrix.submatrix_mul_equiv _ _ _ e _, ← Matrix.submatrix_mul_equiv _ _ _ e _,
      mem_iff_orb M Z0 (sub_intLow M _ x.2.1 hx.1) (sub_intUp M _ y.2 hy.1)]
  have hcs : HasCompactSupport f := by
    obtain ⟨hK, hKc⟩ := isCompact_intLocus E M.R hD.isCompact (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2
    refine HasCompactSupport.intro' hK hKc fun p hp => ?_
    simp only [f]
    rw [if_neg]
    intro hpO
    apply hp
    intro i j
    have := int_of_mem M hZ0 hpO (e.symm i) (e.symm j)
    simpa [Matrix.submatrix_apply, Formalism.FourierDecayAlt.A5.orbZ] using this
  have key := Formalism.DoubleCosetMeasures.Final.intTwoSided _ _ μ₁ μ₂ _ _ (Formalism.DoubleCosetMeasures.P.isOpen_intSub M.R hD.isOpen _)
    (Formalism.DoubleCosetMeasures.P.isOpen_intSub M.R hD.isOpen _) ℂ f hinv hcs
  refine ⟨key.1, ?_⟩
  have hA : MeasurableSet {xy | zAt a xy ∈ O} := by
    exact ((isClosed_orbR M hD.isCompact _).preimage (continuous_zAt a)).measurableSet
  have step1 : (wtZ M a O : ℂ) = ∫ xy, (if zAt a xy ∈ O then (1 : ℂ) else 0) ∂(muA M a) := by
    have : (fun xy => if zAt a xy ∈ O then (1 : ℂ) else 0) =
        fun xy => ((Set.indicator {xy | zAt a xy ∈ O} (1 : (Loc.IL (m + 1) → E) × (Loc.IN a → E) → ℝ) xy : ℝ) : ℂ) := by
      funext xy
      by_cases h : zAt a xy ∈ O <;> simp [h]
    rw [this, integral_complex_ofReal, integral_indicator_one hA]
    rfl
  have step2 : ∫ xy, (if zAt a xy ∈ O then (1 : ℂ) else 0) ∂(muA M a) = ∫ p, f p ∂(μ₁.prod μ₂) :=
    hint (fun Z _ => if Z ∈ O then (1 : ℂ) else 0)
  rw [step1, step2, key.2, hv1, hv2]
  simp only [ENNReal.toReal_one, mul_one, one_smul]
  rfl

theorem wt (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) : OrbitMeasureCosetCount M a := by
  intro O hO
  obtain ⟨xy0, hi, rfl⟩ := hO
  exact wt_gen M hOK a _ hi

theorem rep (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) : IntegralOrbitOfCoset M a := by
  intro q hq
  obtain ⟨hfin, hsum⟩ := wt_gen M hOK a _ hq
  have hne : (wtZ M a (orbR M (zQ M.R a q)) : ℂ) ≠ 0 := by
    rw [hsum, finsum_eq_sum_of_support_subset _ hfin.coe_toFinset.ge, Finset.sum_boole]
    refine Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem (a := q) ?_)
    refine Finset.mem_filter.2 ⟨?_, mem_orbR M _⟩
    rw [Set.Finite.mem_toFinset]
    simp [mem_orbR M (zQ M.R a q)]
  obtain ⟨xy, hxy⟩ : ∃ xy, zAt a xy ∈ orbR M (zQ M.R a q) := by
    by_contra hno
    push Not at hno
    apply hne
    have h0 : {xy | zAt a xy ∈ orbR M (zQ M.R a q)} = ∅ := Set.eq_empty_of_forall_notMem fun xy h => hno xy h
    simp [wtZ, h0]
  exact ⟨xy, int_of_mem M hq hxy, (orbR_eq M hxy).symm⟩

theorem orbitDecomposition_of_integrand (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m)
    (hV : IntegrandConstantOnOrbit M a c) : OrbCut M a c :=
  orbitDecomposition_of_three M hOK a c (wt M hOK a) (rep M hOK a) hV

end Wt

end Formalism.L2.SG.Pf.LocOrbCut
