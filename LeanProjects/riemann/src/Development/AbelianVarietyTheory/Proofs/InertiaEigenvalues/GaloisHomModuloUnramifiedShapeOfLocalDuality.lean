import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteResidueFieldOfCompactIsAdicDvr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotDivisibleByUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionRingQuotKilledByPowUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferCardH0H1Eq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LevelRepOneLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HcLCExistsPowSmulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionShapeOfTorsionCounts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LevelRepFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulEqZeroOfMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2Local
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardUnramifiedLevelTrivialAction

namespace GlobalTheory.ShapeUnrTriv

open ReciprocityTheory.Gal Formalism.NG Formalism.RepresentationBoundsCohomology.BR ReciprocityTheory.ChartRestriction.T2 GlobalTheory.ShapeNeg

private theorem exists_smul_eq_of_card_ker_pow_eq_of_torsion {O : Type} [CommRing O] {B : Type} [AddCommGroup B]
    [Module O B] (ϖ : O) (q : ℕ) (hq : 0 < q)
    (hcount : ∀ n : ℕ, Nat.card ↥((ϖ ^ n • LinearMap.id : B →ₗ[O] B).ker) = q ^ n)
    (htors : ∀ b : B, ∃ n : ℕ, ϖ ^ n • b = 0) (b : B) : ∃ c : B, ϖ • c = b := by
  obtain ⟨m, hm⟩ := htors b
  have hfin : ∀ n : ℕ, Finite ↥((ϖ ^ n • LinearMap.id : B →ₗ[O] B).ker) := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hcount n]; exact (pow_pos hq n).ne')
  have hmaps : ∀ x ∈ (ϖ ^ (m + 1) • LinearMap.id : B →ₗ[O] B).ker,
      (ϖ • LinearMap.id : B →ₗ[O] B) x ∈ (ϖ ^ m • LinearMap.id : B →ₗ[O] B).ker := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    rw [smul_smul, ← pow_succ]
    exact hx
  let f := (ϖ • LinearMap.id : B →ₗ[O] B).restrict hmaps
  have hker : Nat.card ↥(LinearMap.ker f) = q := by
    have e : ↥(LinearMap.ker f) ≃ ↥((ϖ ^ 1 • LinearMap.id : B →ₗ[O] B).ker) :=
      { toFun := fun x => ⟨x.1.1, by
          have := x.2
          simp only [LinearMap.mem_ker, f, LinearMap.restrict_apply, Subtype.ext_iff,
            LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_zero] at this
          simpa using this⟩
        invFun := fun y => ⟨⟨y.1, by
          have := y.2
          simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, pow_one] at this ⊢
          rw [pow_succ, mul_smul, this, smul_zero]⟩, by
          have := y.2
          simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, pow_one] at this
          simp only [LinearMap.mem_ker, f, LinearMap.restrict_apply, Subtype.ext_iff,
            LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_zero]
          exact this⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    rw [Nat.card_congr e, hcount 1, pow_one]
  have hsplit := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv, hker, hcount (m + 1), pow_succ] at hsplit
  have hrange : Nat.card ↥(LinearMap.range f) =
      Nat.card ↥((ϖ ^ m • LinearMap.id : B →ₗ[O] B).ker) := by
    rw [hcount m]
    exact Nat.eq_of_mul_eq_mul_right hq ((mul_comm _ _).trans hsplit.symm)
  have htop : (LinearMap.range f).toAddSubgroup = ⊤ := AddSubgroup.eq_top_of_card_eq _ hrange
  have hmem : (⟨b, by simpa using hm⟩ : ↥((ϖ ^ m • LinearMap.id : B →ₗ[O] B).ker)) ∈
      LinearMap.range f := by
    change _ ∈ (LinearMap.range f).toAddSubgroup
    rw [htop]
    trivial
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x.1, ?_⟩
  have := congrArg Subtype.val hx
  simpa [f] using this

private theorem card_ker_smul_eq_mul_card_ker_quotient_of_divisible {O : Type} [CommRing O] {A : Type} [AddCommGroup A]
    [Module O A] (S : Submodule O A) (c : O) (hdiv : ∀ b ∈ S, ∃ x ∈ S, c • x = b)
    [Finite ↥((c • LinearMap.id : A →ₗ[O] A).ker)] :
    Nat.card ↥((c • LinearMap.id : A →ₗ[O] A).ker) =
      Nat.card ↥((c • LinearMap.id : ↥S →ₗ[O] ↥S).ker) *
        Nat.card ↥((c • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) := by
  have hmaps : ∀ x ∈ (c • LinearMap.id : A →ₗ[O] A).ker,
      S.mkQ x ∈ (c • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker := by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
    rw [← LinearMap.map_smul, hx, map_zero]
  let g := S.mkQ.restrict hmaps
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mkQ_apply] at hy
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨z, hzS, hz⟩ := hdiv _ hy
    refine ⟨⟨x - z, ?_⟩, ?_⟩
    · simp [smul_sub, hz]
    · apply Subtype.ext
      simp only [g, LinearMap.restrict_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simpa using hzS
  have eker : ↥(LinearMap.ker g) ≃ ↥((c • LinearMap.id : ↥S →ₗ[O] ↥S).ker) :=
    { toFun := fun x => ⟨⟨x.1.1, by
          have := x.2
          simp only [LinearMap.mem_ker, g, LinearMap.restrict_apply, Subtype.ext_iff,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.coe_zero] at this
          exact this⟩, by
          have := x.1.2
          simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at this ⊢
          exact Subtype.ext this⟩
      invFun := fun y => ⟨⟨y.1.1, by
          have := y.2
          simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply,
            Subtype.ext_iff, Submodule.coe_smul, Submodule.coe_zero] at this ⊢
          exact this⟩, by
          simp only [LinearMap.mem_ker, g, LinearMap.restrict_apply, Subtype.ext_iff,
            Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.coe_zero]
          exact y.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have hsplit := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g)
  rw [Nat.card_congr g.quotKerEquivRange.toEquiv, LinearMap.range_eq_top.mpr hsurj,
    Nat.card_congr eker] at hsplit
  rw [hsplit]
  congr 1
  exact Nat.card_congr Submodule.topEquiv.toEquiv

private theorem card_ker_smul_id_eq_of_linearEquiv {O P Q : Type} [CommRing O] [AddCommGroup P] [Module O P]
    [AddCommGroup Q] [Module O Q] (e : P ≃ₗ[O] Q) (c : O) :
    Nat.card ↥((c • LinearMap.id : P →ₗ[O] P).ker) = Nat.card ↥((c • LinearMap.id : Q →ₗ[O] Q).ker) :=
  Nat.card_congr
    { toFun := fun x => ⟨e x.1, by
        have := x.2
        simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at this ⊢
        rw [← map_smul, this, map_zero]⟩
      invFun := fun y => ⟨e.symm y.1, by
        have := y.2
        simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at this ⊢
        rw [← map_smul, this, map_zero]⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }

set_option maxHeartbeats 400000 in

theorem _root_.GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality (hT : _root_.Formalism.GaloisCohomology.LocalTateDualityK) (hE : _root_.Formalism.GaloisCohomology.LocalEulerCharK) :
    _root_.ReciprocityTheory.ChartRestriction.T2.ShapeUnr := by
  unfold _root_.ReciprocityTheory.ChartRestriction.T2.ShapeUnr
  intro p _ K O _ _ _ _ _ _ _ G _ _ hK hO hFr i M _ _ u ρ htriv I hI
  haveI : IsTopologicalRing O := hO.ring
  haveI : CompactSpace O := hO.compact
  haveI : Finite (IsLocalRing.ResidueField O) := _root_.GlobalTheory.ShapeNeg.finite_residueField_of_compact_isAdic hO.adic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpϖ : (p : O) ∈ Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact hO.p_mem
  have hpow : ∀ n : ℕ, (p : O) ^ n ∈ Ideal.span {ϖ ^ n} := fun n => by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_mem_pow hpϖ n
  let ρ' : Representation O (_root_.Formalism.GaloisCohomology.GK p K) M := MonoidHom.comp ρ i.symm.toMonoidHom
  have htriv' : ∀ g m, ρ' g m = m := fun g m => htriv _ m
  have hdivM : ∀ m : M, ∃ m', ϖ • m' = m := fun m => by
    obtain ⟨y, hy⟩ := _root_.GlobalTheory.KO_divisible_by_uniformiser hϖ (u m)
    exact ⟨u.symm y, u.injective (by simp [hy])⟩
  have hdivMn : ∀ (n : ℕ) (m : M), ∃ m', ϖ ^ n • m' = m := by
    intro n
    induction n with
    | zero => exact fun m => ⟨m, by simp⟩
    | succ k ih =>
      intro m
      obtain ⟨m₁, hm₁⟩ := ih m
      obtain ⟨m₂, hm₂⟩ := hdivM m₁
      exact ⟨m₂, by rw [pow_succ, mul_smul, hm₂, hm₁]⟩
  have hlc : ∀ m : M, IsLocallyConstant fun g => ρ g m := fun m => by
    simp only [htriv]
    exact IsLocallyConstant.const m
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.UnramifiedH2Bound.h2_bounded_of_trivial_action hT hK hϖ hpϖ hO.p_ne u ρ' htriv'
    (fun n h => _root_.GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant ρ' p n (ϖ ^ n) h fun m _ => by
      simp only [htriv']
      exact IsLocallyConstant.const m)
  set q := Nat.card (IsLocalRing.ResidueField O) with hq
  set d := Module.finrank ℚ_[p] K with hd
  set A := _root_.ReciprocityTheory.ChartRestriction.T2.HcLC ρ with hA
  have hkey : ∀ n : ℕ, 0 < n → Finite ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) ∧
      q ^ n * (q ^ n) ^ d ≤ Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) ∧
      Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) ≤ q ^ n * C * (q ^ n) ^ d ∧
      (n = 1 → Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) ≤ q ^ n * q * (q ^ n) ^ d) := by
    intro n hn
    letI := _root_.GlobalTheory.ShapeNeg.levZ (M := M) p n (hpow n)
    haveI : Finite (_root_.GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) :=
      (_root_.GlobalTheory.ShapeNeg.levKO_card hϖ u n).1
    have hcardTL := (_root_.GlobalTheory.ShapeNeg.levKO_card hϖ u n).2
    have hcontn : _root_.ReciprocityTheory.Gal.ContAction (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ') :=
      _root_.GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant ρ' p n (ϖ ^ n) (hpow n) fun m _ => by
        simp only [htriv']
        exact IsLocallyConstant.const m
    have htr := _root_.GlobalTheory.ShapeNeg.transfer_card_H0_H1 i ρ p n (ϖ ^ n) (hpow n)
    obtain ⟨hfin1, hfin2⟩ := _root_.GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK n _
      (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ') hn hcontn
    have heul := hE p K hK n _ (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ') hn hcontn
    haveI hH1fin : Finite (_root_.ReciprocityTheory.Gal.H1 (_root_.GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) :=
      Nat.finite_of_card_ne_zero (by rw [htr.2]; exact Nat.card_pos.ne')
    obtain ⟨hfinA, hA1⟩ := _root_.GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq ρ ϖ n hdivM hlc hH1fin
    have hinv : Nat.card (↥ρ.invariants ⧸
        (ϖ ^ n • LinearMap.id : ↥ρ.invariants →ₗ[O] ↥ρ.invariants).range) = 1 := by
      haveI : Subsingleton (↥ρ.invariants ⧸
          (ϖ ^ n • LinearMap.id : ↥ρ.invariants →ₗ[O] ↥ρ.invariants).range) := by
        rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
        rintro ⟨x, hx⟩ -
        obtain ⟨y, hy⟩ := hdivMn n x
        refine ⟨⟨y, (Representation.mem_invariants ρ y).mpr fun g => htriv g y⟩, Subtype.ext ?_⟩
        simpa using hy
      exact Nat.card_unique
    have hH0 : Nat.card ↥(_root_.ReciprocityTheory.Gal.H0 (_root_.GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) = q ^ n := by
      have htop : _root_.ReciprocityTheory.Gal.H0 (_root_.GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n)) = ⊤ := by
        unfold _root_.ReciprocityTheory.Gal.H0
        ext x
        simp only [Submodule.mem_top, iff_true, Representation.mem_invariants]
        intro g
        apply _root_.GlobalTheory.ShapeNeg.Lev.ext
        rw [_root_.GlobalTheory.ShapeNeg.levRep_val, htriv]
      rw [htop, Nat.card_congr Submodule.topEquiv.toEquiv, hcardTL]
    have h2pos : 0 < Nat.card (_root_.ReciprocityTheory.Gal.H2 (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ')) :=
      Nat.card_pos
    have hA2 : Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) =
        q ^ n * Nat.card (_root_.ReciprocityTheory.Gal.H2 (_root_.GlobalTheory.ShapeNeg.levRepZ p n (hpow n) ρ')) *
          (q ^ n) ^ d := by
      rw [← mul_one (Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker)), ← hinv, ← hA1, htr.2,
        heul, ← htr.1, hH0, hcardTL]
    refine ⟨hfinA, ?_, ?_, ?_⟩
    · rw [hA2]
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h2pos)
    · rw [hA2]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hC n hn (hpow n)))
    · rintro rfl
      rw [hA2]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (_root_.GlobalTheory.ShapeNeg.card_H2_level_rep_le hT hK hϖ u ρ' (hpow 1) hcontn))
  haveI : CompactSpace G := i.symm.toHomeomorph.compactSpace
  have hMtors : ∀ m : M, ∃ n : ℕ, ϖ ^ n • m = 0 := fun m => by
    obtain ⟨n, hn⟩ := _root_.GlobalTheory.ShapeNeg.ko_killed_by_pow_uniformizer hϖ (u m)
    exact ⟨n, u.injective (by simp [hn])⟩
  have htorsA : ∀ x : A, ∃ n : ℕ, ϖ ^ n • x = 0 := fun x => by
    obtain ⟨n, hn⟩ := _root_.GlobalTheory.hcLC_exists_pow_smul_eq_zero ρ ϖ hMtors x.1 x.2
    exact ⟨n, Subtype.ext hn⟩
  set S : Submodule O A := Submodule.comap A.subtype (_root_.Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I) with hSdef
  have hS : ∀ n : ℕ, Nat.card ↥((ϖ ^ n • LinearMap.id : S →ₗ[O] S).ker) = q ^ n :=
    _root_.GlobalTheory.ShapeNeg.card_unr_lev_of_triv hK hϖ hpϖ i u ρ htriv I hI
  have hqpos : 0 < q := Nat.card_pos
  have hdivS : ∀ b : S, ∃ c : S, ϖ • c = b :=
    exists_smul_eq_of_card_ker_pow_eq_of_torsion ϖ q hqpos hS fun b => by
      obtain ⟨n, hn⟩ := htorsA b.1
      exact ⟨n, Subtype.ext hn⟩
  have hdivSn : ∀ n : ℕ, ∀ b ∈ S, ∃ x ∈ S, ϖ ^ n • x = b := by
    intro n
    induction n with
    | zero => exact fun b hb => ⟨b, hb, by simp⟩
    | succ k ih =>
      intro b hb
      obtain ⟨x, hxS, hx⟩ := ih b hb
      obtain ⟨y, hy⟩ := hdivS ⟨x, hxS⟩
      refine ⟨y.1, y.2, ?_⟩
      rw [pow_succ, mul_smul, ← hx]
      exact congrArg (fun z : S => ϖ ^ k • z.1) hy
  have hY : ∀ n : ℕ, 0 < n → Finite ↥((ϖ ^ n • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) ∧
      Nat.card ↥((ϖ ^ n • LinearMap.id : A →ₗ[O] A).ker) =
        q ^ n * Nat.card ↥((ϖ ^ n • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) := by
    intro n hn
    obtain ⟨hfin, hlow, -, -⟩ := hkey n hn
    have hsplit := card_ker_smul_eq_mul_card_ker_quotient_of_divisible S (ϖ ^ n) (hdivSn n)
    rw [hS n] at hsplit
    refine ⟨Nat.finite_of_card_ne_zero fun h0 => ?_, hsplit⟩
    rw [h0, mul_zero] at hsplit
    have : 0 < q ^ n * (q ^ n) ^ d := by positivity
    omega
  have hcountY : ∀ n : ℕ, 0 < n →
      Nat.card (IsLocalRing.ResidueField O) ^ (n * d) ≤
        Nat.card ↥((ϖ ^ n • LinearMap.id :
          ↥(⊤ : Submodule O (A ⧸ S)) →ₗ[O] ↥(⊤ : Submodule O (A ⧸ S))).ker) ∧
      Nat.card ↥((ϖ ^ n • LinearMap.id :
          ↥(⊤ : Submodule O (A ⧸ S)) →ₗ[O] ↥(⊤ : Submodule O (A ⧸ S))).ker) ≤
        C * Nat.card (IsLocalRing.ResidueField O) ^ (n * d) := by
    intro n hn
    rw [card_ker_smul_id_eq_of_linearEquiv Submodule.topEquiv, ← hq, pow_mul]
    obtain ⟨-, hlow, hup, -⟩ := hkey n hn
    rw [(hY n hn).2] at hlow hup
    have hqn : 0 < q ^ n := by positivity
    constructor
    · exact Nat.le_of_mul_le_mul_left hlow hqn
    · exact Nat.le_of_mul_le_mul_left (by rw [mul_assoc] at hup; exact hup) hqn
  have hone : Nat.card ↥((ϖ ^ 1 • LinearMap.id :
      ↥(⊤ : Submodule O (A ⧸ S)) →ₗ[O] ↥(⊤ : Submodule O (A ⧸ S))).ker) ≤
      Nat.card (IsLocalRing.ResidueField O) ^ (d + 1) := by
    rw [card_ker_smul_id_eq_of_linearEquiv Submodule.topEquiv, ← hq]
    obtain ⟨-, -, -, h1⟩ := hkey 1 one_pos
    have h1 := h1 rfl
    rw [(hY 1 one_pos).2] at h1
    have h1' : Nat.card ↥((ϖ ^ 1 • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) ≤ q * q ^ d :=
      Nat.le_of_mul_le_mul_left (by simpa only [pow_one, mul_assoc] using h1) (by simpa using hqpos)
    rw [pow_succ q d, mul_comm (q ^ d) q]
    exact h1'
  have htorsY : ∀ y : A ⧸ S, ∃ n : ℕ, ϖ ^ n • y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    obtain ⟨n, hn⟩ := htorsA x
    exact ⟨n, by rw [← map_smul, hn, map_zero]⟩
  have hY1 : Finite ↥((ϖ • LinearMap.id : (A ⧸ S) →ₗ[O] (A ⧸ S)).ker) := by
    have := (hY 1 one_pos).1
    rwa [pow_one] at this
  obtain ⟨a, F, _, _, hF, ⟨e⟩⟩ := _root_.GlobalTheory.CofinGen.exists_equiv_pi_prod_finite hϖ htorsY hY1
  haveI := hF
  have hshape := _root_.GlobalTheory.ShapeNeg.Shape.quotShape_of_counts hϖ (⊤ : Submodule O (A ⧸ S)) d a
    (Submodule.topEquiv.trans e) ⟨C, hcountY⟩ hone
  unfold _root_.Formalism.RepresentationBoundsCohomology.JT.QuotShape at hshape ⊢
  obtain ⟨Cy, i1, i2, ι, π, hι, hex, c0, hc0⟩ := hshape
  let E : (↥(⊤ : Submodule O (A ⧸ S)) ⧸ Submodule.comap (⊤ : Submodule O (A ⧸ S)).subtype ⊥) ≃ₗ[O]
      (A ⧸ S) :=
    (Submodule.quotEquivOfEqBot _ (by ext x; simp)).trans Submodule.topEquiv
  refine ⟨Cy, i1, i2, E.toLinearMap ∘ₗ ι, π ∘ₗ E.symm.toLinearMap, E.injective.comp hι, ?_, c0, hc0⟩
  intro y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_range]
  rw [hex (E.symm y)]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [hx]
    exact E.apply_symm_apply y
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hx]
    exact (E.symm_apply_apply (ι x)).symm

end GlobalTheory.ShapeUnrTriv
