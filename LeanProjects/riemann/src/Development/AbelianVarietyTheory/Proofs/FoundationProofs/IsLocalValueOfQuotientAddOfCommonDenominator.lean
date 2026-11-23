import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvOfFintype
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesAndDerivUniqueOfCoefficients
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralBasisOfIntegralAlgebraicElements
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalSeriesCongIffCoeffAndIsUnitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveExpansionQuotientLevelOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponentsStatement

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.IoEx

theorem exists_restrict {R : Type} [CommRing R] {M : ℕ} (hM : 0 < M) (φ : HahnSeries ℚ R) :
    ∃ C : HahnSeries ℤ R, ∀ r : ℤ, C.coeff r = φ.coeff ((r : ℚ) / (M : ℚ)) := by
  refine ⟨⟨fun r => φ.coeff ((r : ℚ) / (M : ℚ)), ?_⟩, fun _ => rfl⟩
  have h := φ.isPWO_support
  rw [Set.IsPWO, Set.partiallyWellOrderedOn_iff_exists_lt] at h ⊢
  intro f hf
  obtain ⟨m, n, hmn, hle⟩ := h (fun i => (f i : ℚ) / (M : ℚ)) hf
  refine ⟨m, n, hmn, ?_⟩
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  exact_mod_cast (div_le_div_iff_of_pos_right hM').1 hle

theorem restrict_mul {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') {M : ℕ} (hM : 0 < M)
    (φ χ : HahnSeries ℚ R) (C D : HahnSeries ℤ R')
    (hφ : ∀ r : ℚ, φ.coeff r ≠ 0 → (r * (M : ℚ)).den = 1) (hχ : ∀ r : ℚ, χ.coeff r ≠ 0 → (r * (M : ℚ)).den = 1)
    (hC : ∀ r : ℤ, C.coeff r = j (φ.coeff ((r : ℚ) / (M : ℚ))))
    (hD : ∀ r : ℤ, D.coeff r = j (χ.coeff ((r : ℚ) / (M : ℚ)))) (r : ℤ) :
    (C * D).coeff r = j ((φ * χ).coeff ((r : ℚ) / (M : ℚ))) := by
  have hM' : (0 : ℚ) < M := by exact_mod_cast hM
  let f : ℤ →+ ℚ := ⟨⟨fun r => (r : ℚ) / (M : ℚ), by simp⟩, fun a b => by push_cast; ring⟩
  have hf : ∀ a b : ℤ, f a ≤ f b ↔ a ≤ b := fun a b =>
    (div_le_div_iff_of_pos_right hM').trans Int.cast_le
  have hi : Function.Injective f := fun a b h => le_antisymm ((hf a b).1 h.le) ((hf b a).1 h.ge)
  let e : HahnSeries ℤ R' →+* HahnSeries ℚ R' := HahnSeries.embDomainRingHom f hi hf
  have he : ∀ (B : HahnSeries ℤ R') (r : ℤ), (e B).coeff ((r : ℚ) / (M : ℚ)) = B.coeff r := fun B r =>
    HahnSeries.embDomain_coeff (f := ⟨⟨f, hi⟩, hf _ _⟩) (a := r)
  have key : ∀ (φ : HahnSeries ℚ R) (C : HahnSeries ℤ R'), (∀ r : ℚ, φ.coeff r ≠ 0 → (r * (M : ℚ)).den = 1) →
      (∀ r : ℤ, C.coeff r = j (φ.coeff ((r : ℚ) / (M : ℚ)))) → φ.map j = e C := by
    intro φ C hφ hC
    ext q
    by_cases hq : q ∈ Set.range f
    · obtain ⟨r, rfl⟩ := hq
      exact (hC r).symm.trans (he C r).symm
    · have h0 : φ.coeff q = 0 := by
        by_contra h
        refine hq ⟨(q * (M : ℚ)).num, ?_⟩
        show (((q * (M : ℚ)).num : ℤ) : ℚ) / (M : ℚ) = q
        rw [(Rat.den_eq_one_iff _).1 (hφ q h), mul_div_cancel_right₀ _ hM'.ne']
      have h1 : (e C).coeff q = 0 := HahnSeries.embDomain_notin_range (f := ⟨⟨f, hi⟩, hf _ _⟩) hq
      rw [h1, HahnSeries.map_coeff, h0, map_zero]
  have hm : (φ * χ).map j = φ.map j * χ.map j := HahnSeries.map_mul (j : R →ₙ+* R')
  rw [← he (C * D) r, map_mul, ← key φ C hφ hC, ← key χ D hχ hD, ← hm, HahnSeries.map_coeff]

open scoped NNReal in

theorem exists_ev {p : ℕ} [hp : Fact p.Prime] {K : Type} [Field K] [Algebra ℚ K] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
    (hc : IsClo p Ω) (ψ : O0 p →+* Ω) (j : K →+* Ω) (hj : ∀ z, IsAlgZp p (j z)) (S : Finset K) (C : HahnSeries ℤ K)
    (hC : ∀ r, IsInt p (j (C.coeff r)) ∧ C.coeff r ∈ IntermediateField.adjoin ℚ (S : Set K)) :
    ∃ x x', Ev ψ (fun r => j (C.coeff r)) x x' := by
  classical
  obtain ⟨v, hv, -, h0, h1⟩ := exists_valuation_isInt p Ω hc
  letI : Algebra ℤ_[p] Ω := ((algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p))).toAlgebra
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hzp : ∀ z, zp Ω z = algebraMap ℤ_[p] Ω z := fun z => by
    have h : (HahnSeries.single 0 z : Lau p) = algebraMap ℤ_[p] (Lau p) z := by
      rw [HahnSeries.algebraMap_apply' ]; simp
    rw [zp, h]
    rfl
  have halg : ∀ x : Ω, IsAlgZp p x ↔ IsAlgebraic ℤ_[p] x := fun x => by
    unfold IsAlgZp IsAlgebraic
    simp only [Polynomial.aeval_map_algebraMap]
  have hle : ∀ z, v (algebraMap ℤ_[p] Ω z) ≤ 1 := fun z =>
    (hv _).2 (isIntegral_algebraMap (x := algebraMap ℤ_[p] (O0 p) z))
  have hinj : Function.Injective (algebraMap ℤ_[p] Ω) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hz0
    obtain ⟨n, hn⟩ := OkBasis.val_int v _ hle hz0
    rw [hz, map_zero] at hn
    exact (pow_pos h0 n).ne hn
  letI : Algebra ℚ_[p] Ω := (IsFractionRing.lift (K := ℚ_[p]) hinj).toAlgebra
  haveI : IsScalarTower ℤ_[p] ℚ_[p] Ω := IsScalarTower.of_algebraMap_eq fun z =>
    (IsFractionRing.lift_algebraMap hinj z).symm
  have halg' : ∀ x : Ω, IsAlgZp p x ↔ IsAlgebraic ℚ_[p] x := fun x =>
    (halg x).trans (IsFractionRing.isAlgebraic_iff ℤ_[p] ℚ_[p] Ω)
  let L := IntermediateField.adjoin ℚ_[p] (j '' (S : Set K))
  haveI : Finite (j '' (S : Set K)) := (S.finite_toSet.image j).to_subtype
  haveI : FiniteDimensional ℚ_[p] L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨t, -, rfl⟩
    exact ((halg' _).1 (hj t)).isIntegral)
  have hL : ∀ x : L, IsAlgZp p (x : Ω) := fun x =>
    (halg' _).2 (IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic x))
  have hf : ∀ z, ((OkBasis.fromInt p L z : L) : Ω) = zp Ω z := fun z =>
    (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] Ω z).symm.trans (hzp z).symm
  have hmem : ∀ x ∈ IntermediateField.adjoin ℚ (S : Set K), j x ∈ L := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap q => rw [eq_ratCast, map_ratCast]; exact SubfieldClass.ratCast_mem L q
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let w : Valuation L ℝ≥0 := v.comap (algebraMap L Ω)
  have hw : ∀ x : L, w x = v (x : Ω) := fun x => rfl
  have hwp : w (p : L) = v (p : Ω) := by rw [hw]; simp
  obtain ⟨E, F, π, κ, hE, hπ, hκ, -, hsp⟩ := OkBasis.exists_basis (p := p) w
    (fun z => by rw [hw, hf, hzp]; exact hle z) (hwp ▸ h0) (hwp ▸ h1)
  have hπ1 : w π ≤ 1 := by
    by_contra h
    exact absurd (hπ ▸ one_le_pow₀ (not_le.1 h).le) (not_le.2 (hwp ▸ h1))
  choose lam hlam using fun r => hsp ⟨j (C.coeff r), hmem _ (hC r).2⟩ ((hv _).2 (hC r).1)
  let a : Fin F × Fin E → Lau p := fun i =>
    ⟨fun r => if C.coeff r = 0 then 0 else lam r i.1 i.2, C.isPWO_support.mono fun r hr h => hr (if_pos h)⟩
  refine ⟨_, _, EvRing.ev_of_fintype ψ _ _ _ (fun i : Fin F × Fin E => ((κ i.1 * π ^ (i.2 : ℕ) : L) : Ω)) a
    (fun i => ⟨(hv _).1 ?_, hL _⟩) (fun r => ?_) rfl rfl⟩
  · rw [← hw, map_mul, map_pow]
    exact mul_le_one' (hκ _) (pow_le_one' hπ1 _)
  · by_cases h : C.coeff r = 0
    · simp [a, h, hzp]
    · have := congrArg (fun x : L => (x : Ω)) (hlam r)
      push_cast at this
      simp only [a, if_neg h, Fintype.sum_prod_type]
      push_cast
      simpa only [hf] using this

section Val
variable {Ω : Type} [Field Ω] {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

def IsVal (j : Ω →+* Ωl) (n : ℕ) (ψ : O0 p →+* Ωl) (φ : HahnSeries ℚ Ω) (x : Ωl) : Prop :=
  ∃ x', Ev ψ (fun r : ℤ => j (φ.coeff ((r : ℚ) / (p : ℚ) ^ n))) x x'

def Supp (p n : ℕ) (φ : HahnSeries ℚ Ω) : Prop := ∀ r : ℚ, φ.coeff r ≠ 0 → (r * ((p ^ n : ℕ) : ℚ)).den = 1

variable {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl} {T : GlobalTheory.K5.Tower p Ωl}

theorem castM (p n : ℕ) : ((p ^ n : ℕ) : ℚ) = (p : ℚ) ^ n := by push_cast; ring

theorem val_uniq (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) {φ : HahnSeries ℚ Ω} {x y : Ωl}
    (hx : IsVal j n ψ φ x) (hy : IsVal j n ψ φ y) : x = y := by
  obtain ⟨x', hx⟩ := hx
  obtain ⟨y', hy⟩ := hy
  exact (GlobalTheory.EvUniq.ev_unique p Ωl hclo T n ψ hreb _ x x' y y' hx hy).1

theorem val_zero : IsVal j n ψ (0 : HahnSeries ℚ Ω) 0 :=
  ⟨0, 0, finZeroElim, finZeroElim, fun t => t.elim0, fun r => by simp, by simp, by simp⟩

theorem val_one : IsVal j n ψ (1 : HahnSeries ℚ Ω) 1 := by
  refine ⟨0, 1, fun _ => 1, fun _ => 1, fun _ => ⟨isIntegral_one, ?_⟩, fun r => ?_, by simp, ?_⟩
  · refine ⟨Polynomial.X - 1, Polynomial.X_sub_C_ne_zero 1, by simp⟩
  · simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, HahnSeries.coeff_one, zp]
    by_cases hr : r = 0
    · subst hr; simp [HahnSeries.single_zero_one]
    · have : (r : ℚ) / (p : ℚ) ^ n ≠ 0 := div_ne_zero (by exact_mod_cast hr)
        (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
      simp [hr, this]
  · have : thL (1 : Lau p) = 0 := by
      ext r
      simp only [thL, HahnSeries.coeff_one, HahnSeries.coeff_zero]
      split_ifs with h <;> simp [h]
    simp [this]

theorem val_add (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) {φ χ : HahnSeries ℚ Ω} {x y : Ωl}
    (hx : IsVal j n ψ φ x) (hy : IsVal j n ψ χ y) : IsVal j n ψ (φ + χ) (x + y) := by
  obtain ⟨x', hx⟩ := hx
  obtain ⟨y', hy⟩ := hy
  have R := GlobalTheory.Glue.EvRing.ev_ring p Ωl hclo T n ψ hreb
  obtain ⟨C, hC⟩ := (R.2 _ _ _ hx).2.2.1
  obtain ⟨D, hD⟩ := (R.2 _ _ _ hy).2.2.1
  have h := (R.1 C D x x' y y' (hC ▸ hx) (hD ▸ hy)).2.1
  refine ⟨x' + y', ?_⟩
  convert h using 1
  funext r
  simp only [HahnSeries.coeff_add, hC, hD, map_add]

theorem val_mul (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) {φ χ : HahnSeries ℚ Ω} {x y : Ωl}
    (hφ : Supp p n φ) (hχ : Supp p n χ)
    (hx : IsVal j n ψ φ x) (hy : IsVal j n ψ χ y) : IsVal j n ψ (φ * χ) (x * y) := by
  obtain ⟨x', hx⟩ := hx
  obtain ⟨y', hy⟩ := hy
  have R := GlobalTheory.Glue.EvRing.ev_ring p Ωl hclo T n ψ hreb
  obtain ⟨C, hC⟩ := (R.2 _ _ _ hx).2.2.1
  obtain ⟨D, hD⟩ := (R.2 _ _ _ hy).2.2.1
  have h := (R.1 C D x x' y y' (hC ▸ hx) (hD ▸ hy)).1
  refine ⟨x' * y + x * y', ?_⟩
  convert h using 1
  funext r
  have hp : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have key := restrict_mul j hp φ χ C D hφ hχ
    (fun r => by rw [hC, castM]) (fun r => by rw [hD, castM]) r
  rw [key, castM]

theorem algMapC (l : Ω) : algebraMap Ω (HahnSeries ℚ Ω) l = HahnSeries.C l := by
  rw [HahnSeries.algebraMap_apply']; simp

theorem coeff_algebraMap_mul (l : Ω) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) l * φ).coeff r = l * φ.coeff r := by
  rw [algMapC, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem val_smul (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) {φ : HahnSeries ℚ Ω} {x : Ωl} (l : Ω)
    (hi : IsInt p (j l)) (ha : IsAlgZp p (j l))
    (hx : IsVal j n ψ φ x) : IsVal j n ψ (algebraMap Ω (HahnSeries ℚ Ω) l * φ) (j l * x) := by
  obtain ⟨x', hx⟩ := hx
  have R := GlobalTheory.Glue.EvRing.ev_ring p Ωl hclo T n ψ hreb
  have h := (R.2 _ _ _ hx).2.2.2.2.1 (j l) hi ha
  refine ⟨j l * x', ?_⟩
  convert h using 1
  funext r
  rw [coeff_algebraMap_mul, map_mul]

theorem val_gal (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) {φ φ' : HahnSeries ℚ Ω} {x : Ωl}
    (g : Gal p Ωl) (s : Ω → Ω) (hq : g (T.qq n) = T.qq n) (hgs : ∀ z, g (j z) = j (s z))
    (hφ : ∀ r, φ'.coeff r = s (φ.coeff r))
    (hx : IsVal j n ψ φ x) : IsVal j n ψ φ' (g x) := by
  obtain ⟨x', hx⟩ := hx
  have R := GlobalTheory.Glue.EvRing.ev_ring p Ωl hclo T n ψ hreb
  have h := (R.2 _ _ _ hx).2.2.2.2.2 g hq
  refine ⟨g x', ?_⟩
  convert h using 1
  funext r
  rw [hφ, hgs]

theorem val_ne (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) {A : ValuationSubring Ω}
    (hint : ∀ z, z ∈ A ↔ IsInt p (j z)) {φ : HahnSeries ℚ Ω} {x : Ωl}
    (hP : Prim A φ) (hs : Supp p n φ) (hx : IsVal j n ψ φ x) : x ≠ 0 := by
  obtain ⟨x', hx⟩ := hx
  obtain ⟨-, r0, h0, hinv⟩ := hP
  have hd := hs r0 h0
  have hpn : ((p ^ n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (pow_pos (Fact.out : p.Prime).pos n).ne'
  have hm : (((r0 * ((p ^ n : ℕ) : ℚ)).num : ℤ) : ℚ) / (p : ℚ) ^ n = r0 := by
    rw [← castM, (Rat.den_eq_one_iff _).1 hd, mul_div_cancel_right₀ _ hpn]
  refine (GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ωl hclo T n ψ hreb 0 _ x x' hx).2 ⟨(r0 * ((p ^ n : ℕ) : ℚ)).num, ?_, ?_⟩ |>.1
  · simp only [hm]; exact (map_ne_zero j).2 h0
  · simp only [hm]; rw [← map_inv₀]; exact (hint _).1 hinv

end Val

section Glob

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def RS (A : ValuationSubring Ω) (S : Finset Ω) : Subring Ω :=
  A.toSubring ⊓ (IntermediateField.adjoin ℚ (S : Set Ω)).toSubalgebra.toSubring

theorem mem_RS {A : ValuationSubring Ω} {S : Finset Ω} {z : Ω} :
    z ∈ RS A S ↔ z ∈ A ∧ z ∈ IntermediateField.adjoin ℚ (S : Set Ω) := Iff.rfl

theorem RS_mono {A : ValuationSubring Ω} {S S' : Finset Ω} (h : S ⊆ S') : RS A S ≤ RS A S' :=
  fun _ hz => ⟨hz.1, IntermediateField.adjoin.mono ℚ _ _ (by exact_mod_cast h) hz.2⟩

theorem coeff_mul_mem (R : Subring Ω) {φ χ : HahnSeries ℚ Ω} (h1 : ∀ r, φ.coeff r ∈ R)
    (h2 : ∀ r, χ.coeff r ∈ R) (r : ℚ) : (φ * χ).coeff r ∈ R := by
  rw [HahnSeries.coeff_mul]
  exact R.sum_mem fun i _ => R.mul_mem (h1 _) (h2 _)

theorem coeff_one_mem (R : Subring Ω) (r : ℚ) : (1 : HahnSeries ℚ Ω).coeff r ∈ R := by
  rw [HahnSeries.coeff_one]
  split_ifs
  exacts [R.one_mem, R.zero_mem]

theorem alg_mem_KT (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (l : Ω) : algebraMap Ω X.K l ∈ KT X L := by
  rw [KT, RingHom.mem_eqLocusField]
  exact (X.sl _).commutes l

theorem gal_alg (X : GlobalTheory.KZ.Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (κ : Ω) :
    X.gal s (algebraMap Ω X.K κ) = algebraMap Ω X.K (s κ) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  show (X.exp (X.gal s _)).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes, algMapC, algMapC, HahnSeries.C_apply,
    HahnSeries.C_apply, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem mem_KT_iff' [IsAlgClosure ℚ Ω] (X : GlobalTheory.KZ.Tower Ω ε) (p n : ℕ) [Fact p.Prime] (a : X.K) :
    a ∈ KT X (p ^ n) ↔ Supp p n (X.exp a) :=
  GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) a

def Good (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) (p n : ℕ) (y a b : X.K) (κ : Ω) (S : Finset Ω) : Prop :=
  κ ≠ 0 ∧ a ∈ KT X (p ^ n) ∧ b ∈ KT X (p ^ n) ∧ y * b = algebraMap Ω X.K κ * a ∧
    ∀ r, (X.exp a).coeff r ∈ RS A S ∧ (X.exp b).coeff r ∈ RS A S

def IsQ (X : GlobalTheory.KZ.Tower Ω ε) (A : ValuationSubring Ω) {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl]
    [Algebra (O0 p) Ωl] (j : Ω →+* Ωl) (n : ℕ) (ψ : O0 p →+* Ωl) (y : X.K) (v : Ωl) : Prop :=
  ∃ (a b : X.K) (κ : Ω) (S : Finset Ω) (xa xb : Ωl), Good X A p n y a b κ S ∧ IsVal j n ψ (X.exp a) xa ∧
    IsVal j n ψ (X.exp b) xb ∧ xb ≠ 0 ∧ v = j κ * xa / xb

variable [IsAlgClosure ℚ Ω] {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {p : ℕ} [Fact p.Prime]
  {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl] {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl} {T : GlobalTheory.K5.Tower p Ωl}

theorem supp_exp {a : X.K} (ha : a ∈ KT X (p ^ n)) : Supp p n (X.exp a) := (mem_KT_iff' X p n a).1 ha

omit [IsAlgClosure ℚ Ω] in
theorem val_exists (hclo : IsClo p Ωl) (hint : ∀ z, z ∈ A ↔ IsInt p (j z)) (halg : ∀ z, IsAlgZp p (j z))
    {φ : HahnSeries ℚ Ω} {S : Finset Ω} (hc : ∀ r, φ.coeff r ∈ RS A S) : ∃ x, IsVal j n ψ φ x := by
  obtain ⟨C, hC⟩ := exists_restrict (pow_pos (Fact.out : p.Prime).pos n) φ
  obtain ⟨x, x', h⟩ := exists_ev hclo ψ j halg S C
    (fun r => ⟨by rw [hC r]; exact (hint _).1 (hc _).1, by rw [hC r]; exact (hc _).2⟩)
  have e : (fun r : ℤ => j (C.coeff r)) = fun r : ℤ => j (φ.coeff ((r : ℚ) / (p : ℚ) ^ n)) := by
    funext r; rw [hC, castM]
  rw [e] at h
  exact ⟨x, x', h⟩

theorem cross (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) (hint : ∀ z, z ∈ A ↔ IsInt p (j z))
    (halg : ∀ z, IsAlgZp p (j z)) {y a b a' b' : X.K} {κ κ' : Ω} {S S' : Finset Ω} {xa xb xa' xb' : Ωl}
    (hG : Good X A p n y a b κ S) (hG' : Good X A p n y a' b' κ' S') (hl : κ' / κ ∈ A)
    (ha : IsVal j n ψ (X.exp a) xa) (hb : IsVal j n ψ (X.exp b) xb)
    (ha' : IsVal j n ψ (X.exp a') xa') (hb' : IsVal j n ψ (X.exp b') xb') :
    j κ * xa * xb' = j κ' * xa' * xb := by
  obtain ⟨hκ, haK, hbK, hrel, -⟩ := hG
  obtain ⟨hκ', haK', hbK', hrel', -⟩ := hG'
  have hκl : κ * (κ' / κ) = κ' := by field_simp
  have hK : a * b' = algebraMap Ω X.K (κ' / κ) * (a' * b) := by
    have h1 : algebraMap Ω X.K κ * (a * b') = algebraMap Ω X.K κ * (algebraMap Ω X.K (κ' / κ) * (a' * b)) := by
      rw [← mul_assoc (algebraMap Ω X.K κ) (algebraMap Ω X.K (κ' / κ)), ← map_mul, hκl]
      calc algebraMap Ω X.K κ * (a * b') = (algebraMap Ω X.K κ * a) * b' := by ring
        _ = (y * b) * b' := by rw [hrel]
        _ = (y * b') * b := by ring
        _ = (algebraMap Ω X.K κ' * a') * b := by rw [hrel']
        _ = algebraMap Ω X.K κ' * (a' * b) := by ring
    exact mul_left_cancel₀ ((map_ne_zero _).2 hκ) h1
  have v1 : IsVal j n ψ (X.exp (a * b')) (xa * xb') := by
    rw [map_mul]; exact val_mul hclo hreb (supp_exp haK) (supp_exp hbK') ha hb'
  have v2 : IsVal j n ψ (X.exp (algebraMap Ω X.K (κ' / κ) * (a' * b))) (j (κ' / κ) * (xa' * xb)) := by
    rw [map_mul, AlgHom.commutes, map_mul]
    exact val_smul hclo hreb _ ((hint _).1 hl) (halg _)
      (val_mul hclo hreb (supp_exp haK') (supp_exp hbK) ha' hb)
  rw [hK] at v1
  have e := val_uniq hclo hreb v1 v2
  rw [← hκl, map_mul]
  linear_combination (j κ) * e

theorem isQ_uniq (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) (hint : ∀ z, z ∈ A ↔ IsInt p (j z))
    (halg : ∀ z, IsAlgZp p (j z)) {y : X.K} {v w : Ωl}
    (hv : IsQ X A j n ψ y v) (hw : IsQ X A j n ψ y w) : v = w := by
  obtain ⟨a, b, κ, S, xa, xb, hG, ha, hb, hxb, rfl⟩ := hv
  obtain ⟨a', b', κ', S', xa', xb', hG', ha', hb', hxb', rfl⟩ := hw
  rw [div_eq_div_iff hxb hxb']
  rcases A.mem_or_inv_mem (κ' / κ) with h | h
  · exact cross hclo hreb hint halg hG hG' h ha hb ha' hb'
  · rw [inv_div] at h
    exact (cross hclo hreb hint halg hG' hG h ha' hb' ha hb).symm

theorem isQ_mul (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) {y1 y2 : X.K} {v1 v2 : Ωl}
    (h1 : IsQ X A j n ψ y1 v1) (h2 : IsQ X A j n ψ y2 v2) : IsQ X A j n ψ (y1 * y2) (v1 * v2) := by
  classical
  obtain ⟨a1, b1, κ1, S1, xa1, xb1, ⟨hκ1, ha1K, hb1K, hr1, hc1⟩, ha1, hb1, hxb1, rfl⟩ := h1
  obtain ⟨a2, b2, κ2, S2, xa2, xb2, ⟨hκ2, ha2K, hb2K, hr2, hc2⟩, ha2, hb2, hxb2, rfl⟩ := h2
  refine ⟨a1 * a2, b1 * b2, κ1 * κ2, S1 ∪ S2, xa1 * xa2, xb1 * xb2,
    ⟨mul_ne_zero hκ1 hκ2, mul_mem ha1K ha2K, mul_mem hb1K hb2K, ?_, fun r => ⟨?_, ?_⟩⟩, ?_, ?_,
    mul_ne_zero hxb1 hxb2, ?_⟩
  · rw [map_mul]
    linear_combination (y2 * b2) * hr1 + (algebraMap Ω X.K κ1 * a1) * hr2
  · rw [map_mul]
    exact coeff_mul_mem _ (fun r => RS_mono Finset.subset_union_left (hc1 r).1)
      (fun r => RS_mono Finset.subset_union_right (hc2 r).1) r
  · rw [map_mul]
    exact coeff_mul_mem _ (fun r => RS_mono Finset.subset_union_left (hc1 r).2)
      (fun r => RS_mono Finset.subset_union_right (hc2 r).2) r
  · rw [map_mul]; exact val_mul hclo hreb (supp_exp ha1K) (supp_exp ha2K) ha1 ha2
  · rw [map_mul]; exact val_mul hclo hreb (supp_exp hb1K) (supp_exp hb2K) hb1 hb2
  · rw [map_mul]
    field_simp

theorem isLocalValueOfQuotient_add_of_common_denominator (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) (hint : ∀ z, z ∈ A ↔ IsInt p (j z))
    (halg : ∀ z, IsAlgZp p (j z)) {y1 y2 a1 b1 a2 b2 : X.K} {κ1 κ2 : Ω} {S1 S2 : Finset Ω}
    {xa1 xb1 xa2 xb2 : Ωl} (hG1 : Good X A p n y1 a1 b1 κ1 S1) (hG2 : Good X A p n y2 a2 b2 κ2 S2)
    (ha1 : IsVal j n ψ (X.exp a1) xa1) (hb1 : IsVal j n ψ (X.exp b1) xb1)
    (ha2 : IsVal j n ψ (X.exp a2) xa2) (hb2 : IsVal j n ψ (X.exp b2) xb2)
    (hxb1 : xb1 ≠ 0) (hxb2 : xb2 ≠ 0) (hl : κ2 / κ1 ∈ A) :
    IsQ X A j n ψ (y1 + y2) (j κ1 * xa1 / xb1 + j κ2 * xa2 / xb2) := by
  classical
  obtain ⟨hκ1, ha1K, hb1K, hr1, hc1⟩ := hG1
  obtain ⟨hκ2, ha2K, hb2K, hr2, hc2⟩ := hG2
  have hκl : κ1 * (κ2 / κ1) = κ2 := by field_simp
  have hκl' : algebraMap Ω X.K κ1 * algebraMap Ω X.K (κ2 / κ1) = algebraMap Ω X.K κ2 := by
    rw [← map_mul, hκl]
  have s1 : S1 ⊆ S1 ∪ S2 ∪ {κ2 / κ1} := Finset.subset_union_left.trans Finset.subset_union_left
  have s2 : S2 ⊆ S1 ∪ S2 ∪ {κ2 / κ1} := Finset.subset_union_right.trans Finset.subset_union_left
  have hlR : κ2 / κ1 ∈ RS A (S1 ∪ S2 ∪ {κ2 / κ1}) :=
    ⟨hl, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  refine ⟨a1 * b2 + algebraMap Ω X.K (κ2 / κ1) * (a2 * b1), b1 * b2, κ1, S1 ∪ S2 ∪ {κ2 / κ1},
    xa1 * xb2 + j (κ2 / κ1) * (xa2 * xb1), xb1 * xb2,
    ⟨hκ1, ?_, mul_mem hb1K hb2K, ?_, fun r => ⟨?_, ?_⟩⟩, ?_, ?_, mul_ne_zero hxb1 hxb2, ?_⟩
  · exact add_mem (mul_mem ha1K hb2K) (mul_mem (alg_mem_KT X _ _) (mul_mem ha2K hb1K))
  · linear_combination b2 * hr1 + b1 * hr2 - (a2 * b1) * hκl'
  · rw [map_add, map_mul, map_mul, AlgHom.commutes, map_mul, HahnSeries.coeff_add, coeff_algebraMap_mul]
    exact add_mem (coeff_mul_mem _ (fun r => RS_mono s1 (hc1 r).1) (fun r => RS_mono s2 (hc2 r).2) r)
      (mul_mem hlR (coeff_mul_mem _ (fun r => RS_mono s2 (hc2 r).1) (fun r => RS_mono s1 (hc1 r).2) r))
  · rw [map_mul]
    exact coeff_mul_mem _ (fun r => RS_mono s1 (hc1 r).2) (fun r => RS_mono s2 (hc2 r).2) r
  · rw [map_add, map_mul, map_mul, AlgHom.commutes, map_mul]
    exact val_add hclo hreb (val_mul hclo hreb (supp_exp ha1K) (supp_exp hb2K) ha1 hb2)
      (val_smul hclo hreb _ ((hint _).1 hl) (halg _)
        (val_mul hclo hreb (supp_exp ha2K) (supp_exp hb1K) ha2 hb1))
  · rw [map_mul]; exact val_mul hclo hreb (supp_exp hb1K) (supp_exp hb2K) hb1 hb2
  · have e : j κ2 = j κ1 * j (κ2 / κ1) := by rw [← map_mul, hκl]
    rw [e]
    field_simp

theorem isQ_add (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) (hint : ∀ z, z ∈ A ↔ IsInt p (j z))
    (halg : ∀ z, IsAlgZp p (j z)) {y1 y2 : X.K} {v1 v2 : Ωl}
    (h1 : IsQ X A j n ψ y1 v1) (h2 : IsQ X A j n ψ y2 v2) : IsQ X A j n ψ (y1 + y2) (v1 + v2) := by
  obtain ⟨a1, b1, κ1, S1, xa1, xb1, hG1, ha1, hb1, hxb1, rfl⟩ := h1
  obtain ⟨a2, b2, κ2, S2, xa2, xb2, hG2, ha2, hb2, hxb2, rfl⟩ := h2
  rcases A.mem_or_inv_mem (κ2 / κ1) with h | h
  · exact isLocalValueOfQuotient_add_of_common_denominator hclo hreb hint halg hG1 hG2 ha1 hb1 ha2 hb2 hxb1 hxb2 h
  · rw [inv_div] at h
    rw [add_comm y1 y2, add_comm (j κ1 * xa1 / xb1)]
    exact isLocalValueOfQuotient_add_of_common_denominator hclo hreb hint halg hG2 hG1 ha2 hb2 ha1 hb1 hxb2 hxb1 h

theorem isQ_zero : IsQ X A j n ψ 0 0 :=
  ⟨0, 1, 1, ∅, 0, 1, ⟨one_ne_zero, zero_mem _, one_mem _, by simp,
    fun r => ⟨by rw [map_zero, HahnSeries.coeff_zero]; exact zero_mem _,
      by rw [map_one]; exact coeff_one_mem _ r⟩⟩,
    by rw [map_zero]; exact val_zero, by rw [map_one]; exact val_one, one_ne_zero, by simp⟩

theorem isQ_one : IsQ X A j n ψ 1 1 :=
  ⟨1, 1, 1, ∅, 1, 1, ⟨one_ne_zero, one_mem _, one_mem _, by simp,
    fun r => ⟨by rw [map_one]; exact coeff_one_mem _ r, by rw [map_one]; exact coeff_one_mem _ r⟩⟩,
    by rw [map_one]; exact val_one, by rw [map_one]; exact val_one, one_ne_zero, by simp⟩

theorem isQ_exists (hX : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero))
    (hpA : ((p : ℕ) : Ω) ∈ A.nonunits) (hclo : IsClo p Ωl) (hreb : IsReb T n ψ)
    (hint : ∀ z, z ∈ A ↔ IsInt p (j z)) (halg : ∀ z, IsAlgZp p (j z)) (y : X.K) (hy : y ∈ KT X (p ^ n)) :
    ∃ v, IsQ X A j n ψ y v := by
  by_cases h0 : y = 0
  · exact ⟨0, h0 ▸ isQ_zero⟩
  obtain ⟨a, b, κ, S, hκ, hrel, hPa, hPb, hinv, hS⟩ := GlobalTheory.T.exists_primitive_expansion_quotient_level_one ε X hX p A hpA y h0
  have hbK : b ∈ KT X (p ^ n) := by
    rw [KT, RingHom.mem_eqLocusField]
    exact hinv _
  have haK : a ∈ KT X (p ^ n) := by
    have e : a = algebraMap Ω X.K κ⁻¹ * (y * b) := by
      rw [hrel, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hκ, map_one, one_mul]
    rw [e]
    exact mul_mem (alg_mem_KT X _ _) (mul_mem hy hbK)
  have hca : ∀ r, (X.exp a).coeff r ∈ RS A S := fun r => ⟨hPa.1 r, (hS r).1⟩
  have hcb : ∀ r, (X.exp b).coeff r ∈ RS A S := fun r => ⟨hPb.1 r, (hS r).2⟩
  obtain ⟨xa, hxa⟩ := val_exists (n := n) (ψ := ψ) hclo hint halg hca
  obtain ⟨xb, hxb⟩ := val_exists (n := n) (ψ := ψ) hclo hint halg hcb
  exact ⟨_, a, b, κ, S, xa, xb, ⟨hκ, haK, hbK, hrel, fun r => ⟨hca r, hcb r⟩⟩, hxa, hxb,
    val_ne hclo hreb hint hPb (supp_exp hbK) hxb, rfl⟩

theorem isQ_gal (hclo : IsClo p Ωl) (hreb : IsReb T n ψ) (hint : ∀ z, z ∈ A ↔ IsInt p (j z))
    (g : Gal p Ωl) (s : Ω ≃ₐ[ℚ] Ω) (hq : g (T.qq n) = T.qq n) (hgs : ∀ x, g (j x) = j (s x))
    {y : X.K} {v : Ωl} (h : IsQ X A j n ψ y v) : IsQ X A j n ψ (X.gal s y) (g v) := by
  classical
  obtain ⟨a, b, κ, S, xa, xb, ⟨hκ, haK, hbK, hrel, hc⟩, ha, hb, hxb, rfl⟩ := h
  have hA : ∀ z ∈ A, s z ∈ A := fun z hz =>
    (hint _).2 (by rw [← hgs]; exact GlobalTheory.K5.Basic.isInt_gal g ((hint z).1 hz))
  have hS : ∀ z ∈ IntermediateField.adjoin ℚ (S : Set Ω),
      s z ∈ IntermediateField.adjoin ℚ ((S.image s : Finset Ω) : Set Ω) := by
    intro z hz
    have e := IntermediateField.adjoin_map ℚ (S : Set Ω) (s : Ω →ₐ[ℚ] Ω)
    rw [Finset.coe_image]
    exact e.le ⟨z, hz, rfl⟩
  have hR : ∀ z ∈ RS A S, s z ∈ RS A (S.image s) := fun z hz => ⟨hA z hz.1, hS z hz.2⟩
  have hKT : ∀ c ∈ KT X (p ^ n), X.gal s c ∈ KT X (p ^ n) := by
    intro c hc
    rw [mem_KT_iff'] at hc ⊢
    intro r hr
    apply hc r
    intro h0
    apply hr
    rw [X.gal_exp, h0, map_zero]
  refine ⟨X.gal s a, X.gal s b, s κ, S.image s, g xa, g xb,
    ⟨(map_ne_zero s).2 hκ, hKT a haK, hKT b hbK, ?_, fun r => ⟨?_, ?_⟩⟩,
    val_gal hclo hreb g s hq hgs (X.gal_exp s a) ha, val_gal hclo hreb g s hq hgs (X.gal_exp s b) hb,
    (map_ne_zero g).2 hxb, ?_⟩
  · rw [← map_mul, hrel, map_mul, gal_alg]
  · rw [X.gal_exp]; exact hR _ (hc r).1
  · rw [X.gal_exp]; exact hR _ (hc r).2
  · rw [map_div₀, map_mul, hgs]

end Glob

theorem exists_isIo : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∀ (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j → ∀ (n : ℕ) (ψ : O0 p →+* Ωl), IsReb T n ψ → ∃ io : KT X (p ^ n) →+* Ωl, IsIo X A T j n ψ io := by
  intro Ω _ _ _ ε X hX p _ _ A hpA Ωl _ _ hclo T j hcusp n ψ hreb
  have hint := hcusp.int
  have halg := hcusp.alg
  choose io hio using fun y : KT X (p ^ n) => isQ_exists hX hpA hclo hreb hint halg (y : X.K) y.2
  refine ⟨{ toFun := io
            map_one' := isQ_uniq hclo hreb hint halg (hio 1) isQ_one
            map_mul' := fun y1 y2 =>
              isQ_uniq hclo hreb hint halg (hio (y1 * y2)) (isQ_mul hclo hreb (hio y1) (hio y2))
            map_zero' := isQ_uniq hclo hreb hint halg (hio 0) isQ_zero
            map_add' := fun y1 y2 =>
              isQ_uniq hclo hreb hint halg (hio (y1 + y2)) (isQ_add hclo hreb hint halg (hio y1) (hio y2)) }, ?_, ?_⟩
  · intro y S hy
    obtain ⟨x, hx⟩ := val_exists (n := n) (ψ := ψ) hclo hint halg (S := S) (fun r => mem_RS.2 (hy r))
    have hQ : IsQ X A j n ψ (y : X.K) x :=
      ⟨y, 1, 1, S, x, 1, ⟨one_ne_zero, y.2, one_mem _, by simp,
        fun r => ⟨mem_RS.2 (hy r), by rw [map_one]; exact coeff_one_mem _ r⟩⟩, hx,
        by rw [map_one]; exact val_one, one_ne_zero, by simp⟩
    rw [← isQ_uniq hclo hreb hint halg (hio y) hQ] at hx
    exact hx
  · intro g s hq hgs y y' hy'
    have h1 := isQ_gal hclo hreb hint g s hq hgs (hio y)
    rw [← hy'] at h1
    exact isQ_uniq hclo hreb hint halg h1 (hio y')

end GlobalTheory.IoEx
