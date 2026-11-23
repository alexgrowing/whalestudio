import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalAcrisToBdRPlusUniqueEquivariantApproxStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section
namespace GlobalTheory.MemLoc.Model
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem exists_zeta (l : ℕ) [Fact l.Prime] :
    ∃ ζ : ℕ → Om l, ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 := by
  have hl : l.Prime := Fact.out
  have : NeZero ((l : ℕ) : Om l) := ⟨Nat.cast_ne_zero.2 hl.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic l (Om l))
    (ne_of_gt (Polynomial.degree_cyclotomic_pos l (Om l) hl.pos))
  have hzp : IsPrimitiveRoot z l := Polynomial.isRoot_cyclotomic_iff.1 hz
  choose r hr using fun x : Om l => IsAlgClosed.exists_pow_nat_eq x hl.pos
  refine ⟨fun n => Nat.casesOn n 1 (fun m => r^[m] z), rfl, ?_, hzp.ne_one hl.one_lt⟩
  intro n
  cases n with
  | zero => exact hzp.pow_eq_one
  | succ m =>
    show (r^[m + 1] z) ^ l = r^[m] z
    rw [Function.iterate_succ_apply', hr]

theorem rootT_ofRoots (f : ℕ → Per.OC l) (hf : ∀ n, f (n + 1) ^ l = f n) (m : ℕ) :
    rootT (ReciprocityTheory.PGsh.ofRoots f hf) m = f m := by
  have := ReciprocityTheory.PGsh.untilt_eq_of_coeff
    (((frobeniusEquiv (Per.Fl l) l).symm)^[m] (ReciprocityTheory.PGsh.ofRoots f hf))
    (fun n => f (n + m)) (fun n => by rw [Nat.add_right_comm]; exact hf _) (by
      intro n
      rw [← PreTilt.coeff_def, PreTilt.coeff_iterate_frobeniusEquiv_symm, PreTilt.coeff_def]
      rfl)
  simpa [rootT] using this

theorem exists_tilt (ζ : ℕ → Om l) (h0 : ζ 0 = 1) (hs : ∀ m, ζ (m + 1) ^ l = ζ m) :
    ∃ ε : Per.Fl l, ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  have hl : l.Prime := Fact.out
  have hn : ∀ m, ‖algebraMap (Om l) ℂ_[l] (ζ m)‖ ≤ 1 := by
    intro m
    induction m with
    | zero => simp [h0]
    | succ m ih =>
      rw [← hs m, map_pow, norm_pow] at ih
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hl.ne_zero).1 ih
  let f : ℕ → Per.OC l := fun m => ⟨_, (GlobalTheory.RingBasics.mem_OC _).2 (hn m)⟩
  have hf : ∀ n, f (n + 1) ^ l = f n := fun n => Subtype.ext (by
    show (algebraMap (Om l) ℂ_[l] (ζ (n + 1))) ^ l = algebraMap (Om l) ℂ_[l] (ζ n)
    rw [← map_pow, hs])
  exact ⟨ReciprocityTheory.PGsh.ofRoots f hf, fun m => by rw [rootT_ofRoots]⟩

theorem isEps_of_root {ζ : ℕ → Om l} (h0 : ζ 0 = 1) (h1 : ζ 1 ≠ 1) {ε : Per.Fl l}
    (h : ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m)) : IsEps ε := by
  refine ⟨Subtype.ext ?_, fun hh => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact this
  · have := h 1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    exact congrArg Subtype.val hh

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, h0, hs, h1⟩ := exists_zeta l
  obtain ⟨ε, h⟩ := exists_tilt ζ h0 hs
  exact ⟨ε, isEps_of_root h0 h1 h⟩

theorem not_isEps_one : ¬ IsEps (1 : Per.Fl l) := fun h => h.2 (by simp)

theorem core_isEps (C : Core l) : IsEps C.ε := isEps_of_root C.ζ_zero C.ζ_one C.ε_root

theorem exists_chi (l : ℕ) [Fact l.Prime] : ∃ χ : GQ l →* ℤ_[l]ˣ, ∀ (g : GQ l) (m : ℕ) (x : Om l),
    x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val :=
  ⟨(cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l)),
    fun g m x hx => cyclotomicCharacter.spec l (n := m) (MulSemiringAction.toRingAut (GQ l) (Om l) g) x hx⟩

theorem mu_eq (e : Per.Fl l) : mu e = xi e * mu ((frobeniusEquiv (Per.Fl l) l).symm e) := by
  rw [xi, mu, mu, geom_sum_mul, ← map_pow]
  congr 2
  exact ((frobeniusEquiv (Per.Fl l) l).apply_symm_apply e).symm

theorem theta_mu (e : Per.Fl l) : Per.θ l (mu e) = e.untilt - 1 := by
  simp [mu]

theorem theta_xi {e : Per.Fl l} (h : IsEps e) : Per.θ l (xi e) = 0 := by
  have h1 := congrArg (Per.θ l) (mu_eq e)
  rw [map_mul, theta_mu, theta_mu, h.1, sub_self] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_right (sub_ne_zero.2 h.2)

theorem core_isCrisDR (C : Core l) : Per.IsCrisDR l C.ι := by
  obtain ⟨ι, hι⟩ := GlobalTheory.CrisIncl.exists_incl l
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.CrisIncl.exists_restrict l ι hι
  have e : j = C.j := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris).1 j ⟨h2, h3⟩
  have e' : C.ι = ι := GlobalTheory.RingIface.bcris_ext l fun x => by rw [C.ι_j, h1, e]
  rwa [e']

theorem isLogA_one : IsLogA (1 : Per.Fl l) 0 := fun r => ⟨0, fun n _ => ⟨0, by simp [mu], 0, by simp⟩⟩

theorem mem_pc (R : Type) [CommRing R] (r : ℕ) (x : GlobalTheory.AdicMaps.PHat l R) :
    x ∈ ((Ideal.span {(l : R)}) ^ r • ⊤ : Submodule R (GlobalTheory.AdicMaps.PHat l R)) ↔
      ∃ z : GlobalTheory.AdicMaps.PHat l R, x = ((l : ℕ) : GlobalTheory.AdicMaps.PHat l R) ^ r * z := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, by rw [Algebra.smul_def, map_pow, map_natCast]⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, trivial, by rw [Algebra.smul_def, map_pow, map_natCast]⟩

theorem pc_sep (R : Type) [CommRing R] (x : GlobalTheory.AdicMaps.PHat l R)
    (h : ∀ r, ∃ z : GlobalTheory.AdicMaps.PHat l R, x = ((l : ℕ) : GlobalTheory.AdicMaps.PHat l R) ^ r * z) : x = 0 :=
  IsHausdorff.haus (I := Ideal.span {(l : R)}) inferInstance x fun r => by
    rw [SModEq.zero]; exact (mem_pc R r x).2 (h r)

theorem pc_lim (R : Type) [CommRing R] (s : ℕ → R)
    (hs : ∀ r n, l ^ r ≤ n → ∃ z : R, s n - s (l ^ r) = (l : R) ^ r * z) :
    ∃ y : GlobalTheory.AdicMaps.PHat l R, ∀ r n, l ^ r ≤ n →
      ∃ z : GlobalTheory.AdicMaps.PHat l R, y - algebraMap R _ (s n) = ((l : ℕ) : GlobalTheory.AdicMaps.PHat l R) ^ r * z := by
  have hl : l.Prime := Fact.out
  have hc : IsAdicComplete (Ideal.span {(l : R)}) (GlobalTheory.AdicMaps.PHat l R) :=
    AdicCompletion.isAdicComplete ⟨{(l : R)}, by simp⟩
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(l : R)}) (M := GlobalTheory.AdicMaps.PHat l R) hc.toIsPrecomplete
    (f := fun r => algebraMap R _ (s (l ^ r))) (by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pc]
      obtain ⟨z, hz⟩ := hs m (l ^ n) (Nat.pow_le_pow_right hl.pos hmn)
      refine ⟨-algebraMap R _ z, ?_⟩
      rw [← map_sub, ← neg_sub, hz, map_neg, map_mul, map_pow, map_natCast, mul_neg])
  refine ⟨L, fun r n hn => ?_⟩
  have h1 := hL r
  rw [SModEq.sub_mem, mem_pc] at h1
  obtain ⟨z, hz⟩ := h1
  obtain ⟨w, hw⟩ := hs r n hn
  have h2 := congrArg (algebraMap R (GlobalTheory.AdicMaps.PHat l R)) hw
  rw [map_sub, map_mul, map_pow, map_natCast] at h2
  exact ⟨-z - algebraMap R _ w, by linear_combination -hz - h2⟩

private theorem acris_sep (x : Per.Acris l)
    (h : ∀ r, ∃ z : Per.Acris l, x = ((l : ℕ) : Per.Acris l) ^ r * z) : x = 0 := by
  obtain ⟨E, -⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  refine E.injective ?_
  rw [map_zero]
  refine pc_sep (l := l) (Per.Acris0 l) (E x) fun r => ?_
  obtain ⟨z, hz⟩ := h r
  exact ⟨E z, by rw [hz, map_mul, map_pow, map_natCast]⟩

private theorem acris_lim (s : ℕ → Per.Acris0 l)
    (hs : ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris0 l, s n - s (l ^ r) = (l : Per.Acris0 l) ^ r * z) :
    ∃ y : Per.Acris l, ∀ r n, l ^ r ≤ n → ∃ z : Per.Acris l,
      y - algebraMap (Per.Acris0 l) (Per.Acris l) (s n) = ((l : ℕ) : Per.Acris l) ^ r * z := by
  obtain ⟨E, hE⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  obtain ⟨y, hy⟩ := pc_lim (l := l) (Per.Acris0 l) s hs
  refine ⟨E.symm y, fun r n hn => ?_⟩
  obtain ⟨z, hz⟩ := hy r n hn
  refine ⟨E.symm z, E.injective ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, hE, E.apply_symm_apply, E.apply_symm_apply]
  exact hz

theorem isLogA_unique {e : Per.Fl l} {y y' : Per.Acris l} (h : IsLogA e y) (h' : IsLogA e y') : y = y' := by
  rw [← sub_eq_zero]
  refine acris_sep (y - y') fun r => ?_
  obtain ⟨N, hN⟩ := h r
  obtain ⟨N', hN'⟩ := h' r
  obtain ⟨s, hs, z, hz⟩ := hN (max N N') (le_max_left _ _)
  obtain ⟨s', hs', z', hz'⟩ := hN' (max N N') (le_max_right _ _)
  have : s = s' := Subtype.ext
    ((GlobalTheory.RingBasics.isUnit_nat l _ (Nat.factorial_ne_zero _)).mul_left_cancel (hs.trans hs'.symm))
  subst this
  have key : y - y' = ((l : ℕ) : Per.Acris l) ^ r * (z - z') := by linear_combination hz - hz'
  exact ⟨z - z', key⟩

theorem exists_isLogA {e : Per.Fl l} (he : e.untilt = 1) : ∃ y : Per.Acris l, IsLogA e y := by
  have hl : l.Prime := Fact.out
  have hμ : Per.θ l (mu e) = 0 := by rw [theta_mu, he, sub_self]
  have hγ : ∀ k : ℕ, ∃ g : Per.Acris0 l, ((k.factorial : ℕ) : Per.AinfP l) * (g : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ k := by
    intro k
    obtain ⟨d, hd⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero).exists_right_inv
    have : ((k.factorial : ℕ) : Per.AinfP l) * (d * algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ k) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ k := by rw [← mul_assoc, hd, one_mul]
    exact ⟨⟨_, GlobalTheory.RingIface.mem_Acris0_of_factorial_mul l (mu e) hμ k _ this⟩, this⟩
  choose g hg using hγ
  let s : ℕ → Per.Acris0 l := fun n =>
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * g (k + 1)
  obtain ⟨y, hy⟩ := acris_lim (l := l) s (by
    intro r n hn
    have : ((l : ℕ) : Per.Acris0 l) ^ r ∣ s n - s (l ^ r) := by
      simp only [s]
      rw [← Finset.sum_Ico_eq_sub _ hn]
      refine Finset.dvd_sum fun k hk => ?_
      have h1 : l ^ r ∣ k.factorial := Nat.dvd_factorial (pow_pos hl.pos r) (Finset.mem_Ico.1 hk).1
      have h2 : ((l : ℕ) : Per.Acris0 l) ^ r ∣ ((k.factorial : ℕ) : Per.Acris0 l) := by
        exact_mod_cast Nat.cast_dvd_cast (α := Per.Acris0 l) h1
      exact (h2.mul_left _).mul_right _
    exact this)
  refine ⟨y, fun r => ⟨l ^ r, fun n hn => ⟨s n, ?_, hy r n hn⟩⟩⟩
  simp only [s]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (k + 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → Per.AinfP l) h1
  rw [← hg (k + 1), Nat.factorial_succ]
  generalize ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) = q at h2 ⊢
  rw [h2]
  push_cast
  ring

theorem isLogA_extends {f : Per.Ainf l →+* Per.Ainf l} {F : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) {e e' : Per.Fl l}
    (h : f (Per.tm e) = Per.tm e') {y : Per.Acris l} (hy : IsLogA e y) : IsLogA e' (F y) := by
  intro r
  obtain ⟨N, hN⟩ := hy r
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s, hs, z, hz⟩ := hN n hn
  refine ⟨⟨Per.extP f s, hf.mem _ s.2⟩, ?_, F z, ?_⟩
  · have hm : f (mu e) = mu e' := by rw [mu, mu, map_sub, map_one, h]
    have := congrArg (Per.extP f) hs
    simpa only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, GlobalTheory.RingBasics.awayMap_algebraMap₂, hm] using this
  · have := congrArg F hz
    rw [map_sub, map_mul, map_pow, map_natCast, hf.env] at this
    exact this

theorem isLogA_phiA {e : Per.Fl l} {y : Per.Acris l} (hy : IsLogA e y) : IsLogA (e ^ l) (phiA l y) :=
  isLogA_extends (GlobalTheory.CrisMaps.phiA_extends l) (GlobalTheory.RingIface.phiA_teich l e) hy

theorem isLogA_sigA (g : Per.Gq l) {e : Per.Fl l} {y : Per.Acris l} (hy : IsLogA e y) :
    IsLogA (Per.σF g e) (sigA g y) :=
  isLogA_extends (GlobalTheory.CrisMaps.sigA_extends g) (GlobalTheory.RingIface.sigA_teich l g e) hy

theorem exists_part (l : ℕ) [Fact l.Prime] : ∃ (ζ : ℕ → Om l) (ε : Per.Fl l) (t : Per.Acris l),
    ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧
    (∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m)) ∧ IsLogA ε t := by
  obtain ⟨ζ, h0, hs, h1⟩ := exists_zeta l
  obtain ⟨ε, h⟩ := exists_tilt ζ h0 hs
  obtain ⟨t, ht⟩ := exists_isLogA (isEps_of_root h0 h1 h).1
  exact ⟨ζ, ε, t, h0, hs, h1, h, ht⟩

end GlobalTheory.MemLoc.Model
