import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Acris0TorsionFree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KerThetaLocalizedEqSpanFontaineXiElementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientCompleteStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisUnique

variable {l : ℕ} [Fact l.Prime]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, e, h0, -, h1, h⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨e, ?_, fun h' => h1 ?_⟩
  · have := h 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · have := h 1
    have h2 : rootT e 1 = 1 := h'
    rw [h2] at this
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← this]
    rfl

theorem dvd_of_pow_mul {R : Type} [CommRing R] (x p : R) (h : ∀ a, x ∣ p * a → x ∣ a) (k : ℕ) (a : R)
    (ha : x ∣ p ^ k * a) : x ∣ a := by
  induction k with
  | zero => simpa using ha
  | succ k ih => exact ih (h _ (by rwa [pow_succ', mul_assoc] at ha))

theorem localization_quotient_separated_dvd {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (x p : R) [IsLocalization.Away p S]
    (h : ∀ a, x ∣ p * a → x ∣ a)
    (hc : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {x}) p}) (R ⧸ Ideal.span {x}))
    (q : S) (hq : ∀ r : ℕ, ∃ a : R, algebraMap R S x ∣ q - algebraMap R S (p ^ r * a)) :
    algebraMap R S x ∣ q := by
  have sat : ∀ b : R, algebraMap R S x ∣ algebraMap R S b → x ∣ b := by
    rintro b ⟨c, hc⟩
    obtain ⟨⟨c', ⟨_, m, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers p) c
    have e : algebraMap R S (p ^ m * b) = algebraMap R S (x * c') := by
      rw [map_mul, map_mul, hc, ← hm]; ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers p) S).1 e
    refine dvd_of_pow_mul x p h m _ (dvd_of_pow_mul x p h k _ ⟨p ^ k * c', ?_⟩)
    simp only at hk
    rw [hk]; ring
  obtain ⟨a0, h0⟩ := hq 0
  rw [pow_zero, one_mul] at h0
  have h1 : Ideal.Quotient.mk (Ideal.span {x}) a0 = 0 := by
    refine hc.haus _ fun r => ?_
    obtain ⟨a, ha⟩ := hq r
    have h2 : x ∣ a0 - p ^ r * a := sat _ (by
      have := dvd_sub ha h0
      rw [map_sub]
      convert this using 1
      ring)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact h2
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1
  have := dvd_add h0 (map_dvd (algebraMap R S) h1)
  simpa using this

theorem sep (n : ℕ) (q : Per.AinfP l ⧸ Per.kerP l ^ n)
    (hq : ∀ r : ℕ, ∃ a : Per.Ainf l, q = (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ r *
      Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a)) : q = 0 := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨h1, h2⟩ := GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l e he n
  have hk : ∀ y : Per.AinfP l, y ∈ Per.kerP l ^ n ↔ algebraMap (Per.Ainf l) (Per.AinfP l) (xi e ^ n) ∣ y := by
    intro y
    rw [GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_pow]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.eq_zero_iff_mem, hk]
  refine localization_quotient_separated_dvd (xi e ^ n) (l : Per.Ainf l) h1 ?_ y fun r => ?_
  · rw [map_natCast]
    exact h2.toIsHausdorff
  · obtain ⟨a, ha⟩ := hq r
    refine ⟨a, ?_⟩
    rw [← hk, ← Ideal.Quotient.eq, ha, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast]

theorem ev_alg (n : ℕ) (y : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) y) = Ideal.Quotient.mk _ y :=
  GlobalTheory.RingIface.ev_alg l n y

theorem ev_aDp (n : ℕ) (a : Per.Ainf l) :
    Per.ev l n (aDp l a) = Ideal.Quotient.mk _ (algebraMap (Per.Ainf l) (Per.AinfP l) a) :=
  ev_alg n _

theorem ev_ext {x y : Per.BdRp l} (h : ∀ n, Per.ev l n x = Per.ev l n y) : x = y :=
  GlobalTheory.RingIface.ev_ext l x y h

theorem σDp_alg (g : Per.Gq l) (y : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) y) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) y) :=
  GlobalTheory.RingIface.sigDp_alg l g y

private theorem ker_evalₐ_fg {A : Type} [CommRing A] (J : Ideal A) (fg : J.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ J n) = (J ^ n).map (algebraMap A (AdicCompletion J A)) := by
  ext a
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
  have hle : (J ^ n • ⊤ : Ideal A) ≤ J ^ n := by intro x hx; simpa using hx
  rw [← AdicCompletion.factor_eval_eq_evalₐ J a hle]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval J A n a)
    rw [← hb] at h ⊢
    have : b ∈ J ^ n := Ideal.Quotient.eq_zero_iff_mem.mp h
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using this)
  · intro h; rw [h, map_zero]

private theorem mem_map_of_ev (n : ℕ) (w : Per.BdRp l) (h : Per.ev l n w = 0) :
    w ∈ (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l)) := by
  obtain ⟨ε, hε⟩ := exists_isEps l
  have fg : (Per.kerP l).FG := by
    rw [GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l ε hε]
    exact Submodule.fg_span_singleton _
  obtain ⟨e, he, hev⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have h1 : e w ∈ RingHom.ker (AdicCompletion.evalₐ (Per.kerP l) n) := by
    rw [RingHom.mem_ker, hev, h]
  rw [ker_evalₐ_fg _ fg] at h1
  have h2 : (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (AdicCompletion (Per.kerP l) (Per.AinfP l))) ≤
      ((Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l))).comap e.symm.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, ← he a]
    have := Ideal.mem_map_of_mem (algebraMap (Per.AinfP l) (Per.BdRp l)) ha
    simpa using this
  have h3 := h2 h1
  rw [Ideal.mem_comap] at h3
  simpa using h3

theorem ev_σDp (g : Per.Gq l) (n : ℕ) (w : Per.BdRp l) (y : Per.AinfP l)
    (h : Per.ev l n w = Ideal.Quotient.mk _ y) :
    Per.ev l n (Per.σDp g w) = Ideal.Quotient.mk _ (Per.extP (Per.σA g) y) := by
  have h0 : Per.ev l n (w - algebraMap (Per.AinfP l) (Per.BdRp l) y) = 0 := by
    rw [map_sub, h, ev_alg, sub_self]
  have h1 := mem_map_of_ev n _ h0
  have h2 : (Per.kerP l ^ n).map (algebraMap (Per.AinfP l) (Per.BdRp l)) ≤
      (RingHom.ker (Per.ev l n)).comap (Per.σDp g) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, σDp_alg, ev_alg, Ideal.Quotient.eq_zero_iff_mem]
    exact ((Ideal.pow_right_mono (GlobalTheory.RingBasics.ker_σ g) n).trans (Ideal.le_comap_pow _ n)) ha
  have h3 := h2 h1
  rw [Ideal.mem_comap, RingHom.mem_ker, map_sub, map_sub, σDp_alg, ev_alg, sub_eq_zero] at h3
  exact h3

theorem sigA_alg (g : Per.Gq l) (s : Per.Acris0 l) :
    sigA g (algebraMap (Per.Acris0 l) (Per.Acris l) s) =
      algebraMap (Per.Acris0 l) (Per.Acris l) ⟨Per.extP (Per.σA g) s, (GlobalTheory.CrisMaps.sigA_extends g).mem _ s.2⟩ :=
  (GlobalTheory.CrisMaps.sigA_extends g).env s

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem ev_eq {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l)
    (h : ∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l),
      x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧
      Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) =
        Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) : Per.ev l n (j x) = Per.ev l n y := by
  obtain ⟨N, hN⟩ := hj.bdd n
  have hu : IsUnit ((l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ N) := by
    have := (GlobalTheory.RingBasics.isUnit_l l).map (Ideal.Quotient.mk (Per.kerP l ^ n))
    rw [map_natCast] at this
    exact this.pow N
  rw [← sub_eq_zero, ← hu.mul_right_eq_zero]
  refine sep n _ fun r => ?_
  obtain ⟨s, z, a, hx, hy⟩ := h r
  obtain ⟨b, hb⟩ := hN z
  refine ⟨b - (l : Per.Ainf l) ^ N * a, ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, ev_aDp] at hy
  rw [map_mul, map_pow, map_natCast] at hb
  simp only [hx, map_add, map_sub, map_mul, map_pow, map_natCast, hj.on0]
  linear_combination (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ r * hb -
    (l : Per.AinfP l ⧸ Per.kerP l ^ n) ^ N * hy

theorem unique {j j' : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (hj' : IsCrisP j') : j' = j := by
  refine RingHom.ext fun x => ev_ext fun n => (ev_eq hj n x _ fun r => ?_).symm
  obtain ⟨N, hN⟩ := hj'.bdd n
  obtain ⟨s, z, hx⟩ := (acris_basic l).2.2.1 x (r + N)
  obtain ⟨a, ha⟩ := hN z
  refine ⟨s, (l : Per.Acris l) ^ N * z, a, by rw [hx, pow_add, mul_assoc], ?_⟩
  rw [map_mul (Per.ev l n), ev_aDp, ← ha, ← map_mul, hx, map_add, map_mul j', map_pow j', map_natCast, hj'.on0,
    add_sub_cancel_left, pow_add, mul_assoc]

theorem equivariant {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (g : Per.Gq l) (x : Per.Acris l) :
    j (sigA g x) = Per.σDp g (j x) := by
  refine ev_ext fun n => ev_eq hj n _ _ fun r => ?_
  obtain ⟨N, hN⟩ := hj.bdd n
  obtain ⟨s, z, hx⟩ := (acris_basic l).2.2.1 x (r + N)
  obtain ⟨a, ha⟩ := hN z
  refine ⟨⟨Per.extP (Per.σA g) s, (GlobalTheory.CrisMaps.sigA_extends g).mem _ s.2⟩, (l : Per.Acris l) ^ N * sigA g z, Per.σA g a, ?_, ?_⟩
  · rw [hx, map_add, sigA_alg, map_mul, map_pow, map_natCast, pow_add, mul_assoc]
  · have hb := ev_σDp g n _ _ ha
    rw [GlobalTheory.RingBasics.awayMap_algebraMap₂, map_mul (Per.σDp g), map_pow (Per.σDp g), map_natCast] at hb
    rw [map_mul (Per.ev l n), ev_aDp, ← hb, ← map_mul, hx, map_add j, map_mul j, map_pow j, map_natCast j, hj.on0,
      map_add (Per.σDp g), σDp_alg, add_sub_cancel_left, map_mul (Per.σDp g), map_pow (Per.σDp g),
      map_natCast (Per.σDp g), pow_add, mul_assoc]

end GlobalTheory.MemLoc.CrisUnique

namespace GlobalTheory.MemLoc

theorem crisP_unique_equivariant : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → (∀ j' : Per.Acris l →+* Per.BdRp l, IsCrisP j' → j' = j) ∧ (∀ (g : Per.Gq l) (x : Per.Acris l), j (sigA g x) = Per.σDp g (j x)) ∧ ∀ (n : ℕ) (x : Per.Acris l) (y : Per.BdRp l), (∀ r : ℕ, ∃ (s : Per.Acris0 l) (z : Per.Acris l) (a : Per.Ainf l), x = algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ r * z ∧ Per.ev l n (y - algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) = Per.ev l n ((l : Per.BdRp l) ^ r * aDp l a)) → Per.ev l n (j x) = Per.ev l n y :=
  fun _ _ _ hj => ⟨fun _ hj' => CrisUnique.unique hj hj', CrisUnique.equivariant hj, CrisUnique.ev_eq hj⟩

end GlobalTheory.MemLoc
