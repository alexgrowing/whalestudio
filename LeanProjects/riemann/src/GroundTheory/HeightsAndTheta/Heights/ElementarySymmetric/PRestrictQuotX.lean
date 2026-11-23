import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistBundleToSubSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U V : Finset (Fin n)} (hVU : V ⊆ U)

def liftCell (J : Cell V) : Cell U := ⟨J.1, J.2.1, J.2.2.trans hVU⟩

def liftIdx {i : ℕ} (J : Idx V i) : Idx U i := ⟨liftCell hVU J.1, J.2⟩

theorem liftIdx_injective {i : ℕ} : Function.Injective (liftIdx (i := i) hVU) := by
  intro J J' h
  exact Subtype.ext (Subtype.ext (congrArg (fun I : Idx U i => I.1.1) h))

theorem exists_liftIdx {i : ℕ} (I : Idx U i) (hI : I.1.1 ⊆ V) : ∃ J : Idx V i, liftIdx hVU J = I :=
  ⟨⟨⟨I.1.1, I.1.2.1, hI⟩, I.2⟩, rfl⟩

variable {R : Type*} [CommRing R]
  {G : Cell U → Type v} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell V → Type w} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell V, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def restrC (e : ∀ J : Cell V, G (liftCell hVU J) →ₗ[R] G' J) (i : ℕ) : Cochain G i →ₗ[R] Cochain G' i :=
  LinearMap.pi fun J : Idx V i =>
    (e J.1).comp (LinearMap.proj (R := R) (φ := fun I : Idx U i => G I.1) (liftIdx hVU J))

theorem restrC_d (e : ∀ J : Cell V, G (liftCell hVU J) →ₗ[R] G' J)
    (he : ∀ (J J' : Cell V) (h : J.1 ⊆ J'.1) (m : G (liftCell hVU J)),
      e J' (ρ (liftCell hVU J) (liftCell hVU J') h m) = ρ' J J' h (e J m))
    (i : ℕ) (s : Cochain G i) : restrC hVU e (i + 1) (d G ρ i s) = d G' ρ' i (restrC hVU e i s) := by
  funext J
  rw [d_apply]
  change e J.1 (d G ρ i s (liftIdx hVU J)) = _
  have hd : (d G ρ i s (liftIdx hVU J) : G (liftCell hVU J.1)) = ∑ j : J.1.1, sgn J.1.1 j •
      ρ (liftCell hVU (face J j).1) (liftCell hVU J.1) (face_subset J j) (s (liftIdx hVU (face J j))) :=
    d_apply i s (liftIdx hVU J)
  refine (congrArg (e J.1) hd).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  congr 1
  exact he (face J j).1 J.1 (face_subset J j) (s (liftIdx hVU (face J j)))

theorem restrC_bijective (e : ∀ J : Cell V, G (liftCell hVU J) ≃ₗ[R] G' J)
    (hz : ∀ I : Cell U, ¬ I.1 ⊆ V → ∀ m : G I, m = 0) (i : ℕ) :
    Function.Bijective (restrC hVU (fun J => (e J).toLinearMap) i) := by
  constructor
  · intro s t hst
    funext I
    by_cases hI : I.1.1 ⊆ V
    · obtain ⟨J, rfl⟩ := exists_liftIdx hVU I hI
      exact (e J.1).injective (congrFun hst J)
    · rw [hz I.1 hI (s I), hz I.1 hI (t I)]
  · intro t
    have key : ∀ I : Idx U i, ∃ m : G I.1, ∀ (J : Idx V i) (h : liftIdx hVU J = I),
        cast (congrArg (fun I : Idx U i => G I.1) h) ((e J.1).symm (t J)) = m := by
      intro I
      by_cases hI : I.1.1 ⊆ V
      · obtain ⟨J₀, rfl⟩ := exists_liftIdx hVU I hI
        refine ⟨(e J₀.1).symm (t J₀), fun J h => ?_⟩
        obtain rfl := liftIdx_injective hVU h
        rfl
      · refine ⟨0, fun J h => (hI ?_).elim⟩
        rw [← h]
        exact J.1.2.2
    choose s hs using key
    refine ⟨s, funext fun J => ?_⟩
    change e J.1 (s (liftIdx hVU J)) = t J
    rw [← hs (liftIdx hVU J) J rfl]
    exact LinearEquiv.apply_symm_apply _ _

def equivHOfCochain {n' : ℕ} {V' : Finset (Fin n')} {G'' : Cell V' → Type w} [∀ I, AddCommGroup (G'' I)]
    [∀ I, Module R (G'' I)] {ρ'' : ∀ I J : Cell V', I.1 ⊆ J.1 → G'' I →ₗ[R] G'' J}
    (Φ : ∀ i, Cochain G i ≃ₗ[R] Cochain G'' i)
    (hΦ : ∀ i s, Φ (i + 1) (d G ρ i s) = d G'' ρ'' i (Φ i s)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G'' ρ'' i := by
  have hker : ∀ i s, s ∈ LinearMap.ker (d G ρ i) ↔ Φ i s ∈ LinearMap.ker (d G'' ρ'' i) := by
    intro i s
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hΦ, LinearEquiv.map_eq_zero_iff]
  have hbdry : ∀ i s, s ∈ bdry G ρ i ↔ Φ i s ∈ bdry G'' ρ'' i := by
    intro i s
    cases i with
    | zero =>
      change s ∈ (⊥ : Submodule R _) ↔ Φ 0 s ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
    | succ i =>
      change s ∈ LinearMap.range (d G ρ i) ↔ Φ (i + 1) s ∈ LinearMap.range (d G'' ρ'' i)
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨Φ i t, (hΦ i t).symm⟩
      · rintro ⟨t', ht'⟩
        refine ⟨(Φ i).symm t', (Φ (i + 1)).injective ?_⟩
        rw [hΦ, LinearEquiv.apply_symm_apply, ht']
  let K : LinearMap.ker (d G ρ i) ≃ₗ[R] LinearMap.ker (d G'' ρ'' i) :=
    LinearEquiv.ofSubmodules (Φ i) _ _ (by
      ext z
      rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, hker i,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])
  exact Submodule.Quotient.equiv _ _ K (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.subtype_apply, hbdry i]
    congr! 1
    change Φ i ((Φ i).symm (z : Cochain G'' i)) = z
    exact LinearEquiv.apply_symm_apply _ _)

def equivHRestr (e : ∀ J : Cell V, G (liftCell hVU J) ≃ₗ[R] G' J)
    (he : ∀ (J J' : Cell V) (h : J.1 ⊆ J'.1) (m : G (liftCell hVU J)),
      e J' (ρ (liftCell hVU J) (liftCell hVU J') h m) = ρ' J J' h (e J m))
    (hz : ∀ I : Cell U, ¬ I.1 ⊆ V → ∀ m : G I, m = 0) (i : ℕ) : H G ρ i ≃ₗ[R] H G' ρ' i :=
  equivHOfCochain (fun i => LinearEquiv.ofBijective _ (restrC_bijective hVU e hz i))
    (fun i s => restrC_d hVU (fun J => (e J).toLinearMap) he i s) i

end Cech

namespace PrimeFiltration.RestrictQuot

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem support_subset (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) : support y ⊆ support x :=
  fun i hi => (mem_support x).mpr (hxy i ((mem_support y).mp hi))

theorem map_eq_zero_of_mem {L : SubSystem S x Ω} {L' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData L hxy L' r) {pp : Ideal (Poly S N)} (hpp : pp ≤ primeOf (S := S) y) (J : Chart y)
    {z : Ω} (hz : z ∈ (L.twist (idealSys x pp)).sub (liftChart hxy J)) :
    z ∈ L.sub (liftChart hxy J) ∧ r z = 0 := by
  refine Submodule.span_induction (p := fun z _ => z ∈ L.sub (liftChart hxy J) ∧ r z = 0) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨q, hq, w, hw, rfl⟩
    refine Submodule.span_induction
      (p := fun q _ => q • w ∈ L.sub (liftChart hxy J) ∧ r (q • w) = 0) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
      have hc : aeval x f / aeval x s ∈ chartRing S x (liftChart hxy J) := ⟨f, s, e, hs, hfe, hse, rfl⟩
      refine ⟨RestrictTwist.mul_mem' hc hw, ?_⟩
      rw [smul_eq_mul, h.smul J w hw f s e hs hfe hse,
        (mem_primeOf_of_isHomogeneous y hfe).mp (hpp hf), zero_div, zero_mul]
    · rw [zero_smul]
      exact ⟨(L.sub _).zero_mem, RestrictTwist.map_zero_of h J⟩
    · rintro a b - - ⟨ha, ha'⟩ ⟨hb, hb'⟩
      rw [add_smul]
      exact ⟨(L.sub _).add_mem ha hb, by rw [h.add J _ ha _ hb, ha', hb', add_zero]⟩
    · rintro c a - ⟨ha, ha'⟩
      rw [smul_assoc]
      refine ⟨(L.sub _).smul_mem c ha, ?_⟩
      rw [chartRing_smul_def, RestrictTwist.map_mul_of h J c.2 ha, ha', mul_zero]
  · exact ⟨(L.sub _).zero_mem, RestrictTwist.map_zero_of h J⟩
  · rintro a b - - ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨(L.sub _).add_mem ha hb, by rw [h.add J _ ha _ hb, ha', hb', add_zero]⟩
  · rintro c a - ⟨ha, ha'⟩
    refine ⟨(L.sub _).smul_mem c ha, ?_⟩
    rw [chartRing_smul_def, RestrictTwist.map_mul_of h J c.2 ha, ha', mul_zero]

theorem mem_of_map_eq_zero {L : LineBundle S x} {L' : LineBundle S y} {r : Ω → K'}
    (h : RestrictData L.toSubSystem hxy L'.toSubSystem r) {pp : Ideal (Poly S N)}
    (hpp : primeOf (S := S) y ≤ pp) (J : Chart y) {z : Ω} (hz : z ∈ L.sub (liftChart hxy J))
    (hr : r z = 0) : z ∈ (L.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J) := by
  obtain ⟨l, hl, hsum⟩ := RestrictTwist.exists_dual L (liftChart hxy J)

  obtain ⟨q, hq, hrq⟩ : ∃ q ∈ L.sub (liftChart hxy J), r q ≠ 0 := by
    by_contra hcon'
    have hcon : ∀ q ∈ L.sub (liftChart hxy J), r q = 0 := fun q hq =>
      by_contra fun hne => hcon' ⟨q, hq, hne⟩
    have hbot : L'.sub J = ⊥ := by
      rw [← h.span J, Submodule.span_eq_bot]
      rintro _ ⟨q, hq, rfl⟩
      exact hcon q hq
    obtain ⟨P, hP⟩ := L'.invertible J
    have h1 : (1 : K') ∈ L'.sub J * P := by
      rw [hP]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [hbot, Submodule.bot_mul, Submodule.mem_bot] at h1
    exact one_ne_zero h1

  have hmem : ∀ p ∈ l, p.2 * z ∈ idealMod (x := x) pp (liftChart hxy J) := by
    intro p hp
    obtain ⟨f, s, e, hs, hf, hse, hfz⟩ := (hl p hp).2 z hz
    obtain ⟨f', s', e', hs', hf', hse', hfq⟩ := (hl p hp).2 q hq
    have h1 := h.smul J q hq f s e hs hf hse
    have h2 := h.smul J z hz f' s' e' hs' hf' hse'
    rw [← hfz] at h1
    rw [← hfq, hr, mul_zero] at h2
    rw [show p.2 * z * q = p.2 * q * z by ring, h2] at h1
    have hsy : aeval y s ≠ 0 := eval_ne_zero_of_mem_monos J hs
    have hfy : aeval y f = 0 := by
      rcases mul_eq_zero.mp h1.symm with h0 | h0
      · rwa [div_eq_zero_iff, or_iff_left hsy] at h0
      · exact absurd h0 hrq
    have hfp : f ∈ pp := hpp ((mem_primeOf_of_isHomogeneous y hf).mpr hfy)
    rw [hfz]
    exact Submodule.subset_span ⟨f, s, e, hfp, hs, hf, hse, rfl⟩
  have hz' : z = (l.map fun p => (p.2 * z) • p.1).sum := by
    calc z = z * (l.map fun p => p.1 * p.2).sum := by rw [hsum, mul_one]
      _ = (l.map fun p => z * (p.1 * p.2)).sum := by rw [List.sum_map_mul_left]
      _ = _ := by
        congr 1
        refine List.map_congr_left fun p _ => ?_
        rw [smul_eq_mul]; ring
  rw [hz']
  refine list_sum_mem fun w hw => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
  exact Submodule.subset_span ⟨p.2 * z, hmem p hp, p.1, (hl p hp).1, rfl⟩

theorem mem_twist_ideal_of_not_subset {pp : Ideal (Poly S N)} (hpp : primeOf (S := S) y ≤ pp)
    (F : SubSystem S x Ω) (I : Chart x) (hI : ¬ I.1 ⊆ support y) {z : Ω} (hz : z ∈ F.sub I) :
    z ∈ (F.twist (idealSys x pp)).sub I := by
  obtain ⟨i, hiI, hiy⟩ := Finset.not_subset.mp hI
  have hyi : y i = 0 := by
    by_contra h0; exact hiy ((mem_support y).mpr h0)
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hiI)
  have hXp : (X i : Poly S N) ∈ pp :=
    hpp ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X S i)).mpr (by rw [aeval_X, hyi]))
  have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
    Submodule.subset_span ⟨X i, X i, 1, hXp, X_mem_monos hiI, isHomogeneous_X S i, isHomogeneous_X S i,
      by rw [aeval_X, div_self hxi]⟩
  exact Submodule.subset_span ⟨1, h1, z, hz, (one_smul _ _).symm⟩

def chartMap {L : SubSystem S x Ω} {L' : SubSystem S y K'} {r : Ω → K'} (h : RestrictData L hxy L' r)
    (J : Chart y) : L.sub (liftChart hxy J) →ₗ[S] L'.sub J where
  toFun z := ⟨r z, h.mem J z z.2⟩
  map_add' a b := Subtype.ext (h.add J a a.2 b b.2)
  map_smul' c a := Subtype.ext (by
    change r (c • (a : Ω)) = c • r a
    have := h.smul J a a.2 (C c) 1 0 (one_mem _) (isHomogeneous_C _ _) (isHomogeneous_one _ _)
    simpa [aeval_C, Algebra.smul_def] using this)

theorem chartMap_surjective {L : SubSystem S x Ω} {L' : SubSystem S y K'} {r : Ω → K'}
    (h : RestrictData L hxy L' r) (J : Chart y) : Function.Surjective (chartMap h J) := by
  intro w
  have hw : (w : K') ∈ r '' (L.sub (liftChart hxy J) : Set Ω) := by
    have hw0 : (w : K') ∈ Submodule.span (chartRing S y J) (r '' (L.sub (liftChart hxy J) : Set Ω)) := by
      rw [h.span J]; exact w.2
    refine Submodule.span_induction (p := fun z _ => z ∈ r '' (L.sub (liftChart hxy J) : Set Ω))
      (fun z hz => hz) ⟨0, (L.sub _).zero_mem, RestrictTwist.map_zero_of h J⟩ ?_ ?_ hw0
    · rintro _ _ - - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, (L.sub _).add_mem ha hb, h.add J a ha b hb⟩
    · rintro c _ - ⟨a, ha, rfl⟩
      obtain ⟨f, s, e, hs, hf, hse, hc⟩ := c.2
      have hcx : aeval x f / aeval x s ∈ chartRing S x (liftChart hxy J) := ⟨f, s, e, hs, hf, hse, rfl⟩
      refine ⟨aeval x f / aeval x s * a, RestrictTwist.mul_mem' hcx ha, ?_⟩
      rw [h.smul J a ha f s e hs hf hse, chartRing_smul_def, ← hc]
  obtain ⟨z, hz, hzw⟩ := hw
  exact ⟨⟨z, hz⟩, Subtype.ext hzw⟩

theorem ker_chartMap {L : LineBundle S x} {L' : LineBundle S y} {r : Ω → K'}
    (h : RestrictData L.toSubSystem hxy L'.toSubSystem r) {pp : Ideal (Poly S N)}
    (hpy : primeOf (S := S) y = pp) (J : Chart y) :
    LinearMap.ker (chartMap h J) =
      SubSystem.quotSub L.toSubSystem (L.toSubSystem.twist (idealSys x pp)) (liftChart hxy J) := by
  ext z
  rw [LinearMap.mem_ker]
  change (⟨r z, _⟩ : L'.sub J) = 0 ↔ (z : Ω) ∈ (L.toSubSystem.twist (idealSys x pp)).sub (liftChart hxy J)
  constructor
  · intro hz
    exact mem_of_map_eq_zero h hpy.le J z.2 (congrArg Subtype.val hz)
  · intro hz
    exact Subtype.ext (map_eq_zero_of_mem h hpy.ge J hz).2

def chartEquiv {L : LineBundle S x} {L' : LineBundle S y} {r : Ω → K'}
    (h : RestrictData L.toSubSystem hxy L'.toSubSystem r) {pp : Ideal (Poly S N)}
    (hpy : primeOf (S := S) y = pp) (J : Chart y) :
    (L.sub (liftChart hxy J) ⧸
      SubSystem.quotSub L.toSubSystem (L.toSubSystem.twist (idealSys x pp)) (liftChart hxy J)) ≃ₗ[S]
      L'.sub J :=
  (Submodule.quotEquivOfEq _ _ (ker_chartMap h hpy J).symm).trans
    ((chartMap h J).quotKerEquivOfSurjective (chartMap_surjective h J))

theorem chartEquiv_mk {L : LineBundle S x} {L' : LineBundle S y} {r : Ω → K'}
    (h : RestrictData L.toSubSystem hxy L'.toSubSystem r) {pp : Ideal (Poly S N)}
    (hpy : primeOf (S := S) y = pp) (J : Chart y) (z : L.sub (liftChart hxy J)) :
    chartEquiv h hpy J (Submodule.Quotient.mk z) = chartMap h J z := by
  simp [chartEquiv]

theorem quotH_equiv {L : LineBundle S x} {L' : LineBundle S y} {r : Ω → K'}
    (h : RestrictData L.toSubSystem hxy L'.toSubSystem r) {pp : Ideal (Poly S N)}
    (hpy : primeOf (S := S) y = pp) (i : ℕ) :
    Nonempty (SubSystem.quotH L.toSubSystem (L.toSubSystem.twist (idealSys x pp)) i ≃ₗ[S]
      L'.toSubSystem.H i) := by
  refine ⟨Cech.equivHRestr (support_subset hxy) (fun J => chartEquiv h hpy J) ?_ ?_ i⟩
  · intro J J' hJJ' m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    apply Subtype.ext
    have e1 := congrArg Subtype.val
      (chartEquiv_mk h hpy J' (L.toSubSystem.res (liftChart hxy J) (liftChart hxy J') hJJ' z))
    have e2 := congrArg Subtype.val (chartEquiv_mk h hpy J z)
    exact e1.trans e2.symm
  · intro I hI m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_twist_ideal_of_not_subset hpy.le _ I hI z.2)

end PrimeFiltration.RestrictQuot

theorem PrimeFiltration.RestrictQuot.proof : PrimeFiltration.RestrictQuot.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x pp hpp hhom hle j hj hX K' _ _ ψ hker hxy Q Q' r hRD c i
  have hpy : primeOf (S := S) (fun l => ψ (ratio hj l)) = pp :=
    (PrimeFiltration.Point.proof S Ω N x pp hpp hhom hle j hj hX).2 K' ψ hker
  have hle' : primeOf (S := S) x ≤ primeOf (S := S) (fun l => ψ (ratio hj l)) := hpy ▸ hle
  obtain ⟨rc, hrc⟩ := RestrictTwist.restrictData_twist (Q₂ := twistBundle S x c)
    (Q₂' := twistBundle S (fun l => ψ (ratio hj l)) c) hRD
    (RestrictTwist.restrictData_twistSys hxy hle' c)
  exact PrimeFiltration.RestrictQuot.quotH_equiv (L := Q.tensor (twistBundle S x c))
    (L' := Q'.tensor (twistBundle S (fun l => ψ (ratio hj l)) c)) hrc hpy i

end

end GroundTheory.Heights₂.Heights.Kleiman
