import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionComplex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreReduction

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

section Grading

variable {R : Type} [CommRing R]

open Classical in

def blockWt : (Σ k, ι k) → (K → ℕ) := fun q k => if q.1 = k then 1 else 0

theorem weight_blockWt_apply (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight blockWt d k = ∑ i, d ⟨k, i⟩ := by
  rw [Finsupp.weight_eq_sum, Finset.sum_apply, Fintype.sum_sigma]
  simp only [blockWt, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem isMultiHomog_iff (f : MRingOver R ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous blockWt f a := by
  constructor
  · intro h d hd
    funext k
    rw [weight_blockWt_apply]
    exact h d (mem_support_iff.mpr hd) k
  · intro h d hd k
    rw [← weight_blockWt_apply, h (mem_support_iff.mp hd)]

theorem comp_mem {P : Ideal (MRingOver R ι)} (hP : IsMultiHomogIdeal P) {q : MRingOver R ι} (hq : q ∈ P)
    (D : K → ℕ) : weightedHomogeneousComponent blockWt D q ∈ P := by
  classical
  let _ := weightedGradedAlgebra R (blockWt (ι := ι))
  obtain ⟨S, hS, rfl⟩ := hP
  refine weightedHomogeneousComponent_mem_of_mem R blockWt (Ideal.homogeneous_span _ S fun x hx => ?_) hq D
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨a, (mem_weightedHomogeneousSubmodule R blockWt a x).mpr ((isMultiHomog_iff x a).mp ha)⟩

end Grading

section Lift

variable (p : ℕ)

theorem cellMon_lift {S : Type} [CommRing S] {I : ∀ k, Finset (ι k)} {t : MRingOver S ι}
    (ht : t ∈ KH.cellMon S I) : ∃ d, t = monomial d 1 ∧ (monomial d 1 : MRingOver ℤ ι) ∈ KH.cellMon ℤ I := by
  unfold KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    exact ⟨Finsupp.single ⟨k, i⟩ 1, rfl, Submonoid.subset_closure ⟨k, i, hi, rfl⟩⟩
  | one => exact ⟨0, rfl, one_mem _⟩
  | mul f g _ _ hf hg =>
    obtain ⟨d, rfl, hd⟩ := hf
    obtain ⟨d', rfl, hd'⟩ := hg
    exact ⟨d + d', by rw [monomial_mul, mul_one], by rw [← mul_one (1 : ℤ), ← monomial_mul]; exact mul_mem hd hd'⟩

theorem map_monomial_one (d : (Σ k, ι k) →₀ ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (monomial d 1 : MRingOver ℤ ι) = monomial d 1 := by
  rw [map_monomial, map_one]

theorem homog_monomial_one_of_zmod [Fact p.Prime] {d : (Σ k, ι k) →₀ ℕ} {e : K → ℕ}
    (h : IsMultiHomog (monomial d 1 : MRingOver (ZMod p) ι) e) : IsMultiHomog (monomial d 1 : MRingOver ℤ ι) e :=
  by
  classical
  exact GenOnFibres.homog_monomial d 1 e fun k => h d (by rw [mem_support_iff, coeff_monomial, if_pos rfl]; exact one_ne_zero) k

def liftPoly (F : MRingOver (ZMod p) ι) : MRingOver ℤ ι :=
  ∑ d ∈ F.support, monomial d ((coeff d F).val : ℤ)

theorem coeff_liftPoly (F : MRingOver (ZMod p) ι) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (liftPoly p F) = ((coeff d F).val : ℤ) := by
  classical
  rw [liftPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : d ∈ F.support
  · rw [if_pos h]
  · rw [if_neg h, notMem_support_iff.mp h]
    simp

theorem map_liftPoly [NeZero p] (F : MRingOver (ZMod p) ι) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (liftPoly p F) = F := by
  ext d
  rw [coeff_map, coeff_liftPoly]
  simp

theorem homog_liftPoly {F : MRingOver (ZMod p) ι} {a : K → ℕ} (hF : IsMultiHomog F a) :
    IsMultiHomog (liftPoly p F) a := fun d hd => by
  refine hF d (mem_support_iff.mpr fun h0 => mem_support_iff.mp hd ?_)
  rw [coeff_liftPoly, h0]
  simp

end Lift

section Reduction

theorem span_int_induction {A : Type*} [AddCommGroup A] (h : Module ℤ A) {s : Set A} {P : A → Prop}
    (mem : ∀ x ∈ s, P x) (zero : P 0) (add : ∀ x x', P x → P x' → P (x + x')) (neg : ∀ x, P x → P (-x))
    {x : A} (hx : x ∈ @Submodule.span ℤ A _ _ h s) : P x := by
  obtain rfl : h = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  induction hx using Submodule.span_induction with
  | mem x hx => exact mem x hx
  | zero => exact zero
  | add x x' _ _ hx hx' => exact add x x' hx hx'
  | smul r x _ hx =>
    induction r using Int.induction_on with
    | zero => rw [zero_smul]; exact zero
    | succ n ih => rw [add_smul, one_smul]; exact add _ _ ih hx
    | pred n ih => rw [sub_smul, one_smul, sub_eq_add_neg]; exact add _ _ ih (neg _ hx)

theorem liftOfLE_mk {S : Type} [CommRing S] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    {T T' : Submonoid (MRingOver S ι)} (h : T ≤ T') (m : M) (t : T) :
    LocalizedModule.liftOfLE T T' h (LocalizedModule.mk m t) = LocalizedModule.mk m (⟨t.1, h t.2⟩ : T') := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

theorem mk_mem_locPart {S : Type} [CommRing S] {V : Ideal (MRingOver S ι)} {T : Submonoid (MRingOver S ι)}
    {c : K → ℤ} {m : MRingOver S ι ⧸ V} {t : T} {e : K → ℕ} (ht : IsMultiHomog (t : MRingOver S ι) e)
    (hm : m ∈ KH.quotPart S V (c + fun k => (e k : ℤ))) :
    LocalizedModule.mk m t ∈ KH.locPart ι (KH.quotPart S V) T c :=
  Submodule.subset_span ⟨m, t, e, ht, hm, rfl⟩

variable (y : (Σ k, ι k) → Ω) (p : ℕ)

theorem redRing_mem_quotPart (c : K → ℤ) {m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ}
    (hm : m ∈ KH.quotPart ℤ (GenOnFibres.idealOver y ℤ) c) :
    redRing y p m ∈ KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p)) c := by
  refine span_int_induction _ (P := fun m => redRing y p m ∈ KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p)) c)
    ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨F, ⟨hc, hF⟩, rfl⟩
    rw [redRing_mk]
    exact Submodule.subset_span ⟨_, ⟨hc, GenOnFibres.homog_map _ hF⟩, rfl⟩
  · rw [map_zero]; exact zero_mem _
  · intro x x' hx hx'; rw [map_add]; exact add_mem hx hx'
  · intro x hx; rw [map_neg]; exact neg_mem hx

theorem redLoc_mem_locPart (I : ∀ k, Finset (ι k)) (a : K → ℤ)
    {x : LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) (KH.cellMon ℤ I) a) :
    redLoc y p I x ∈
      KH.locPart ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) (KH.cellMon (ZMod p) I) a := by
  refine span_int_induction _ (P := fun x => redLoc y p I x ∈
      KH.locPart ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) (KH.cellMon (ZMod p) I) a) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨m, t, e, ht, hm, rfl⟩
    rw [redLoc_mk]
    exact Submodule.subset_span ⟨_, _, e, GenOnFibres.homog_map _ ht, redRing_mem_quotPart y p _ hm, rfl⟩
  · rw [map_zero]; exact zero_mem _
  · intro x x' hx hx'; rw [map_add]; exact add_mem hx hx'
  · intro x hx; rw [map_neg]; exact neg_mem hx

theorem exists_lift_quotPart [Fact p.Prime] (c : K → ℤ)
    {m : MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)}
    (hm : m ∈ KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p)) c) :
    ∃ m' ∈ KH.quotPart ℤ (GenOnFibres.idealOver y ℤ) c, redRing y p m' = m := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, ⟨hc, hF⟩, rfl⟩ := hx
    exact ⟨_, Submodule.subset_span ⟨liftPoly p F, ⟨hc, homog_liftPoly p hF⟩, rfl⟩,
      by rw [redRing_mk, map_liftPoly]⟩
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨m', hm', rfl⟩ := hx'
    exact ⟨m + m', add_mem hm hm', map_add _ _ _⟩
  | smul r x _ hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨r.val • m, nsmul_mem hm _, ?_⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

theorem exists_lift_locPart [Fact p.Prime] (I : ∀ k, Finset (ι k)) (a : K → ℤ)
    {x : LocalizedModule (KH.cellMon (ZMod p) I) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p))}
    (hx : x ∈ KH.locPart ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) (KH.cellMon (ZMod p) I) a) :
    ∃ x' ∈ KH.locPart ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) (KH.cellMon ℤ I) a, redLoc y p I x' = x := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, ⟨t, ht⟩, e, hte, hm, rfl⟩ := hx
    obtain ⟨d, rfl, hd⟩ := cellMon_lift ht
    obtain ⟨m', hm', rfl⟩ := exists_lift_quotPart y p _ hm
    refine ⟨LocalizedModule.mk m' ⟨_, hd⟩,
      mk_mem_locPart (homog_monomial_one_of_zmod p hte) hm', ?_⟩
    rw [redLoc_mk]
    congr 1
    exact Subtype.ext (map_monomial_one p d)
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hx'
    exact ⟨w + w', add_mem hw hw', map_add _ _ _⟩
  | smul r x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨r.val • w, nsmul_mem hw _, ?_⟩
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

end Reduction

section Kernel

variable (y : (Σ k, ι k) → Ω) (p : ℕ)

def ZeroOrHomog (c : K → ℤ) (F : MRingOver ℤ ι) : Prop :=
  F = 0 ∨ ((∀ k, 0 ≤ c k) ∧ IsMultiHomog F fun k => (c k).toNat)

variable {y p}

theorem ZeroOrHomog.add {c : K → ℤ} {F G : MRingOver ℤ ι} (hF : ZeroOrHomog c F) (hG : ZeroOrHomog c G) : ZeroOrHomog c (F + G) := by
  rcases hF with rfl | ⟨hc, hF⟩
  · rwa [zero_add]
  rcases hG with rfl | ⟨-, hG⟩
  · rw [add_zero]; exact Or.inr ⟨hc, hF⟩
  exact Or.inr ⟨hc, GenOnFibres.homog_add hF hG⟩

theorem ZeroOrHomog.neg {c : K → ℤ} {F : MRingOver ℤ ι} (hF : ZeroOrHomog c F) : ZeroOrHomog c (-F) := by
  rcases hF with rfl | ⟨hc, hF⟩
  · left; exact neg_zero
  refine Or.inr ⟨hc, ?_⟩
  have h := GenOnFibres.homog_sub (GenOnFibres.homog_zero _) hF
  rwa [zero_sub] at h

theorem ZeroOrHomog.mul {c : K → ℤ} {F t : MRingOver ℤ ι} {e : K → ℕ} (ht : IsMultiHomog t e) (hF : ZeroOrHomog c F) :
    ZeroOrHomog (c + fun k => (e k : ℤ)) (t * F) := by
  rcases hF with rfl | ⟨hc, hF⟩
  · left; exact mul_zero t
  refine Or.inr ⟨fun k => by have := hc k; simp only [Pi.add_apply]; omega, ?_⟩
  have hd : (fun k => ((c + fun k => (e k : ℤ)) k).toNat) = e + fun k => (c k).toNat :=
    funext fun k => by have := hc k; simp only [Pi.add_apply]; omega
  rw [hd]
  exact GenOnFibres.homog_mul ht hF

theorem ZeroOrHomog.congr {c c' : K → ℤ} {F : MRingOver ℤ ι} (h : c = c') (hF : ZeroOrHomog c F) : ZeroOrHomog c' F :=
  h ▸ hF

variable (y)

theorem quotPart_normal {c : K → ℤ} {m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ}
    (hm : m ∈ KH.quotPart ℤ (GenOnFibres.idealOver y ℤ) c) :
    ∃ F, ZeroOrHomog c F ∧ m = Ideal.Quotient.mk _ F := by
  refine span_int_induction _ (P := fun m => ∃ F, ZeroOrHomog c F ∧ m = Ideal.Quotient.mk _ F) ?_
    ⟨0, Or.inl rfl, (map_zero _).symm⟩ ?_ ?_ hm
  · rintro _ ⟨F, ⟨hc, hF⟩, rfl⟩
    exact ⟨F, Or.inr ⟨hc, hF⟩, rfl⟩
  · rintro _ _ ⟨F, hF, rfl⟩ ⟨G, hG, rfl⟩
    exact ⟨F + G, hF.add hG, (map_add _ _ _).symm⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨-F, hF.neg, (map_neg _ _).symm⟩

theorem locPart_normal {T : Submonoid (MRingOver ℤ ι)} {a : K → ℤ}
    {x : LocalizedModule T (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) T a) :
    ∃ (F t : MRingOver ℤ ι) (e : K → ℕ) (ht : t ∈ T), IsMultiHomog t e ∧ ZeroOrHomog (a + fun k => (e k : ℤ)) F ∧
      x = LocalizedModule.mk (Ideal.Quotient.mk _ F) ⟨t, ht⟩ := by
  refine span_int_induction _ (P := fun x => ∃ (F t : MRingOver ℤ ι) (e : K → ℕ) (ht : t ∈ T),
      IsMultiHomog t e ∧ ZeroOrHomog (a + fun k => (e k : ℤ)) F ∧
        x = LocalizedModule.mk (Ideal.Quotient.mk _ F) ⟨t, ht⟩) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨m, t, e, hte, hm, rfl⟩
    obtain ⟨F, hF, rfl⟩ := quotPart_normal y hm
    exact ⟨F, t, e, t.2, hte, hF, rfl⟩
  · exact ⟨0, 1, 0, one_mem _, GenOnFibres.homog_one, Or.inl rfl, by rw [map_zero, LocalizedModule.zero_mk]⟩
  · rintro _ _ ⟨F, t, e, ht, hte, hF, rfl⟩ ⟨G, s, f, hs, hsf, hG, rfl⟩
    refine ⟨s * F + t * G, t * s, e + f, mul_mem ht hs, GenOnFibres.homog_mul hte hsf,
      ((hF.mul hsf).congr ?_).add ((hG.mul hte).congr ?_), ?_⟩
    · funext k; simp only [Pi.add_apply]; push_cast; ring
    · funext k; simp only [Pi.add_apply]; push_cast; ring
    · rw [LocalizedModule.mk_add_mk, Submonoid.smul_def, Submonoid.smul_def, GenOnFibres.smul_mk, GenOnFibres.smul_mk,
        ← map_add]
      rfl
  · rintro _ ⟨F, t, e, ht, hte, hF, rfl⟩
    exact ⟨-F, t, e, ht, hte, hF.neg, by rw [map_neg, LocalizedModule.mk_neg]⟩

variable (p)

theorem ker_locPart [Fact p.Prime] (hP : IsMultiHomogIdeal (mCoordIdeal y)) (I : ∀ k, Finset (ι k)) (a : K → ℤ)
    {x : LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) (KH.cellMon ℤ I) a)
    (h0 : redLoc y p I x = 0) :
    ∃ x' ∈ KH.locPart ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) (KH.cellMon ℤ I) a, x = (p : ℤ) • x' := by
  obtain ⟨F, t, e, ht, hte, hF, rfl⟩ := locPart_normal y hx
  rcases hF with rfl | ⟨hc, hF⟩
  · exact ⟨0, zero_mem _, by simp⟩
  rw [redLoc_mk, redRing_mk] at h0
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp (h0.trans (LocalizedModule.zero_mk 1).symm)
  simp only [one_smul, smul_zero, Submonoid.smul_def, GenOnFibres.smul_mk] at hu
  rw [Ideal.Quotient.eq_zero_iff_mem] at hu
  obtain ⟨d, hud, hd⟩ := cellMon_lift u.2
  rw [hud, ← map_monomial_one p d, ← map_mul] at hu
  have hsurj : Function.Surjective
      (MvPolynomial.map (Int.castRingHom (ZMod p)) : MRingOver ℤ ι →+* MRingOver (ZMod p) ι) :=
    MvPolynomial.map_surjective _ ZMod.intCast_surjective
  have hmem : monomial d 1 * F ∈
      mCoordIdeal y ⊔ Ideal.comap (MvPolynomial.map (Int.castRingHom (ZMod p)) : MRingOver ℤ ι →+* _) ⊥ := by
    rw [← Ideal.comap_map_of_surjective _ hsurj]
    exact hu
  obtain ⟨q, hq, g0, hg0, hsum⟩ := Submodule.mem_sup.mp hmem
  have hg0' : g0 ∈ Ideal.span {C ((p : ℤ))} := by
    have h1 : g0 ∈ RingHom.ker (MvPolynomial.map (Int.castRingHom (ZMod p)) : MRingOver ℤ ι →+* _) := by
      rw [RingHom.mem_ker]
      exact Ideal.mem_bot.mp (Ideal.mem_comap.mp hg0)
    rwa [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton] at h1
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hg0'
  have hU : IsMultiHomog (monomial d 1 : MRingOver ℤ ι) fun k => ∑ i, d ⟨k, i⟩ := by
    classical
    exact GenOnFibres.homog_monomial d 1 _ fun k => rfl
  have hUF := GenOnFibres.homog_mul hU hF
  set D : K → ℕ := (fun k => ∑ i, d ⟨k, i⟩) + fun k => ((a + fun k => (e k : ℤ)) k).toNat with hDdef
  have hcomp := congrArg (weightedHomogeneousComponent blockWt D) hsum
  rw [map_add, mul_comm g, weightedHomogeneousComponent_C_mul,
    weightedHomogeneousComponent_eq_self ((isMultiHomog_iff _ _).mp hUF)] at hcomp
  have hq' := comp_mem hP hq D
  set g' := weightedHomogeneousComponent blockWt D g
  have hg' : IsMultiHomog g' D := (isMultiHomog_iff _ _).mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  have hD : D = fun k => ((a + fun k => (((fun k => ∑ i, d ⟨k, i⟩) + e) k : ℤ)) k).toNat := by
    funext k
    have := hc k
    simp only [hDdef, Pi.add_apply, Nat.cast_add] at this ⊢
    omega
  refine ⟨LocalizedModule.mk (Ideal.Quotient.mk _ g') ⟨_, mul_mem hd ht⟩,
    mk_mem_locPart (GenOnFibres.homog_mul hU hte) (Submodule.subset_span ⟨g', ⟨fun k => ?_, hD ▸ hg'⟩, rfl⟩), ?_⟩
  · have := hc k
    simp only [Pi.add_apply, Nat.cast_add] at this ⊢
    omega
  rw [← LocalizedModule.mk_cancel_common_left ⟨monomial d 1, hd⟩ ⟨t, ht⟩ (Ideal.Quotient.mk _ F),
    Submonoid.smul_def, GenOnFibres.smul_mk, ← Int.cast_smul_eq_zsmul (MRingOver ℤ ι), LocalizedModule.smul'_mk,
    GenOnFibres.smul_mk]
  congr 1
  rw [Ideal.Quotient.eq, idealOver_int]
  show monomial d 1 * F - ((p : ℤ) : MRingOver ℤ ι) * g' ∈ mCoordIdeal y
  rw [← hcomp, ← eq_intCast (C : ℤ →+* MRingOver ℤ ι) (p : ℤ)]
  convert hq' using 1
  ring

theorem eq_zero_of_p_smul (hP : (mCoordIdeal y).IsPrime) (hH : IsHorizontal (mCoordIdeal y)) (hp : p ≠ 0)
    (I : ∀ k, Finset (ι k)) (x : LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ))
    (h : (p : ℤ) • x = 0) : x = 0 := by
  have hpP : ((p : ℤ) : MRingOver ℤ ι) ∉ mCoordIdeal y := by
    intro hmem
    have h1 : (p : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRingOver ℤ ι) := by
      rw [Ideal.mem_comap, eq_intCast]
      exact hmem
    rw [hH, Ideal.mem_bot] at h1
    exact hp (by exact_mod_cast h1)
  induction x using LocalizedModule.induction_on with
  | h m t =>
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [← Int.cast_smul_eq_zsmul (MRingOver ℤ ι), LocalizedModule.smul'_mk, GenOnFibres.smul_mk] at h
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp (h.trans (LocalizedModule.zero_mk 1).symm)
    simp only [one_smul, smul_zero, Submonoid.smul_def, GenOnFibres.smul_mk] at hu
    rw [Ideal.Quotient.eq_zero_iff_mem, idealOver_int] at hu
    have hu' : (u : MRingOver ℤ ι) * F ∈ mCoordIdeal y := by
      refine (hP.mem_or_mem ?_).resolve_left hpP
      convert hu using 1
      ring
    refine (LocalizedModule.mk_eq.mpr ⟨u, ?_⟩).trans (LocalizedModule.zero_mk 1)
    simp only [one_smul, smul_zero, Submonoid.smul_def, GenOnFibres.smul_mk]
    rw [Ideal.Quotient.eq_zero_iff_mem, idealOver_int]
    exact hu'

theorem redLoc_p_smul (I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ)) :
    redLoc y p I ((p : ℤ) • x) = 0 := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul (MRingOver (ZMod p) ι)]
  have h : (((p : ℤ)) : MRingOver (ZMod p) ι) = 0 := by
    rw [Int.cast_natCast, ← map_natCast C, ZMod.natCast_self, map_zero]
  rw [h, zero_smul]

end Kernel

section Complex

theorem mem_cechCc_iff {S : Type} [CommRing S] {V : Ideal (MRingOver S ι)} {c : K → ℤ} {n : ℕ}
    {w : KH.CechC S ι (MRingOver S ι ⧸ V) n} :
    w ∈ KH.cechCc ι (KH.quotPart S V) c n ↔ ∀ I, w I ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) c := by
  unfold KH.cechCc
  rw [Submodule.mem_pi]
  simp

variable [LinearOrder K] [∀ k, LinearOrder (ι k)] (y : (Σ k, ι k) → Ω) (p : ℕ)

theorem redCoch_cechD (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) :
    redCoch y p (n + 1) (KH.cechD ℤ ι _ n w) = KH.cechD (ZMod p) ι _ n (redCoch y p n w) := by
  funext I
  simp only [redCoch_apply, KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · have hJ : ∀ l, Function.update I.1 k ((I.1 k).erase i) l ⊆ I.1 l := by
      intro l
      by_cases hl : l = k
      · subst hl
        rw [Function.update_self]
        exact Finset.erase_subset _ _
      · rw [Function.update_of_ne hl]
    show redLoc y p I.1 (KH.faceSign I.1 k i • KH.cellRes ℤ (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ)
        (Function.update I.1 k ((I.1 k).erase i)) I.1 (w ⟨_, h⟩)) =
      KH.faceSign I.1 k i • KH.cellRes (ZMod p) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p))
        (Function.update I.1 k ((I.1 k).erase i)) I.1 (redLoc y p _ (w ⟨_, h⟩))
    rw [map_zsmul, GenOnFibres.cellRes_of_le (GenOnFibres.cellMon_mono hJ),
      GenOnFibres.cellRes_of_le (GenOnFibres.cellMon_mono hJ)]
    congr 1
    induction w ⟨_, h⟩ using LocalizedModule.induction_on with
    | h m t => rw [liftOfLE_mk, redLoc_mk, redLoc_mk, liftOfLE_mk]
  · exact map_zero _

end Complex

end FibreReduction

open FibreReduction in

theorem ReductionComplex.proof : ReductionComplex.Statement := by
  intro K _ _ ι _ _ Ω _ y D p a hV hp
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨_, ⟨hprime, hhom, -⟩, hhor, -⟩ := hV
  refine ⟨fun n w => redCoch_cechD y p n w, fun n w hw => ?_, fun n z hz => ?_, fun n w hw h0 => ?_,
    fun n w h => ?_, fun n w => ?_⟩
  · exact mem_cechCc_iff.mpr fun I => redLoc_mem_locPart y p I.1 a (mem_cechCc_iff.mp hw I)
  · have hl : ∀ I : KH.Cell K ι n, ∃ x' ∈ KH.locPart ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) (KH.cellMon ℤ I.1) a,
        redLoc y p I.1 x' = z I := fun I => exists_lift_locPart y p I.1 a (mem_cechCc_iff.mp hz I)
    choose w hw hwz using hl
    exact ⟨w, mem_cechCc_iff.mpr fun I => hw I, funext hwz⟩
  · have hl : ∀ I : KH.Cell K ι n, ∃ x' ∈ KH.locPart ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) (KH.cellMon ℤ I.1) a,
        w I = (p : ℤ) • x' := fun I =>
      ker_locPart y p hhom I.1 a (mem_cechCc_iff.mp hw I) (by
        have h1 := congrFun h0 I
        rwa [redCoch_apply] at h1)
    choose w' hw' hww using hl
    exact ⟨w', mem_cechCc_iff.mpr fun I => hw' I, funext hww⟩
  · funext I
    exact eq_zero_of_p_smul y p hprime hhor hp.ne_zero I.1 (w I) (congrFun h I)
  · funext I
    rw [redCoch_apply]
    exact redLoc_p_smul y p I.1 (w I)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
