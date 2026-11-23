import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularAndBoundedTorsionOfAdicTopologicalBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDeltaOfPrismIdealEqSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinHomOfUniformizerFrameStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomImageXDeltaZeroLiftsUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomExtOfXStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingletonStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EnvRingExistsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingHomUniqueOfAdicTopologicalBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvCop

section
variable {l : ℕ}

theorem map_eq_span {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) : I.map f = Ideal.span {f d} := by
  subst hI; rw [Ideal.map_span, Set.image_singleton]

theorem map_sup_le {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (I : Ideal A) (I' : Ideal C)
    (h : ∀ a ∈ I, f a ∈ I') : (Ideal.span {(l : A)} ⊔ I).map f ≤ Ideal.span {(l : C)} ⊔ I' := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  exact sup_le_sup_left (Ideal.map_le_of_le_comap fun a ha => Ideal.mem_comap.2 (h a ha)) _

theorem eq_add_mul_of {R : Type} [CommRing R] {a b c v : R} (h : v * c = a - b) : a = b + c * v := by
  linear_combination -h

theorem map_span_mem {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (q : Q) (I : Ideal C)
    (hq : h q ∈ I) : ∀ a ∈ Ideal.span {q}, h a ∈ I := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [map_mul]; exact Ideal.mul_mem_left _ _ hq

theorem quot_eq_of {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (I : Ideal C) (a b : Q) (c : C)
    (hb : h b = c) (e : h (a - b) ∈ I) : Ideal.Quotient.mk I (h a) = Ideal.Quotient.mk I c := by
  subst hb; rw [map_sub] at e; exact Ideal.Quotient.eq.2 e

theorem eval_lin {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (x P D w : Q) (p d v : C)
    (hx : x = P + D * w) (hP : h P = p) (hD : h D = d) (hw : h w = v) : h x = p + d * v := by
  subst hx hP hD hw; rw [map_add, map_mul]

theorem cancel_of {C : Type} [CommRing C] {p d a v : C} (hd : d ∈ nonZeroDivisors C)
    (h : p + d * a = p + d * v) : a = v := by
  have e : d * (a - v) = 0 := by rw [mul_sub]; exact sub_eq_zero.2 (add_left_cancel h)
  exact sub_eq_zero.1 (hd.1 _ e)

theorem fg_sup_span {A : Type} [CommRing A] (I : Ideal A) (d : A) (hI : I = Ideal.span {d}) :
    (Ideal.span {(l : A)} ⊔ I).FG := by
  subst hI; exact (Submodule.fg_span_singleton _).sup (Submodule.fg_span_singleton _)
end

theorem comp_hf_X {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {P P' : Obj l ↥(OL K)} (h' : Hom P P')
    (g0 : Hom bk.prism P) (g : Hom bk.prism P') (h2 : h'.comp g0 = g) : h'.f (BK.hf g0 X) = BK.hf g X := by
  subst h2; rfl

section

variable {l : ℕ}

theorem quot_bdd_of_mem {A : Type} [CommRing A] (q : A) (N : ℕ)
    (h : ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {q} → (l : A) ^ N * x ∈ Ideal.span {q}) :
    ∀ x : A ⧸ Ideal.span {q}, (∃ m : ℕ, (l : A ⧸ Ideal.span {q}) ^ m * x = 0) →
      (l : A ⧸ Ideal.span {q}) ^ N * x = 0 := by
  rintro x ⟨m, hm⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hm' : (l : A) ^ m * y ∈ Ideal.span {q} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast]; exact hm
  have h2 := h y m hm'
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast] at h2
  exact h2

theorem pow_mul_mem_of_pow_mul_mem {A : Type} [CommRing A] (I : Ideal A) (N : ℕ)
    (h : ∀ x : A ⧸ I, (∃ m : ℕ, (l : A ⧸ I) ^ m * x = 0) → (l : A ⧸ I) ^ N * x = 0) :
    ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ I → (l : A) ^ N * x ∈ I := by
  intro x m hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast] at hm ⊢
  exact h _ ⟨m, hm⟩

theorem map_sup_span {A Q : Type} [CommRing A] [CommRing Q] (i : A →+* Q) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) :
    (Ideal.span {(l : A)} ⊔ I).map i = Ideal.span {(l : Q)} ⊔ Ideal.span {i d} := by
  subst hI
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]

theorem le_comap_span {A Q : Type} [CommRing A] [CommRing Q] (i : A →+* Q) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) : I ≤ (Ideal.span {i d}).comap i := by
  subst hI
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [Ideal.mem_comap, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {B : Obj l ↥(OL K)} {d p : B.A}

section
variable (hI : B.I = Ideal.span {d}) (En : EnvRing B.D (JJ B) d p)
include hI

theorem facts : ∃ N : ℕ, En.i d ∈ nonZeroDivisors En.Q ∧ ∀ (x : En.Q) (m : ℕ),
    (l : En.Q) ^ m * x ∈ Ideal.span {En.i d} → (l : En.Q) ^ N * x ∈ Ideal.span {En.i d} := by
  obtain ⟨N, hN⟩ := B.bdd
  have hnz : d ∈ nonZeroDivisors B.A := by
    have h := B.inv; rw [hI] at h; exact GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' _ d h
  have hb : ∀ (x : B.A) (m : ℕ), (l : B.A) ^ m * x ∈ Ideal.span {d} → (l : B.A) ^ N * x ∈ Ideal.span {d} := by
    rw [← hI]; exact pow_mul_mem_of_pow_mul_mem B.I N hN
  have tb : TopBasis En.i (Ideal.span {(l : B.A)} ⊔ Ideal.span {d}) (Digits l) := by
    rw [← hI]; exact En.tb
  exact ⟨N, GlobalTheory.T.regular_and_bounded_torsion_of_adicTopologicalBasis l B.A En.Q En.i d N (Digits l) hnz hb tb⟩

def strQ : ↥(OL K) →+* En.Q ⧸ Ideal.span {En.i d} :=
  (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)).comp B.str

theorem strQ_eq (r : ↥(OL K)) (b : B.A) (hb : Ideal.Quotient.mk B.I b = B.str r) :
    strQ hI En r = Ideal.Quotient.mk (Ideal.span {En.i d}) (En.i b) :=
  (congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)) hb).symm.trans
    Ideal.quotientMap_mk

abbrev obj : Obj l ↥(OL K) where
  A := En.Q
  D := En.DQ
  I := Ideal.span {En.i d}
  inv := invertible_span_singleton (facts hI En).choose_spec.1
  complete := by rw [← map_sup_span En.i B.I d hI]; exact En.tb.complete
  l_mem := En.DQ.l_mem_of_isUnit hl.out.pos (by rw [← En.i_δ d]; exact (GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span l _ B d hI).map En.i)
  bdd := ⟨(facts hI En).choose, quot_bdd_of_mem (En.i d) _ (facts hI En).choose_spec.2⟩
  str := strQ hI En

def inl : Hom B (obj hI En) where
  f := En.i
  f_δ := En.i_δ
  f_I a ha := le_comap_span En.i B.I d hI ha
  f_str r a h := Ideal.quotientMap_mk.symm.trans
    (congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)) h)

end

variable {bk : BK K} (En : EnvRing B.D (JJ B) d p)

theorem frame (hF : IsFrame bk B d p) : IsFrame bk (obj hF.1 En) (En.i d) (En.i p + En.i d * En.w) := by
  refine ⟨rfl, ?_⟩
  have e1 := congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hF.1)) hF.2
  have e2 : En.i p + En.i d * En.w - En.i p ∈ Ideal.span {En.i d} := by
    rw [add_sub_cancel_left]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  exact (Ideal.Quotient.eq.2 e2).trans (Ideal.quotientMap_mk.symm.trans e1)

theorem str_of (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0a : ∀ a, h0 (En.i a) = f.f a) (hIQ : ∀ a ∈ Ideal.span {En.i d}, h0 a ∈ C.I) (r : ↥(OL K)) (a : En.Q)
    (ha : Ideal.Quotient.mk (Ideal.span {En.i d}) a = strQ hI En r) :
    Ideal.Quotient.mk C.I (h0 a) = C.str r := by
  have hsu : ∃ b : B.A, Ideal.Quotient.mk B.I b = B.str r := Ideal.Quotient.mk_surjective (B.str r)
  obtain ⟨b, hb⟩ := hsu
  have e1 : Ideal.Quotient.mk (Ideal.span {En.i d}) a = Ideal.Quotient.mk (Ideal.span {En.i d}) (En.i b) :=
    ha.trans (strQ_eq hI En r b hb)
  have hab : a - En.i b ∈ Ideal.span {En.i d} := Ideal.Quotient.eq.1 e1
  exact (quot_eq_of h0 C.I a (En.i b) (f.f b) (h0a b) (hIQ _ hab)).trans (f.f_str r b hb)

theorem I_of (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0a : ∀ a, h0 (En.i a) = f.f a) : ∀ a ∈ Ideal.span {En.i d}, h0 a ∈ C.I :=
  map_span_mem h0 (En.i d) C.I ((congrArg (· ∈ C.I) (h0a d)).mpr
    (f.f_I d (by rw [hI]; exact Ideal.mem_span_singleton_self d)))

def lift (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0δ : IsδMap En.DQ C.D h0) (h0a : ∀ a, h0 (En.i a) = f.f a) : Hom (obj hI En) C where
  f := h0
  f_δ := h0δ
  f_I := I_of En hI f h0 h0a
  f_str := str_of En hI f h0 h0a (I_of En hI f h0 h0a)

set_option maxHeartbeats 2000000 in

theorem univ (hF : IsFrame bk B d p) (g0 : Hom bk.prism (obj hF.1 En))
    (hg0 : BK.hf g0 X = En.i p + En.i d * En.w) (C : Obj l ↥(OL K)) (f : Hom B C)
    (g : Hom bk.prism C) : ∃! h : Hom (obj hF.1 En) C, h.comp (inl hF.1 En) = f ∧ h.comp g0 = g := by
  have hdI : d ∈ B.I := by rw [hF.1]; exact Ideal.mem_span_singleton_self d
  have hCI : C.I = Ideal.span {f.f d} :=
    (GlobalTheory.T.prism_hom_map_ideal_eq l _ B C f).symm.trans (map_eq_span f.f B.I d hF.1)
  have hnz : f.f d ∈ nonZeroDivisors C.A := by
    have h := C.inv; rw [hCI] at h; exact GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' _ _ h
  obtain ⟨hgδ, hgs⟩ := GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer l K bk C g
  have hfp := f.f_str _ p hF.2
  have hmem : BK.hf g X - f.f p ∈ Ideal.span {f.f d} := by
    rw [← hCI]; exact Ideal.Quotient.eq.1 (hgs.trans hfp.symm)
  have hex : ∃ v', v' * f.f d = BK.hf g X - f.f p := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨v', hv'⟩ := hex
  have hgX : BK.hf g X = f.f p + f.f d * v' := eq_add_mul_of hv'
  have hrel : C.D.δ (f.f p + f.f d * v') = 0 := (congrArg C.D.δ hgX).symm.trans hgδ
  have hJ : (JJ B).map f.f ≤ JJ C := map_sup_le f.f B.I C.I f.f_I
  have hlift : ∃ h : En.Q →+* C.A, IsδMap En.DQ C.D h ∧ h.comp En.i = f.f ∧ h En.w = v' :=
    En.lift C.A C.D (JJ C) C.complete f.f f.f_δ hJ v' hrel
  obtain ⟨h0, h0δ, h0i, h0w⟩ := hlift
  have h0a : ∀ a, h0 (En.i a) = f.f a := fun a => RingHom.congr_fun h0i a
  refine ⟨lift En hF.1 f h0 h0δ h0a, ⟨Hom.ext' h0i, GlobalTheory.T.breuilKisin_prism_hom_ext_of_X l K bk C _ _ ?_⟩, ?_⟩
  · exact (eval_lin h0 _ _ _ _ _ _ _ hg0 (h0a p) (h0a d) h0w).trans hgX.symm
  · rintro h' ⟨h1, h2⟩
    have e1 : h'.f.comp En.i = f.f := congrArg Hom.f h1
    have e1a : ∀ a, h'.f (En.i a) = f.f a := fun a => RingHom.congr_fun e1 a
    have e2 := comp_hf_X h' g0 g h2
    have e3 : h'.f En.w = v' :=
      cancel_of hnz ((eval_lin h'.f (BK.hf g0 X) (En.i p) (En.i d) En.w (f.f p) (f.f d) (h'.f En.w) hg0 (e1a p) (e1a d) rfl).symm.trans (e2.trans hgX))
    have hJ' : (JJ B).map (h'.f.comp En.i) ≤ JJ C := (congrArg (fun φ => (JJ B).map φ ≤ JJ C) e1).mpr hJ
    exact Hom.ext' (GlobalTheory.T.deltaRingHom_unique_of_adicTopologicalBasis l B.A En.Q C.A En.DQ C.D (JJ B) (JJ C) En.i En.w En.tb En.tb_b
      C.complete.toIsHausdorff h'.f h0 h'.f_δ h0δ hJ' (e1.trans h0i.symm) (e3.trans h0w.symm))

def env (hF : IsFrame bk B d p) : Env bk B d p :=
  have hex := GlobalTheory.T.exists_breuilKisinHom_of_uniformizerFrame l K bk (obj hF.1 En) (En.i d) (En.i p + En.i d * En.w) (frame En hF) En.rel
  { Q := obj hF.1 En
    inl := inl hF.1 En
    inr := hex.choose
    univ := univ En hF hex.choose hex.choose_spec
    w := En.w
    w_eq := hex.choose_spec
    I_eq := rfl
    tb := En.tb
    tb_b := En.tb_b }

end GlobalTheory.BSP.EnvCop

open GlobalTheory.BSP.EnvCop in

theorem GlobalTheory.BSP.nonempty_env : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (d p : B.A), IsFrame bk B d p → Nonempty (Env bk B d p) := by
  intro l _ K bk B d p hF
  have hd : d ∈ JJ B := Ideal.mem_sup_right (by rw [hF.1]; exact Ideal.mem_span_singleton_self d)
  have hEn : Nonempty (EnvRing B.D (JJ B) d p) :=
    GlobalTheory.T.nonempty_envRing l B.A B.D (JJ B) d p (fg_sup_span B.I d hF.1)
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (l : B.A))) hd (GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span l _ B d hF.1) B.complete
  exact ⟨env hEn.some hF⟩
