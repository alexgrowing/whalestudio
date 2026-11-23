import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.SecJetCmp

section Val

variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

private def valHom (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (x.appLE U ⊤ h).hom

private theorem valR_eq (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = valHom x U h f := by
  unfold valR
  rw [dif_pos h]
  rfl

private theorem valR_res (x : Sp R ⟶ X) {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_eq x V h, valR_eq x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]
  rfl

private theorem valR_spMap {R' : Type} [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U ∧ ∀ f, valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun y _ => h (Set.mem_univ ((spMap φ) y))
  refine ⟨h', fun f => ?_⟩
  rw [valR_eq _ U h', valR_eq x U h]
  have e : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change ((spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom).hom f =
    (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ).hom f
  rw [e, Category.assoc, n]

private theorem valR_comp (x : Sp R ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valR (x ≫ g) U f = valR x (g ⁻¹ᵁ U) ((g.app U).hom f) := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ U)
  · rw [valR_eq _ _ h, valR_eq (x ≫ g) U h]
    change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (((x ≫ g).appLE U ⊤ h).hom f) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.app U ≫ x.appLE (g ⁻¹ᵁ U) ⊤ h).hom f)
    rw [Scheme.Hom.comp_appLE x g U ⊤ h]
  · unfold valR
    rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (x ≫ g) ⁻¹ᵁ U from h)]

private theorem valAt'_eq (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valAt' x U f = valR x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · unfold valAt' valR
    rw [dif_pos h, dif_pos h]
    rfl
  · unfold valAt' valR
    rw [dif_neg h, dif_neg h]

private theorem eq_spMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    spMap (valHom x U h) ≫ hU.fromSpec = x := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp R)) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  change Spec.map (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp]
  simp

private theorem valR_fromSpec {U : X.Opens} (hU : IsAffineOpen U) :
    ⊤ ≤ (show Sp Γ(X, U) ⟶ X from hU.fromSpec) ⁻¹ᵁ U ∧
      ∀ f, valR (A := Γ(X, U)) hU.fromSpec U f = f := by
  have h : ⊤ ≤ (show Sp Γ(X, U) ⟶ X from hU.fromSpec) ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  refine ⟨h, fun f => ?_⟩
  rw [valR_eq _ _ h]
  have e := eq_spMap_fromSpec (R := Γ(X, U)) hU hU.fromSpec h
  have e2 : spMap (valHom (R := Γ(X, U)) hU.fromSpec U h) = 𝟙 _ := by
    rw [← cancel_mono hU.fromSpec]
    exact e.trans (Category.id_comp _).symm
  have e3 : CommRingCat.ofHom (valHom (R := Γ(X, U)) hU.fromSpec U h) = 𝟙 _ :=
    Spec.map_injective (e2.trans (Spec.map_id _).symm)
  exact congrArg (fun φ : CommRingCat.of Γ(X, U) ⟶ CommRingCat.of Γ(X, U) => φ.hom f) e3

end Val

section Der

variable {R T : Type} [CommRing R] [CommRing T]

private def dl (s : R →+* T) (e : T) (he : e * e = 0) : DualNumber R →+* T where
  toFun a := s a.fst + e * s a.snd
  map_one' := by simp
  map_mul' a b := by
    simp only [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, map_mul, map_add]
    linear_combination (-(s a.snd * s b.snd)) * he
  map_zero' := by simp
  map_add' a b := by simp; ring

private theorem dl_apply (s : R →+* T) (e : T) (he : e * e = 0) (a : DualNumber R) :
    dl s e he a = s a.fst + e * s a.snd := rfl

private theorem spMap_fst_surj (z : Sp (DualNumber R)) : ∃ z', spMap (TrivSqZeroExt.fstHom R R R).toRingHom z' = z := by
  have : z ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
    intro a ha
    refine (show PrimeSpectrum (DualNumber R) from z).2.mem_of_pow_mem 2 ?_
    have ha' : a.fst = 0 := ha
    have : a ^ 2 = 0 := by
      ext <;> simp [sq, ha']
    rw [this]
    exact zero_mem _
  exact this

private theorem exists_der {G : Over (Sp R)} [GrpObj G] {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens}
    (hU : IsAffineOpen U) (f : Γ(G.left, U)) :
    ∃ f' : Γ(G.left, U), ∀ (T : Type) [CommRing T] (s : R →+* T) (e : T) (he : e * e = 0)
      (t : Sp T ⟶ Sp R) (_ : t = spMap s)
      (j : Over.mk t ⟶ epsR R) (p : Over.mk t ⟶ G), j.left = spMap (dl s e he) →
      ⊤ ≤ p.left ⁻¹ᵁ U → ⊤ ≤ ((j ≫ y) * p).left ⁻¹ᵁ U ∧
        valR (A := T) ((j ≫ y) * p).left U f = valR (A := T) p.left U f + e * valR (A := T) p.left U f' := by
  obtain ⟨sB', hsB⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := Γ(G.left, U)) (hU.fromSpec ≫ G.hom)
  let B : Type := Γ(G.left, U)
  let sB : R →+* B := sB'.hom
  have hsB' : spMap sB = hU.fromSpec ≫ G.hom := hsB
  let ic : B →+* DualNumber B := algebraMap B (DualNumber B)
  let π : DualNumber B →+* B := (TrivSqZeroExt.fstHom B B B).toRingHom
  let jC : Over.mk (spMap (ic.comp sB)) ⟶ epsR R :=
    Over.homMk (spMap (dl (ic.comp sB) DualNumber.eps DualNumber.eps_mul_eps)) (by
      refine (spMap_comp_spMap _ _).trans ?_
      congr 1
      ext a <;> simp [dl_apply, ic, TrivSqZeroExt.algebraMap_eq_inl])
  let xC : Over.mk (spMap (ic.comp sB)) ⟶ G :=
    Over.homMk (spMap ic ≫ hU.fromSpec) (by
      rw [Category.assoc, ← hsB']
      exact spMap_comp_spMap _ _)
  let q : Over.mk (spMap sB) ⟶ Over.mk (spMap (ic.comp sB)) :=
    Over.homMk (spMap π) (by
      refine (spMap_comp_spMap _ _).trans ?_
      congr 1)
  have hq1 : q ≫ jC ≫ y = 1 := by
    ext1
    have e1 : spMap π ≫ spMap (dl (ic.comp sB) DualNumber.eps DualNumber.eps_mul_eps) =
        spMap sB ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
      rw [spMap_comp_spMap, spMap_comp_spMap]
      congr 1
      refine RingHom.ext fun a => ?_
      simp [dl_apply, ic, π, TrivSqZeroExt.algebraMap_eq_inl]
    change spMap π ≫ spMap (dl (ic.comp sB) DualNumber.eps DualNumber.eps_mul_eps) ≫ y.left = _
    rw [← Category.assoc, e1, Category.assoc, hy]
    rfl
  have hq : spMap π ≫ ((jC ≫ y) * xC).left = hU.fromSpec := by
    change (q ≫ ((jC ≫ y) * xC)).left = _
    rw [MonObj.comp_mul, hq1, _root_.one_mul]
    change spMap π ≫ spMap ic ≫ hU.fromSpec = _
    rw [← Category.assoc, spMap_comp_spMap]
    refine Eq.trans ?_ (Category.id_comp _)
    congr 1
    exact Spec.map_id (CommRingCat.of B)
  have hC : ⊤ ≤ ((jC ≫ y) * xC).left ⁻¹ᵁ U := by
    intro z _
    obtain ⟨z', rfl⟩ := spMap_fst_surj (R := B) z
    have : z' ∈ (spMap π ≫ ((jC ≫ y) * xC).left) ⁻¹ᵁ U := by
      rw [hq]
      exact (valR_fromSpec hU).1 (Set.mem_univ _)
    exact this
  have hf : (valR (A := DualNumber B) ((jC ≫ y) * xC).left U f).fst = f := by
    have := (valR_spMap π ((jC ≫ y) * xC).left U hC).2 f
    rw [hq, (valR_fromSpec hU).2] at this
    exact this.symm
  refine ⟨(valR (A := DualNumber B) ((jC ≫ y) * xC).left U f).snd, ?_⟩
  rintro T _ s e he _ rfl j p hj hp
  let β : B →+* T := valHom (R := T) p.left U hp
  have hβ : spMap β ≫ hU.fromSpec = p.left := eq_spMap_fromSpec (R := T) hU p.left hp
  have hs : β.comp sB = s := by
    have : spMap (β.comp sB) = spMap s := by
      rw [← spMap_comp_spMap, hsB', ← Category.assoc, hβ]
      exact Over.w p
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  let gm : Over.mk (spMap s) ⟶ Over.mk (spMap (ic.comp sB)) :=
    Over.homMk (spMap (dl β e he)) (by
      refine (spMap_comp_spMap _ _).trans ?_
      congr 1

      rw [← hs]
      refine RingHom.ext fun a => ?_
      simp [dl_apply, ic, TrivSqZeroExt.algebraMap_eq_inl])
  have h1 : gm ≫ jC = j := by
    ext1
    rw [hj]
    refine (spMap_comp_spMap _ _).trans ?_
    congr 1
    rw [← hs]
    refine RingHom.ext fun a => ?_
    simp [dl_apply, ic, TrivSqZeroExt.algebraMap_eq_inl]
  have h2 : gm ≫ xC = p := by
    ext1
    rw [← hβ]
    change spMap (dl β e he) ≫ spMap ic ≫ hU.fromSpec = _
    rw [← Category.assoc, spMap_comp_spMap]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dl_apply, ic, TrivSqZeroExt.algebraMap_eq_inl]
  have h3 : ((j ≫ y) * p).left = spMap (dl β e he) ≫ ((jC ≫ y) * xC).left := by
    change _ = (gm ≫ ((jC ≫ y) * xC)).left
    rw [MonObj.comp_mul, h2, ← Category.assoc, h1]
  obtain ⟨k1, k2⟩ := valR_spMap (dl β e he) ((jC ≫ y) * xC).left U hC
  rw [h3]
  refine ⟨k1, (k2 f).trans ?_⟩
  rw [dl_apply, hf, valR_eq _ _ hp, valR_eq _ _ hp]

end Der

section Top

variable {R : Type} [CommRing R]

private def jp {k : ℕ} (a : ℕ → R) (l : List (Fin k)) : ℕ → MvPolynomial (Fin k) R :=
  l.foldr (fun x F n => F n + MvPolynomial.X x * F (n + 1)) (fun n => MvPolynomial.C (a n))

private theorem jp_nil {k : ℕ} (a : ℕ → R) (n : ℕ) : jp (k := k) a [] n = MvPolynomial.C (a n) := rfl

private theorem jp_cons {k : ℕ} (a : ℕ → R) (x : Fin k) (l : List (Fin k)) (n : ℕ) :
    jp a (x :: l) n = jp a l n + MvPolynomial.X x * jp a l (n + 1) := rfl

private theorem jp_supp {k : ℕ} (a : ℕ → R) (l : List (Fin k)) :
    ∀ (n : ℕ) (d : Fin k →₀ ℕ) (x : Fin k), x ∉ l → d x ≠ 0 → MvPolynomial.coeff d (jp a l n) = 0 := by
  induction l with
  | nil =>
    intro n d x _ hd
    rw [jp_nil, MvPolynomial.coeff_C, if_neg]
    rintro rfl
    exact hd rfl
  | cons z l ih =>
    intro n d x hx hd
    rw [List.mem_cons, not_or] at hx
    rw [jp_cons, MvPolynomial.coeff_add, ih n d x hx.2 hd, MvPolynomial.coeff_X_mul', zero_add]
    split_ifs with h
    · refine ih _ _ x hx.2 ?_
      simpa [Finsupp.single_apply, Ne.symm hx.1] using hd
    · rfl

private theorem jp_top {k : ℕ} (a : ℕ → R) (l : List (Fin k)) (hl : l.Nodup) :
    ∀ n : ℕ, MvPolynomial.coeff (l.map fun x => Finsupp.single x 1).sum (jp a l n) = a (n + l.length) := by
  induction l with
  | nil => intro n; simp [jp_nil]
  | cons z l ih =>
    intro n
    rw [List.nodup_cons] at hl
    rw [jp_cons, MvPolynomial.coeff_add, jp_supp a l n _ z hl.1 (by simp), zero_add, List.map_cons, List.sum_cons,
      MvPolynomial.coeff_X_mul, ih hl.2, List.length_cons]
    congr 1
    omega

private theorem topCoeff_jp {k : ℕ} (a : ℕ → R) :
    topCoeff R k (Ideal.Quotient.mk _ (jp a (List.finRange k) 0)) = a k := by
  have := jp_top a (List.finRange k) (List.nodup_finRange k) 0
  rw [zero_add, List.length_finRange] at this
  rw [← this]
  change MvPolynomial.coeff (topMon k) _ = _
  rw [topMon, Fin.sum_univ_def]
  rfl

private theorem epsIn_left {k : ℕ} (x : Fin k) :
    (epsIn R x).left = spMap (dl (algebraMap R (EpsAlg R k)) (eps R x) (eps_mul_self R x)) := by
  change spMap _ = _
  congr 1
  refine RingHom.ext fun z => ?_
  rw [dl_apply]
  simp [epsIncl, DualNumber.lift_apply_apply, mul_comm]

private theorem jetVal_eq {G : Over (Sp R)} [GrpObj G] {y : epsR R ⟶ G} {U : G.left.Opens} (h0 : ⊤ ≤ eSec G ⁻¹ᵁ U)
    (f : ℕ → Γ(G.left, U))
    (hf : ∀ n, ∀ (T : Type) [CommRing T] (s : R →+* T) (e : T) (he : e * e = 0)
      (t : Sp T ⟶ Sp R) (_ : t = spMap s)
      (j : Over.mk t ⟶ epsR R) (p : Over.mk t ⟶ G), j.left = spMap (dl s e he) →
      ⊤ ≤ p.left ⁻¹ᵁ U → ⊤ ≤ ((j ≫ y) * p).left ⁻¹ᵁ U ∧
        valR (A := T) ((j ≫ y) * p).left U (f n) =
          valR (A := T) p.left U (f n) + e * valR (A := T) p.left U (f (n + 1))) (k : ℕ) :
    ⊤ ≤ (SecJet.epsPt y k).left ⁻¹ᵁ U ∧ jetVal y k U (f 0) = valR (A := R) (eSec G) U (f k) := by
  have key : ∀ (l : List (Fin k)) (n : ℕ), ⊤ ≤ ((l.map fun x => epsIn R x ≫ y).prod).left ⁻¹ᵁ U ∧
      valR (A := EpsAlg R k) ((l.map fun x => epsIn R x ≫ y).prod).left U (f n) =
        Ideal.Quotient.mk _ (jp (fun m => valR (A := R) (eSec G) U (f m)) l n) := by
    intro l
    induction l with
    | nil =>
      intro n
      obtain ⟨k1, k2⟩ := valR_spMap (algebraMap R (EpsAlg R k)) (eSec G) U h0
      exact ⟨k1, k2 (f n)⟩
    | cons z l ih =>
      intro n
      obtain ⟨k1, k2⟩ := hf n (EpsAlg R k) (algebraMap R _) (eps R z) (eps_mul_self R z) _ rfl (epsIn R z) _
        (epsIn_left z) (ih n).1
      rw [List.map_cons, List.prod_cons]
      refine ⟨k1, k2.trans ?_⟩
      rw [(ih n).2, (ih (n + 1)).2, jp_cons, map_add, map_mul]
      rfl
  have e : SecJet.epsPt y k = ((List.finRange k).map fun x => epsIn R x ≫ y).prod := by
    rw [SecJet.epsPt, List.ofFn_eq_map]
  rw [jetVal, e]
  refine ⟨(key _ 0).1, ?_⟩
  rw [(key _ 0).2, topCoeff_jp]

end Top

section An

open Topology Filter

private theorem iteratedDeriv_chain (g : ℕ → ℂ → ℂ) {O : Set ℂ} (hO : IsOpen O)
    (h : ∀ n, ∀ t ∈ O, HasDerivAt (g n) (g (n + 1) t) t) (n : ℕ) : ∀ t ∈ O, iteratedDeriv n (g 0) t = g n t := by
  induction n with
  | zero => intro t _; rfl
  | succ n ih =>
    intro t ht
    rw [iteratedDeriv_succ, ← (h n t ht).deriv]
    refine EventuallyEq.deriv_eq ?_
    filter_upwards [hO.mem_nhds ht] with z hz using ih z hz

private theorem iteratedDeriv_mul_of_vanish {B h : ℂ → ℂ} (hB : AnalyticAt ℂ B 0) (hh : AnalyticAt ℂ h 0) (i : ℕ)
    (hv : ∀ m < i, iteratedDeriv m B 0 = 0) :
    iteratedDeriv i (fun t => B t * h t) 0 = iteratedDeriv i B 0 * h 0 := by
  rw [iteratedDeriv_fun_mul hB.contDiffAt hh.contDiffAt, Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp
  · intro m hm
    rw [hv m (Finset.mem_range.1 hm)]
    simp

private theorem filt_vanish {K V : Type} [Field K] [AddCommGroup V] [Module K V] (j : ℕ → V →ₗ[K] K) (c : V) (i : ℕ)
    (hc : c ∈ filt j i) : ∀ m < i, j m c = 0 := by
  induction i with
  | zero => intro m hm; omega
  | succ i ih =>
    intro m hm
    rw [filt_succ] at hc
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | rfl
    · exact ih hc.1 m h
    · exact hc.2

end An

section Hol

open Topology Filter

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
  (u : HolUnif A L g)

private theorem ex_zero_left : (u.ex 0).left = eSec A := by
  have h : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
  rw [h, Hom.one_def, show toUnit (𝟙_ (Over (Sp ℂ))) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
  rfl

private theorem hol_valR (U : A.left.Opens) (f : Γ(A.left, U)) : IsOpen {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valR (A := ℂ) (u.ex z).left U f) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
  have := u.hol U f
  simp only [valAt'_eq] at this
  exact this

private theorem fderiv_eq {σ : K →+* ℂ} {ψ : A.left ⟶ G.left} (hψ : IsGrpPullback A G (spMap σ) ψ) {y : epsR K ⟶ G}
    {yq : epsR ℂ ⟶ A} (hv : IsVecOver σ ψ y yq) {Y0 : Fin g → ℂ} (hd : u.IsDiff Y0 yq) {U : G.left.Opens}
    (f f' : Γ(G.left, U))
    (hf : ∀ (T : Type) [CommRing T] (s : K →+* T) (e : T) (he : e * e = 0)
      (t : Sp T ⟶ Sp K) (_ : t = spMap s)
      (j : Over.mk t ⟶ epsR K) (p : Over.mk t ⟶ G), j.left = spMap (dl s e he) →
      ⊤ ≤ p.left ⁻¹ᵁ U → ⊤ ≤ ((j ≫ y) * p).left ⁻¹ᵁ U ∧
        valR (A := T) ((j ≫ y) * p).left U f = valR (A := T) p.left U f + e * valR (A := T) p.left U f')
    (z : Fin g → ℂ) (hz : ⊤ ≤ ((u.ex z).left ≫ ψ) ⁻¹ᵁ U) :
    fderiv ℂ (fun w => valR (A := ℂ) ((u.ex w).left ≫ ψ) U f) z Y0 = valR (A := ℂ) ((u.ex z).left ≫ ψ) U f' := by
  let ic : ℂ →+* DualNumber ℂ := algebraMap ℂ (DualNumber ℂ)
  let tz : A ⟶ A := 𝟙 A * (toUnit A ≫ u.ex z)
  have htz : ∀ {T : Over (Sp ℂ)} (x : T ⟶ A), x ≫ tz = x * (toUnit T ≫ u.ex z) := by
    intro T x
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  let cz : epsR ℂ ⟶ A := toUnit _ ≫ u.ex z
  have hcz : cz.left = spMap ic ≫ (u.ex z).left := rfl
  have ht : (epsR ℂ).hom ≫ spMap σ = spMap (ic.comp σ) := spMap_comp_spMap _ _
  have hdm : Chart.dualMapR σ = dl (ic.comp σ) DualNumber.eps DualNumber.eps_mul_eps := by
    refine RingHom.ext fun a => ?_
    rw [dl_apply]
    ext <;> simp [Chart.dualMapR, ic, TrivSqZeroExt.algebraMap_eq_inl]
  let j : Over.mk ((epsR ℂ).hom ≫ spMap σ) ⟶ epsR K := Over.homMk (spMap (Chart.dualMapR σ)) (by
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ ht.symm)
    congr 1
    refine RingHom.ext fun a => ?_
    ext <;> simp [Chart.dualMapR, ic, TrivSqZeroExt.algebraMap_eq_inl])
  let p : Over.mk ((epsR ℂ).hom ≫ spMap σ) ⟶ G := Over.homMk (cz.left ≫ ψ) (by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w cz]
    rfl)
  have hp : p.left = spMap ic ≫ ((u.ex z).left ≫ ψ) := rfl
  obtain ⟨q1, q2⟩ := valR_spMap ic ((u.ex z).left ≫ ψ) U hz
  obtain ⟨k1, k2⟩ := hf (DualNumber ℂ) (ic.comp σ) DualNumber.eps DualNumber.eps_mul_eps _ ht j p
    (congrArg spMap hdm) q1
  have hm : ((j ≫ y) * p).left = yq.left ≫ (tz.left ≫ ψ) := by
    rw [hψ.2 (epsR ℂ) yq cz (j ≫ y) p hv.symm rfl, ← htz yq]
    rfl
  rw [hm] at k1 k2
  have hD := hd ((tz.left ≫ ψ) ⁻¹ᵁ U) k1 (((tz.left ≫ ψ).app U).hom f)
  have e1 : (fun w => valAt' (u.ex w).left ((tz.left ≫ ψ) ⁻¹ᵁ U) (((tz.left ≫ ψ).app U).hom f)) =
      fun w => (fun w => valR (A := ℂ) ((u.ex w).left ≫ ψ) U f) (w + z) := by
    funext w
    beta_reduce
    rw [valAt'_eq, ← valR_comp, u.ex_add]
    have : u.ex w * u.ex z = u.ex w ≫ tz := by
      rw [htz, show toUnit (𝟙_ (Over (Sp ℂ))) = 𝟙 _ from Subsingleton.elim _ _, Category.id_comp]
    rw [this]
    rfl
  rw [e1, fderiv_comp_add_right (f := fun w => valR (A := ℂ) ((u.ex w).left ≫ ψ) U f), zero_add] at hD
  rw [← hD]
  have e2 := valR_comp (R := DualNumber ℂ) yq.left (tz.left ≫ ψ) U f
  rw [valR_eq (R := DualNumber ℂ) yq.left ((tz.left ≫ ψ) ⁻¹ᵁ U) k1, k2, hp, q2, q2] at e2
  refine (congrArg TrivSqZeroExt.snd e2.symm).trans ?_
  simp [ic, TrivSqZeroExt.algebraMap_eq_inl]

private theorem jetVal_eq_iteratedDeriv {σ : K →+* ℂ} {ψ : A.left ⟶ G.left} (hψ : IsGrpPullback A G (spMap σ) ψ)
    {y : epsR K ⟶ G} (hy : IsTangent y)
    {yq : epsR ℂ ⟶ A} (hv : IsVecOver σ ψ y yq) {Y0 : Fin g → ℂ} (hd : u.IsDiff Y0 yq) {V : G.left.Opens}
    (hV : ⊤ ≤ eSec G ⁻¹ᵁ V) (f : Γ(G.left, V)) (n : ℕ) :
    σ (jetVal y n V f) = iteratedDeriv n (fun t : ℂ => valR (A := ℂ) ((u.ex (t • Y0)).left ≫ ψ) V f) 0 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, hUV⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show eSec G (default : Sp K) ∈ (V : Set G.left) from hV (Set.mem_univ _)) V.2
  replace hUV : U ≤ V := hUV
  replace hU : IsAffineOpen U := hU
  have h0 : ⊤ ≤ eSec G ⁻¹ᵁ U := by
    intro x _
    rw [Subsingleton.elim (α := Sp K) x default]
    exact hx
  choose D hD using fun f : Γ(G.left, U) => exists_der hy hU f
  let F : ℕ → Γ(G.left, U) := fun m => D^[m] (resG _ hUV f)
  have hF : ∀ m, F (m + 1) = D (F m) := fun m => Function.iterate_succ_apply' _ _ _
  obtain ⟨j1, j2⟩ := jetVal_eq (y := y) h0 F (fun m => by rw [hF]; exact hD (F m)) n
  have j3 : jetVal y n V f = jetVal y n U (F 0) := by
    rw [jetVal, jetVal]
    exact congrArg _ (valR_res _ hUV j1 f).symm
  have hO := (hol_valR u (ψ ⁻¹ᵁ U) 0).1
  have hc : Continuous fun t : ℂ => t • Y0 := by fun_prop
  have he : (u.ex ((0 : ℂ) • Y0)).left ≫ ψ = spMap σ ≫ eSec G := by
    rw [zero_smul, ex_zero_left]
    exact PolBaseChange.eSec_comm hψ
  obtain ⟨q1, q2⟩ := valR_spMap σ (eSec G) U h0
  have h0' : (0 : ℂ) ∈ (fun t : ℂ => t • Y0) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (ψ ⁻¹ᵁ U)} := by
    change ⊤ ≤ ((u.ex ((0 : ℂ) • Y0)).left ≫ ψ) ⁻¹ᵁ U
    rw [he]
    exact q1
  have key := iteratedDeriv_chain (fun m t => valR (A := ℂ) ((u.ex (t • Y0)).left ≫ ψ) U (F m)) (hO.preimage hc)
    (fun m t ht => by
      have hdf : DifferentiableAt ℂ (fun w => valR (A := ℂ) ((u.ex w).left ≫ ψ) U (F m)) (t • Y0) := by
        have := (hol_valR u (ψ ⁻¹ᵁ U) ((ψ.app U).hom (F m))).2.differentiableAt (hO.mem_nhds ht)
        simp only [← valR_comp] at this
        exact this
      have h2 : HasDerivAt (fun t : ℂ => t • Y0) Y0 t := by simpa using (hasDerivAt_id t).smul_const Y0
      have := hdf.hasFDerivAt.comp_hasDerivAt t h2
      rw [fderiv_eq u hψ hv hd (F m) (D (F m)) (hD (F m)) _ ht, ← hF] at this
      exact this) n 0 h0'
  rw [j3, j2, ← q2, ← he]
  refine key.symm.trans (EventuallyEq.iteratedDeriv_eq n ?_)
  filter_upwards [(hO.preimage hc).mem_nhds h0'] with t ht
  exact valR_res ((u.ex (t • Y0)).left ≫ ψ) hUV ht f

end Hol

section Main

open Topology Filter

private theorem valR_mul {R : Type} [CommRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a b : Γ(X, U)) : valR x U (a * b) = valR x U a * valR x U b := by
  rw [valR_eq x U h, valR_eq x U h, valR_eq x U h, map_mul]

private theorem valR_unit_ne {R : Type} [Field R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (a : Γ(X, U)ˣ) : valR x U a.val ≠ 0 := by
  rw [valR_eq x U h]
  exact (a.isUnit.map (valHom x U h)).ne_zero

private theorem exists_chart {R : Type} [Field R] {X : Scheme.{0}} (x : Sp R ⟶ X) {L : LB X} (hL : L.IsLB) :
    ∃ i, ⊤ ≤ x ⁻¹ᵁ L.U i := by
  have : x (default : Sp R) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  refine ⟨i, fun z _ => ?_⟩
  rw [Subsingleton.elim (α := Sp R) z default]
  exact hi

private theorem rigVal_spec {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA]
    [IsCommMonObj AA] {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {N : ℕ} {w : LB.Iso (MM.L.pull φ) (lbPow P.L N)}
    (hφ : IsGrpPullback P.A AA (spMap (algebraMap (𝓞 K) K)) φ) {i₀ : (lbPow P.L N).ι}
    (h0 : ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀) {σ : K →+* ℂ} {Q : Out.PolAV (Sp ℂ)} {ψ : Q.A.left ⟶ P.A.left}
    (hψ : IsGrpPullback Q.A P.A (spMap σ) ψ) {wσ : LB.Iso ((lbPow P.L N).pull ψ) (lbPow Q.L N)} {g : ℕ}
    {u : HolUnif Q.A Q.L g} {ρ : ℂ} (hρ : RigIs w σ wσ u ρ) (k : (lbPow Q.L N).ι)
    (hk : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ ((lbPow Q.L N).U k ⊓ ((lbPow P.L N).pull ψ).U (fun _ => i₀))) :
    rigVal w i₀ ≠ 0 ∧
      valR (A := ℂ) (u.ex 0).left ((lbPow Q.L N).U k ⊓ ((lbPow P.L N).pull ψ).U (fun _ => i₀))
        (wσ.s (k, fun _ => i₀)).val * σ (rigVal w i₀) = ρ * u.fr (k PUnit.unit) 0 ^ N := by
  have he : eSec P.A ≫ φ = spMap (algebraMap (𝓞 K) K) ≫ eSec AA := PolBaseChange.eSec_comm hφ
  have he' : (u.ex 0).left ≫ ψ = spMap σ ≫ eSec P.A := by
    rw [ex_zero_left]
    exact PolBaseChange.eSec_comm hψ
  have h : ∃ p : PUnit → MM.L.ι,
      ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) := by
    obtain ⟨p, hp⟩ := exists_chart (R := K) (spMap (algebraMap (𝓞 K) K) ≫ eSec AA) MM.isLB
    exact ⟨fun _ => p, fun z hz => Set.mem_iInter.2 fun _ => hp hz⟩
  have hp := h.choose_spec
  have h1 : ⊤ ≤ (eSec P.A) ⁻¹ᵁ ((lbPow P.L N).U i₀ ⊓ (MM.L.pull φ).U h.choose) := by
    intro z hz
    refine ⟨h0 hz, Set.mem_iInter.2 fun c => ?_⟩
    have : z ∈ (eSec P.A ≫ φ) ⁻¹ᵁ MM.L.U (h.choose c) := by
      rw [he]
      exact Set.mem_iInter.1 (hp hz) c
    exact this
  obtain ⟨a1, a2⟩ := valR_spMap σ (eSec P.A) _ h1
  obtain ⟨_, b2⟩ := valR_spMap σ (spMap (algebraMap (𝓞 K) K)) _ hp
  have hr := hρ k (fun _ => i₀) h.choose hk (by rw [he']; exact a1)
  rw [he', ← spMap_comp_spMap] at hr
  rw [rigVal, dif_pos h]
  refine ⟨mul_ne_zero (valR_unit_ne (R := K) _ _ h1 _) (valR_unit_ne (R := K) _ _ hp _), ?_⟩
  rw [map_mul, ← _root_.mul_assoc, ← hr]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (valAt'_eq _ _ _).symm ((valAt'_eq _ _ _).trans (a2 _)).symm)
    ((valAt'_eq _ _ _).trans (b2 _)).symm

private theorem jetFun_mul_eq_iteratedDeriv : ∀ (K'' : Type) [Field K''] [NumberField K''] (P : Out.PolAV (Sp K'')) (AA : Over (Sp (𝓞 K''))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (r : ℕ) (b : Fin r → (lbPow P.L N).Sec) (i₀ : (lbPow P.L N).ι) (y : epsR K'' ⟶ P.A) (σ : K'' →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ P.A.left) (wσ : LB.Iso ((lbPow P.L N).pull ψ) (lbPow Q.L N)) (s : Fin r → (lbPow Q.L N).Sec) (g : ℕ) (u : HolUnif Q.A Q.L g) (ρ : ℂ) (θ : Fin r → (Fin g → ℂ) → ℂ) (yq : epsR ℂ ⟶ Q.A) (Y0 : Fin g → ℂ) (c : Fin r → K'') (i : ℕ), IsModel w → ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀ → IsTangent y → GlobalTheory.IsPolFibre σ P Q ψ → wσ.IsGen → (∀ a, SecMaps wσ (secPull (b a) ψ) (s a)) → RigIs w σ wσ u ρ → (∀ a, u.IsFnPow N (s a) (θ a)) → GlobalTheory.IsVecOver σ ψ y yq → u.IsDiff Y0 yq → c ∈ filt (jetFun y i₀ (rigVal w i₀) b) i → σ (jetFun y i₀ (rigVal w i₀) b i c) * ρ = iteratedDeriv i (fun t : ℂ => ∑ a, σ (c a) * θ a (t • Y0)) 0 := by
  intro K _ _ P AA _ _ φ MM N w r b i₀ y σ Q ψ wσ s g u ρ θ yq Y0 c i hM h0 hy hψ _ hs hρ hθ hv hd hc
  have hψ' := hψ.2.1
  have he' : (u.ex 0).left ≫ ψ = spMap σ ≫ eSec P.A := by
    rw [ex_zero_left]
    exact PolBaseChange.eSec_comm hψ'
  obtain ⟨k₀, hk₀⟩ := exists_chart (R := ℂ) (u.ex 0).left Q.isLB
  let k : (lbPow Q.L N).ι := fun _ => k₀
  let j : ((lbPow P.L N).pull ψ).ι := fun _ => i₀
  let V : P.A.left.Opens := (lbPow P.L N).U i₀
  let W : Q.A.left.Opens := (lbPow Q.L N).U k ⊓ ((lbPow P.L N).pull ψ).U j
  have hW1 : W ≤ Q.L.U k₀ := inf_le_left.trans (lbPow_U Q.L N k).le
  have hW2 : W ≤ ψ ⁻¹ᵁ V := inf_le_right.trans (pull_U (lbPow P.L N) ψ j).le
  have hk : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W := by
    have h2 : ⊤ ≤ ((u.ex 0).left ≫ ψ) ⁻¹ᵁ V := by
      rw [he']
      exact (valR_spMap σ (eSec P.A) _ h0).1
    exact fun z hz => ⟨(lbPow_U Q.L N k).ge (hk₀ hz), (pull_U (lbPow P.L N) ψ j).ge (h2 hz)⟩
  obtain ⟨hne, hrig⟩ := rigVal_spec hM.2.2.2.1 h0 hψ' hρ k hk
  have hne' : σ (rigVal w i₀) ≠ 0 := (map_ne_zero σ).2 hne
  let wv : Γ(Q.A.left, W) := (wσ.s (k, j)).val
  have hO := (hol_valR u W wv).1
  have hc' : Differentiable ℂ fun t : ℂ => t • Y0 := by fun_prop
  have hO' := hO.preimage hc'.continuous
  have h0' : (0 : ℂ) ∈ (fun t : ℂ => t • Y0) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} := by
    change ⊤ ≤ (u.ex ((0 : ℂ) • Y0)).left ⁻¹ᵁ W
    rw [zero_smul]
    exact hk
  have han : ∀ F : (Fin g → ℂ) → ℂ, DifferentiableOn ℂ F {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} →
      AnalyticAt ℂ (fun t : ℂ => F (t • Y0)) 0 := fun F hF =>
    (hF.comp hc'.differentiableOn (fun _ h => h)).analyticAt (hO'.mem_nhds h0')
  have hsub : ∀ {W' : Q.A.left.Opens}, W ≤ W' →
      {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W} ⊆ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ W'} :=
    fun h z hz x hx => h (hz hx)
  let Bv : Fin r → ℂ → ℂ := fun a t => valR (A := ℂ) ((u.ex (t • Y0)).left ≫ ψ) V ((b a).f i₀)
  have hBv : ∀ a, AnalyticAt ℂ (Bv a) 0 := fun a => by
    have := han _ ((hol_valR u (ψ ⁻¹ᵁ V) ((ψ.app V).hom ((b a).f i₀))).2.mono (hsub hW2))
    simp only [← valR_comp] at this
    exact this
  let H : ℂ → ℂ := fun t => valR (A := ℂ) (u.ex (t • Y0)).left W wv / u.fr k₀ (t • Y0) ^ N
  have hH : AnalyticAt ℂ H 0 := by
    refine (han _ (hol_valR u W wv).2).div ((han _ ((u.fr_hol k₀).mono (hsub hW1))).pow N) (pow_ne_zero _ ?_)
    exact u.fr_ne k₀ _ (hsub hW1 h0')
  let B : ℂ → ℂ := fun t => ∑ a, σ (c a) * Bv a t
  have hB : AnalyticAt ℂ B 0 := Finset.analyticAt_fun_sum _ fun a _ => analyticAt_const.mul (hBv a)
  have hjet : ∀ m, iteratedDeriv m B 0 = σ (rigVal w i₀) * σ (jetFun y i₀ (rigVal w i₀) b m c) := fun m => by
    rw [show iteratedDeriv m B 0 = _ from iteratedDeriv_fun_sum (f := fun a t => σ (c a) * Bv a t)
      (fun a _ => (analyticAt_const.mul (hBv a)).contDiffAt), jetFun_apply, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [iteratedDeriv_const_mul_field, map_mul, map_mul, map_inv₀,
      jetVal_eq_iteratedDeriv u hψ' hy hv hd h0 ((b a).f i₀) m]
    field_simp
    rfl
  have hev : (fun t : ℂ => ∑ a, σ (c a) * θ a (t • Y0)) =ᶠ[𝓝 0] fun t => B t * H t := by
    filter_upwards [hO'.mem_nhds h0'] with t ht
    replace ht : ⊤ ≤ (u.ex (t • Y0)).left ⁻¹ᵁ W := ht
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e1 := hθ a k (t • Y0) (hsub inf_le_left ht)
    have e2 := congrArg (valR (A := ℂ) (u.ex (t • Y0)).left W) (hs a (k, j))
    rw [valR_res _ _ ht, valR_mul _ _ ht, valR_res _ _ ht, ← valAt'_eq, e1] at e2
    have e3 : valR (A := ℂ) (u.ex (t • Y0)).left (((lbPow P.L N).pull ψ).U j) ((secPull (b a) ψ).f j) = Bv a t :=
      (valR_res _ (pull_U (lbPow P.L N) ψ j).le (hsub inf_le_right ht) _).trans (valR_comp _ _ _ _).symm
    have e4 : θ a (t • Y0) * u.fr k₀ (t • Y0) ^ N = valR (A := ℂ) (u.ex (t • Y0)).left W wv * Bv a t :=
      e2.trans (congrArg _ e3)
    have hfr : u.fr k₀ (t • Y0) ^ N ≠ 0 := pow_ne_zero _ (u.fr_ne k₀ _ (hsub hW1 ht))
    rw [_root_.mul_assoc, ← mul_div_assoc, _root_.mul_comm (Bv a t), ← e4, mul_div_cancel_right₀ _ hfr]
  rw [hev.iteratedDeriv_eq, iteratedDeriv_mul_of_vanish hB hH i (fun m hm => by
    rw [hjet, filt_vanish _ c i hc m hm, map_zero, mul_zero]), hjet]
  have hfr : u.fr k₀ 0 ^ N ≠ 0 := pow_ne_zero _ (u.fr_ne k₀ _ hk₀)
  have e5 : valR (A := ℂ) (u.ex 0).left W wv * σ (rigVal w i₀) = ρ * u.fr k₀ 0 ^ N := hrig
  simp only [H, zero_smul]
  field_simp
  linear_combination (-σ (jetFun y i₀ (rigVal w i₀) b i c)) * e5

end Main

end GlobalTheory.SecJetCmp

theorem _root_.GlobalTheory.T.complex_embedding_section_pullback : ∀ (K'' : Type) [Field K''] [NumberField K''] (P : Out.PolAV (Sp K'')) (AA : Over (Sp (𝓞 K''))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (r : ℕ) (b : Fin r → (lbPow P.L N).Sec) (i₀ : (lbPow P.L N).ι) (y : epsR K'' ⟶ P.A) (σ : K'' →+* ℂ) (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ P.A.left) (wσ : LB.Iso ((lbPow P.L N).pull ψ) (lbPow Q.L N)) (s : Fin r → (lbPow Q.L N).Sec) (g : ℕ) (u : HolUnif Q.A Q.L g) (ρ : ℂ) (θ : Fin r → (Fin g → ℂ) → ℂ) (yq : epsR ℂ ⟶ Q.A) (Y0 : Fin g → ℂ) (c : Fin r → K'') (i : ℕ), IsModel w → ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀ → IsTangent y → GlobalTheory.IsPolFibre σ P Q ψ → wσ.IsGen → (∀ a, SecMaps wσ (secPull (b a) ψ) (s a)) → RigIs w σ wσ u ρ → (∀ a, u.IsFnPow N (s a) (θ a)) → GlobalTheory.IsVecOver σ ψ y yq → u.IsDiff Y0 yq → c ∈ filt (jetFun y i₀ (rigVal w i₀) b) i → σ (jetFun y i₀ (rigVal w i₀) b i c) * ρ = iteratedDeriv i (fun t : ℂ => ∑ a, σ (c a) * θ a (t • Y0)) 0 :=
  GlobalTheory.SecJetCmp.jetFun_mul_eq_iteratedDeriv
