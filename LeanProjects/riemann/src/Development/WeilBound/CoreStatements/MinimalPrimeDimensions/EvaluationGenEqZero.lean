import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier

namespace ChowFormHeightComparison₂.CF.C

variable {R : Type} [CommRing R] {m : ℕ}

private theorem finsupp_prod_mul_pow {A : Type} [CommRing A] (b : Fin m → A) (c : A) (d : Fin m →₀ ℕ) :
    (d.prod fun j e => (b j * c) ^ e) = c ^ (d.sum fun _ e => e) * d.prod fun j e => b j ^ e := by
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem exists_homogenise (k : Fin m) (r : MvPolynomial (Fin m) R) : ∃ (N : ℕ) (r' : MvPolynomial (Fin m) R),
    ∀ (A : Type) [CommRing A] (f : R →+* A) (a b : Fin m → A), (∀ j, a j = b j * a k) →
      eval₂ f a r' = a k ^ N * eval₂ f b r := by
  refine ⟨r.totalDegree, ∑ d ∈ r.support, monomial d (r.coeff d) * X k ^ (r.totalDegree - d.sum fun _ e => e), ?_⟩
  intro A _ f a b hab
  conv_rhs => arg 2; rw [r.as_sum]
  rw [eval₂_sum, eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hle : (d.sum fun _ e => e) ≤ r.totalDegree := le_totalDegree hd
  have hp : (d.prod fun j e => a j ^ e) = d.prod fun j e => (b j * a k) ^ e :=
    Finsupp.prod_congr fun j _ => by rw [hab j]
  rw [eval₂_mul, eval₂_pow, eval₂_X, eval₂_monomial, eval₂_monomial, hp, finsupp_prod_mul_pow]
  conv_rhs => rw [← Nat.sub_add_cancel hle, pow_add]
  ring

theorem eval₂_mul_of_isHomogeneous {A : Type} [CommRing A] (f : R →+* A) (c : A) (a : Fin m → A) {n : ℕ}
    {q : MvPolynomial (Fin m) R} (hq : q.IsHomogeneous n) :
    eval₂ f (fun k => c * a k) q = c ^ n * eval₂ f a q := by
  conv_lhs => rw [q.as_sum]
  conv_rhs => rw [q.as_sum]
  rw [eval₂_sum, eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hq (mem_support_iff.mp hd)
  have hs : (d.sum fun _ e => e) = n := by
    rw [← hdeg, Finsupp.weight_apply]
    simp
  simp only [eval₂_monomial]
  simp only [mul_comm c]
  rw [finsupp_prod_mul_pow, hs]
  ring

variable {Z : Scheme.{0}} {B : LB Z} {p : Z ⟶ Sp R} {s : Fin m → B.Sec} {σ : R →+* ℂ}

theorem resG_algX {U W : Z.Opens} (h : W ≤ U) (a : R) : resG Z h (algX p U a) = algX p W a := by
  simp only [resG, algX, RingHom.comp_apply, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map]

theorem evaluation_resG {U W : Z.Opens} (h : W ≤ U) {z : Z} (hz : z ∈ W) (a : Γ(Z, U)) :
    Z.evaluation W z hz (resG Z h a) = Z.evaluation U z (h hz) a := by
  simp only [resG, Scheme.evaluation, ← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.germ_res]

theorem ev_eval₂ {U : Z.Opens} {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) (t : Fin m → Γ(Z, U))
    (r : MvPolynomial (Fin m) R) :
    ev p σ U (eval₂ (algX p U) t r) y = eval₂ σ (fun l => ev p σ U (t l) y) r := by
  induction r using MvPolynomial.induction_on with
  | C a => simp [ev_algX hy]
  | add f g hf hg => simp [ev_add, hf, hg]
  | mul_X f l hf => simp [ev_mul, hf]

variable (p s σ) in

def loc (i : B.ι) (y : CxPts p σ) : Fin m → ℂ := fun k => ev p σ (B.U i) ((s k).f i) y

variable {y y' : CxPts p σ} {i j : B.ι}

theorem loc_eq_smul (hi : y ∈ ptsIn p σ (B.U i)) (hj : y ∈ ptsIn p σ (B.U j)) :
    ∃ c : ℂ, c ≠ 0 ∧ loc p s σ i y = c • loc p s σ j y := by
  have hij : y ∈ ptsIn p σ (B.U i ⊓ B.U j) := mem_ptsIn.2 ⟨mem_ptsIn.1 hi, mem_ptsIn.1 hj⟩
  refine ⟨ev p σ _ (↑(B.g i j)) y, ev_ne_zero hij (B.g i j).isUnit, ?_⟩
  funext k
  have h := congrArg (fun f => ev p σ _ f y) ((s k).compat i j)
  simp only [ev_mul] at h
  rw [ev_res _ hij, ev_res _ hij] at h
  simpa [loc] using h

theorem loc_ne_zero_iff (hi : y ∈ ptsIn p σ (B.U i)) (k : Fin m) :
    loc p s σ i y k ≠ 0 ↔ y ∈ ptsIn p σ (nonzeroLocus (s k)) := secVal_ne_zero_iff (s k) hi

theorem loc_ne_zero (hE : Emb p s) (hi : y ∈ ptsIn p σ (B.U i)) : loc p s σ i y ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_mem_ptsIn hE.cover y
  intro h
  exact (loc_ne_zero_iff hi k).2 hk (congrFun h k)

theorem loc_ratio {k : Fin m} {t : Fin m → Γ(Z, nonzeroLocus (s k))}
    (ht : ∀ j i, resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s j).f i) =
      resG Z (inf_le_left : nonzeroLocus (s k) ⊓ B.U i ≤ nonzeroLocus (s k)) (t j) *
        resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s k).f i))
    (hk : y ∈ ptsIn p σ (nonzeroLocus (s k))) (hi : y ∈ ptsIn p σ (B.U i)) (l : Fin m) :
    loc p s σ i y l = ev p σ _ (t l) y * loc p s σ i y k := by
  have hki : y ∈ ptsIn p σ (nonzeroLocus (s k) ⊓ B.U i) := mem_ptsIn.2 ⟨mem_ptsIn.1 hk, mem_ptsIn.1 hi⟩
  have h := congrArg (fun f => ev p σ _ f y) (ht l i)
  simp only [ev_mul] at h
  rw [ev_res _ hki, ev_res _ hki, ev_res _ hki] at h
  simpa [loc] using h

theorem eq_of_loc (hE : Emb p s) (hi : y ∈ ptsIn p σ (B.U i)) (hj : y' ∈ ptsIn p σ (B.U j)) {c c' : ℂ}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (h : c • loc p s σ i y = c' • loc p s σ j y') : y = y' := by
  obtain ⟨k, hk⟩ := exists_mem_ptsIn hE.cover y
  obtain ⟨hA, t, hsurj, ht⟩ := hE.chart k
  have hyk : loc p s σ i y k ≠ 0 := (loc_ne_zero_iff hi k).2 hk
  have hl : ∀ l, c * loc p s σ i y l = c' * loc p s σ j y' l := fun l => by
    simpa using congrFun h l
  have hy'k : y' ∈ ptsIn p σ (nonzeroLocus (s k)) := by
    refine (loc_ne_zero_iff hj k).1 ?_
    intro h0
    have := hl k
    rw [h0, mul_zero] at this
    exact mul_ne_zero hc hyk this
  have rat : ∀ l, ev p σ _ (t l) y = ev p σ _ (t l) y' := by
    intro l
    have e1 := loc_ratio ht hk hi l
    have e2 := loc_ratio ht hy'k hj l
    have e3 := hl l
    have e4 := hl k
    rw [e1, e2] at e3
    have hne : c * loc p s σ i y k ≠ 0 := mul_ne_zero hc hyk
    apply mul_left_cancel₀ hne
    calc c * loc p s σ i y k * ev p σ _ (t l) y = c * (ev p σ _ (t l) y * loc p s σ i y k) := by ring
      _ = c' * (ev p σ _ (t l) y' * loc p s σ j y' k) := e3
      _ = (c' * loc p s σ j y' k) * ev p σ _ (t l) y' := by ring
      _ = c * loc p s σ i y k * ev p σ _ (t l) y' := by rw [e4]
  have hval : ∀ f, ev p σ (nonzeroLocus (s k)) f y = ev p σ _ f y' := by
    intro f
    obtain ⟨r, rfl⟩ := hsurj f
    rw [coe_eval₂Hom, ev_eval₂ hk, ev_eval₂ hy'k]
    simp only [rat]
  exact Subtype.ext (ext_of_valR hA hk hy'k hval)

variable [IsIntegral Z]

theorem evaluation_gen_eq_zero {U : Z.Opens} (h : genericPoint Z ∈ U) {a : Γ(Z, U)}
    (ha : Z.evaluation U _ h a = 0) : a = 0 := by
  have h1 : Function.Injective (Z.residue (genericPoint Z)).hom := by
    let K : Field (Z.presheaf.stalk (genericPoint Z)) := inferInstanceAs (Field Z.functionField)
    exact RingHom.injective _
  apply germ_injective_of_isIntegral Z _ h
  apply h1
  simpa [Scheme.evaluation] using ha

omit [IsIntegral Z] in
theorem coneHom_eq (z : Z) (h : z ∈ B.U i) (q : MvPolynomial (Fin m) R) :
    coneHom p s z i h q = Polynomial.map (Z.evaluation (B.U i) z h).hom
      (eval₂ (Polynomial.C.comp (algX p (B.U i))) (fun k => Polynomial.X * Polynomial.C ((s k).f i)) q) := by
  rw [← Polynomial.coe_mapRingHom, eval₂_comp_left]
  simp only [coneHom, coe_eval₂Hom]
  congr 1
  · ext a
    simp
  · ext k
    simp

theorem mem_ptIdeal_iff {z : Z} {q : MvPolynomial (Fin m) R} :
    q ∈ ptIdeal p s z ↔ ∀ i (h : z ∈ B.U i), coneHom p s z i h q = 0 := by
  simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem eval₂_loc_eq_zero (hi : y ∈ ptsIn p σ (B.U i)) {q : MvPolynomial (Fin m) R}
    (hq : q ∈ ptIdeal p s (genericPoint Z)) (c : ℂ) : eval₂ σ (c • loc p s σ i y) q = 0 := by
  have hi' : ⊤ ≤ (y : Sp ℂ ⟶ Z) ⁻¹ᵁ B.U i := hi
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(Z, B.U i) →+* ℂ, ∀ f, φ f = ev p σ (B.U i) f y :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (Scheme.Hom.appLE y.1 (B.U i) ⊤ hi').hom,
      fun f => by simp only [ev, valR, dif_pos hi']; rfl⟩
  have h0 : under y ∈ B.U i := hi (Set.mem_univ _)
  have hU : genericPoint Z ∈ B.U i :=
    (genericPoint_spec Z).mem_open_set_iff (B.U i).isOpen |>.mpr ⟨_, Set.mem_univ _, h0⟩
  have h1 := (mem_ptIdeal_iff.mp hq) i hU
  rw [coneHom_eq] at h1
  have hinj : Function.Injective (Z.evaluation (B.U i) (genericPoint Z) hU).hom := by
    intro a b hab
    exact sub_eq_zero.mp (evaluation_gen_eq_zero hU (by rw [map_sub, hab, sub_self]))
  have h2 : eval₂ (Polynomial.C.comp (algX p (B.U i)))
      (fun k => Polynomial.X * Polynomial.C ((s k).f i)) q = 0 := by
    apply Polynomial.map_injective _ hinj
    rw [h1, Polynomial.map_zero]
  have hσ : ∀ a : R, φ (algX p (B.U i) a) = σ a := by
    intro a
    have := ev_eval₂ hi (fun k => (s k).f i) (C a)
    simpa [hφ] using this
  have key : ∀ r : MvPolynomial (Fin m) R, Polynomial.eval₂ φ c (eval₂ (Polynomial.C.comp (algX p (B.U i)))
      (fun k => Polynomial.X * Polynomial.C ((s k).f i)) r) = eval₂ σ (c • loc p s σ i y) r := by
    intro r
    induction r using MvPolynomial.induction_on with
    | C a => simp [hσ]
    | add a b ha hb => rw [eval₂_add, Polynomial.eval₂_add, ha, hb, eval₂_add]
    | mul_X a k ha =>
      rw [eval₂_mul, eval₂_X, Polynomial.eval₂_mul, ha, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_C, hφ, eval₂_mul, eval₂_X]
      rfl
  rw [← key, h2, Polynomial.eval₂_zero]

theorem exists_loc (hE : Emb p s) {x : Fin m → ℂ} (hx : x ≠ 0)
    (h : ∀ q ∈ ptIdeal p s (genericPoint Z), eval₂ σ x q = 0) :
    ∃ (y : CxPts p σ) (c : ℂ), c ≠ 0 ∧ x = c • loc p s σ (pick hE.isLB y) y := by
  obtain ⟨k, hk⟩ : ∃ k, x k ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx (funext hne)
  obtain ⟨hU, t, hsurj, ht⟩ := hE.chart k
  have hgen : genericPoint Z ∈ nonzeroLocus (s k) := by
    by_contra hg
    apply hk
    have hmem : (X k : MvPolynomial (Fin m) R) ∈ ptIdeal p s (genericPoint Z) := by
      rw [mem_ptIdeal_iff]
      intro i hi
      have h0 : Z.evaluation (B.U i) (genericPoint Z) hi ((s k).f i) = 0 := by
        rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
        intro hb
        exact hg (TopologicalSpace.Opens.mem_iSup.2 ⟨i, hb⟩)
      simp [coneHom, h0]
    simpa using h _ hmem
  have hker : RingHom.ker (eval₂Hom (algX p (nonzeroLocus (s k))) t) ≤
      RingHom.ker (eval₂Hom σ (fun j => x j / x k)) := by
    intro r hr
    rw [RingHom.mem_ker] at hr ⊢
    obtain ⟨N, r', hr'⟩ := exists_homogenise k r
    have hmem : r' ∈ ptIdeal p s (genericPoint Z) := by
      rw [mem_ptIdeal_iff]
      intro i hi
      have hgi : genericPoint Z ∈ nonzeroLocus (s k) ⊓ B.U i := ⟨hgen, hi⟩
      have hrel : ∀ j, Z.evaluation (B.U i) _ hi ((s j).f i) =
          Z.evaluation (nonzeroLocus (s k)) _ hgen (t j) * Z.evaluation (B.U i) _ hi ((s k).f i) := by
        intro j
        have := congrArg (Z.evaluation _ _ hgi) (ht j i)
        rw [map_mul, evaluation_resG, evaluation_resG, evaluation_resG] at this
        exact this
      have halg : ∀ a, Z.evaluation (B.U i) _ hi (algX p (B.U i) a) =
          Z.evaluation (nonzeroLocus (s k)) _ hgen (algX p _ a) := by
        intro a
        rw [← evaluation_resG inf_le_right hgi, ← evaluation_resG inf_le_left hgi, resG_algX, resG_algX]
      have key := hr' (Polynomial (Z.residueField (genericPoint Z)))
        (Polynomial.C.comp ((Z.evaluation (B.U i) _ hi).hom.comp (algX p (B.U i))))
        (fun j => Polynomial.X * Polynomial.C (Z.evaluation (B.U i) _ hi ((s j).f i)))
        (fun j => Polynomial.C (Z.evaluation (nonzeroLocus (s k)) _ hgen (t j)))
        (fun j => by rw [hrel j, map_mul]; ring)
      have hf : Polynomial.C.comp ((Z.evaluation (B.U i) _ hi).hom.comp (algX p (B.U i))) =
          (Polynomial.C.comp (Z.evaluation (nonzeroLocus (s k)) _ hgen).hom).comp (algX p _) := by
        ext a
        simp [halg]
      have hb : (fun j => Polynomial.C (Z.evaluation (nonzeroLocus (s k)) _ hgen (t j))) =
          (Polynomial.C.comp (Z.evaluation (nonzeroLocus (s k)) _ hgen).hom) ∘ t := rfl
      rw [hf, hb, ← MvPolynomial.eval₂_comp_left] at key
      simp only [coe_eval₂Hom] at hr
      rw [hr, map_zero, mul_zero] at key
      simp only [coneHom, coe_eval₂Hom]
      rw [hf]
      simpa using key
    have key := hr' ℂ σ x (fun j => x j / x k) (fun j => by field_simp)
    rw [h r' hmem] at key
    simp only [coe_eval₂Hom]
    exact (mul_eq_zero.1 key.symm).resolve_left (pow_ne_zero _ hk)
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(Z, nonzeroLocus (s k)) →+* ℂ,
      ∀ r, φ (eval₂Hom (algX p _) t r) = eval₂ σ (fun j => x j / x k) r :=
    ⟨_, fun r => RingHom.liftOfSurjective_comp_apply _ hsurj ⟨_, hker⟩ r⟩
  have hφa : ∀ a, φ (algX p _ a) = σ a := by
    intro a
    simpa using hφ (C a)
  obtain ⟨y, hy⟩ : ∃ y, y = ofHom hU φ hφa := ⟨_, rfl⟩
  have hyU : y ∈ ptsIn p σ (nonzeroLocus (s k)) := hy ▸ ofHom_mem hU φ hφa
  have hi := mem_pick hE.isLB y
  have hkne : loc p s σ (pick hE.isLB y) y k ≠ 0 := (loc_ne_zero_iff hi k).2 hyU
  have hev : ∀ l, ev p σ _ (t l) y = x l / x k := by
    intro l
    rw [hy, ev_ofHom]
    simpa using hφ (X l)
  refine ⟨y, x k / loc p s σ (pick hE.isLB y) y k, div_ne_zero hk hkne, ?_⟩
  funext l
  rw [Pi.smul_apply, smul_eq_mul, loc_ratio ht hyU hi l, hev l]
  field_simp

theorem eval₂_loc_ne_zero (hy : under y = genericPoint Z) (hj : y ∈ ptsIn p σ (B.U j)) {n : ℕ}
    {q : MvPolynomial (Fin m) R} (hn : q.IsHomogeneous n) (hq : q ∉ ptIdeal p s (genericPoint Z)) :
    eval₂ σ (loc p s σ j y) q ≠ 0 := by
  have hq' : ∃ i, ∃ hU : genericPoint Z ∈ B.U i, coneHom p s (genericPoint Z) i hU q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq (mem_ptIdeal_iff.mpr hc)
  obtain ⟨i, hU, hne⟩ := hq'
  have hyi : y ∈ ptsIn p σ (B.U i) := by
    intro x _
    have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hx
    show under y ∈ B.U i
    rw [hy]
    exact hU
  have hcone : coneHom p s (genericPoint Z) i hU q = Polynomial.X ^ n *
      Polynomial.C ((Z.evaluation (B.U i) (genericPoint Z) hU).hom
        (eval₂ (algX p (B.U i)) (fun k => (s k).f i) q)) := by
    rw [coneHom_eq, eval₂_mul_of_isHomogeneous (Polynomial.C.comp (algX p (B.U i))) Polynomial.X
      (fun k => Polynomial.C ((s k).f i)) hn,
      show eval₂ (Polynomial.C.comp (algX p (B.U i))) (fun k => Polynomial.C ((s k).f i)) q =
        Polynomial.C (eval₂ (algX p (B.U i)) (fun k => (s k).f i) q) from
        (MvPolynomial.eval₂_comp_left Polynomial.C _ _ _).symm]
    simp [Polynomial.map_mul, Polynomial.map_pow]
  have hF0 : (Z.evaluation (B.U i) (genericPoint Z) hU).hom
      (eval₂ (algX p (B.U i)) (fun k => (s k).f i) q) ≠ 0 := by
    intro h0
    apply hne
    rw [hcone, h0, map_zero, mul_zero]
  have hgen : genericPoint Z ∈ Z.basicOpen (eval₂ (algX p (B.U i)) (fun k => (s k).f i) q) := by
    by_contra h
    exact hF0 ((Z.evaluation_eq_zero_iff_notMem_basicOpen _ hU _).mpr h)
  have hpt : Adelic.ptOf (y : Sp ℂ ⟶ Z) = genericPoint Z := hy
  have hval : ev p σ (B.U i) (eval₂ (algX p (B.U i)) (fun k => (s k).f i) q) y ≠ 0 := by
    show valR (y : Sp ℂ ⟶ Z) (B.U i) _ ≠ 0
    rw [Adelic.valR_ne_zero_iff _ (hpt ▸ hU), hpt]
    exact hgen
  rw [ev_eval₂ hyi] at hval
  change eval₂ σ (loc p s σ i y) q ≠ 0 at hval
  obtain ⟨c, _, hloc⟩ := loc_eq_smul hyi hj
  rw [hloc, show c • loc p s σ j y = fun k => c * loc p s σ j y k from rfl,
    eval₂_mul_of_isHomogeneous σ c _ hn] at hval
  exact right_ne_zero_of_mul hval

end ChowFormHeightComparison₂.CF.C
