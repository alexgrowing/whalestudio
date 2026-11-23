import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValRConstHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLinearCombinationIsTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.SecJet.Orders

section Alg
open MvPolynomial

variable {R : Type} [CommRing R]

private def lineMap {k : ℕ} (c : Fin k → R) : EpsAlg R k →ₐ[R] DualNumber R :=
  Ideal.Quotient.liftₐ (sqIdeal R k) (aeval fun b => (TrivSqZeroExt.inr (c b) : DualNumber R)) (by
    intro p hp
    have : sqIdeal R k ≤ RingHom.ker (aeval fun b => (TrivSqZeroExt.inr (c b) : DualNumber R) :
        MvPolynomial (Fin k) R →ₐ[R] DualNumber R) := by
      rw [sqIdeal, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      simp [RingHom.mem_ker, sq, TrivSqZeroExt.inr_mul_inr]
    exact this hp)

private theorem lineMap_mk {k : ℕ} (c : Fin k → R) (p : MvPolynomial (Fin k) R) :
    lineMap c (Ideal.Quotient.mk _ p) = aeval (fun b => (TrivSqZeroExt.inr (c b) : DualNumber R)) p := rfl

private theorem topCoeff_mk {k : ℕ} (p : MvPolynomial (Fin k) R) :
    topCoeff R k (Ideal.Quotient.mk _ p) = coeff (topMon k) p := rfl

private theorem fst_aeval {k : ℕ} (c : Fin k → R) (p : MvPolynomial (Fin k) R) :
    (aeval (fun b => (TrivSqZeroExt.inr (c b) : DualNumber R)) p).fst = coeff 0 p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq => rw [map_add, TrivSqZeroExt.fst_add, hp, hq, coeff_add]
  | mul_X p n hp => simp [← constantCoeff_eq]

private theorem snd_aeval {k : ℕ} (a : Fin k) (p : MvPolynomial (Fin k) R) :
    (aeval (fun b => (TrivSqZeroExt.inr ((Pi.single a 1 : Fin k → R) b) : DualNumber R)) p).snd
      = coeff (Finsupp.single a 1) p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    have : (0 : Fin k →₀ ℕ) ≠ Finsupp.single a 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
    simp [TrivSqZeroExt.algebraMap_eq_inl, coeff_C, this]
  | add p q hp hq => rw [map_add, TrivSqZeroExt.snd_add, hp, hq, coeff_add]
  | mul_X p n hp =>
    rw [map_mul, TrivSqZeroExt.snd_mul, fst_aeval, aeval_X, coeff_mul_X']
    by_cases h : n = a
    · subst h; simp
    · have : n ∉ (Finsupp.single a 1).support := by simp [h]
      simp [this, h]

private theorem degree_topMon (k : ℕ) : Finsupp.degree (topMon k) = k := by
  simp [topMon, map_sum]

private theorem coeff_top_of_mem {k n : ℕ} (h : k < n) {p : MvPolynomial (Fin k) R} (hp : p ∈ idealOfVars (Fin k) R ^ n) :
    coeff (topMon k) p = 0 := by
  by_contra h0
  have := (mem_pow_idealOfVars_iff n p).1 hp _ (mem_support_iff.2 h0)
  rw [degree_topMon] at this
  omega

private theorem mem_idealOfVars {k : ℕ} {p : MvPolynomial (Fin k) R} (hp : coeff 0 p = 0) : p ∈ idealOfVars (Fin k) R := by
  rw [← pow_one (idealOfVars (Fin k) R), mem_pow_idealOfVars_iff]
  intro x hx
  by_contra h
  have : x = 0 := (Finsupp.degree_eq_zero_iff x).1 (by omega)
  subst this
  exact mem_support_iff.1 hx hp

private theorem mem_idealOfVars_sq {k : ℕ} {p : MvPolynomial (Fin k) R} (hp : coeff 0 p = 0)
    (h1 : ∀ a, coeff (Finsupp.single a 1) p = 0) : p ∈ idealOfVars (Fin k) R ^ 2 := by
  rw [mem_pow_idealOfVars_iff]
  intro x hx
  by_contra h
  rcases Nat.lt_or_ge (Finsupp.degree x) 1 with h2 | h2
  · have : x = 0 := (Finsupp.degree_eq_zero_iff x).1 (by omega)
    subst this
    exact mem_support_iff.1 hx hp
  · have h3 : Finsupp.degree x = 1 := by omega
    have : ∃ a, x = Finsupp.single a 1 := by
      have := (Finsupp.sum_eq_one_iff x).1 (by simpa [Finsupp.degree_apply, Finsupp.sum] using h3)
      exact this
    obtain ⟨a, rfl⟩ := this
    exact mem_support_iff.1 hx (h1 a)

private theorem topCoeff_eq_zero {k i : ℕ} (h : k < i) (u z : EpsAlg R k) (hz : (lineMap 0 z).fst = 0) :
    topCoeff R k (u * z ^ i) = 0 := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [lineMap_mk, fst_aeval] at hz
  rw [← map_pow, ← map_mul, topCoeff_mk]
  exact coeff_top_of_mem h (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (mem_idealOfVars hz) i))

private theorem multinomial_topMon (k : ℕ) : (topMon k).multinomial = k.factorial := by
  have h : ∀ a, topMon k a = 1 := fun a => by simp [topMon, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hs : (topMon k).support = Finset.univ := by ext a; simp [h]
  rw [Finsupp.multinomial_eq, hs, Nat.multinomial]
  simp [h]

private theorem topCoeff_eq {k : ℕ} (u z : EpsAlg R k) (d : R) (hz : (lineMap 0 z).fst = 0)
    (hd : ∀ a, (lineMap (Pi.single a 1) z).snd = d) :
    topCoeff R k (u * z ^ k) = (lineMap 0 u).fst * d ^ k * k.factorial := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [lineMap_mk, fst_aeval, snd_aeval] at hz hd ⊢
  rw [← map_pow, ← map_mul, topCoeff_mk]
  set J := idealOfVars (Fin k) R
  set l : MvPolynomial (Fin k) R := C d * ∑ a, X a with hl
  have hl0 : coeff 0 l = 0 := by simp [hl, coeff_sum]
  have hl1 : ∀ a, coeff (Finsupp.single a 1) l = d := fun a => by
    simp [hl, coeff_sum, coeff_X', Finsupp.single_left_inj]
  have hp : p ∈ J := mem_idealOfVars hz
  have hlJ : l ∈ J := mem_idealOfVars hl0
  have h2 : p - l ∈ J ^ 2 := mem_idealOfVars_sq (by simp [hz, hl0]) (fun a => by simp [hd, hl1])
  have h3 : ∀ n : ℕ, p ^ n - l ^ n ∈ J ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : p ^ (n + 1) - l ^ (n + 1) = (p ^ n - l ^ n) * p + l ^ n * (p - l) := by ring
      rw [this]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ J (n + 1)]; exact Ideal.mul_mem_mul ih hp
      · rw [show n + 1 + 1 = n + 2 from rfl, pow_add J n 2]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hlJ n) h2
  have hq : q - C (coeff 0 q) ∈ J := mem_idealOfVars (by simp)
  have h4 : q * p ^ k = C (coeff 0 q) * l ^ k + (q * (p ^ k - l ^ k) + l ^ k * (q - C (coeff 0 q))) := by ring
  have h5 : q * (p ^ k - l ^ k) + l ^ k * (q - C (coeff 0 q)) ∈ J ^ (k + 1) :=
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ (h3 k))
      (by rw [pow_succ J k]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hlJ k) hq)
  rw [h4, coeff_add, coeff_top_of_mem (Nat.lt_succ_self k) h5, add_zero, hl, mul_pow, ← map_pow, coeff_C_mul,
    coeff_C_mul, coeff_sum_X_pow_of_fintype, if_pos, multinomial_topMon, _root_.mul_assoc]
  simpa [Finsupp.degree_apply, Finsupp.sum] using degree_topMon k

private theorem isNilpotent_of_fst {k : ℕ} (z : EpsAlg R k) (hz : (lineMap 0 z).fst = 0) : IsNilpotent z := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [lineMap_mk, fst_aeval] at hz
  have : idealOfVars (Fin k) R ≤ (nilradical (EpsAlg R k)).comap (Ideal.Quotient.mk _) := by
    rw [idealOfVars, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨2, by rw [sq]; exact eps_mul_self R a⟩
  exact this (mem_idealOfVars hz)

private theorem lineMap_epsIncl {k : ℕ} (c : Fin k → R) (a : Fin k) :
    ((lineMap c : EpsAlg R k →ₐ[R] DualNumber R) : EpsAlg R k →+* DualNumber R).comp
      ((epsIncl R a : DualNumber R →ₐ[R] EpsAlg R k) : DualNumber R →+* EpsAlg R k) = epsScaleR (c a) := by
  have : (lineMap c).comp (epsIncl R a) = epsScaleA R (c a) := by
    apply DualNumber.algHom_ext
    have : epsIncl R a DualNumber.eps = eps R a := by simp [epsIncl]
    rw [AlgHom.comp_apply, this, eps, lineMap_mk, aeval_X]
    ext <;> simp [epsScaleA, epsScaleR]
  exact congrArg (fun f : DualNumber R →ₐ[R] DualNumber R => (f : DualNumber R →+* DualNumber R)) this

end Alg

section Val

variable {A : Type} [CommRing A] {X : Scheme.{0}}

private def vh (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom

private theorem valR_eq (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR x U f = vh x U h f := by
  rw [valR, dif_pos h]; rfl

private theorem vh_congr {x y : Sp A ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) :
    vh x U h = vh y U h' := by subst e; rfl

private theorem vh_spMap {B : Type} [CommRing B] (ψ : A →+* B) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) (f : Γ(X, U)) : vh (spMap ψ ≫ x) U h' f = ψ (vh x U h f) := by
  have h1 : (spMap ψ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap ψ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have h3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom f)) h2
  simp only [vh, h1, RingHom.comp_apply, CommRingCat.hom_comp]
  exact h3

private theorem vh_res (x : Sp A ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    vh x V h' (resG X hVU f) = vh x U h f := by
  have h1 : X.presheaf.map (homOfLE hVU).op ≫ x.appLE V ⊤ h' = x.appLE U ⊤ h := Scheme.Hom.map_appLE _ _ _
  simp only [vh, ← h1, RingHom.comp_apply, CommRingCat.hom_comp]

private theorem vh_const {R : Type} [CommRing R] (ψ : R →+* A) (p : X ⟶ Sp R) (x : Sp A ⟶ X) (hx : x ≫ p = spMap ψ)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : R) : vh x U h (Geo.Tor.constFn p U a) = ψ a := by
  have h1 : p.appLE ⊤ U le_top ≫ x.appLE U ⊤ h = (spMap ψ).appTop := by
    refine (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ?_
    rw [← hx, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have h3 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h2
  have h4 := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) h1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3 h4
  simp only [vh, Geo.Tor.constFn, RingHom.comp_apply]
  erw [h4, h3]
  simp

private theorem eq_of_vh {x y : Sp A ⟶ X} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U)
    (e : vh x U h = vh y U h') : x = y := by
  have e' : x.appLE U ⊤ h = y.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of A)).hom]
    exact CommRingCat.hom_ext e
  have hT : IsAffineOpen (⊤ : (Sp A).Opens) := isAffineOpen_top _
  have a1 := IsAffineOpen.SpecMap_appLE_fromSpec x hU hT h
  have a2 := IsAffineOpen.SpecMap_appLE_fromSpec y hU hT h'
  rw [e', a2] at a1
  haveI : IsIso hT.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  exact ((cancel_epi _).1 a1).symm

private theorem vh_ne_zero [Nontrivial A] (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U))
    (hf : ⊤ ≤ x ⁻¹ᵁ X.basicOpen f) : vh x U h f ≠ 0 := by
  intro h0
  have h1 : (x.appLE U ⊤ h).hom f = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
    rw [map_zero]; exact h0
  have h2 := Scheme.basicOpen_appLE x ⊤ U h f
  erw [h1] at h2
  rw [Scheme.basicOpen_zero, top_inf_eq] at h2
  obtain ⟨p⟩ : Nonempty (Sp A) := inferInstanceAs (Nonempty (PrimeSpectrum A))
  have := hf (show p ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← h2] at this
  exact this

private theorem top_le_of_nil {B : Type} [CommRing B] (ψ : A →+* B) (hs : Function.Surjective ψ)
    (hn : ∀ z, ψ z = 0 → IsNilpotent z) (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ U) :
    ⊤ ≤ x ⁻¹ᵁ U := by
  intro p _
  have : p ∈ Set.range (PrimeSpectrum.comap ψ) := by
    rw [range_comap_of_surjective _ ψ hs]
    refine (PrimeSpectrum.mem_zeroLocus _ _).2 ?_
    intro z hz
    obtain ⟨n, hn⟩ := hn z hz
    exact (show PrimeSpectrum A from p).isPrime.mem_of_pow_mem n (by rw [hn]; exact Ideal.zero_mem _)
  obtain ⟨q, rfl⟩ := this
  exact h (show (show Sp B from q) ∈ (⊤ : (Sp B).Opens) from trivial)

end Val

section Grp

variable {R : Type} [CommRing R]

private def linePt {k : ℕ} (c : Fin k → R) : epsR R ⟶ epsT R k :=
  Over.homMk (spMap ((lineMap c : EpsAlg R k →ₐ[R] DualNumber R) : EpsAlg R k →+* DualNumber R))
    (spMap_comp_eq R (lineMap c))

private theorem linePt_epsIn {k : ℕ} (c : Fin k → R) (a : Fin k) : linePt c ≫ epsIn R a = epsScale R (c a) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap (epsScaleR (c a))
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, lineMap_epsIncl]

private theorem epsScale_one : epsScale R 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap (epsScaleR (1 : R)) = 𝟙 _
  have : epsScaleR (1 : R) = RingHom.id _ := by
    ext x <;> simp [epsScaleR]
  rw [this]
  exact Spec.map_id _

private theorem epsScale_zero : epsScale R 0 = toUnit _ ≫ TanComb.zeroPt := by
  apply Over.OverMorphism.ext
  show spMap (epsScaleR (0 : R)) = spMap (algebraMap R (DualNumber R)) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

variable {G : Over (Sp R)} [GrpObj G]

private theorem epsScale_zero_comp {y : epsR R ⟶ G} (hy : IsTangent y) : epsScale R 0 ≫ y = 1 := by
  rw [epsScale_zero, Category.assoc, (TanComb.isTangent_iff y).1 hy, MonObj.comp_one]

private theorem comp_prod {S T : Over (Sp R)} (f : S ⟶ T) (l : List (T ⟶ G)) : f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons a l ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

private theorem linePt_epsPt {k : ℕ} (c : Fin k → R) (y : epsR R ⟶ G) :
    linePt c ≫ epsPt y k = (List.ofFn fun a => epsScale R (c a) ≫ y).prod := by
  rw [GlobalTheory.SecJet.epsPt, comp_prod, List.map_ofFn]
  congr 2
  funext a
  simp only [Function.comp_apply]
  rw [← Category.assoc, linePt_epsIn]

private theorem linePt_zero {k : ℕ} {y : epsR R ⟶ G} (hy : IsTangent y) : linePt 0 ≫ epsPt y k = 1 := by
  rw [linePt_epsPt]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
  exact epsScale_zero_comp hy

private theorem linePt_single {k : ℕ} {y : epsR R ⟶ G} (hy : IsTangent y) (a : Fin k) :
    linePt (Pi.single a 1) ≫ epsPt y k = y := by
  rw [linePt_epsPt, List.ofFn_eq_map, List.prod_map_eq_pow_single a]
  · simp [epsScale_one]
  · intro b hb _
    rw [Pi.single_eq_of_ne hb]
    exact epsScale_zero_comp hy

private def orig (G : Over (Sp R)) [GrpObj G] : Sp R ⟶ G.left := eSec G

private theorem top_le_tangent {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U) :
    ⊤ ≤ (show Sp (DualNumber R) ⟶ G.left from y.left) ⁻¹ᵁ U := by
  refine top_le_of_nil (TrivSqZeroExt.fstHom R R R).toRingHom (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) ?_ _ U ?_
  · intro z hz
    have hz' : z.fst = 0 := hz
    refine ⟨2, ?_⟩
    ext <;> simp [sq, hz']
  · have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (show Sp (DualNumber R) ⟶ G.left from y.left) = orig G := hy
    rw [this]; exact he

private theorem fst_vh_tangent {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U)
    (f : Γ(G.left, U)) : (vh (A := DualNumber R) y.left U (top_le_tangent hy he) f).fst = vh (orig G) U he f := by
  have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (show Sp (DualNumber R) ⟶ G.left from y.left) = orig G := hy
  rw [← vh_congr this U (by rw [this]; exact he) he, vh_spMap _ _ _ (top_le_tangent hy he)]
  rfl

private theorem isTangent_one : IsTangent (1 : epsR R ⟶ G) := by
  rw [TanComb.isTangent_iff, MonObj.comp_one]

private theorem top_le_epsPt {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U) (k : ℕ) :
    ⊤ ≤ (show Sp (EpsAlg R k) ⟶ G.left from (epsPt y k).left) ⁻¹ᵁ U := by
  refine top_le_of_nil ((TrivSqZeroExt.fstHom R R R).toRingHom.comp
    ((lineMap 0 : EpsAlg R k →ₐ[R] DualNumber R) : EpsAlg R k →+* DualNumber R))
    (fun r => ⟨algebraMap R _ r, by simp [TrivSqZeroExt.algebraMap_eq_inl]⟩) isNilpotent_of_fst _ U ?_
  have h1 : spMap ((TrivSqZeroExt.fstHom R R R).toRingHom.comp
    ((lineMap 0 : EpsAlg R k →ₐ[R] DualNumber R) : EpsAlg R k →+* DualNumber R)) ≫
      (show Sp (EpsAlg R k) ⟶ G.left from (epsPt y k).left) = orig G := by
    have h2 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (linePt 0 ≫ epsPt y k).left = orig G := by
      rw [linePt_zero hy]; exact isTangent_one
    rw [← h2]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rfl
  rw [h1]; exact he

private theorem lineMap_vh {y w : epsR R ⟶ G} (hy : IsTangent y) (hw : IsTangent w) {U : G.left.Opens}
    (he : ⊤ ≤ orig G ⁻¹ᵁ U) {k : ℕ} (c : Fin k → R) (hc : linePt c ≫ epsPt y k = w) (f : Γ(G.left, U)) :
    lineMap c (vh (A := EpsAlg R k) (epsPt y k).left U (top_le_epsPt hy he k) f) =
      vh (A := DualNumber R) w.left U (top_le_tangent hw he) f := by
  subst hc
  exact (vh_spMap ((lineMap c : EpsAlg R k →ₐ[R] DualNumber R) : EpsAlg R k →+* DualNumber R) _ U
    (top_le_epsPt hy he k) (top_le_tangent hw he) f).symm

private theorem jetVal_eq_zero {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U) {k i : ℕ}
    (h : k < i) (u z : Γ(G.left, U)) (hz : vh (orig G) U he z = 0) : jetVal y k U (u * z ^ i) = 0 := by
  rw [jetVal]
  erw [valR_eq _ _ (top_le_epsPt hy he k)]
  rw [map_mul, map_pow]
  refine topCoeff_eq_zero h _ _ ?_
  erw [lineMap_vh hy isTangent_one he 0 (linePt_zero hy), fst_vh_tangent isTangent_one he, hz]

private theorem jetVal_eq {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U) (k : ℕ)
    (u z : Γ(G.left, U)) (hz : vh (orig G) U he z = 0) :
    jetVal y k U (u * z ^ k) = vh (orig G) U he u *
      (vh (A := DualNumber R) y.left U (top_le_tangent hy he) z).snd ^ k * k.factorial := by
  rw [jetVal]
  erw [valR_eq _ _ (top_le_epsPt hy he k)]
  rw [map_mul, map_pow]
  refine (topCoeff_eq _ _ (vh (A := DualNumber R) y.left U (top_le_tangent hy he) z).snd ?_ ?_).trans ?_
  · erw [lineMap_vh hy isTangent_one he 0 (linePt_zero hy), fst_vh_tangent isTangent_one he, hz]
  · intro a
    erw [lineMap_vh hy hy he _ (linePt_single hy a)]
  · erw [lineMap_vh hy isTangent_one he 0 (linePt_zero hy), fst_vh_tangent isTangent_one he]

private theorem jetVal_comb {y : epsR R ⟶ G} (hy : IsTangent y) {U : G.left.Opens} (he : ⊤ ≤ orig G ⁻¹ᵁ U) (k : ℕ)
    {r : ℕ} (c : Fin r → R) (f : Fin r → Γ(G.left, U)) :
    jetVal y k U (∑ a, Geo.Tor.constFn G.hom U (c a) * f a) = ∑ a, jetVal y k U (f a) * c a := by
  simp only [jetVal]
  have h : ∀ g, valR (A := EpsAlg R k) (epsPt y k).left U g = vh (A := EpsAlg R k) (epsPt y k).left U
    (top_le_epsPt hy he k) g := fun g => valR_eq _ _ _ g
  erw [h]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  erw [h]
  rw [map_mul, vh_const (algebraMap R (EpsAlg R k)) G.hom _ (Over.w (epsPt y k)), ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]

end Grp

section Sec

private def monoSec {X : Scheme.{0}} {L : LB X} {a : ℕ} (s t : (lbPow L a).Sec) {n i : ℕ} (h : i ≤ n) :
    (lbPow L (a * n)).Sec where
  f j := (show Γ(X, (lbPow L a).U j) from s.f j ^ (n - i) * t.f j ^ i)
  compat j j' := by
    have hs := s.compat j j'
    have ht := t.compat j j'
    have hg : ((lbPow L (a * n)).g j j').val = (((lbPow L a).g j j') ^ n).val := by
      refine congrArg Units.val ((lbPow_g L (a * n) j j').trans ?_)
      exact (pow_mul _ a n).trans (congrArg (· ^ n) (lbPow_g L a j j').symm)
    replace hg := hg.trans (Units.val_pow_eq_pow_val _ n)
    show resG X (inf_le_left : (lbPow L a).U j ⊓ (lbPow L a).U j' ≤ _) (s.f j ^ (n - i) * t.f j ^ i) =
      _ * resG X (inf_le_right : (lbPow L a).U j ⊓ (lbPow L a).U j' ≤ _) (s.f j' ^ (n - i) * t.f j' ^ i)
    erw [hg]
    simp only [map_mul, map_pow]
    erw [hs, ht]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left]
    have key : ∀ {A : Type} [CommRing A] (g a b : A), (g * a) ^ m * (g * b) ^ i = g ^ (i + m) * (a ^ m * b ^ i) := by
      intros; ring
    exact key _ _ _

private theorem vh_sec_ne_zero {K : Type} [Field K] {X : Scheme.{0}} {H : LB X} (s : H.Sec) (x : Sp K ⟶ X) (l : H.ι)
    (hl : ⊤ ≤ x ⁻¹ᵁ H.U l) (hs : ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s) : vh x (H.U l) hl (s.f l) ≠ 0 := by
  haveI : Unique (Sp K) := inferInstanceAs (Unique (PrimeSpectrum K))
  have h1 : x default ∈ Out.nonzeroLocus s := hs (show (default : Sp K) ∈ (⊤ : (Sp K).Opens) from trivial)
  rw [Out.nonzeroLocus, TopologicalSpace.Opens.mem_iSup] at h1
  obtain ⟨k, hk⟩ := h1
  have hk' : ⊤ ≤ x ⁻¹ᵁ X.basicOpen (s.f k) := by
    intro p _
    rw [Subsingleton.elim p default]; exact hk
  have hkU : ⊤ ≤ x ⁻¹ᵁ H.U k := hk'.trans (x.preimage_mono (X.basicOpen_le _))
  have hkl : ⊤ ≤ x ⁻¹ᵁ (H.U k ⊓ H.U l) := fun p hp => ⟨hkU hp, hl hp⟩
  have h2 := vh_ne_zero x _ hkU _ hk'
  have h3 := congrArg (vh x _ hkl) (s.compat k l)
  rw [map_mul] at h3
  erw [vh_res x _ hkU hkl, vh_res x _ hl hkl] at h3
  intro h0
  rw [h0, mul_zero] at h3
  exact h2 h3

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G]

private theorem exists_sep {H : LB G.left} {J : Type} (s : J → H.Sec) (hs : GlobalTheory.ZH.ImmBy G.hom H s Set.univ)
    {y : epsR K ⟶ G} (hy : IsTangent y) (hy1 : y ≠ 1) (l : H.ι) (hl : ⊤ ≤ orig G ⁻¹ᵁ H.U l) :
    ∃ s₀ s₁ : H.Sec, vh (orig G) _ hl (s₀.f l) ≠ 0 ∧ vh (orig G) _ hl (s₁.f l) = 0 ∧
      (vh (A := DualNumber K) y.left _ (top_le_tangent hy hl) (s₁.f l)).snd ≠ 0 := by
  haveI : Unique (Sp K) := inferInstanceAs (Unique (PrimeSpectrum K))
  obtain ⟨hc, hs⟩ := hs
  have h1 : orig G default ∈ ⨆ i ∈ (Set.univ : Set J), Out.nonzeroLocus (s i) := by rw [hc]; trivial
  simp only [TopologicalSpace.Opens.mem_iSup] at h1
  obtain ⟨i, -, hi⟩ := h1
  obtain ⟨haff, r, hr, hgen⟩ := hs i trivial
  have hV : ⊤ ≤ orig G ⁻¹ᵁ Out.nonzeroLocus (s i) := by
    intro p _
    rw [Subsingleton.elim p default]; exact hi
  have h0 := vh_sec_ne_zero (s i) (orig G) l hl hV
  have hj : ∃ j, (vh (A := DualNumber K) y.left _ (top_le_tangent hy hV) (r j)).snd ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hy1
    apply Over.OverMorphism.ext
    refine eq_of_vh (A := DualNumber K) haff (top_le_tangent hy hV) (top_le_tangent isTangent_one hV) ?_
    refine RingHom.eq_of_eqOn_set_dense hgen ?_
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact (vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w y) _ _ a).trans
        (vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w (1 : epsR K ⟶ G)) _ _ a).symm
    · apply TrivSqZeroExt.ext
      · exact (fst_vh_tangent hy hV _).trans (fst_vh_tangent isTangent_one hV _).symm
      · refine (hn j).trans ?_
        have := vh_spMap (algebraMap K (DualNumber K)) (orig G) _ hV (top_le_tangent isTangent_one hV) (r j)
        erw [this]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨j, hj⟩ := hj
  have key : vh (A := DualNumber K) y.left _ (top_le_tangent hy hl)
      ((secComb G.hom ![1, -vh (orig G) _ hV (r j)] ![s j, s i]).f l) =
      (vh (A := DualNumber K) y.left _ (top_le_tangent hy hV) (r j) - algebraMap K _ (vh (orig G) _ hV (r j))) *
        vh (A := DualNumber K) y.left _ (top_le_tangent hy hl) ((s i).f l) := by
    have hW : ⊤ ≤ (show Sp (DualNumber K) ⟶ G.left from y.left) ⁻¹ᵁ (Out.nonzeroLocus (s i) ⊓ H.U l) :=
      fun p hp => ⟨top_le_tangent hy hV hp, top_le_tangent hy hl hp⟩
    have h3 := congrArg (vh _ _ hW) (hr j l)
    rw [map_mul, vh_res _ _ (top_le_tangent hy hl) hW, vh_res _ _ (top_le_tangent hy hl) hW,
      vh_res _ _ (top_le_tangent hy hV) hW] at h3
    simp only [secComb, Fin.sum_univ_two, map_add, map_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w y),
      vh_const (algebraMap K (DualNumber K)) G.hom _ (Over.w y)]
    erw [h3]
    simp only [map_one, map_neg]
    ring
  have hf : (vh (A := DualNumber K) y.left _ (top_le_tangent hy hV) (r j) -
      algebraMap K _ (vh (orig G) _ hV (r j))).fst = 0 := by
    rw [TrivSqZeroExt.fst_sub, fst_vh_tangent hy hV]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨s i, secComb G.hom ![1, -vh (orig G) _ hV (r j)] ![s j, s i], h0, ?_, ?_⟩
  · rw [← fst_vh_tangent hy hl, key, TrivSqZeroExt.fst_mul, hf, zero_mul]
  · rw [key, TrivSqZeroExt.snd_mul, hf, fst_vh_tangent hy hl, zero_smul, zero_add, TrivSqZeroExt.snd_sub]
    simpa [TrivSqZeroExt.algebraMap_eq_inl, h0] using hj

private theorem tanComb_ne_one {m : ℕ} {v : Fin m → (epsR K ⟶ G)} (hv : IsLieBasis v) {x : Fin m → K} (hx : x ≠ 0) :
    tanComb x v ≠ 1 := by
  intro h
  have h0 : tanComb 0 v = 1 := by
    apply List.prod_eq_one
    intro w hw
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hw
    exact epsScale_zero_comp (hv.1 a)
  obtain ⟨c, -, hc⟩ := hv.2 1 isTangent_one
  exact hx ((hc x (h ▸ isLieComb_tanComb x v)).trans (hc 0 (h0 ▸ isLieComb_tanComb 0 v)).symm)

private theorem mem_filt {V : Type} [AddCommGroup V] [Module K V] (j : ℕ → V →ₗ[K] K) (c : V) (i : ℕ)
    (h : ∀ k < i, j k c = 0) : c ∈ filt j i := by
  induction i with
  | zero => trivial
  | succ i ih => exact ⟨ih fun k hk => h k (by omega), h i (by omega)⟩

end Sec

end GlobalTheory.SecJet.Orders

namespace GlobalTheory.SecJet

open Orders in

private theorem exists_mem_filt_jetFun_ne_zero :
    ∀ (K'' : Type) [Field K''] [NumberField K''] (P : Out.PolAV (Sp K'')) (m : ℕ) (v' : Fin m → (epsR K'' ⟶ P.A)) (x : Fin m → K'') (n r : ℕ) (b : Fin r → (lbPow P.L (4 * n)).Sec) (i₀ : (lbPow P.L (4 * n)).ι) (c₀ : K''), IsLieBasis v' → x ≠ 0 → 1 ≤ n → Function.Bijective (fun c : Fin r → K'' => secComb P.A.hom c b) → ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L (4 * n)).U i₀ → c₀ ≠ 0 → ∀ i ≤ n, ∃ c ∈ filt (jetFun (tanComb x v') i₀ c₀ b) i, jetFun (tanComb x v') i₀ c₀ b i c ≠ 0 := by
  intro K _ _ P m v x n r b i₀ c₀ hv hx _ hb hi₀ hc₀ i hi
  obtain ⟨M, s, hs⟩ := GlobalTheory.ZH.CrdMove.immBy_lbPow GlobalTheory.allSixLaws.1.ample K P 4 le_rfl
  have hy := isTangent_tanComb K P.A m v x hv.1
  have hl : ⊤ ≤ orig P.A ⁻¹ᵁ (lbPow P.L 4).U i₀ := hi₀
  obtain ⟨s₀, s₁, h0, h1, h2⟩ := exists_sep s hs hy (tanComb_ne_one hv hx) i₀ hl
  obtain ⟨c, hc⟩ := hb.2 (monoSec s₀ s₁ hi)
  have key : ∀ k, jetFun (tanComb x v) i₀ c₀ b k c =
      c₀⁻¹ * jetVal (tanComb x v) k ((lbPow P.L 4).U i₀) (s₀.f i₀ ^ (n - i) * s₁.f i₀ ^ i) := by
    intro k
    have h3 : (secComb P.A.hom c b).f i₀ = (monoSec s₀ s₁ hi).f i₀ := congrArg (fun q => q.f i₀) hc
    have h4 := jetVal_comb hy (U := (lbPow P.L (4 * n)).U i₀) hi₀ k c (fun a => (b a).f i₀)
    rw [jetFun_apply]
    simp only [_root_.mul_assoc]
    rw [← Finset.mul_sum, ← h4]
    congr 1
    exact congrArg (jetVal (tanComb x v) k ((lbPow P.L (4 * n)).U i₀)) h3
  refine ⟨c, mem_filt _ _ _ fun k hk => ?_, ?_⟩
  · rw [key, jetVal_eq_zero hy hl hk _ _ h1, mul_zero]
  · rw [key, jetVal_eq hy hl i _ _ h1, map_pow]
    exact mul_ne_zero (inv_ne_zero hc₀) (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ h2))
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)))

end GlobalTheory.SecJet

end

theorem _root_.GlobalTheory.T.jet_filtration_section_combination : ∀ (K'' : Type) [Field K''] [NumberField K''] (P : Out.PolAV (Sp K'')) (m : ℕ) (v' : Fin m → (epsR K'' ⟶ P.A)) (x : Fin m → K'') (n r : ℕ) (b : Fin r → (lbPow P.L (4 * n)).Sec) (i₀ : (lbPow P.L (4 * n)).ι) (c₀ : K''), IsLieBasis v' → x ≠ 0 → 1 ≤ n → Function.Bijective (fun c : Fin r → K'' => secComb P.A.hom c b) → ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L (4 * n)).U i₀ → c₀ ≠ 0 → ∀ i ≤ n, ∃ c ∈ filt (jetFun (tanComb x v') i₀ c₀ b) i, jetFun (tanComb x v') i₀ c₀ b i c ≠ 0 :=
  GlobalTheory.SecJet.exists_mem_filt_jetFun_ne_zero
