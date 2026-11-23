import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AutomorphicArithmetic.CommutativeAlgebra.BijectiveEtaleCohomologyLaurentPolynomialOfCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LaurentCharacterLambda
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

namespace UpperTheory.KG

variable {S : Type} [CommRing S]

private noncomputable def tU (S : Type) [CommRing S] : (LaurentPolynomial S)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by rw [← LaurentPolynomial.T_add]; simp,
    by rw [← LaurentPolynomial.T_add]; simp⟩

private theorem tU_zpow (n : ℤ) : (((tU S) ^ n : (LaurentPolynomial S)ˣ) : LaurentPolynomial S) = LaurentPolynomial.T n := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T 1 : LaurentPolynomial S) ^ k = _
    rw [LaurentPolynomial.T_pow]; simp
  · rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    change (LaurentPolynomial.T (-1) : LaurentPolynomial S) ^ k = _
    rw [LaurentPolynomial.T_pow]; simp

private theorem lp_hom_ext {R : Type} [CommRing R] {f g : LaurentPolynomial S →+* R}
    (h1 : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C)
    (h2 : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  have hu : Units.map f.toMonoidHom (tU S) = Units.map g.toMonoidHom (tU S) := Units.ext h2
  have hT : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    intro n
    rw [← tU_zpow n]
    have h : Units.map f.toMonoidHom (tU S ^ n) = Units.map g.toMonoidHom (tU S ^ n) := by
      rw [map_zpow, map_zpow, hu]
    exact congrArg (fun v : Rˣ => (v : R)) h
  refine RingHom.ext fun p => ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a => rw [map_mul, map_mul, hT n]; exact congrArg (· * _) (RingHom.congr_fun h1 a)

private noncomputable def lam (q : ℕ) (hq : IsUnit (q : S)) : Localization.Away (q : ℤ) →+* S :=
  IsLocalization.Away.lift (q : ℤ) (g := Int.castRingHom S) (by simpa using hq)

private noncomputable def iot (q : ℕ) (hq : IsUnit (q : S)) : LqR q →+* LaurentPolynomial S :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp (lam q hq)) (tU S)

private theorem inclusion_T (q : ℕ) (hq : IsUnit (q : S)) : iot q hq (LaurentPolynomial.T 1) = LaurentPolynomial.T 1 := by
  rw [iot, LaurentPolynomial.eval₂_T, tU_zpow]

private noncomputable def chi (q : ℕ) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R) : LaurentPolynomial S →+* R :=
  LaurentPolynomial.eval₂ ψ (Units.map φ.toMonoidHom (tR q))

private theorem character_T (q : ℕ) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R) :
    chi q φ ψ (LaurentPolynomial.T 1) = φ (LaurentPolynomial.T 1) := by
  rw [chi, LaurentPolynomial.eval₂_T, zpow_one]; rfl

private theorem chi_C (q : ℕ) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R) :
    (chi q φ ψ).comp LaurentPolynomial.C = ψ :=
  RingHom.ext fun a => LaurentPolynomial.eval₂_C _ _ _

private theorem chi_iot (q : ℕ) (hq : IsUnit (q : S)) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R) :
    (chi q φ ψ).comp (iot q hq) = φ := by
  refine lp_hom_ext ?_ ?_
  · refine IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ)) (RingHom.ext_int _ _)
  · rw [RingHom.comp_apply, inclusion_T, character_T]

private theorem chi_uniq (q : ℕ) (hq : IsUnit (q : S)) {R : Type} [CommRing R] (φ : LqR q →+* R) (ψ : S →+* R)
    (χ : LaurentPolynomial S →+* R) (h1 : χ.comp (iot q hq) = φ) (h2 : χ.comp LaurentPolynomial.C = ψ) :
    χ = chi q φ ψ :=
  _root_.UpperTheory.Reformulated.B.LaurentCharacterLambda.chi_uniq q hq φ ψ χ h1 h2

private noncomputable def sec {X : Scheme.{0}} {R : CommRingCat.{0}} (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

private theorem sec_inj {X : Scheme.{0}} {R : CommRingCat.{0}} {f g : X ⟶ Spec R} (h : sec f = sec g) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso R).inv).1 h)

private theorem sec_comp {X : Scheme.{0}} {R R' : CommRingCat.{0}} (f : X ⟶ Spec R') (ψ : R ⟶ R') :
    sec (f ≫ Spec.map ψ) = ψ ≫ sec f := by
  simp only [sec, Scheme.Hom.comp_appTop]
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

private theorem sec_to {X : Scheme.{0}} {R : CommRingCat.{0}} (φ : R ⟶ Γ(X, ⊤)) : sec (X.toSpecΓ ≫ Spec.map φ) = φ := by
  rw [sec_comp, sec, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

private noncomputable def isProd (q : ℕ) (hq : IsUnit (q : S)) :
    IsLimit (BinaryFan.mk (Spec.map (CommRingCat.ofHom (iot q hq)) : Spec (CommRingCat.of (LaurentPolynomial S)) ⟶ Gq q)
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : S →+* LaurentPolynomial S)) :
        Spec (CommRingCat.of (LaurentPolynomial S)) ⟶ Spec (CommRingCat.of S))) :=
  BinaryFan.isLimitMk
    (fun s => s.pt.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chi q (sec s.fst).hom (sec s.snd).hom)))
    (fun s => sec_inj (by
      rw [sec_comp, sec_to, ← CommRingCat.ofHom_comp, chi_iot]; rfl))
    (fun s => sec_inj (by
      rw [sec_comp, sec_to, ← CommRingCat.ofHom_comp, chi_C]; rfl))
    (fun s m h1 h2 => sec_inj (by
      rw [sec_to]
      have e1 : (sec m).hom.comp (iot q hq) = (sec s.fst).hom := by
        rw [← h1, sec_comp]; rfl
      have e2 : (sec m).hom.comp LaurentPolynomial.C = (sec s.snd).hom := by
        rw [← h2, sec_comp]; rfl
      rw [← chi_uniq q hq _ _ _ e1 e2]; rfl))

private theorem isUnit_q (q : ℕ) : IsUnit ((q : ℕ) : Γ(Gq q, ⊤)) := by
  have h0 : IsUnit ((q : ℕ) : Localization.Away (q : ℤ)) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (q : ℤ)) (q : ℤ)
    simpa using this
  have h1 : IsUnit ((q : ℕ) : LqR q) := by
    simpa using h0.map (LaurentPolynomial.C : Localization.Away (q : ℤ) →+* LqR q)
  simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of (LqR q))).inv.hom

private theorem coord (q : ℕ) (hq : IsUnit (q : S)) :
    ((Units.map (Spec.map (CommRingCat.ofHom (iot q hq))).appTop.hom.toMonoidHom (tq q) :
        (Γ(Spec (CommRingCat.of (LaurentPolynomial S)), ⊤))ˣ) : Γ(Spec (CommRingCat.of (LaurentPolynomial S)), ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial S))).inv.hom (LaurentPolynomial.T 1) := by
  have n := congrArg (fun k => k.hom (LaurentPolynomial.T 1 : LqR q))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (iot q hq)))
  have n' : (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial S))).inv.hom (iot q hq (LaurentPolynomial.T 1)) =
      (Spec.map (CommRingCat.ofHom (iot q hq))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (LqR q))).inv.hom (LaurentPolynomial.T 1)) := n
  rw [inclusion_T] at n'
  exact n'.symm

private theorem pull_cup {q : ℕ} {E E' : Spc} (s : E ⟶ E') {n m i j : ℤ} (x : Ht q E' n i) (y : Ht q E' m j) :
    pull _ s _ _ (cup q x y) = cup q (pull _ s _ _ x) (pull _ s _ _ y) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) s rfl x y

end UpperTheory.KG

theorem UpperTheory.bijective_etaleCohomology_multiplicativeGroup_prod :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) → ∀ m j : ℤ,
        Function.Bijective fun p : Ht q (sp O) (m + 1) (j + 1) × Ht q (sp O) m j =>
          pull _ (sch.map (prod.snd : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of O))) _ _ p.1 +
            cup q (pull _ (sch.map (prod.snd : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of O))) _ _ p.2)
              (pull _ (sch.map (prod.fst : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Gq q)) _ _ (kappa q)) := by
  intro q _ O _ hO hq m j
  let i0 := IsLimit.conePointUniqueUpToIso (UpperTheory.KG.isProd q hq) (prodIsProd (Gq q) (Spec (CommRingCat.of O)))
  let i : Spec (CommRingCat.of (LaurentPolynomial O)) ≅ Gq q ⨯ Spec (CommRingCat.of O) := i0
  have h1 : i.hom ≫ (prod.fst : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Gq q) =
      Spec.map (CommRingCat.ofHom (UpperTheory.KG.iot q hq)) :=
    IsLimit.conePointUniqueUpToIso_hom_comp (UpperTheory.KG.isProd q hq) (prodIsProd _ _) ⟨WalkingPair.left⟩
  have h2 : i.hom ≫ (prod.snd : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of O)) =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : O →+* LaurentPolynomial O)) :=
    IsLimit.conePointUniqueUpToIso_hom_comp (UpperTheory.KG.isProd q hq) (prodIsProd _ _) ⟨WalkingPair.right⟩
  have hbij : Function.Bijective (pull _ (sch.map i.hom) (tw q (j + 1)) (m + 1)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨pull _ (sch.map i.inv) _ _, fun x => ?_, fun x => ?_⟩
    · rw [← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, i.inv_hom_id, CategoryTheory.Functor.map_id, GlobalTheory.EtC.pull_id]
    · rw [← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, i.hom_inv_id, CategoryTheory.Functor.map_id, GlobalTheory.EtC.pull_id]
  have hk := UpperTheory.bijective_etaleCohomology_laurentPolynomial_of_coordinate_unit q O hO hq _ (UpperTheory.KG.coord q hq) m j
  refine (Function.Bijective.of_comp_iff' hbij _).1 ?_
  refine (congrArg Function.Bijective (funext fun p => ?_)).mpr hk
  have hκ : pull _ (sch.map i.hom) _ _ (pull _ (sch.map (prod.fst : Gq q ⨯ Spec (CommRingCat.of O) ⟶ Gq q)) _ _ (kappa q)) =
      kum q (Units.map (Spec.map (CommRingCat.ofHom (UpperTheory.KG.iot q hq))).appTop.hom.toMonoidHom (tq q)) := by
    rw [← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, h1]
    exact (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 _ _ (UpperTheory.KG.isUnit_q q)
  simp only [Function.comp_apply, map_add, UpperTheory.KG.pull_cup, hκ]
  rw [← GlobalTheory.EtC.pull_comp, ← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, h2]
