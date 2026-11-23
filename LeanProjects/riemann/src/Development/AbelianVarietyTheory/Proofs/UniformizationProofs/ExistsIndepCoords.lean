import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombEqZeroIffExpansionCombEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxProductLinearIndependent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpansionSingleValued

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep

theorem exists_indep_coords (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] [Algebra R F] [IsScalarTower R (FractionRing R) F] {Λ : Type} [Fintype Λ] (c : Λ → F) :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → F) (a : Λ → κ → R), LinearIndependent R b ∧ ∀ i, c i = ∑ l, a i l • b l := by
  classical
  let B := Module.Basis.ofVectorSpace (FractionRing R) F
  let S := Finset.univ.biUnion fun i => (B.repr (c i)).support
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Λ × S => B.repr (c p.1) p.2)
  choose a ha using hd
  have hd0 : algebraMap R (FractionRing R) d ≠ 0 := (IsLocalization.map_units _ d).ne_zero
  refine ⟨S, inferInstance, fun l => (algebraMap R (FractionRing R) d)⁻¹ • B l, fun i l => a (i, l), ?_, fun i => ?_⟩
  · refine LinearIndependent.restrict_scalars' (K := FractionRing R) R ?_
    exact (B.linearIndependent.comp (fun l : S => l.1) Subtype.val_injective).units_smul
      (fun _ => (Units.mk0 _ hd0)⁻¹)
  · have h : ∀ l : S, a (i, l) • (algebraMap R (FractionRing R) d)⁻¹ • B l = B.repr (c i) l • B l := fun l => by
      rw [← algebraMap_smul (FractionRing R), ha, smul_smul, Algebra.smul_def (d : R), mul_right_comm,
        mul_inv_cancel₀ hd0, _root_.one_mul]
    simp only [h]
    rw [Finset.sum_coe_sort S (fun l => B.repr (c i) l • B l)]
    conv_lhs => rw [← B.linearCombination_repr (c i), Finsupp.linearCombination_apply]
    exact Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun i => (B.repr (c i)).support) (Finset.mem_univ i)) _
      (fun _ _ => zero_smul _ _)

theorem flat_germOf {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (x : X) :
    (germOf p x).Flat := by
  have e : germOf p x = (p.stalkMap x).hom.comp
      (((Sp R).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.ext fun c => by
      rw [germOf_apply, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  rw [e]
  refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)) ?_) (Flat.stalkMap p x)
  have hU := isAffineOpen_top (Sp R)
  let _ := (Sp R).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
  have := hU.isLocalization_stalk ⟨p x, trivial⟩
  exact IsLocalization.flat ((Sp R).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp R).Opens)) : Sp R))
    (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl

theorem split_relation {R F : Type} [CommRing R] [CommRing F] [Algebra R F] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] (x : X) {U : X.Opens} (hx : x ∈ U) {Λ κ : Type} [Fintype Λ] [Fintype κ]
    (b : κ → F) (hb : LinearIndependent R b) (a : Λ → κ → R) (s : Λ → Γ(X, U))
    (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of F)) (r : Z ⟶ X),
      r ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) → ∀ z, r z ∈ U →
        ∑ i, germOf q z (∑ l, a i l • b l) * gs r z U (s i) = 0) (l : κ) :
    ∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i) = 0 := by
  let O : Type := X.presheaf.stalk x
  let : Algebra R O := (germOf p x).toAlgebra
  have : Module.Flat R O := flat_germOf p x
  have hi : LinearIndependent O (fun l => (1 : O) ⊗ₜ[R] b l) := Module.Flat.linearIndependent_one_tmul hb
  refine Fintype.linearIndependent_iff.1 hi (fun l => ∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i)) ?_ l
  let eL : O →+* TensorProduct R O F := Algebra.TensorProduct.includeLeftRingHom
  let eR : F →+* TensorProduct R O F := (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := F)).toRingHom
  refine eq_zero_of_germOf (B := CommRingCat.of (TensorProduct R O F)) _ fun z => ?_
  have h := H (Spec (CommRingCat.of (TensorProduct R O F))) (Spec.map (CommRingCat.ofHom eR))
    ((Spec.map (CommRingCat.ofHom eL) : _ ⟶ Spec (X.presheaf.stalk x)) ≫ X.fromSpecStalk x) (by
      rw [Category.assoc, fromSpecStalk_comp]
      refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
      ext r
      exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R) (A := O) (B := F) r)) z (fromSpecStalk_mem x hx _)
  have e : ∑ l, (∑ i, germOf p x (a i l) * gs (𝟙 X) x U (s i)) • ((1 : O) ⊗ₜ[R] b l) =
      ∑ i, eR (∑ l, a i l • b l) * eL (gs (𝟙 X) x U (s i)) := by
    simp only [Finset.sum_smul, map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    show _ = ((1 : O) ⊗ₜ[R] (a i l • b l)) * ((gs (𝟙 X) x U (s i) : O) ⊗ₜ[R] (1 : F))
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rfl
  rw [e, ← h, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  congr 1
  · rw [← Category.id_comp (Spec.map _), germOf_map]; rfl
  · rw [gs_fromSpecStalk x hx]
    exact (germOf_map (B := X.presheaf.stalk x) (𝟙 _) (CommRingCat.ofHom eL) z _).symm

theorem gs_scal {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z)
    (a : R) : gs r z ⊤ (scal p a) = germOf (r ≫ p) z a :=
  (gs_pull r p z ⊤ trivial _).trans (germOf_apply _ _ _).symm

theorem gs_scal_comb {R : Type} [CommRing R] {X Z : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ X) (z : Z)
    {U : X.Opens} (hz : r z ∈ U) {Λ : Type} [Fintype Λ] (a : Λ → R) (s : Λ → Γ(X, U)) :
    gs r z U (∑ i, resTop U (scal p (a i)) * s i) = ∑ i, germOf (r ≫ p) z (a i) * gs r z U (s i) := by
  rw [gs_fsum r z U hz]
  exact Finset.sum_congr rfl fun i _ => by rw [gs_mul r z U hz, gs_res r z le_top hz, gs_scal]

theorem sum_append {F O T : Type} [CommRing F] [CommRing O] (g : F →+* O) {n n' : ℕ} (c : Fin n → F) (c' : Fin n' → F)
    (t : Fin n → T) (t' : Fin n' → T) (v : T → O) :
    ∑ i, g (Fin.append c (-c') i) * v (Fin.append t t' i) =
      ∑ i, g (c i) * v (t i) - ∑ i, g (c' i) * v (t' i) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.neg_apply, map_neg, neg_mul,
    Finset.sum_neg_distrib, sub_eq_add_neg]

end ExpansionSingleValued

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.BoxIndep ExpansionSingleValued in

theorem expandsG_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : U.SecGF F k) (s s₂ : Fam D.toPre F k), U.ExpandsG F k σ s → U.ExpandsG F k σ s₂ → s = s₂ := by
  intro R _ _ I hR D A G _ _ U k F _ _ σ s s₂ ⟨n, c, τ, f, hE, hG, hB⟩ ⟨n', c', τ', f', hE', hG', hB'⟩
  let : Algebra R F := ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))).toAlgebra
  have : IsScalarTower R (FractionRing R) F := IsScalarTower.of_algebraMap_eq' rfl
  have hj : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom (algebraMap R F)) :=
    (Spec.map_comp _ _).symm
  obtain ⟨κ, _, b, a, hb, ha⟩ := exists_indep_coords R F (Fin.append c (-c'))
  have := U.smooth
  have hz : ∀ l α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (a i l)) * (Fin.append f f' i α).f j = 0 := fun l => by
    refine (comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k _ (fun i => a i l) (Fin.append τ τ')
      (Fin.append f f') (fun i => ?_)).1 fun j => ?_
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hE i
      · simpa only [Fin.append_right] using hE' i
    refine fn_ext fun x hx => (gs_scal_comb G.hom (𝟙 _) x hx _ _).trans (Eq.trans ?_ (gs_zero _ _ _ hx).symm)
    rw [Category.id_comp]
    refine split_relation G.hom x hx b hb a (fun i => (Fin.append τ τ' i).f j) (fun Z q r hr z hz => ?_) l
    let ρ₀ : Z ⟶ pullback G.hom (jK R) := pullback.lift r (q ≫ jFK (R := R) F) (by rw [hr, Category.assoc, hj])
    let ρ : Z ⟶ (UnifPre.GF (G := G) F).left := pullback.lift q ρ₀ (pullback.lift_snd _ _ _).symm
    have e₁ : ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = q := pullback.lift_fst _ _ _
    have e₂ : ρ ≫ UnifPre.gFK (G := G) F = r :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G.hom (jK R)) (pullback.lift_snd _ _ _)).trans
        (pullback.lift_fst _ _ _))
    obtain ⟨J, hJ, eJ⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : Fin 1 => r ≫ 𝟙 _) j
      (fun u v _ => congrArg j (Subsingleton.elim u v)) (fun u => Set.mem_iInter.1 hz u)
    have h₁ := ExpGTrans.secLin_val hG ρ z hJ
    have h₂ := ExpGTrans.secLin_val hG' ρ z hJ
    simp only [gs_scal, e₂, sval_of _ r z J j eJ] at h₁ h₂
    simp only [← ha]
    refine (sum_append (germOf q z) c c' τ τ' (fun t => gs r z _ (t.f j))).trans (sub_eq_zero.2 ?_)
    rw [← e₁]
    exact h₁.symm.trans h₂
  refine fam_ext fun α => sec_ext_val D.toPre.P.isLB fun y J hJ => ?_
  rw [ExpGTrans.secLin_val (hB α) _ y hJ, ExpGTrans.secLin_val (hB' α) _ y hJ]
  simp only [gs_scal]
  set q := 𝟙 _ ≫ (fst (TF (R := R) F) D.toPre.P.A).left
  set r := 𝟙 _ ≫ (DegPre.prB D.toPre F).left
  have e : r ≫ D.toPre.P.A.hom = q ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [Category.assoc, Category.assoc, Over.w, ← hj]
    exact congrArg _ (Over.w (fst (TF (R := R) F) D.toPre.P.A)).symm
  refine sub_eq_zero.1 ((sum_append (germOf q y) c c' f f' (fun t => sval (t α) r y J)).symm.trans ?_)
  simp only [ha, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have hm := hJ.mem (D.toPre.famφB α) r
  have h := (gs_scal_comb D.toPre.P.A.hom r y hm _ _).symm.trans
    ((congrArg _ (hz l α _)).trans (gs_zero _ _ _ hm))
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((Finset.mul_sum _ _ (germOf q y (b l))).symm.trans
    ((congrArg _ h).trans (mul_zero _)))
  rw [Algebra.smul_def, map_mul, e, germOf_map, mul_comm (germOf q y _), _root_.mul_assoc]
  rfl

end GlobalTheory
