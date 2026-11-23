import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalSecComb
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MatchingSectionsExist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftUnitTensor
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalOfPointwise

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ExpFrac

def sc {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) :
    F →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem gs_inv {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (a : F) :
    gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a) = sc p z a := by
  rw [gs_eq p z ⊤ trivial]; rfl

theorem gs_scal {F : Type} [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of F)) (z : Z)
    (a : F) : gs r z ⊤ (scal p a) = sc (r ≫ p) z a :=
  (gs_pull r p z ⊤ trivial _).trans (gs_inv _ z a)

theorem sc_map {F F' : Type} [CommRing F] [CommRing F'] (φ : F →+* F') {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of F')) (z : Z) (a : F) :
    sc (p ≫ Spec.map (CommRingCat.ofHom φ)) z a = sc p z (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [sc, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, e]

theorem jFK_self (R : Type) [CommRing R] [IsDomain R] :
    jFK (R := R) (FractionRing R) = 𝟙 (Spec (CommRingCat.of (FractionRing R))) := by
  show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))) = _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

theorem clear_sum {R S : Type} [CommRing R] [IsDomain R] [CommRing S] (χ : FractionRing R →+* S) {n : ℕ} (r : R)
    (a : Fin n → R) (c : Fin n → FractionRing R) (h : ∀ i, algebraMap R (FractionRing R) (a i) = r • c i)
    (v : Fin n → S) :
    ∑ i, χ (algebraMap R _ (a i)) * v i = χ (algebraMap R _ r) * ∑ i, χ (c i) * v i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i, Algebra.smul_def, map_mul, _root_.mul_assoc]

theorem expands_of_expF : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U.ExpF (FractionRing R) k t s.s → U'.Expands k σ s := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ t s hσ hK hE
  obtain ⟨n, c, σs, fs, hT, hA, hB⟩ := hE
  obtain ⟨⟨r, hr⟩, ha⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
  choose a ha using ha
  obtain ⟨σ', f', hT', hσ', hf'⟩ := ExpLin.expT_linear R I D.toPre A G U (𝟙_ _) k n
    (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) σs fs hT
  obtain ⟨-, e₁, -, e₂⟩ := UnitSec.same_exists R D.toPre G U.P.L.L U.P.L.isLB k
  obtain ⟨τ, hτ⟩ := e₁ σ'
  obtain ⟨f, hf⟩ := e₂ f'
  have hAt := fun τ' => expandsAt_of_expT R I D A G U U' hM k τ' τ σ' f f'
  have hG : GeneratorPullback.SecScal U.P.L.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) σ₀
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) τ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r) := by
    refine BoxFamScalar.secScal_of_pointwise U.P.L.isLB fun y J hJ => ?_
    obtain ⟨rG, hG₁, hG₂⟩ := exists_lift_unit_tensor G (𝟙 _ ≫ pullback.fst G.hom (jK R))
    choose JA hJA using fun ψ : pullback G.hom (jK R) ⟶ A.A.left => exists_chart A.isLB (ψ y)
    have w : pullback.snd G.hom (jK R) ≫ (TFK (R := R) (FractionRing R)).hom = U.gen.hom.left ≫ A.A.hom :=
      ((congrArg (pullback.snd G.hom (jK R) ≫ ·) (jFK_self R)).trans (Category.comp_id _)).trans
        (Over.w U.gen.hom).symm
    obtain ⟨rA, hA₁, hA₂⟩ : ∃ rA : pullback G.hom (jK R) ⟶ (TFK (R := R) (FractionRing R) ⊗ A.A).left,
        rA ≫ (fst _ A.A).left = pullback.snd G.hom (jK R) ∧ rA ≫ (snd _ A.A).left = 𝟙 _ ≫ U.gen.hom.left :=
      ⟨pullback.lift _ _ w, pullback.lift_fst _ _ w, (pullback.lift_snd _ _ w).trans (Category.id_comp _).symm⟩
    have e₃ := (hK _ rA (𝟙 _) hA₂ y JA J hJA hJ).symm.trans (hA _ rA (𝟙 _) rG hA₂ hG₁ y JA J hJA hJ)
    have e₄ : rG ≫ (fst _ G).left = pullback.snd G.hom (jK R) ≫ jK R :=
      hG₂.trans ((congrArg (· ≫ G.hom) (Category.id_comp _)).trans pullback.condition)
    refine ((congrArg (fun q => sval τ q y J) hG₁).symm.trans (hτ _ rG y J hJ).symm).trans
      ((hσ' _ rG y J hJ).trans ?_)
    refine Eq.trans ?_ (congrArg (_ * ·) e₃).symm
    refine Eq.trans ?_ ((clear_sum (sc (pullback.snd G.hom (jK R)) y) r a c ha (fun i => sval (σs i) rG y J)).trans ?_)
    · refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      exact (gs_inv _ y _).trans ((congrArg (fun q => sc q y (a i)) e₄).trans (sc_map _ _ y _))
    · refine congrArg₂ (· * ·) ?_ (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)
      · rw [gs_scal, Category.id_comp, sc_map]
      · exact ((gs_scal _ _ y _).trans (congrArg (fun q => sc q y (c i)) hA₁)).symm
  have hF : ∀ α : D.toPre.X,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom r) := by
    intro α
    refine BoxFamScalar.secScal_of_pointwise D.toPre.P.isLB fun y J hJ => ?_
    obtain ⟨rB, hB₁, hB₂⟩ := exists_lift_unit_tensor D.toPre.P.A (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing R)).left)
    have e₃ := hB α _ (𝟙 _) rB hB₁ y J hJ
    have e₅ : (DegPre.BF D.toPre (FractionRing R)).hom =
        (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R :=
      (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm.trans (congrArg
        ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ ·)
        ((congrArg (· ≫ jK R) (jFK_self R)).trans (Category.id_comp _)))
    have e₄ : rB ≫ (fst _ D.toPre.P.A).left = (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R :=
      hB₂.trans ((congrArg (· ≫ D.toPre.P.A.hom) (Category.id_comp _)).trans
        ((Over.w (DegPre.prB D.toPre (FractionRing R))).trans e₅))
    refine ((congrArg (fun q => sval (f α) q y J) hB₁).symm.trans (hf α _ rB y J hJ).symm).trans
      ((hf' α _ rB y J hJ).trans ?_)
    refine Eq.trans ?_ (congrArg (_ * ·) e₃).symm
    refine Eq.trans ?_ ((clear_sum (sc (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left y) r a c ha
      (fun i => sval (fs i α) rB y J)).trans ?_)
    · refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      exact (gs_inv _ y _).trans ((congrArg (fun q => sc q y (a i)) e₄).trans (sc_map _ _ y _))
    · refine congrArg₂ (· * ·) ?_ (Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_)
      · exact ((gs_scal _ _ y _).trans ((congrArg (fun q => sc q y r) ((Category.id_comp _).trans e₅)).trans
          (sc_map _ _ y _))).symm
      · exact ((gs_scal _ _ y _).trans (congrArg (fun q => sc q y (c i)) (Category.id_comp _))).symm
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U
  cases P
  have hL := hM.LG
  dsimp only at hL
  subst hL
  obtain rfl := eq_of_heq hσ
  exact ⟨r, nonZeroDivisors.ne_zero hr, τ, f, hG, hF, hAt τ HEq.rfl hτ hf hT'⟩

end GlobalTheory.UU.ExpFrac
end
