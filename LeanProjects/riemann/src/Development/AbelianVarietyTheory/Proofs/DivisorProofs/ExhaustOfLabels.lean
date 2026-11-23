import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section

namespace GlobalTheory.Poinc.Tors
open GlobalTheory.TorusExt

private theorem sumF_mul_left {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} {x y : Ix → F} {s t : F} (a : F) (h : SumF I F x s)
    (hy : ∀ i, y i = a * x i) (ht : t = a * s) : SumF I F y t := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, happ⟩ := h
  let f : F →ₗ[R] F :=
    { toFun := fun u => a * u
      map_add' := fun u v => mul_add a u v
      map_smul' := fun r u => by
        change a * ((algebraMap R (FractionRing R) r) • u) = (algebraMap R (FractionRing R) r) • (a * u)
        rw [Algebra.smul_def, Algebra.smul_def]
        ring }
  refine ⟨N.map f, hN.map f, ⟨s, hs, ht.symm⟩, fun i => ⟨x i, hx i, (hy i).symm⟩, fun n => ?_⟩
  obtain ⟨S, hS⟩ := happ n
  refine ⟨S, fun T hT => ?_⟩
  have hm := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at hm
  have e : f (s - ∑ i ∈ T, x i) = t - ∑ i ∈ T, y i := by
    change a * (s - ∑ i ∈ T, x i) = t - ∑ i ∈ T, y i
    rw [mul_sub, Finset.mul_sum, ht]
    simp only [hy]
  rw [e] at hm
  exact hm

attribute [local instance] gtGroup in

theorem exhaust_of_labels : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ N : ℕ, 1 ≤ N → ∀ (C : Type) (g : C → GtPtF D.toPre (FractionRing R)) (x : C → (TFK (R := R) (FractionRing R) ⟶ A.A)), (∀ c, ∃ o, GtPtF.IsNsmul N (g c) o ∧ o.IsZero) → (∀ c c', g c = g c' → x c = x c') → (∀ (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) N) (y : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A), p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing R)) N p y → ∃ c, y.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (x c).left) → ∀ b : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ D.toPre.P.A, b ^ N = 1 → ∃ c, b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (g c).b.left := by
  intro hLL R _ _ _ I hI D A G _ _ hSA U N hN C g x htor hfun hcov b hb
  have hB : D.toPre.TauBimult := D.tau_bimult
  have hN0 : N ≠ 0 := by omega
  have hf : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp (algebraMap (FractionRing R) (FractionRing R)) = (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) :=
    RingHom.ext fun _ => rfl
  obtain ⟨fT, hT⟩ := GlobalTheory.TorsionIso.torsion_eq hLL R I hI D A G hSA U (AlgebraicClosure (FractionRing R)) N hN
  obtain ⟨hT1, -, hT3, -⟩ := hT
  let P : {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} → QkPt D.toPre (AlgebraicClosure (FractionRing R)) N :=
    fun h => qkMk hB 0 h.1 (by rw [map_zero]; exact h.2)
  have hPy : ∀ h, (P h).y = 0 := fun h => qkMk_y hB _ _ _
  have hPg : ∀ h, (P h).g = h.1 := fun h => qkMk_g hB _ _ _
  have hEq : ∀ h h', QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (P h) (P h') → h = h' := by
    intro h h' e
    obtain ⟨z, hy, hg⟩ := (equiv_iff hB _ _).1 e
    rw [hPy, hPy, zero_add] at hy
    have hz : z = 0 := by
      have h2 : (N : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hy.symm
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact absurd (by exact_mod_cast h3 : N = 0) hN0
      · exact h3
    rw [hPg, hPg, hz, map_zero, add_zero] at hg
    exact Subtype.ext hg.symm
  haveI : Finite {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} := by
    have hc := GlobalTheory.UT.card_qk hLL R I hI D (AlgebraicClosure (FractionRing R)) N hN
    haveI : Finite (Quot (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N))) :=
      Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hN0)
    refine Finite.of_injective (β := Quot (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N)))
      (fun h => Quot.mk (QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing R)) (k := N)) (P h)) fun h h' e => hEq h h' ?_
    exact (equiv_equivalence hB).eqvGen_iff.1 (Quot.eqvGen_exact e)
  have hcx : ∀ h, ∃ c, (fT (P h)).left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ (x c).left :=
    fun h => hcov (P h) (fT (P h)) (hPy h) ((hT1 _ _).2 rfl)
  choose c hc using hcx
  have hgc : ∀ c, N • g c = 0 := by
    intro c
    obtain ⟨o, ho, hz⟩ := htor c
    rw [isNsmul_iff_eq] at ho
    rw [isZero_iff_eq] at hz
    rw [← ho, hz]
  let Φ : {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} → {h : GtPtF D.toPre (AlgebraicClosure (FractionRing R)) // N • h = 0} :=
    fun h => ⟨gtExt D.toPre (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) hf (g (c h)), by rw [← map_nsmul, hgc, map_zero]⟩
  have hΦ : Function.Injective Φ := by
    intro h h' e
    have e1 : g (c h) = g (c h') := GlobalTheory.Balanced.gtExt_injective _ hf D.toPre (congrArg Subtype.val e)
    have e2 := hfun _ _ e1
    apply hEq
    apply (hT3 _ _).1
    apply Over.OverMorphism.ext
    rw [hc, hc, e2]
  obtain ⟨g', hg'b, hg'N⟩ :=
    exists_nsmul_eq_of_pow_eq (D := D.toPre) (F := (AlgebraicClosure (FractionRing R))) hN0 0 (hb.trans zero_b.symm)
  obtain ⟨h, hh⟩ := (Finite.injective_iff_surjective.1 hΦ) ⟨g', hg'N⟩
  refine ⟨c h, ?_⟩
  have e1 : g' = gtExt D.toPre (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) hf (g (c h)) := (congrArg Subtype.val hh).symm
  rw [← hg'b, e1, gtExt_b, Over.comp_left, extMap_left]

section Scale
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

omit [IsDomain R] in
theorem exists_scale {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := R) F).left ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) {c : F} (hc : c ≠ 0) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ z J, Good L z J →
      (val t' (𝟙 _) z J).val = CoefBasic.cstH (R := R) z c * (val t (𝟙 _) z J).val := by
  let u : Γ((TF (R := R) F).left, ⊤)ˣ :=
    Units.map ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom : F →* Γ(Spec (CommRingCat.of F), ⊤)) (Units.mk0 c hc)
  refine ⟨GlobalTheory.UU.scaleGen u t, GlobalTheory.UU.scaleGen_isGen u ht, fun z J hJ => ?_⟩
  rw [GlobalTheory.UU.val_scaleGen u t (𝟙 _) hJ, Units.val_mul, ← gs_unit (𝟙 _) z ⊤ trivial u, ← CoefBasic.cst_eq]
  rfl

theorem coef_scale {D : DegPre R} {k : ℕ} (g : GtPtF D F) {w w' : Frm D F k g.b} (hw : w.IsGen) {c : F}
    (h : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = CoefBasic.cstH (R := R) z c * (val w (𝟙 _) z J).val)
    (s : Fam D F k) (χ : D.X) : coef s g w' χ = c * coef s g w χ := by
  apply CoefBasic.coef_eq
  intro z J hJ
  have hx := CoefBasic.isCoef_coef g hw χ s z J hJ
  rw [h z J hJ]
  rw [CoefBasic.cst_eq] at hx ⊢
  rw [map_mul]
  linear_combination (CoefBasic.cstH (R := R) z c) * hx

end Scale

theorem liesOver_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U) (g : GtPtF D.toPre F) (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x), w.IsGen → fr.IsGen → LiesOver U w₀ g w x fr → ∀ c : F, c ≠ 0 → ∃ (w' : Frm D.toPre F 1 g.b) (fr' : FrAt x), w'.IsGen ∧ fr'.IsGen ∧ LiesOver U w₀ g w' x fr' ∧ (∀ (s : Fam D.toPre F 1) χ, c * coef s g w' χ = coef s g w χ) ∧ ∀ z J, Good A.L z J → (val fr' (𝟙 _) z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val fr (𝟙 _) z J).val := by
  intro R _ _ I _ D A G _ _ U F _ _ w₀ g w x fr hw hfr hL c hc
  obtain ⟨w', hw', hw'v⟩ := exists_scale (R := R) (F := F) w hw (inv_ne_zero hc)
  obtain ⟨fr', hfr', hfr'v⟩ := exists_scale (R := R) (F := F) fr hfr hc
  refine ⟨w', fr', hw', hfr', ?_, ?_, ?_⟩
  · intro k hk wk hwk hwkg s s' v hexp hval
    have hck : c ^ k ≠ 0 := pow_ne_zero k hc
    obtain ⟨wk0, hwk0g, hwk0v⟩ := exists_scale (R := R) (F := F) wk hwkg hck
    have h1 : SumF I F (coef s' g wk0) (c ^ k * v) := by
      refine hL k hk wk0 ?_ hwk0g s s' (c ^ k * v) hexp ?_
      · intro z J hJ
        apply Units.ext
        have e : CoefBasic.cstH (R := R) z (c ^ k) * (CoefBasic.cstH (R := R) z c⁻¹) ^ k = 1 := by
          rw [← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ hc, one_pow, map_one]
        rw [hwk0v z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw'v z J hJ]
        linear_combination ((val w (𝟙 _) z J).val) ^ k * e
      · intro z J hJ
        have hv := hval z J hJ
        rw [hv, GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, zpow_natCast, zpow_natCast,
          Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
          show (val fr' (𝟙 (TFK (R := R) F).left) z J).val =
            @id ((TFK (R := R) F).left.presheaf.stalk z) (CoefBasic.cstH (R := R) z c) * (val fr (𝟙 (TFK (R := R) F).left) z J).val from hfr'v z J hJ]
        simp only [id, CoefBasic.cst_eq, map_mul, map_pow]
        ring
    have h2 : ∀ χ, coef s' g wk0 χ = c ^ k * coef s' g wk χ := fun χ => coef_scale g hwkg hwk0v s' χ
    exact sumF_mul_left (c ^ k)⁻¹ h1
      (fun χ => by rw [h2, ← _root_.mul_assoc, inv_mul_cancel₀ hck, _root_.one_mul])
      (by rw [← _root_.mul_assoc, inv_mul_cancel₀ hck, _root_.one_mul])
  · intro s χ
    rw [coef_scale g hw hw'v s χ, ← _root_.mul_assoc, mul_inv_cancel₀ hc, _root_.one_mul]
  · intro z J hJ
    rw [show (val fr' (𝟙 (TFK (R := R) F).left) z J).val =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (CoefBasic.cstH (R := R) z c) * (val fr (𝟙 (TFK (R := R) F).left) z J).val from hfr'v z J hJ]
    simp only [CoefBasic.cst_eq, id]

end GlobalTheory.Poinc.Tors
end
