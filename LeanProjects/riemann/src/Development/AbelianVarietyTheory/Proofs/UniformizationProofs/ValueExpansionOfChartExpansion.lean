import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpTOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MatchingSectionsExist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) : sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have e := H (fun k => J (r ≫ φ₁ k)) (fun k => J (r ≫ h ≫ φ₂ k)) (by
    rintro (a | a) (b | b) e <;> exact congrArg (fun q => J (r ≫ q)) e)
  have hm : r z ∈ LB.wchart L φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) :=
    ⟨hJ.mem φ₁ r, hJ.mem (fun k => h ≫ φ₂ k) r⟩
  have le : LB.wchart L (fun k => h ≫ φ₂ k) (fun k => J (r ≫ h ≫ φ₂ k)) ≤
      h ⁻¹ᵁ LB.wchart L φ₂ (fun k => J (r ≫ h ≫ φ₂ k)) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  rw [sval_of s₂ (r ≫ h) z J (fun k => J (r ≫ h ≫ φ₂ k)) (fun k => by rw [Category.assoc])]
  have e2 := congrArg (gs r z _) e
  exact ((gs_res r z _ hm _).trans (gs_pull r h z _ (le hm.2) _)).symm.trans (e2.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_res r z le_top hm _) (gs_res r z _ hm _))))

theorem scal_specMap {A C : Type} [CommRing A] [CommRing C] (φ : A →+* C) {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (a : A) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) a = scal p (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact congrArg p.appTop.hom e.symm

theorem gs_scal_inv_mul {R : Type} [CommRing R] [IsDomain R] {Y₁ Y₂ Z : Scheme.{0}}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of (FractionRing R))) (p₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂) (h : r₂ ≫ p₂ = ((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) (z : Z)
    {a : R} (ha : a ≠ 0) :
    gs r₁ z ⊤ (scal p₁ (algebraMap R (FractionRing R) a)⁻¹) * gs r₂ z ⊤ (scal p₂ a) = 1 := by
  have k : ∀ {S : Type} [CommRing S] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of S)) (r : Z ⟶ Y) (c : S),
      gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
    intro S _ Y p r c
    calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
      _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
      _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl
  have e : scal (((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) a =
      scal (r₁ ≫ p₁) (algebraMap R (FractionRing R) a) :=
    (scal_specMap _ _ a).trans (scal_specMap _ _ _)
  have ha' : algebraMap R (FractionRing R) a ≠ 0 := fun h0 =>
    ha (IsFractionRing.injective R (FractionRing R) (h0.trans (map_zero _).symm))
  rw [k p₁, k p₂, h, e, ← gs_mul _ z ⊤ trivial, scal, scal, ← map_mul, ← map_mul, inv_mul_cancel₀ ha', map_one, map_one,
    gs_eq _ z ⊤ trivial, map_one, map_one]

theorem expF_of_expands : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G) (U' : UnifPre I D A G), Match U U' → ∀ (k : ℕ) (σ : U'.SecK k) (σ₀) (t) (s : Fam D.toPre (FractionRing R) k), HEq σ σ₀ → U.SameK (k := k) σ₀ t → U'.Expands k σ s → U.ExpF (FractionRing R) k t s.s := by
  intro R _ _ I D A G _ _ U U' hM k σ σ₀ t s hσ hK hE
  obtain ⟨r, hr, τ, f, hτ, hf, hE⟩ := hE
  have hL := hM.LG
  have hX := fun τ₀ τ' f' h₁ h₂ h₃ => expT_of_expandsAt R I D A G U U' hM k τ τ₀ τ' f f' h₁ h₂ h₃ hE
  clear hE hM
  cases U'
  dsimp only at hL
  subst hL
  cases hσ
  obtain ⟨e₁, -, e₃, -⟩ := GlobalTheory.UnitSec.same_exists R D.toPre G U.P.L.L U.P.L.isLB k
  obtain ⟨τ', hτ'⟩ := e₁ τ
  obtain ⟨f', hf'⟩ := e₃ f
  refine ⟨1, fun _ => (algebraMap R (FractionRing R) r)⁻¹, fun _ => τ', fun _ => f',
    fun _ => hX τ τ' f' HEq.rfl hτ' hf', ?_, ?_⟩
  · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
    refine (hK Z rA y h₁ z JA JG hJA hJG).trans ?_
    rw [Fin.sum_univ_one, hτ' Z rG z JG hJG, h₂]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal hτ y z hJG)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rA y ?_ z hr).symm)
    have w₁ := Over.w (fst (TFK (R := R) (FractionRing R)) A.A)
    have w₂ := Over.w (snd (TFK (R := R) (FractionRing R)) A.A)
    have w₃ := Over.w U.gen.hom
    have w₄ : (rA ≫ (fst (TFK (R := R) (FractionRing R)) A.A).left) ≫ jFK (R := R) (FractionRing R) =
        y ≫ pullback.snd G.hom (jK R) :=
      (Category.assoc _ _ _).trans ((congrArg (rA ≫ ·) (w₁.trans w₂.symm)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ A.A.hom) h₁).trans ((Category.assoc _ _ _).trans (congrArg (y ≫ ·) w₃)))))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) w₄.symm)
  · intro α Z rF rB h₁ z J hJ
    rw [Fin.sum_univ_one, hf' α Z rB z J hJ, h₁]
    refine Eq.trans ?_ (congrArg (_ * ·) (sval_of_secScal (hf α) rF z hJ)).symm
    rw [← _root_.mul_assoc]
    refine (_root_.one_mul _).symm.trans (congrArg (· * _) (gs_scal_inv_mul _ _ rF rF ?_ z hr).symm)
    have w₁ := Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)
    exact (congrArg (rF ≫ ·) w₁.symm).trans ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm)

end GlobalTheory.UU
