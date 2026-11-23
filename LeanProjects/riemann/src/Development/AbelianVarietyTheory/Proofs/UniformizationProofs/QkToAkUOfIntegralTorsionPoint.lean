import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIndepCoords
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointQkStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsionStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace IntegralTorsionImage

open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding pw pw_trans
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.BoxExpansion

section General

variable {X X₁ X₂ Y Y' : Scheme.{0}} {K K' K₃ : Type} [Fintype K] [Fintype K'] [Fintype K₃]

theorem exists_gen_pull_smul {L : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) (a : Γ(Y', ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      val t' r z J = gm r z ⊤ a * val t (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι), r z ∈ LB.wchart L (fun k => h ≫ φ k) j →
      gm r z (LB.wchart L (fun k => h ≫ φ k) j) (res le_top a * (LB.pullGen L φ ε t h).s j) =
        gm r z ⊤ a * gm r z (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j) :=
    fun Z r z j hz => (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z le_top hz a))
  refine ⟨⟨fun j => @id (Γ(Y', LB.wchart L (fun k => h ≫ φ k) j)ˣ) (res le_top a * (LB.pullGen L φ ε t h).s j)⟩,
    isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z J hJ => ?_⟩
  · refine (v _ _ y j hj).trans (Eq.trans ?_ (congrArg _ (v _ _ y j' hj')).symm)
    rw [gen_trans (pullGen_isGen _ _ _ _ ht h) (𝟙 _) y hj hj', mul_left_comm]
  · exact (v Z r z _ (hJ.mem _ r)).trans (congrArg _ (val_pull hJ t h r))

theorem exists_translate {L : LB X} (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y ⟶ Y)
    {φ₃ : K₃ → (Y ⟶ X)} {ε₃ : K₃ → ℤ} (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (q : (Y ⟶ X) → U),
      ∏ k, q (φ₃ k) ^ ε₃ k = (∏ k, q (φ k) ^ ε k) * (∏ k, q (h ≫ φ k) ^ ε k)⁻¹)
    (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ ε), GeneratorPullback.SecRel L φ ε s' φ ε s h φ₃ ε₃ u := by
  obtain ⟨s', hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ q => by
    refine (prod_sum₂ (K := K) (K' := K₃) (U := U) _ (c := ∏ k, q (h ≫ φ k) ^ ε k) rfl (hF U q)).trans ?_
    exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)) (pullMulSec s h u hu)
  exact ⟨s', (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ =>
    (hs _ _ y J hJ).trans (sval_pullMulSec _ _ _ _ _ y hJ)⟩

theorem exists_unit_ratio {L₁ : LB X₁} {L₂ : LB X₂} (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (ψ : K → (Y' ⟶ Y)) {ε : K → ℤ}
    {φ₁ : K → (Y' ⟶ X₁)} {φ₂ : K → (Y' ⟶ X₂)} (h₁ : ∀ k, φ₁ k = ψ k ≫ f₁) (h₂ : ∀ k, φ₂ k = ψ k ≫ f₂)
    {t₁ : LB.Gen (LB.LinComb L₁ φ₁ ε)} {t₂ : LB.Gen (LB.LinComb L₂ φ₂ ε)} (ht₁ : t₁.IsGen) (ht₂ : t₂.IsGen) :
    ∃ u : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J₁ J₂), Good L₁ z J₁ → Good L₂ z J₂ →
      (∏ k, pw w (r ≫ ψ k) z (J₁ ((r ≫ ψ k) ≫ f₁)) (J₂ ((r ≫ ψ k) ≫ f₂)) ^ ε k) * val t₁ r z J₁ =
        gm r z ⊤ u * val t₂ r z J₂ := by
  obtain rfl : φ₁ = fun k => ψ k ≫ f₁ := funext h₁
  obtain rfl : φ₂ = fun k => ψ k ≫ f₂ := funext h₂
  let W : (K → L₁.ι) × (K → L₂.ι) → Y'.Opens := fun p =>
    LB.wchart L₁ (fun k => ψ k ≫ f₁) p.1 ⊓ LB.wchart L₂ (fun k => ψ k ≫ f₂) p.2
  have l : ∀ p k, W p ≤ ψ k ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => p.2 k) ⊓ (L₁.pull f₁).U (fun _ => p.1 k)) :=
    fun p k y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 k), mem_pull.2 (Set.mem_iInter.1 hy.1 k)⟩
  let θ : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y') (z : Z), (K → L₁.ι) × (K → L₂.ι) → (Z.presheaf.stalk z)ˣ := fun Z r z p =>
    (∏ k, pw w (r ≫ ψ k) z (p.1 k) (p.2 k) ^ ε k) * gm r z (LB.wchart L₁ (fun k => ψ k ≫ f₁) p.1) (t₁.s p.1) *
      (gm r z (LB.wchart L₂ (fun k => ψ k ≫ f₂) p.2) (t₂.s p.2))⁻¹
  obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(Y', W p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p, r z ∈ W p →
      gm r z (W p) (u p) = θ Z r z p := by
    refine ⟨fun p => (∏ k, res (l p k) (pullU (ψ k) _ (w.s (fun _ => p.2 k, fun _ => p.1 k))) ^ ε k) *
      res inf_le_left (t₁.s p.1) * (res inf_le_right (t₂.s p.2))⁻¹, fun Z r z p hz => ?_⟩
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans
      (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans
      (congrArg (· ^ ε k) ((gm_res r z _ hz _).trans (gm_pull r (ψ k) z _ (l p k hz) _))))) (gm_res r z _ hz _)))
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r z _ hz _))))
  have hθ : ∀ (y : Y') p q, y ∈ W p → y ∈ W q → θ _ (𝟙 Y') y p = θ _ (𝟙 Y') y q := by
    intro y p q hp hq
    have a := fun k => pw_trans hw (𝟙 Y' ≫ ψ k) y (j₁ := p.1 k) (j₁' := q.1 k) (j₂ := p.2 k) (j₂' := q.2 k)
      (Set.mem_iInter.1 hp.1 k) (Set.mem_iInter.1 hq.1 k) (Set.mem_iInter.1 hp.2 k) (Set.mem_iInter.1 hq.2 k)
    simp only [θ]
    rw [gen_trans ht₁ (𝟙 Y') y hp.1 hq.1, gen_trans ht₂ (𝟙 Y') y hp.2 hq.2,
      Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) (a k)]
    simp only [Geo.Tor.trF, Category.assoc, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨s, hs⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      choose a ha using fun k => exists_chart hL₁ ((ψ k ≫ f₁) y)
      choose b hb using fun k => exists_chart hL₂ ((ψ k ≫ f₂) y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), Set.mem_iInter.2 ha, Set.mem_iInter.2 hb⟩) u
    (fun p q y hy => (hu _ _ y p hy.1).trans ((hθ y p q hy.1 hy.2).trans (hu _ _ y q hy.2).symm))
  refine ⟨s, fun Z r z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  have hz : r z ∈ W (fun k => J₁ (r ≫ ψ k ≫ f₁), fun k => J₂ (r ≫ ψ k ≫ f₂)) := ⟨hJ₁.mem _ r, hJ₂.mem _ r⟩
  have := (gm_res r z le_top hz s).symm.trans ((congrArg (gm r z _) (hs _)).trans (hu Z r z _ hz))
  rw [this]
  simp only [Category.assoc]
  exact (inv_mul_cancel_right _ _).symm

end General

section Points

variable {S S' : Scheme.{0}} {G : Over S} {A : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj A] {f : S' ⟶ S}
  {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) {T : Over S'} (x : 𝟙_ (Over S) ⟶ G) (xT : T ⟶ A)
  (hx : xT.left ≫ φ = T.hom ≫ f ≫ x.left)
include h hx

omit [IsCommMonObj G] in
theorem push_eq {T' : Over S'} (ρ : T' ⟶ T) : pushHom h T' (ρ ≫ xT) = toUnit _ ≫ x := by
  apply Over.OverMorphism.ext
  show (ρ.left ≫ xT.left) ≫ φ = (T'.hom ≫ f) ≫ x.left
  rw [Category.assoc, hx, ← Category.assoc, Over.w ρ, Category.assoc]

theorem pow_eq_one_of_push {k : ℕ} (hk : x ^ k = 1) : xT ^ k = 1 := by
  have e : pushHom h T (xT ^ k) = pushHom h T 1 := by
    rw [map_pow, map_one, ← Category.id_comp xT, push_eq h x xT hx]
    exact (map_pow (preHom _) x k).symm.trans ((congrArg _ hk).trans (map_one _))
  apply Over.OverMorphism.ext
  exact h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w _).trans (Over.w _).symm)

theorem translPt_push :
    (translPt A xT).left ≫ φ = ((snd T A).left ≫ φ) ≫ (𝟙 G * (toUnit G ≫ x)).left := by
  have e : pushHom h (T ⊗ A) (translPt A xT) = pushHom h (T ⊗ A) (snd T A) ≫ (𝟙 G * (toUnit G ≫ x)) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, mul_comm, ← push_eq h x xT hx (fst T A),
      ← map_mul]
    rfl
  exact congrArg (fun q => q.left) e

end Points

section Sides

variable {F : Type} [CommRing F] {X Y Y' : Scheme.{0}} {L : LB X} {K K₃ : Type} [Fintype K] [Fintype K₃]

theorem secLin_translate (hL : L.IsLB) {φ : K → (Y ⟶ X)} {φ₁ : K → (Y' ⟶ X)} {ε : K → ℤ} {φ₃ : K₃ → (Y ⟶ X)}
    {ε₃ : K₃ → ℤ} {u : LB.Gen (LB.LinComb L φ₃ ε₃)} {p : Y' ⟶ Y} {τ : Y ⟶ Y} {τ' : Y' ⟶ Y'} (hτ : τ' ≫ p = p ≫ τ)
    {π : Y' ⟶ Spec (CommRingCat.of F)} (hπ : τ' ≫ π = π) {n : ℕ} {c : Fin n → F} (a : F)
    {σ σ' : Fin n → LB.Sec (LB.LinComb L φ ε)} (hσ : ∀ i, GeneratorPullback.SecRel L φ ε (σ' i) φ ε (σ i) τ φ₃ ε₃ u)
    {s s' : LB.Sec (LB.LinComb L φ₁ ε)} (hs : GeneratorPullback.SecLin L φ₁ ε s φ ε σ p (fun i => scal π (c i)))
    (hs' : ∀ y J, Good L y J → sval s' (𝟙 Y') y J = sval s τ' y J * (constHomVal π y a * (val u p y J).val)) :
    GeneratorPullback.SecLin L φ₁ ε s' φ ε σ' p (fun i => scal π (a * c i)) := by
  refine (secLin_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  rw [hs' y J hJ, secLin_val hs τ' y hJ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (hσ i) _ _ y J hJ, gs_scal, gs_scal, hπ, hτ, Category.id_comp,
    Category.id_comp, constVal_eq, constVal_eq, map_mul]
  ring

theorem unit_of_base {π : Y ⟶ Spec (CommRingCat.of F)} (hπ : Function.Surjective π.appTop.hom)
    (e : Spec (CommRingCat.of F) ⟶ Y) (he : e ≫ π = 𝟙 _) (u : Γ(Y, ⊤)ˣ) :
    ∃ (a : F) (b : Γ(Spec (CommRingCat.of F), ⊤)ˣ), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      (gm r z ⊤ u).val = constHomVal (r ≫ π) z a) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z),
      (gm r z ⊤ b).val = constHomVal r z a := by
  obtain ⟨b, hb⟩ := hπ u.val
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 b
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), (gm r z ⊤ u).val = constHomVal (r ≫ π) z a := fun Z r z =>
    (gs_unit r z ⊤ trivial u).symm.trans ((congrArg (gs r z ⊤) hb.symm).trans
      ((gs_scal π r z a).trans (constVal_eq _ _ _)))
  refine ⟨a, pullU e ⊤ u, v, fun Z r z => ?_⟩
  refine (congrArg Units.val (gm_pull r e z ⊤ trivial u)).trans ((v _ _ z).trans ?_)
  rw [Category.assoc, he, Category.comp_id]

variable {X₁ X₂ E T : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}

theorem act_through_iso (hL₁ : L₁.IsLB) {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {k : ℕ} {g : E ⟶ X₁} {m : T ⟶ Y}
    {h : T ⟶ E} {τ : E ⟶ E} {τ' : T ⟶ T} (hτ : τ' ≫ h = h ≫ τ) {ψ : Fin 2 → (E ⟶ Y)} (e₀ : h ≫ ψ 0 = m)
    (e₁ : h ≫ ψ 1 = τ' ≫ m) {t t' : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g) (fun _ => (k : ℤ)))}
    {s s' : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => m ≫ f₂) (fun _ => (k : ℤ)))}
    (H : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g h t (m ≫ f₂) (𝟙 T) s)
    (H' : GeneratorPullback.IsoRelM L₁ L₂ f₁ f₂ w m k g h t' (m ≫ f₂) (𝟙 T) s') (y : T) {J₂} (hJ₂ : Good L₂ y J₂)
    (v : ((T ⟶ X₁) → L₁.ι) → (T.presheaf.stalk y)ˣ) (v₂ : (T.presheaf.stalk y)ˣ)
    (ha : ∀ J₁, Good L₁ y J₁ → sval t' h y J₁ = (v J₁).val * sval t (h ≫ τ) y J₁)
    (hv : ∀ J₁, Good L₁ y J₁ → (∏ i, pw w (h ≫ ψ i) y (J₁ ((h ≫ ψ i) ≫ f₁)) (J₂ ((h ≫ ψ i) ≫ f₂)) ^
      (![(k : ℤ), -(k : ℤ)] i)) * v J₁ = v₂) :
    sval s' (𝟙 T) y J₂ = sval s τ' y J₂ * v₂.val := by
  choose J hJ using fun χ : T ⟶ X₁ => exists_chart hL₁ (χ y)
  have hJ : Good L₁ y J := hJ
  have a₁ := isoRel_val H τ' y hJ hJ₂
  have a₂ := isoRel_val H' (𝟙 _) y hJ hJ₂
  have a₃ := hv J hJ
  rw [Fin.prod_univ_two, e₀, e₁] at a₃
  simp only [Category.id_comp, Category.comp_id] at a₁ a₂
  rw [a₁, a₂, ha J hJ, hτ, ← a₃]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast]
  generalize pw w (τ' ≫ m) y _ _ ^ k = P
  simp only [Units.val_mul]
  linear_combination (-(pw w m y (J (m ≫ f₁)) (J₂ (m ≫ f₂)) ^ k).val * (v J).val * sval t (h ≫ τ) y J) * P.mul_inv

end Sides

end IntegralTorsionImage

open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding pw pw_trans in
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.BoxExpansion IntegralTorsionImage in
set_option maxHeartbeats 1000000 in

theorem qkToAkU_of_integral_torsion : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (k : ℕ), 1 ≤ k → ∀ (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (p : QkPt D.toPre F k) (xF : TFK (R := R) F ⟶ A.A), p.y = 0 → GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g → xF.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R) F) ≫ x).left → QkToAkU U.toUnifPre F k p xF := by
  intro hL R _ _ _ I hR hI D A G _ _ U k hk x gp hx hm F _ _ p xF hy hp hxF w hw
  have hG : GlobalFnsSt := hL.globalFns
  obtain ⟨hb, -⟩ := T.torsionPoint_qk_alt hG R I hR hI D A G U.toUnifPre k x gp hx hm
  obtain ⟨ν, uL, uM, hν, huL, huM, hE⟩ := T.expandsAt_translate_torsion_alt hG R I hR hI D A G U.toUnifPre k x gp hx hb hm
  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gpb : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have hx' : xF.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (TFK (R := R) F).hom ≫ jK R ≫ x.left :=
    hxF.trans (Category.assoc _ _ _)
  refine ⟨pow_eq_one_of_push gpb x xF hx' hx, fun θ hθ => ?_⟩
  subst hθ
  have tp := translPt_push gpb x θ.pt hx'
  have ih : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := congrArg Over.Hom.left U.gen.inv_hom_id
  let ψ : Fin 2 → ((TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left) :=
    ![(snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left, (translPt A.A θ.pt).left ≫ U.gen.inv.left]
  obtain ⟨t₂, ht₂, vt₂⟩ := exists_gen_pull_smul uL huL
    ((snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))
    (fun i => ψ i ≫ pullback.fst G.hom (jK R)) (Fin.forall_fin_two.2
      ⟨(Category.assoc _ _ _).trans (Category.comp_id _).symm, (Category.assoc _ _ _).trans tp⟩) 1
  obtain ⟨u, hu⟩ := exists_unit_ratio A.isLB U.LG.isLB hw ψ
    (φ₁ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left]) (Fin.forall_fin_two.2
      ⟨((Category.assoc _ _ _).trans ((congrArg _ ih).trans (Category.comp_id _))).symm,
        ((Category.assoc _ _ _).trans ((congrArg _ ih).trans (Category.comp_id _))).symm⟩) (fun _ => rfl) θ.isGen ht₂
  obtain ⟨a, b, ha, hb'⟩ := unit_of_base (F := F) (π := (fst (TFK (R := R) F) A.A).left)
    (BoxTheta.surj_fst hG A.isAb _) (lift (𝟙 (TFK (R := R) F)) (1 : _ ⟶ A.A)).left
    (congrArg Over.Hom.left (lift_fst (𝟙 (TFK (R := R) F)) (1 : _ ⟶ A.A))) u
  obtain ⟨w', hw', vw'⟩ := exists_gen_pull_smul ν hν (toUnit (TF (R := R) F)).left (DegPre.lineφ D.toPre F p.g.b)
    (Fin.forall_fin_two.2 ⟨rfl, hp.1⟩) b
  refine ⟨w', hw', ?_⟩
  rintro t t' s s' ⟨σF, hR₁, n, c, σ, f, hA, hs, hf⟩ ⟨σF', hR₂, hE'⟩ hact
  obtain ⟨s₂, hs₂⟩ := exists_phi hG p w' hw' D.tau_bimult s
  choose σ' hσ' using fun i => exists_translate U.LG.isLB (𝟙 G * (toUnit G ≫ x)).left uL huL (fun V _ q => by
    rw [Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, Category.comp_id]
    exact congrArg _ (zpow_neg _ _)) (σ i)
  choose f' hf' using fun i α => exists_translate D.toPre.P.isLB
    (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left (uM α) (huM α).1 (fun V _ q =>
      prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ rfl (prod_neg _ _ rfl)) (f i α)
  obtain rfl : s' = s₂ := by
    refine expandsG_unique R I hR D A G U.toUnifPre k F σF' s' s₂ hE'
      ⟨n, fun i => a * c i, σ', f', fun i e => hE _ _ _ _ (hσ' i) (hf' i) e (hA i e), ?_, fun α => ?_⟩
    · let τ : UnifPre.GF (G := G) F ⟶ UnifPre.GF (G := G) F :=
        lift (fst _ _) (U.toUnifPre.genF F ≫ translPt A.A θ.pt ≫ U.gen.inv)
      have e₀ : (U.toUnifPre.genF F).left ≫ ψ 0 = (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left :=
        congrArg Over.Hom.left (show U.toUnifPre.genF F ≫ snd _ _ ≫ U.gen.inv = snd _ _ by simp)
      have e₁ : (U.toUnifPre.genF F).left ≫ ψ 1 =
          τ.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left :=
        congrArg Over.Hom.left (lift_snd (fst _ _) (U.toUnifPre.genF F ≫ translPt A.A θ.pt ≫ U.gen.inv)).symm
      have e₂ : τ ≫ U.toUnifPre.genF F = U.toUnifPre.genF F ≫ translT A.A θ.pt := by
        ext1 <;> simp [τ, translT]
      have e₃ : (U.toUnifPre.genF F).left ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫
          pullback.fst G.hom (jK R) = UnifPre.gFK (G := G) F := by
        rw [UnifPre.gFK, ← e₀]; simp only [ψ, Matrix.cons_val_zero, Category.assoc]
      have e₄ : (U.toUnifPre.genF F).left ≫ (fst (TFK (R := R) F) A.A).left =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := congrArg Over.Hom.left (lift_fst _ _)
      refine secLin_translate U.LG.isLB (τ' := τ.left) ?_ (congrArg Over.Hom.left (lift_fst _ _)) a hσ' hs
        fun y J hJ => ?_
      · rw [← e₃, Category.assoc (U.toUnifPre.genF F).left, ← tp, e₃, UnifPre.gFK, ← Category.assoc, ← e₁]
        simp only [ψ, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc]
      · refine (act_through_iso A.isLB (congrArg Over.Hom.left e₂) e₀ e₁ hR₁ hR₂ y hJ _ _
          (fun J₁ hJ₁ => BoxTheta.act_val θ t t' hact _ y hJ₁) (fun J₁ hJ₁ => hu _ _ y J₁ J hJ₁ hJ)).trans ?_
        rw [vt₂ _ _ y J hJ, map_one, _root_.one_mul, Units.val_mul, ha, e₃, e₄]
    · have e₁ : DegPre.trPt D.toPre F p.g.b ≫ DegPre.prB D.toPre F =
          DegPre.prB D.toPre F ≫ (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)) := by
        have e : p.g.b = toUnit _ ≫ gp.b := Over.OverMorphism.ext hp.1
        rw [tr_pr, MonObj.comp_mul, Category.comp_id, e, ← Category.assoc, ← Category.assoc, comp_toUnit, comp_toUnit]
      have e₂ := congrArg Over.Hom.left e₁
      have hα : α + p.y = α := by rw [hy, add_zero]
      obtain ⟨v, hv, vv⟩ := exists_gen_pull_smul (uM α) (huM α).1 (DegPre.prB D.toPre F).left
        (DegPre.phiφ D.toPre F p.y α p.g.b) (by
          rintro (i | i)
          · exact (congrArg (fun β => DegPre.famφ D.toPre F β i) hα).trans (GC.famφ_eq D.toPre F α i)
          · exact (congrArg _ (GC.famφ_eq D.toPre F α i)).trans ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ _) e₂).trans (Category.assoc _ _ _))))
        (pullU (fst (TF (R := R) F) D.toPre.P.A).left ⊤ b)
      have hc : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ v (DegPre.zF D.toPre F).left)
          (LB.mulGen D.toPre.P.L _ _ _ _ (p.g.s α) w') := corr_of_val D.toPre.P.isLB fun y J hJ => by
        have z₁ : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := R) F) D.toPre.P.A).left = 𝟙 _ :=
          congrArg Over.Hom.left (lift_fst _ _)
        have z₂ : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left =
            (toUnit (TF (R := R) F)).left ≫ eSec D.toPre.P.A := congrArg Over.Hom.left (lift_snd _ _)
        have c₁ := val_corr hJ (huM α).2 (toUnit (TF (R := R) F)).left
        have c₂ := val_corr hJ (hp.2 α) (𝟙 _)
        rw [val_pull hJ, val_mul hJ] at c₁
        rw [val_pull hJ, Category.id_comp] at c₂
        rw [val_pull hJ, vv _ _ y J hJ, val_mul hJ, vw' _ _ y J hJ, Category.id_comp, Category.id_comp, z₂, c₁, c₂,
          mul_left_comm]
        refine congrArg _ (congrArg (· * _) ?_)
        exact (gm_pull _ _ y ⊤ trivial b).trans (by rw [z₁])
      refine secLin_translate D.toPre.P.isLB e₂ (congrArg Over.Hom.left (tr_fst D.toPre F p.g.b)) a
        (fun i => hf' i α) (hf α) fun y J hJ => ?_
      have h₁ := hs₂ α α hα _ (𝟙 _) y J hJ
      rw [← (gen_phi hG p w' hw' α).2 v hv hc _ (𝟙 _) y J hJ, vv _ _ y J hJ, Category.id_comp, Over.id_left,
        Category.id_comp, Units.val_mul] at h₁
      refine h₁.trans (congrArg _ (congrArg (· * _) ?_))
      exact (congrArg Units.val (gm_pull _ _ y ⊤ trivial b)).trans ((hb' _ _ y).trans (by rw [Category.id_comp]))
  exact (phiRel_iff hG p w' hw' s s').2 hs₂

end GlobalTheory
