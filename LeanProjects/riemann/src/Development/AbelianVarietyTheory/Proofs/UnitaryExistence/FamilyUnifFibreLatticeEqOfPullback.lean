import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueLinearLiftUniformisedFibres
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

namespace FibreMatch

theorem surjective_of_countable {V W L : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Countable L] (f : V →ₗ[ℂ] W) (P : L → W) (h : ∀ w, ∃ z a, w = f z + P a) : Function.Surjective f := by
  have hc : Countable (W ⧸ LinearMap.range f) :=
    Function.Surjective.countable (f := fun a => (LinearMap.range f).mkQ (P a)) fun q => by
      obtain ⟨w, rfl⟩ := (LinearMap.range f).mkQ_surjective q
      obtain ⟨z, a, rfl⟩ := h w
      refine ⟨a, ?_⟩
      have : (LinearMap.range f).mkQ (f z) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩
      simp only [map_add, this, zero_add]
  intro w
  by_contra hw
  have hq : (LinearMap.range f).mkQ w ≠ 0 := fun h0 => hw ((Submodule.Quotient.mk_eq_zero _).1 h0)
  have : Countable ℂ := (smul_left_injective ℂ hq).countable
  exact not_countable (α := ℝ) (Complex.ofReal_injective.countable)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem countable_La (D : Datum H) : Countable D.La := by
  have := D.fin
  have : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  exact Finsupp.Countable.of_moduleFinite (R := 𝓞 E)

theorem fibrewise {X : Scheme.{0}} (t : SAB H (Sp ℂ)) (t' : SAB H X) (D₁ D₂ : Datum H) {g : ℕ}
    (ty : Fin g → (E →+* ℂ))
    (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (y y' : Sp ℂ ⟶ X) (n : SABMap t t' y) (hy : (𝟙_ (Over (Sp ℂ))).hom ≫ y = y')
    (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ t'.G))
    (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (hl : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (hl' : ∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t'.act.act a)
    (hw : ∀ (k : ℕ) (a b : D₁.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₁.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hw' : ∀ (k : ℕ) (a b : D₂.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₂.EF a b : ℂ) / k) →
      Out.WeilIs t'.G t'.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c))
    (hh : IsHolTo Set.univ (fun z => (e z).left)) (hh' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd' : (∀ w, ∃! v : epsPt y' ⟶ t'.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧
      ∀ v : epsPt y' ⟶ t'.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La ≃ₗ[𝓞 E] D₂.La), (∀ z, (e z).left ≫ n.φ = (e' (h z)).left) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', D₂.EF (gam a) (gam a') = D₁.EF a a') := by
  subst hy
  have dk' : DiscreteTopology {z // e' z = 1} := by
    have h0 : (fun z => e' z = 1) = fun z => z ∈ P'.range := funext fun z => propext (hk' z)
    show DiscreteTopology (Subtype fun z => e' z = 1)
    rw [h0]
    exact hP'.2.2.1
  let ρ := pushHom n.cart (𝟙_ (Over (Sp ℂ)))
  have hρ : ∀ x, (ρ x).left = x.left ≫ n.cm.F := fun _ => rfl
  have ρi : Function.Injective ρ := fun x x' hx => Over.OverMorphism.ext <| n.cart.1.hom_ext
    (by rw [← hρ, ← hρ, hx]) (by rw [Over.w, Over.w])
  have ρs : Function.Surjective ρ := fun x =>
    ⟨Over.homMk (n.cart.1.lift x.left (𝟙_ (Over (Sp ℂ))).hom (Over.w x)) (n.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (n.cart.1.lift_fst _ _ _)⟩
  let ψ : pullback t.G.hom (𝟙 (Sp ℂ)) ⟶ pullback t'.G.hom ((𝟙_ (Over (Sp ℂ))).hom ≫ y) :=
    pullback.lift (pullback.fst _ _ ≫ n.cm.F) (pullback.snd _ _) (by
      rw [Category.assoc, n.cart.1.w, ← Category.assoc, pullback.condition, Category.assoc]
      rfl)
  have ψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ n.cm.F := pullback.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  obtain ⟨f, hf, -⟩ := existsUnique_linear_lift_fibre (Sp ℂ) X t.G t'.G (𝟙 _) _ g g e e' ψ ρ t'.semi.smooth ha ha'
    hh hh' hd' dk' ψ₂ (fun x => pullback.hom_ext
      (by rw [Category.assoc, ψ₁, ← Category.assoc, UniformLift.fibPt_fst, UniformLift.fibPt_fst]; rfl)
      (by rw [Category.assoc, ψ₂, UniformLift.fibPt_snd, UniformLift.fibPt_snd]))
  have hf : ∀ z, e' (f z) = ρ (e z) := hf
  have := countable_La D₂
  have fs : Function.Surjective f := surjective_of_countable f P' fun w => by
    obtain ⟨x, hx⟩ := ρs (e' w)
    obtain ⟨z, rfl⟩ := hs x
    obtain ⟨a, ha⟩ := (hk' _).1 ((ExpUniqFamily.eq_iff_sub e' ha' w (f z)).1 (hx.symm.trans (hf z).symm))
    exact ⟨z, a, by rw [ha]; abel⟩
  let fe := LinearEquiv.ofBijective f ⟨LinearMap.injective_iff_surjective.2 fs, fs⟩
  obtain ⟨h, gam, h1, h2, -⟩ := ExpUniqFamily.algebraic (fun k (a : 𝓞 E) => ty k (a : E)) P P' hP.1 hP'.1
    hP.2.1 hP'.2.1 hP.2.2.1 hP'.2.2.1 (fun z => ρ (e z)) e' (fun z w => by rw [ha, map_mul]) ha'
    (fun z => by rw [← hk, map_eq_one_iff ρ ρi]) hk' (fun a x => x ≫ t'.act.act a)
    (fun a z => by
      rw [hl]
      apply Over.OverMorphism.ext
      rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, n.act, Category.assoc])
    hl' f fe.symm hf (fun z => by
      rw [← hf]
      exact congrArg e' (fe.apply_symm_apply z))
  refine ⟨h, gam, fun z => by rw [h1, hρ], h2, fun a a' => ?_⟩
  refine ExpUniqFamily.int_eq_of_exp _ _ fun k hk0 => ?_
  have hL : LBIso t.PP.L (t'.PP.L.pull n.cm.F) := by
    obtain ⟨w, hw, -⟩ := n.lin
    exact ⟨w, hw⟩
  have w1 := (weilIs_grpPullback_of_comm X (Sp ℂ) t'.G t.G y n.cm.F t'.PP.L t.PP.L t'.PP.isLB t.PP.isLB n.cart hL
    _ k _ _ (ρ _) (ρ _) _ (hρ _) (hρ _)).1 (hw k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl)
  have w2 := hw' k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  rw [h2, h2, ← map_smul h, ← map_smul h, h1, h1] at w2
  exact congrArg Units.val (weilIs_unique_fieldPoint X t'.G t'.PP.L t'.PP.isLB ℂ _ k _ _ _ _ w2 w1)

end FibreMatch

theorem familyUnif_fibre_lattice_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (D' : Datum H) (P' : D'.La →+ (Fin g → ℂ)) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (n : SABMap t Xo.univ.t (U.u i P)), IsPeriod (U.Di i) ty P → IsPeriod D' ty P' → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D' t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) (unitOn c)) → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ z, (e z).left ≫ n.φ = (U.ex i P (h z)).left) ∧ (∀ a, P (gam a) = h (P' a)) ∧ ∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a' := by
  intro E _ _ _ H D l Xo σ g ty U i P D' P' t e n hP hP' ⟨_, _, _, _, _, ha, hs, hk, hl, hh, hw⟩
  exact FibreMatch.fibrewise t Xo.univ.t D' (U.Di i) ty P' P hP' hP _ _ n (Category.id_comp _) e (U.ex i P) ha
    (U.ex_add i P hP) hs hk (U.ex_ker i P hP) hl (U.ex_lin i P hP) hw (U.ex_weil i P hP) hh
    (ExpUniqFamily.isHolTo_ex U i P hP) (U.ex_diff i P hP)

end GlobalTheory
