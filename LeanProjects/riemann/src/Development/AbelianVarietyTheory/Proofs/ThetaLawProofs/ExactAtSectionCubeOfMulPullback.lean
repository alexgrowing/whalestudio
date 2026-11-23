import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FirstCohomologyVanishesDescent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

noncomputable section
namespace GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish

theorem exactAt_of_trace {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (A B : GlobalTheory.Cube.{0} κ R)
    (φ : ∀ s, A.obj s →+ B.obj s) (T : ∀ s, B.obj s →+ B.obj s)
    (hφ : ∀ {s t : Finset κ} (h : s ⊆ t) x, φ t (Cube.res A h x) = Cube.res B h (φ s x))
    (hT : ∀ {s t : Finset κ} (h : s ⊆ t) x, T t (Cube.res B h x) = Cube.res B h (T s x))
    (inj : ∀ s, Function.Injective (φ s)) (n : ℕ) (hn : IsUnit (n : R))
    (himg : ∀ s y, ∃ x, φ s x = T s y) (htr : ∀ s x, T s (φ s x) = n • φ s x) (p : ℕ)
    (H : (cubeComplex B).ExactAt p) : (cubeComplex A).ExactAt p := by
  have dφ : ∀ q (x : Cube.Term A q), Cube.d B q (fun s => φ s.1 (x s)) = fun t => φ t.1 (Cube.d A q x t) :=
    fun q x => funext fun t => by
      simp only [Cube.d_apply, map_sum, map_zsmul, hφ]
  have dT : ∀ q (x : Cube.Term B q), Cube.d B q (fun s => T s.1 (x s)) = fun t => T t.1 (Cube.d B q x t) :=
    fun q x => funext fun t => by
      simp only [Cube.d_apply, map_sum, map_zsmul, hT]
  rcases p with _ | p
  · rw [cubeComplex_exactAt_zero_iff'] at H ⊢
    intro x y hxy
    have : (fun s => φ s.1 (x s) : Cube.Term B 0) = fun s => φ s.1 (y s) := H (by rw [dφ, dφ, hxy])
    exact funext fun s => inj _ (congrFun this s)
  · rw [cubeComplex_exactAt_succ_iff] at H ⊢
    intro x
    refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => hy ▸ Cube.d_d A p y⟩
    obtain ⟨y, hy⟩ := (H (fun s => φ s.1 (x s))).1 (by
      rw [dφ, hx]; exact funext fun t => map_zero _)
    choose z hz using fun s : {s : Finset κ // s.card = p} => himg s.1 (y s)
    have key : Cube.d A p z = (n : R) • x := funext fun t => inj _ (by
      have e := congrFun (dφ p z) t
      have e' := congrFun (dT p y) t
      simp only [hz] at e
      rw [← e, e', hy, htr, Pi.smul_apply, Nat.cast_smul_eq_nsmul, map_nsmul])
    obtain ⟨u, hu⟩ := hn.exists_left_inv
    exact ⟨u • z, by rw [map_smul, key, smul_smul, hu, one_smul]⟩

variable {X Y : Scheme.{0}} (f : Y ⟶ X) (M : LB X)

theorem le_deck {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) (j : (M.pull f).ι) :
    W' ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U j) := fun y hy =>
  ⟨e hy.1, mem_pull.2 (by
    have := mem_pull.1 hy.2
    rwa [← hτ] at this)⟩

def act {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W) :
    SecOn (M.pull f) W →+ SecOn (M.pull f) W' where
  toFun s := GlobalTheory.LB.mkSec (fun j => pb τ (le_deck f M hτ e j) (GlobalTheory.LB.coord s j)) fun i j => by
    have e₀ : W' ⊓ (M.pull f).U i ⊓ (M.pull f).U j ≤ τ ⁻¹ᵁ (W ⊓ (M.pull f).U i ⊓ (M.pull f).U j) :=
      le_deck f M hτ (le_deck f M hτ e i) j
    have h := congrArg (pb τ e₀) (GlobalTheory.LB.coord_mem s i j)
    have g₁ : ∀ (O : Y.Opens) (e : O ≤ (M.pull f).U i ⊓ (M.pull f).U j),
        rs Y e ((M.pull f).g i j).val = pb f (pre_pull M f (i PUnit.unit) (j PUnit.unit) e)
          (M.g (i PUnit.unit) (j PUnit.unit)).val :=
      fun O e => rs_pull_g M f (i PUnit.unit) (j PUnit.unit) (W := O) e
    exact (rs_pb τ _ _ _).trans ((pb_rs τ e₀ _ _).symm.trans (h.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ((congrArg (pb τ e₀) (g₁ _ _)).trans ((pb_pb τ f _ e₀ _).trans
        ((pb_congr hτ _ _).trans (g₁ _ _).symm))) ((pb_rs τ e₀ _ _).trans (rs_pb τ _ _ _).symm)))))
  map_zero' := GlobalTheory.LB.sec_ext fun j => map_zero (pb τ _)
  map_add' s t := GlobalTheory.LB.sec_ext fun j => map_add (pb τ _) _ _

theorem coord_act {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W' ≤ τ ⁻¹ᵁ W)
    (s : SecOn (M.pull f) W) (j : (M.pull f).ι) :
    GlobalTheory.LB.coord (act f M hτ e s) j = pb τ (le_deck f M hτ e j) (GlobalTheory.LB.coord s j) := rfl

theorem act_restrict {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {W W' : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W) (e' : W' ≤ τ ⁻¹ᵁ W')
    (h : W' ≤ W) (s : SecOn (M.pull f) W) :
    act f M hτ e' (SecOn.restrict _ h s) = SecOn.restrict _ h (act f M hτ e s) :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, SecOn.coord_restrict, SecOn.coord_restrict, coord_act, pb_rs, rs_pb]

theorem act_act {τ σ ρ : Y ⟶ Y} (hτ : τ ≫ f = f) (hσ : σ ≫ f = f) (hρ : ρ ≫ f = f) (H : τ ≫ σ = ρ)
    {W : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W) (e' : W ≤ σ ⁻¹ᵁ W) (e'' : W ≤ ρ ⁻¹ᵁ W) (s : SecOn (M.pull f) W) :
    act f M hτ e (act f M hσ e' s) = act f M hρ e'' s :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, coord_act, coord_act, pb_pb, pb_congr H]

theorem coord_pullLE {V : X.Opens} {W : Y.Opens} (e : W ≤ f ⁻¹ᵁ V) (s : SecOn M V) (j : (M.pull f).ι) :
    GlobalTheory.LB.coord (SecOn.pullLE M f V W e s) j =
      pb f ((inf_le_inf_right _ e).trans (GlobalTheory.LB.pull_inf_le f V j)) (GlobalTheory.LB.coord s (j PUnit.unit)) :=
  SecOn.coord_pullLE f e s j

theorem act_pullLE {τ : Y ⟶ Y} (hτ : τ ≫ f = f) {V : X.Opens} {W : Y.Opens} (e : W ≤ τ ⁻¹ᵁ W)
    (h : W ≤ f ⁻¹ᵁ V) (s : SecOn M V) :
    act f M hτ e (SecOn.pullLE M f V W h s) = SecOn.pullLE M f V W h s :=
  GlobalTheory.LB.sec_ext fun j => by
    rw [coord_act, coord_pullLE, pb_pb, pb_congr hτ]

variable {G : Type} (τ : G → (Y ⟶ Y)) (hτ : ∀ y, τ y ≫ f = f)
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
include hτ hgal

omit hτ in

theorem exists_fun (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) (s : Γ(Y, W))
    (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), pb (τ y) e s = s) : ∃! g : Γ(X, U), pb f e g = s := by
  obtain rfl := le_antisymm e e'
  simpa only [app_eq_pb] using hgal U s hs

theorem pb_injective (U : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : f ⁻¹ᵁ U ≤ W) :
    Function.Injective (pb f e) := fun a _ hab =>
  (exists_fun f τ hgal U W e e' (pb f e a) (fun y _ => by rw [pb_pb, pb_congr (hτ y)])).unique rfl hab.symm

theorem pullLE_injective (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W) :
    Function.Injective (SecOn.pullLE M f V W e) := fun a b hab => GlobalTheory.LB.sec_ext fun i => by
  have h := (coord_pullLE f M e a (fun _ => i)).symm.trans
    ((congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) hab).trans (coord_pullLE f M e b (fun _ => i)))
  exact pb_injective f τ hτ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
    (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) h

theorem exists_pullLE (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W)
    (s : SecOn (M.pull f) W) (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), act f M (hτ y) e s = s) :
    ∃ x, SecOn.pullLE M f V W e x = s := by
  have inv : ∀ y, W ≤ τ y ⁻¹ᵁ W := fun y => by
    obtain rfl := le_antisymm e e'
    rw [← Scheme.Hom.comp_preimage, hτ]
  have H : ∀ i : M.ι, ∃ g : Γ(X, V ⊓ M.U i),
      pb f ((inf_le_inf_right _ e).trans (GlobalTheory.LB.pull_inf_le f V (fun _ => i))) g =
        GlobalTheory.LB.coord s (fun _ => i) := fun i =>
    (exists_fun f τ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
      (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) _ fun y _ =>
      congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) (hs y (inv y))).exists
  choose g hg using H
  refine ⟨GlobalTheory.LB.mkSec g fun i j => ?_, GlobalTheory.LB.sec_ext fun j => (coord_pullLE f M e _ j).trans (hg _)⟩
  have e₀ : W ⊓ (M.pull f).U (fun _ => i) ⊓ (M.pull f).U (fun _ => j) ≤ f ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
    fun y hy => ⟨⟨e hy.1.1, mem_pull.1 hy.1.2⟩, mem_pull.1 hy.2⟩
  apply pb_injective f τ hτ hgal (V ⊓ M.U i ⊓ M.U j) _ e₀
    (fun y hy => ⟨⟨e' hy.1.1, mem_pull.2 hy.1.2⟩, mem_pull.2 hy.2⟩)
  have h := GlobalTheory.LB.coord_mem s (fun _ => i) (fun _ => j)
  rw [← hg, ← hg] at h
  exact (pb_rs f e₀ _ _).trans ((rs_pb f _ _ _).symm.trans (h.trans ((congrArg₂ (· * ·)
    ((rs_pull_g M f i j _).trans (pb_rs f e₀ _ _).symm)
    ((rs_pb f _ _ _).trans (pb_rs f e₀ _ _).symm)).trans (map_mul _ _ _).symm)))

theorem exactAt_of_pull [Group G] [Fintype G] (hmul : ∀ y z, τ y ≫ τ z = τ (y * z))
    {R : Type} [CommRing R] (a : X ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ Spec (CommRingCat.of R))
    (hu : IsUnit ((Fintype.card G : ℕ) : R)) {I : Type} [LinearOrder I] (D : I → X.Opens) (p : ℕ)
    (H : (cubeComplex (secCube b (M.pull f) (fun i => f ⁻¹ᵁ D i))).ExactAt p) :
    (cubeComplex (secCube a M D)).ExactAt p := by
  have inv : ∀ y (s : Finset I), (⨅ i ∈ s, f ⁻¹ᵁ D i) ≤ τ y ⁻¹ᵁ (⨅ i ∈ s, f ⁻¹ᵁ D i) := fun y s => by
    rw [← preimage_biInf, ← Scheme.Hom.comp_preimage, hτ]
  let φ : ∀ s : Finset I, SecOn M (⨅ i ∈ s, D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => (SecOn.pullLE M f _ _ (preimage_biInf D f s).ge).toAddMonoidHom
  let T : ∀ s : Finset I, SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => ∑ y, act f M (hτ y) (inv y s)
  have hT : ∀ s x, T s x = ∑ y, act f M (hτ y) (inv y s) x := fun s x => AddMonoidHom.finset_sum_apply _ _ _
  refine exactAt_of_trace _ _ φ T (fun {s t} h x => ?_) (fun {s t} h x => ?_)
    (fun s => pullLE_injective f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le) _ hu (fun s y => ?_)
    (fun s x => ?_) p H
  · exact (SecOn.pullLE_restrict f (iInf_le_iInf_of_subset D h) (preimage_biInf D f t).ge _).trans
      (SecOn.restrict_pullLE f (preimage_biInf D f s).ge (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) _).symm
  · change T t (SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) x) =
      SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) (T s x)
    rw [hT t, hT s x, map_sum]
    exact Finset.sum_congr rfl fun y _ => act_restrict f M (hτ y) (inv y s) (inv y t) _ x
  · refine exists_pullLE f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le (T s y)
      fun z e => ?_
    rw [hT s y, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun w =>
      act_act f M (hτ z) (hτ w) (hτ (z * w)) (hmul z w) e (inv w s) (inv (z * w) s) y
  · refine (hT s _).trans ((Finset.sum_congr rfl fun y _ =>
      act_pullLE f M (hτ y) (inv y s) (preimage_biInf D f s).ge x).trans ?_)
    rw [Finset.sum_const, Finset.card_univ]
    rfl

end GlobalTheory.TraceDescent

theorem GlobalTheory.exactAt_secCube_of_mul_pull : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (m : ℕ) (N : LB P.A.left) (I : Type) [LinearOrder I] [Fintype I] (D : I → P.A.left.Opens) (p : ℕ), (m : K) ≠ 0 → N.IsLB → (cubeComplex (secCube P.A.hom (N.pull (Out.mulA P.A m).left) (fun i => (Out.mulA P.A m).left ⁻¹ᵁ D i))).ExactAt p → (cubeComplex (secCube P.A.hom N D)).ExactAt p := by
  intro L K _ _ P m N I _ _ D p hm _ H
  classical
  haveI := P.isAb.comm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr fun h => hm (by rw [h, Nat.cast_zero])
  let G : Subgroup (𝟙_ (Over (Sp K)) ⟶ P.A) := (powMonoidHom m).ker
  have hc : Nat.card G = m ^ (2 * P.g) := (L.mulN _ P m hm1).2.2.2.2 K (𝟙 _) hm
  haveI : Finite G := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ (by omega))
  haveI : Fintype G := Fintype.ofFinite G
  have hgal := GlobalTheory.torsion_invariant_descends (fun S _ P n hn =>
    have h := L.mulN S P n hn
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) K P m hm
  refine GlobalTheory.TraceDescent.exactAt_of_pull (Out.mulA P.A m).left N (G := G)
    (fun y => ((toUnit P.A ≫ y.1) * 𝟙 P.A).left) (fun y => ?_)
    (fun U f hf => hgal U f fun y hy e => hf ⟨y, hy⟩ e) (fun y z => ?_) _ _ ?_ D p H
  · have hy : y.1 ^ m = 1 := y.2
    rw [← Over.comp_left, Out.mulA, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.comp_pow, hy,
      MonObj.comp_one, _root_.one_mul]
  · rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
      Subgroup.coe_mul, MonObj.comp_mul, ← _root_.mul_assoc, _root_.mul_comm (toUnit P.A ≫ z.1)]
  · rw [← Nat.card_eq_fintype_card, hc, Nat.cast_pow]
    exact (IsUnit.mk0 _ hm).pow _
