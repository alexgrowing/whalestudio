import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsInCoordinatesFromBasePullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToUnitTKLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastFurther

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTautData

def unitK {R : Type} [CommRing R] [IsDomain R] (t : R) (ht : t ≠ 0) : (FractionRing R)ˣ :=
  Units.mk0 (algebraMap R (FractionRing R) t) ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 ht)

def coordsK {R : Type} [CommRing R] [IsDomain R] {m N : ℕ} (t : Fin m → R) (ht : ∀ i, t i ≠ 0) (u : Fin N → Rˣ) :
    Fin (m + N) → (FractionRing R)ˣ := fun k =>
  Sum.elim (fun i => unitK (t i) (ht i)) (fun j => Units.map (algebraMap R (FractionRing R)).toMonoidHom (u j))
    (finSumFinEquiv.symm k)

def forms {X : Type} [AddCommGroup X] {m N : ℕ} (M : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X)
    (ε : Fin N → LinearMap.BilinForm ℤ X) : Fin (m + N) → LinearMap.BilinForm ℤ X := fun k =>
  (M : ℤ) • Sum.elim δ ε (finSumFinEquiv.symm k)

def scaleFn {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] {U : Type} [CommGroup U] {n : ℕ}
    (v : Fin n → U) (w0 : O) (β : Fin n → LinearMap.BilinForm ℤ X) (y : X) : U :=
  ∏ k, v k ^ β k y (w0 • y)

abbrev taut {W R : Type} [CommRing W] [IsDomain W] [CommRing R] [IsDomain R] {D₀ : DegPre W} {O : Type} [CommRing O]
    [Module O D₀.X] (D' : DegPre R) [Module O D'.X] (e : D'.X ≃ₗ[O] D₀.X) (w0 : O) {m N : ℕ} (t : Fin m → R)
    (ht : ∀ i, t i ≠ 0) (u : Fin N → Rˣ) (M : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ D₀.X)
    (ε : Fin N → LinearMap.BilinForm ℤ D₀.X) : DegPre R :=
  GlobalTheory.PolDeg.rescale D' (scaleFn (coordsK t ht u) w0
    (forms M (fun i => GlobalTheory.PolFan.pull e.toLinearMap (δ i)) (fun j => GlobalTheory.PolFan.pull e.toLinearMap (ε j))))

instance {W R : Type} [CommRing W] [IsDomain W] [CommRing R] [IsDomain R] {D₀ : DegPre W} {O : Type} [CommRing O]
    [Module O D₀.X] (D' : DegPre R) [Module O D'.X] (e : D'.X ≃ₗ[O] D₀.X) (w0 : O) {m N : ℕ} (t : Fin m → R)
    (ht : ∀ i, t i ≠ 0) (u : Fin N → Rˣ) (M : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ D₀.X)
    (ε : Fin N → LinearMap.BilinForm ℤ D₀.X) : Module O (taut D' e w0 t ht u M δ ε).X := ‹Module O D'.X›

end GlobalTheory.UTautData

namespace GlobalTheory.UTautData

@[reducible] def modOf {O X Y : Type} [Ring O] [AddCommGroup X] [AddCommGroup Y] [Module O Y] (f : X ≃+ Y) :
    Module O X where
  smul a x := f.symm (a • f x)
  one_smul x := by show f.symm ((1 : O) • f x) = x; simp
  mul_smul a b x := by show f.symm ((a * b) • f x) = f.symm (a • f (f.symm (b • f x))); simp [mul_smul]
  smul_zero a := by show f.symm (a • f 0) = 0; simp
  smul_add a x y := by show f.symm (a • f (x + y)) = f.symm (a • f x) + f.symm (a • f y); simp
  add_smul a b x := by show f.symm ((a + b) • f x) = f.symm (a • f x) + f.symm (b • f x); simp [add_smul]
  zero_smul x := by show f.symm ((0 : O) • f x) = 0; simp

theorem diag_eq_two_mul {O : Type} [CommRing O] [StarRing O] {X : Type} [AddCommGroup X] [Module O X]
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ GlobalTheory.PolFan.balForms (star : O → O) X) {w0 : O}
    (hw : w0 + star w0 = 1) (y : X) : β y y = 2 * β y (w0 • y) := by
  have h1 : β y y = β y (w0 • y) + β y (star w0 • y) := by
    rw [← map_add, ← add_smul, hw, one_smul]
  have h2 : β y (star w0 • y) = β y (w0 • y) := by
    rw [← hβ.2 w0 y y, hβ.1]
  rw [h1, h2]; ring

theorem finite_sublevel {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (β : LinearMap.BilinForm ℤ X) (hs : ∀ y z, β y z = β z y) (hp : ∀ y, y ≠ 0 → 0 < β y y) (C : ℤ) :
    {y | β y y ≤ C}.Finite := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hnn : ∀ y, 0 ≤ β y y := fun y => by
    by_cases hy : y = 0
    · simp [hy]
    · exact (hp y hy).le
  let F : X → Module.Free.ChooseBasisIndex ℤ X → ℤ := fun y j => β (b j) y
  have hinj : Function.Injective F := by
    intro x y hxy
    by_contra hne
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h0 : ∀ j, β (b j) (x - y) = 0 := fun j => by
      rw [map_sub, sub_eq_zero]; exact congrFun hxy j
    have h1 : β (x - y) (x - y) = 0 := by
      generalize x - y = z at h0
      have e := congrArg (fun w => β w z) (b.sum_repr z)
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h0, smul_zero,
        Finset.sum_const_zero] at e
      exact e.symm
    exact (hp _ hz).ne' h1
  refine Set.Finite.of_finite_image ?_ hinj.injOn
  refine (Set.Finite.pi' fun j => Set.finite_Icc (-(β (b j) (b j) + C)) (β (b j) (b j) + C)).subset ?_
  rintro _ ⟨x, hx, rfl⟩ j
  have hx' : β x x ≤ C := hx
  have e1 := hnn (b j + x)
  have e2 := hnn (b j - x)
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, hs x (b j)] at e1 e2
  simp only [Set.mem_Icc, F]
  constructor <;> nlinarith [hnn x]

end GlobalTheory.UTautData

namespace GlobalTheory.UTautData

theorem twist_keeps {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O D.X] (oa : D.OAct O) (w0 : O) (hw : w0 + star w0 = 1) (he : D.PsiEven) (hb : D.TauBimult)
    (hW : TraceFormTwistIso D oa w0) (T : D.X → D.X → (FractionRing R)ˣ) (hs : GlobalTheory.TauTwist.IsScalarForm O T)
    (g : D.X → (FractionRing R)ˣ) (hg : g = fun y => T y (w0 • y)) :
    letI : Module O (GlobalTheory.PolDeg.rescale D g).X := ‹Module O D.X›
    (GlobalTheory.PolDeg.rescale D g).PsiEven ∧ (GlobalTheory.PolDeg.rescale D g).TauBimult ∧
      ∃ oa1 : (GlobalTheory.PolDeg.rescale D g).OAct O, oa1.onB = oa.onB ∧ TraceFormTwistIso (GlobalTheory.PolDeg.rescale D g) oa1 w0 := by
  subst hg
  exact ⟨GlobalTheory.TauTwist.psiEven_twist hs w0 he, GlobalTheory.TauTwist.tauBimult_twist hw hs hb,
    GlobalTheory.TauTwist.twistAct hw hs oa, rfl, GlobalTheory.TauTwist.psi_weight_zero_twist hw hs hW⟩

end GlobalTheory.UTautData

namespace GlobalTheory.UTautData

theorem tauIn_twist {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O D.X] (w0 : O) (hw : w0 + star w0 = 1) (T : D.X → D.X → (FractionRing R)ˣ)
    (hs : GlobalTheory.TauTwist.IsScalarForm O T) (g : D.X → (FractionRing R)ˣ) (hg : g = fun y => T y (w0 • y))
    (τ₁ : GlobalTheory.UChart.Gens D) (hτ : ∀ a b, (τ₁ a b).IsGen ∧ ∀ z J, Good D.P.L z J →
      val (D.tau a b) (𝟙 _) z J = val (τ₁ a b) (toUnit (TK R)).left z J)
    {n : ℕ} (s : Fin n → R) (β : Fin n → LinearMap.BilinForm ℤ D.X)
    (hT : ∀ a b, (T a b : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s k) ^ β k a b) :
    GlobalTheory.UChart.TauIn (GlobalTheory.PolDeg.rescale D g) τ₁ s β := by
  subst hg
  intro a b
  obtain ⟨hgen, hv⟩ := hτ a b
  refine ⟨hgen, T a b, hT a b, fun z J hJ => ?_⟩
  refine (GlobalTheory.TauTwist.val_tau_twist hw hs a b (𝟙 _) hJ).trans ?_
  rw [hv z J hJ]
  rfl

theorem scaleFn_coe {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] {X : Type} [AddCommGroup X]
    [Module O X] {m N : ℕ} (t : Fin m → R) (ht : ∀ i, t i ≠ 0) (u : Fin N → Rˣ) (M : ℕ) (w0 : O)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (ε : Fin N → LinearMap.BilinForm ℤ X) (y : X) :
    ((scaleFn (coordsK t ht u) w0 (forms M δ ε) y : (FractionRing R)ˣ) : FractionRing R) =
      (∏ i, algebraMap R (FractionRing R) (t i) ^ ((M : ℤ) * δ i y (w0 • y))) *
        ∏ j, algebraMap R (FractionRing R) (u j : R) ^ ((M : ℤ) * ε j y (w0 • y)) := by
  simp only [scaleFn, Fin.prod_univ_add, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, coordsK, forms,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr, unitK,
    Units.val_mk0, LinearMap.smul_apply, smul_eq_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]

end GlobalTheory.UTautData

namespace GlobalTheory.UTautData

theorem gens_of_psiUnitOn {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (hb : D.TauBimult)
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ τ₀ : GlobalTheory.UChart.Gens D, ∀ a b, (τ₀ a b).IsGen ∧ ∀ z J, Good D.P.L z J →
      val (D.tau a b) (𝟙 _) z J = val (τ₀ a b) (toUnit (TK R)).left z J :=
  GlobalTheory.DDataGens.main R D hb hU

open GlobalTheory.UChart in

theorem fromBase_self {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : Gens Q) (h : ∀ a b, (τ₀ a b).IsGen) :
    FromBase Q τ₀ (RingHom.id V) := by
  have hs : spMap (RingHom.id V) = 𝟙 (Sp V) := Spec.map_id _
  refine ⟨Q.P.A, inferInstance, Q.P.L, cpt Q, τ₀, 𝟙 _, GlobalTheory.PolDeg.Wit.idPull _, Q.P.isAb, Q.P.isLB, ?_,
    GlobalTheory.PolDeg.Wit.idPull_isGen Q.P.isLB, fun a => ?_, h, fun a b z J J₀ hJ hJ₀ => ?_⟩
  · rw [hs]; exact GlobalTheory.PolDeg.Wit.grpPullback_id Q.P.A
  · rw [hs]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [hs]
    refine (gen_trans (h a b) (𝟙 _) z (hJ.mem _ _) (hJ₀.mem _ _)).trans (congrArg (· * _) ?_)
    have e : ∀ q : Sp V ⟶ Q.P.A.left, gm q z _ ((GlobalTheory.PolDeg.Wit.idPull Q.P.L).s (fun _ => J₀ (q ≫ 𝟙 _), J q)) =
        (gm q z _ (Q.P.L.g (J q) (J₀ q)))⁻¹ := fun q => by
      have h0 : q z ∈ Q.P.L.U (J₀ (q ≫ 𝟙 _)) := by rw [Category.comp_id]; exact hJ₀ q
      refine (GlobalTheory.PolDeg.Wit.gw_idPull Q.P.L q z _ _ h0 (hJ q)).trans ?_
      rw [Category.comp_id]
      exact eq_inv_of_mul_eq_one_left ((gm_cocycle Q.P.isLB q z (hJ₀ q) (hJ q) (hJ₀ q)).trans
        (gm_self Q.P.isLB q z (hJ₀ q)))
    rw [e, e, e, e]
    let F : (Sp V ⟶ Q.P.A.left) → ((Sp V).presheaf.stalk z)ˣ := fun q => gm q z _ (Q.P.L.g (J q) (J₀ q))
    show ∏ k : Fin 4, F (𝟙 _ ≫ ![cpt Q (a + b), cpt Q a, cpt Q b, cpt Q 0] k) ^ (![-1, 1, 1, -1] : Fin 4 → ℤ) k =
      (F _)⁻¹ * ((F _)⁻¹)⁻¹ * ((F _)⁻¹)⁻¹ * (F _)⁻¹
    simp only [Category.id_comp, Fin.prod_univ_four]
    simp

theorem gens_fromBase {W R : Type} [CommRing W] [IsDomain W] [CommRing R] [IsDomain R] (ρ : W →+* R)
    (hρ : Function.Injective ρ) (D₀ : DegPre W) (D' : DegPre R) (hD : IsPullDeg ρ D₀ D') (hb : D₀.TauBimult)
    (hU : ∀ y, PsiUnitOn D₀ y Set.univ) :
    ∃ τ₀ : GlobalTheory.UChart.Gens D', (∀ a b, (τ₀ a b).IsGen ∧ ∀ z J, Good D'.P.L z J →
      val (D'.tau a b) (𝟙 _) z J = val (τ₀ a b) (toUnit (TK R)).left z J) ∧ GlobalTheory.UChart.FromBase D' τ₀ ρ := by
  obtain ⟨σ, hσ⟩ := gens_of_psiUnitOn D₀ hb hU
  have h1 : ∀ (V : Type) [CommRing V] [IsDomain V] (z : (TK V).left),
      gm (𝟙 (TK V).left) z ⊤ (unitOn (1 : (FractionRing V)ˣ)) = 1 := fun V _ _ z => by
    have e : unitOn (1 : (FractionRing V)ˣ) = 1 := Units.ext (map_one _)
    rw [e]
    first | exact map_one _ | simp [gm]
  obtain ⟨τ₁, hT, hF⟩ := GlobalTheory.USep.tauIn_fromBase_pull W R ρ hρ D₀ D' hD σ 0 Fin.elim0 Fin.elim0 Fin.elim0
    (fun k => k.elim0) (fun a b => ⟨(hσ a b).1, 1, by simp, fun z J hJ => by
      rw [h1, _root_.one_mul]; exact (hσ a b).2 z J hJ⟩) W (RingHom.id W) (fromBase_self D₀ σ fun a b => (hσ a b).1)
  refine ⟨τ₁, fun a b => ?_, by simpa using hF⟩
  obtain ⟨hg, k, hk, hv⟩ := hT a b
  obtain rfl : k = 1 := Units.ext (by simpa using hk)
  refine ⟨hg, fun z J hJ => ?_⟩
  rw [hv z J hJ, h1, _root_.one_mul]

theorem psiCoord_rescale {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    (q : D.X → (FractionRing R)ˣ) (y : D.X) (hU : PsiUnitOn D y Set.univ) (s : R)
    (hq : (q y : FractionRing R) = algebraMap R (FractionRing R) s) :
    ∃ u : Rˣ, Formalism.L2.Pj.PsiCoord (GlobalTheory.PolDeg.rescale D q) y (u * s) :=
  GlobalTheory.PsiCoordRescaleLocal.main R D q y hU s hq

end GlobalTheory.UTautData

namespace GlobalTheory.UTautData

theorem main (W R : Type) [CommRing W] [IsDomain W] [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R)
    (ρ : W →+* R) (hρ : Function.Injective ρ) (D₀ : DegPre W) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (oa : D₀.OAct O) (w0 : O) (hw : w0 + star w0 = 1) (he : D₀.PsiEven) (hb : D₀.TauBimult)
    (hW0 : TraceFormTwistIso D₀ oa w0) (hU : ∀ y, PsiUnitOn D₀ y Set.univ) {m N : ℕ} (t : Fin m → R) (ht : ∀ i, t i ≠ 0)
    (htI : ∀ i, t i ∈ I) (u : Fin N → Rˣ) (M : ℕ) (hM : 0 < M) (δ : Fin m → LinearMap.BilinForm ℤ D₀.X)
    (ε : Fin N → LinearMap.BilinForm ℤ D₀.X) (hδ : ∀ i, δ i ∈ GlobalTheory.PolFan.balForms (star : O → O) D₀.X)
    (hδ0 : ∀ i y, 0 ≤ δ i y y) (hε : ∀ j, ε j ∈ GlobalTheory.PolFan.balForms (star : O → O) D₀.X)
    (hdef : ∀ y, y ≠ 0 → 0 < ∑ i, δ i y y) (hne : ∃ i, δ i ≠ 0) :
    ∃ (D' : DegPre R) (hD : IsPullDeg ρ D₀ D') (_ : Module O D'.X) (e : D'.X ≃ₗ[O] D₀.X),
      (∀ y, e y = hD.xe y) ∧
      (taut D' e w0 t ht u M δ ε).PsiEven ∧ (taut D' e w0 t ht u M δ ε).TauBimult ∧
      (∀ χ, χ ≠ 0 → (taut D' e w0 t ht u M δ ε).PsiIn χ I) ∧
      (∀ n : ℕ, {χ | ¬ (taut D' e w0 t ht u M δ ε).PsiIn χ (I ^ n)}.Finite) ∧
      (∃ oa1 : (taut D' e w0 t ht u M δ ε).OAct O,
        (let p : D'.P.A.left ⟶ D₀.P.A.left := GlobalTheory.PsiEvenPull.proj hD
          ∀ a, (oa1.onB.act a).left ≫ p = p ≫ (oa.onB.act a).left) ∧
        TraceFormTwistIso (taut D' e w0 t ht u M δ ε) oa1 w0) ∧
      GlobalTheory.Toroidal.IsMonomial (taut D' e w0 t ht u M δ ε) t (fun i => (M : ℤ) • GlobalTheory.PolFan.pull e.toLinearMap (δ i)) ∧
      (∃ τ₀ : GlobalTheory.UChart.Gens (taut D' e w0 t ht u M δ ε),
        (∀ a b z J, Good D'.P.L z J → val (D'.tau a b) (𝟙 _) z J = val (τ₀ a b) (toUnit (TK R)).left z J) ∧
        GlobalTheory.UChart.FromBase (taut D' e w0 t ht u M δ ε) τ₀ ρ ∧
        GlobalTheory.UChart.TauIn (taut D' e w0 t ht u M δ ε) τ₀ (fun k => Sum.elim t (fun j => (u j : R)) (finSumFinEquiv.symm k))
          (forms M (fun i => GlobalTheory.PolFan.pull e.toLinearMap (δ i)) (fun j => GlobalTheory.PolFan.pull e.toLinearMap (ε j)))) ∧
      Nontrivial (taut D' e w0 t ht u M δ ε).X ∧
      ∃ D1 : DegData R I, D1.toPre = taut D' e w0 t ht u M δ ε := by
  classical
  obtain ⟨hL, -⟩ := GlobalTheory.allSixLaws
  have hG : GlobalFnsSt := hL.globalFns
  obtain ⟨D', hD, -, -⟩ := GlobalTheory.StrictPull.exists_isPullDeg_strict hL W R ρ D₀ ⊤
    (GlobalTheory.ArcPull.nonempty_psiOn_top D₀ hU) trivial
  letI iM : Module O D'.X := modOf hD.xe
  have hx : ∀ (a : O) y, hD.xe (a • y) = a • hD.xe y := fun a y => hD.xe.apply_symm_apply _
  let e : D'.X ≃ₗ[O] D₀.X := { hD.xe with map_smul' := hx }
  obtain ⟨oa', ho⟩ := GlobalTheory.ArcPull.exists_oAct hD hG hρ oa hx
  have hW' : TraceFormTwistIso D' oa' w0 := GlobalTheory.ArcPull.traceFormTwistIso_of_pullback hD hρ hx ho hW0
  have he' : D'.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull hG W R ρ D₀ D' hD he
  have hb' : D'.TauBimult := GlobalTheory.TauPull.tauBimult_pull hG hD hb
  have hU' : ∀ y, PsiUnitOn D' y Set.univ := fun y => GlobalTheory.ArcPull.psiUnitOn_pull hD hρ y (hU _)
  set δ' : Fin m → LinearMap.BilinForm ℤ D'.X := fun i => GlobalTheory.PolFan.pull e.toLinearMap (δ i) with hδ'
  set ε' : Fin N → LinearMap.BilinForm ℤ D'.X := fun j => GlobalTheory.PolFan.pull e.toLinearMap (ε j) with hε'
  set β := forms M δ' ε' with hβdef
  set v := coordsK t ht u with hv
  have hβ : ∀ k, β k ∈ GlobalTheory.PolFan.balForms (star : O → O) D'.X := fun k => by
    refine Submodule.smul_mem _ _ ?_
    rcases finSumFinEquiv.symm k with i | j
    · exact GlobalTheory.PolFan.pull_mem _ (hδ i)
    · exact GlobalTheory.PolFan.pull_mem _ (hε j)
  have hs : GlobalTheory.TauTwist.IsScalarForm O (fun a b : D'.X => ∏ k, v k ^ β k a b) :=
    ⟨fun y x x' => by simp only [map_add, zpow_add, Finset.prod_mul_distrib],
      fun y x => by simp only [(hβ _).1 y x],
      fun a y x => by simp only [(hβ _).2 a y x]⟩
  refine ⟨D', hD, iM, e, fun y => rfl, ?_⟩
  obtain ⟨hPE, hTB, oa1, hoa1, hPW⟩ := twist_keeps D' oa' w0 hw he' hb' hW' (fun a b => ∏ k, v k ^ β k a b) hs
    (scaleFn v w0 β) rfl

  have hδ'b : ∀ i, δ' i ∈ GlobalTheory.PolFan.balForms (star : O → O) D'.X := fun i => GlobalTheory.PolFan.pull_mem _ (hδ i)
  have hδ'0 : ∀ i y, 0 ≤ δ' i y (w0 • y) := fun i y => by
    have h := diag_eq_two_mul (hδ'b i) hw y
    have h0 : 0 ≤ δ' i y y := hδ0 i (e y)
    omega

  have hmono : GlobalTheory.Toroidal.IsMonomial (taut D' e w0 t ht u M δ ε) t (fun i => (M : ℤ) • δ' i) := by
    intro (y : D'.X)
    let n : Fin m → ℕ := fun i => ((M : ℤ) * δ' i y (w0 • y)).toNat
    have hn : ∀ i, (((n i : ℕ) : ℤ)) = (M : ℤ) * δ' i y (w0 • y) := fun i =>
      Int.toNat_of_nonneg (mul_nonneg (Int.natCast_nonneg M) (hδ'0 i y))
    let w : Rˣ := ∏ j, u j ^ ((M : ℤ) * ε' j y (w0 • y))
    have hq : ((scaleFn v w0 β y : (FractionRing R)ˣ) : FractionRing R) =
        algebraMap R (FractionRing R) ((w : R) * ∏ i, t i ^ n i) := by
      rw [hv, hβdef]
      refine (scaleFn_coe t ht u M w0 δ' ε' y).trans ?_
      rw [map_mul, mul_comm]
      congr 1
      · simp only [w, Units.coe_prod]
        rw [map_prod]
        refine Finset.prod_congr rfl fun j _ => ?_
        have h := congrArg Units.val (map_zpow (Units.map (algebraMap R (FractionRing R)).toMonoidHom) (u j)
          ((M : ℤ) * ε' j y (w0 • y)))
        rw [Units.val_zpow_eq_zpow_val] at h
        rw [Units.coe_map, Units.coe_map] at h
        exact h.symm
      · rw [map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← hn i, zpow_natCast, map_pow]
    obtain ⟨u', hu'⟩ := psiCoord_rescale D' (scaleFn v w0 β) y (hU' y) _ hq
    refine ⟨u' * w, n, fun i => ?_, ?_⟩
    · show ((M : ℤ) • δ' i) y y = 2 * ((n i : ℕ) : ℤ)
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, hn i, diag_eq_two_mul (hδ'b i) hw y]
      ring
    · rw [Units.val_mul, _root_.mul_assoc]
      exact hu'

  have hpos' : ∀ χ : D'.X, χ ≠ 0 → 0 < ∑ i, δ' i χ χ := fun χ hχ =>
    hdef (e χ) ((LinearEquiv.map_ne_zero_iff e).2 hχ)
  have hsm : ∀ i (y : D'.X), ((M : ℤ) • δ' i) y y = (M : ℤ) * δ' i y y := fun i y => rfl
  have hPI : ∀ χ : D'.X, χ ≠ 0 → (taut D' e w0 t ht u M δ ε).PsiIn χ I := fun χ hχ => by
    obtain ⟨w, n, hn, hc⟩ := hmono χ
    rw [GlobalTheory.PeriodFormEdge.psiIn_iff hc]
    obtain ⟨i, hi⟩ : ∃ i, 0 < δ' i χ χ := by
      by_contra h
      push_neg at h
      have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => h i
      linarith [hpos' χ hχ]
    have hni : 0 < n i := by
      have h1 : (M : ℤ) * δ' i χ χ = 2 * (n i : ℤ) := (hsm i χ).symm.trans (hn i)
      have h3 : (1 : ℤ) ≤ M := by exact_mod_cast hM
      have : (0 : ℤ) < n i := by nlinarith
      exact_mod_cast this
    refine Ideal.mul_mem_left _ _ ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (htI i) _ hni)
  have hfin : ∀ n : ℕ, {χ | ¬ (taut D' e w0 t ht u M δ ε).PsiIn χ (I ^ n)}.Finite := fun n => by
    let B : LinearMap.BilinForm ℤ D'.X := ∑ i, δ' i
    have hB : ∀ y z, B y z = ∑ i, δ' i y z := fun y z => by simp [B, LinearMap.sum_apply]
    refine (finite_sublevel B (fun y z => by rw [hB, hB]; exact Finset.sum_congr rfl fun i _ => (hδ'b i).1 y z)
      (fun y hy => by rw [hB]; exact hpos' y hy) (2 * n)).subset ?_
    intro χ hχ
    obtain ⟨w, k, hk, hc⟩ := hmono χ
    have hχ' : ¬ (w : R) * ∏ i, t i ^ k i ∈ I ^ n := fun h => hχ ((GlobalTheory.PeriodFormEdge.psiIn_iff hc _).2 h)
    show B χ χ ≤ 2 * (n : ℤ)
    by_contra hlt
    push_neg at hlt
    apply hχ'
    refine Ideal.mul_mem_left _ _ ?_
    have h1 : ∀ i, (M : ℤ) * δ' i χ χ = 2 * (k i : ℤ) := fun i => (hsm i χ).symm.trans (hk i)
    have h2 : (M : ℤ) * ∑ i, δ' i χ χ = 2 * ((∑ i, k i : ℕ) : ℤ) := by
      rw [Finset.mul_sum, Nat.cast_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => h1 i
    rw [hB] at hlt
    have h3 : (1 : ℤ) ≤ M := by exact_mod_cast hM
    have hsum : n ≤ ∑ i, k i := by
      have : (n : ℤ) ≤ ((∑ i, k i : ℕ) : ℤ) := by nlinarith
      exact_mod_cast this
    have hprod : ∏ i, t i ^ k i ∈ I ^ (∑ i, k i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (htI i) _
    exact Ideal.pow_le_pow_right hsum hprod

  obtain ⟨τ₁, hτ₁, hFB⟩ := gens_fromBase ρ hρ D₀ D' hD hb hU
  have hTI := tauIn_twist D' w0 hw (fun a b => ∏ k, v k ^ β k a b) hs (scaleFn v w0 β) rfl τ₁ hτ₁
    (fun k => Sum.elim t (fun j => (u j : R)) (finSumFinEquiv.symm k)) β (fun a b => by
      simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val]
      refine Finset.prod_congr rfl fun k _ => ?_
      congr 1
      simp only [hv, coordsK]
      rcases finSumFinEquiv.symm k with i | j
      · simp [unitK]
      · simp)

  have hnt : Nontrivial D'.X := by
    obtain ⟨i, hi⟩ := hne
    obtain ⟨y, hy⟩ : ∃ y : D₀.X, y ≠ 0 := by
      by_contra h
      push_neg at h
      exact hi (LinearMap.ext₂ fun y z => by simp [h y])
    exact ⟨⟨e.symm y, 0, by simpa using hy⟩⟩
  refine ⟨hPE, hTB, hPI, hfin, ⟨oa1, fun a => ?_, hPW⟩, hmono, ⟨τ₁, fun a b => (hτ₁ a b).2, hFB, hTI⟩, hnt, ⟨⟨_, hPE, hTB, hPI, hfin⟩, rfl⟩⟩
  rw [hoa1]
  exact ho a

end GlobalTheory.UTautData
