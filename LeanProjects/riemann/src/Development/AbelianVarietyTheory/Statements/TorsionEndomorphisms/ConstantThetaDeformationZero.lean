import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Theta1
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section Defs

variable {X : Scheme.{0}} {R : Type} [CommRing R]

def IsRatioFamily {H : LB X} {m : ℕ} (s : Fin (m + 1) → H.Sec) (i : Fin (m + 1))
    (r : Fin (m + 1) → Γ(X, Out.nonzeroLocus (s i))) : Prop :=
  ∀ j k, resG X (inf_le_right : Out.nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
    resG X (inf_le_left : Out.nonzeroLocus (s i) ⊓ H.U k ≤ Out.nonzeroLocus (s i)) (r j) *
      resG X (inf_le_right : Out.nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k)

def vanishingForms (f : X ⟶ Sp R) {H : LB X} {m : ℕ} (s : Fin (m + 1) → H.Sec) (d : ℕ) :
    Set (MvPolynomial (Fin (m + 1)) R) :=
  {F | F.IsHomogeneous d ∧ ∀ k, MvPolynomial.eval₂Hom (AbLaw.cst f (H.U k)) (fun j => (s j).f k) F = 0}

def IsCutOutInDegree (f : X ⟶ Sp R) {H : LB X} {m : ℕ} (s : Fin (m + 1) → H.Sec) (d : ℕ) : Prop :=
  ∀ (i : Fin (m + 1)) (r : Fin (m + 1) → Γ(X, Out.nonzeroLocus (s i))), IsRatioFamily s i r →
    ∀ p : MvPolynomial (Fin (m + 1)) R, MvPolynomial.eval₂Hom (AbLaw.cst f _) r p = 0 →
      p ∈ Ideal.span (insert (MvPolynomial.X i - 1) (vanishingForms f s d))

abbrev epsRed (K : Type) [CommRing K] : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom

def HasConstantThetaPt (P : Out.PolAV (Sp (DualNumber R))) (q : ℕ) {ze : Γ(Sp (DualNumber R), ⊤)ˣ}
    (lev : Out.Level P (q ^ 2) ze) : Prop :=
  ∃ c : (Fin (2 * P.g) → ZMod (q ^ 2)) → R,
    Out.IsThetaPt P q lev.toPt
      (fun a => (Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (algebraMap R (DualNumber R) (c a)))

def IsConstantFamily (P : Out.PolAV (Sp (DualNumber R))) (P₀ : Out.PolAV (Sp R)) (φ : P₀.A.left ⟶ P.A.left)
    {I : Type} (x : I → (Out.baseOver (Sp (DualNumber R)) ⟶ P.A)) : Prop :=
  ∃ ψ : P.A.left ⟶ P₀.A.left, IsPolFibre (algebraMap R (DualNumber R)) P₀ P ψ ∧ φ ≫ ψ = 𝟙 _ ∧
    ∀ (i : I) (x₀ : Out.baseOver (Sp R) ⟶ P₀.A), x₀.left ≫ φ = spMap (epsRed R) ≫ (x i).left →
      (x i).left ≫ ψ = spMap (algebraMap R (DualNumber R)) ≫ x₀.left

end Defs

def ConstantThetaDeformationSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (n k j N N' d₀ : ℕ), n.Prime → Odd n → (n : K) ≠ 0 → 2 ≤ k →
    N = (n ^ k) ^ 2 → N' = n ^ j * N →
  ∀ (P : Out.PolAV (Sp (DualNumber K))) (ze : Γ(Sp (DualNumber K), ⊤)ˣ) (lev : Out.Level P (N' ^ 2) ze)
    (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left), IsPolFibre (epsRed K) P P₀ φ →
  ∀ (m : ℕ) (s : Fin (m + 1) → (lbPow P₀.L N).Sec), AbLaw.VeryAmpleBy P₀.A.hom (lbPow P₀.L N) s →
    IsCutOutInDegree P₀.A.hom s d₀ → N ^ P.g * P.g.factorial * d₀ < N' ^ 2 →
    HasConstantThetaPt P N' lev → IsConstantFamily P P₀ φ lev.pt

section CutOut

open MvPolynomial

variable {X : Scheme.{0}} {R : Type} [CommRing R] {H : LB X} {m : ℕ}

theorem ThetaDeform.eval₂_scale {σ A : Type} [CommRing A] (φ : R →+* A) (c : A) (x : σ → A) {F : MvPolynomial σ R}
    {e : ℕ} (hF : F.IsHomogeneous e) : eval₂ φ (fun j => x j * c) F = c ^ e * eval₂ φ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hF (mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

def ThetaDeform.germAt (y : X) (U : X.Opens) (h : y ∈ U) : Γ(X, U) →+* X.presheaf.stalk y :=
  (X.presheaf.germ U y h).hom

theorem ThetaDeform.germAt_eq (y : X) (U : X.Opens) (h : y ∈ U) (a : Γ(X, U)) :
    ThetaDeform.germAt y U h a = gs (𝟙 X) y U a := (gs_eq (𝟙 X) y U h a).symm

theorem ThetaDeform.gs_eval (f : X ⟶ Sp R) (y : X) (U : X.Opens) (h : y ∈ U) (x : Fin (m + 1) → Γ(X, U))
    (F : MvPolynomial (Fin (m + 1)) R) : gs (𝟙 X) y U (eval₂Hom (AbLaw.cst f U) x F) =
      eval₂ ((ThetaDeform.germAt y ⊤ (TopologicalSpace.Opens.mem_top y)).comp (AbLaw.cst f ⊤)) (fun j => gs (𝟙 X) y U (x j)) F := by
  rw [← ThetaDeform.germAt_eq y U h, coe_eval₂Hom, eval₂_comp_left]
  congr 1
  · ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, ThetaDeform.germAt_eq, ThetaDeform.germAt_eq,
      ← AbLaw.rs_cst f (le_top : U ≤ ⊤) a, gs_res _ y _ h]
  · ext j
    exact ThetaDeform.germAt_eq y U h _

variable {s : Fin (m + 1) → H.Sec} {i : Fin (m + 1)} {r : Fin (m + 1) → Γ(X, Out.nonzeroLocus (s i))}

theorem IsRatioFamily.gs_eq (hr : IsRatioFamily s i r) {y : X} (hy : y ∈ Out.nonzeroLocus (s i)) {k : H.ι}
    (hk : y ∈ H.U k) (j : Fin (m + 1)) :
    gs (𝟙 X) y _ ((s j).f k) = gs (𝟙 X) y _ (r j) * gs (𝟙 X) y _ ((s i).f k) := by
  have h : y ∈ Out.nonzeroLocus (s i) ⊓ H.U k := ⟨hy, hk⟩
  have e := congrArg (gs (𝟙 X) y _) (hr j k)
  rwa [gs_res _ y _ h, gs_mul _ y _ h, gs_res _ y _ h, gs_res _ y _ h] at e

theorem IsRatioFamily.unique {r' : Fin (m + 1) → Γ(X, Out.nonzeroLocus (s i))} (hr : IsRatioFamily s i r)
    (hr' : IsRatioFamily s i r') : r = r' := funext fun j => fn_ext fun y hy => by
  obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
  exact ((mem_nonzeroLocus_iff_isUnit _ hk).1 hy).mul_right_cancel
    ((hr.gs_eq hy hk j).symm.trans (hr'.gs_eq hy hk j))

theorem IsRatioFamily.self_eq_one (hr : IsRatioFamily s i r) : r i = 1 := fn_ext fun y hy => by
  obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
  refine ((mem_nonzeroLocus_iff_isUnit _ hk).1 hy).mul_right_cancel ((hr.gs_eq hy hk i).symm.trans ?_)
  rw [← ThetaDeform.germAt_eq y _ hy 1, map_one, _root_.one_mul]

theorem IsRatioFamily.gs_form (f : X ⟶ Sp R) (hr : IsRatioFamily s i r) {y : X} (hy : y ∈ Out.nonzeroLocus (s i))
    {k : H.ι} (hk : y ∈ H.U k) {F : MvPolynomial (Fin (m + 1)) R} {e : ℕ} (hF : F.IsHomogeneous e) :
    gs (𝟙 X) y _ (eval₂Hom (AbLaw.cst f (H.U k)) (fun j => (s j).f k) F) =
      gs (𝟙 X) y _ ((s i).f k) ^ e * gs (𝟙 X) y _ (eval₂Hom (AbLaw.cst f _) r F) := by
  rw [ThetaDeform.gs_eval f y _ hk, ThetaDeform.gs_eval f y _ hy, ← ThetaDeform.eval₂_scale _ _ _ hF]
  congr 1
  exact funext fun j => hr.gs_eq hy hk j

theorem IsRatioFamily.eval_eq_zero (f : X ⟶ Sp R) (hr : IsRatioFamily s i r) {F : MvPolynomial (Fin (m + 1)) R}
    {d : ℕ} (hF : F ∈ vanishingForms f s d) : eval₂Hom (AbLaw.cst f _) r F = 0 := fn_ext fun y hy => by
  obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
  have e := hr.gs_form f hy hk hF.1
  rw [hF.2 k, LBGerm.gs_zero _ y _ hk] at e
  rw [LBGerm.gs_zero _ y _ hy]
  exact (((mem_nonzeroLocus_iff_isUnit _ hk).1 hy).pow d).mul_right_eq_zero.1 e.symm

theorem mem_vanishingForms_of_ratios (f : X ⟶ Sp R) (hc : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (r : ∀ i, Fin (m + 1) → Γ(X, Out.nonzeroLocus (s i))) (hr : ∀ i, IsRatioFamily s i (r i))
    {F : MvPolynomial (Fin (m + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d)
    (h : ∀ i, eval₂Hom (AbLaw.cst f _) (r i) F = 0) : F ∈ vanishingForms f s d :=
  ⟨hF, fun k => fn_ext fun y hk => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ y))
    rw [(hr i).gs_form f hi hk hF, h i, LBGerm.gs_zero _ y _ hi, LBGerm.gs_zero _ y _ hk, mul_zero]⟩

theorem ThetaDeform.exists_homogeneous (i : Fin (m + 1)) (p : MvPolynomial (Fin (m + 1)) R) :
    ∀ᶠ d in Filter.atTop, ∃ F : MvPolynomial (Fin (m + 1)) R, F.IsHomogeneous d ∧ MvPolynomial.X i - 1 ∣ F - p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine Filter.Eventually.of_forall fun d => ⟨C a * MvPolynomial.X i ^ d,
      by simpa using (isHomogeneous_C _ a).mul (isHomogeneous_X_pow i d), ?_⟩
    rw [← mul_sub_one]
    exact (sub_one_dvd_pow_sub_one _ d).mul_left _
  | add p q hp hq =>
    filter_upwards [hp, hq] with d ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨F + G, hF.add hG, by rw [add_sub_add_comm]; exact e.add e'⟩
  | mul_X p j hp =>
    obtain ⟨e, he⟩ := Filter.eventually_atTop.1 hp
    refine Filter.eventually_atTop.2 ⟨e + 1, fun d hd => ?_⟩
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨F, hF, h⟩ := he d (by omega)
    exact ⟨F * MvPolynomial.X j, hF.mul (isHomogeneous_X _ j), by rw [← sub_mul]; exact h.mul_right _⟩

end CutOut

section Families

variable {R : Type} [CommRing R]

theorem IsPolFibre.existsUnique_point {R' : Type} [CommRing R'] {f : R →+* R'} {P : Out.PolAV (Sp R)}
    {P' : Out.PolAV (Sp R')} {φ : P'.A.left ⟶ P.A.left} (h : IsPolFibre f P P' φ)
    (x : Out.baseOver (Sp R) ⟶ P.A) :
    ∃! x' : Out.baseOver (Sp R') ⟶ P'.A, x'.left ≫ φ = spMap f ≫ x.left := by
  have hφ := h.2.1.1
  have w : (spMap f ≫ x.left) ≫ P.A.hom = 𝟙 _ ≫ spMap f := by
    rw [Category.assoc, Over.w x]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  refine ⟨Over.homMk (hφ.lift _ _ w) (hφ.lift_snd _ _ w), hφ.lift_fst _ _ w, fun v' h => ?_⟩
  exact Over.OverMorphism.ext (hφ.hom_ext (h.trans (hφ.lift_fst _ _ w).symm)
    ((Over.w v').trans (hφ.lift_snd _ _ w).symm))

end Families

section Point

end Point

section Zero

open Out Out.Inh Out.InhVV

def ThetaDeform.zeroLevel (S : Scheme.{0}) (q : ℕ) (ze : Γ(S, ⊤)ˣ) (h : IsPrimitiveRoot ze q) :
    Out.Level (zeroPolAV S) q ze where
  pt i := i.elim0
  prim := h
  torsion i := i.elim0
  indep _ _ _ _ _ _ _ := funext fun i => i.elim0
  span _ _ _ _ _ _ := ⟨fun i => i.elim0, toUnit_unique _ _⟩
  pairing i := i.elim0

section Ones

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}

theorem ThetaDeform.pullGen_one (ht : ∀ j, t.s j = 1) (h : Z ⟶ Y) (j) : (LB.pullGen L φ ε t h).s j = 1 :=
  (congrArg (fun u => res _ (pullU h _ u)) (ht j)).trans ((congrArg (res _) (map_one _)).trans (map_one _))

theorem ThetaDeform.mulGen_one (ht : ∀ j, t.s j = 1) (ht' : ∀ j, t'.s j = 1) (j) :
    (LB.mulGen L φ ε φ' ε' t t').s j = 1 :=
  (congrArg₂ (· * ·) ((congrArg (res _) (ht _)).trans (map_one _))
    ((congrArg (res _) (ht' _)).trans (map_one _))).trans (_root_.mul_one _)

theorem ThetaDeform.invGen_one (ht : ∀ j, t.s j = 1) (j) : (LB.invGen L φ ε t).s j = 1 :=
  (congrArg (·⁻¹) (ht j)).trans inv_one

theorem ThetaDeform.corr_one (ht : ∀ j, t.s j = 1) (ht' : ∀ j, t'.s j = 1) : LB.Gen.Corr L φ ε φ' ε' t t' :=
  fun j j' _ _ _ => ((congrArg (res _) (ht j)).trans (map_one _)).trans
    ((congrArg (res _) (ht' j')).trans (map_one _)).symm

end Ones

open ThetaDeform in

theorem ThetaDeform.zero_isThetaPtOver (S : Scheme.{0}) (q : ℕ) (T : Over S) {I : Type}
    (x : I → (T ⟶ (zeroPolAV S).A)) : IsThetaPtOver (zeroPolAV S) q x (fun _ => 1) := by
  refine ⟨oneSec S 1 T, oneSec S _ T, ⟨fun _ => 1⟩, one1 S T 1 _, fun _ => theta1 S T _, fun _ => oneSec S _ T,
    fun _ => 1, 1, ?_, ?_, ?_, ?_, fun i => ⟨toUnit_unique _ _, ?_, ⟨fun _ => 1⟩, ?_, ?_⟩, fun i => ?_, fun i => ?_,
    fun _ => (_root_.one_mul _).symm⟩
  · intro s
    have hU : ∀ j, (LPow (zeroPolAV S).A (zeroPolAV S).L 1 T).U j = ⊤ := fun j =>
      top_unique fun _ _ => Set.mem_iInter.2 fun _ => trivial
    have h₀ : IsIso (fst T (𝟙_ (Over S))) := by
      rw [← rightUnitor_hom]
      infer_instance
    have : IsIso (fst T (zeroPolAV S).A).left := inferInstanceAs (IsIso ((Over.forget S).map (fst T (𝟙_ (Over S)))))
    obtain ⟨r, hr⟩ := surj_appLE (fst T (zeroPolAV S).A).left _ (hU fun _ => PUnit.unit) le_top
      (s.f fun _ => PUnit.unit)
    exact ⟨r, fun j => hr.symm.trans (_root_.mul_one _).symm⟩
  · intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]
  · intro i j
    erw [linComb_triv_g, _root_.one_mul]; dsimp only [one1]; repeat erw [map_one]
  · intro j
    simp only [oneSec, Units.val_one]
    (repeat erw [map_one]); (try erw [_root_.one_mul])
  · refine corr_one _ (fun j => ?_) fun _ => rfl
    dsimp only [powGen]
    apply Finset.prod_eq_one
    intro a _
    exact (congrArg (res _) (pullGen_one _ (t := (theta1 S T _).φ) (fun _ => rfl) _ _)).trans (map_one _)
  · intro i j
    erw [linComb_triv_g, _root_.one_mul]; repeat erw [map_one]
  · exact corr_one _ (mulGen_one _ (mulGen_one _ (pullGen_one _ (fun _ => rfl) _) fun _ => rfl)
      (mulGen_one _ (pullGen_one _ (fun _ => rfl) _) (invGen_one _ (pullGen_one _ (fun _ => rfl) _)))) fun _ => rfl
  · intro j
    simp only [oneSec]
    (repeat erw [map_one]); (try erw [_root_.one_mul])
  · intro j
    simp only [oneSec, one1, Units.val_one]
    (repeat erw [map_one]); (try erw [_root_.one_mul])
    rfl

end Zero

end GlobalTheory
