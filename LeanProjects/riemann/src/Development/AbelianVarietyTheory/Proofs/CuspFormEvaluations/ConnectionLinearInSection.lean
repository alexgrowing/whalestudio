import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.LocalToGlobal.ProjectiveLattices.ThExpBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.NabLinear

section Formal

variable {k : Type} [CommRing k] {d : ℕ}

theorem dof_C_mul (F : Fin d → PS k 2 d) (u : Fin d → k) (c : k) (f : PS k 1 d) :
    Germ.Dof F u (MvPowerSeries.C c * f) = MvPowerSeries.C c * Germ.Dof F u f := by
  unfold Germ.Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← MvPowerSeries.smul_eq_C_mul, Derivation.map_smul, MvPowerSeries.smul_eq_C_mul]
  ring

theorem dof_iter_C_mul (F : Fin d → PS k 2 d) (u : Fin d → k) (c : k) (n : ℕ) (f : PS k 1 d) :
    (Germ.Dof F u)^[n] (MvPowerSeries.C c * f) = MvPowerSeries.C c * (Germ.Dof F u)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dof_C_mul, ih]

theorem dmon_C_mul (F : Fin d → PS k 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → k) (m : κ →₀ ℕ) (c : k)
    (f : PS k 1 d) :
    Germ.DmonOf F u m (MvPowerSeries.C c * f) = MvPowerSeries.C c * Germ.DmonOf F u m f := by
  unfold Germ.DmonOf
  induction (Finset.univ : Finset κ).toList with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, List.foldr_cons, ih, dof_iter_C_mul]

theorem nabVal_C_mul [Algebra ℚ k] {R : Type} [CommRing R] [Algebra R k] {O : Type} [CommRing O] [StarRing O]
    (B : Germ.FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (c : k) (f : PS k 1 d) {κ : Type} [Fintype κ]
    (u : κ → Fin d → k) (P : MvPolynomial κ k) :
    B.nabVal k h w0 q (MvPowerSeries.C c * f) u P = c * B.nabVal k h w0 q f u P := by
  unfold Germ.FB.nabVal Germ.DpolyOf
  rw [_root_.mul_assoc, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dmon_C_mul]
  simp only [map_mul, MvPowerSeries.constantCoeff_C]
  ring

theorem psJet_C {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (c : k) :
    psJet m (MvPowerSeries.C c : MvPowerSeries κ k) = algebraMap k (Jet k κ m) c := by
  have h : (MvPowerSeries.C c : MvPowerSeries κ k) = ((MvPolynomial.C c : MvPolynomial κ k) : MvPowerSeries κ k) := by
    simp
  rw [h, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
  rfl

end Formal

section Sec

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

omit [GrpObj A] in
theorem gs_liftFun {T : Over S0} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) {Z : Scheme.{0}}
    (q : Z ⟶ (T ⊗ A).left) (z : Z) (hz : q z ∈ W) :
    gs q z W (liftFun A W r) = gs (q ≫ (fst T A).left) z ⊤ r :=
  (gs_res q z le_top hz _).trans (gs_pull q (fst T A).left z ⊤ trivial r)

theorem isValueAt_scale {T T' : Over S0} (g : T' ⟶ T) {F F' : LB.Sec (LPow A L a T)} {r : Γ(T.left, ⊤)}
    (hF : ∀ j, F'.f j = liftFun A _ (T := T) r * F.f j) {F₁ F₂ : LB.Sec (LPow A L a T')}
    (h₁ : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) F F₁)
    (h₂ : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) F' F₂) {z : T' ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T'.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T'.left, ⊤)}
    (hv : IsValueAt A L a F₁ z τ v) : IsValueAt A L a F₂ z τ (g.left.appTop.hom r * v) := by
  intro j
  have key : (T'.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (F₂.f j)) =
      (T'.left.presheaf.map (homOfLE le_top).op).hom (g.left.appTop.hom r) *
      (T'.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (F₁.f j)) := by
    apply fn_ext
    intro x hx
    have hP := val_le A L z j hx
    have hP' : (𝟙 T'.left ≫ (ptSecT A z).left) x ∈ (LPow A L a T').U j := hP
    have hQ : ((𝟙 T'.left ≫ (ptSecT A z).left) ≫ (g ▷ A).left) x ∈ (LPow A L a T).U j :=
      chart_le_res A L (g ▷ A) (whiskerRight_snd g A) a j hP'
    have e : ((𝟙 T'.left ≫ (ptSecT A z).left) ≫ (g ▷ A).left) ≫ (fst T A).left = 𝟙 T'.left ≫ g.left := by
      rw [Category.id_comp, Category.id_comp, ← Over.comp_left, ← Over.comp_left]
      congr 1
      simp [ptSecT]
    have t : ∀ s : LB.Sec (LPow A L a T'), gs (𝟙 _) x _
        ((T'.left.presheaf.map (homOfLE (val_le A L z j)).op).hom (((ptSecT A z).left.app _).hom (s.f j))) =
        gs (𝟙 _ ≫ (ptSecT A z).left) x _ (s.f j) := fun s =>
      (gs_res (𝟙 _) x (val_le A L z j) hx _).trans (gs_pull (𝟙 _) (ptSecT A z).left x _ hP (s.f j))
    refine (t F₂).trans ((GermD.pullSec_stalk A L a h₂ _ x j hP').trans ?_)
    refine Eq.trans ?_ (gs_mul (𝟙 _) x _ hx _ _).symm
    refine (congrArg (gs _ x _) (hF j)).trans ((gs_mul _ x _ hQ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
    · refine (gs_liftFun A _ r _ x hQ).trans ?_
      rw [e]
      exact ((gs_res (𝟙 _) x le_top hx _).trans (gs_pull (𝟙 _) g.left x ⊤ trivial r)).symm
    · exact ((t F₁).trans (GermD.pullSec_stalk A L a h₁ _ x j hP')).symm
  rw [key, hv j, map_mul]
  exact (_root_.mul_assoc _ _ _).symm

end Sec

theorem appTop_toΓ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    ((spMap f).appTop).hom (toΓ A a) = toΓ B (f a) := by
  simp only [toΓ, spMap]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end GlobalTheory.NabLinear

namespace GlobalTheory

open NabLinear in

theorem nab_smul_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (N : ℕ) (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (r : S), (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) → ∀ α, nab y ((N : ℤ) ^ 2) F' α = r * nab y ((N : ℤ) ^ 2) F α := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S _ _ y N
  letI : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have key : ∀ (K : ℤ) (k : ℕ), K = (k : ℤ) →
      ∀ (F F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x))) (r : S),
      (∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) →
        ∀ α, nab y K F' α = r * nab y K F α := by
    rintro K k rfl F F' r hF α
    obtain ⟨C, hex, hval⟩ := hnab.2 S y
    obtain ⟨f, hf⟩ := hex k F
    have hf' : IsGerm y C.d C.x C.B.A.act C.e C.wP k F' (MvPowerSeries.C r * f) := by
      intro m
      obtain ⟨F₁, τ, hP, hC, hV⟩ := hf m
      obtain ⟨F₂, hP₂⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
        (jBase y C.d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F'
      refine ⟨F₂, τ, hP₂, hC, ?_⟩
      have h := isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (jBase y C.d m 1) hF hP hP₂ hV
      refine (congrArg (IsValueAt Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) F₂ (C.x m) τ) ?_).mp h
      refine (congrArg (fun w : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤) => w * toΓ _ (psJet m f))
        (appTop_toΓ (algebraMap S (Jet S (Fin 1 × Fin C.d) m)) r)).trans ?_
      rw [FBIdJet.psJet_mul, psJet_C, map_mul]
    exact (hval k F' _ hf' α).trans ((nabVal_C_mul _ _ _ _ _ _ _ _).trans (congrArg (r * ·) (hval k F f hf α).symm))
  exact key _ (N ^ 2) (Nat.cast_pow N 2).symm

end GlobalTheory
