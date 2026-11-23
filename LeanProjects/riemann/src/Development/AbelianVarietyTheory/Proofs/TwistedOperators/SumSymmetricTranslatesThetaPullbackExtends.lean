import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.VtMoveSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTieAsm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NuChainPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ThetaNuPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VGeIffExtended
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPullByEndOfPullRel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.RegTiePfA

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.RegSum

def secSum {X : Scheme.{0}} {N : LB X} {n : ℕ} (F : Fin n → LB.Sec N) : LB.Sec N :=
  ⟨fun j => ∑ i, (F i).f j, fun a b => by
    simp only [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (F i).compat a b⟩

theorem sval_sum {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {a : LB.Sec (LB.LinComb L φ ε)} {F : Fin n → LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, a.f j = ∑ i, (F i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) : sval a r z J = ∑ i, sval (F i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ hm _).trans ?_)
  exact ((congrArg _ (map_sum _ _ _)).trans (map_sum _ _ _)).trans
    (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm)

theorem zCast_sum {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {a b : ℤ} (e : a = b) {n : ℕ}
    {t : LB.Sec (LPow A L a T)} {F : Fin n → LB.Sec (LPow A L a T)} (h : ∀ j, t.f j = ∑ i, (F i).f j) (j) :
    (PullbackSections.zCast A e t).f j = ∑ i, (PullbackSections.zCast A e (F i)).f j := by
  subst e
  exact h j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem reg_sum (I : IntData Xo c T io y.1) (M : ℕ) {n : ℕ}
    {t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    {F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    (h : ∀ j, t.f j = ∑ i, (F i).f j) (hF : ∀ i, Reg I M (F i)) : Reg I M t := by
  choose σ σt h1 h2 using hF
  refine ⟨secSum σ, secSum σt, fun Z r zp e1 e2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · refine (sval_sum (zCast_sum _ _ h) zp z hJ).trans ?_
    rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h1 i Z r zp e1 e2 z J J' hJ hJ'
  · rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ',
      sval_sum (a := secSum σ) (F := σ) (fun _ => rfl) _ z hJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h2 i Z r z J J' hJ hJ'

theorem reg_of_isTransl (I : IntData Xo c T io y.1) (M : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y))))
    (P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G) (hP : P.TorsionIso) (hM : IsUnit (M : T.V))
    (hF : letI := io.toAlgebra; IsTransl M y.1.s F) : Reg I M F := by
  let _ := io.toAlgebra
  obtain ⟨a, hVt⟩ := hF
  obtain ⟨θ, hθ, θK, hθ1, hθ2⟩ := PullbackSections.thetaTie _ _ _ _ _ _ T io y.1 I
  obtain ⟨ttK, FK, hVK, hFK⟩ := PullbackSections.VtMove.vtMoveSt _ _ _ _ _ y.1.x I.t' I.m1 I.w1 I.rig1 M _ y.1.s _ F hVt
    (fun u hu => hu) θK hθ1
  obtain ⟨σ, hσ⟩ := PullbackSections.regUnif_of' PullbackSections.thetaNu GlobalTheory.EndPullNu.main.2 GlobalTheory.FiniteLiftNu.finNu _ _ T.V I.G P hP θ hθ M hM
    I.t' I.m2 I.w2 I.rig2 θK hθ2 ttK FK hVK
  obtain ⟨σt, hσt⟩ := PullbackSections.exists_restrict I.t' _ (PullbackSections.zCast I.t'.G (PullbackSections.natCast_sq M) FK)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left),
      (r ≫ PullbackSections.gsec I.t'.G) ≫ (snd (𝟙_ (Over (Sp T.Fr))) I.t'.G).left = r := fun r => by
    rw [Category.assoc, PullbackSections.gsec_snd, Category.comp_id]
  refine ⟨σ, σt, fun Z r zp h1 h2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [hσt Z r z J' hJ']
    exact hFK Z r zp (r ≫ PullbackSections.gsec I.t'.G) h1 h2 (hg r) z J J' hJ hJ'
  · rw [hσt Z r z J' hJ']
    exact hσ Z r (r ≫ PullbackSections.gsec I.t'.G) (hg r) z J J' hJ hJ'

theorem reg_of_isTranslSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (M : ℕ) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), (∃ U : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, U.TorsionIso) → IsUnit (M : T.V) → letI := io.toAlgebra; IsTranslSum M y.1.s t → Reg I M t := by
  intro E _ _ _ H Dw l Xo c T io y I M t ⟨P, hP⟩ hM ⟨n, F, hF, h⟩
  exact reg_sum I M h fun i => reg_of_isTransl I M (F i) P hP hM (hF i)

end GlobalTheory.HkIntegral.RegSum
