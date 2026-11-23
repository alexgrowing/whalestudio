import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.MulDeg

variable {R : Type} [CommRing R] [IsDomain R]

def tau3 (D : DegPre R) (s a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi s) (LB.invGen D.P.L _ _ (D.psi a)))
      (LB.invGen D.P.L _ _ (D.psi b)))
    (LB.invGen D.P.L _ _ D.rigK)

theorem corr_even_degenerationData_negPoint (D : DegPre R) (h : D.PsiEven) (a m : D.X) (hm : m = -a) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.psi m) (LB.pullGen D.P.L _ _ D.sym (D.xK a))) (D.psi a) := by
  subst hm
  exact h a

theorem corr_bimultiplicative_degenerationData_sums (D : DegPre R) (h : D.TauBimult) (a a' b s t u v : D.X) (hs : s = a + a') (ht : t = a + a' + b)
    (hu : u = a + b) (hv : v = a' + b) :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (tau3 D t s b)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a a' b)))
      (LB.mulGen D.P.L _ _ _ _ (tau3 D u a b) (tau3 D v a' b)) := by
  subst hs ht hu hv
  exact h a a' b

theorem corr_balanced_degenerationData_rosati (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (p q : D.X → D.X) (h : D.TauBal f g p q)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (h1 : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (y y' a a' s t : D.X) (ha : a = p y) (ha' : a' = q y') (hs : s = p y + y') (ht : t = y + q y') :
    LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (tau3 D s a y') (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (tau3 D t y a') := by
  subst ha ha' hs ht
  exact h u hu h1 y y'

variable {O : Type} [CommRing O] [StarRing O]

local instance modMul (D : DegPre R) [h : Module O D.X] (n : ℕ) : Module O (mulDeg D n).X := h

def mulAct (D : DegPre R) [Module O D.X] (oa : D.OAct O) (n : ℕ) : (mulDeg D n).OAct O where
  onB := oa.onB
  c_lin := fun a (y : D.X) => by
    show D.c (n • (a • y)) = D.c (n • y) ≫ oa.onB.act a
    rw [smul_comm n a y, oa.c_lin]
  tau_bal := fun a u hu h1 (y y' : D.X) =>
    corr_balanced_degenerationData_rosati D _ _ _ _ (oa.tau_bal a) u hu h1 (n • y) (n • y') (n • (a • y)) (n • (star a • y'))
      (n • (a • y + y')) (n • (y + star a • y')) (smul_comm n a y) (smul_comm n (star a) y')
      (by rw [nsmul_add, smul_comm n a y]) (by rw [nsmul_add, smul_comm n (star a) y'])

theorem corr_polarisationElement_degenerationData (D : DegPre R) [Module O D.X] (oa : D.OAct O) (w0 : O)
    (u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left, (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left]
      ![1, -2, -1, 2]))
    (h : ∀ y, LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau y (w0 • y)) (LB.pullGen D.P.L _ _ u (D.xK y)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)) (y s b : D.X) (hb : b = w0 • y) (hs : s = y + w0 • y) :
    LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (tau3 D s y b) (LB.pullGen D.P.L _ _ u (D.xK y)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK) := by
  subst hb hs
  exact h y

theorem mulDeg_laws : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O) (n : ℕ), D.PsiEven → D.TauBimult → TraceFormTwistIso D oa w0 → (∀ y, PsiUnitOn D y Set.univ) → letI : Module O (mulDeg D n).X := ‹Module O D.X›; (mulDeg D n).PsiEven ∧ (mulDeg D n).TauBimult ∧ (∀ y, PsiUnitOn (mulDeg D n) y Set.univ) ∧ ∃ oa' : (mulDeg D n).OAct O, oa'.onB = oa.onB ∧ TraceFormTwistIso (mulDeg D n) oa' w0 := by
  intro R _ _ D O _ _ _ oa w0 n he hb hw hg
  refine ⟨fun (a : D.X) => corr_even_degenerationData_negPoint D he (n • a) (n • (-a)) (neg_nsmul a n),
    fun (a a' b : D.X) => corr_bimultiplicative_degenerationData_sums D hb (n • a) (n • a') (n • b) (n • (a + a')) (n • (a + a' + b)) (n • (a + b))
      (n • (a' + b)) (nsmul_add _ _ _) (by rw [nsmul_add, nsmul_add]) (nsmul_add _ _ _) (nsmul_add _ _ _),
    fun (y : D.X) => hg (n • y), mulAct D oa n, rfl, ?_⟩
  obtain ⟨u, hu, h1, h⟩ := hw
  exact ⟨u, hu, h1, fun (y : D.X) => corr_polarisationElement_degenerationData D oa w0 u h (n • y) (n • (y + w0 • y)) (n • (w0 • y)) (smul_comm n w0 y)
    (by rw [nsmul_add, smul_comm n w0 y])⟩

end GlobalTheory.UCanon.MulDeg
