import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLiftSymbol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfVectorMultiplicationsGlobalResiduesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionShiftCommSingleMonomialStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.HSShort

theorem exists_filV_mulPow {K : Type} [Field K] [NumberField K] (X : Data K) {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s}
    {δ : ℕ} (Co : Coord X.toGeo hs δ) {a : ℕ} (haT : a ≤ X.T) (α : MonoDeg (Fin X.D) a)
    (m : X.Sec (X.T - a)) (hg : m ∈ X.global (X.T - a)) :
    ∃ f : filV X s a, (f.1 : X.Sec X.T) = mulPow X.toGeo s (Nat.sub_add_cancel haT) α m ∧
      ∀ α' p, symV Co a f (α', p) = if α'.1 = α.1 then Co.ev (X.T - a) (hs.res (X.T - a) m) p else 0 := by
  have hh : X.T - a + a = X.T := Nat.sub_add_cancel haT
  have hgl := GlobalTheory.HSCore.IntLift.mulPow_mem_global X.toGeo s hh α hg
  obtain ⟨f, hfeq⟩ : ∃ f : X.V X.T, (f : X.Sec X.T) = mulPow X.toGeo s hh α m := ⟨⟨_, X.global_le _ le_rfl hgl⟩, rfl⟩
  have hfF : (f : X.Sec X.T) ∈ Fil (X.ideal s) a (spaceV X s) := by
    refine (mem_Fil).2 ⟨Submodule.mem_sup_left ?_, ?_⟩
    · rw [hfeq]; exact hgl
    · rw [hfeq]; exact vanishesTo_mulMono _ _ _ _ _ _
  refine ⟨⟨f, hfF⟩, hfeq, fun α' p => ?_⟩
  have key : hs.sym hh (spaceV X s) ((X.V X.T).subtype.restrict (p := filV X s a) (q := Fil (X.ideal s) a (spaceV X s))
      (fun _ hx => hx) ⟨f, hfF⟩) = Pi.single α (hs.res (X.T - a) m) :=
    Vanishing.sym_mulMono _ _ _ _ _ _ _ _ _ _ α (m : X.Sec (X.T - a)) _ hfeq
  unfold symV
  rw [dif_pos haT]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, LinearEquiv.coe_coe, LinearMap.coe_proj,
    Function.eval]
  rw [key]
  by_cases hα : α' = α
  · subst hα; simp
  · rw [if_neg (fun h => hα (Subtype.ext h)), Pi.single_eq_of_ne hα, map_zero]; rfl

theorem totSym_incl {K : Type} [Field K] [NumberField K] {X : Data K} {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s}
    {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) (f : filV X s a) (y : totFil X s a) (h : y.1 = incl X X.T f.1) :
    totSym Co a y = symV Co a f := by
  have : y = Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a) f := Subtype.ext h
  rw [this]
  exact congrArg (symV Co a) (LinearEquiv.symm_apply_apply _ f)

theorem totSym_mono : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), X.MulStable → ∀ a < X.T - X.D, ∀ (α : MonoDeg (Fin X.D) a) (l : Fin (X.T - a) → Fin X.N → K), ∀ m ∈ LinearMap.range (incl X 0), ∃ h : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l m) ∈ totFil X s a, ∀ α' p, totSym Co a ⟨_, h⟩ (α', p) = if α'.1 = α.1 then (∏ q, ∑ k, l q k * Co.y p k) * totRes Co m p else 0 := by
  intro K _ _ X s hs δ Co _ a ha α l m hm
  obtain ⟨m₀, rfl⟩ := hm
  have haT : a ≤ X.T := by omega
  have hm₀ : (m₀ : X.Sec 0) ∈ X.global 0 := (SetLike.ext_iff.1 X.V_zero _).1 m₀.2
  have H : ∀ (t k : ℕ) (_ : 0 + t = k) (u : Fin t → Fin X.N → K), ∃ x' ∈ X.global k,
      word (shift X.toGeo) u (Pi.single 0 (m₀ : X.Sec 0)) = Pi.single k x' ∧ ∀ p,
        Co.ev k (hs.res k x') p = (∏ q, ∑ j, u q j * Co.y p j) * Co.ev 0 (hs.res 0 m₀) p := by
    intro t k h u
    subst h
    obtain ⟨x', h1, h2, h3⟩ := GlobalTheory.T.productOfVectorMultiplications_global_residues K X.toGeo t 0 u _ hm₀
    exact ⟨x', h1, h2, h3 s hs δ Co⟩
  obtain ⟨x', h1, h2, h3⟩ := H _ _ (Nat.zero_add _) l
  obtain ⟨f, hf, hsym⟩ := exists_filV_mulPow X Co haT α x' h1
  have e : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l (incl X 0 m₀)) = incl X X.T f.1 := by
    change pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l (Pi.single 0 (m₀ : X.Sec 0))) =
      Pi.single X.T (f.1 : X.Sec X.T)
    rw [h2, hf]
    exact (GlobalTheory.T.hilbertSamuelSectionShift_comm_single_monomial K X.toGeo).2.2 s a _ _ _ α x'
  refine ⟨⟨f.1, f.2, e.symm⟩, fun α' p => ?_⟩
  rw [totSym_incl Co a f _ e, hsym, h3]
  have : totRes Co (incl X 0 m₀) = Co.ev 0 (hs.res 0 m₀) := by simp [totRes, incl]
  rw [this]

end GlobalTheory.HSShort
