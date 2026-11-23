import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionDeterminantRoot

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem chars_of_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), IsEtaTilde D R.eta ∧ R.xi A.μ0 = 1 ∧ R.Q A.μ0 = ∅ ∧ ∀ t v ε, NonSplitAt D v ε → UnramAt ε (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 ∧ UnramAt ε (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i
  classical
  have hL := h.lev
  have hW := h.thP.ωP i A.μ0
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  refine ⟨GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr)),
    MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x,
    Finset.eq_empty_of_forall_notMem fun P hP =>
      (hL.Q_ram A.μ0 P).2 (Or.inl hP) (by rw [hL.xi_base]; exact fun _ _ => rfl), fun t v ε hv => ?_⟩
  obtain ⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩ := h.thP.vP i t
  have key := fun P (hP : P.under (𝓞 D.host.F) = v) =>
    (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by
      rw [hP]
      exact GlobalTheory.AdTh.RecPair.under_ne (hes PP (Finset.mem_union.2 hPP)) hv
  have u1 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i
  have u2 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1
  have u3 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P
  have u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1)) := fun x a b c => by
    show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1
    rw [u1 x a b c, u2 x a b c, one_mul]
  refine ⟨u4, fun x a b c => ?_⟩
  show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1
  rw [u4 x a b c, u3 x a b c, inv_one, one_mul]

end GlobalTheory.OneMapRef
