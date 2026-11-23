import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionFieldEmbeddingCompat
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

noncomputable section

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

namespace GlobalTheory.BigOn.Exp.ProjRd

attribute [local instance] GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.algKK

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem rd_eOp {D : D7} {c : NChoice D} {w : D.what₂.places.Pl} (ht : NChTie D c) {Gp : Type} [Group Gp] [Fintype Gp]
    (I : Gp ≃* G0g D.nd) (S : RatDat D.ntw) (j : ℕ)
    {Ks' WL' : Type} {_ : Field Ks'} {_ : NumberField Ks'} {_ : Algebra Ks' D.what₂.LL} {_ : AddCommGroup WL'}
    {_ : Module D.what₂.LL WL'} {_ : Module Ks' WL'} [IsScalarTower Ks' D.what₂.LL WL']
    {_ : Module (𝓞 Ks') WL'} {_ : IsScalarTower (𝓞 Ks') Ks' WL'}
    {W' : (D.what₂.LL →+* ℂ) → Type} {_ : ∀ σ, NormedAddCommGroup (W' σ)} {_ : ∀ σ, InnerProductSpace ℂ (W' σ)}
    (A' : FormsL D.what₂.LL Ks' WL' W' Gp) (fi : FormsIso (S.A j) A') (hks : (S.A j).IsKsForm)
    (hgeq : ∀ s, I (fi.eG s) = S.eG s)
    (rho : RhoStab S j) (chi : ChiInLL0 S j)
    (eF : D.nexp.Fm (c.twI w) j (c.sd w) ≃ₗ[FractionRing (D.ntw.O (c.twI w))] Fm S (c.twI w) j (c.sd w))
    (hact : ∀ g x, eF (D.nexp.actG (c.twI w) j (c.sd w) g x) = actG S (c.twI w) j (c.sd w) rho chi g (eF x))
    (eC : Gp → D.what₂.LL) (heC : ∀ h, eC h = (D.nexp.eLL0 (I h) : D.what₂.LL))
    (rd : WL' →ₛₗ[c.embW w] FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w))
    (hrd : ∀ f : FmK S j, rd (fi.e (Subtype.val f)) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] eF.symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f))
    (y : WL') :
    rd (A'.eOp eC y) = GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eExt D.nexp (c.twI w) j (c.sd w) (c.Oe w) (rd y) := by
  classical
  obtain ⟨e, -, -, h3, h4⟩ := GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.stage1 (w := w) ht j S hks rho chi eF hact
  have hre : ∀ x, rd (fi.e x) = e x := by
    intro x
    obtain ⟨n, b, hbK, -, -, -, hsp⟩ := hks
    have hx : x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.what₂.LL).1 hx
    have h5 := h3 n a (fun k => ⟨b k, hbK k⟩)
    refine Eq.trans ?_ h5.symm
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ]
    rw [hrd ⟨b k, hbK k⟩, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨x, rfl⟩ := fi.e.surjective y
  letI : Fintype S.G := Fintype.ofEquiv Gp fi.eG.symm.toEquiv
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Gp I.toEquiv
  have hL : A'.eOp eC (fi.e x) = fi.e (∑ s : S.G, eC (fi.eG s) •
      ((((S.A j).chi s)⁻¹ : D.what₂.LLˣ).val • (S.A j).ρ s x)) := by
    rw [map_sum, FormsL.eOp, LinearMap.sum_apply]
    refine (Fintype.sum_equiv fi.eG.toEquiv _ _ fun s => ?_).symm
    rw [map_smul, map_smul, fi.rho]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, LinearMap.smul_apply, smul_smul, fi.chi]
  have hR : ∀ t : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w),
      GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eExt D.nexp (c.twI w) j (c.sd w) (c.Oe w) t = ∑ s : S.G,
        algebraMap (FractionRing (D.ntw.O (c.twI w))) (FractionRing (c.Oe w)) ((D.nexp.eAlg (c.twI w) (c.sd w)).coeff (S.eG s)) •
          GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.ext (D.ntw.O (c.twI w)) (FractionRing (c.Oe w))
            ((D.nexp.actG (c.twI w) j (c.sd w) (S.eG s)).toLinearMap) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => rw [map_add, hu, hv, ← Finset.sum_add_distrib]; simp only [map_add, smul_add]
    | tmul a m =>
      have h1 : GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eExt D.nexp (c.twI w) j (c.sd w) (c.Oe w) (a ⊗ₜ m) =
          a ⊗ₜ[D.ntw.O (c.twI w)] GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eOp D.nexp (c.twI w) j (c.sd w) m := rfl
      have h2 : GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eOp D.nexp (c.twI w) j (c.sd w) m = ∑ s : S.G,
          (D.nexp.eAlg (c.twI w) (c.sd w)).coeff (S.eG s) • D.nexp.actG (c.twI w) j (c.sd w) (S.eG s) m := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eOp
        rw [GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lift_eq_sum, LinearMap.sum_apply]
        exact (Fintype.sum_equiv S.eG.toEquiv _ _ fun s => rfl).symm
      rw [h1, h2, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.tmul_smul_frac, GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.ext_tmul, TensorProduct.smul_tmul', smul_eq_mul]
      rfl
  rw [hL, hre, hre, hR, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smulₛₗ, h4 s x]
  congr 1
  rw [heC, hgeq, GlobalTheory.Proof.FractionFieldEmbeddingCompat.embW_eq_of_tie ht w]
  change _ = fracExt c w ((D.nexp.eAlg (c.twI w) (c.sd w)).coeff (S.eG s))
  rw [D.nexp.eAlg_def]
  rfl

end GlobalTheory.BigOn.Exp.ProjRd

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem GlobalTheory.BigOn.Exp.canProj : CanProj := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    EvPt.of_forall fun x hx i p _ _ w _ j rd hrd y => ?_⟩⟩
  obtain ⟨-, -, -, hid, -⟩ := p.grpRecPin
  exact GlobalTheory.BigOn.Exp.ProjRd.rd_eOp (Fm.ex x hx i).nch_tie (p.R.eG.trans p.cG) p.Sx ((j : ℕ) + 1) ((R2 p).FW j)
    (p.nexp.fi j) (GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.isKsForm_of_iso (p.nexp.fi j) (p.fw.ks j)) (p.nexp.geq j) (p.nexp.rho _ (Nat.le_add_left _ _) j.2) (p.nexp.chi _ (Nat.le_add_left _ _) j.2)
    (p.nexp.eF _ _ _ (Nat.le_add_left _ _) j.2) (p.nexp.act _ _ _ (Nat.le_add_left _ _) j.2)
    (fun g => (Formalism.L2.DIV.idemOf p.P.A3.A.X).coeff g)
    (fun g => (Fm.D x i).what₂.embLL.injective ((hid g).trans ((Fm.D x i).nStage_trivialCharacter_coeff_eq _).symm)) rd hrd y
