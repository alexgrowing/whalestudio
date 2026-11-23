import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresChangeOfForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimSys
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTateDiff :
    TateDiff := by
  intro p _ D G L R _ _ gb S s N o k _ _ t I J hI hJ
  have hN : 0 < N.1 := by have := N.2.1; omega
  have hNp : N.1.Coprime p := N.2.2
  obtain ⟨g, hg⟩ := GlobalTheory.LKGeo.GammaUniq.exists_simSys_all hN hNp
    (fun n q q' z z' h h' => GlobalTheory.weilIs_unique_fieldPoint S o.A _ (LB.isLB_pull o.isLB _) k t n q q' z z' h h')
    (GenCmp.tateRestrict J) (GenCmp.tateRestrict I)
    (fun y => (hJ y).symm.trans (hI y))
  obtain ⟨u, hu, hh⟩ := GlobalTheory.T.similitude_action_adelic_lattice p D G L N.1 hN hNp g
  refine ⟨u, hu, fun n hn hc x y => ?_⟩
  have e₁ : I.ev n x = J.ev n (g.g n x) := hg n hn hc x
  have e₂ : ∀ a b : D.La, J.ev n a = J.ev n b ↔ ∃ z, a = b + n • z := fun a b =>
    GlobalTheory.UPel.HT.TateCompare.ev_eq_iff (GenCmp.tateRestrict J) hn hc
  obtain ⟨w, hw, e₃⟩ := hh n hn hc x
  let f : D.La →+ (AfP p ⊗[ℚ] VQ D) := AddMonoidHom.mk' (inAf D) (GlobalTheory.LKGeo.GammaUniq.inAf_add (p := p) (D := D))
  have hf : ∀ a, f a = inAf D a := fun _ => rfl
  rw [Category.comp_id, e₁, e₂]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨inAf D z + w, add_mem (GlobalTheory.LKGeo.GammaUniq.inAf_mem z) hw, ?_⟩
    rw [e₃, hz, ← hf, ← hf, ← hf, map_add, map_nsmul, smul_add, add_assoc]
  · rintro ⟨v, hv, e₄⟩
    have e₅ : inAf D (g.g n x - y) = n • (v - w) := by
      rw [← hf, map_sub, hf, hf, smul_sub]
      rw [e₃] at e₄
      rw [sub_eq_sub_iff_add_eq_add, e₄, add_comm]
    obtain ⟨z, hz⟩ := GlobalTheory.LKGeo.LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hc _ (sub_mem hv hw) e₅
    exact ⟨z, by rw [← hz]; abel⟩
