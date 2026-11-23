import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGTateIsoTwistOfSimilitude
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntIntCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTateTwist :
    GSimOf → TateTwist := by
  intro hG p _ D G L R _ _ gb S s N o k _ t I hI u hu
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have hNcop : (N : ℕ).Coprime p := N.2.2
  have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
  have hui1 : u⁻¹ ∈ L.KN 1 := inv_mem hu1
  obtain ⟨g, hg⟩ := hG p D G L u⁻¹ hui1
  obtain ⟨J, hJ⟩ := UpperTheory.exists_gTateIso_twist_of_similitude I g
  have intU := UpperTheory.Gal.Int.Geo.integ_of_mem hu1
  have intUi := UpperTheory.Gal.Int.Geo.integ_of_mem hui1
  unfold UpperTheory.Gal.Int.Geo.Integ at intU intUi
  have hcong : L.CongOne (N : ℕ) u⁻¹ := by
    unfold GlobalTheory.LKGeo.Link.KN at hu
    simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq] at hu
    exact hu.2
  unfold GlobalTheory.LKGeo.Link.CongOne at hcong
  have inv_act : ∀ v, L.actG u⁻¹ (L.actG u v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have act_inv : ∀ v, L.actG u (L.actG u⁻¹ v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine ⟨J, ?_, ?_⟩
  · unfold UpperTheory.Gal.G3.Ind at hI ⊢
    intro y
    rw [hI y, hJ _ hNpos y]
    symm
    refine (HeckeRestrict.ev_eq_iff I _ hNpos (g.f N y) y).mpr ?_
    obtain ⟨w, hw, hgw⟩ := hg N hNpos hNcop y
    obtain ⟨w', hw', hcw⟩ := hcong (inAf D y) (GlobalTheory.HeckeApprox.inAf_mem D y)
    apply LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ N hNpos hNcop (w' - w) (sub_mem hw' hw)
    have e := hgw.symm.trans hcw
    rw [show inAf D (g.f N y - y) = inAf D (g.f N y) - inAf D y from GlobalTheory.HeckeApprox.inAf_sub D _ _, smul_sub]
    calc inAf D (g.f N y) - inAf D y = (inAf D (g.f N y) + (N : ℕ) • w) - (N : ℕ) • w - inAf D y := by abel
      _ = (inAf D y + (N : ℕ) • w') - (N : ℕ) • w - inAf D y := by rw [e]
      _ = (N : ℕ) • w' - (N : ℕ) • w := by abel
  · unfold UpperTheory.Gal.G3.Rel
    intro n hn hnp x y
    rw [Category.comp_id, hJ n hn y]
    refine (HeckeRestrict.ev_eq_iff I n hn x (g.f n y)).trans ?_
    obtain ⟨w, hw, hgw⟩ := hg n hn hnp y
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨L.actG u (inAf D z - w), intU _ (sub_mem (GlobalTheory.HeckeApprox.inAf_mem D z) hw), ?_⟩
      have h1 := GlobalTheory.HeckeApprox.inAf_add D (g.f n y) (n • z)
      have h2 := GlobalTheory.HeckeApprox.inAf_nsmul D n z
      have hx : inAf D x = inAf D (g.f n y) + n • inAf D z :=
        (congrArg (inAf D) (eq_add_of_sub_eq' hz)).trans (h1.trans (congrArg (inAf D (g.f n y) + ·) h2))
      have e1 : inAf D (g.f n y) = L.actG u⁻¹ (inAf D y) - n • w := by
        rw [hgw]
        abel
      rw [hx, e1, map_add, map_sub, map_nsmul, map_nsmul, act_inv, map_sub, smul_sub]
      abel
    · rintro ⟨v, hv, hxv⟩
      apply LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp (w + L.actG u⁻¹ v) (add_mem hw (intUi _ hv))
      have hx : inAf D x = L.actG u⁻¹ (inAf D y) + n • L.actG u⁻¹ v := by
        rw [← map_nsmul, ← map_add, ← hxv, inv_act]
      refine (GlobalTheory.HeckeApprox.inAf_sub D x (g.f n y)).trans ?_
      rw [hx, hgw, smul_add]
      abel
