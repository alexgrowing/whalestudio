import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorBundlePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransIso :
    IsoPts → IsogFEt → TransIso := by
  intro IP IF p _ D G L R _ _ gb S s N' N o' o ψ u hu T
  obtain ⟨hmon, -, ⟨ψ', d, hψ', -, hd, hd', hdp⟩, -, tate⟩ := T
  haveI := hmon
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  obtain ⟨hfin, het, hsurj⟩ := IF R S s o'.A o.A o'.ab o.ab ψ ψ' d hd0 hmon hψ' hd hd'
  haveI := het
  haveI := hfin
  have hiso : IsIso ψ.left := by
    apply IP ψ.left
    intro Ω _ _ z
    obtain ⟨v, hv⟩ := hsurj.surj (UpperTheory.Gal.TranscendenceTraces.pt z)
    obtain ⟨y, hy, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ.left Ω z v hv
    refine ⟨y, hy, fun y₂ hy₂ => ?_⟩
    let t : sp Ω ⟶ S := y ≫ o'.A.hom
    have ht2 : y₂ ≫ o'.A.hom = t := by
      rw [← Over.w ψ, ← Category.assoc, hy₂, ← hy, Category.assoc, Over.w ψ]
    let a₁ : Over.mk t ⟶ o'.A := Over.homMk y rfl
    let a₂ : Over.mk t ⟶ o'.A := Over.homMk y₂ ht2
    have hc : a₁ ≫ ψ = a₂ ≫ ψ := by
      ext
      simp [a₁, a₂, hy, hy₂]
    have ha : (a₂ * a₁⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, ← hc, mul_inv_cancel]
    have had : (a₂ * a₁⁻¹) ^ d = 1 := by
      have e : (a₂ * a₁⁻¹) ^ d = (a₂ * a₁⁻¹) ≫ ψ ≫ ψ' := by
        rw [hd, MonObj.comp_pow, Category.comp_id]
      rw [e, ← Category.assoc, ha, MonObj.one_comp]
    let β : R →+* Ω := (Spec.preimage (t ≫ s)).hom
    have hβ : t ≫ s = spMap β := by
      simp [β, spMap, Spec.map_preimage]
    obtain ⟨I', I'', -, -, hrel⟩ := tate Ω t β hβ
    obtain ⟨x, hx⟩ := (I'.onto d hd0 _).mp had
    have h0 : I'.ev d x ≫ ψ = I''.ev d 0 := by
      rw [hx, ha, HeckeRestrict.ev_zero]
    obtain ⟨w, hw, hxw⟩ := (hrel d hd0 hdp x 0).mp h0
    have hinv : u⁻¹ ∈ L.KN 1 := Subgroup.inv_mem _ hu
    have hdw : d • w = L.actG u (inAf D x) := by
      rw [hxw]
      simp [inAf]
    have hxa : inAf D x = d • L.actG u⁻¹ w := by
      rw [← map_nsmul, hdw, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    obtain ⟨z', hz'⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x d hd0 hdp _
      (UpperTheory.Gal.Int.Geo.integ_of_mem hinv w hw) hxa
    have h1 : a₂ * a₁⁻¹ = 1 := by
      rw [← hx]
      exact (I'.ker d hd0 x).mpr ⟨z', hz'⟩
    have h2 : a₂ = a₁ := mul_inv_eq_one.mp h1
    exact congrArg Over.Hom.left h2
  have : IsIso ((Over.forget S).map ψ) := hiso
  exact isIso_of_reflects_iso ψ (Over.forget S)
