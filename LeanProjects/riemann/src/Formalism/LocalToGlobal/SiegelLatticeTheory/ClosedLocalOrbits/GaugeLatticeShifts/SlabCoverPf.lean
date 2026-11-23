import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfLam

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem slabCoverC_of (hGF : GFInfInj) (hSA : NStrongApprox) (hNL : NLift) (hNR : NRatLam)
    (hRL : RatLeviC) (hPD : PsiDdC) : SlabCoverC := by
  intro D X Y u Ωs hKL hNeat hΩ
  have hK := Y.hK
  refine ⟨?_, ?_⟩
  ·
    rintro y ⟨n, h, k, hn, hk, hy⟩
    obtain ⟨ρ, ⟨γ, κ, hγκ⟩, -⟩ := Y.colReps u h
    have hs0 : ((γ : X.B.I.GA))⁻¹ ∈ Srat X u := inv_mem (gam_srat X u _ γ.2)
    obtain ⟨hn', -⟩ := nfinConj_holds X u (iotaF X u γ)⁻¹ n hn
    rw [Subgroup.coe_inv, inv_inv, iotaF_coe] at hn'
    obtain ⟨ν, hνS, hνK⟩ := hSA D X Y u ρ _ hKL hn'
    have hκ : (X.xu u)⁻¹ * (((κ : Hfin X u)) : X.B.I.Gf) * X.xu u ∈ X.K2 := κ.2
    set s1 : X.B.I.GA := ν * ((γ : X.B.I.GA))⁻¹ with hs1
    obtain ⟨t, ht, htΩ⟩ := (hΩ ρ).2.1 (s1 * y).1
    obtain ⟨s2, hs2, hs21, hs2K⟩ := hNL D X Y u ρ t ht
    refine ⟨s2 * s1, mul_mem hs2 (mul_mem hνS hs0), ρ, ?_, ?_⟩
    · show (s2 * s1 * y).1 ∈ Ωs ρ
      rw [mul_assoc, Prod.fst_mul, hs21]
      exact htΩ
    · refine ⟨_, hK.2.1 _ hs2K _ (hK.2.1 _ hνK _ (hK.2.1 _ hκ _ hk)), ?_⟩
      show _ = (s2 * s1 * y).2
      rw [hs1]
      simp only [Prod.snd_mul, Prod.snd_inv, hy, hγκ, Subgroup.coe_mul, iotaF_coe]
      group
  ·
    intro ρ ρ' y s hs hy hsy
    obtain ⟨hy1, k, hk, hyk⟩ := hy
    obtain ⟨hsy1, k', hk', hsyk⟩ := hsy
    have hyk' : ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u * k = y.2 := hyk
    have hsyk' : ((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u * k' = s.2 * y.2 := hsyk
    have hg : (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2 := by
      have e : (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) =
          k' * k⁻¹ := by
        calc (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)
            = (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * (s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u * k)) * k⁻¹ := by
              group
          _ = (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u * k') * k⁻¹ := by
              rw [hyk', ← hsyk']
          _ = k' * k⁻¹ := by group
      rw [e]; exact hK.2.1 _ hk' _ (hK.2.2.1 _ hk)
    obtain ⟨hs1, hs2⟩ := sratComp_holds X u s hs
    obtain ⟨ν, η, hνη, hνG, hν1, hν2, hη⟩ := hRL D X u s (Subgroup.mem_inf.1 hs).1 hs1 hs2
    obtain ⟨ηg, hηg⟩ : ∃ ηg : Gam X u, ηg = ⟨η, hη⟩ := ⟨_, rfl⟩
    have hs2e : s.2 = ν.2 * η.2 := by rw [hνη]; rfl
    obtain ⟨hn1, -⟩ := nfinConj_holds X u ((Y.cs u).h ρ')⁻¹ ν.2 hν2
    have hLD := levelDec_of_psiDd (X := X) (u := u) (hPD D X)
    obtain ⟨h1, hh1⟩ : ∃ h1 : Hfin X u, h1 = ((Y.cs u).h ρ')⁻¹ * iotaF X u ηg * (Y.cs u).h ρ := ⟨_, rfl⟩
    have e1 : (X.xu u)⁻¹ * ((((Y.cs u).h ρ')⁻¹ : Hfin X u) * ν.2 * ((((Y.cs u).h ρ')⁻¹ : Hfin X u) : X.B.I.Gf)⁻¹ *
        (h1 : X.B.I.Gf)) * X.xu u =
        (((Y.cs u).h ρ' : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) := by
      rw [hs2e, hh1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, iotaF_coe, hηg]
      group
    have hh1K : (X.xu u)⁻¹ * (h1 : X.B.I.Gf) * X.xu u ∈ X.K2 := (hLD _ hn1 h1 (e1 ▸ hg)).1
    have hρρ : ρ' = ρ := by
      refine (Y.colReps u ((Y.cs u).h ρ)).unique ⟨ηg⁻¹, ⟨h1, hh1K⟩, ?_⟩ ⟨1, 1, by simp⟩
      show (Y.cs u).h ρ = iotaF X u ηg⁻¹ * (Y.cs u).h ρ' * h1
      rw [map_inv, hh1]
      group
    subst hρρ
    have hmem : ((Y.cs u).h ρ')⁻¹ * iotaF X u ηg * (Y.cs u).h ρ' ∈ Ku X u Y.hK := by
      rw [← hh1]; exact hh1K
    have hη1 : ηg = 1 := hNeat ((Y.cs u).h ρ') ηg hmem
    have hη1' : η = 1 := by
      have := congrArg Subtype.val hη1
      rw [hηg] at this
      exact this
    have hsν : s = ν := by rw [hνη, hη1', mul_one]
    subst hsν
    have hsN := hNR D X Y u ρ' s hKL hνG hν1 hν2 hg
    have hs1' : s.1 = 1 := (hΩ ρ').2.2 y.1 hy1 s.1 hsN hsy1
    exact ⟨hGF D X s hνG hs1', rfl⟩

theorem finite_infinite_injective : GFInfInj := by
  intro D X s hs h1
  change s ∈ X.B.I.GFset at hs
  obtain ⟨γ, -, hinf, hfin⟩ := hs
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  have hv := hinf v
  rw [h1, Pi.one_apply] at hv
  have hv' : (X.B.I.P v)⁻¹ * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) *
      X.B.I.P v = 1 := by
    rw [← hv]; simp [uMat]
  have hPu : IsUnit (X.B.I.P v).det := Matrix.isUnit_det_of_left_inverse hv'
  have h2 : (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) = 1 := by
    calc (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v)
        = (X.B.I.P v * (X.B.I.P v)⁻¹) * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) *
            (X.B.I.P v * (X.B.I.P v)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul, Matrix.mul_one]
      _ = X.B.I.P v * ((X.B.I.P v)⁻¹ * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) *
            X.B.I.P v) * (X.B.I.P v)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hv', Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]
  have hγ := Matrix.map_injective (f := ⇑(X.B.I.φ v)) (RingHom.injective _)
    (h2.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)] at hfin
  unfold AutInst.fmat at hfin
  have h2' : s.2 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa using hfin
  exact Prod.ext h1 h2'

theorem nLift_of (hNC : Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel) : NLift := by
  intro D X Y u ρ t ht
  obtain ⟨x, n, hL, rfl, hn⟩ := ht
  have hi := Formalism.L2.SG.Pf.nLamNinf_holds D X u _ x n hL hn
  have hf := Formalism.L2.SG.Pf.nLamNfin_holds D X u _ x n hL hn
  refine ⟨x, Subgroup.mem_inf.2 ⟨Formalism.L2.SG.TermOp.ratLink_mem (X := X) hL,
    Subgroup.subset_closure ⟨fun v => (hi v).1, ⟨hf.1, hf.2.1⟩⟩⟩, rfl, (hNC D X Y u ρ x n hn hL).1⟩

theorem nStrongApprox_of (hD : NDense) : NStrongApprox := by
  intro D X Y u ρ n hKL hn
  set a : X.B.I.Gf := ((Y.cs u).h ρ : X.B.I.Gf) * X.xu u
  have hKo : IsOpen X.K2 := (level_subgroup_isClopen X Y.hK hKL).isOpen
  have hc : Continuous fun m : X.B.I.Gf => a⁻¹ * (m * n) * a :=
    (continuous_const.mul (continuous_id.mul continuous_const)).mul continuous_const
  have hninv : n⁻¹ ∈ X.NfinU u := (nfinGroup_holds (X := X) (u := u)).2 n hn
  obtain ⟨ν, hνG, hν1, hν2, hνU⟩ := hD D X u n⁻¹ hninv _ (hKo.preimage hc)
    (by show a⁻¹ * (n⁻¹ * n) * a ∈ X.K2; rw [inv_mul_cancel, mul_one, inv_mul_cancel]; exact Y.hK.1)
  exact ⟨ν, Subgroup.mem_inf.2 ⟨hνG, Subgroup.subset_closure ⟨fun v => (hν1 v).1, ⟨hν2.1, hν2.2.1⟩⟩⟩, hνU⟩

theorem slab_covering_of_strong_approx (hD : NDense) (hNC : Formalism.L2.SG.TermOp.Vanish.NilradicalConjLevel) (hRL : RatLeviC) (hPD : PsiDdC) :
    SlabCoverC :=
  slabCoverC_of finite_infinite_injective (nStrongApprox_of hD) (nLift_of hNC) nilradical_rational_lattice hRL hPD

end Formalism.L2.SG.Pf.SlabCoverPf
