import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCharacterTimesInverseUnitary
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
open NumberField
noncomputable section
namespace GlobalTheory.CovTop
open Formalism.L2.DIV
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem chi_mul_psi_inv_mem_core_alt (p : GlobalTheory.BigTop.PtAt ex Csz) (i : Fin D.R.m) : p.PointConditions' → RecTied D L →
    ∀ u : (p.F.lv2.lvl false).P, (((p.R.toRealDat.FW i).chi u * (p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ∈
      Set.range (algebraMap p.T.Q.c.F D.what₂.LL) := by
  intro _ _ u
  have hB := p.charW.base
  obtain ⟨ψ0, -, hlev, -⟩ := hB.grp.levels
  have hL := hB.lev
  have hN0 : p.T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := p.T.Q.l.three_le; omega) p.T.Q.l.A_pos.ne'
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hN : ∀ PP : p.R.Pg, (p.T.Q.l.M' : kP PP.1) = 0 := by
    intro PP
    obtain ⟨k, hk⟩ := (hL.Pg PP.1).1 PP.2
    have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.1.under (𝓞 D.host.K)).asIdeal := by
      rw [hk]; exact p.R.C.P.pb_over k
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
      change _ ∈ Ideal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) PP.1.asIdeal at h2
      rwa [Ideal.mem_comap, map_natCast] at h2
    have h3 : ((D.host.g k : ℕ) : kP PP.1) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.1.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h1
    have hk' : D.host.g k ∣ p.T.Q.l.M' := by
      refine dvd_trans ?_ (Nat.dvd_lcm_left p.T.Q.l.M p.T.Q.l.A)
      rw [hM]
      fin_cases k
      exacts [dvd_mul_right _ _, dvd_mul_left _ _]
    obtain ⟨c, hc⟩ := hk'
    rw [hc, Nat.cast_mul, h3, zero_mul]
  have hu : p.R.eG u ∈ (p.R.levR p.F.lv2 false).H := by
    show p.R.eG.symm.toMonoidHom (p.R.eG u) ∈ (p.F.lv2.lvl false).P
    simp
  have key : ∀ X : LevelP p.R.Pg D.R.r ℂ, X = P0 p.R.Pg D.R.r ψ0 → ∀ g (hg : g ∈ X.H),
      (∀ PP, g PP ∈ unip (kP PP.1) D.R.r) ∧ X.chi ⟨g, hg⟩ ^ p.T.Q.l.M' = 1 := by
    rintro X rfl g hg
    exact ⟨fun PP => (Subgroup.mem_pi _).1 hg PP (Set.mem_univ _), unipotentTypeLevel_char_pow_eq_one _ _ ψ0 _ hN _⟩
  obtain ⟨hun, hpow⟩ := key _ hlev _ hu
  have e1 : (p.R.levR p.F.lv2 false).chi ⟨p.R.eG u, hu⟩ =
      Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((p.F.lv2.lvl false).ψ u) := by
    show Units.map _ ((p.F.lv2.lvl false).ψ _) = _
    congr 2
    exact Subtype.ext (by show p.R.eG.symm (p.R.eG u) = u; exact p.R.eG.symm_apply_apply _)
  have h5 : (((p.F.lv2.lvl false).ψ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    apply D.what₂.embLL.injective
    have := congrArg (fun z : ℂˣ => (z : ℂ)) (e1 ▸ hpow)
    simpa using this
  have hchi : (p.R.toRealDat.FW i).chi u = 1 := by
    apply Units.ext
    apply D.what₂.embLL.injective
    rw [hB.grp.chiW i u, Finset.prod_eq_one (fun PP _ => by rw [det_of_mem_unip (hun PP), map_one, Units.val_one]),
      Units.val_one, map_one]
  rw [hchi, one_mul]
  have hy : (((p.F.lv2.lvl false).ψ⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) ^ p.T.Q.l.M' = 1 := by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_pow, h5, inv_one]
  have hz : IsPrimitiveRoot (⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta p.T.Q.l.M', p.T.Q.c.zeta_mem⟩ : p.T.Q.c.F) p.T.Q.l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := p.T.Q.c.F.val) (Complex.isPrimitiveRoot_exp _ hN0) Subtype.val_injective
  have hz' := hz.map_of_injective (f := algebraMap p.T.Q.c.F D.what₂.LL) (algebraMap p.T.Q.c.F D.what₂.LL).injective
  haveI : NeZero p.T.Q.l.M' := ⟨hN0⟩
  obtain ⟨k, -, hk⟩ := hz'.eq_pow_of_pow_eq_one hy
  exact ⟨_ ^ k, by rw [map_pow, hk]⟩
end GlobalTheory.CovTop
end
end
