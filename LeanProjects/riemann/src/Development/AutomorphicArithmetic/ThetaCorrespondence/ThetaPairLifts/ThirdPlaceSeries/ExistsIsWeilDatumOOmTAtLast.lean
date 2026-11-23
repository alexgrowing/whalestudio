import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroLocalScalars
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GVec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DatumTopStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEqStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.GVecAt
section Gen
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
end Gen
end GlobalTheory.GVecAt
namespace GlobalTheory.GVecAt
theorem datum_mid_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ (((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := _root_.GlobalTheory.T.descent_data_chain_step_alt
theorem datum_top_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (M' : GlobalTheory.FinPl.Lat D.sp.X') (o' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), IsSelfDualC (Yc D (j + 1)) M ∧ IsSelfDualC D.sp.X' M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) (comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) ∧ ((omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0 → comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) = κ • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) := _root_.GlobalTheory.T.descent_data_top_step_alt
section Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
theorem exists_isWeilDatumO_omT_at_last (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ χS χT, IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' χS χT
    (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) := by
  have hω := W.Q.charW.base.chain.ωX W.P.A3.A.μ0
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X'
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact hω
  exact ⟨_, _, key _ (GlobalTheory.Fam.idx_top h)⟩
end Fam
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∃ s : ℕ → ℂ, (∀ j, s j ≠ 0) ∧ _root_.GlobalTheory.Fam.GVectorCondition f v s := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR
  have fin : ∀ {S T : HSp D} (P : GlobalTheory.FinPl.Pl D → Prop) (e : WO S T →₀ ℂ), IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) →
      GlobalTheory.FinPl.CombAt P e → IsFinComb e := fun P e hψ he =>
    ((GlobalTheory.DisjComb.main D (_root_.GlobalTheory.Fam.pk_z W).ψ hψ _ _ P (fun _ => False) (fun _ _ h => h)).2.1 e he).1
  have mid : ∀ j, j + 1 < D.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∀ P, ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1))
        (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D j) (Yc D (j + 1)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)))
          (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) ((_root_.GlobalTheory.Fam.pk_z W).vac j) P)) = c • comb f.c.ψ _ _ (v.eG j) (v.Ψ j P a a') := by
    intro j hj
    by_cases hex : ∃ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀
    swap
    · exact ⟨1, one_ne_zero, fun d hd => absurd ⟨d, hd⟩ hex⟩
    obtain ⟨d₀, hd₀⟩ := hex
    obtain ⟨M, M', o', hM, hM', ho', hg0, ho'v, ho'nz, κ, hκ, hdat⟩ := _root_.GlobalTheory.GVecAt.datum_mid_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT
      n G pl hGP hGR j hj d₀ hd₀
    obtain ⟨o, ho, hΨ⟩ := hVT.Ψ j hj
    have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := hd₀.2.1.1
    have hinf : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hd₀.2.1.2.inf
    have hvth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).vac j) := hd₀.2.1.2.theta
    have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
    have hb : f.g.b j ∈ GfC _ := hVT.b j ▸ hv.b j
    have hb' : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
    have hΨ1 : v.Ψ j 1 1 1 = comb f.c.ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) := by
      rw [hΨ, GlobalTheory.FiniteFock.pureTensorO_one, one_mul, one_mul]
    have hov := vac_mono (· ∈ v.gP) (hΨ1 ▸ hv.Ψ j hj 1 1 (one_mem _) 1 (one_mem _))
    have honz : comb f.c.ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 := by
      intro h0
      obtain ⟨P, hP⟩ := hVT.nz.1 j hj
      apply hP
      rw [hΨ, one_mul, one_mul]
      have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ _ _ _ hWe hinf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (f.g.b j) (f.g.b (j + 1))
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) _ hvth P
      rw [hfin.2, comb_pureTensorO hstd hinf _ _ _ _ (fin _ o hstd ho) (hWe.om_pres _ _ hvth), h0, pureTensorO_zero]
    have hg0nz : (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) ≠ 0 := fun h0 =>
      honz (by rw [h0]; exact comb_zero _)
    obtain ⟨c, hc⟩ := scalar D f.c.ψ _ _ M (v.N j) M' (v.N (j + 1)) v.gP o o' _ hstd hM hM' (hv.sd j (by omega))
      (hv.sd (j + 1) hj) ho ho' hg0 hov ho'v (ho'nz hg0nz)
    have hc0 : c ≠ 0 := fun h0 => honz (by rw [hc, h0, zero_smul])
    refine ⟨κ / c, div_ne_zero hκ hc0, fun d hd P a ha a' ha' => ?_⟩
    have hbase : (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) =
        (κ / c) • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
      rw [hdat d hd, hc, comb_smul, smul_smul, div_mul_cancel₀ _ hc0]
    rw [hΨ P a a']
    exact fock hinf hWe _ _ _ _ (fin _ d hstd hd.1) (fin _ o hstd ho) (fin _ _ hstd (hv.atG j).1) hvth hb hb' hbase P ha ha'
  have top : ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ c : ℂ, c ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d →
      ∀ P, omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (pureTensorO f.c.ψ f.c.θ (Yc D (j + 1)) D.sp.X'
        (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) P)) =
        c • comb f.c.ψ _ _ (v.eGT j h) (v.ΨT j h P) := by
    intro j h
    by_cases hex : ∃ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀
    swap
    · exact ⟨1, one_ne_zero, fun d hd => absurd ⟨d, hd⟩ hex⟩
    obtain ⟨d₀, hd₀⟩ := hex
    obtain ⟨M, M', o', hM, hM', ho', hg0, ho'v, ho'nz, κ, hκ, hdat⟩ := _root_.GlobalTheory.GVecAt.datum_top_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT
      n G pl hGP hGR j h d₀ hd₀
    obtain ⟨o, ho, hΨ⟩ := hVT.ΨT j h
    have hstd : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := hd₀.2.1.1
    have hinf : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := hd₀.2.1.2.inf
    have hvth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) := hd₀.2.1.2.theta
    obtain ⟨χS, χT, hWe⟩ := _root_.GlobalTheory.GVecAt.exists_isWeilDatumO_omT_at_last W j h
    have hb : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
    have hb' : f.g.bT ∈ GfC _ := hVT.bT.1 ▸ hv.bT
    have hΨ1 : v.ΨT j h 1 = comb f.c.ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) := by
      rw [hΨ, GlobalTheory.FiniteFock.pureTensorO_one]
    have hov := vac_mono (· ∈ v.gP) (hΨ1 ▸ hv.ΨT j h 1)
    have honz : comb f.c.ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0 := by
      intro h0
      obtain ⟨P, hP⟩ := hVT.nz.2 j h
      apply hP
      rw [hΨ]
      have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ _ _ _ _ _ hWe hinf (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (f.g.b (j + 1)) f.g.bT
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
        (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) _ hvth P
      rw [hfin.2, comb_pureTensorO hstd hinf _ _ _ _ (fin _ o hstd ho) (hWe.om_pres _ _ hvth), h0, pureTensorO_zero]
    have hg0nz : omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) ≠ 0 := fun h0 =>
      honz (by rw [h0]; exact comb_zero _)
    obtain ⟨c, hc⟩ := scalar D f.c.ψ _ _ M (v.N (j + 1)) M' v.NT v.gP o o' _ hstd hM hM' (hv.sd (j + 1) (by omega))
      hv.sdT ho ho' hg0 hov ho'v (ho'nz hg0nz)
    have hc0 : c ≠ 0 := fun h0 => honz (by rw [hc, h0, zero_smul])
    refine ⟨κ / c, div_ne_zero hκ hc0, fun d hd P => ?_⟩
    have hbase : omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) =
        (κ / c) • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) := by
      rw [hdat d hd, hc, comb_smul, smul_smul, div_mul_cancel₀ _ hc0]
    rw [hΨ P]
    have := fock hinf hWe (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) (fin _ d hstd hd.1) (fin _ o hstd ho) (fin _ _ hstd ((hv.atG j).2.2 h)) hvth hb hb' hbase P
      (one_mem (GinfC _)) (one_mem (GinfC _))
    simpa only [one_mul] using this
  choose cm hcm using mid
  choose ct hct using top
  let s : ℕ → ℂ := fun i => if hi : i + 1 < D.R.m then cm i hi else
    match i with
    | 0 => 1
    | k + 1 => if hk : k + 2 * 0 + 2 = D.R.m then ct k hk else 1
  refine ⟨s, fun i => ?_, fun j hj d hd P a ha a' ha' => ?_, fun j h d hd P => ?_⟩
  · show (if hi : i + 1 < D.R.m then cm i hi else
      (match i with
      | 0 => 1
      | k + 1 => if hk : k + 2 * 0 + 2 = D.R.m then ct k hk else 1)) ≠ 0
    split_ifs with hi
    · exact (hcm i hi).1
    · split
      · exact one_ne_zero
      · split_ifs with hk
        · exact (hct _ hk).1
        · exact one_ne_zero
  · have hs : s j = cm j hj := dif_pos hj
    rw [hs]
    exact (hcm j hj).2 d hd P a ha a' ha'
  · have hs : s (j + 1) = ct j h := by
      show (if hi : j + 1 + 1 < D.R.m then cm (j + 1) hi else if hk : j + 2 * 0 + 2 = D.R.m then ct j hk else 1) = ct j h
      rw [dif_neg (by omega), dif_pos h]
    rw [hs]
    exact (hct j h).2 d hd P
end GlobalTheory.GVecAt
end
end
