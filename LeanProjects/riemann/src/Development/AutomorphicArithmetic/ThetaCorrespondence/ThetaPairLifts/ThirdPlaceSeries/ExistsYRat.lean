import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorBesselExistence
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
namespace GlobalTheory.Fam.RatDec
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem exists_yRat_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ a : XGeo D, IsLineVec a.Lz a.ζ₀ → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → ∃ (y : YRat a) (B : GlobalTheory.Core.Mi.SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) ∧ B.lev = (y.bes 0 D.R.rS h0).lev (a.x 0).vol ∧ B.Adapted (W.S.tr u).wt ∧ GlobalTheory.MiTop.Framed B ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(((D.mem u).A.T : ℕ) : D.host.E) ∧ ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) k)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a hLz hT0
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hN : D.host.xi0 * star D.host.xi0 ≠ 0 := mul_ne_zero hxi (star_ne_zero.2 hxi)
  obtain ⟨lam0, hlam0, hB⟩ := GlobalTheory.Core.Mi.exists_sBes_scaled_dual D W.S.X W.Q.instEq u W.Q.Rl.ψ _ (W.S.tr u)
    hP.bot.idE W.Q.stdChar
  obtain ⟨B, hA, hvA, hz, he, he'⟩ := hB 1 (a.x 0).vol one_ne_zero
  have hz1 : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) k)) :=
    fun k => by rw [hz k, one_mul]
  have hB0 := sbes_norm B hP.bot.idE hz1
  have hI := GlobalTheory.T.exists_thetaLiftSpaces_positiveIndex_with_lineNorms D u (fun j hj => D.X_posDef j hj)
  have hbes : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), ∃ b : BesAt (Yc D j) (D.sp.X j) ρ,
      star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E) := by
    intro j ρ h
    obtain ⟨V, b, hr, hs, hsig, hn⟩ := hI.1 j ρ h
    obtain ⟨b2, hb2⟩ := bes_to_Yc j ρ (by omega) b hr hs hsig
    exact ⟨b2, by rw [hb2]; exact hn⟩
  choose b' hb' using hbes
  have hjac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → Nonempty (JacAt (Yc D (j + 1)) (D.sp.X (j + 1)) ρ) := by
    intro j ρ h
    obtain ⟨V, b, hr, hs, hsig⟩ := hI.2 j ρ h
    exact jac_to_Yc (j + 1) ρ (by omega) b hr hs hsig
  obtain ⟨bes, hbes_def⟩ : ∃ f, f = besF (besOf B) b' := ⟨_, rfl⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    show 0 + 2 * (D.R.m / 2 - 1) + 2 = D.R.m
    obtain ⟨k, hk⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  have hbes0 : bes 0 D.R.rS h0 = besOf B := by rw [hbes_def]; rfl
  have hnorm : ∀ j ρ h, star (bes j ρ h).ζ ⬝ᵥ (bes j ρ h).L.gram *ᵥ (bes j ρ h).ζ *
      (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [hbes_def]; exact besF_norm (besOf B) b' _ _ hB0 hb'
  have hlnk : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), Nonempty (Link ((bes j (σ + 1) h).lev (a.x j).vol)
      (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ) := by
    intro j σ h
    have hn1 := hnorm j (σ + 1) h
    have hn2 := hnorm (j + 1 + 1) σ (idx_step h)
    have e : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
    rw [e, pow_succ] at hn2
    have hrel : star (bes j (σ + 1) h).ζ ⬝ᵥ (bes j (σ + 1) h).L.gram *ᵥ (bes j (σ + 1) h).ζ =
        D.host.xi0 * star D.host.xi0 * (star (bes (j + 1 + 1) σ (idx_step h)).ζ ⬝ᵥ
          (bes (j + 1 + 1) σ (idx_step h)).L.gram *ᵥ (bes (j + 1 + 1) σ (idx_step h)).ζ) := by
      apply mul_right_cancel₀ (pow_ne_zero (j / 2) hN)
      rw [hn1]
      linear_combination -hn2
    have hl := (GlobalTheory.Unf.LinkExist.link_of_norm D (σ + 1) ((bes j (σ + 1) h).lev (a.x j).vol)
      (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ D.host.xi0
      (bes (j + 1 + 1) σ (idx_step h)).line hrel).2
    rwa [div_self hxi, one_smul] at hl
  have hvol := GlobalTheory.Unf.VolExist.measures_exist D
  have hrelT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), star (-D.host.xi0 ^ (D.R.m / 2)) * (-D.host.xi0 ^ (D.R.m / 2)) *
      (star (bes j 0 h).ζ ⬝ᵥ (bes j 0 h).L.gram *ᵥ (bes j 0 h).ζ) =
        -(D.host.xi0 * star D.host.xi0) * (star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀) := by
    intro j h
    have hn := hnorm j 0 h
    have e : D.R.m / 2 = j / 2 + 1 := by omega
    have hl : star (-D.host.xi0 ^ (D.R.m / 2)) * (-D.host.xi0 ^ (D.R.m / 2)) =
        (D.host.xi0 * star D.host.xi0) ^ (D.R.m / 2) := by
      rw [star_neg, star_pow, neg_mul_neg, mul_pow]; ring
    rw [hl, e, pow_succ, hT0]
    linear_combination (D.host.xi0 * star D.host.xi0) * hn
  refine ⟨⟨bes, fun j ρ h => (hjac j ρ h).some, fun j σ h => (hlnk j σ h).some, fun j σ h => (hvol.2.2.1 _ _).some,
    fun j h => Matrix.of fun i k => -D.host.xi0 ^ (D.R.m / 2) * (bes j 0 h).ζ i / a.ζ₀ k⟩, B, h0, ?_, ?_, hA,
    ⟨1, lam0, one_ne_zero, hlam0, hz, he, he'⟩, hB0, hz1⟩
  · intro j h
    exact tau_line (bes j 0 h).line.1 hLz.1 _ _ _ _ _ _ hLz.2 (hrelT j h)
  · show B.lev = (bes 0 D.R.rS h0).lev (a.x 0).vol
    rw [hbes0, ← hvA]
    rfl
end GlobalTheory.Fam.RatDec
end
end
