import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadWMemGoodW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanTie

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem mem_goodL_iff_iotaR (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hU : R.toRealDat.LUnif) (hW : R.toRealDat.models_HW)
    (hidem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g))
    (hψ : LvlPsi R F cG θ) (j : ℕ) (v : (ratDatR R cG kKs hk).WL j) :
    v ∈ goodL D (ratDatR R cG kKs hk) θ j ↔
      GlobalTheory.EigSpanDesc.iotaR R (idxOf D j) v ∈ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j) := by
  have hinj : Function.Injective fun x : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x) := by
    refine (hW _ _).1.comp ((injective_iff_map_eq_zero ((R.FW (idxOf D j)).j (sg0 D A3.A))).2 fun x hx => ?_)
    by_contra hne
    exact ((hU _ _).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hx
  have hact : ∀ (g : G) (x : Fin (R.nW (idxOf D j)) → D.what₂.LL),
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A)
        ((((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g x)) =
      postOn _ (Links.actL (Wc D (idxOf D j)) (R.βW (idxOf D j)) (R.datWp (idxOf D j) R.triv) (R.eG g))
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x)) := fun g x => by
    rw [map_smulₛₗ, map_smul, (hU _ _).2.2, smul_smul, ← map_mul, inv_mul_cancel₀ (Units.ne_zero _), map_one, one_smul]
  have hactL : ∀ (g : G) (x : (ratDatR R cG kKs hk).WL j),
      GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j ((R.eG.trans cG) g) x =
        (((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g x := fun g x => by
    show ((((R.FW (idxOf D j)).chi ((R.eG.trans cG).symm ((R.eG.trans cG) g)) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (R.FW (idxOf D j)).ρ ((R.eG.trans cG).symm ((R.eG.trans cG) g)) x = _
    rw [MulEquiv.symm_apply_apply]
  have hsum : ∀ x : (ratDatR R cG kKs hk).WL j,
      (∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j g) x =
        ∑ g : G, (idemOf A3.A.X).coeff g •
          ((((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g x) := fun x => by
    rw [← finsum_comp_equiv (R.eG.trans cG).toEquiv, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hc : ((D.nexp.eLL0 ((R.eG.trans cG) g) : ↥D.LL0) : D.what₂.LL) = (idemOf A3.A.X).coeff g :=
      D.what₂.embLL.injective ((D.nStage_trivialCharacter_coeff_eq _).trans (hidem g).symm)
    rw [LinearMap.smul_apply, ← hactL g x, ← hc]
    rfl
  have hsmul : ∀ (c : D.what₂.LL) (x : Fin (R.nW (idxOf D j)) → D.what₂.LL),
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) (c • x)) =
        sg0 D A3.A c • (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x) := fun c x => by
    rw [map_smulₛₗ, map_smul]
  have hact2 : ∀ (g : G) (x : (ratDatR R cG kKs hk).WL j),
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A)
        (GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j ((R.eG.trans cG) g) x)) =
      postOn _ (Links.actL (Wc D (idxOf D j)) (R.βW (idxOf D j)) (R.datWp (idxOf D j) R.triv) (R.eG g))
        ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) x)) := fun g x =>
    (congrArg (fun y : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
      (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) y)) (hactL g x)).trans (hact g x)
  have hchain : (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A)
      (∑ g : G, (idemOf A3.A.X).coeff g •
        ((((R.FW (idxOf D j)).chi g : D.what₂.LLˣ) : D.what₂.LL)⁻¹ • (R.FW (idxOf D j)).ρ g v))) =
      ∑ g : G, sg0 D A3.A ((idemOf A3.A.X).coeff g) •
        postOn _ (Links.actL (Wc D (idxOf D j)) (R.βW (idxOf D j)) (R.datWp (idxOf D j) R.triv) (R.eG g))
          ((R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) v)) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smulₛₗ, map_smul]
    exact congrArg _ (hact g v)
  rw [goodL, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, one_smul]
  change _ ↔ (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) v) ∈
    R.toRealDat.Wat (idxOf D j) (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))
  rw [GlobalTheory.LevelForms.mem_wat_iff R.toRealDat F.lv2 hU hW false]
  refine and_comm.trans (and_congr ?_ ?_)
  · constructor
    · intro h p
      have hu : (R.eG.trans cG) (p : G) ∈ Formalism.IndefR.NX.U D.nd := (hψ.1 p).1 p.2
      have h1 : GlobalTheory.HeightCounting.actL D (ratDatR R cG kKs hk) j ((R.eG.trans cG) (p : G)) v =
          (((psiUOf D.nd (NX.xiRed D) θ ⟨_, hu⟩ : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL) • v :=
        Module.End.mem_eigenspace_iff.1 (h ⟨_, hu⟩)
      rw [hψ.2 ⟨p.1, p.2⟩ hu] at h1
      exact (hact2 p v).symm.trans ((congrArg (fun y : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
        (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) y)) h1).trans (hsmul _ v))
    · intro h u
      obtain ⟨u, hu⟩ := u
      obtain ⟨g, rfl⟩ := (R.eG.trans cG).surjective u
      have hg : g ∈ F.P0 := (hψ.1 g).2 hu
      have hp := hψ.2 ⟨g, hg⟩ hu
      refine Module.End.mem_eigenspace_iff.2 (hinj ?_)
      refine (hact2 g v).trans ((h ⟨g, hg⟩).trans ?_)
      rw [hp]
      exact (hsmul _ v).symm
  · rw [hsum]
    exact ⟨fun h => hchain.symm.trans (congrArg (fun y : Fin (R.nW (idxOf D j)) → D.what₂.LL =>
        (R.HW (idxOf D j) (sg0 D A3.A)).e ((R.FW (idxOf D j)).j (sg0 D A3.A) y)) h),
      fun h => hinj (hchain.trans h)⟩

end Core

set_option maxHeartbeats 4000000 in

theorem mem_goodL_iff_of_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x →
    ∀ θ : (∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ), (∀ kk, θ kk ≠ 1) →
      LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → ∀ j, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v : (SOf x).WL j,
        (v ∈ goodL (Dof x) (SOf x) θ j ↔
          GlobalTheory.EigSpanDesc.iotaR x.m.z.R (idxOf (Dof x) j) v ∈
            GlobalTheory.EigRows.goodW x.m.z.R.toRealDat x.m.z.F.lv2 (idxOf (Dof x) j)) := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x _ θ _ hlv j _ _ v
  obtain ⟨_, _, -, hidem, -, -⟩ := x.m.z.pins.keep.grp
  exact mem_goodL_iff_iotaR x.m.z.R x.m.z.F x.m.z.cG (kKsOf x) (hkOf x) θ x.m.intersectionNumber_baseChange.prim.unif
    x.m.z.pins.char.base.models.HW hidem hlv j v

end GlobalTheory.EigSpanTie

end
