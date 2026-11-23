import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DdPowConj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgnConjIntUp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocGlobInt

noncomputable section

open scoped Classical Matrix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_ddS_pow (t : 𝓞 D.host.F) (ht : t ∈ differentIdeal ℤ (𝓞 D.host.F)) (k : ℕ) :
    (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ k : 𝓞 D.host.E) : D.host.E) ∈ ddS D ^ k := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈
      Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :=
    Ideal.mem_map_of_mem _ ht
  have h2 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) ∈ ddS D :=
    FractionalIdeal.mem_coeIdeal_of_mem _ h1
  have h3 := Submodule.pow_mem_pow (ddS D : Submodule (𝓞 D.host.E) D.host.E) h2 k
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
  push_cast
  exact h3

theorem dict_holds (Zd : LocDat D) : Formalism.L2.SG.Pf.TupGlob.Dict Zd := by
  intro A B hA hB hloc
  have hAu : IsLoUni A := fun i j => ⟨hA.2 i j, fun h => h ▸ hA.1 i⟩
  have hBu : IsUpUni B := Formalism.L2.SG.Pf.TupGlob.isUpUni_of hB
  have hsh : ∀ p, Formalism.L2.SG.Pf.StabIntSh.LocEntryShape D p A B := fun p =>
    (Formalism.L2.SG.Pf.StabIntSh.loc_iff Formalism.L2.SG.Pf.StabIntSh.locShapeL Formalism.L2.SG.Pf.StabIntSh.locShapeG (p := p)
      Zd.agree hAu hBu).1
      ⟨by rw [lOf_eq]; exact (hloc p).1, by rw [ρOf_eq]; exact Formalism.L2.SG.Pf.FibQ.sgn_conj_intUp Zd p (hloc p).2⟩
  have hES := (Formalism.L2.SG.Pf.StabIntSh.glob_iff Formalism.L2.SG.Pf.StabIntSh.locGlob Formalism.L2.SG.Pf.StabIntSh.shapeNZ A B).1 hsh
  refine ⟨fun c b hcb x hx => ?_, fun c b hcb x hx => ?_, fun P hP c b => ?_⟩
  · rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF]
    exact mem_aaF hcb hx (ddPow_conj Zd (by have := b.isLt; omega) (hES b c hcb).1)
  · rw [sg_entry]
    exact mem_aaF hcb hx (hES b c hcb).2.1
  · rcases lt_trichotomy c b with h | h | h
    · have hq := (hES b c h).2.2
      unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at hq
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hq
      obtain ⟨z, hz, hzy⟩ := hq
      obtain ⟨t, ht, htP⟩ := diff_avoid P hP
      have hk : b.val - c.val ≤ D.R.rS := by have := b.isLt; omega
      have hz' := ddPow_conj Zd hk hz
      have hprod := FractionalIdeal.mul_mem_mul (mem_ddS_pow t ht (b.val - c.val)) hz'
      unfold Formalism.L2.SG.Pf.StabIntSh.ddPow at hprod
      rw [← zpow_natCast, ← zpow_add₀ (PI.NRCW.ddS_ne_zero D), add_neg_cancel, zpow_zero] at hprod
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
      refine ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ (b.val - c.val), fun hs => htP (P.isPrime.mem_of_pow_mem _ hs),
        o, ?_⟩
      rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, sg_entry]
      have e1 : D.conjF (A b c) - Formalism.L2.SG.Pf.StabIntSh.bt D B c b =
          D.conjF (algebraMap (𝓞 D.host.E) D.host.E ((gS D : ℕ) : 𝓞 D.host.E) * z) := by
        have := congrArg D.conjF hzy
        simpa only [map_sub, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol] using this
      rw [e1, map_mul, map_natCast, map_natCast, mul_left_comm, ← ho]
    · subst h
      refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.1 c, hB.1 c, ← pow_add, ← two_mul, pow_mul]
    · refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.2 b c h, hB.2 b c h]

end Formalism.L2.SG.Pf.FibD
