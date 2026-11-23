import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq

noncomputable section
open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frameExp_cast (r l : ℕ) (hl : l ≤ r + 1) :
    ((frameExp r l : ℕ) : ℤ) = ∑ a ∈ Finset.range l, ((r : ℤ) - a) := by
  induction l with
  | zero => simp [frameExp]
  | succ l ih =>
    have h1 : frameExp r (l + 1) = frameExp r l + (r + 1 - (l + 1)) := by
      unfold frameExp
      rw [Finset.sum_Icc_succ_top (by omega)]
    have h2 : ((r + 1 - (l + 1) : ℕ) : ℤ) = (r : ℤ) - l := by omega
    rw [h1, Nat.cast_add, ih (by omega), Finset.sum_range_succ, h2]

theorem nloc_eq (D : D7) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) =
      |((Algebra.norm ℚ x : ℚ) : ℝ)| * (Ideal.absNorm (dI D) : ℝ) ^ (-(2 * (frameExp r l : ℤ))) := by
  unfold Nloc
  rw [map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 D.host.E), map_zpow₀,
    show ddS D = ((dI D : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) from rfl,
    FractionalIdeal.coeIdeal_absNorm]
  push_cast
  rfl

theorem norm_star (D : D7) (x : D.host.E) : Algebra.norm ℚ (star x) = Algebra.norm ℚ x := by
  have := Algebra.norm_eq_of_algEquiv ((starRingAut : D.host.E ≃+* D.host.E).toRatAlgEquiv) x
  simpa using this

theorem nloc_ne_zero (D : D7) (hd : dI D ≠ ⊥) (r l : ℕ) (x : D.host.E) :
    ((Nloc (ddS D) r l x : ℚ) : ℝ) ≠ 0 ↔ x ≠ 0 := by
  have hA : (Ideal.absNorm (dI D) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 hd)
  rw [nloc_eq, mul_ne_zero_iff, abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]
  simp only [ne_eq, zpow_neg, inv_eq_zero, and_iff_left_iff_imp]
  intro _
  exact zpow_ne_zero _ hA

theorem T_eq {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ}
    (F G : Formalism.HermitianLatticeCounting.S6.FlagD H r) (h : G.e (Fin.last r) - F.e (Fin.last r) ∈ F.X) : G.T = F.T := by
  have hX : ∀ w : V, (∀ a : Fin r, H.B (F.e a.castSucc) w = 0) → ∀ y ∈ F.X, H.B y w = 0 := by
    intro w hw y hy
    have hle : F.X ≤ LinearMap.ker (H.B.flip w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, -, rfl⟩
      simpa using hw b
    simpa using hle hy
  set x := G.e (Fin.last r) - F.e (Fin.last r) with hxdef
  have hxz : H.B x (F.e (Fin.last r)) = 0 := hX _ F.zperp x h
  have hzx : H.B (F.e (Fin.last r)) x = 0 := by rw [← H.herm, hxz, star_zero]
  have hxx : H.B x x = 0 := by
    refine hX x (fun a => ?_) x h
    have := hX (F.e a.castSucc) (fun b => F.iso b a) x h
    rw [← H.herm, this, star_zero]
  have hG : G.e (Fin.last r) = F.e (Fin.last r) + x := by rw [hxdef]; abel
  have h1 := G.zz
  rw [hG] at h1
  simp only [map_add, LinearMap.add_apply, hxz, hzx, hxx, F.zz, add_zero] at h1
  exact (neg_inj.1 h1).symm

end GlobalTheory.TypeAsm.HasLabelling

namespace GlobalTheory.TypeAsm
open GlobalTheory.TypeAsm.HasLabelling
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem labC : LabC := by
  intro D large₂ X Y u hS t N hN
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := by
    obtain ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩ := hS
    exact hH.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, hj, hDl, -, -, -⟩ :=
    GlobalTheory.DegAsm.adapt_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (Ft t) (dI D) N hN
  have hII : Formalism.HermitianLatticeCounting.S6.II (F0 X u) (Ft t) = Isp (lf D (X.Fu u)).fl (frq X t.rep).fl := nf_II _ _ _ _
  have hjT : N.j = jT t := by rw [hj, hII]; rfl
  have hjle : jT t ≤ D.R.rS := by unfold jT; omega
  have hnf : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl) :=
    fun l hl => nf_Dl _ _ _ _ l hl
  have hd : N.𝔡 = dI D := hN.1
  have hdne : dI D ≠ ⊥ := hd ▸ N.𝔡_ne
  have key : ∀ l, l ≤ jT t → N.nD l = ((Nloc (ddS D) D.R.rS l (labT t l) : ℚ) : ℝ) := by
    intro l hl
    have hl' : l ≤ D.R.rS + 1 := by omega
    have hlab : labT t l = star (Formalism.HermitianLatticeCounting.S6.Dl (F0 X u) (Ft t) l hl') := by
      simp only [labT, if_pos hl]
      exact hnf l hl'
    unfold GlobalTheory.DegCnt.NF.nD
    rw [dif_pos hl', hDl l hl', nloc_eq, hlab, norm_star, hd, frameExp_cast _ _ hl']
  refine ⟨hjT, ?_, ?_, ?_, ?_⟩
  · have hz : N.F.e (Fin.last D.R.rS) - (F0 X u).e (Fin.last D.R.rS) ∈ (F0 X u).X := hN.2.1 (Fin.last _)
    have h1 : ((N.T : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := by
      rw [← N.hT, T_eq (F0 X u) N.F hz]
      rfl
    exact_mod_cast h1
  · unfold GlobalTheory.DegCnt.NF.Del
    rw [hjT, key _ le_rfl]
    rfl
  · unfold GlobalTheory.DegCnt.NF.Db DbL
    rw [hjT]
    have hset : (Finset.Icc 1 (jT t)).filter (fun l => N.nD l ≠ 0) = k2ends D (jT t) (labT t) := by
      ext l
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2] at h3
        exact (nloc_ne_zero D hdne _ _ _).1 h3
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨h1, h2⟩, ?_⟩
        rw [key l h2]
        exact (nloc_ne_zero D hdne _ _ _).2 h3
    rw [hset]
    refine Finset.prod_congr rfl fun l hl => ?_
    have h2 : l ≤ jT t := by
      simp only [k2ends, Finset.mem_filter, Finset.mem_Icc] at hl
      exact hl.1.2
    exact key l h2
  · funext l
    unfold GlobalTheory.DegAsm.lab
    by_cases hl : l ≤ jT t
    · have hl' : l ≤ D.R.rS + 1 := by omega
      rw [dif_pos ⟨hl, hl'⟩]
      simp only [labT, if_pos hl]
      rw [hnf l hl', star_star]
    · rw [dif_neg (fun h => hl h.1)]
      simp only [labT, if_neg hl, star_zero]

end GlobalTheory.TypeAsm
