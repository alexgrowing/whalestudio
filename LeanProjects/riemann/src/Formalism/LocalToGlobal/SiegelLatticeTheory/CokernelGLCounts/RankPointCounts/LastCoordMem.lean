import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemOfBcPMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IotaFIntMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocEqOfLocFEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemInvCoeIdeal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentCoprimeSplit

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdCut
open Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LocalXS

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

def uF (b : Fin (D.R.rS + 1)) : (D.s.atP p).Ep := sgnP' D p b * frFac Zd.δ p b

theorem locF'_eq {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') (b : Fin (D.R.rS + 1)) :
    locF' Zd p F' b = uF Zd p b • baseChange₂ D p (frame F' b) := rfl

theorem sgnP'_mem (b : Fin (D.R.rS + 1)) : sgnP' D p b ∈ (D.s.atP p).O := by
  haveI := (D.s.atP p).lf
  rw [(D.s.atP p).O_def]
  refine ⟨Polynomial.X ^ 2 - 1, Polynomial.monic_X_pow_sub_C 1 (by norm_num), ?_⟩
  have h := sgnP'_sq p b
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one]
  rw [sq, h, sub_self]

theorem frFac_unit (b : Fin (D.R.rS + 1)) : IsUnit (frFac Zd.δ p b) := by
  rw [frFac_eq Zd p b]
  refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
  exact pow_ne_zero _ (inv_ne_zero (yP_ne Zd p))

theorem uF_unit (b : Fin (D.R.rS + 1)) : IsUnit (uF Zd p b) :=
  (show IsUnit (sgnP' D p b) from ⟨⟨_, _, sgnP'_sq p b, sgnP'_sq p b⟩, rfl⟩).mul (frFac_unit Zd p b)

end LocalXS

section LocalXS2

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem frame_cs {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') (a : Fin D.R.rS) :
    frame F' a.castSucc = F'.fl.e a := by
  simp [frame, FlagG.fvec]

theorem exists_baseChange_flagVector_eq_smul {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') (a : Fin D.R.rS) :
    ∃ w : (D.s.atP p).Ep, baseChange₂ D p (F'.fl.e a) = w • locF' Zd p F' a.castSucc := by
  obtain ⟨U, hU⟩ := uF_unit Zd p a.castSucc
  refine ⟨((U⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep), ?_⟩
  rw [locF'_eq, ← hU, smul_smul, Units.inv_mul, one_smul, frame_cs]

theorem span_bcP_X {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') :
    Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp F' : Set (VS D).V)) =
      Submodule.span (D.s.atP p).Ep (Set.range fun a : Fin D.R.rS => locF' Zd p F' a.castSucc) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span D.host.E (Set.range F'.fl.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨w, hw⟩ := exists_baseChange_flagVector_eq_smul Zd p F' a
      rw [SetLike.mem_coe, hw]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | zero => rw [SetLike.mem_coe, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [SetLike.mem_coe, map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [SetLike.mem_coe, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
      exact Submodule.smul_mem _ _ hy
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    show locF' Zd p F' a.castSucc ∈ _
    rw [locF'_eq, frame_cs]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨F'.fl.e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩)

theorem mem_O_M {x : (D.s.atP p).Ep} (hx : x ∈ (D.s.atP p).O) : x ∈ (Zd.M p).L.O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.hO Zd p]; exact hx

theorem smul_mem_O {N : Submodule (Zd.M p).L.O (Vp D p)} {c : (D.s.atP p).Ep} (hc : c ∈ (Zd.M p).L.O)
    {v : Vp D p} (hv : v ∈ N) : c • v ∈ N :=
  N.smul_mem ⟨c, hc⟩ hv

set_option maxHeartbeats 1000000 in

theorem latP_XS {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') :
    lattice₂ D Zd.M p (XS D F'.fl) =
      Submodule.span (Zd.M p).L.O (Set.range fun a : Fin D.R.rS => locF' Zd p F' a.castSucc) := by
  have hdiff := Formalism.L2.SG.Pf.locDiffC_holds D Zd p
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ XS D F'.fl := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, x, hx, rfl⟩ := hz
      have hmem : (D.s.atP p).ιE x ∈ Submodule.span (Zd.M p).L.O {frFac Zd.δ p a.castSucc} := by
        rw [← hdiff a.castSucc]
        exact Submodule.subset_span ⟨x, by simpa using hx, rfl⟩
      obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hmem
      have hs : sgnP' D p a.castSucc ∈ (Zd.M p).L.O := mem_O_M Zd p (sgnP'_mem p a.castSucc)
      have e : baseChange₂ D p (x • F'.fl.e a) = ((o : (D.s.atP p).Ep) * sgnP' D p a.castSucc) • locF' Zd p F' a.castSucc := by
        rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, ← ho, locF'_eq, uF, frame_cs, smul_smul]
        congr 1
        rw [Subring.smul_def, smul_eq_mul]
        linear_combination (-((o : (D.s.atP p).Ep) * frFac Zd.δ p a.castSucc)) * sgnP'_sq p a.castSucc
      rw [SetLike.mem_coe, e]
      exact smul_mem_O Zd p (Subring.mul_mem _ o.2 hs) (Submodule.subset_span ⟨a, rfl⟩)
    | zero => rw [SetLike.mem_coe, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [SetLike.mem_coe, map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [SetLike.mem_coe, Formalism.L2.SG.Pf.LocalDenominators.oE_smul, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
      have hc : (D.s.atP p).ιE (c : D.host.E) ∈ (Zd.M p).L.O :=
        mem_O_M Zd p (Formalism.L2.SG.Pf.PCountEx.iotaE_mem_O (fun q => D.s.atP q) p c)
      exact smul_mem_O Zd p hc hy
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have key : ∀ t ∈ Submodule.span (Zd.M p).L.O ((D.s.atP p).ιE '' ((ddS D ^ (-((D.R.rS : ℤ) - ((a.castSucc :
        Fin (D.R.rS + 1)) : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)),
        t • baseChange₂ D p (F'.fl.e a) ∈ lattice₂ D Zd.M p (XS D F'.fl) := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨x, hx, rfl⟩ := ht
        rw [← Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
        rw [Fin.val_castSucc] at hx
        exact Submodule.subset_span ⟨x • F'.fl.e a, Submodule.subset_span ⟨a, x, hx, rfl⟩, rfl⟩
      | zero => rw [zero_smul]; exact zero_mem _
      | add s t _ _ hs ht => rw [add_smul]; exact add_mem hs ht
      | smul o t _ ht => rw [Subring.smul_def, smul_eq_mul, mul_smul]; exact smul_mem_O Zd p o.2 ht
    have hf : frFac Zd.δ p a.castSucc ∈ Submodule.span (Zd.M p).L.O ((D.s.atP p).ιE '' ((ddS D ^ (-((D.R.rS : ℤ) -
        ((a.castSucc : Fin (D.R.rS + 1)) : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Set D.host.E)) := by
      rw [hdiff a.castSucc]; exact Submodule.mem_span_singleton_self _
    have hs : sgnP' D p a.castSucc ∈ (Zd.M p).L.O := mem_O_M Zd p (sgnP'_mem p a.castSucc)
    show locF' Zd p F' a.castSucc ∈ _
    rw [locF'_eq, uF, frame_cs, mul_smul]
    exact smul_mem_O Zd p hs (key _ hf)

end LocalXS2

section Prim

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {O : Subring K} {n : ℕ}

theorem inter_span_eq (N : Submodule O V) (f : Fin (n + 1) → V) (hN : ∀ a, f a ∈ N) (hLI : LinearIndependent K f)
    (hpr : ∀ x ∈ N, x ∈ Submodule.span K (Set.range f) → x ∈ Submodule.span O (Set.range f)) :
    (N : Set V) ∩ Submodule.span K (Set.range fun a : Fin n => f a.castSucc) =
      Submodule.span O (Set.range fun a : Fin n => f a.castSucc) := by
  ext x
  constructor
  · rintro ⟨hxN, hxS⟩
    have hx1 : x ∈ Submodule.span K (Set.range f) :=
      Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, rfl⟩) hxS
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hpr x hxN hx1)
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxS
    have hz : ∑ b, (Fin.snoc (α := fun _ => K) (fun a : Fin n => (o a.castSucc : K) - d a)
        (o (Fin.last n) : K) b) • f b = 0 := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, sub_smul, Finset.sum_sub_distrib]
      have e1 : ∑ b, (o b : K) • f b = x := by rw [← ho]; simp only [Subring.smul_def]
      rw [Fin.sum_univ_castSucc] at e1
      rw [hd]
      rw [sub_add_eq_add_sub, e1, sub_self]
    have hg := Fintype.linearIndependent_iff.1 hLI _ hz
    have hl : (o (Fin.last n) : K) = 0 := by simpa [Fin.snoc_last] using hg (Fin.last n)
    have ex : x = ∑ a : Fin n, o a.castSucc • f a.castSucc := by
      rw [← ho, Fin.sum_univ_castSucc, Subring.smul_def (o (Fin.last n)), hl, zero_smul, add_zero]
    rw [SetLike.mem_coe, ex]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro hx
    refine ⟨?_, ?_⟩
    · exact (Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hN a.castSucc)) hx
    · exact Submodule.span_le_restrictScalars O K _ hx

theorem last_coord_mem (N : Submodule O V) (f : Fin (n + 1) → V) (hLI : LinearIndependent K f)
    (hpr : ∀ x ∈ N, x ∈ Submodule.span K (Set.range f) → x ∈ Submodule.span O (Set.range f))
    (c : K) (y l : V) (hy : y ∈ Submodule.span K (Set.range fun a : Fin n => f a.castSucc)) (hl : l ∈ N)
    (hly : l = c • f (Fin.last n) - y) : c ∈ O := by
  have hl1 : l ∈ Submodule.span K (Set.range f) := by
    rw [hly]
    refine sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
      (Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨a.castSucc, rfl⟩) hy)
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hpr l hl hl1)
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
  have hz : ∑ b, (Fin.snoc (α := fun _ => K) (fun a : Fin n => (o a.castSucc : K) + d a)
      ((o (Fin.last n) : K) - c) b) • f b = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_last, Fin.snoc_castSucc, add_smul, sub_smul, Finset.sum_add_distrib]
    have e1 : ∑ b, (o b : K) • f b = l := by rw [← ho]; simp only [Subring.smul_def]
    rw [Fin.sum_univ_castSucc] at e1
    rw [hd]
    have : ∑ a : Fin n, (o a.castSucc : K) • f a.castSucc + (o (Fin.last n) : K) • f (Fin.last n) = c • f (Fin.last n) - y := by
      rw [e1, hly]
    calc _ = (∑ a : Fin n, (o a.castSucc : K) • f a.castSucc + (o (Fin.last n) : K) • f (Fin.last n)) -
          (c • f (Fin.last n) - y) := by abel
      _ = 0 := by rw [this, sub_self]
  have hg := Fintype.linearIndependent_iff.1 hLI _ hz
  have hl' : (o (Fin.last n) : K) - c = 0 := by simpa [Fin.snoc_last] using hg (Fin.last n)
  have : c = (o (Fin.last n) : K) := by linear_combination -hl'
  rw [this]; exact (o (Fin.last n)).2

end Prim

section Main

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

theorem int_of_loc (c : D.host.E) (h : ∀ p : PlF D, (D.s.atP p).ιE c ∈ (D.s.atP p).O) : IsIntegral ℤ c := by
  let I : Ideal (𝓞 D.host.F) :=
    { carrier := {s | IsIntegral ℤ (algebraMap D.host.F D.host.E (s : D.host.F) * c)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [show ((a + b : 𝓞 D.host.F) : D.host.F) = (a : D.host.F) + b from rfl, map_add, add_mul]
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [show ((0 : 𝓞 D.host.F) : D.host.F) = 0 from rfl, map_zero, zero_mul]
        exact isIntegral_zero
      smul_mem' := fun r {s} hs => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at hs ⊢
        rw [show ((r * s : 𝓞 D.host.F) : D.host.F) = (r : D.host.F) * s from rfl, map_mul, mul_assoc]
        exact (r.2.map (algebraMap D.host.F D.host.E).toIntAlgHom).mul hs }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField D.host.F)
    let p : PlF D := ⟨m, hm.isPrime, hm0⟩
    obtain ⟨s, hs, hsint⟩ := (Formalism.L2.SG.Pf.LocalDenominators.iE_mem_O_iff_D p c).1 (h p)
    exact hs (hIm hsint)
  have h1 : (1 : 𝓞 D.host.F) ∈ I := by rw [hI]; exact Submodule.mem_top
  have h2 : IsIntegral ℤ (algebraMap D.host.F D.host.E ((1 : 𝓞 D.host.F) : D.host.F) * c) := h1
  simpa using h2

theorem xlam_eq {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V)
    (hlat : Submodule.IsLattice D.host.E Λ₂)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (locF' Zd p F')) :
    XLam Λ₂ F' = XS D F'.fl := by
  have hloc : ∀ p, lattice₂ D Zd.M p (XLam Λ₂ F') = lattice₂ D Zd.M p (XS D F'.fl) := by
    intro p
    apply SetLike.ext'
    have hsat := Formalism.L2.SG.Pf.locSatC_holds D Zd p Λ₂ (Xsp F') hlat.fg
    rw [show XLam Λ₂ F' = Λ₂ ⊓ toO (VS D) (Xsp F') from rfl, hsat, span_bcP_X Zd p F', latP_XS Zd p F']
    exact inter_span_eq _ _ (hprim p).1 (hprim p).2.1 (hprim p).2.2
  apply Formalism.L2.SG.Pf.eq_of_locP
  intro P
  haveI := P.isPrime
  have hfg1 : (XLam Λ₂ F').FG := Submodule.FG.of_le hlat.fg inf_le_left
  have hfg2 : (XS D F'.fl).FG := Formalism.L2.SG.Pf.Cnt.R3.XS_fg D F'.fl
  exact ((Formalism.L2.SG.Pf.locEqC_holds D Zd (Formalism.L2.SG.Pf.LocalDenominators.plOf (D := D) P.asIdeal P.isMaximal) _ _ hfg1 hfg2).1
    (hloc _)) P rfl

theorem z_prim {T' : D.host.E} (F' : LFlag (VS D) D.R.rS T') (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (locF' Zd p F')) :
    ∀ c : D.host.E, c • F'.fl.z ∈ Lsub Λ₂ F' → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  intro c hc
  obtain ⟨hsup, -⟩ := Submodule.mem_inf.1 hc
  obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 hsup
  have hlΛ : l ∈ Λ₂ := (Submodule.mem_inf.1 hl).1
  have hxX : x ∈ Xsp F' := hx
  have hloc : ∀ p, (D.s.atP p).ιE c ∈ (D.s.atP p).O := by
    intro p
    have hy : baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (Set.range fun a : Fin D.R.rS => locF' Zd p F' a.castSucc) := by
      rw [← span_bcP_X Zd p F']
      exact Submodule.subset_span ⟨x, hxX, rfl⟩
    have hly : baseChange₂ D p l = (D.s.atP p).ιE c • locF' Zd p F' (Fin.last D.R.rS) - baseChange₂ D p x := by
      rw [locF'_last, ← Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, ← map_sub, ← hlx, add_sub_cancel_right]
    have hc' := last_coord_mem (K := (D.s.atP p).Ep) (O := (Zd.M p).L.O) (lattice₂ D Zd.M p Λ₂) (locF' Zd p F')
      (hprim p).2.1 (hprim p).2.2 ((D.s.atP p).ιE c) (baseChange₂ D p x) (baseChange₂ D p l) hy
      (Submodule.subset_span ⟨l, hlΛ, rfl⟩) hly
    rw [← Formalism.L2.SG.Pf.LocalDenominators.hO Zd p]
    exact hc'
  exact ⟨⟨c, int_of_loc c hloc⟩, rfl⟩

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem btOK_holds : BtOK Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ φ' Λ₂ hs
  obtain ⟨_, _, ⟨hlat, hloc⟩, _⟩ := hs
  have hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (locF' Zd p (liftF F'₂)) := fun p =>
    (hloc p).1.1.2.2.1.1
  have hX : XLam Λ₂ (liftF F'₂) = XS D (liftF F'₂).fl := xlam_eq Zd (liftF F'₂) Λ₂ hlat hprim
  refine ⟨⟨fun P => ?_, z_prim Zd (liftF F'₂) Λ₂ hprim⟩, hX⟩
  obtain ⟨c, h1, h2, h3⟩ := PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.local_genus_exists D u' (liftF F'₂).fl P
  exact ⟨c, h1, h2, by rw [hX]; exact h3⟩

end Main

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
