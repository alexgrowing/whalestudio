import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem lattice_eq_base_off_twist : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ p, p ∉ a.v.tP → GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) (a.g.x 0).L (· = p) = GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) ((F0 W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft (I.rec7 l Z).host.E (I.rec7 l Z).host.E (finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 (I.rec7 l Z).host.E))) (· = p) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr row col hc p hp
  obtain ⟨hs⟩ := hW.tr.std
  obtain ⟨k, hk⟩ := (hs u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hx := (hTr.pinX.xs 0 (Nat.zero_le _)).2.2
  have hlb := hk.lb ()
  have hTp : (((B.T u : ℕ) : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    intro h; apply hp; rw [(ha.tie row col).1.tP p]; exact_mod_cast h
  have hd : ((B.T u : ℕ) : ℤ) ≠ 0 := fun h => hTp (by rw [h]; simp)
  have h1 : ((1 : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    rw [Int.cast_one]; exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  set e := finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) with he
  have hpi : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := by
    refine ⟨⟨B.host.conj (X.piT u : B.host.E), map_isIntegral_int (B.host.conj : B.host.E →+* B.host.E) (X.piT u).2⟩, ?_⟩
    apply RingOfIntegers.ext
    have := X.piT_norm u
    push_cast
    exact this.symm
  refine le_antisymm (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ ((B.T u : ℕ) : ℤ) hd ?_ p hTp)
    (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ 1 one_ne_zero ?_ p h1)
  · intro y hy
    have hyi : ∀ j, IsIntegral ℤ (y j) := (hx y).1 hy
    refine Submodule.mem_map.2 ⟨fun j => (((B.T u : ℕ) : ℤ) • y) (e.symm j), (hlb _).2 fun j => ?_, ?_⟩
    · refine ⟨((B.T u : ℕ) : 𝓞 B.host.E) * ⟨y (e.symm j), hyi _⟩, ?_, fun _ => dvd_mul_of_dvd_left hpi _⟩
      show (((B.T u : ℕ) : ℤ) • y) (e.symm j) = _
      rw [Pi.smul_apply, zsmul_eq_mul]
      push_cast
      rfl
    · funext i
      show (((B.T u : ℕ) : ℤ) • y) (e.symm (e i)) = _
      rw [Equiv.symm_apply_apply]
  · rintro _ ⟨x, hxm, rfl⟩
    rw [one_smul]
    refine (hx _).2 fun j => ?_
    obtain ⟨r, hr, -⟩ := (hlb x).1 hxm (e j)
    show IsIntegral ℤ (x (e j))
    rw [hr]; exact r.2

end GlobalTheory.Fam
