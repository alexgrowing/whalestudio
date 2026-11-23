import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountStmt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountFib
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountIdx
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountSurj
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountConv
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountStab
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountGenIn
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGap
import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum

noncomputable section

namespace Formalism.MainNotions.Gaps.CC

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.StandardLattice Formalism.MainNotions.Gaps.LG
open scoped TensorProduct

section Asm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ} (P : Par F E k)

theorem Kstd_le : Kstd P.σ P.J ≤ P.GA := inf_le_left

theorem stabTriv_sub (hstab : P.StabTriv) (S : P.Splits) (g : P.GA) (γ : GamG P.σ P.J)
    (h : g⁻¹ * (γ : P.GA) * g ∈ (P.U S).subgroupOf P.GA) : γ = 1 := by
  obtain ⟨γ0, hγ0, hγ⟩ : ((γ : P.GA) : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈
      ratPts P.σ P.J (FiniteAdeleRing (𝓞 F) F) := γ.2
  have h1 : γ0 = 1 := by
    refine hstab S g g.2 γ0 hγ0 ?_
    refine ⟨_, h, ?_⟩
    rw [hγ]
    simp [MulAut.conj_apply, mul_assoc]
  subst h1
  apply Subtype.ext
  apply Subtype.ext
  rw [← hγ, map_one]
  rfl

variable [StarRing E]

theorem classCount_of (f : ℕ) (S : P.Splits) (hfib : FibCount) (hidx : IdxOK P f) (hfin : KFinite P.σ P.J)
    (hmass : MassSum P.σ P.J) (hstab : P.StabTriv) (hne : (P.U S).relIndex (Kstd P.σ P.J) ≠ 0) :
    (Nat.card (P.Cls S) : ℝ) =
      Formalism.HermitianLatticesTheory.mass (stdForm E k) (stdLat E k) * (idxColLoc (P.gp 0) k ^ f * idxColLoc (P.gp 1) k ^ f) *
        ((P.T : ℝ) ^ k - 1) ^ f := by
  have hrel : ((P.U S).subgroupOf P.GA).relIndex (KstdG P.σ P.J) = (P.U S).relIndex (Kstd P.σ P.J) :=
    Subgroup.relIndex_subgroupOf (Kstd_le P)
  have h := hfib P.GA (GamG P.σ P.J) ((P.U S).subgroupOf P.GA) (KstdG P.σ P.J)
    (Subgroup.comap_mono (hidx S).1) (by rw [hrel]; exact hne) hfin.1 hfin.2 (stabTriv_sub P hstab S)
    Quotient.out (DoubleCoset.out_eq' _ _)
  rw [h, hrel, (hidx S).2, ← hmass Quotient.out (DoubleCoset.out_eq' _ _)]
  ring

end Asm

section HostS

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Inhab

variable {R : Ranks} (H : Host R)

def HostCount : Prop :=
  ∀ {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E), LevHyp H T pz piG →
    ∀ S : (hostPar H T pz piG).Splits,
      (Nat.card ((hostPar H T pz piG).Cls S) : ℝ) =
        massH H R.k * (idxColLoc (H.g 0) R.k ^ R.f * idxColLoc (H.g 1) R.k ^ R.f) * ((T : ℝ) ^ R.k - 1) ^ R.f

def HostGenusIn : Prop :=
  ∀ {R : Ranks} (H : Host R) (k : ℕ), letI := H.cmStar
    GenusIn (conjF H) (1 : Matrix (Fin k) (Fin k) H.E)

theorem host_sig (e : H.E) : conjF H e = (letI := H.cmStar; star e) := (star_eq_conj H e).symm

theorem host_fix (e : H.E) (h : conjF H e = e) : ∃ a : H.F, algebraMap H.F H.E a = e :=
  ⟨⟨e, (conj_eq_self_iff H e).1 h⟩, rfl⟩

theorem host_theta : ∃ θ : H.E, conjF H θ ≠ θ := by
  by_contra hcon
  push Not at hcon
  exact hs_conj_ne_one H (AlgEquiv.ext fun x => hcon x)

theorem hostGenusIn_of_core (hc : Surj.WACore) : HostGenusIn := fun H _ =>
  letI := H.cmStar
  Surj.genusIn_of_core hc (conjF H) (host_sig H) (host_fix H) (host_theta H)

theorem host_genusSurj (k : ℕ) :
    letI := H.cmStar
    GenusSurj (conjF H) (1 : Matrix (Fin k) (Fin k) H.E) :=
  letI := H.cmStar
  Surj.genusSurj (conjF H) (host_sig H) (host_fix H)

theorem classCount_host_of (hIn : HostGenusIn) : HostCount := by
  intro R H T pz piG hyp S
  letI := H.cmStar
  exact classCount_of (hostPar H T pz piG) R.f S Fib.fibCount (Idx.idxOK_host H T pz piG hyp)
    (Stab.kFinite (conjF H) (host_sig H) (fun φ a => emb_star H φ a) (hIn H R.k))
    (Stab.massSum (conjF H) (host_sig H) (fun φ a => emb_star H φ a) (hIn H R.k) (host_genusSurj H R.k))
    (factStabTriv H T pz piG hyp) (Idx.host_relIndex_Kstd_ne_zero H T pz piG hyp S)

theorem classCount_host_of_core (hc : Surj.WACore) : HostCount := classCount_host_of (hostGenusIn_of_core hc)

theorem hostGenusIn : HostGenusIn := hostGenusIn_of_core WA.waCore

theorem classCount : HostCount := classCount_host_of hostGenusIn

theorem classCount_par {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E) (piG : Fin 2 → 𝓞 H.E) (hyp : LevHyp H T pz piG)
    (P : Par H.F H.E R.k) (hP : P = hostPar H T pz piG) (S : P.Splits) :
    (Nat.card (P.Cls S) : ℝ) =
      massH H R.k * (idxColLoc (H.g 0) R.k ^ R.f * idxColLoc (H.g 1) R.k ^ R.f) * ((T : ℝ) ^ R.k - 1) ^ R.f := by
  subst hP
  exact classCount H T pz piG hyp S

end HostS

end Formalism.MainNotions.Gaps.CC

end
