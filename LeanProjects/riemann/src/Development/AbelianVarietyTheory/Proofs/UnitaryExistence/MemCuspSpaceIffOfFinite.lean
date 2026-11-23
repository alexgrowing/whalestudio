import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CuspSectionNorms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

noncomputable section

namespace GlobalTheory.CuspSecCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.CuspSectionNorms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {ι : Type}

theorem bdd_iff_supE_ne_top (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    (∃ C : ℝ, ∀ p : FramePt X, ptNorm la P p ≤ C) ↔ Formalism.L2.PjFree.supE X la P ≠ ⊤ := by
  constructor
  · rintro ⟨C, hC⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun p => ENNReal.ofReal_le_ofReal (hC p))
  · intro h
    refine ⟨(Formalism.L2.PjFree.supE X la P).toReal, fun p => ?_⟩
    rw [← ENNReal.ofReal_le_iff_le_toReal h]
    exact le_iSup (fun q : FPt X => ENNReal.ofReal ((X q.1).pnorm (la q.1) (P q.1) q.2)) p

theorem isCuspSec_iff (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    IsCuspSec la P ↔ IsHolCusp X la P ∧ Formalism.L2.PjFree.supE X la P ≠ ⊤ :=
  and_congr Iff.rfl (bdd_iff_supE_ne_top X la P)

theorem isCuspSec_iff_isHolCusp [Finite ι] (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    IsCuspSec la P ↔ IsHolCusp X la P :=
  isCuspSec_iff_of_finite la P

theorem mem_holSub_iff (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    P ∈ holSub X la ↔ IsHolCusp X la P := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem Q hQ => exact hQ
  | zero => exact fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.1
  | add Q R _ _ hQ hR => exact fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.2.1 _ (hQ c) _ (hR c)
  | smul a Q _ hQ => exact fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.2.2 a _ (hQ c)

theorem mem_cuspSpace_iff (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    P ∈ cuspSpace la ↔ P ∈ holSub X la ∧ Formalism.L2.PjFree.supE X la P ≠ ⊤ ∧ ZeroOff P := by
  rw [mem_holSub_iff, ← and_assoc, ← isCuspSec_iff]
  rfl

theorem mem_cuspSpace_iff_of_finite [Finite ι] (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    P ∈ cuspSpace la ↔ P ∈ holSub X la ∧ ZeroOff P := by
  rw [mem_holSub_iff, ← isCuspSec_iff_isHolCusp]
  rfl

theorem cuspSpace_le_holSub (X : ι → Data E r) (la : FamWt X) : cuspSpace la ≤ holSub X la :=
  fun P hP => ((mem_cuspSpace_iff X la P).1 hP).1

theorem mem_SS_congr (X : Data E r) (la : Wt X.Ψ r) {P Q : Frame X.Ψ r → ℂ}
    (h : ∀ x ∈ X.dom, P x = Q x) (hP : P ∈ X.SS la) : Q ∈ X.SS la := by
  obtain ⟨⟨⟨hd, hb, hg⟩, C, hC⟩, hc⟩ := hP
  refine ⟨⟨⟨hd.congr fun x hx => (h x hx).symm, fun x hx b hb' => ?_, fun γ hγ x hx => ?_⟩, C,
    fun x hx => ?_⟩, fun ξ hξ x hx => ?_⟩
  · rw [← h _ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb'), ← h x hx, hb x hx b hb']
  · rw [← h _ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact X hγ hx), ← h x hx, hg γ hγ x hx]
  · have := hC x hx
    unfold Data.pnorm at this ⊢
    rwa [← h x hx]
  · have e : ∀ s : X.Ψ → ℝ,
        P (X.flow ξ (fun τ => (s τ : ℂ)) x) = Q (X.flow ξ (fun τ => (s τ : ℂ)) x) :=
      fun s => h _ (TransvectionPeriodicity.flow_real_mem_dom X hξ.2.1 s x hx)
    have := hc ξ hξ x hx
    unfold Data.fj at this ⊢
    simpa only [e] using this

def res (X : ι → Data E r) : FDSec X →ₗ[ℂ] (FPt X → ℂ) where
  toFun P p := P p.1 p.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def trunc (X : ι → Data E r) : FDSec X →ₗ[ℂ] FDSec X where
  toFun P c := (X c).dom.indicator (P c)
  map_add' P Q := funext fun c => Set.indicator_add' _ (P c) (Q c)
  map_smul' a P := funext fun c => funext fun x => by
    by_cases hx : x ∈ (X c).dom <;> simp [hx]

theorem trunc_of_mem (X : ι → Data E r) (P : FDSec X) (c : ι) {x : Frame (X c).Ψ r}
    (hx : x ∈ (X c).dom) : trunc X P c x = P c x := Set.indicator_of_mem hx _

theorem zeroOff_trunc (X : ι → Data E r) (P : FDSec X) : ZeroOff (trunc X P) :=
  fun _ _ hx => Set.indicator_of_notMem hx _

theorem trunc_eq_self (X : ι → Data E r) {P : FDSec X} (h : ZeroOff P) : trunc X P = P := by
  funext c x
  by_cases hx : x ∈ (X c).dom
  · exact trunc_of_mem X P c hx
  · rw [zeroOff_trunc X P c x hx, h c x hx]

theorem res_trunc (X : ι → Data E r) (P : FDSec X) : res X (trunc X P) = res X P :=
  funext fun p => trunc_of_mem X P p.1 p.2.2

theorem ker_trunc (X : ι → Data E r) : LinearMap.ker (trunc X) = LinearMap.ker (res X) := by
  ext P
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    rw [← res_trunc, h, map_zero]
  · intro h
    funext c x
    by_cases hx : x ∈ (X c).dom
    · rw [trunc_of_mem X P c hx]
      exact congrFun h ⟨c, x, hx⟩
    · exact zeroOff_trunc X P c x hx

theorem isHolCusp_trunc_iff (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    IsHolCusp X la (trunc X P) ↔ IsHolCusp X la P :=
  ⟨fun h c => mem_SS_congr _ _ (fun _ hx => trunc_of_mem X P c hx) (h c),
    fun h c => mem_SS_congr _ _ (fun _ hx => (trunc_of_mem X P c hx).symm) (h c)⟩

theorem holSub_eq_comap [Finite ι] (X : ι → Data E r) (la : FamWt X) :
    holSub X la = (cuspSpace la).comap (trunc X) := by
  ext P
  rw [Submodule.mem_comap, mem_cuspSpace_iff_of_finite, mem_holSub_iff, mem_holSub_iff,
    isHolCusp_trunc_iff, and_iff_left (zeroOff_trunc X P)]

theorem map_res_eq [Finite ι] (X : ι → Data E r) (la : FamWt X) :
    (holSub X la).map (res X) = (cuspSpace la).map (res X) := by
  refine le_antisymm ?_ (Submodule.map_mono (cuspSpace_le_holSub X la))
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨trunc X P, (holSub_eq_comap X la).le hP, res_trunc X P⟩

theorem disjoint_cuspSpace_ker (X : ι → Data E r) (la : FamWt X) :
    Disjoint (cuspSpace la) (LinearMap.ker (res X)) := by
  rw [← ker_trunc, Submodule.disjoint_def]
  intro P hP h0
  rw [← trunc_eq_self X hP.2]
  exact h0

def cuspSpaceEquiv [Finite ι] (X : ι → Data E r) (la : FamWt X) :
    cuspSpace la ≃ₗ[ℂ] (holSub X la).map (res X) :=
  LinearEquiv.ofBijective
    ((res X).restrict fun _ hP => Submodule.mem_map_of_mem (cuspSpace_le_holSub X la hP))
    ⟨fun P Q h => Subtype.ext (LinearMap.disjoint_ker_iff_injOn.1 (disjoint_cuspSpace_ker X la)
        P.2 Q.2 (congrArg Subtype.val h)),
      fun F => by
        obtain ⟨P, hP, e⟩ := (map_res_eq X la).le F.2
        exact ⟨⟨P, hP⟩, Subtype.ext e⟩⟩

end GlobalTheory.CuspSecCompare
