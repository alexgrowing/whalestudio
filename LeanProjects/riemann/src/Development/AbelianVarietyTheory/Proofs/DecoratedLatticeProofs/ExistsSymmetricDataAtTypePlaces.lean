import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCharacterConductorOneExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSymmetricPositionLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SymReadEx
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem tame_step {D : D7} {T : Type} (L : LevCh D T) {μ0 : T} (hL : L.Is μ0) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Pl D.host.E} (hP : PP ∈ L.Pg)
    (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) {μ : kˣ →* ℂˣ}
    (hμ : (ofSplit q).IsComp (Lift.chrStep L.mu0 L.eta j).1⁻¹ μ) : IsTame μ := by
  intro x hx
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have e1 : L.mu0 (i + 1) (idl q x) = 1 := res_idl q h (hL.mu0 ⟨i, h2⟩) (hL.chi ⟨i, h2⟩ PP hP) x hx
  have hr : IsRes L.C.eta PP 1 := fun z y v hy hv => by
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    have hzP : z ∉ PP.asIdeal := fun hm => v.ne_zero (hv.trans (Ideal.Quotient.eq_zero_iff_mem.2 hm))
    rw [GlobalTheory.NormOneUnit.locK_unr (L.C.isEta.unr PP) (y := y)
      (by rw [hy]; exact (PP.valuation_eq_one_iff_notMem (K := D.host.E)).2 hzP)]
    rfl
  have e2 : L.eta (idl q x) = 1 := res_idl q h hL.eta hr x hx
  have e3 : (Lift.chrStep L.mu0 L.eta (i + 1)).1 (idl q x) = 1 := by
    unfold Lift.chrStep
    split_ifs
    · change L.mu0 (i + 1) (idl q x) * (L.eta (idl q x))⁻¹ = 1
      rw [e2, inv_one, mul_one]
      exact e1
    · exact e1
  refine Units.ext ((hμ x (idl q x) rfl).trans ?_)
  rw [MonoidHom.inv_apply, e3]
  simp

theorem red_sym {D : D7} {a : XGeo D} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP)
    (S : SymData l.k l.s D.R.k) {π : Equiv.Perm (Fin D.R.r)} (hπ : IsSymOrd D.R.rS D.R.k π)
    (g g' : GL (Fin D.R.r) (kP PP)) (hg : ∀ i j, g'.val i j = g.val (π i) (π j)) :
    ((∃ x, l.Red S x g) ↔ g' ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧
    ∀ ψ₀ : AddChar (kP PP) ℂ,
      (∀ z, (S.ψ (((S.ϖ⁻¹ : l.kˣ) : l.k) * prO l.q z) : ℂ) = ψ₀ (Ideal.Quotient.mk _ z)) → ∀ x, l.Red S x g →
        (S.P.lam x : ℂ) = ψ₀ (edgeSum (symEdge D.R.rS D.R.k) g') := by
  have h1 := l.hs
  have h2 := S.odd
  have hρ : D.R.rS = S.ρ := by unfold Ranks.rS; omega
  let e : Fin D.R.k ⊕ Fin (l.s + 1) ≃ Fin D.R.r := finSumFinEquiv.trans (finCongr (by unfold Ranks.r; omega))
  have he : ∀ a, (e a).val = framePos _ _ a := by rintro (a | a) <;> simp [e, framePos]
  have hr : ∀ x, l.Red S x g ↔ ∀ a b z, Ideal.Quotient.mk PP.asIdeal z = g.val (e a) (e b) →
      valuation l.k ((x : GL (Fin D.R.k ⊕ Fin (l.s + 1)) l.k).val a b - prO l.q z) < 1 := fun x =>
    ⟨fun h a b => h a b _ _ (he a) (he b), fun h a b a' b' ha hb => by
      obtain rfl : a' = e a := Fin.ext (ha.trans (he a).symm)
      obtain rfl : b' = e b := Fin.ext (hb.trans (he b).symm)
      exact h a b⟩
  rw [hρ] at hπ ⊢
  simp only [hr]
  exact ⟨sym_grp S (prO l.q) (prO_le l.q l.idem) (prO_lt l.q l.idem) e he hπ g g' hg,
    fun ψ₀ h x hx => sym_chr S (prO l.q) e he hπ g g' hg ψ₀ h x hx⟩

theorem exists_symRead : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ (a : XGeo D) (l : ∀ PP : (pk W).Pg, LocX a (pk W).βX PP.1), ∃ S : ∀ PP, SymData (l PP).k (l PP).s D.R.k, SymRead W l S := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW _ a l
  obtain ⟨ψ₀, hψ₀, -, π, hπ, hH, hχ⟩ := W.Q.charW.base.grp.levels
  have hlev := W.Q.charW.base.lev
  have loc : ∀ PP : (pk W).Pg, ∃ S : SymData (l PP).k (l PP).s D.R.k, (ofSplit (l PP).q).IsChar (pk W).ψ S.ψ ∧
      (∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit (l PP).q).IsComp (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹ (S.μ j)) ∧
      ∀ z, (S.ψ (((S.ϖ⁻¹ : (l PP).kˣ) : (l PP).k) * prO (l PP).q z) : ℂ) = ψ₀ PP.1 (Ideal.Quotient.mk _ z) := by
    intro PP
    obtain ⟨⟨ψk, hch, hcond⟩, -⟩ := GlobalTheory.WeilCondUnif.cond_unif W u hW a PP.1 (Or.inl PP.2) (l PP)
    obtain ⟨ϖ, hϖ, hres⟩ := exists_unif (l PP).q (l PP).idem hcond (hψ₀ PP.1 PP.2)
    obtain ⟨ρ, hρ⟩ : ∃ ρ, (l PP).s + 1 = 2 * ρ + 1 := by
      obtain ⟨b, hb⟩ := D.R.m_even
      have := (l PP).hs
      exact ⟨b - 1, by omega⟩
    obtain ⟨P, hP'⟩ := GlobalTheory.SymLevelExists.exists_isSymLevel (l PP).k ψk hcond ϖ hϖ ρ D.R.k ((l PP).s + 1)
    choose μ hμ using fun j => GlobalTheory.LocMod.Witness.exists_isComp (ofSplit (l PP).q) (Lift.chrStep (pk W).mu0 (pk W).eta j).1⁻¹
    refine ⟨⟨ψk, ϖ, ρ, P, fun j => if 1 ≤ j ∧ j ≤ D.R.m then μ j else 1, fun j => ?_, hcond, hϖ, hρ, hP'⟩, hch,
      fun j h1 h2 => ?_, hres⟩
    · split_ifs with h
      · exact tame_step (pk W).toLevCh hlev (l PP).q PP.2 (l PP).idem h.1 h.2 (hμ j)
      · exact fun _ _ => rfl
    · simp only [if_pos (And.intro h1 h2)]
      exact hμ j
  choose S h1 h2 h3 using loc
  refine ⟨S, h1, h2, fun x => (hH x).trans ?_, fun x hx y hxy => ?_⟩
  · exact ⟨fun h PP => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.2 (h PP (Set.mem_univ _)),
      fun h PP _ => (red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).1.1 (h PP)⟩
  · refine (hχ x hx ((hH _).1 hx)).trans ?_
    refine (MonoidHom.finset_prod_apply _ _ _).trans (Finset.prod_congr rfl fun PP _ => Units.ext ?_)
    exact ((red_sym (l PP) (S PP) hπ (x PP) (reord π x PP) fun _ _ => rfl).2 _ (h3 PP) _ (hxy PP)).symm

end GlobalTheory.SymReadEx

end
