import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

structure RowMatch (ch : Choice R) (G' : GlobalTheory.Grid.GridPre R) : Prop where

  V : ∀ i, i ≤ D.R.m → (G'.V i 0).V = ch.G.V (.grid i 0)

  ν : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).ν (ch.M.ν (.grid i 0))

  fd : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).fd (ch.M.fd (.grid i 0))

  ker : ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
    GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f ∧ ∃ p,
      HEq (fun h g => thetaKO (G'.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f p))
        (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h)

theorem row_induction {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (C : ∀ i, Set (Fn G (.grid i 0))) : ∀ (n : ℕ) (f : ∀ i : Fin n, Sch G (.right (i : ℕ) 0)),
    (∀ (i : Fin n) F, F ∈ C i → LiftConv W M (.right (i : ℕ) 0) (f i) F ∧
      liftA W M (.right (i : ℕ) 0) (f i) F ∈ C ((i : ℕ) + 1)) →
    ∀ F ∈ C 0, PathConv W M (rowPath T 0 n) (rowFam 0 n f) F ∧ liftP W M (rowPath T 0 n) (rowFam 0 n f) F ∈ C n
  | 0, _, _, _, hF => ⟨trivial, hF⟩
  | n + 1, f, h, F, hF => by
    have ih := row_induction W M C n (fun i => f i.castSucc) (fun i F hF => h i.castSucc F hF) F hF
    have := h (Fin.last n) _ ih.2
    exact ⟨⟨ih.1, this.1⟩, this.2⟩

theorem isAutFun_zero (V : HSp D) : IsAutFun V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩

theorem isAutFun_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsAutFun V f) (hg : IsAutFun V g) : IsAutFun V (f + g) := by
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨U', hU', h'⟩ := hg.level
  refine ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.left γ hγ x, hg.left γ hγ x], ⟨U ⊓ U', hU.inter hU', fun k hk hf x => ?_⟩,
    hf.cont.add hg.cont⟩
  simp only [Pi.add_apply, h k hk.1 hf x, h' k hk.2 hf x]

theorem isAutFun_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsAutFun V f) (a : ℂ) : IsAutFun V (a • f) := by
  obtain ⟨U, hU, h⟩ := hf.level
  refine ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.left γ hγ x], ⟨U, hU, fun k hk hf x => ?_⟩, hf.cont.const_smul a⟩
  simp only [Pi.smul_apply, h k hk hf x]

theorem isAutFun_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have hU' : ∀ w, IsAutFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => (hx.aut w).toIsAutFun
    | zero => exact fun w => isAutFun_zero _
    | add x y _ _ hx hy => exact fun w => isAutFun_add (hx w) (hy w)
    | smul c x _ hx => exact fun w => isAutFun_smul (hx w) c
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using isAutFun_smul (hU' f) r
  | add x y hx hy => simpa using isAutFun_add hx hy

theorem start_mem {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (u : R.HE.H) :
    PiTensorProduct.lift (R.HE.e u) ∈ (GlobalTheory.Grid.nodeY R 0).Cusp R.θ := by
  have h1 : R.HE.e u ∈ R.EEat R.triv := h.models.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have h2 := Formalism.IndefR.Mult.goodPart_le R.θ (R.MY 0) _ _ _ h1
  exact GlobalTheory.Grid.Node.multT_le_cusp (GlobalTheory.Grid.nodeY R 0) R.θ _ _ (Submodule.mem_map_of_mem h2)

theorem rowBase_of_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
  ⟨h.lev, h.models.inf, h.models.νY, h.models.νY', h.models.νX⟩

end GlobalTheory.RowLift

end
