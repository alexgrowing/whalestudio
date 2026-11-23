import Formalism.SharpRestriction.GrowthBounds.ChartComparison.LocTiesOf
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.BadQNotOver
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelWithoutExtraPlaces

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.AgreeLv

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Tw : TwForms D} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)}

theorem one_le (i : ℕ) : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)

set_option maxHeartbeats 4000000 in

def formsInTw (W : TwFormsTiedS D Tw T J F) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (i : ℕ)
    (hi : i + 1 ≤ D.R.m) (dt : ∀ β, DetTie (W.ch u μ hμ (i + 1) (one_le i) hi β).lev) :
    FormsIn (Tw.fm u μ) (i + 1) hi where
  T := (D.mem u).A.T
  bad := badQ D (T.Q μ)
  eY := twYS T F u μ (i + 1) hi
  okW := okQ D (T.Q μ)
  Ch := T.Ch u μ (i + 1)
  chOf := T.chOf u μ (i + 1)
  lat := fun c => latCrd D (i + 1) hi (T.lat u μ (i + 1) c)
  K := W.ch u μ hμ (i + 1) (one_le i) hi
  val := W.val u μ hμ (i + 1) (one_le i) hi
  tw := fun β => DetTw.ofChiD (dt β) (cTw D (i + 1))

section Agree

variable {p : ℕ} {W' Qq : Type} [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] [Field Qq] [Algebra W' Qq]
  (W : TwFormsTiedS D Tw T J F) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (i : ℕ) (hi : i + 1 ≤ D.R.m)
  {L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ}
  (I : LocId L p nV W' Qq) (Z : Type) [CommGroup Z] (β : T.Ch u μ (i + 1))
  (M : StepMore D T u μ I Z (i + 1) (one_le i) hi β)

end Agree

variable {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}

set_option maxHeartbeats 2000000 in

def locInOf {Ch : Type} (cmpt : Ch → Type) [∀ β, Fintype (cmpt β)] (em : ∀ β, cmpt β → Lv.compS i) (cov : ChartsCover Lv i em)
    (Lb : Ch → Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E))
    (Uloc : Ch → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
      Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))
    (ψ : ∀ β, awayG D.sp.cm.sig (D.sp.X (i + 1)).gram (Uloc β) (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ)
    (t : ∀ β, GChartTie (X.g u w hg) Lv i (em β) (D.sp.X (i + 1)).gram (Lb β) (Uloc β) (ψ β) 1)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : LocIn X u w hg Lv i Ch where
  cmpt := cmpt
  eC := Equiv.ofBijective _ cov
  Lb := Lb
  Uloc := Uloc
  ψ := ψ
  t := t
  B := B

end Formalism.MainNotions.G.CmpJ.AgreeLv

end
