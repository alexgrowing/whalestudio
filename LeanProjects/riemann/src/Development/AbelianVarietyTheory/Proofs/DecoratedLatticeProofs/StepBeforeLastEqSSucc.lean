import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ToBlocksMulFinZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]

def toSum0 (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] : GL n k ≃* GL (n ⊕ Fin 0) k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k (Equiv.sumEmpty n (Fin 0)).symm).toMulEquiv

theorem toSum0_val (g : GL n k) :
    ((toSum0 k n g : GL (n ⊕ Fin 0) k) : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) =
      (g : Matrix n n k).reindex (Equiv.sumEmpty n (Fin 0)).symm (Equiv.sumEmpty n (Fin 0)).symm := rfl

end Local

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

theorem step_before_last_eq_s_succ (J : QJ a t) {j : ℕ} (hj : j + 1 = B.R.m) (i : Fin J.r) : j = (J.G i).s + 1 := by
  have h1 := (J.G i).hs
  have h2 : (I.rec7 l Z).R.m = B.R.m := rfl
  omega

def frJ (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    Frame (J.G i).k ((I.rec7 l Z).sp.X j).rank (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) := by
  subst e
  exact (J.G i).FX _ le_rfl

def rdAt (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k :=
  (toSum0 (J.G i).k _).toMonoidHom.comp (GlobalTheory.LevIdx.locHom (J.G i).q _ (frJ J j i e))

def rd (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k) :=
  MonoidHom.pi fun i => rdAt J j i (step_before_last_eq_s_succ J hj i)

def plF (J : QJ a t) (p : GlobalTheory.FinPl.Pl (I.rec7 l Z)) : Prop := ∃ i, (J.G i).q.v = p

end GlobalTheory.PenBridge
end

namespace GlobalTheory.PenBridge

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]

theorem toSum0_mem_KO_iff (x : GL n k) : toSum0 k n x ∈ KO k (n ⊕ Fin 0) ↔ x ∈ KO k n := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.mapEquiv (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] (Equiv.sumEmpty n (Fin 0))).toMulEquiv y, ?_⟩
    ext a b
    have := congrArg (fun g : GL (n ⊕ Fin 0) k => (g : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) k) (Sum.inl a) (Sum.inl b)) hy
    simpa [toSum0_val, Matrix.reindex_apply] using this
  · rintro ⟨y, rfl⟩
    refine ⟨Units.mapEquiv (Matrix.reindexAlgEquiv 𝒪[k] 𝒪[k] (Equiv.sumEmpty n (Fin 0)).symm).toMulEquiv y, ?_⟩
    ext a b
    simp [toSum0_val, Matrix.reindex_apply]

end Local

theorem relIndex_comap_conj {G : Type} [Group G] (H K : Subgroup G) {c : G} (hc : c ∈ K) :
    (H.comap (MulAut.conj c).toMonoidHom).relIndex K = H.relIndex K := by
  rw [Subgroup.relIndex_comap]
  congr 1
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact K.mul_mem (K.mul_mem hc hy) (K.inv_mem hc)
  · intro hx
    exact ⟨c⁻¹ * x * c, K.mul_mem (K.mul_mem (K.inv_mem hc) hx) hc, by group⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

theorem intIn_frJ (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) :
    IntIn (J.G i).q ((I.rec7 l Z).sp.X j) (frJ J j i e) (a.g.x j).L := by
  subst e
  exact fun y => (J.G i).latX _ le_rfl y

theorem rdAt_apply (J : QJ a t) (j : ℕ) (i : Fin J.r) (e : j = (J.G i).s + 1) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    rdAt J j i e g = toSum0 (J.G i).k _ (GlobalTheory.LevIdx.locHom (J.G i).q _ (frJ J j i e) g) := rfl

end GlobalTheory.PenBridge
