import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataGatTies
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

noncomputable section

namespace Formalism.BasicNotions

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical

structure LatCmp (D : D7) where

  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf

  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)

  cmp : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ((D.fm u).lat 0).V →+ (D.gat u w hg).Fn
  cmp_smul : ∀ u w hg (a : D.what₂.LL) (x : ((D.fm u).lat 0).V),
    cmp u w hg (a • x) = embW u w hg a • cmp u w hg x

  cmp_li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (fun a => cmp u w hg (((D.fm u).lat 0).b a))

  cmp_M : ∀ u w hg, Submodule.span (D.gat u w hg).O (cmp u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) =
    (D.gat u w hg).M

def InLoc {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) V) (x : V) : Prop :=
  ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ A

namespace LatCmp

variable {D : D7} (c : LatCmp D)

def VramDef (Y : LatInst D) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    (Y.Vram u w hg : Set (D.gat u w hg).Fn) =
      Submodule.span (D.gat u w hg).Kf (c.cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V))

def NuServedDef {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
    ∀ x : (D.div.Nu u).V, InLoc (D.plEq w) (L.NuLat u) x ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg

end LatCmp

namespace LT

variable (D : D7) (u : D.what₂.Word)

abbrev Fn (i : ℕ) : Type := (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ

abbrev Vl (i : ℕ) : Type := ((D.fm u).lat i).V

abbrev Ow (w : D.what₂.places.Pl) : Subring D.what₂.LL := intW D.what₂.places w

instance lvModFin (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Module.Finite ((D.mem u).A.Fv v) ((D.fm u).lv i v c) :=
  Module.finite_of_finrank_pos (by rw [(D.fm u).lv_rank]; exact D.R.N_pos i)

instance lvFintype (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : Fintype ((D.fm u).lv i v c) :=
  haveI : Finite ((D.fm u).lv i v c) := Module.finite_of_finite ((D.mem u).A.Fv v)
  Fintype.ofFinite _

def Uop (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i :=
  LinearMap.pi fun c => ∑ x ∈ Finset.univ.filter (fun x : (D.fm u).lv i v c => (D.fm u).fv i v c x = 1),
    ((D.fm u).upT i v c x).toLinearMap ∘ₗ LinearMap.proj ((D.fm u).up i v c x)

def VVT (w : D.what₂.places.Pl) : Finset (D.mem u).A.vT :=
  if (D.fm u).seenP w then Finset.univ.filter (fun v => (D.fm u).tauOf w v ∈ topsOf D.host D.eTau) else ∅

def Uprod (i : ℕ) (w : D.what₂.places.Pl) : Fn D u i →ₗ[ℂ] Fn D u i :=
  (VVT D u w).toList.foldr (fun v g => (Uop D u i v).comp g) LinearMap.id

def imgL {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn D u i →ₗ[ℂ] Fn D u j)
    (A : Submodule (Ow D w) (Vl D u i)) : Submodule (Ow D w) (Vl D u j) where
  carrier := {y | ∃ x ∈ A, (D.fm u).emb j y = f ((D.fm u).emb i x)}
  add_mem' := by
    rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
    exact ⟨x + y, A.add_mem hx hy, by rw [map_add, map_add, map_add, h1, h2]⟩
  zero_mem' := ⟨0, A.zero_mem, by simp⟩
  smul_mem' := by
    rintro r a ⟨x, hx, h1⟩
    refine ⟨r • x, A.smul_mem r hx, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1,
      LinearMap.map_smul]

def Sram (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl D u 0) :=
  (D.fm u).S 0 w ⊓ (D.fm u).ramSub.restrictScalars (Ow D w)

def expT (w : D.what₂.places.Pl) : ℤ :=
  (D.R.m : ℤ) * ∑ v ∈ VVT D u w, (D.fm u).bTop ((D.fm u).tauOf w v)

def Nlam (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl D u 0) :=
  imgL D u w ((((D.mem u).A.T : ℂ) ^ expT D u w) • (Uprod D u 0 w) ^ D.R.m) (Sram D u w)

def URat (i : ℕ) (v : (D.mem u).A.vT) : Prop :=
  ∀ x, ∃ y, (D.fm u).emb i y = Uop D u i v ((D.fm u).emb i x)

def UL (i : ℕ) (v : (D.mem u).A.vT) (h : URat D u i v) : Vl D u i →ₗ[D.what₂.LL] Vl D u i :=
  descend ((D.fm u).emb i) ((D.fm u).emb i) ((D.fm u).emb_inj i) (Uop D u i v) h

theorem UL_spec (i : ℕ) (v : (D.mem u).A.vT) (h : URat D u i v) (x : Vl D u i) :
    (D.fm u).emb i (UL D u i v h x) = Uop D u i v ((D.fm u).emb i x) :=
  descend_spec ((D.fm u).emb i) ((D.fm u).emb i) ((D.fm u).emb_inj i) (Uop D u i v) h x

end LT

def NuAtTDef (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ x : (D.div.Nu u).V, InLoc (D.plEq w) (L.NuLat u) x ↔ D.nuIn u x ∈ LT.Nlam D u w

structure LatDefs (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) : Prop where
  vram : c.VramDef Y
  served : c.NuServedDef X Y K
  atT : NuAtTDef D L

end Formalism.BasicNotions

end
