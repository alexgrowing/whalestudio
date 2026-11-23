import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ChainFirstChainKMem
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanRec

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (α : Type) {LL : Type} [Field LL] (e : LL →+* Kf) (Mi : Submodule O (FnP P α))

theorem span_image_eq {V : Type} [AddCommGroup V] [Module LL V] (A : Subring LL)
    (hA : ∀ a ∈ A, e a ∈ Set.range (algebraMap O Kf)) (phi : V ≃ₗ[LL] FormsLL P α e Mi) (S : Set V)
    (hlat : ∀ x, (phi x).1 ∈ Mi ↔ x ∈ Submodule.span A S) (hd : MRatSpan P α e Mi) :
    Submodule.span O ((fun x => (phi x).1) '' S) = Mi := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact (hlat x).2 (Submodule.subset_span hx)
  · refine hd.symm.le.trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := phi.surjective y
    have hx : x ∈ Submodule.span A S := (hlat x).1 hy
    show (phi x).1 ∈ _
    clear hy
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
    | smul a y _ h1 =>
      obtain ⟨o, ho⟩ := hA a.1 a.2
      have : (phi (a • y)).1 = o • (phi y).1 := by
        rw [Subring.smul_def, map_smul]
        show e a.1 • (phi y).1 = _
        rw [← ho, algebraMap_smul]
      rw [this]
      exact Submodule.smul_mem _ _ h1

end Gen

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

abbrev FormsJ (j : ℕ) : Type := FormsLL (Fl.Pj j) (Lv.comp j) (c.embW u w h) (Lv.Int j)

structure UpData where

  phi : ∀ j, j + 1 ≤ D.R.m → (((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V ≃ₗ[D.what₂.LL] FormsJ c u w h Lv (j + 1))

  lat : ∀ j (hj : j + 1 ≤ D.R.m) x, (phi j hj x).1 ∈ Lv.Int (j + 1) ↔
    x ∈ locW D.what₂.places w ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).L

variable {c Tw u w h Lv}

def UpData.cmpI (X : UpData c Tw u w h Lv) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1) where
  toFun x := (X.phi j hj x).1
  map_add' x y := by rw [map_add]; rfl
  map_smul' a x := by rw [map_smul]; rfl

open Classical in

def UpData.cmpS (X : UpData c Tw u w h Lv) (j : ℕ) :
    ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V →ₛₗ[c.embW u w h] Lv.Fm (j + 1) :=
  if hj : j + 1 ≤ D.R.m then X.cmpI j hj else 0

theorem UpData.cmpS_apply (X : UpData c Tw u w h Lv) (j : ℕ) (hj : j + 1 ≤ D.R.m)
    (x : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V) : X.cmpS j x = (X.phi j hj x).1 := by
  unfold UpData.cmpS
  rw [dif_pos hj]
  rfl

def UpData.up (X : UpData c Tw u w h Lv) : CmpUp c Tw u w h Lv :=
  CmpUp.ofRat X.cmpS
    (fun j hj x y hxy => (X.phi j hj).injective (Subtype.ext (by rw [← X.cmpS_apply j hj, ← X.cmpS_apply j hj]; exact hxy)))
    (fun j hj x => by rw [X.cmpS_apply j hj]; exact (X.phi j hj x).2.2)

def DescUp (c : LatCmp D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl) : Prop :=
  ∀ j, j + 1 ≤ D.R.m → MRatSpan (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) (Lv.Int (j + 1))

theorem UpData.intS (X : UpData c Tw u w h Lv) (hd : DescUp c u w h Lv) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    Submodule.span (D.gat u w h).O
      (X.up.cmpS j '' (((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).L : Set ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V)) =
      Lv.Int (j + 1) := by
  have h0 : (X.up.cmpS j : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V → Lv.Fm (j + 1)) = fun x => (X.phi j hj x).1 :=
    funext fun x => X.cmpS_apply j hj x
  rw [h0]
  exact span_image_eq (Fl.Pj (j + 1)) (Lv.comp (j + 1)) (c.embW u w h) (Lv.Int (j + 1)) (intW D.what₂.places w)
    (fun a ha => (c.embW_int u w h a).1 ha) (X.phi j hj) _ (X.lat j hj) (hd j hj)

end Formalism.L2.G.Cmp
