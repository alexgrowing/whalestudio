import Development.EtaleCohomology.EtaleSheaves.LeafSuppKillPfSec

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

def twCls {q : ℕ} (j : ℤ) {A : CommRingCat.{0}} (ζ : Prim q A) : (twF q j).obj A :=
  Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))

def LeafOfRingsLocSurj : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
  (X : Scheme.{0}) (s : Sec (ofRings R M) X) (x : X), ∃ (U : Scheme.{0}) (w : U ⟶ X), Etale w ∧ x ∈ Set.range w ∧
  ∃ t : M.obj Γ(U, ⊤), Sec.res w s = ofRings.sec M U t

def LeafOfRingsLocInj : Prop := ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
  (U : Scheme.{0}) (t : M.obj Γ(U, ⊤)), ofRings.sec M U t = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (v : V ⟶ U),
  Etale v ∧ u ∈ Set.range v ∧ (M.map (Scheme.Γ.map v.op)).hom t = 0

def LeafTwAdj : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (u : U), IsUnit (q : Γ(U, ⊤)) →
  ∃ (W : Scheme.{0}) (w : W ⟶ U), Etale w ∧ u ∈ Set.range w ∧ Nonempty (Prim q Γ(W, ⊤))

def LeafTwGen : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (t : (twF q j).obj Γ(W, ⊤))
  (w0 : W), ∃ (O : W.Opens) (c : ZMod q), w0 ∈ O ∧
    ((twF q j).map (Scheme.Γ.map O.ι.op)).hom t = ((twF q j).map (Scheme.Γ.map O.ι.op)).hom (ULift.up c • twCls j ζ)

def LeafTwFieldZ : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (K : CommRingCat.{0}), IsField K →
  ∀ (ζ : Prim q K) (c : ZMod q), ULift.up c • twCls j ζ = 0 → c = 0

def LeafTwPt : Prop := ∀ (q : ℕ) [NeZero q] (j : ℤ) (U : Scheme.{0}) (u : U) (t : (twF q j).obj Γ(U, ⊤))
  (V : Scheme.{0}) (g : V ⟶ U) (v : V), g v = u → ((twF q j).map (Scheme.Γ.map g.op)).hom t = 0 →
  ∃ (W : Scheme.{0}) (w : W ⟶ U), Etale w ∧ u ∈ Set.range w ∧ ((twF q j).map (Scheme.Γ.map w.op)).hom t = 0

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (t : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U t) = ofRings.sec M V ((M.map (Scheme.Γ.map g.op)).hom t) := by
  have h := congrArg (fun f => f.hom t) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  exact h.symm

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (s : Sec F U) :
    Sec.res (f ≫ g) s = Sec.res f (Sec.res g s) := by
  simp [Sec.res]

theorem sec_zero {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) :
    ofRings.sec M U 0 = 0 :=
  map_zero _

theorem goal_of (h1 : LeafOfRingsLocSurj) (h2 : LeafOfRingsLocInj) (h3 : LeafTwPt) : LateralTheory.E.E8.LeafTwSecKill := by
  intro q _ X Z _ ι _ hq j s hs x hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨U, w, hw, ⟨u, hu⟩, t, ht⟩ := h1 (ZMod q) (twF q j) X s (ι z)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := ι) u z hu
  have hP : ofRings.sec (twF q j) _ (((twF q j).map (Scheme.Γ.map (pullback.fst w ι).op)).hom t) = 0 := by
    rw [← sec_res, ← ht]
    have e2 : Sec.res (F := tw q j) (pullback.fst w ι) (Sec.res w s) =
        Sec.res (F := tw q j) (pullback.snd w ι) (Sec.res ι s) := by
      rw [← res_comp, ← res_comp, pullback.condition]
    exact e2.trans (by rw [hs]; exact map_zero _)
  obtain ⟨V, v, hv, ⟨v0, hv0⟩, hV⟩ := h2 (ZMod q) (twF q j) _ _ hP p
  have hV' : ((twF q j).map (Scheme.Γ.map (v ≫ pullback.fst w ι).op)).hom t = 0 := by
    rw [op_comp, Functor.map_comp, Functor.map_comp]
    exact hV
  obtain ⟨W, w', hw', hu', hW⟩ := h3 q j U u t V (v ≫ pullback.fst w ι) v0 (by simp [hv0, hp1]) hV'
  haveI := hw; haveI := hw'
  refine ⟨W, w' ≫ w, inferInstance, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hu'
    exact ⟨a, by simp [ha, hu]⟩
  · rw [res_comp]
    have e := sec_res (twF q j) w' t
    rw [hW] at e
    exact (congrArg (Sec.res w') ht).trans (e.trans (sec_zero _ _))

end LateralTheory.E.E8.TwSec
