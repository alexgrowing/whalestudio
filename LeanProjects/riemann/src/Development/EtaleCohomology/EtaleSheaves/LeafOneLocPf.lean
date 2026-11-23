import Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneLocPf

theorem freeGen_res (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  have h2 : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} (P.map g.op x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg _ h2)

theorem ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (Sx.res g x) := by
  unfold ev
  have hn := congrArg (fun f => f.hom (freeGen R _ U x))
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hn
  change _ = _ at hn
  rw [Sx.res, ← freeGen_res]
  exact hn.symm

def LeafPrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))

theorem LeafOneLoc_of (hprim : LeafPrimLoc) : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := by
  intro q _ E hE α hα U x
  obtain ⟨S, hS, hP⟩ := hprim q U (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  exact ⟨ζ, (ev_res α.1 0 0 (by simp) g x).trans (hα V (Sx.res g x) ζ)⟩

end LateralTheory.E.LeafOneLocPf
