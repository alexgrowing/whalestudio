import Development.EtaleCohomology.KummerTheory.EtaleKummerDegreeZeroCohomologyOfTwistSectionCla

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def TwRes0 : Prop := ∀ (q : ℕ) [NeZero q] {U X : Scheme.{0}} (x : U ⟶ X) (ζ₀ : Prim q Γ(X, ⊤)) (ζ : Prim q Γ(U, ⊤)),
  Sec.res x (twGen 0 ζ₀) = twGen 0 ζ

def DegreeZeroSectionExists : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 0 (by simp) U x = Sec.res x (Sec.map (resι R F) s)

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (s : Sec F U) :
    Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun f => f.hom s) h).symm

theorem OneEx_of (hT : TwSec) (hR : TwRes0) (hS : DegreeZeroSectionExists) : OneEx := by
  intro q _ A _ hA hq
  obtain ⟨⟨ζ₀⟩, -⟩ := hT q A hA hq
  obtain ⟨α, hα⟩ := hS (ZMod q) (tw q 0) (Spec (CommRingCat.of A)) (twGen 0 ζ₀)
  refine ⟨_, α, rfl, ?_⟩
  intro U x ζ
  refine (hα U x).trans ((sec_res_map (resι (ZMod q) (tw q 0)) (x : U ⟶ Spec (CommRingCat.of A)) (twGen 0 ζ₀)).trans ?_)
  rw [hR q (x : U ⟶ Spec (CommRingCat.of A)) ζ₀ ζ]
  rfl

end LateralTheory.KummerTheory
