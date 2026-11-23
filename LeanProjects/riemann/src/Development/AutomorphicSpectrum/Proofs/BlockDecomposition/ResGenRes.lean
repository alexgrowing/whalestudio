import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtRoot

open CochainComplex CochainComplex.HomComplex

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (primRes g ζ) := by
  unfold twGen Sec.res ofRings.sec
  have h := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) g.op
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q i).obj (op U))
  have h2 : ((Scheme.Γ ⋙ twF q i).map g.op).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      (Submodule.Quotient.mk (Finsupp.single (primRes g ζ) 1) : (Scheme.Γ ⋙ twF q i).obj (op V)) := by
    simp only [Functor.comp_map, twF, ModuleCat.hom_ofHom]
    erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    unfold primRes
    rw [Scheme.Γ_map_op]
  exact h.symm.trans (congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V))) h2)

theorem resGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (primRes g ζ) := by
  unfold resGen
  rw [← twGen_res i g ζ]
  unfold Sec.res Sec.map
  exact (NatTrans.naturality_apply (resι (ZMod q) (tw q i)).hom g.op (twGen i ζ)).symm

theorem repRoot : CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.ResZero → CrystallineSemistableComparison.E.RepRoot := by
  intro hC hZ q i X ζ
  refine ⟨fun V g => ⟨twGen_res i g ζ, resGen_res i g ζ⟩, ?_⟩
  have hd : Sec.map ((res (ZMod q) (tw q i)).d 0 1) (resGen i ζ) = 0 :=
    ((hZ (ZMod q) (tw q i) X).2.1 (resGen i ζ)).mpr ⟨twGen i ζ, rfl⟩
  obtain ⟨α, hα⟩ := (hC (ZMod q) (res (ZMod q) (tw q i)) X 0 (resGen i ζ)).1 hd
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.EtC.pick_spec
    (P := fun c => ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res (ZMod q) (tw q i)) 0,
      CohomologyClass.mk α = c ∧
        ∀ (U : Scheme) (x : U ⟶ X), ev (R := ZMod q) (E := sch.obj X) (I := res (ZMod q) (tw q i)) (n := 0) (↑α) 0 0 (by simp) U x = Sec.res x (resGen i ζ))
    ⟨_, α, rfl, hα.1⟩
  unfold CrystallineSemistableComparison.E.Rep GlobalTheory.EtC.rootClass
  refine ⟨β, hβ1, (hβ2 X (𝟙 X)).trans ?_⟩
  unfold Sec.res
  simp

end GlobalTheory.CompanionTheory.EtRoot
