import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (a : F ⟶ G) (b : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

theorem sec_map_add {R : Type} [CommRing R] {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a + b) x = Sec.map a x + Sec.map b x := rfl

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← a.hom.naturality]

theorem LeafImgHom_of (hG : LeafGen) : LeafImgHom := by
  intro S R _ _ I J ρ
  have ex : ∀ (P : PSh) (s : ℤ) (φ : (free S).obj P ⟶ I.X s), ∃ ψ : (free R).obj P ⟶ J.X s,
      ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map ψ (freeGen R P U x) = ρ.app U s (Sec.map φ (freeGen S P U x)) := by
    intro P s φ
    refine (hG R P).2.2.2 (J.X s) (fun U x => ρ.app U s (Sec.map φ (freeGen S P U x))) ?_
    intro V U g x
    rw [ρ.nat, sec_map_res, (hG S P).1]
  choose T hT using ex
  have ext : ∀ (P : PSh) (s : ℤ) (ψ ψ' : (free R).obj P ⟶ J.X s),
      (∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map ψ (freeGen R P U x) = Sec.map ψ' (freeGen R P U x)) → ψ = ψ' :=
    fun P s ψ ψ' h => (hG R P).2.2.1 _ ψ ψ' h
  refine ⟨fun P s => { toFun := T P s, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
  · apply ext; intro U x
    rw [hT]; show ρ.app U s 0 = 0; exact map_zero _
  · intro φ ψ; apply ext; intro U x
    rw [sec_map_add, hT, hT, hT, sec_map_add, map_add]
  · intro P s φ U x; exact hT P s φ U x
  · intro P s t φ; apply ext; intro U x
    show Sec.map (T P t (φ ≫ I.d s t)) _ = Sec.map (T P s φ ≫ J.d s t) _
    rw [hT, sec_map_comp, sec_map_comp, hT, ρ.comm]
  · intro P P' f s φ; apply ext; intro U x
    show Sec.map (T P s ((free S).map f ≫ φ)) _ = Sec.map ((free R).map f ≫ T P' s φ) _
    rw [hT, sec_map_comp, sec_map_comp, (hG S P).2.1, (hG R P).2.1, hT]

end LateralTheory.CohomologicalPurity.Bd
