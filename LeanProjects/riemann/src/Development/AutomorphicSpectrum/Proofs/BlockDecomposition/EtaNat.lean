import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransfer
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

section Pts

variable {d : ℕ} (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D)

def Gp : Pt E' ⥤ Pt E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} f := m.G.map (show X.T ⟶ Y.T from f)
  map_id X := m.G.map_id X.T
  map_comp {X Y Z} f g := m.G.map_comp (show X.T ⟶ Y.T from f) (show Y.T ⟶ Z.T from g)

def mPt (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Pt.U E ⋙ sq a b) (Pt.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := (m.sqC c ha hb).τ X.T
  nat {X Y} φ x := (m.sqC c ha hb).nat (show X.T ⟶ Y.T from φ) x

end Pts

section Cuts

variable {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D)
  (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T))

include he hρ in
theorem cut_mem {X Y : Cut E'} (φ : X ⟶ Y) :
    E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map φ.1) (e ≫ m.G.map Y.s) = 0 := by
  apply hρ Y.T
  have h := he 0 (X.s ≫ φ.1) Y.s
  rw [map_zero, Category.assoc, ← m.G.map_comp, h]
  exact φ.2

def G1 : Cut E' ⥤ Cut E where
  obj X := ⟨m.G.obj X.T, e ≫ m.G.map X.s⟩
  map {X Y} φ := ⟨m.G.map φ.1, cut_mem m E E' e he hρ φ⟩
  map_id X := Cut.hom_ext (m.G.map_id X.T)
  map_comp {X Y Z} f g := Cut.hom_ext (m.G.map_comp f.1 g.1)

def m1 : SMor (Cut.Φ1 E) (Cut.Φ1 E') σ where
  G := G1 m E E' e he hρ
  ρ T := m.ρ T.T
  comm T r := m.comm T.T r
  nat {T T'} φ x := m.nat φ.1 x
  mem T x hx := m.mem T.T hx
  dp T k x hx := m.dp T.T k hx

def e1 : (Cut.E1 E).D ⟶ (G1 m E E' e he hρ).obj (Cut.E1 E').D :=
  ⟨e, by
    change E.τ 0 (𝟙 E.D ≫ e) (e ≫ m.G.map (𝟙 E'.D)) = 0
    rw [Category.id_comp, m.G.map_id, Category.comp_id]
    exact E.τ_self 0 e⟩

theorem fr1 : (m1 m E E' e he hρ).Fr (Cut.E1 E) (Cut.E1 E') (e1 m E E' e he hρ) :=
  fun i {T} s s' => he i.succ s.1 s'.1

variable (Q : Poly Φ) (Q' : Poly Φ')

def etaC (X : Pt E') : (Cut.P0 Q).obj ((Gp m E E' e).obj X) ⟶ (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X) :=
  Cut.adjInv Q _ _ (m.G.map (Q'.j X.T))

theorem j_eta (X : Pt E') : Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 = m.G.map (Q'.j X.T) :=
  Cut.adjInv_j Q ((Gp m E E' e).obj X) ((G1 m E E' e he hρ).obj ((Cut.P0 Q').obj X)) (m.G.map (Q'.j X.T))

theorem rho_eta (X : Pt E') :
    m.ρ (Q'.P X.T) ((Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T))) = Q'.X X.T := by
  have h1 : (Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom (Q.X (m.G.obj X.T)) =
      E.τ 0 ((e ≫ m.G.map X.s) ≫ m.G.map (Q'.j X.T)) (e ≫ m.G.map (Cut.sec Q' X)) :=
    Q.lift_X (m.G.map (Q'.j X.T)) _ (E.mem 0 _ _)
  rw [h1, Category.assoc, ← m.G.map_comp, he 0 (X.s ≫ Q'.j X.T) (Cut.sec Q' X), Cut.sec_spec, if_pos rfl]

theorem eta_nat {X Y : Pt E'} (φ : X.T ⟶ Y.T) :
    Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫ (etaC m E E' e he hρ Q Q' Y).1 =
      (etaC m E E' e he hρ Q Q' X).1 ≫ m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
  have e1 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) =
      m.G.map φ ≫ Q.j (m.G.obj Y.T) := Cut.Pmap_j (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ)
  have e2 : Q'.j X.T ≫ Cut.Pmap (X := X) (Y := Y) Q' φ = φ ≫ Q'.j Y.T := Cut.Pmap_j (X := X) (Y := Y) Q' φ
  have e3 : Q.j (m.G.obj X.T) ≫ Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ) ≫
      (etaC m E E' e he hρ Q Q' Y).1 = Q.j (m.G.obj X.T) ≫ (etaC m E E' e he hρ Q Q' X).1 ≫
        m.G.map (Cut.Pmap (X := X) (Y := Y) Q' φ) := by
    rw [← Category.assoc, e1, Category.assoc, j_eta, ← Category.assoc (Q.j _), j_eta, ← m.G.map_comp, ← m.G.map_comp, e2]
  have e4 := Cut.truncation_hom_ext Q (X := (Gp m E E' e).obj X) (Y := (G1 m E E' e he hρ).obj ((Cut.P0 Q').obj Y))
    (ψ := (Cut.P0 Q).map (show (Gp m E E' e).obj X ⟶ (Gp m E E' e).obj Y from m.G.map φ) ≫ etaC m E E' e he hρ Q Q' Y)
    (ψ' := etaC m E E' e he hρ Q Q' X ≫ (G1 m E E' e he hρ).map ((Cut.P0 Q').map (show X ⟶ Y from φ))) e3
  exact congrArg Subtype.val e4

def eta : Gp m E E' e ⋙ Cut.P0 Q ⟶ Cut.P0 Q' ⋙ G1 m E E' e he hρ where
  app X := etaC m E E' e he hρ Q Q' X
  naturality {X Y} φ := Cut.hom_ext (eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ)

def mP (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') :
    CH.Mor (Cut.P0 Q ⋙ Cut.U E ⋙ sq a b) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ where
  G := Gp m E E' e
  τ X := ((m.sqC c ha hb).τ (Q'.P X.T)).comp ((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom
  nat {X Y} φ x := by
    have key : ∀ (φ : X.T ⟶ Y.T) (x : sqM a b (Q.P (m.G.obj X.T))),
        (m.sqC c ha hb).τ (Q'.P Y.T) (((sq a b).map (etaC m E E' e he hρ Q Q' Y).1).hom
          (((sq a b).map (Cut.Pmap (X := (Gp m E E' e).obj X) (Y := (Gp m E E' e).obj Y) Q (m.G.map φ))).hom x)) =
        ((sq a' b').map (Cut.Pmap (X := X) (Y := Y) Q' φ)).hom
          ((m.sqC c ha hb).τ (Q'.P X.T) (((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom x)) := by
      intro φ x
      rw [← (m.sqC c ha hb).nat]
      congr 1
      have h := eta_nat m E E' e he hρ Q Q' (X := X) (Y := Y) φ
      have h2 := congrArg (fun t => ((sq a b).map t).hom x) h
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
      exact h2
    exact key φ x

end Cuts

end GlobalTheory.CompanionTheory.LocBC
