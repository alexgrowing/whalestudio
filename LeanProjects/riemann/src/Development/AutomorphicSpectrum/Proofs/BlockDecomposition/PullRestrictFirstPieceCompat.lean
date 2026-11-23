import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransfer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaNat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsCongr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SqCSmul
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

section Cuts

variable {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D)
  (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T)) (Q : Poly Φ) (Q' : Poly Φ')

theorem le_cover_restrict_compat {c : R'} {a : IdF Φ.A} {a' : IdF Φ'.A} (h : m.LeC c a a') :
    (m1 m E E' e he hρ).LeC c (a.res (Cut.U E)) (a'.res (Cut.U E')) := fun T x hx => h T.T x hx

theorem pull_restrict_first_piece_compat (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (j : ℕ)
    (x : CH.H (sq (a.res (Cut.U E)) (b.res (Cut.U E))) j) :
    (mP m E E' e he hρ Q Q' c ha hb).pull j
        ((CH.Mor.restrict (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q)).pull j x) =
      (CH.Mor.restrict (sq (a'.res (Cut.U E')) (b'.res (Cut.U E'))) (Cut.P0 Q')).pull j
        (((m1 m E E' e he hρ).sqC c (le_cover_restrict_compat m E E' e he hρ ha) (le_cover_restrict_compat m E E' e he hρ hb)).pull j x) := by
  let μ₁ : CH.Mor (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ :=
    (CH.Mor.restrict (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q)).comp (mP m E E' e he hρ Q Q' c ha hb)
  let μ₂ : CH.Mor (sq (a.res (Cut.U E)) (b.res (Cut.U E))) (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq a' b') σ :=
    ((m1 m E E' e he hρ).sqC c (le_cover_restrict_compat m E E' e he hρ ha) (le_cover_restrict_compat m E E' e he hρ hb)).comp
      (CH.Mor.restrict (sq (a'.res (Cut.U E')) (b'.res (Cut.U E'))) (Cut.P0 Q'))
  have h := CrystallineSemistableComparison.P.prism μ₁ μ₂ (eta m E E' e he hρ Q Q') (fun T x => rfl) j x
  exact (CrystallineSemistableComparison.P.pull_comp _ _ j x).1.symm.trans (h.trans (CrystallineSemistableComparison.P.pull_comp _ _ j x).1)

def alpha {d : ℕ} {E : Frame Φ (d + 1)} (Q : Poly Φ) (a b : IdF Φ.A) : Pt.U E ⋙ sq a b ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq a b :=
  Functor.whiskerRight (Cut.jNat (E := E) Q) (sq a b)

theorem alpha_τ (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (X : Pt E')
    (y : sqM a b (m.G.obj X.T)) :
    (mP m E E' e he hρ Q Q' c ha hb).τ X (((alpha Q a b).app ((Gp m E E' e).obj X)).hom y) =
      ((alpha Q' a' b').app X).hom ((mPt m E E' e c ha hb).τ X y) := by
  change (m.sqC c ha hb).τ (Q'.P X.T) (((sq a b).map (etaC m E E' e he hρ Q Q' X).1).hom
      (((sq a b).map (Q.j (m.G.obj X.T))).hom y)) = ((sq a' b').map (Q'.j X.T)).hom ((m.sqC c ha hb).τ X.T y)
  rw [← (m.sqC c ha hb).nat]
  congr 1
  have h2 := congrArg (fun t => ((sq a b).map t).hom y) (j_eta m E E' e he hρ Q Q' X)
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

theorem alpha_hom (c : R') {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : m.LeC c a a') (hb : m.LeC c b b') (k : ℕ)
    (x : CH.Cn (Pt.U E ⋙ sq a b) k) :
    (mP m E E' e he hρ Q Q' c ha hb).hom.f k ((CH.Mor.ofNatTrans (alpha Q a b)).hom.f k x) =
      (CH.Mor.ofNatTrans (alpha Q' a' b')).hom.f k ((mPt m E E' e c ha hb).hom.f k x) :=
  funext fun s => alpha_τ m E E' e he hρ Q Q' c ha hb _ _

theorem rho_finsupp_sum_dpow (c : R') {T P' : C'} (jj : T ⟶ P') (η : Q.P (m.G.obj T) ⟶ m.G.obj P') (X' : Φ'.A.obj P')
    (hj : Q.j (m.G.obj T) ≫ η = m.G.map jj) (hx : m.ρ P' ((Φ.A.map η).hom (Q.X (m.G.obj T))) = X')
    (cc : ℕ →₀ Φ.A.obj (m.G.obj T)) :
    algebraMap R' (Φ'.A.obj P') c * m.ρ P' ((Φ.A.map η).hom
        (cc.sum fun k y => (Φ.A.map (Q.j (m.G.obj T))).hom y * Φ.dp k (Q.X (m.G.obj T)))) =
      (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj T) c * m.ρ T x) (by simp)).sum
        fun k y => (Φ'.A.map jj).hom y * Φ'.dp k X' := by
  rw [Finsupp.sum_mapRange_index (by intro k; simp), map_finsuppSum, map_finsuppSum, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  have hX := Q.X_mem (m.G.obj T)
  have hX' := Φ.J.map_mem η hX
  have h1 : (Φ.A.map η).hom ((Φ.A.map (Q.j (m.G.obj T))).hom (cc k)) = (Φ.A.map (m.G.map jj)).hom (cc k) := by
    rw [← Cut.mapA_comp, hj]
  rw [map_mul, map_mul, h1, m.nat, Φ.dp_map _ _ hX, m.dp _ _ hX', hx, map_mul, AlgHom.commutes, mul_assoc]

theorem rho_sum (c : R') (X : Pt E') (cc : ℕ →₀ Φ.A.obj (m.G.obj X.T)) :
    algebraMap R' (Φ'.A.obj (Q'.P X.T)) c * m.ρ (Q'.P X.T) ((Φ.A.map (etaC m E E' e he hρ Q Q' X).1).hom
        (cc.sum fun k y => (Φ.A.map (Q.j (m.G.obj X.T))).hom y * Φ.dp k (Q.X (m.G.obj X.T)))) =
      (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp)).sum
        fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T) :=
  rho_finsupp_sum_dpow m Q c (Q'.j X.T) (etaC m E E' e he hρ Q Q' X).1 (Q'.X X.T) (j_eta m E E' e he hρ Q Q' X)
    (rho_eta m E E' e he hρ Q Q' X) cc

theorem beta_τ {a b : ℤ → IdF Φ.A} {a' b' : ℤ → IdF Φ'.A} {r : ℤ} (c : R')
    (ha : ∀ r', m.LeC c (a r') (a' r')) (hb : ∀ r', m.LeC c (b r') (b' r'))
    (hca : Q.Crit a r) (hca1 : Q.Crit a (r - 1))
    (β : Cut.P0 Q ⋙ Cut.U E ⋙ sq (a r) (b r) ⟶ Cut.P0 Q ⋙ Cut.U E ⋙ sq (a (r - 1)) (b (r - 1)))
    (hβ : ∀ (X : Pt E) (c c' : ℕ →₀ Φ.A.obj X.T) (z : sqM (a r) (b r) (Q.P X.T)) (z' : sqM (a (r - 1)) (b (r - 1)) (Q.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j X.T)).hom y * Φ.dp k (Q.X X.T)) →
        (β.app X).hom z = z')
    (β' : Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r) (b' r) ⟶ Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' (r - 1)) (b' (r - 1)))
    (hβ' : ∀ (X : Pt E') (c c' : ℕ →₀ Φ'.A.obj X.T) (z : sqM (a' r) (b' r) (Q'.P X.T)) (z' : sqM (a' (r - 1)) (b' (r - 1)) (Q'.P X.T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ'.A.map (Q'.j X.T)).hom y * Φ'.dp k (Q'.X X.T)) →
        (β'.app X).hom z = z')
    (X : Pt E') (y : sqM (a r) (b r) (Q.P (m.G.obj X.T))) :
    (mP m E E' e he hρ Q Q' c (ha (r - 1)) (hb (r - 1))).τ X ((β.app ((Gp m E E' e).obj X)).hom y) =
      (β'.app X).hom ((mP m E E' e he hρ Q Q' c (ha r) (hb r)).τ X y) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
  obtain ⟨cc, rfl⟩ := Q.span _ w
  have hmem := (hca (m.G.obj X.T) cc).1 hw
  let c' : ℕ →₀ Φ.A.obj (m.G.obj X.T) := cc.comapDomain (· + 1) (fun _ _ _ _ h => Nat.add_right_cancel h)
  have hc' : ∀ k, c' k = cc (k + 1) := fun k => Finsupp.comapDomain_apply _ _ _ _
  have hw' := (hca1 (m.G.obj X.T) c').2 fun k => by
    rw [hc']
    have h := hmem (k + 1)
    rwa [show r - ((k + 1 : ℕ) : ℤ) = r - 1 - (k : ℤ) by push_cast; ring] at h
  have hb1 := hβ ((Gp m E E' e).obj X) cc c' ⟨_, hy⟩ ⟨_, Ideal.mem_map_of_mem _ hw'⟩ hc' rfl rfl
  rw [hb1]
  symm
  refine hβ' X (cc.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp))
    (c'.mapRange (fun x => algebraMap R' (Φ'.A.obj X.T) c * m.ρ X.T x) (by simp)) _ _ (fun k => ?_) ?_ ?_
  · rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, hc']
  · exact congrArg (Ideal.Quotient.mk _) (rho_sum m E E' e he hρ Q Q' c X cc)
  · exact congrArg (Ideal.Quotient.mk _) (rho_sum m E E' e he hρ Q Q' c X c')

end Cuts

end GlobalTheory.CompanionTheory.LocBC
