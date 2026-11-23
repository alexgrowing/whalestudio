import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Topology Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.AffCxPts

variable {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} {k : ℕ}

def coords (φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)) (y : ↥(CxPts.ptsIn p (RingHom.id ℂ) U)) :
    Fin k → ℂ :=
  fun i => CxPts.ev p (RingHom.id ℂ) U (φ (MvPolynomial.X i)) y.1

theorem evHom_comp (φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U))
    (hC : ∀ a, φ (MvPolynomial.C a) = algX p U a) (y : ↥(CxPts.ptsIn p (RingHom.id ℂ) U)) :
    (CxPts.evHom y.2).comp φ = MvPolynomial.eval (coords φ y) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, hC, MvPolynomial.eval_C, ← CxPts.ev_eq y.2, CxPts.ev_algX y.2,
      RingHom.id_apply]
  · rw [RingHom.comp_apply, MvPolynomial.eval_X, coords, CxPts.ev_eq y.2]

def homAt {φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)} (hφ : Function.Surjective φ) (z : Fin k → ℂ)
    (hz : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval z)) : Γ(X, U) →+* ℂ :=
  φ.liftOfSurjective hφ ⟨MvPolynomial.eval z, hz⟩

theorem homAt_comp {φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U)} (hφ : Function.Surjective φ)
    (z : Fin k → ℂ) (hz : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval z))
    (P : MvPolynomial (Fin k) ℂ) : homAt hφ z hz (φ P) = MvPolynomial.eval z P :=
  φ.liftOfSurjective_comp_apply hφ ⟨_, hz⟩ P

end GlobalTheory.AffCxPts

open GlobalTheory.AffCxPts GlobalTheory.CxPts GlobalTheory.Points in

theorem GlobalTheory.AffCxPts.homeomorph_zeroSet : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (U : X.Opens),
    IsAffineOpen U → (algX p U).FiniteType → ∃ (k : ℕ) (G : Finset (MvPolynomial (Fin k) ℂ)),
      Nonempty (↥(GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U) ≃ₜ
        ↥{z : Fin k → ℂ | ∀ P ∈ G, MvPolynomial.eval z P = 0}) := by
  intro X p U hU hft
  letI := (algX p U).toAlgebra
  obtain ⟨k, φa, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  let φ : MvPolynomial (Fin k) ℂ →+* Γ(X, U) := φa.toRingHom
  have hφ' : Function.Surjective φ := hφ
  have hC : ∀ a, φ (MvPolynomial.C a) = algX p U a := fun a => φa.commutes a
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (RingHom.ker φ) :)
  refine ⟨k, G, ⟨?_⟩⟩
  let Z : Set (Fin k → ℂ) := {z | ∀ P ∈ G, MvPolynomial.eval z P = 0}
  have hker (z : Z) : RingHom.ker φ ≤ RingHom.ker (MvPolynomial.eval (z : Fin k → ℂ)) := by
    rw [← hG]
    exact Ideal.span_le.2 fun P hP => RingHom.mem_ker.2 (z.2 P hP)
  have hψ (z : Z) (a : ℂ) : homAt hφ' z (hker z) (algX p U a) = RingHom.id ℂ a := by
    rw [← hC, homAt_comp, MvPolynomial.eval_C, RingHom.id_apply]
  let s (z : Z) : CxPts p (RingHom.id ℂ) := ofHom hU (homAt hφ' z (hker z)) (hψ z)
  have hs_ev (z : Z) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (s z) = homAt hφ' z (hker z) f :=
    ev_ofHom hU _ (hψ z) f
  have hcoords (z : Z) (i : Fin k) :
      ev p (RingHom.id ℂ) U (φ (MvPolynomial.X i)) (s z) = (z : Fin k → ℂ) i := by
    rw [hs_ev, homAt_comp, MvPolynomial.eval_X]
  have htZ (y : ↥(ptsIn p (RingHom.id ℂ) U)) : coords φ y ∈ Z := fun P hP => by
    rw [← evHom_comp φ hC y, RingHom.comp_apply,
      RingHom.mem_ker.1 (hG ▸ Ideal.subset_span hP : P ∈ RingHom.ker φ), map_zero]
  have hgen : Subring.closure (Set.range (ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn p U) ∪
      Set.range fun i : Fin k => φ (MvPolynomial.X i)) = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨P, rfl⟩ := hφ' f
    induction P using MvPolynomial.induction_on with
    | C a => exact Subring.subset_closure (Or.inl ⟨a, (hC a).symm⟩)
    | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
    | mul_X P i hP =>
      rw [map_mul]; exact mul_mem hP (Subring.subset_closure (Or.inr ⟨i, rfl⟩))
  have hsc : Continuous s := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    refine (PtsOver.tendsto_iff_of_generators hU (ofHom_mem hU _ (hψ z)) hgen).2
      ⟨Eventually.of_forall fun w => ofHom_mem hU _ (hψ w), ?_⟩
    rintro _ ⟨i, rfl⟩
    have e (w : Z) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (s w).1 U (φ (MvPolynomial.X i)) = (w : Fin k → ℂ) i := hcoords w i
    rw [show (fun w : Z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (s w).1 U (φ (MvPolynomial.X i))) =
        fun w : Z => (w : Fin k → ℂ) i from funext e]
    exact (e z).symm ▸ ((continuous_apply i).comp continuous_subtype_val).tendsto z
  exact
    { toFun := fun y => ⟨coords φ y, htZ y⟩
      invFun := fun z => ⟨s z, ofHom_mem hU _ (hψ z)⟩
      left_inv := fun y => by
        refine Subtype.ext (Subtype.ext (ext_of_valR hU (ofHom_mem hU _ (hψ _)) y.2 fun f => ?_))
        obtain ⟨P, rfl⟩ := hφ' f
        change ev p (RingHom.id ℂ) U (φ P) (s _) = ev p (RingHom.id ℂ) U (φ P) y.1
        rw [hs_ev, homAt_comp, ev_eq y.2, ← RingHom.comp_apply, evHom_comp φ hC y]
      right_inv := fun z => Subtype.ext (funext fun i => hcoords z i)
      continuous_toFun := by
        refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
        exact (continuousOn_iff_continuous_restrict.1 (continuousOn_ev (φ (MvPolynomial.X i))))
      continuous_invFun := hsc.subtype_mk _ }
