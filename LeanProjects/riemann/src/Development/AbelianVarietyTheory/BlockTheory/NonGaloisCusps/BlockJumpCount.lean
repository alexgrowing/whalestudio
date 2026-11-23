import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain

section Local

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def IsJumpMultiset (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) : Prop :=
  FiniteDimensional LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, multV PD ρ τ a = (J.count a : ℤ)

theorem IsJumpMultiset.unique {ρ : Representation LL G V} {τ : K →ₐ[Qp] LL} {J J' : Multiset ℤ}
    (h : IsJumpMultiset PD ρ τ J) (h' : IsJumpMultiset PD ρ τ J') : J = J' := by
  ext a
  exact_mod_cast (h.2 a).symm.trans (h'.2 a)

end Local

def blockJumps (t : ℕ) : Multiset ℤ := (Multiset.range t).map (fun k : ℕ => (k : ℤ))

example : blockJumps 3 = {0, 1, 2} := by decide

section Glob

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def IsBlockSum (i : N.Loc) (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i)))
    (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) (π : N.X i) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] ((Fin R.r → KK N i) × (Fin R.t → KK N i)),
    ∀ (g : GE N) (u : Fin R.nV → KK N i),
      e ((mapM (toK N i) (rO N i r π) g).mulVec u) =
        ((mapM (toK N i) (rhoO N i ρ π) g).mulVec (e u).1,
          fun c : Fin R.t => toK N i ((chiU N i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i) * (e u).2 c)

end Glob

def blockJumps_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    π ∈ D.nd.Z i → IsHeckeGalois D.nd i π (r π) → IsBlockSum D.nd i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw),
      ∃ J : Multiset ℤ,
        IsJumpMultiset (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π))) τ J ∧
        IsJumpMultiset (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r π))) τ
          (J + blockJumps D.R.t)

def blockJumpsF {eps : ℝ} (Fm : FamP eps) (_CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, blockJumps_at (Fm.D x i)

def blockJumpsClosed (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm CH => blockJumpsF Fm CH)

theorem count_blockJumps (t : ℕ) (a : ℤ) :
    (blockJumps t).count a = if 0 ≤ a ∧ a < t then 1 else 0 := by
  have hn : (blockJumps t).Nodup := (Multiset.nodup_range t).map Nat.cast_injective
  have hm : a ∈ blockJumps t ↔ 0 ≤ a ∧ a < t := by
    simp only [blockJumps, Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨h0, h1⟩
      exact ⟨a.toNat, by omega, by omega⟩
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem hn (hm.2 h)
  · exact Multiset.count_eq_zero.2 (fun h' => h (hm.1 h'))

theorem blockJumps_at.mult {D : D7} (h : blockJumps_at D) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hπ : π ∈ D.nd.Z i) (hr : IsHeckeGalois D.nd i π (r π)) (hs : IsBlockSum D.nd i r ρ π)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ) :
    multV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r π))) τ a =
      multV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π))) τ a +
        (if 0 ≤ a ∧ a < D.R.t then 1 else 0) := by
  obtain ⟨J, h1, h2⟩ := h i r ρ π hπ hr hs w hw τ
  rw [h1.2, h2.2, Multiset.count_add, count_blockJumps]
  push_cast
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.BlockJumpCount

end
