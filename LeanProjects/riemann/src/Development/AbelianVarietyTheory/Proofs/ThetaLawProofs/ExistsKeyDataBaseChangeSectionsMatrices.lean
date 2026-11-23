import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FinitePreimageOfIsPullbackOfFiniteBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyBaseChangeData

theorem via_mul {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} {l l' k : ℕ}
    (hk : l + l' = k) {a' b' : ∀ i, Γ(Y, L'.U i)} {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a)
    (hb : KeyVia.Via w l' b' b) : KeyVia.Via w k (fun i => a' i * b' i) (fun j => a j * b j) := by
  intro j i h
  rw [map_mul, map_mul, ha j i h, hb j i h, ← hk, pow_add, _root_.mul_mul_mul_comm]

theorem coords_mul {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (hx : KeyVia x' x f φ w) {n l k N : ℕ} (hk : n + l = k) {s : RR x n} {s' : RR x' n} {e : RR x l} {e' : RR x' l}
    {b : Fin N → RR x k} {b' : Fin N → RR x' k} {c : Fin N → R} (hs : SecVia x' x φ w s' s)
    (he : SecVia x' x φ w e' e) (hb : ∀ i, SecVia x' x φ w (b' i) (b i))
    (hc : Coords x b c (fun i => (show Γ(x.P.A.left, x.P.L.U i) from s.f i) * (show Γ(x.P.A.left, x.P.L.U i) from e.f i))) :
    Coords x' b' (fun i => f (c i))
      (fun i => (show Γ(x'.P.A.left, x'.P.L.U i) from s'.f i) * (show Γ(x'.P.A.left, x'.P.L.U i) from e'.f i)) := by
  obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
  have H := KeyVia.Via.comb (w := w) (l := k) (b' := fun i => (b' i).f) (b := fun i => (b i).f) f x.P.A.hom
    x'.P.A.hom hP.w hb c
  have H' := via_mul (w := w) hk (a' := s'.f) (b' := e'.f) (a := s.f) (b := e.f) hs he
  have H'' := (congrArg (KeyVia.Via w k _) (funext hc)).mp H'
  exact fun i => congrFun (KeyVia.Via.unique x.P.isLB H'' H) i

theorem exists_baseChange_data : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (R' : Type) [CommRing R'] (f : O →+* R') (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → ∃ (x' : KeyIn R') (φ : x'.P.A.left ⟶ x.P.A.left) (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (s' : Fin x'.P.g → RR x' n) (b' : ∀ j, Fin ((l - j * n) ^ x'.P.g) → RR x' (l - j * n)) (m' : _), KeyVia x' x f φ w ∧ (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) ∧ (∀ j k, SecVia x' x φ w (b' j k) (b j (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)))) ∧ (∀ j ≤ x'.P.g, IsBasis x' (b' j)) ∧ IsMul x' l s' b' m' ∧ (∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j' (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg)))) ∧ (Finite (Sp R') → FinZ x s → FinZ x' s') := by
  intro laws O _ _ _ R' _ f x n l s b m hl hb hm
  obtain ⟨x', hx'⟩ := KeyPow.exists_keyPB_ring x f
  obtain ⟨φ, w, hx⟩ := (KeyVia.main O R' x x' f).1.1 hx'
  have hg : x'.P.g = x.P.g := by
    obtain ⟨-, hg, -⟩ := hx
    exact hg
  obtain ⟨⟨A', ab, g', sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := x'
  obtain rfl : g' = x.P.g := hg
  let x' : KeyIn R' := ⟨⟨A', ab, x.P.g, sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩
  have hex := ((KeyVia.main O R' x x' f).2 φ w hx).1
  choose s' hs' using fun i => (hex _ (s i)).exists
  choose b' hb' using fun j k => (hex _ (b j k)).exists
  refine ⟨x', φ, w, rfl, s', b', fun i j j' => (m i j j').map f, hx, hs', hb', fun j hj => ?_,
    fun i j hj k => ?_, fun _ _ _ _ _ => rfl, fun hfin hz => ?_⟩
  · have h₁ : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
    exact (KeyBasis.main laws O x (l - j * n) (by omega)).2 (b j) (hb j hj) R' f x' φ w (b' j) hx (hb' j)
  · have h₁ : (j + 1) * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
    have h₂ : n + (l - (j + 1) * n) = l - j * n := by
      rw [Nat.add_mul, Nat.one_mul] at h₁ ⊢
      omega
    exact coords_mul hx h₂ (hs' i) (hb' (j + 1) k) (hb' j) (hm i j hj k)
  · obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
    have hc : IsClosed {y : x.P.A.left | ∀ i, y ∉ Out.nonzeroLocus (s i)} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i => (Out.nonzeroLocus (s i)).isOpen.isClosed_compl
    haveI : IsProper x.P.A.hom := x.P.isAb.proper
    refine (KeyFin.finite_preimage_of_isPullback_of_finite_base _ _ _ _ _ _ _ _ _ inferInstance inferInstance
      hP hfin hc hz).subset fun y hy i h => hy i ?_
    exact EtBaseChange.mem_nonzeroLocus_via (hs' i) y h

end GlobalTheory.KeyBaseChangeData
end
