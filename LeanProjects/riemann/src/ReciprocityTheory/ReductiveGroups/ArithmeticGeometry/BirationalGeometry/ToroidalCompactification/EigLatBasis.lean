import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

def eigLat {O : Type} (act : O → (G ⟶ G)) [∀ a, IsMonHom (act a)] (χ : O → R) : Submodule R (Fin n → R) :=
  ⨅ a, LinearMap.ker (tmap hx (act a) - χ a • LinearMap.id)

theorem eigLat_basis [IsDomain R] [IsPrincipalIdealRing R] {O : Type} (act : O → (G ⟶ G)) [∀ a, IsMonHom (act a)]
    (χ : O → R) : ∃ k, Nonempty (Module.Basis (Fin k) R (eigLat hx act χ)) := by
  obtain ⟨k, bk⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin n)) (eigLat hx act χ)
  exact ⟨k, ⟨bk⟩⟩

def dualMapR {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') : DualNumber R →+* DualNumber R' where
  toFun a := TrivSqZeroExt.inl (φ a.fst) + TrivSqZeroExt.inr (φ a.snd)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

def TanBCSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (n : ℕ)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G), IsUnivChart G n x →
    letI := φ.toAlgebra
    ∃ x' : ∀ m : ℕ, sp (R₀ := R') (JetR R' (Fin n) m) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj G,
      IsUnivChart _ n x' ∧ ∀ c : Fin n → R,
        (tvec (x := x') (φ ∘ c)).left ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (dualMapR φ)) ≫ (tvec (x := x) c).left

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

def RankSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V]
    (G : SAB H (Spec (CommRingCat.of V))) (t' : SAB H (Spec (CommRingCat.of (FractionRing V))))
    (_m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))))
    (n : ℕ) (xc : ∀ m : ℕ, sp (R₀ := V) (JetR V (Fin n) m) ⟶ G.G) (hx : IsUnivChart G.G n xc) (χ : 𝓞 E →+* V) (ρ : V),
    (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (FractionRing V) k],
      DetCond D t'.act (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) k)))
        (algebraMap (FractionRing V) k (algebraMap V (FractionRing V) ρ))) →
    letI : ∀ a, IsMonHom (G.act.act a) := G.act.hom
    (χ H.rt = ρ → Module.finrank V (eigLat hx G.act.act χ) = D.p) ∧
      (χ H.rt ≠ ρ → Module.finrank V (eigLat hx G.act.act χ) = D.q)

end ReciprocityTheory.ChartRestriction.G.Chart
