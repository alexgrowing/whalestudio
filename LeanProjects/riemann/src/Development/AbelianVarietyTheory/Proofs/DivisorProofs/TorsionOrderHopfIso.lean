import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPairingFunctorialStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem natFn_eq_of_eq_on {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (K : Type) [Field K]
    [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {N : ℕ} (hG : IsSemiAbelian G) (hN : N ≠ 0)
    (σ τ : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → B) (hσ : IsNatFn G N σ) (hτ : IsNatFn G N τ)
    (h : ∀ x, σ K x = τ K x) (B : Type) [CommRing B] [Algebra R B] (x : Tors G N B) : σ B x = τ B x := by
  have := GlobalTheory.T.torsion_pairing_functorial R K G hG N N hN hN (fun B _ _ x _ => σ B x - τ B x)
    (fun B C _ _ _ _ φ x _ => by simp only [map_sub, hσ B C φ x, hτ B C φ x]) (fun x _ => sub_eq_zero.2 (h x)) B x 1
  exact sub_eq_zero.1 this

theorem exists_torsPt_of_ord : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] (io : A ≃ₐ[R] ord G N K), (∀ a b : Tors G N K, toConv (((Pi.evalAlgHom R (fun _ : Tors G N K => K) (a * b)).comp (ord G N K).val).comp io.toAlgHom) = toConv (((Pi.evalAlgHom R (fun _ : Tors G N K => K) a).comp (ord G N K).val).comp io.toAlgHom) * toConv (((Pi.evalAlgHom R (fun _ : Tors G N K => K) b).comp (ord G N K).val).comp io.toAlgHom)) → ∃ θ : TorsPt G N A, ∀ (x : Tors G N K) (a : A), θ.pt K x a = (io a : Tors G N K → K) x := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN A _ _ io hmul
  have hex : ∀ a : A, ∃ σ : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → B,
      IsNatFn G N σ ∧ ∀ x, σ K x = (io a : Tors G N K → K) x := fun a => by
    obtain ⟨σ, hσ, h⟩ := (io a).2 1
    exact ⟨σ, hσ, fun x => by rw [h x, _root_.one_mul]⟩
  choose σ hσ hσK using hex
  have sep := natFn_eq_of_eq_on K hG hN
  have natMul : ∀ a b : A, IsNatFn G N (fun B _ _ x => σ a B x * σ b B x) := fun a b B C _ _ _ _ φ z => by
    simp only [map_mul, hσ a B C φ z, hσ b B C φ z]
  have natAdd : ∀ a b : A, IsNatFn G N (fun B _ _ x => σ a B x + σ b B x) := fun a b B C _ _ _ _ φ z => by
    simp only [map_add, hσ a B C φ z, hσ b B C φ z]
  have natC : ∀ c : R, IsNatFn G N (fun B _ _ _ => algebraMap R B c) := fun c B C _ _ _ _ φ z =>
    (φ.commutes c).symm
  let pt : ∀ (B : Type) [CommRing B] [Algebra R B], Tors G N B → (A →ₐ[R] B) := fun B _ _ x =>
    { toFun := fun a => σ a B x
      map_one' := by
        have := sep (σ 1) _ (hσ 1) (natC 1) (fun x => by simp [hσK]) B x
        simpa using this
      map_mul' := fun a b => sep (σ (a * b)) _ (hσ _) (natMul a b) (fun x => by simp [hσK]) B x
      map_zero' := by
        have := sep (σ 0) _ (hσ 0) (natC 0) (fun x => by simp [hσK]) B x
        simpa using this
      map_add' := fun a b => sep (σ (a + b)) _ (hσ _) (natAdd a b) (fun x => by simp [hσK]) B x
      commutes' := fun c => sep (σ (algebraMap R A c)) _ (hσ _) (natC c) (fun x => by simp [hσK]) B x }
  have ptApp : ∀ (B : Type) [CommRing B] [Algebra R B] (x : Tors G N B) (a : A), pt B x a = σ a B x :=
    fun _ _ _ _ _ => rfl
  have ptNat : ∀ (B C : Type) [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] (φ : B →ₐ[R] C)
      (z : Tors G N B), pt C (torsMap φ z) = φ.comp (pt B z) := fun B C _ _ _ _ φ z => by
    ext a; exact hσ a B C φ z
  have ptK : ∀ x : Tors G N K, pt K x =
      ((Pi.evalAlgHom R (fun _ : Tors G N K => K) x).comp (ord G N K).val).comp io.toAlgHom := fun x => by
    ext a; simp [ptApp, hσK]
  refine ⟨⟨pt, ptNat, fun B _ _ x y => ?_⟩, fun x a => hσK a x⟩
  apply WithConv.ofConv_injective
  ext a
  have := GlobalTheory.T.torsion_pairing_functorial R K G hG N N hN hN
    (fun B _ _ x y => σ a B (x * y) - (toConv (pt B x) * toConv (pt B y)).ofConv a) ?_ ?_ B x y
  · exact sub_eq_zero.1 this
  · intro B C _ _ _ _ φ x y
    have h1 : φ ((toConv (pt B x) * toConv (pt B y)).ofConv a) =
        (toConv (pt C (torsMap φ x)) * toConv (pt C (torsMap φ y))).ofConv a := by
      rw [ptNat, ptNat, ← AlgHom.comp_convMul_distrib]; rfl
    have h2 : torsMap φ (x * y) = torsMap φ x * torsMap φ y := by
      apply Subtype.ext; simp [MonObj.comp_mul]
    simp only [map_sub, h1, ← h2, hσ a B C φ (x * y)]
  · intro x y
    rw [sub_eq_zero, hσK, ptK, ptK, ← hmul]
    rfl

end GlobalTheory.GroupBplus.Aff
