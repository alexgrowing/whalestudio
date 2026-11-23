import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingLevelStructureFiniteFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualityTensorPairingCompatStatement
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

theorem bialgHom_dual_integral_of_pairs : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (θ : TorsPt G N A), IsLevel K θ → ∀ F : K ⊗[R] CartierDual R A →ₐc[K] K ⊗[R] A, (∀ (B : Type) [CommRing B] [Algebra R B] (z z' : Tors G N B), ∃ c : B, ∀ (ψ : B →ₐ[R] K) (s s' : A →ₐ[R] R), θ.pt K (torsMap ψ z) = (Algebra.ofId R K).comp s → θ.pt K (torsMap ψ z') = (Algebra.ofId R K).comp s' → ψ c = Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp s') (fun _ _ => .all _ _) (F ((1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R A)))) → ∀ l : CartierDual R A, ∃ a : A, F ((1 : K) ⊗ₜ[R] l) = (1 : K) ⊗ₜ[R] a := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN A _ _ _ _ _ θ hθ F hF
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  choose s hs using fun x : A →ₐ[R] K => exists_algHom_comp_eq (A := R) x
  have hinj : ∀ u v : A →ₐ[R] R, (Algebra.ofId R K).comp u = (Algebra.ofId R K).comp v → u = v := by
    intro u v h
    ext a
    exact IsFractionRing.injective R K (DFunLike.congr_fun h a)
  let E : (A →ₐ[R] R) → (A →ₐ[R] K) → K := fun u y =>
    Algebra.TensorProduct.lift (AlgHom.id K K) y (fun _ _ => .all _ _)
      (F ((1 : K) ⊗ₜ[R] (toConv u.toLinearMap : CartierDual R A)))
  have hmul : ∀ (u v : WithConv (A →ₐ[R] R)) y, E (u * v).ofConv y = E u.ofConv y * E v.ofConv y := by
    intro u v y
    simp only [E]
    rw [AlgHom.toLinearMap_convMul, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
  have hone : ∀ y, E (1 : WithConv (A →ₐ[R] R)).ofConv y = 1 := by
    intro y
    simp only [E]
    rw [AlgHom.toLinearMap_convOne, ← Algebra.TensorProduct.one_def, map_one, map_one]
  have hgl : ∀ u : A →ₐ[R] R,
      IsGroupLikeElem K (F ((1 : K) ⊗ₜ[R] (toConv u.toLinearMap : CartierDual R A))) := by
    intro u
    have h1 : IsGroupLikeElem R (toConv u.toLinearMap : CartierDual R A) :=
      (CartierDual.isGroupLikeElem_dual_iff _).2 ⟨map_one u, map_mul u⟩
    have h2 : IsGroupLikeElem K ((1 : K) ⊗ₜ[R] (toConv u.toLinearMap : CartierDual R A)) := by
      rw [isGroupLikeElem_tensor_iff]
      simp [h1.counit_eq_one, h1.comul_eq_tmul_self, Algebra.TensorProduct.one_def]
    exact h2.map F
  have hlift : ∀ (y : A →ₐ[R] K) (t : K ⊗[R] A),
      Algebra.TensorProduct.lift (AlgHom.id K K) y (fun _ _ => .all _ _) t =
        Algebra.TensorProduct.productMap (AlgHom.id R K) y t := by
    intro y t
    induction t with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp
  obtain ⟨T, hT⟩ := GlobalTheory.T.weil_pairing_level_structure_finite_flat R K G hG N hN A θ hθ (fun x y => E (s x) y) (by
    intro x y z w hz
    constructor
    · have : s z = (toConv (s x) * toConv (s y)).ofConv := by
        apply hinj
        rw [AlgHom.comp_convMul_distrib, ofConv_toConv, ofConv_toConv, hs, hs, hs, ← hz]
      show E (s z) w = _
      rw [this, hmul]
    · have hz' : z = (toConv x * toConv y).ofConv := by rw [← hz]
      simp only [E, hlift]
      rw [hz', productMap_convMul_of_isGroupLikeElem (hgl _)]) (by
    intro x y h0
    have h := hmul (toConv (s x))⁻¹ (toConv (s x)) y
    rw [inv_mul_cancel, hone, ofConv_toConv] at h
    have h0' : E (s x) y = 0 := h0
    rw [h0', mul_zero] at h
    exact one_ne_zero h) (by
    intro B _ _ z z'
    obtain ⟨c, hc⟩ := hF B z z'
    refine ⟨c, fun ψ => ?_⟩
    have := hc ψ (s _) (s _) (hs _).symm (hs _).symm
    rw [hs] at this
    exact this)
  refine GlobalTheory.T.exists_map_one_tmul_cartierDual_eq_one_tmul R K A F.toLinearMap T fun u v => ?_
  have h := hT ((Algebra.ofId R K).comp u) ((Algebra.ofId R K).comp v)
  rw [hinj _ _ (hs _)] at h
  refine Eq.trans ?_ h
  clear h hT
  induction T with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b => simp [Algebra.ofId_apply]

end GlobalTheory.GroupBplus.Aff
