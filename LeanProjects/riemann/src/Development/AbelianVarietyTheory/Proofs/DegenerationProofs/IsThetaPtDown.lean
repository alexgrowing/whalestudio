import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ThetaNest
open ThetaCoord CommPairing GlobalLift

variable {S : Scheme.{0}} {T : Over S}

theorem isThetaPt_of_over (P : PolAV S) [Subsingleton T.left] {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (ho : Odd k) (hu : IsUnit (k : Γ(T.left, ⊤))) (H : IsThetaPtOver P k x v) :
    IsThetaPt P k x v := by
  refine ⟨ho, hu, fun p => ⟨⊤, trivial, ?_⟩⟩
  obtain ⟨h, hh⟩ := exists_section (T := T) (V := ⊤) (p := p) trivial
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  exact isThetaPtOver_pull P H _ h hi

theorem weilIs_one_left (hG : GlobalFnsSt) (P : PolAV S) {k : ℤ} {ν : LB.Gen (negLB P.A P.L k T)} (hν : ν.IsGen)
    (θ : ThetaGrp P.A P.L k T) : WeilIs P.A P.L k 1 θ.pt 1 := by
  obtain ⟨o, ho, hv⟩ := exists_symLift_one P.isLB hν 1
  rw [← ho.pt_eq]
  refine weilIs_of_commIsOf hG P.isAb P.isLB ((commIsOf_iff P.isLB _ _ _).2 fun Z r z J hJ => ?_)
  have e : translT P.A (1 : T ⟶ P.A) = 𝟙 _ := by
    rw [translT, ThetaAct.translPt_one, lift_fst_snd]
  rw [hv _ _ z J hJ, hv _ _ z J hJ, ho.pt_eq, e, map_one]
  simp

theorem isThetaPtOver_down (hG : GlobalFnsSt) (P : PolAV S) [Subsingleton T.left] {n m : ℕ} (ho : Odd (n * m))
    {I : Type} {x : I → (T ⟶ P.A)} {v v' : I → Γ(T.left, ⊤)} (hx : ∀ i, (x i ^ n) ^ m ^ 2 = 1)
    (H : IsThetaPtOver P (n * m) x v) (H' : IsThetaPtOver P m (fun i => x i ^ n) v') :
    IsThetaPtOver P m (fun i => x i ^ n) v := by
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · rwa [Subsingleton.elim v v']
  obtain ⟨th', s', α', τ', W, t', w', u', hth', hα', hτ', hs', hW, ht', hw', hv⟩ := H
  obtain ⟨th, s, α, τ, U, t, -, -, hth, hα, hτ, hs, hU, ht, -, -⟩ := H'
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec hth hth'
  obtain ⟨ν, hν, -⟩ := (hW i₀).sym
  obtain ⟨o, hoo, -⟩ := exists_symLift_one P.isLB hν ((n * m) ^ 2)
  obtain ⟨u, hu⟩ := exists_unit_isValueAt hG P.isAb P.isLB (r := n) (q := m ^ 2) rfl
    (pow_dvd_pow_of_dvd (Dvd.intro_left n rfl) 2) ho.pow hρ hα hα' hs hs' hτ' (one_pow n) hoo hτ
  refine ⟨th, s, α, τ, U, t, fun i => ρ * u * w' i, u' * (ρ * u)⁻¹, hth, hα, hτ, hs, hU, ht, fun i => ?_, fun i => ?_⟩
  · have := hu (x i) (U i) (t i) (W i) (t' i) (w' i) 1
      (by rw [show (n * m) ^ 2 = n * m ^ 2 * n by ring, pow_mul, pow_mul, hx, one_pow]) (hU i) (ht i)
      (by rw [_root_.mul_one]; exact hW i) (ht' i) (hw' i)
      (by rw [← (hW i).pt_eq]; exact weilIs_one_left hG P hν _)
    rwa [one_pow, Units.val_one, _root_.mul_one] at this
  · rw [hv, ← Units.val_mul, ← _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel_right]

theorem isThetaPt_down : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (n m : ℕ) (Ix : Type)
    (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → Γ((baseOver (Sp K)).left, ⊤)),
    (∀ i, (x i ^ n) ^ m ^ 2 = 1) → IsThetaPt P (n * m) x v → IsThetaPt P m (fun i => x i ^ n) v := by
  intro hL K _ _ P n m Ix x v hx H
  haveI : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have ho : Odd m := (Nat.odd_mul.1 H.1).2
  have hu : IsUnit (m : Γ((baseOver (Sp K)).left, ⊤)) :=
    isUnit_of_mul_isUnit_right (by rw [← Nat.cast_mul]; exact H.2.1)
  have hK : (m : K) ≠ 0 := by
    have := IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom hu
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨v', H'⟩ := ThetaPtExist.exists_isThetaPt hL K P m ho hK (fun i => x i ^ n) hx
  exact isThetaPt_of_over P ho hu (isThetaPtOver_down hL.globalFns P H.1 hx (isThetaPtOver_of_subsingleton P H)
    (isThetaPtOver_of_subsingleton P H'))

end GlobalTheory.ThetaNest
