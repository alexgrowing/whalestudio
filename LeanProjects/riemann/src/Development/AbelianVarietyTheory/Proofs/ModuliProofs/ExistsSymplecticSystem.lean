import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStdSympZmod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticTorsionSystemIsGeometricBasis
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EllipticLevel

theorem exists_stdSymp_of_rel {k g : ℕ} (hk : 0 < k) {G R : Type} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ d, d ∣ k → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze k)
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ k = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ k = 1 → (∀ y, y ^ k = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ k = 1) ∧ ∀ i j, W (v i) (v j) (ze ^ Out.stdSymp g i j) := by
  classical

  set H : Subgroup G := (powMonoidHom k : G →* G).ker with hH
  have memH : ∀ x : G, x ∈ H ↔ x ^ k = 1 := fun x => by
    rw [hH, MonoidHom.mem_ker, powMonoidHom_apply]
  have torsH : ∀ x : H, (x : G) ^ k = 1 := fun x => (memH x).1 x.2

  let f : H → H → Rˣ := fun x y => (hW x y (torsH x) (torsH y)).exists.choose
  have hf : ∀ x y : H, W x y (f x y) := fun x y => (hW x y (torsH x) (torsH y)).exists.choose_spec
  have uniq : ∀ (x y : H) (c : Rˣ), W x y c → c = f x y := fun x y c h =>
    (hW x y (torsH x) (torsH y)).unique h (hf x y)
  have fswap : ∀ x y : H, f y x = (f x y)⁻¹ := fun x y =>
    (uniq y x _ (hsymm _ _ _ (hf x y))).symm
  have fmulL : ∀ x x' y : H, f (x * x') y = f x y * f x' y := fun x x' y =>
    (uniq _ _ _ (hmul _ _ _ _ _ (hf x y) (hf x' y))).symm
  have fmulR : ∀ x y y' : H, f x (y * y') = f x y * f x y' := fun x y y' => by
    rw [← uniq x (y * y') _ (hsymm _ _ _ (hmul _ _ _ _ _ (hf y x) (hf y' x))), fswap x y, fswap x y',
      mul_inv, inv_inv, inv_inv]
  let e : H →* H →* Rˣ :=
    MonoidHom.mk' (fun x => MonoidHom.mk' (f x) (fmulR x)) (fun x x' => by
      ext y
      simp only [MonoidHom.mk'_apply, MonoidHom.mul_apply]
      rw [fmulL])
  have heq : ∀ x y : H, e x y = f x y := fun _ _ => rfl

  have hcH : ∀ d : ℕ, d ∣ k → Nat.card {x : H // x ^ d = 1} = d ^ (2 * g) := by
    intro d hd
    obtain ⟨m, hm⟩ := hd
    have eqv : {x : H // x ^ d = 1} ≃ {x : G // x ^ d = 1} :=
      { toFun := fun x => ⟨x.1, by simpa using congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, (memH _).2 (by rw [hm, pow_mul, y.2, one_pow])⟩,
          Subtype.ext (by simpa using y.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr eqv]
    exact hc d ⟨m, hm⟩
  have hkH : ∀ x : H, x ^ k = 1 := fun x => Subtype.ext (by simpa using torsH x)
  have halt' : ∀ x : H, e x x = 1 := fun x => by
    rw [heq]
    exact (uniq x x 1 (halt x (torsH x))).symm
  have hnd' : ∀ x : H, (∀ y, e x y = 1) → x = 1 := by
    intro x hx
    apply Subtype.ext
    refine hnd x (torsH x) (fun y hy => ?_)
    have h1 := hf x ⟨y, (memH y).2 hy⟩
    rwa [← heq, hx] at h1
  obtain ⟨v, hv⟩ := GlobalTheory.exists_stdSymp_of_alternating_pairing k g H R ze hk hz hkH hcH e halt' hnd'
  refine ⟨fun i => (v i : G), fun i => torsH (v i), fun i j => ?_⟩
  have h2 := hf (v i) (v j)
  rwa [← heq, hv i j] at h2

theorem exists_symplectic_system (hL : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (k : ℕ)
    (hk : (k : K) ≠ 0) (ze : Kˣ) (hze : IsPrimitiveRoot ze k) :
    ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), (∀ i, pt i ^ k = 1) ∧
      ∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j) := by
  obtain ⟨-, -, -, -, -, hmn, -, -, -, hw, hwn, -⟩ := hL
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have := P.isAb.comm

  have hc : ∀ d, d ∣ k → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} = d ^ (2 * P.g) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hk0
    have hdK : (d : K) ≠ 0 := by
      obtain ⟨m, rfl⟩ := hd
      intro h0
      apply hk
      rw [Nat.cast_mul, h0, zero_mul]
    exact ((hmn (Sp K) P d hd0).2.2.2.2 K (𝟙 _) hdK)

  have hleft : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = a := fun a => by simp
  have hleft' : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a) = a := fun a => by simp
  haveI : IsDomain Γ(Sp K, ⊤) := Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (Function.LeftInverse.injective hleft')
  have hz' : IsPrimitiveRoot (unitOn ze) k :=
    hze.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)
      (Units.map_injective (Function.LeftInverse.injective hleft))
  have hwB := hw (Sp K) P k (Out.baseOver (Sp K))
  obtain ⟨v, hv1, hv2⟩ := exists_stdSymp_of_rel (G := Out.baseOver (Sp K) ⟶ P.A) (R := Γ(Sp K, ⊤)) hk0 hc hz'
    (fun x y c => Out.WeilIs P.A P.L k x y c) hwB.1 hwB.2.1 hwB.2.2.1
    (fun _ _ _ h => GlobalTheory.CommPairing.weilIs_symm P.isLB h) (fun x hx h => hwn K P k hk x hx h)
  exact ⟨v, hv1, hv2⟩

end GlobalTheory.EllipticLevel

namespace GlobalTheory

end GlobalTheory
