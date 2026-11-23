import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.WeilRoot

theorem eq_zpow_of_map_eq {O K : Type} [CommRing O] [IsDomain O] [Field K] (κ : O →+* K) {N : ℕ} (hN : 0 < N)
    (hu : IsUnit (N : O)) {ζ w : Oˣ} (hζ : IsPrimitiveRoot ζ N) (hw : w ^ N = 1) (m : ℤ)
    (h : Units.map κ.toMonoidHom w = Units.map κ.toMonoidHom (ζ ^ m)) : w = ζ ^ m := by
  have : NeZero N := ⟨hN.ne'⟩
  set y : Oˣ := w * (ζ ^ m)⁻¹ with hy
  have hyN : y ^ N = 1 := by
    rw [hy, _root_.mul_pow, hw, _root_.one_mul, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hζ.pow_eq_one, one_zpow, inv_one]
  have hζ' : IsPrimitiveRoot (ζ : O) N := IsPrimitiveRoot.coe_units_iff.2 hζ
  obtain ⟨i, hi, hiy⟩ := hζ'.eq_pow_of_pow_eq_one (ξ := (y : O)) (by rw [← Units.val_pow_eq_pow_val, hyN, Units.val_one])
  have hκ : IsPrimitiveRoot (κ ζ) N := by
    have : NeZero (N : K) := ⟨by simpa using (hu.map κ).ne_zero⟩
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic N κ]
    exact (hζ'.isRoot_cyclotomic hN).map
  have hκy : κ (y : O) = 1 := by
    have h' : κ (w : O) = κ ((ζ ^ m : Oˣ) : O) := congrArg (fun u : Kˣ => (u : K)) h
    rw [hy, Units.val_mul, map_mul, h', ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hi0 : i = 0 := by
    have h1 : κ (ζ : O) ^ i = 1 := by rw [← map_pow, hiy, hκy]
    have := hκ.dvd_of_pow_eq_one i h1
    exact Nat.eq_zero_of_dvd_of_lt this hi
  have hy1 : y = 1 := Units.ext (by rw [← hiy, hi0, pow_zero, Units.val_one])
  rw [hy] at hy1
  exact mul_inv_eq_one.1 hy1

end GlobalTheory.WeilRoot
end

noncomputable section
namespace GlobalTheory.WeilRoot

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem weilIs_zpow_of_fieldPoint : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), IsPPol A P → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (ζ : Oˣ), IsPrimitiveRoot ζ N → ∀ (m : ℤ) (K : Type) [Field K] (κ : O →+* K), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap κ)) ≫ u) (toUnit (Over.mk (spMap κ)) ≫ v) (unitOn (Units.map κ.toMonoidHom (ζ ^ m))) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom (ζ ^ m))) := by
  intro O _ _ A _ _ hA P hPP N hN hNu u v hu hv ζ hζ m K _ κ H k _ ρ
  obtain ⟨⟨hP, h₁, h₂, -⟩, hamp, -⟩ := hPP
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over (Sp O)) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over (Sp O)) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : 𝟙_ (Over (Sp O)) ⟶ A, z ^ N = 1 → ∀ p : (𝟙_ (Over (Sp O))).left, ∃ V : (𝟙_ (Over (Sp O))).left.Opens,
      p ∈ V ∧ ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag hP hB hB' (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts u hu) (lifts v hv)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts 1 (one_pow N)) (lifts v hv)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ = 1 := mul_eq_left.1 (CommutatorPairing.weilIs_unique hG hA hD h11 hc₁)
  have pw : ∀ n : ℕ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (u ^ (n + 1)) v (c₀ ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa using hc₀
    | succ n ih =>
      rw [pow_succ u (n + 1), pow_succ c₀ (n + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hu] at hp
  have hc₀N : c₀ ^ N = 1 := CommutatorPairing.weilIs_unique hG hA hD hp (e₁ ▸ hc₁)
  obtain ⟨w, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 c₀
  have hwN : w ^ N = 1 := by
    apply GlobalTheory.Ex.Specialise.unitOn_bijective.1
    have e : unitOn (w ^ N) = unitOn w ^ N := by unfold unitOn; exact map_pow _ _ _
    rw [e, hc₀N]
    unfold unitOn; exact (map_one _).symm
  have spec : ∀ (F : Type) [Field F] (σ : O →+* F), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N
      (toUnit (Over.mk (spMap σ)) ≫ u) (toUnit (Over.mk (spMap σ)) ≫ v) (unitOn (Units.map σ.toMonoidHom w)) := by
    intro F _ σ
    have hN' := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk (spMap σ))) hc₀
    have hl : (toUnit (Over.mk (spMap σ))).left = spMap σ := rfl
    rw [hl, GlobalTheory.Ex.Specialise.map_unitOn] at hN'
    exact hN'
  have e := GlobalTheory.Ex.Specialise.unitOn_bijective.1 (CommutatorPairing.weilIs_unique hG hA hD (spec K κ) H)
  have hw : w = ζ ^ m := eq_zpow_of_map_eq κ hN hNu hζ hwN m e
  rw [← hw]
  exact spec k ρ

end GlobalTheory.WeilRoot
end
