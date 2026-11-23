import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CvZeroTerm
import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.VSumPowNonneg

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03
open Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W}

theorem crystalline_to_deRham_injective (T : LocLat G Qp LL O) : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem levelExpansion_smul
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) (k : ℤ) :
    Lb.levB T i ζ (a • x) k = cv (W.lev i ζ a) (Lb.levB T i ζ x) k := by
  obtain ⟨m, hm⟩ := Lb.supp T i ζ x
  apply crystalline_to_deRham_injective (PD := PD) (LL := LL) T
  rw [← levN_eq, W.levN_smul, cv_map _ _ _ m hm]
  unfold cv
  congr 1
  funext j
  rw [levN_eq]

theorem level_pi_constantCoeff_zero (i : ZMod n) :
    PowerSeries.constantCoeff (W.lev i 1 (letπ : LetA O n)) = 0 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π i 1 ⟨0, by simp⟩
  have h := congrArg PowerSeries.constantCoeff hE
  simp only [map_add, map_mul, hE0, mul_one, map_one] at h
  linear_combination h

theorem levelExpansion_neg_eq_zero
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hs1 : W.s = 1) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (T : LocLat G Qp LL O)
    (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) (i : ZMod n) (x : ↥(W.N T)) (k : ℤ) (hk : k < 0) :
    Lb.levB T i 1 x k = 0 := by
  have hX : PowerSeries.constantCoeff (W.lev i 1 W.X) = 0 := by
    have : W.X = (letπ : LetA O n) := by
      show (W.φA ^ (W.s - 1)) _ = _
      rw [hs1, Nat.sub_self, pow_zero]
      rfl
    rw [this]
    exact level_pi_constantCoeff_zero (W := W) i
  apply crystalline_to_deRham_injective (PD := PD) (LL := LL) T
  rw [← levN_eq, map_zero]
  exact ((hP4.1 i 1 ⟨0, by simp⟩ hX).1 x k).2 hk

theorem level_pi0_X_pow_dvd
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (i : ZMod n) : (PowerSeries.X : PowerSeries LL) ^ (PD.p - 1) ∣ W.lev i 1 W.π₀ := by
  obtain ⟨w, hw⟩ := hp9.2.2.1
  rw [hw, map_mul, map_pow]
  refine Dvd.dvd.mul_left (pow_dvd_pow_of_dvd ?_ _) _
  rw [PowerSeries.X_dvd_iff]
  exact level_pi_constantCoeff_zero (W := W) i

theorem levelExpansion_gamma
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T W.gam (x : W.DD T) ∈ W.N T) (k : ℤ) :
    Lb.levB T i 1 ⟨W.γD T W.gam (x : W.DD T), hx⟩ k =
      (algebraMap O LL (W.χΓ W.gam : O)) ^ k • Lb.levB T i 1 x k := by
  refine levB_Γ T hT W.gam i 1 1 0 1 (by simp) ?_ (by simp) x hx k
  rw [Nat.cast_one, W.gam_gen]
  simp

theorem expansion_at_one
    (levN_eq : ∀ (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (levB_Γ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : W.Gam) (i : ZMod n) (ζ ζ' : LL) (j a : ℕ),
      IsPrimitiveRoot ζ (PD.p ^ j) → (j : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - (a : LL)) →
      ζ' = ζ ^ a → ∀ (x : ↥(W.N T)) (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ),
      Lb.levB T i ζ ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Lb.levB T i ζ' x k)
    (hs1 : W.s = 1) (hp2 : PD.p ≠ 2) {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (i : ZMod n) (x y : ↥(W.N T)) (M : ℕ) (hx : W.γD T W.gam (x : W.DD T) ∈ W.N T)
    (hxy : W.γD T W.gam (x : W.DD T) - (x : W.DD T) = W.π₀ ^ M • (y : W.DD T))
    (k : ℤ) (hk0 : 0 < k) (hk : k < (((PD.p - 1) * M : ℕ) : ℤ)) : Lb.levB T i 1 x k = 0 := by
  have hsub : (⟨W.γD T W.gam (x : W.DD T), hx⟩ : ↥(W.N T)) - x = W.π₀ ^ M • y := Subtype.ext (by
    rw [Submodule.coe_sub, Submodule.coe_smul]
    exact hxy)
  have hz : Lb.levB T i 1 (W.π₀ ^ M • y) k = 0 := by
    rw [levelExpansion_smul levN_eq]
    refine cv_vanish _ _ (fun k hk => levelExpansion_neg_eq_zero levN_eq hs1 T hP4 i y k hk) ((PD.p - 1) * M) ?_ k hk
    rw [map_pow, pow_mul]
    exact pow_dvd_pow_of_dvd (level_pi0_X_pow_dvd hp9 i) M
  have he : Lb.levB T i 1 ⟨W.γD T W.gam (x : W.DD T), hx⟩ k - Lb.levB T i 1 x k = 0 := by
    rw [← Pi.sub_apply, ← map_sub, hsub]
    exact hz
  rw [levelExpansion_gamma levB_Γ T hT i x hx k] at he
  have he' : ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1) • Lb.levB T i 1 x k = 0 := by
    rw [sub_smul, one_smul]
    exact he
  have hu : (algebraMap O LL (W.χΓ W.gam : O)) ^ k ≠ 1 := by
    refine ValuationPow.zpow_ne_one v PD.p PD.hp hp2 W.v_l _ ?_ k hk0.ne'
    rw [W.gam_gen, hs1]
    simp
  exact (smul_eq_zero.1 he').resolve_left (sub_ne_zero.2 hu)

end Formalism.MainNotions.N.Ln03.Pf
