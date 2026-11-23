import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
open scoped TensorProduct

namespace GlobalTheory.GenericFibreInt

theorem exists_nat_mul_mem (F : Type) [Field F] [NumberField F] (c : F) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ o : 𝓞 F, (N : F) * c = algebraMap (𝓞 F) F o := by
  obtain ⟨y, hy, hi⟩ :=
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  let o : 𝓞 F := ⟨y • c, hi⟩
  have key : algebraMap (𝓞 F) F o = (y : F) * c := by
    simp [o, zsmul_eq_mul]
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · refine ⟨o, ?_⟩
    have h' : ((y.natAbs : ℤ) : F) = (y : F) := by rw [← h]
    rw [key, ← h', Int.cast_natCast]
  · refine ⟨-o, ?_⟩
    have h' : ((y.natAbs : ℤ) : F) = -(y : F) := by
      rw [← Int.cast_neg]; congr 1; omega
    rw [map_neg, key, ← Int.cast_natCast, h', neg_mul]

theorem tensor_int (F A : Type) [Field F] [NumberField F] [CommRing A] [Algebra (𝓞 F) A]
    (t : A ⊗[𝓞 F] F) : ∃ N : ℕ, N ≠ 0 ∧ ∃ a : A, N • t = a ⊗ₜ[𝓞 F] (1 : F) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul a c =>
    obtain ⟨N, hN, o, ho⟩ := exists_nat_mul_mem F c
    refine ⟨N, hN, o • a, ?_⟩
    rw [← TensorProduct.tmul_smul, nsmul_eq_mul, ho, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨N₁, hN₁, a₁, e₁⟩ := h₁
    obtain ⟨N₂, hN₂, a₂, e₂⟩ := h₂
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, N₂ • a₁ + N₁ • a₂, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm N₁ N₂ t₁, e₁, e₂, TensorProduct.add_tmul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul']

theorem resG_resG' {Y : Scheme.{0}} {A B C : Y.Opens} (h₁ : B ≤ A) (h₂ : C ≤ B) (z : Γ(Y, A)) :
    resG Y h₂ (resG Y h₁ z) = resG Y (h₂.trans h₁) z := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_self' {Y : Scheme.{0}} {A : Y.Opens} (h : A ≤ A) (z : Γ(Y, A)) : resG Y h z = z := by
  simp only [resG]
  rw [show homOfLE h = 𝟙 A from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem app_resG' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) {U V : Z.Opens} (h : V ≤ U) (a : Γ(Z, U)) :
    (φ.app V).hom (resG Z h a) = resG Y (φ.preimage_mono h) ((φ.app U).hom a) := by
  change ((Z.presheaf.map (homOfLE h).op ≫ φ.app V).hom) a = _
  rw [Scheme.Hom.naturality]
  rfl

variable {F : Type} [Field F] [NumberField F] {X G : Scheme.{0}} {p : X ⟶ Sp (𝓞 F)} {q : G ⟶ Sp F}
  {j : G ⟶ X}

theorem integ (H : IsPullback j q p (spMap (algebraMap (𝓞 F) F))) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(G, j ⁻¹ᵁ U)) : ∃ N : ℕ, N ≠ 0 ∧ ∃ a : Γ(X, U), (N : Γ(G, j ⁻¹ᵁ U)) * s = (j.app U).hom a := by
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  have hle : j ⁻¹ᵁ U ⊓ q ⁻¹ᵁ ⊤ ≤ j ⁻¹ᵁ U := inf_le_left
  have hge : j ⁻¹ᵁ U ≤ j ⁻¹ᵁ U ⊓ q ⁻¹ᵁ ⊤ := le_inf le_rfl le_top
  obtain ⟨N, hN, a, ha⟩ :=
    tensor_int F Γ(X, U) ((ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p q j H U hU).symm (resG G hle s))
  refine ⟨N, hN, a, ?_⟩
  have e := congrArg (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p q j H U hU) ha
  rw [map_nsmul, RingEquiv.apply_symm_apply, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul, map_one, mul_one,
    nsmul_eq_mul] at e
  have e2 := congrArg (resG G hge) e
  rw [map_mul, map_natCast, resG_resG', resG_self'] at e2
  rw [e2]
  show ((j.appLE U _ inf_le_left ≫ G.presheaf.map (homOfLE hge).op).hom a) = _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE]

theorem eq_mul_inverse_pow {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (h : Γ(Y, U)) (V : Y.Opens)
    (E : V = Y.basicOpen h) (z : Γ(Y, V)) :
    ∃ (n : ℕ) (b : Γ(Y, U)), z * resG Y (E.le.trans (Y.basicOpen_le h)) h ^ n =
      resG Y (E.le.trans (Y.basicOpen_le h)) b := by
  subst E
  haveI := hU.isLocalization_basicOpen h
  obtain ⟨⟨b, _, n, rfl⟩, hb⟩ := IsLocalization.surj (Submonoid.powers h) z
  exact ⟨n, b, by rw [← map_pow]; exact hb⟩

end GlobalTheory.GenericFibreInt

namespace GlobalTheory.GenericFibreInt

theorem exists_nat_mul_eq_app : ∀ (F : Type) [Field F] [NumberField F] (X G : Scheme.{0}) (p : X ⟶ Sp (𝓞 F))
    (q : G ⟶ Sp F) (j : G ⟶ X), IsPullback j q p (spMap (algebraMap (𝓞 F) F)) →
    ∀ (W : G.Opens) (x : G), x ∈ W → ∀ (ι : Type) [Fintype ι] (g : ι → Γ(G, W)),
      ∃ (W' : X.Opens) (h : j ⁻¹ᵁ W' ≤ W), x ∈ j ⁻¹ᵁ W' ∧ ∃ (n : ℕ) (g' : ι → Γ(X, W')), n ≠ 0 ∧
        ∀ a, (n : Γ(G, j ⁻¹ᵁ W')) * resG G h (g a) = j.app W' (g' a) := by
  intro F _ _ X G p q j H W x hx ι _ g
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hjx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (j x)) isOpen_univ
  have hU' : IsAffineOpen (j ⁻¹ᵁ U) := TopForm.isAffineOpen_preimage_of_isPullback H hU
  obtain ⟨h, hle, hxh⟩ := hU'.exists_basicOpen_le (V := W ⊓ j ⁻¹ᵁ U) ⟨x, hx, hjx⟩ hjx
  obtain ⟨N₀, hN₀, h', hh'⟩ := integ H hU h
  have hunit : IsUnit (N₀ : Γ(G, j ⁻¹ᵁ U)) := by
    have : IsUnit (N₀ : F) := (Nat.cast_ne_zero.2 hN₀).isUnit
    simpa using this.map (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX q (j ⁻¹ᵁ U))
  have E : j ⁻¹ᵁ X.basicOpen h' = G.basicOpen h := by
    rw [Scheme.preimage_basicOpen, ← hh', Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit G hunit]
    exact inf_eq_right.2 (G.basicOpen_le h)
  have hVU : j ⁻¹ᵁ X.basicOpen h' ≤ j ⁻¹ᵁ U := E.le.trans (G.basicOpen_le h)
  have hVW : j ⁻¹ᵁ X.basicOpen h' ≤ W := E.le.trans (hle.trans inf_le_left)
  have key : ∀ a, ∃ N : ℕ, N ≠ 0 ∧ ∃ c : Γ(X, X.basicOpen h'),
      (N : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVW (g a) = (j.app (X.basicOpen h')).hom c := by
    intro a
    obtain ⟨n, b, hb⟩ := eq_mul_inverse_pow hU' h _ E (resG G hVW (g a))
    obtain ⟨N, hN, b', hb'⟩ := integ H hU b
    obtain ⟨u, hu⟩ : IsUnit (resG X (X.basicOpen_le h') h') := X.toRingedSpace.isUnit_res_basicOpen h'
    refine ⟨N, hN, resG X (X.basicOpen_le h') ((N₀ : Γ(X, U)) ^ n * b') * ((u⁻¹ : _ˣ) : Γ(X, _)) ^ n, ?_⟩
    have f1 : (j.app (X.basicOpen h')).hom (resG X (X.basicOpen_le h') ((N₀ : Γ(X, U)) ^ n * b')) =
        (N₀ : Γ(G, j ⁻¹ᵁ X.basicOpen h')) ^ n * N * resG G hVU b := by
      rw [app_resG', map_mul, map_pow, map_natCast, ← hb', map_mul, map_mul, map_pow, map_natCast, map_natCast,
        mul_assoc]
    have f2 : (j.app (X.basicOpen h')).hom (u : Γ(X, _)) = (N₀ : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVU h := by
      rw [hu, app_resG', ← hh', map_mul, map_natCast]
    have hJu : (j.app (X.basicOpen h')).hom (u : Γ(X, _)) * (j.app (X.basicOpen h')).hom ((u⁻¹ : _ˣ) : Γ(X, _)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have one : (N₀ : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVU h *
        (j.app (X.basicOpen h')).hom ((u⁻¹ : _ˣ) : Γ(X, _)) = 1 := by rw [← f2, hJu]
    rw [map_mul, map_pow, f1, ← hb]
    calc (N : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVW (g a)
        = (N : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVW (g a) * ((N₀ : Γ(G, j ⁻¹ᵁ X.basicOpen h')) * resG G hVU h *
          (j.app (X.basicOpen h')).hom ((u⁻¹ : _ˣ) : Γ(X, _))) ^ n := by rw [one, one_pow, mul_one]
      _ = _ := by ring
  choose Nf hNf c hc using key
  refine ⟨X.basicOpen h', hVW, E ▸ hxh, ∏ a, Nf a, fun a => ((∏ a' ∈ Finset.univ.erase a, Nf a' : ℕ) : Γ(X, _)) * c a,
    Finset.prod_ne_zero_iff.2 fun a _ => hNf a, fun a => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a), Nat.cast_mul, mul_assoc, hc a]
  show _ = (j.app (X.basicOpen h')).hom _
  rw [map_mul, map_natCast]

end GlobalTheory.GenericFibreInt
