import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
noncomputable section
namespace GlobalTheory.PhiGam.Model
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

section
variable (k : Type) [Field k]

theorem algebraMap_eq (c : k) : algebraMap k k⸨X⸩ c = HahnSeries.C c := by rw [HahnSeries.algebraMap_apply', ← HahnSeries.ofPowerSeries_C]; rfl

theorem smul_eq (c : k) (x : k⸨X⸩) : c • x = algebraMap k k⸨X⸩ c * x := by rw [algebraMap_eq, HahnSeries.C_mul_eq_smul]

instance towerA : IsScalarTower k k⸨X⸩ k⸨X⸩ := ⟨fun c x y => by
  rw [smul_eq, smul_eq k c, smul_eq_mul, smul_eq_mul, mul_assoc]⟩

instance towerB : IsScalarTower k k⟦X⟧ k⸨X⸩ := ⟨fun c a y => by
  rw [smul_eq k c, Algebra.smul_def (c • a), Algebra.smul_def a, Algebra.smul_def c, map_mul, mul_assoc]
  rfl⟩

theorem vv_eq : vv k = ((PowerSeries.X : k⟦X⟧) : k⸨X⸩) := by unfold vv; exact (HahnSeries.ofPowerSeries_X).symm

theorem vv_ne : vv k ≠ 0 := by unfold vv; exact HahnSeries.single_ne_zero one_ne_zero

def inv1 (c : k) : k⟦X⟧ := PowerSeries.invOfUnit (1 + PowerSeries.C c * PowerSeries.X) 1

theorem powerSeries_oneAddConstMulX_mul_inv (c : k) : (1 + PowerSeries.C c * PowerSeries.X) * inv1 k c = 1 := by unfold inv1; exact PowerSeries.mul_invOfUnit _ _ (by simp)

theorem hs (c : k) : PowerSeries.HasSubst (PowerSeries.X * inv1 k c : k⟦X⟧) := PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

def sb (c : k) : k⟦X⟧ →ₐ[k] k⟦X⟧ := PowerSeries.substAlgHom (hs k c)

theorem sb_X (c : k) : sb k c PowerSeries.X = PowerSeries.X * inv1 k c := PowerSeries.substAlgHom_X _

theorem sb_C (c d : k) : sb k c (PowerSeries.C d) = PowerSeries.C d := by
  rw [← mul_one (PowerSeries.C d), ← PowerSeries.smul_eq_C_mul, map_smul, map_one]

theorem sb_key (c : k) : sb k c (PowerSeries.X * inv1 k (-c)) = PowerSeries.X := by
  have hv := powerSeries_oneAddConstMulX_mul_inv k c
  have hs0 := congrArg (sb k c) (powerSeries_oneAddConstMulX_mul_inv k (-c))
  simp only [map_mul, map_add, map_one, sb_C, sb_X, map_neg] at hs0
  rw [map_mul, sb_X]
  linear_combination (PowerSeries.X * inv1 k c * PowerSeries.C c * PowerSeries.X * sb k c (inv1 k (-c))
      + PowerSeries.X) * hv + PowerSeries.X * inv1 k c * (1 + PowerSeries.C c * PowerSeries.X) * hs0

theorem sb_sb (c : k) (f : k⟦X⟧) : sb k c (sb k (-c) f) = f := by
  have h := sb_key k c
  simp only [sb, PowerSeries.coe_substAlgHom] at h ⊢
  rw [PowerSeries.subst_comp_subst_apply (hs k (-c)) (hs k c), h, PowerSeries.X_subst]

def sbE : k⟦X⟧ ≃+* k⟦X⟧ :=
  RingEquiv.ofBijective (sb k 1).toRingHom
    ⟨Function.LeftInverse.injective (g := sb k (-1)) (fun f => by simpa using sb_sb k (-1) f),
     Function.RightInverse.surjective (g := sb k (-1)) (fun f => sb_sb k 1 f)⟩

def gE : k⸨X⸩ ≃+* k⸨X⸩ := IsFractionRing.ringEquivOfRingEquiv (A := k⟦X⟧) (B := k⟦X⟧) (sbE k)

theorem gE_coe (a : k⟦X⟧) : gE k (a : k⸨X⸩) = ((sb k 1 a : k⟦X⟧) : k⸨X⸩) := IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := k⸨X⸩) (L := k⸨X⸩) (sbE k) a

def gA : k⸨X⸩ →ₐ[k] k⸨X⸩ :=
  { (gE k).toRingHom with
    commutes' := fun c => by
      change gE k ((algebraMap k k⟦X⟧ c : k⟦X⟧) : k⸨X⸩) = ((algebraMap k k⟦X⟧ c : k⟦X⟧) : k⸨X⸩)
      rw [gE_coe, AlgHom.commutes] }

end

def ringModel (p : ℕ) [Fact p.Prime] : RingPG (ZMod p) p where
  φ := FiniteField.frobeniusAlgHom (ZMod p) _
  γ := gA (ZMod p)
  φ_int a := ⟨a ^ p, by simp [ZMod.card]⟩
  γ_int a := ⟨_, gE_coe _ a⟩
  φ_v := ⟨1, by simp [ZMod.card]⟩
  γ_v := ⟨inv1 (ZMod p) 1, by simp [inv1], by
    change gE _ _ = _
    rw [vv_eq, gE_coe, sb_X, ← map_mul, ← map_one (HahnSeries.ofPowerSeries ℤ (ZMod p)), ← map_sub, ← map_mul]
    congr 1
    have := powerSeries_oneAddConstMulX_mul_inv (ZMod p) 1
    rw [map_one] at this
    linear_combination PowerSeries.X * this⟩
  comm x := by simp

section
variable {k : Type} [Field k]

def lin (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) : k⸨X⸩ →ₗ[k] k⸨X⸩ where
  toFun := σ
  map_add' := map_add σ
  map_smul' c x := by simp only [smul_eq, map_mul, AlgHom.commutes, RingHom.id_apply]

def unitMod {l : ℕ} (R : RingPG k l) (hγ : Function.Bijective R.γ) (n : ℕ) : ModPG R n k⸨X⸩ where
  φ _ := lin R.φ
  γ _ := lin R.γ
  φ_semi _ a x := map_mul R.φ a x
  γ_semi _ a x := map_mul R.γ a x
  etale _ := by
    rw [eq_top_iff]
    intro x _
    have : x = x • (lin R.φ 1) := by change x = x * R.φ 1; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  γ_bij _ := hγ
  comm _ x := R.comm x

def lat (k : Type) [Field k] (a : ℤ) : Submodule k⟦X⟧ k⸨X⸩ := Submodule.span k⟦X⟧ {vv k ^ a}

theorem mem_lat {a : ℤ} {y : k⸨X⸩} : y ∈ lat k a ↔ ∃ b : k⟦X⟧, (b : k⸨X⸩) * vv k ^ a = y := by
  unfold lat
  rw [Submodule.mem_span_singleton]
  simp only [Algebra.smul_def, LaurentSeries.coe_algebraMap]

theorem sh_lat (a b : ℤ) : sh a (lat k b) = lat k (a + b) := by
  unfold sh lat
  rw [Submodule.map_span, Set.image_singleton, zpow_add₀ (vv_ne k)]
  congr 1

theorem isLat_lat (a : ℤ) : IsLat (lat k a) := by
  unfold IsLat
  refine ⟨Submodule.fg_span_singleton _, ?_⟩
  rw [eq_top_iff]
  intro y _
  have hmem : vv k ^ a ∈ Submodule.span k⸨X⸩ ((lat k a : Submodule k⟦X⟧ k⸨X⸩) : Set k⸨X⸩) :=
    Submodule.subset_span (by unfold lat; exact Submodule.mem_span_singleton_self _)
  have hy : y = (y * (vv k ^ a)⁻¹) • vv k ^ a := by
    rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ (vv_ne k)), mul_one]
  rw [hy]
  exact Submodule.smul_mem _ _ hmem

theorem nab_apply (g : k⸨X⸩ →ₗ[k] k⸨X⸩) (y : k⸨X⸩) : nab g y = (vv k)⁻¹ * (g y - y) := rfl

theorem sb_sub (a : k⟦X⟧) : ∃ b : k⟦X⟧, sb k 1 a - a = PowerSeries.X * b := by
  refine ⟨inv1 k 1 * sb k 1 (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) a)
    - PowerSeries.mk fun p => PowerSeries.coeff (p + 1) a, ?_⟩
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const a]
  rw [map_add, map_mul, sb_X, sb_C]
  ring

theorem nab_coe (a : k⟦X⟧) : ∃ b : k⟦X⟧, nab (lin (gA k)) (a : k⸨X⸩) = b := by
  obtain ⟨b, hb⟩ := sb_sub a
  refine ⟨b, ?_⟩
  rw [nab_apply]
  change (vv k)⁻¹ * (gE k (a : k⸨X⸩) - (a : k⸨X⸩)) = _
  rw [gE_coe, show ((sb k 1 a : k⟦X⟧) : k⸨X⸩) - (a : k⸨X⸩) = ((sb k 1 a - a : k⟦X⟧) : k⸨X⸩) from
    (map_sub _ _ _).symm, hb, map_mul, ← vv_eq, inv_mul_cancel_left₀ (vv_ne k)]

theorem g_vinv : gE k (vv k)⁻¹ = (vv k)⁻¹ + 1 := by
  have h1 : gE k (vv k) = vv k * ((inv1 k 1 : k⟦X⟧) : k⸨X⸩) := by
    rw [vv_eq, gE_coe, sb_X, map_mul]
  have h2 : ((1 + PowerSeries.X : k⟦X⟧) : k⸨X⸩) * ((inv1 k 1 : k⟦X⟧) : k⸨X⸩) = 1 := by
    rw [← map_mul, ← map_one (HahnSeries.ofPowerSeries ℤ k)]
    congr 1
    simpa using powerSeries_oneAddConstMulX_mul_inv k 1
  have h3 : ((1 + PowerSeries.X : k⟦X⟧) : k⸨X⸩) = 1 + vv k := by rw [map_add, map_one, vv_eq]
  rw [h3] at h2
  rw [map_inv₀, h1, mul_inv, ← eq_inv_of_mul_eq_one_left h2, mul_add, mul_one,
    inv_mul_cancel₀ (vv_ne k)]

theorem nab_vinv : nab (lin (gA k)) (vv k)⁻¹ = (vv k)⁻¹ := by
  rw [nab_apply]
  change (vv k)⁻¹ * (gE k (vv k)⁻¹ - (vv k)⁻¹) = _
  rw [g_vinv, add_sub_cancel_left, mul_one]

theorem decomp {y : k⸨X⸩} (hy : y ∈ lat k (-1)) :
    ∃ (c : k) (b : k⟦X⟧), y = c • (vv k)⁻¹ + b := by
  obtain ⟨b, rfl⟩ := mem_lat.mp hy
  refine ⟨PowerSeries.constantCoeff b, PowerSeries.mk fun p => PowerSeries.coeff (p + 1) b, ?_⟩
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const b]
  rw [map_add, map_mul, ← vv_eq, HahnSeries.ofPowerSeries_C, smul_eq, algebraMap_eq, zpow_neg_one]
  linear_combination ((PowerSeries.mk fun p => PowerSeries.coeff (p + 1) b : k⟦X⟧) : k⸨X⸩) *
    mul_inv_cancel₀ (vv_ne k)

theorem heckeAlgebra_mapsTo_localisationLatticeSpan {y : k⸨X⸩} : y ∈ lat k 0 ↔ ∃ b : k⟦X⟧, (b : k⸨X⸩) = y := by rw [mem_lat]; simp only [zpow_zero, mul_one]

theorem vinv_mem : (vv k)⁻¹ ∈ lat k (-1) := mem_lat.mpr ⟨1, by rw [map_one, one_mul, zpow_neg_one]⟩

theorem coe_mem (b : k⟦X⟧) : (b : k⸨X⸩) ∈ lat k (-1) := mem_lat.mpr ⟨PowerSeries.X * b, by
  rw [map_mul, ← vv_eq, zpow_neg_one, mul_comm (vv k), mul_inv_cancel_right₀ (vv_ne k)]⟩

theorem vinv_eq : (vv k)⁻¹ = HahnSeries.single (-1) 1 := by
  unfold vv
  exact inv_eq_of_mul_eq_one_right (by rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one,
    HahnSeries.single_zero_one])

theorem coeff_decomp (c : k) (b : k⟦X⟧) : (c • (vv k)⁻¹ + (b : k⸨X⸩)).coeff (-1) = c := by
  rw [vinv_eq, HahnSeries.coeff_add, HahnSeries.coeff_smul, PowerSeries.coeff_coe]
  simp

theorem step (x c : k) (b : k⟦X⟧) : ∃ b' : k⟦X⟧,
    (nab (lin (gA k)) - algebraMap k (Module.End k k⸨X⸩) x) (c • (vv k)⁻¹ + b)
      = ((1 - x) * c) • (vv k)⁻¹ + b' := by
  obtain ⟨b₁, hb₁⟩ := nab_coe (k := k) b
  refine ⟨b₁ - PowerSeries.C x * b, ?_⟩
  rw [LinearMap.sub_apply, Module.algebraMap_end_apply, map_add, map_smul, nab_vinv, hb₁]
  simp only [smul_eq k, algebraMap_eq, map_sub, map_mul, map_one, HahnSeries.ofPowerSeries_C]
  ring

theorem steps (x : k) (m : ℕ) : ∀ (c : k) (b : k⟦X⟧), ∃ b' : k⟦X⟧,
    ((nab (lin (gA k)) - algebraMap k (Module.End k k⸨X⸩) x) ^ m) (c • (vv k)⁻¹ + b)
      = ((1 - x) ^ m * c) • (vv k)⁻¹ + b' := by
  induction m with
  | zero => intro c b; exact ⟨b, by simp⟩
  | succ m ih =>
    intro c b
    obtain ⟨b₁, hb₁⟩ := step x c b
    obtain ⟨b₂, hb₂⟩ := ih ((1 - x) * c) b₁
    refine ⟨b₂, ?_⟩
    rw [pow_succ, Module.End.mul_apply, hb₁, hb₂, pow_succ, mul_assoc]

theorem condC : CondC (lin (gA k)) (lat k (-1)) := by
  rw [condC_iff_nab_mem]
  intro y hy
  obtain ⟨c, b, rfl⟩ := decomp hy
  obtain ⟨b₁, hb₁⟩ := nab_coe (k := k) b
  rw [map_add, map_smul, nab_vinv, hb₁]
  exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ c vinv_mem) (coe_mem b₁)

theorem sen_one : sen (lin (gA k)) (lat k (-1)) 1 = 1 := by
  have key : ∀ S : Submodule k k⸨X⸩, (∀ c : k, c • (vv k)⁻¹ ∈ S) → (∀ y ∈ S, y ∈ lat k (-1)) →
      Module.finrank k (↥S ⧸ ((lat k 0).restrictScalars k).submoduleOf S) = 1 := by
    intro S h1 h2
    let φ : S →ₗ[k] k :=
      { toFun := fun y => (y : k⸨X⸩).coeff (-1)
        map_add' := fun y z => by simp [HahnSeries.coeff_add]
        map_smul' := fun c y => by simp [HahnSeries.coeff_smul] }
    have hφ : Function.Surjective φ := fun c => ⟨⟨_, h1 c⟩, by
      show (c • (vv k)⁻¹ : k⸨X⸩).coeff (-1) = c
      simpa using coeff_decomp (k := k) c 0⟩
    have hker : LinearMap.ker φ = ((lat k 0).restrictScalars k).submoduleOf S := by
      ext ⟨y, hy⟩
      rw [LinearMap.mem_ker, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        Submodule.restrictScalars_mem]
      change y.coeff (-1) = 0 ↔ y ∈ lat k 0
      obtain ⟨c, b, rfl⟩ := decomp (h2 _ hy)
      rw [coeff_decomp]
      constructor
      · intro hc
        rw [hc, zero_smul, zero_add]
        exact heckeAlgebra_mapsTo_localisationLatticeSpan.mpr ⟨b, rfl⟩
      · intro h
        obtain ⟨a, ha⟩ := heckeAlgebra_mapsTo_localisationLatticeSpan.mp h
        have h3 := congrArg (fun z : k⸨X⸩ => z.coeff (-1)) ha
        simp only [coeff_decomp] at h3
        rw [← h3, PowerSeries.coeff_coe]
        simp
    rw [← hker, (φ.quotKerEquivOfSurjective hφ).finrank_eq, Module.finrank_self]
  have hQ : sh 1 (lat k (-1)) = lat k 0 := by rw [sh_lat]; norm_num
  unfold sen qmult gmult
  rw [hQ]
  apply key
  · intro c
    refine Submodule.mem_inf.mpr ⟨Submodule.smul_of_tower_mem _ c vinv_mem, ?_⟩
    refine Submodule.mem_iSup_of_mem 1 ?_
    obtain ⟨b', hb'⟩ := steps (k := k) 1 1 c 0
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
    have e : c • (vv k)⁻¹ = c • (vv k)⁻¹ + ((0 : k⟦X⟧) : k⸨X⸩) := by simp
    rw [e, hb', sub_self, zero_pow one_ne_zero, zero_mul, zero_smul, zero_add]
    exact heckeAlgebra_mapsTo_localisationLatticeSpan.mpr ⟨b', rfl⟩
  · intro y hy
    exact (Submodule.mem_inf.mp hy).1

theorem sen_ne {x : k} (hx : x ≠ 1) : sen (lin (gA k)) (lat k (-1)) x = 0 := by
  have key0 : ∀ (S : Submodule k k⸨X⸩) (P : Submodule k S), P = ⊤ → Module.finrank k (↥S ⧸ P) = 0 := by
    rintro S P rfl
    have : Subsingleton (↥S ⧸ (⊤ : Submodule k S)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton
  have hQ : sh 1 (lat k (-1)) = lat k 0 := by rw [sh_lat]; norm_num
  unfold sen qmult gmult
  rw [hQ]
  have hst : ∀ z ∈ lat k 0,
      (nab (lin (gA k)) - algebraMap k (Module.End k k⸨X⸩) x) z ∈ lat k 0 := by
    intro z hz
    obtain ⟨a, rfl⟩ := heckeAlgebra_mapsTo_localisationLatticeSpan.mp hz
    obtain ⟨b₁, hb₁⟩ := nab_coe (k := k) a
    rw [LinearMap.sub_apply, Module.algebraMap_end_apply, hb₁]
    exact Submodule.sub_mem _ (heckeAlgebra_mapsTo_localisationLatticeSpan.mpr ⟨b₁, rfl⟩) (Submodule.smul_of_tower_mem _ x hz)
  have hmono : Monotone fun m : ℕ => ((lat k 0).restrictScalars k).comap
      ((nab (lin (gA k)) - algebraMap k (Module.End k k⸨X⸩) x) ^ m) := by
    refine monotone_nat_of_le_succ fun m y hy => ?_
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at hy ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hst _ hy
  apply key0
  rw [eq_top_iff]
  rintro ⟨y, hy⟩ -
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
  obtain ⟨hy1, hy2⟩ := Submodule.mem_inf.mp hy
  obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hy2
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at hm
  obtain ⟨c, b, rfl⟩ := decomp hy1
  obtain ⟨b', hb'⟩ := steps (k := k) x m c b
  rw [hb'] at hm
  obtain ⟨a, ha⟩ := heckeAlgebra_mapsTo_localisationLatticeSpan.mp hm
  have h3 := congrArg (fun z : k⸨X⸩ => z.coeff (-1)) ha
  simp only [coeff_decomp] at h3
  have h4 : (1 - x) ^ m * c = 0 := by rw [← h3, PowerSeries.coeff_coe]; simp
  have hc : c = 0 := (mul_eq_zero.mp h4).resolve_left (pow_ne_zero m (sub_ne_zero.mpr (Ne.symm hx)))
  change c • (vv k)⁻¹ + (b : k⸨X⸩) ∈ lat k 0
  rw [hc, zero_smul, zero_add]
  exact heckeAlgebra_mapsTo_localisationLatticeSpan.mpr ⟨b, rfl⟩

end

def modModel (p : ℕ) [Fact p.Prime] (n : ℕ) : ModPG (ringModel p) n (ZMod p)⸨X⸩ :=
  unitMod _ (gE (ZMod p)).bijective n

theorem pull_lat (p : ℕ) [Fact p.Prime] (a : ℤ) :
    pull (lin (ringModel p).φ) (lat (ZMod p) a) = lat (ZMod p) (p * a) := by
  have hφ : ∀ y : (ZMod p)⸨X⸩, lin (ringModel p).φ y = y ^ p := fun y => by
    change FiniteField.frobeniusAlgHom (ZMod p) _ y = y ^ p
    rw [FiniteField.coe_frobeniusAlgHom, ZMod.card]
  have hpow : (vv (ZMod p) ^ a) ^ p = vv (ZMod p) ^ ((p : ℤ) * a) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  apply le_antisymm
  · unfold pull
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := mem_lat.mp hy
    rw [SetLike.mem_coe, hφ, mul_pow, hpow, ← map_pow]
    exact mem_lat.mpr ⟨b ^ p, rfl⟩
  · unfold lat pull
    rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨vv (ZMod p) ^ a, Submodule.mem_span_singleton_self _, ?_⟩
    rw [hφ, hpow]

theorem condAB (p : ℕ) [Fact p.Prime] (n : ℕ) (a : ℤ) :
    CondAB (modModel p n).φ (fun _ => (1 - p) * a) (fun _ => (p - 1) * a) (fun _ => lat (ZMod p) a) := by
  intro i
  dsimp only
  have h1 : pull ((modModel p n).φ i) (lat (ZMod p) a) = lat (ZMod p) (p * a) := pull_lat p a
  constructor
  · rw [h1, sh_lat]
    apply le_of_eq
    congr 1
    ring
  · rw [h1, sh_lat]
    apply le_of_eq
    congr 1
    ring

theorem condC_model (p : ℕ) [Fact p.Prime] (n : ℕ) (i : ZMod n) :
    CondC ((modModel p n).γ i) (lat (ZMod p) (-1)) := condC (k := ZMod p)

theorem sen_model (p : ℕ) [Fact p.Prime] (n : ℕ) (i : ZMod n) (x : ZMod p) :
    sen ((modModel p n).γ i) (lat (ZMod p) (-1)) x = if x = 1 then 1 else 0 := by
  split_ifs with h
  · subst h
    exact sen_one (k := ZMod p)
  · exact sen_ne (k := ZMod p) h

theorem sg_test : sg 5 (fun _ : ZMod 1 => 9) 0 = 2 := by
  unfold sg
  simp only [Nat.cast_ofNat]
  have h : (∑' j : ℕ, (9 : ℝ) / 5 ^ (j + 1)) = 9 / 4 := by
    have e : ∀ j : ℕ, (9 : ℝ) / 5 ^ (j + 1) = 9 / 5 * (5⁻¹ : ℝ) ^ j := fun j => by
      rw [pow_succ, mul_comm ((5 : ℝ) ^ j) 5, ← div_div, div_eq_mul_inv _ ((5 : ℝ) ^ j), ← inv_pow]
    simp_rw [e]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [h]
  exact (Nat.floor_eq_iff (by norm_num)).mpr ⟨by norm_num, by norm_num⟩

section
variable {k : Type} [Field k]

theorem gmult_top_bot {U : Type} [AddCommGroup U] [Module k U] (T : Module.End k U) (x : k) :
    gmult T ⊤ ⊥ x = Module.finrank k (T.maxGenEigenspace x) := by
  have hS : (⨆ m : ℕ, (⊥ : Submodule k U).comap ((T - algebraMap k (Module.End k U) x) ^ m))
      = T.maxGenEigenspace x := by
    apply le_antisymm
    · refine iSup_le fun m y hy => ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one] at hy
      exact (Module.End.mem_maxGenEigenspace T x y).mpr ⟨m, hy⟩
    · intro y hy
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace T x y).mp hy
      refine Submodule.mem_iSup_of_mem m ?_
      rw [Submodule.mem_comap, Submodule.mem_bot, Algebra.algebraMap_eq_smul_one]
      exact hm
  unfold gmult
  rw [top_inf_eq, hS]
  have hb : (⊥ : Submodule k U).submoduleOf (T.maxGenEigenspace x) = ⊥ := by
    ext y
    simp [Submodule.submoduleOf]
  rw [hb]
  exact (Submodule.quotEquivOfEqBot _ rfl).finrank_eq

theorem isEmpty_ringPG_zero : IsEmpty (RingPG k 0) := by
  refine ⟨fun R => ?_⟩
  obtain ⟨u, hu⟩ := R.φ_v
  rw [pow_zero, mul_one] at hu
  have hc0 : PowerSeries.constantCoeff (u : k⟦X⟧) ≠ 0 :=
    (PowerSeries.isUnit_iff_constantCoeff.mp u.isUnit).ne_zero
  have ha : IsUnit (PowerSeries.X - PowerSeries.C (PowerSeries.constantCoeff (u : k⟦X⟧)) : k⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simpa using hc0
  obtain ⟨w, hw⟩ := ha
  obtain ⟨b, hb⟩ := R.φ_int ((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)
  have h1 : R.φ ((PowerSeries.X - PowerSeries.C (PowerSeries.constantCoeff (u : k⟦X⟧)) : k⟦X⟧) : k⸨X⸩)
      = (((u : k⟦X⟧) - PowerSeries.C (PowerSeries.constantCoeff (u : k⟦X⟧)) : k⟦X⟧) : k⸨X⸩) := by
    simp only [map_sub, ← vv_eq, hu, HahnSeries.ofPowerSeries_C, ← algebraMap_eq, AlgHom.commutes]
  have h2 : R.φ ((PowerSeries.X - PowerSeries.C (PowerSeries.constantCoeff (u : k⟦X⟧)) : k⟦X⟧) : k⸨X⸩)
      * R.φ ((((w⁻¹ : (k⟦X⟧)ˣ) : k⟦X⟧)) : k⸨X⸩) = 1 := by
    rw [← map_mul, ← map_mul, ← hw, Units.mul_inv, map_one, map_one]
  rw [h1, hb, ← map_mul, ← map_one (HahnSeries.ofPowerSeries ℤ k)] at h2
  have h3 := congrArg PowerSeries.constantCoeff (HahnSeries.ofPowerSeries_injective h2)
  simp at h3

def twistMod {l : ℕ} (R : RingPG k l) (hγ : Function.Bijective R.γ) (n : ℕ) (c : ZMod n → kˣ) :
    ModPG R n k⸨X⸩ where
  φ i := (c i : k) • lin R.φ
  γ _ := lin R.γ
  φ_semi i a x := by
    change (c i : k) • R.φ (a * x) = R.φ a * ((c i : k) • R.φ x)
    rw [smul_eq, smul_eq, map_mul]; ring
  γ_semi _ a x := map_mul R.γ a x
  etale i := by
    rw [eq_top_iff]
    intro x _
    have h0 : algebraMap k k⸨X⸩ (c i) ≠ 0 := by simp
    have : x = (x * (algebraMap k k⸨X⸩ (c i))⁻¹) • (((c i : k) • lin R.φ) 1) := by
      change x = _ * ((c i : k) • R.φ 1)
      rw [smul_eq, map_one]; field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  γ_bij _ := hγ
  comm i x := by
    change (c i : k) • R.φ (R.γ x) = lin R.γ ((c i : k) • R.φ x)
    rw [map_smul, R.comm]; rfl

end

theorem condAB_var (p : ℕ) [Fact p.Prime] (n : ℕ) (a : ZMod n → ℤ) :
    CondAB (modModel p n).φ (fun i => a i - p * a (i - 1)) (fun i => p * a (i - 1) - a i)
      (fun i => lat (ZMod p) (a i)) := by
  intro i
  dsimp only
  have h1 : pull ((modModel p n).φ i) (lat (ZMod p) (a (i - 1))) = lat (ZMod p) (p * a (i - 1)) :=
    pull_lat p (a (i - 1))
  constructor
  · rw [h1, sh_lat]
    apply le_of_eq
    congr 1
    ring
  · rw [h1, sh_lat]
    apply le_of_eq
    congr 1
    ring

theorem sg_sharp : sg 5 (fun _ : ZMod 3 => 4) 0 = 1 := by
  unfold sg
  simp only [Nat.cast_ofNat]
  have h : (∑' j : ℕ, (4 : ℝ) / 5 ^ (j + 1)) = 1 := by
    have e : ∀ j : ℕ, (4 : ℝ) / 5 ^ (j + 1) = 4 / 5 * (5⁻¹ : ℝ) ^ j := fun j => by
      rw [pow_succ, mul_comm ((5 : ℝ) ^ j) 5, ← div_div, div_eq_mul_inv _ ((5 : ℝ) ^ j), ← inv_pow]
    simp_rw [e]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  rw [h]
  simp

end GlobalTheory.PhiGam.Model
