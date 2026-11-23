import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKurOfActStFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst.Test

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)

def cycRep (K LL : FinExt l) : Representation ↥LL.1 ↥(GK K) ↥LL.1 where
  toFun g := algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) • LinearMap.id
  map_one' := by ext; simp
  map_mul' g h := by
    rw [smul_mul_smul_comm, ← map_mul, ← Units.val_mul, ← map_mul]; rfl

theorem cycRep_apply (K LL : FinExt l) (g : ↥(GK K)) (v : ↥LL.1) :
    cycRep P K LL g v = (P.χQ (g : GQ l) : ℚ_[l]) • v := by
  show algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) • v = _
  rw [algebraMap_smul]

theorem stRep_per (K LL : FinExt l) (g : ↥(GK K)) :
    stRep P (cycRep P K LL) g ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] (C (tInv P) : Bst P)) = (1 : ↥LL.1) ⊗ₜ C (tInv P) := by
  rw [stRep_tmul, cycRep_apply, smul_tmul, actSt_C, smul_C, smul_actQ_tInv]

def per (K LL : FinExt l) : ↥(Dpst P (cycRep P K LL)) :=
  ⟨(1 : ↥LL.1) ⊗ₜ C (tInv P), (mem_Dpst P _).mpr ⟨K, fun g _ => stRep_per P K LL g⟩⟩

theorem per_ne_zero (K LL : FinExt l) : per P K LL ≠ 0 := by
  intro h0
  have := nontrivial_B P
  have h1 : ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] (C (tInv P) : Bst P)) = 0 := congrArg Subtype.val h0
  have h2 : Function.Injective (Algebra.TensorProduct.includeRight : Bst P →ₐ[ℚ_[l]] ↥LL.1 ⊗[ℚ_[l]] Bst P) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ_[l] ↥LL.1).injective
  have h3 : (C (tInv P) : Bst P) = 0 := h2 (by rw [map_zero]; exact h1)
  have h4 := tInv_mul P
  rw [C_eq_zero.mp h3, zero_mul] at h4
  exact zero_ne_one h4

theorem phiD_per (K LL : FinExt l) : phiD P _ (per P K LL) = (l : ↥LL.1)⁻¹ • per P K LL := by
  have : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  have hl : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  rw [eq_inv_smul_iff₀ hl]
  apply Subtype.ext
  show (l : ↥LL.1) • phiV P _ _ ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] (C (tInv P) : Bst P)) = (1 : ↥LL.1) ⊗ₜ C (tInv P)
  rw [phiV_tmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul ℚ_[l], ← tmul_smul, phiSt_C, smul_C,
    smul_phiB_tInv]

theorem phiD_pow_per (K LL : FinExt l) (n : ℕ) :
    (phiD P _ ^ n) (per P K LL) = ((l : ↥LL.1)⁻¹ ^ n) • per P K LL := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', End.mul_apply, ih, map_smul, phiD_per, smul_smul, pow_succ]

theorem wdMk_per_ne_zero (K LL : FinExt l) : wdMk P ι _ (per P K LL) ≠ 0 := fun h0 =>
  per_ne_zero P K LL (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι K LL _ _ _ fun n => by rw [phiD_pow_per, wdMk_smul, h0, smul_zero])

theorem isPst_cycRep
    (h : ∀ (K : FinExt l) (b : P.R.B), ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB)
    (K : FinExt l) : IsPst P (cycRep P K (botExt l)) := by
  have hr : Module.rank ℚ_[l] ↥(botExt l).1 = 1 := IntermediateField.rank_bot
  rw [IsPst, hr, rank_eq_one_iff]
  refine ⟨toUr P _ (per P K _), fun h0 => per_ne_zero P K _ h0, fun x => ?_⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := (toUr P _).surjective x
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : Bst P →ₐ[ℚ_[l]] ↥(botExt l).1 ⊗[ℚ_[l]] Bst P) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ_[l] ↥(botExt l).1).injective
  obtain ⟨p, rfl⟩ : ∃ p : Bst P, x = (1 : ↥(botExt l).1) ⊗ₜ[ℚ_[l]] p := by
    clear hx
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul v b =>
      obtain ⟨c, rfl⟩ := (IntermediateField.botEquiv ℚ_[l] (Om l)).symm.surjective v
      refine ⟨c • b, ?_⟩
      rw [← smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      rfl
    | add x y hx hy =>
      obtain ⟨p, rfl⟩ := hx; obtain ⟨q, rfl⟩ := hy
      exact ⟨p + q, by rw [tmul_add]⟩
  obtain ⟨K', hK'⟩ := (mem_Dpst P _).mp hx
  obtain ⟨c, hc⟩ := exists_kur_of_actSt_fixed P (supExt K K') (h _) (p * C P.tB) fun g hg => by
    have h1 := hK' ⟨g, GK_le (K' := supExt K K') le_sup_left hg⟩
      (GK_le (K' := supExt K K') le_sup_right hg)
    rw [stRep_tmul, cycRep_apply, smul_tmul] at h1
    have h2 : (P.χQ g : ℚ_[l]) • actSt P g p = p := hinj h1
    rw [map_mul, actSt_C, localPrime_galoisAction_periodT, ← smul_C, mul_smul_comm, ← smul_mul_assoc, h2]
  refine ⟨c, ?_⟩
  rw [smul_toUr]
  congr 1
  apply Subtype.ext
  show mulV P _ _ c ((1 : ↥(botExt l).1) ⊗ₜ[ℚ_[l]] (C (tInv P) : Bst P)) = (1 : ↥(botExt l).1) ⊗ₜ p
  rw [mulV_tmul, hc, mul_assoc, ← map_mul, mul_comm P.tB, tInv_mul, map_one, mul_one]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) (LL : FinExt l)

section Generic

variable {LL} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (x : ↥(Dpst P ρ))

theorem weilD_of_phiD [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (hj : Induces Bw)
    (hx : ∀ g, actD P ρ g x = x) (hφ : ∀ n : ℕ, (phiD P ρ ^ n) x = ((l : ↥LL.1)⁻¹ ^ n) • x)
    (σ : ↥(Weil h)) (hσ : deg σ = 1) :
    weilD Bw h P ρ σ x = ((normV w : ℕ) : ↥LL.1) • x := by
  have : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  have hl : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have h3 : x = ((phiU P ρ ^ resDeg l w : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ))
      (((normV w : ℕ) : ↥LL.1) • x) := by
    rw [Units.val_pow_eq_pow_val, coe_phiU, map_smul, hφ, smul_smul, normV_eq_pow (hj.mem_placesOver h),
      Nat.cast_pow, ← mul_pow, mul_inv_cancel₀ hl, one_pow, one_smul]
  have h4 := congrArg (((phiU P ρ ^ resDeg l w)⁻¹ : (End ↥LL.1 ↥(Dpst P ρ))ˣ) : End ↥LL.1 ↥(Dpst P ρ)) h3
  rw [← End.mul_apply, Units.inv_mul, End.one_apply] at h4
  rw [weilD_apply, alpha, hσ, mul_one, zpow_neg, zpow_natCast, End.mul_apply, h4, map_smul, hx]

theorem apply_eq_of_nilpotent {W : Type} [AddCommGroup W] [Module ℂ W] (hd : finrank ℂ W = 1) {v : W}
    (hv : v ≠ 0) (u : End ℂ W) (hu : IsNilpotent (u - 1)) : u v = v := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hd ((u - 1) v)
  have hp : ∀ n : ℕ, ((u - 1) ^ n) v = c ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have hc0 : c = 0 := by
    have := hp k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    exact pow_eq_zero_iff'.mp (this.resolve_right hv) |>.1
  rw [hc0, zero_smul, LinearMap.sub_apply, eq_comm, sub_eq_zero] at hc
  exact hc

theorem frobEig_wdPst_of_phiD [FiniteDimensional ↥LL.1 V] (h1 : finrank ↥LL.1 V = 1) (hV : IsPst P ρ)
    (hx : ∀ g, actD P ρ g x = x) (hφ : ∀ n : ℕ, (phiD P ρ ^ n) x = ((l : ↥LL.1)⁻¹ ^ n) • x)
    (hv : wdMk P ι ρ x ≠ 0) : (wdPst P ι Bw h hj ρ).frobEig = {((normV w : ℕ) : ℂ)} := by
  have := hV.finite
  have hd : finrank ℂ (WDSpace P ι ρ) = 1 := by
    rw [LetterDim.finrank_wdSpace l P ι _ LL _ _ hV, h1]
  have hcard := WD.card_eig (wdPst P ι Bw h hj ρ) (frob h)
  rw [lpDim_wdPst ι Bw h hj hV, hd] at hcard
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
  obtain ⟨u, -, hk, -, -, hu⟩ := wdRep_spec P ι Bw h hj ρ
  have huv := apply_eq_of_nilpotent hd hv _ hk
  have he : (wdRep P ι Bw h hj ρ).ρ (frob h) (wdMk P ι ρ x) = ((normV w : ℕ) : ℂ) • wdMk P ι ρ x := by
    have h1 := LinearMap.congr_fun (hu (frob h)) (wdMk P ι ρ x)
    rw [deg_frob, zpow_one, End.mul_apply, huv] at h1
    rw [← h1, wdRho_mk, weilD_of_phiD P Bw h ρ x hj hx hφ _ deg_frob, wdMk_smul]
    have e : ι ((((normV w : ℕ) : ↥LL.1)) : Om l) = ((normV w : ℕ) : ℂ) :=
      map_natCast (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) _
    rw [e]
  have hm : ((normV w : ℕ) : ℂ) ∈ (wdPst P ι Bw h hj ρ).eig (frob h) := by
    rw [wdPst_of_isPst ι Bw h hj hV, WD.eig_mk, mem_roots (LinearMap.charpoly_monic _).ne_zero,
      ← End.hasEigenvalue_iff_isRoot_charpoly]
    exact End.hasEigenvalue_of_hasEigenvector ⟨End.mem_eigenspace_iff.mpr he, hv⟩
  rw [ha, Multiset.mem_singleton] at hm
  rw [WD.frobEig, ha, hm]

end Generic

theorem frobEig_wdPst_cycRep (hV : IsPst P (cycRep P Bw.Kw LL)) :
    (wdPst P ι Bw h hj (cycRep P Bw.Kw LL)).frobEig = {((normV w : ℕ) : ℂ)} :=
  frobEig_wdPst_of_phiD P ι Bw h hj _ (per P Bw.Kw LL) (finrank_self _) hV
    (fun g => Subtype.ext (stRep_per P _ LL g)) (phiD_pow_per P _ LL) (wdMk_per_ne_zero P ι _ LL)

theorem wdPst_cycRep_ne_trivWD (hV : IsPst P (cycRep P Bw.Kw LL)) :
    wdPst P ι Bw h hj (cycRep P Bw.Kw LL) ≠ trivWD h 1 := by
  intro he
  have h1 := frobEig_wdPst_cycRep P ι Bw h hj LL hV
  rw [he, trivWD, WD.frobEig_diag] at h1
  have h2 : (1 : ℂ) = ((normV w : ℕ) : ℂ) := by simpa using h1
  exact (one_lt_normV w).ne (by exact_mod_cast h2)

theorem lpDim_wdAt {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) :
    (wdAt P ι Bw h hj r).lpDim = a := by
  by_cases hr : IsPstAt P Bw r
  · obtain ⟨LL', r', -, h2, h3⟩ := wdAt_of_isPstAt ι Bw h hj hr
    rw [h3, lpDim_wdPst ι Bw h hj h2, LetterDim.finrank_wdSpace l P ι _ LL' _ _ h2]
    simp
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, lpDim_trivWD]

omit P ι in

theorem exists_induces (hw : w ∈ placesOver E l) (h : IsPlaceOver A w) :
    ∃ (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), Induces Bw := by
  obtain ⟨j, L0, hj, hL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l E Ω w A hw h
  obtain ⟨Bw, hB, -⟩ := hL L0 le_rfl
  exact ⟨L0, Bw, fun x => by rw [hB]; exact hj x⟩

omit P ι in

example : Nonempty (LocPrime l) := ⟨(GlobalTheory.MemLoc.exists_locPrime_tied l).choose⟩

end GlobalTheory.Pst.Test
