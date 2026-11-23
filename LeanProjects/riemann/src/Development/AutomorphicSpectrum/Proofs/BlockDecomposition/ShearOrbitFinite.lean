import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearOrbit

variable {k : Type} [Field k]

theorem shear_mul_inv (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (1 + vecMulVec (eLast k n) b) * (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b) = 1 := by
  have hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n) := by
    simp [GlobalTheory.BZMir.eLast, dotProduct_single]
  have hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b =
      b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    rw [vecMulVec_mul_vecMulVec, hd]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1 := by
    rw [← mul_one_add]
    exact inv_mul_cancel₀ hb
  rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc,
    one_smul, add_sub_cancel_right]

theorem shearGL_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
  have h := GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_mul_inv n b hb
  have hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) :=
    ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩
  rw [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hu]
  exact hu.unit_spec

theorem shearGL_inv_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (((shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b :=
  Units.inv_eq_of_mul_eq_one_right (by rw [shearGL_val n b hb]; exact shear_mul_inv n b hb)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_add_ne_zero_of_mem_box (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) {b : Fin (n + 1) → k}
    (hb : b ∈ box (n + 1) r) : 1 + b (Fin.last n) ≠ 0 := by
  intro h
  have h1 : valuation k (b (Fin.last n)) ≤ valuation k (r : k) := hb (Fin.last n)
  have h2 : b (Fin.last n) = -1 := by linear_combination h
  rw [h2, Valuation.map_neg, map_one] at h1
  exact absurd hr (not_lt.mpr h1)

theorem continuous_shearGL (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) :
    Continuous fun b : (box (n + 1) r : Set (Fin (n + 1) → k)) => shearGL n b.1 := by
  have hne : ∀ b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)), 1 + b.1 (Fin.last n) ≠ 0 :=
    fun b => GlobalTheory.CompanionTheory.MirPair.ShearOrbit.one_add_ne_zero_of_mem_box n hr b.2
  have hv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      vecMulVec (GlobalTheory.BZMir.eLast k n) b.1 :=
    continuous_matrix fun i j => by
      simp only [vecMulVec_apply]
      exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_const.add hv).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_val n b.1 (hne b)).symm
  · have hinv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
        (1 + b.1 (Fin.last n))⁻¹ :=
      (continuous_const.add ((continuous_apply _).comp continuous_subtype_val)).inv₀ hne
    exact (continuous_const.sub (hinv.smul hv)).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_inv_val n b.1 (hne b)).symm

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem continuous_levi (m : ℕ) : Continuous (levi k m) := by
  have hmat : Continuous (GlobalTheory.BZMir.glEmbHom k m) := by
    apply continuous_matrix
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [GlobalTheory.BZMir.glEmbHom, GlobalTheory.BZMir.glEmbMat] <;>
      first
        | exact continuous_const
        | exact continuous_id.matrix_elem _ _
        | fun_prop
  have hGL : Continuous (GlobalTheory.BZMir.glEmb k m) := Continuous.units_map _ hmat
  exact continuous_induced_rng.2 hGL

theorem isOpen_orbit_fiber {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v w : V) :
    IsOpen {p : Mir k (n + 1) | T p v = w} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hS : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v} := hT v
  have hcont : Continuous fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g) ⁻¹' {g | T g v = v} ∈ 𝓝 p := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hS.mem_nhds
    simp
  filter_upwards [hmem] with g hg
  have hg' : T (p⁻¹ * g) v = v := hg
  have hsplit : T g = T p * T (p⁻¹ * g) := by
    rw [← map_mul, mul_inv_cancel_left]
  show T g v = w
  rw [hsplit, Module.End.mul_apply, hg']
  exact hp

theorem shear_orbit_finite {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v : V) (r : kˣ)
    (hr : valuation k (r : k) < 1) :
    ((fun b => T (levi k (n + 1) (shearGL n b)) v) '' (box (n + 1) r : Set (Fin (n + 1) → k))).Finite := by
  haveI : CompactSpace (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) r)
  have hc : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1) :=
    (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_levi (n + 1)).comp (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_shearGL n hr)
  have hlc : IsLocallyConstant fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      T (GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1)) v := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro w
    exact (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.isOpen_orbit_fiber T hT v w).preimage hc
  rw [Set.image_eq_range]
  exact hlc.range_finite

end GlobalTheory.CompanionTheory.MirPair.ShearOrbit

end
