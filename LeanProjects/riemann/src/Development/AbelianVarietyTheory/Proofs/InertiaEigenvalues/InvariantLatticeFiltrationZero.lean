import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

section
open scoped Formalism.Per

namespace Bridge.FilZeroMul

theorem mul_mem_div_self {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (N : Submodule R A) {x y : A} (hx : x ∈ N / N) (hy : y ∈ N / N) : x * y ∈ N / N := by
  rw [Submodule.mem_div_iff_forall_mul_mem] at hx hy ⊢
  intro z hz
  rw [mul_assoc]
  exact hx _ (hy z hz)

theorem mul_mem_filD_zero (l : ℕ) [Fact l.Prime] {x y : Formalism.Per.BdR l}
    (hx : x ∈ Formalism.Per.FilD l 0) (hy : y ∈ Formalism.Per.FilD l 0) : x * y ∈ Formalism.Per.FilD l 0 :=
  mul_mem_div_self (Reformulated.AutPerF.BdR.filNat l (Formalism.Per.OC l) 0) hx hy

end Bridge.FilZeroMul

theorem Bridge.mul_mem_filtration_zero : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {O : Type} [inst_1 : CommRing O] [inst_2 : Algebra ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) {x y : GlobalTheory.BKReal.OB l O}, x ∈ GlobalTheory.BKGal.XiFil.filO O C 0 → y ∈ GlobalTheory.BKGal.XiFil.filO O C 0 → x * y ∈ GlobalTheory.BKGal.XiFil.filO O C 0 := by
  intro l _ O _ _ C x y hx hy
  unfold GlobalTheory.BKGal.XiFil.filO at hx hy ⊢
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨a * b, ?_, ?_⟩
  · rw [map_mul]
    exact Bridge.FilZeroMul.mul_mem_filD_zero l ha hb
  · simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiFil.ImageFil

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem mul_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) {x y : OB l O} (hx : x ∈ filO O C 0)
    (hy : y ∈ filO O C 0) : x * y ∈ filO O C 0 := by
  first | exact Bridge.mul_mem_filtration_zero | exact Bridge.mul_mem_filtration_zero .. | (intros; apply Bridge.mul_mem_filtration_zero <;> assumption)

theorem toOB_mem_filO (C : GlobalTheory.MemLoc.Core l) (x : OCr l O) : toOB l O x ∈ filO O C 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul o w =>
    have h : toOB l O (o ⊗ₜ w) = o • ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l w) := by
      rw [smul_tmul', smul_eq_mul, mul_one]; rfl
    rw [h]
    refine Submodule.smul_mem _ o (Submodule.subset_span ⟨acrisToBcris l w, ?_, rfl⟩)
    rw [mem_FilD_zero_iff]
    exact ⟨C.j w, C.ι_j w⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem pow_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) {x : OB l O} (hx : x ∈ filO O C 0) (n : ℕ) :
    x ^ n ∈ filO O C 0 := by
  induction n with
  | zero =>
    rw [pow_zero, ← map_one (toOB l O)]
    exact toOB_mem_filO C 1
  | succ n ih => rw [pow_succ]; exact mul_mem_filO_zero C ih hx

theorem isUnit_l_BdRp : IsUnit ((l : ℕ) : Per.BdRp l) := by
  simpa using (GlobalTheory.RingBasics.isUnit_l (l := l)).map (algebraMap (Per.AinfP l) (Per.BdRp l))

theorem exists_inv_l_mem (C : GlobalTheory.MemLoc.Core l) : ∃ r ∈ filO O C 0, r * (l : OB l O) = 1 := by
  obtain ⟨β, hβ⟩ := (GlobalTheory.MemLoc.isUnit_l_Bcris l).exists_left_inv
  obtain ⟨z, hz⟩ := (isUnit_l_BdRp (l := l)).exists_left_inv
  refine ⟨(1 : O) ⊗ₜ β, Submodule.subset_span ⟨β, ?_, rfl⟩, ?_⟩
  · rw [mem_FilD_zero_iff]
    refine ⟨z, ?_⟩
    have h1 : C.ι β * ((l : ℕ) : Per.BdR l) = 1 := by rw [← map_natCast C.ι, ← map_mul, hβ, map_one]
    have h2 : algebraMap (Per.BdRp l) (Per.BdR l) z * ((l : ℕ) : Per.BdR l) = 1 := by
      rw [← map_natCast (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_mul, hz, map_one]
    calc C.ι β = C.ι β * (((l : ℕ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) z) := by
          rw [mul_comm ((l : ℕ) : Per.BdR l), h2, mul_one]
      _ = algebraMap (Per.BdRp l) (Per.BdR l) z := by rw [← mul_assoc, h1, one_mul]
  · rw [show (l : OB l O) = (1 : O) ⊗ₜ[ℤ_[l]] ((l : ℕ) : Per.Bcris l) from
      (map_natCast (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O) l).symm,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, hβ]
    rfl

variable {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem iSl_mem_filO (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (p : invL l (S O K e)) :
    ϖ.iSl O K p ∈ filO O C 0 := by
  obtain ⟨f, n, hf⟩ := p
  have h1 : (l : invL l (S O K e)) ^ n * ⟨f, n, hf⟩ = ⟨_, le_away _ _ hf⟩ := Subtype.ext (by simp)
  have h2 := congrArg (ϖ.iSl O K) h1
  rw [map_mul, map_pow, map_natCast, ϖ.iSl_of_mem O K hf] at h2
  obtain ⟨r, hr, hrl⟩ := exists_inv_l_mem (O := O) C
  have h3 : ϖ.iSl O K ⟨f, n, hf⟩ = r ^ n * toOB l O (ϖ.iS O K ⟨_, hf⟩) := by
    rw [← h2, ← mul_assoc, ← mul_pow, hrl, one_pow, one_mul]
  rw [h3]
  exact mul_mem_filO_zero C (pow_mem_filO_zero C hr n) (toOB_mem_filO C _)

end GlobalTheory.BKGal.XiFil.ImageFil

namespace GlobalTheory.BKGal.XiFil

open GlobalTheory.BKGal.XiFil.ImageFil in

theorem iB_mem_filO_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (C : GlobalTheory.MemLoc.Core l) (f : ZMod a → invL l (S O K e)), ϖ.iB t K f ∈ filO O C 0 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ C f
  rw [PiSys.iB, glue_apply]
  refine Submodule.sum_mem _ fun τ _ => mul_mem_filO_zero C ?_ (iSl_mem_filO K ϖ C (f τ))
  rw [idem, constB, AlgHom.comp_apply]
  exact toOB_mem_filO C _

end GlobalTheory.BKGal.XiFil
