import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.FinrankAdjoinRootsEqRootDeg
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalAbelian
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.SumArith
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Generate
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EqOneOfMemPrincOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.CostCond
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthFrac

namespace KStar.TotallyRealRoots

open IsDiscreteValuationRing

variable (l : ℕ) [Fact l.Prime] (O : Type*) [CommRing O] [Algebra ℤ_[l] O]

def twistInvOver (A : Type*) [AddCommGroup A] [Module O A] (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) :
    Submodule O A where
  carrier := {x | ∀ u ∈ U, (algebraMap ℤ_[l] O (u : ℤ_[l]) ^ tr) • x = x}
  zero_mem' := fun u _ => smul_zero _
  add_mem' := fun {x y} hx hy u hu => by rw [smul_add, hx u hu, hy u hu]
  smul_mem' := fun c x hx u hu => by rw [smul_comm, hx u hu]

variable {l O}

theorem mem_twistInvOver {A : Type*} [AddCommGroup A] [Module O A] {U : Subgroup ℤ_[l]ˣ} {tr : ℕ}
    {x : A} : x ∈ twistInvOver l O A U tr ↔
      ∀ u ∈ U, (algebraMap ℤ_[l] O (u : ℤ_[l]) ^ tr) • x = x := Iff.rfl

private theorem torsionBy_pow_le_twistInvOver (A : Type*) [AddCommGroup A] [Module O A] {U : Subgroup ℤ_[l]ˣ}
    {tr n : ℕ} (h : (n : ℕ∞) ≤ nu l U tr) :
    Submodule.torsionBy O A ((l : O) ^ n) ≤ twistInvOver l O A U tr := by
  intro x hx
  rw [Submodule.mem_torsionBy_iff] at hx
  rw [mem_twistInvOver]
  intro u hu
  obtain ⟨c, hc⟩ := le_nu_iff.mp h u hu
  have e : (algebraMap ℤ_[l] O (u : ℤ_[l])) ^ tr - 1 = (l : O) ^ n * algebraMap ℤ_[l] O c := by
    rw [← map_pow, ← map_one (algebraMap ℤ_[l] O), ← map_sub, hc, map_mul, map_pow, map_natCast]
  have e2 : ((algebraMap ℤ_[l] O (u : ℤ_[l])) ^ tr) • x =
      x + ((algebraMap ℤ_[l] O (u : ℤ_[l])) ^ tr - 1) • x := by
    rw [sub_smul, one_smul]
    abel
  rw [e2, e, mul_comm, mul_smul, hx, smul_zero, add_zero]

theorem twistInvOver_eq_torsionBy (A : Type*) [AddCommGroup A] [Module O A] {U : Subgroup ℤ_[l]ˣ}
    {tr n : ℕ} (h : nu l U tr = n) :
    twistInvOver l O A U tr = Submodule.torsionBy O A ((l : O) ^ n) := by
  apply le_antisymm
  · intro x hx
    rw [mem_twistInvOver] at hx
    rw [Submodule.mem_torsionBy_iff]
    have hstar : nuStar (l : ℤ_[l]) ((fun u : ℤ_[l]ˣ => (u : ℤ_[l])) '' (U : Set ℤ_[l]ˣ)) tr = (n : ℕ∞) := h
    obtain ⟨w, ⟨v, hv, rfl⟩, hdvd, hndvd⟩ := exists_exact_of_nuStar_eq hstar
    obtain ⟨c, hc⟩ := hdvd
    have hcu : IsUnit c := by
      by_contra hnu
      rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at hnu
      obtain ⟨d, hd⟩ := hnu
      apply hndvd
      refine ⟨d, ?_⟩
      rw [hc, hd, pow_succ]
      ring
    have e : (algebraMap ℤ_[l] O (v : ℤ_[l])) ^ tr - 1 = (l : O) ^ n * algebraMap ℤ_[l] O c := by
      rw [← map_pow, ← map_one (algebraMap ℤ_[l] O), ← map_sub, hc, map_mul, map_pow, map_natCast]
    have h1 : ((algebraMap ℤ_[l] O (v : ℤ_[l])) ^ tr - 1) • x = 0 := by
      rw [sub_smul, one_smul, hx v hv, sub_self]
    rw [e, mul_comm, mul_smul] at h1
    exact ((hcu.map (algebraMap ℤ_[l] O)).smul_eq_zero).mp h1
  · exact torsionBy_pow_le_twistInvOver A (by rw [h])

variable [IsDomain O] [IsDiscreteValuationRing O]
  (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]

omit [Algebra ℤ_[l] O] in

theorem length_torsionBy_fracMod (b : O) :
    Module.length O (Submodule.torsionBy O (Selmer.FracMod O K) b) = addVal O b := by
  classical
  let Φ : Matrix (Fin 1) (Fin 1) O := Matrix.of (fun _ _ => b)
  have hdet : Φ.det = b := by simp [Φ, Matrix.det_unique]
  conv_rhs => rw [← hdet]
  rw [← Selmer.length_kernel_fraction_module_eq_addVal_det (K := K) Φ]
  let e : (Fin 1 → Selmer.FracMod O K) ≃ₗ[O] Selmer.FracMod O K := LinearEquiv.funUnique (Fin 1) O _
  have hmap : (Selmer.H1c Φ (Selmer.FracMod O K)).map (e : (Fin 1 → Selmer.FracMod O K) →ₗ[O] Selmer.FracMod O K) =
      Submodule.torsionBy O (Selmer.FracMod O K) b := by
    ext x
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_torsionBy_iff]
    simp only [Selmer.H1c, LinearMap.mem_ker]
    constructor
    · intro hx
      have h0 := congrFun hx 0
      rw [Selmer.coefMap_apply] at h0
      simpa [Φ, e] using h0
    · intro hx
      funext i
      rw [Selmer.coefMap_apply]
      simpa [Φ, e] using hx
  rw [← hmap]
  exact ((e.submoduleMap _).length_eq).symm

theorem length_twistInvOver_of_eq {U : Subgroup ℤ_[l]ˣ} {tr n : ℕ} (h : nu l U tr = n) :
    Module.length O (twistInvOver l O (Selmer.FracMod O K) U tr) = n * addVal O (l : O) := by
  rw [twistInvOver_eq_torsionBy _ h, length_torsionBy_fracMod K, addVal_pow, nsmul_eq_mul]

theorem length_twistInvOver (hl : ¬ IsUnit (l : O)) (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) :
    Module.length O (twistInvOver l O (Selmer.FracMod O K) U tr) =
      nu l U tr * addVal O (l : O) := by
  by_cases htop : nu l U tr = ⊤
  · have hv : addVal O (l : O) ≠ 0 := by
      rw [Ne, addVal_eq_zero_iff]
      exact hl
    rw [htop, ENat.top_mul hv, ENat.eq_top_iff_forall_ge]
    intro m
    have hle : Submodule.torsionBy O (Selmer.FracMod O K) ((l : O) ^ m) ≤
        twistInvOver l O (Selmer.FracMod O K) U tr :=
      torsionBy_pow_le_twistInvOver _ (by rw [htop]; exact le_top)
    calc (m : ℕ∞) ≤ (m : ℕ∞) * addVal O (l : O) :=
          le_mul_of_one_le_right (by positivity) (ENat.one_le_iff_ne_zero.mpr hv)
      _ = Module.length O (Submodule.torsionBy O (Selmer.FracMod O K) ((l : O) ^ m)) := by
          rw [length_torsionBy_fracMod K, addVal_pow, nsmul_eq_mul]
      _ ≤ _ := Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [length_twistInvOver_of_eq K hn.symm, ← hn]

end KStar.TotallyRealRoots
