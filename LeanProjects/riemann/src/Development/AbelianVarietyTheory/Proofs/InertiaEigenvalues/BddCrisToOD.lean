import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.CrisBounded

theorem dvd_of_ev_eq_zero {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l))
    (m : ℕ) (y : Per.BdRp l) (hy : Per.ev l m y = 0) : ainfToBdRp l d ^ m ∣ y := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have h2 := hd.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  have h3 : d ∣ GlobalTheory.MemLoc.xi e := Ideal.mem_span_singleton.1 (h2 ▸ Ideal.mem_span_singleton_self _)
  have h4 := ((GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE).1 m y).1 ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m y).2 hy)
  exact (pow_dvd_pow_of_dvd (map_dvd (GlobalTheory.MemLoc.aDp l) h3) m).trans h4

theorem bdd_crisP {l : ℕ} [Fact l.Prime] {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ) :
    ∃ N : ℕ, ∀ x : Per.Acris l, ∃ a : Ainf l,
      ainfToBdRp l d ^ m ∣ (l : Per.BdRp l) ^ N * acrisToBdRp l x - ainfToBdRp l a := by
  obtain ⟨N, hN⟩ := (isCrisP_crisP l).bdd m
  refine ⟨N, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hN x
  refine ⟨a, dvd_of_ev_eq_zero hd m _ ?_⟩
  rw [map_sub, sub_eq_zero]
  exact ha.trans (GlobalTheory.MemLoc.CrisUnique.ev_aDp m a).symm

theorem bdd_tensor {Z O A C D : Type} [CommRing Z] [CommRing O] [Algebra Z O] [Module.Free Z O]
    [Module.Finite Z O] [CommRing A] [Algebra Z A] [CommRing C] [Algebra Z C] [CommRing D] [Algebra Z D]
    (f : A →ₐ[Z] D) (j : C →ₐ[Z] D) (t : D) (n : ℕ) (h : ∀ x : C, ∃ a : A, t ∣ (n : D) * j x - f a)
    (z : O ⊗[Z] C) : ∃ y : O ⊗[Z] A, ((1 : O) ⊗ₜ[Z] t) ∣
      (n : O ⊗[Z] D) * Algebra.TensorProduct.map (AlgHom.id O O) j z -
        Algebra.TensorProduct.map (AlgHom.id O O) f y := by
  let b := Module.Free.chooseBasis Z O
  choose a c hc using fun i => h (GlobalTheory.Decompl.crd b i z)
  refine ⟨∑ i, b i ⊗ₜ[Z] a i, ∑ i, b i ⊗ₜ[Z] c i, GlobalTheory.Decompl.ext_crd b fun i => ?_⟩
  rw [map_sub, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_map, GlobalTheory.Decompl.crd_mul,
    GlobalTheory.Decompl.crd_sum, GlobalTheory.Decompl.crd_sum, hc]

theorem bdd_crisToOD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ), ∃ N : ℕ, ∀ z : OCr l O, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ N * crisToOD l O z - toOD l O y := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m
  rw [show ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) from
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))]
  obtain ⟨N, hN⟩ := bdd_crisP (ϖ.span_ev_eis 1) m
  refine ⟨N, fun z => ?_⟩
  obtain ⟨y, hy⟩ := bdd_tensor (ainfToBdRp l) (acrisToBdRp l) _ (l ^ N)
    (fun x => by rw [Nat.cast_pow]; exact hN x) z
  refine ⟨y, ?_⟩
  rw [Algebra.TensorProduct.tmul_pow, one_pow, ← Nat.cast_pow]
  exact hy

end GlobalTheory.BKReal.CrisBounded
