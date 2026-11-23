import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFactsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BdRLatticeGens

variable {l : ℕ} [Fact l.Prime]

theorem iota_sigma {K : FinExt l} {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (g : ↥(GK K)) (b : Per.Bcris l) :
    C.ι (Per.σB (g : GQ l) b) = Per.σD (g : GQ l) (C.ι b) := by
  obtain ⟨b0, rfl⟩ := T.eB.surjective b
  have h1 := (P.PD K).ι_comm g b0
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h1
  rw [← T.actB, ← hF.ι, ← hF.ι, h1, T.actD]

theorem iota_zB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (a : ℤ_[l]) : C.ι (Per.zB l a) = Per.zD l a := by
  rw [← T.zB, ← hF.ι, AlgHom.commutes, T.zD]

theorem sigma_U' {d : ℕ} {K : FinExt l} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hU : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) (g : ↥(GK K)) :
    U'.map (Per.σB (g : GQ l)) = U' * (ρ g).map (Per.zB l) := by
  have h1 : U.map (Per.σB (g : GQ l)) * U'.map (Per.σB (g : GQ l)) = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (ρ g).map (Per.zB l) = U * U'.map (Per.σB (g : GQ l)) := by
    conv_rhs => rw [← hU g]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h3 : U' * U = 1 := mul_eq_one_comm.1 hUU
  rw [h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem inv_vec {K : FinExt l} {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hU : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U)
    (v : Fin d → Per.BdR l)
    (hv : ∀ g : ↥(GK K), ((ρ g).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v r)) = v)
    (g : ↥(GK K)) (r : Fin d) :
    Per.σD (g : GQ l) ((U'.map C.ι).mulVec v r) = (U'.map C.ι).mulVec v r := by
  rw [RingHom.map_mulVec]
  have e1 : (U'.map C.ι).map (Per.σD (g : GQ l)) = U'.map C.ι * (ρ g).map (Per.zD l) := by
    have : (U'.map C.ι).map (Per.σD (g : GQ l)) = (U'.map (Per.σB (g : GQ l))).map C.ι := by
      ext a b; simp [iota_sigma hF g]
    rw [this, sigma_U' ρ U U' hUU hU g, Matrix.map_mul]
    congr 1
    ext a b; simp [iota_zB hF]
  rw [e1, ← Matrix.mulVec_mulVec]
  exact congrFun (congrArg _ (hv g)) r

theorem isUnit_aDp_zA {y : ℤ_[l]} (hy : y ≠ 0) : IsUnit (aDp l (Per.zA l y)) := by
  rw [PadicInt.unitCoeff_spec hy, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  exact ((PadicInt.unitCoeff hy).isUnit.map _).map _ |>.mul ((isUnit_l_BdRp l).pow _)

theorem oD_int (C : Core l) (y : ℤ_[l]) (x : Om l) :
    C.oD (algebraMap ℚ_[l] (Om l) (y : ℚ_[l]) * x) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * C.oD x := by
  rw [map_mul]
  congr 1
  simp only [Core.oD, RingHom.comp_apply, C.o_sec.z]

theorem descend {K : FinExt l} (C : Core l) (hI : C.InvdR) {d : ℕ} (w : Fin d → Per.BdR l)
    (hw : ∀ (g : ↥(GK K)) r, Per.σD (g : GQ l) (w r) = w r) :
    ∃ (y : ℤ_[l]) (z : Fin d → ↥(OL K)), y ≠ 0 ∧
      ∀ r, C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z r))) =
        algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * w r := by
  have hx : ∀ r, ∃ x ∈ K.1, C.oD x = w r := fun r => hI K (w r) (fun g hg => hw ⟨g, hg⟩ r)
  choose x hxK hxw using hx
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  classical
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ_[l] ℚ_[l]
    (Finset.univ.image fun r => (⟨x r, hxK r⟩ : ↥K.1))
  refine ⟨y, fun r => ⟨y • ⟨x r, hxK r⟩, hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))⟩, hy0, fun r => ?_⟩
  rw [← hxw r, ← oD_int]
  congr 1
  change ((y • (⟨x r, hxK r⟩ : ↥K.1) : ↥K.1) : Om l) = _
  rw [← algebraMap_smul ℚ_[l] y, Algebra.smul_def]
  simp

theorem exists_lattice_generators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → (∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → Per.BdR l) (v : Fin m → Fin d → Per.BdR l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → Per.BdR l) = ∑ i, c i • v i) → ∀ N₀ : ℕ, ∃ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), N₀ ≤ N ∧ (∀ i, |k i| ≤ N) ∧ (∀ r s, C.ι (U r s) ∈ Per.FilD l (-(N : ℤ))) ∧ (∀ r i, (U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) ∧ (∀ i j, β i j ∈ Per.FilD l (-k i)) ∧ U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 := by
  intro l _ K P AI T C hF hI d ρ U U' hUU hU hfam N₀
  have hfil := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (xi C.ε) C.ker_theta.symm
  obtain ⟨-, -, hmono, -, hbd, -, -⟩ := hfil
  choose m k c v hv hvF hcF hsum using hfam
  have hUι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcol : ∀ (j : Fin d) (a : Fin (m j)), ∃ (y : ℤ_[l]) (z : Fin d → ↥(OL K)), y ≠ 0 ∧
      ∀ r, (U.map C.ι).mulVec (fun s => C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z s)))) r =
        algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * v j a r := by
    intro j a
    obtain ⟨y, z, hy0, hz⟩ := descend (K := K) C hI ((U'.map C.ι).mulVec (v j a))
      (inv_vec hF ρ U U' hUU hU (v j a) (hv j a))
    refine ⟨y, z, hy0, fun r => ?_⟩
    have : (fun s => C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z s)))) =
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y))) • (U'.map C.ι).mulVec (v j a) := by
      ext s; rw [hz s]; rfl
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hUι, Matrix.one_mulVec]
    rfl
  choose y z hy0 hz using hcol
  choose n hn using hbd

  classical
  let e : Fin (∑ j, m j) ≃ (Σ j : Fin d, Fin (m j)) := finSigmaFinEquiv.symm
  let inv : (p : Σ j : Fin d, Fin (m j)) → Per.BdRp l := fun p => ((isUnit_aDp_zA (hy0 p.1 p.2)).unit⁻¹ : (Per.BdRp l)ˣ)
  let kk : Fin (∑ j, m j) → ℤ := fun i => k (e i).1 (e i).2
  let cc : Matrix (Fin d) (Fin (∑ j, m j)) ↥(OL K) := fun r i => z (e i).1 (e i).2 r
  let β : Matrix (Fin (∑ j, m j)) (Fin d) (Per.BdR l) := fun i j' =>
    if (e i).1 = j' then algebraMap (Per.BdRp l) (Per.BdR l) (inv (e i)) * c (e i).1 (e i).2 else 0
  let N : ℕ := max N₀ (max (Finset.univ.sup fun i => (kk i).natAbs) (Finset.univ.sup fun q : Fin d × Fin d => n (C.ι (U q.1 q.2))))
  have hA : ∀ r i, (U.map C.ι * cc.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y (e i).1 (e i).2))) * v (e i).1 (e i).2 r := by
    intro r i
    rw [← hz]
    rfl
  refine ⟨N, ∑ j, m j, kk, cc, β, le_max_left _ _, fun i => ?_, fun r s => ?_, fun r i => ?_, fun i j' => ?_, ?_⟩
  · have h1 : (kk i).natAbs ≤ N :=
      le_trans (Finset.le_sup (f := fun i => (kk i).natAbs) (Finset.mem_univ i))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  · have h1 : n (C.ι (U r s)) ≤ N :=
      le_trans (Finset.le_sup (f := fun q : Fin d × Fin d => n (C.ι (U q.1 q.2))) (Finset.mem_univ (r, s)))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    exact hmono _ _ (by simpa using h1) (hn _)
  · rw [hA, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hvF _ _ _)
  · simp only [β]
    split_ifs
    · rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hcF _ _)
    · exact Submodule.zero_mem _
  · ext r j'
    rw [Matrix.mul_apply]
    simp_rw [hA]
    let G : (Σ j : Fin d, Fin (m j)) → Per.BdR l := fun p =>
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y p.1 p.2))) * v p.1 p.2 r *
        (if p.1 = j' then algebraMap (Per.BdRp l) (Per.BdR l) (inv p) * c p.1 p.2 else 0)
    have e1 : ∀ i, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y (e i).1 (e i).2))) * v (e i).1 (e i).2 r * β i j' = G (e i) := fun i => rfl
    simp_rw [e1]
    rw [Equiv.sum_comp e G, Fintype.sum_sigma, Finset.sum_eq_single j']
    · have hs : ∀ a : Fin (m j'), G ⟨j', a⟩ = c j' a * v j' a r := by
        intro a
        show algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y j' a))) * v j' a r *
          (if j' = j' then algebraMap (Per.BdRp l) (Per.BdR l) (inv ⟨j', a⟩) * c j' a else 0) = _
        rw [if_pos rfl]
        have hu : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y j' a))) *
            algebraMap (Per.BdRp l) (Per.BdR l) (inv ⟨j', a⟩) = 1 := by
          rw [← map_mul, show aDp l (Per.zA l (y j' a)) * inv ⟨j', a⟩ = 1 from
            (isUnit_aDp_zA (hy0 j' a)).mul_val_inv, map_one]
        calc _ = (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y j' a))) *
            algebraMap (Per.BdRp l) (Per.BdR l) (inv ⟨j', a⟩)) * (c j' a * v j' a r) := by ring
          _ = _ := by rw [hu, one_mul]
      simp_rw [hs]
      have h2 := congrFun (hsum j') r
      rw [Finset.sum_apply] at h2
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      rw [← h2, Pi.single_apply, Matrix.one_apply]
    · intro j _ hj
      exact Finset.sum_eq_zero fun a _ => by simp [G, hj]
    · intro h; exact absurd (Finset.mem_univ j') h

end GlobalTheory.BdRLatticeGens
