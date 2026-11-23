import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmpSemilinearPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitToBFrobEisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiWInclLEPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToBcrisPhiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisComparisonKisinLatticeStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrisComparison

theorem toB_tmul' {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O) (w : Ainf l) :
    toB l O (o ⊗ₜ w) = o ⊗ₜ acrisToBcris l (ainfToAcris l w) := rfl

theorem toB_frobOA {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (x : OA l O) :
    toB l O (frobOA l O x) = frobOB l O (toB l O x) := by
  simp only [toB, AlgHom.comp_apply, frobOB_toOB, frobOCr_toOCr]

theorem toB_galOA {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) (x : OA l O) :
    toB l O (galOA O g x) = galOB O g (toB l O x) := by
  simp only [toB, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]

theorem map_smul_tw {O R N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup N] [Module O N]
    (σ : R →ₐ[O] R) (h : N →ₗ[O] N) (r : R) (z : R ⊗[O] N) :
    TensorProduct.map σ.toLinearMap h (r • z) = σ r • TensorProduct.map σ.toLinearMap h z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul x y => simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem inclL_smul' {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)
    (r : OA l O) (c : ι → OA l O) : inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

theorem exists_Y : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → ∃ Y : Matrix ι ι (OA l O), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α hα
  have key : ∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) := by
    intro i j
    have hv : (fun τ k => P.mx τ k j : Vec K a ι) ∈ P.L := mem_tot.2 fun τ => P.mem_extc.2
      ⟨Pi.single j 1, fun k => by
        by_cases hk : k = j
        · subst hk; simp only [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne hk]; exact zero_mem _, by
        ext1 k; simp [Matrix.mulVec_single]⟩
    have h := hα _ hv
    exact ⟨fun τ => ⟨E K l e ^ α * P.mx τ i j, mem_tot.1 h τ i⟩, fun τ => rfl⟩
  choose f hf using key
  exact ⟨fun i j => ϖ.iTot t K (f i j), fun i j => ⟨f i j, hf i j, rfl⟩⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), (∃ jB, IsCrisCmp I jB) ∧ ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → (∀ (m m' : P.MMl), m'.1 = P.phi m.1 → jB (toBcris t ϖ P m') = TWmap (frobOB l O) T (jB (toBcris t ϖ P m))) ∧ (∀ w b b', IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB w b' → b = b') ∧ (∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB (phiW t ϖ P w) (TWmap (frobOB l O) T b)) ∧ (∀ x : ↥T.L.T, IsCrisVal t ϖ P jB (I.ofT x) ((1 : OB l O) ⊗ₜ[O] x)) ∧ (∀ g : Gl l, (∀ v ∈ LA t ϖ P, I.act (sQ l g) g v ∈ LA t ϖ P) → ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB (I.act (sQ l g) g w) (actB (sQ l) T g b)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).1
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, hμB, -, -, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨-, -, hK3, hK4⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  have hunit : ∀ n : ℕ, IsUnit (toB l O (1 ⊗ₜ (muOf ε ^ n))) := fun n => by
    rw [toB_tmul', map_pow, map_pow]
    exact (hμB.pow n).map (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
  obtain ⟨Y, hY⟩ := exists_Y l a e O K t ϖ ι P α hα
  have hEu := GlobalTheory.T.isUnit_toB_frobOA_eis l a e O ϖ
  have hYphi := GlobalTheory.T.eis_pow_smul_phiW_inclL_eq_inclL_mulVec l a e O K t ϖ ι P α Y hY
  have hSl := GlobalTheory.T.toBcris_phi_alt l a e O K t ϖ ι P α Y hY
  refine ⟨GlobalTheory.T.exists_bcris_comparison_kisinLattice l a e O K t ϖ ι P T I, fun jB hjB => ?_⟩
  have hμL : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • v) = TWincl (inclO l O) T z :=
    hK4
  have keyφ := GlobalTheory.T.cmp_semilinear_pair_alt l a e O K t ϖ ι P T I jB hjB _ (hunit α) hμL (frobOA l O) (frobOW l O) (frobOB l O)
    LinearMap.id (phiW t ϖ P) (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α) (Y.map (frobOA l O))
    (fun x => (frobOW_inclO x).symm) toB_frobOA (fun v => I.j_φ v) (phiW_smul t ϖ P)
    (fun c => by rw [map_pow]; exact hYphi c)
  refine ⟨fun m m' hmm => ?_, fun w b b' hb hb' => ?_, fun w b hb => ?_, fun x => ?_, fun g hg w b hb => ?_⟩
  · refine (hEu.pow α).smul_left_cancel.1 ?_
    rw [← LinearEquiv.map_smul, hSl m m' hmm, keyφ, map_pow]
    rfl
  · obtain ⟨m, c, hm, hw, hb⟩ := hb
    obtain ⟨m', c', hm', hw', hb'⟩ := hb'
    have h1 : m' • c = m • c' := inclL_injective t ϖ P (by
      rw [inclL_smul', inclL_smul', ← hw, ← hw', smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm])
    have h2 : ∀ (r : OA l O) (d : ι → OA l O), toB l O r • (fun i => toB l O (d i)) = fun i => toB l O ((r • d) i) :=
      fun r d => funext fun i => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    refine ((hm.mul hm').smul_left_cancel).1 ?_
    rw [mul_comm, mul_smul, hb, mul_comm, mul_smul, hb', ← LinearEquiv.map_smul, ← LinearEquiv.map_smul, h2, h2, h1]
  · obtain ⟨m, c, hm, hw, hb⟩ := hb
    refine ⟨frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * frobOA l O m, Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i), ?_, ?_, ?_⟩
    · rw [map_mul, map_pow, toB_frobOA m]
      exact (hEu.pow α).mul (hm.map _)
    · rw [map_mul, map_pow, mul_smul, ← frobOW_inclO m, ← phiW_smul, hw]
      exact hYphi c
    · have h3 := keyφ (fun i => toB l O (c i))
      rw [map_mul, mul_smul, toB_frobOA m]
      change _ • frobOB l O (toB l O m) • TensorProduct.map (frobOB l O).toLinearMap LinearMap.id b = _
      rw [← map_smul_tw, hb, ← h3]
      congr 1
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, toB_frobOA]
  · obtain ⟨c, hc⟩ := hK3 x
    refine ⟨1 ⊗ₜ (muOf ε ^ β), c, hunit β, hc.symm, ?_⟩
    have h4 := hjB c ((1 ⊗ₜ (muOf ε ^ β)) ⊗ₜ x) (by
      rw [hc, LinearEquiv.map_smul, I.j_ofT, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl)
    rw [h4, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  · obtain ⟨m, c, hm, hw, hb⟩ := hb
    obtain ⟨Γ, hΓ⟩ := (I.exists_isLMat_iff (sQ l g) g).2 hg
    have key := GlobalTheory.T.cmp_semilinear_pair_alt l a e O K t ϖ ι P T I jB hjB _ (hunit α) hμL (galOA O (sQ l g)) (galOW O (sQ l g))
      (galOB O (sQ l g)) (T.actT g) (I.act (sQ l g) g) 1 Γ (fun x => (galOW_inclO _ x).symm) (toB_galOA _)
      (fun v => I.j_act _ _ v) (I.act_smul _ _) (fun c => by rw [map_one, one_smul]; exact hΓ c)
    refine ⟨galOA O (sQ l g) m, Γ *ᵥ fun i => galOA O (sQ l g) (c i), ?_, ?_, ?_⟩
    · rw [toB_galOA]
      exact hm.map _
    · rw [← galOW_inclO, ← I.act_smul, hw]
      exact hΓ c
    · have h3 := key (fun i => toB l O (c i))
      rw [map_one, one_smul] at h3
      rw [toB_galOA]
      change _ • TensorProduct.map (galOB O (sQ l g)).toLinearMap (T.actT g) b = _
      rw [← map_smul_tw, hb, ← h3]
      congr 1
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, toB_galOA]

end GlobalTheory.CrisComparison
