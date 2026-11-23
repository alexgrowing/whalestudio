import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsMonicUnitCoeffZeroAnnihilatingOfSpectrumNo
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.InertiaFixesOfFrobeniusAnnihilatedMemFilZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfMemSpectrumFrobeniusMatrixFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriods
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc

open Polynomial

variable {l : ℕ} [Fact l.Prime]

private def wtS (l : ℕ) [Fact l.Prime] : Subring (Bcr l) where
  carrier := {b | (PP l).ιB b ∈ ((PP l).PD (botExt l)).Fil 0}
  mul_mem' := fun {a b} ha hb => by
    have := ((PP l).PD (botExt l)).Fil_mul 0 0 _ _ ha hb
    rw [add_zero, ← map_mul] at this
    exact this
  one_mem' := by
    change (PP l).ιB 1 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_one]; exact ((PP l).PD (botExt l)).one_mem
  add_mem' := fun {a b} ha hb => by
    change (PP l).ιB (a + b) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    change (PP l).ιB 0 ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_zero]; exact Submodule.zero_mem _
  neg_mem' := fun {a} ha => by
    change (PP l).ιB (-a) ∈ ((PP l).PD (botExt l)).Fil 0
    rw [map_neg]; exact Submodule.neg_mem _ ha

private theorem wt_alg (K : FinExt l) (c : ↥(K0 K)) : algebraMap ↥(K0 K) (Bcr l) c ∈ wtS l := by
  have h : (PP l).ιB (algebraMap ↥(K0 K) (Bcr l) c) ∈ ((PP l).PD K).Fil 0 := by
    rw [← (PP l).PD_ι K, AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 (PP l).R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact (((PP l).PD K).Fil 0).smul_mem _ ((PP l).PD K).one_mem
  have h2 := (PP l).PD_Fil K (botExt l) 0
  change (PP l).ιB _ ∈ (((PP l).PD (botExt l)).Fil 0 : Set (PP l).R.BdR)
  rw [← h2]
  exact h

private theorem wt_phi (K : FinExt l) (c : ↥(K0 K)) :
    (PP l).φB (algebraMap ↥(K0 K) (Bcr l) c) = algebraMap ↥(K0 K) (Bcr l) (((PP l).PD K).σ c) := by
  rw [← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]

private theorem wt_iter (K : FinExt l) {d : ℕ} (M : Matrix (Fin d) (Fin d) (Bcr l))
    (A : Matrix (Fin d) (Fin d) ↥(K0 K)) (hA : IsUnit A.det)
    (h : M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l))) (k : ℕ) :
    ∃ F : Matrix (Fin d) (Fin d) ↥(K0 K), IsUnit F.det ∧
      M.map (((PP l).φB)^[k]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) := by
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨F, hF, e⟩ := ih
    refine ⟨A * F.map ((PP l).PD K).σ, ?_, ?_⟩
    · rw [Matrix.det_mul]
      refine hA.mul ?_
      have := hF.map (((PP l).PD K).σ : ↥(K0 K) →+* ↥(K0 K))
      rw [RingHom.map_det] at this
      exact this
    · rw [Function.iterate_succ', ← Matrix.map_map, e, Matrix.map_mul, h, Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext i j
      exact wt_phi K _

private theorem wt_spec {L : Type} [Field L] {d : ℕ} (G : Matrix (Fin d) (Fin d) L) (hG : IsUnit G.det) {a : L}
    (ha : a ∈ spectrum L G) : a ≠ 0 ∧ a⁻¹ ∈ spectrum L (G⁻¹).transpose := by
  rw [spectrum.mem_iff] at ha
  have h0 : a ≠ 0 := by
    rintro rfl
    apply ha
    rw [map_zero, zero_sub]
    exact ((Matrix.isUnit_iff_isUnit_det _).2 hG).neg
  refine ⟨h0, spectrum.mem_iff.2 fun hu => ha ?_⟩
  have e : (algebraMap L (Matrix (Fin d) (Fin d) L) a⁻¹ - (G⁻¹).transpose).transpose * ((-a) • G) =
      algebraMap L (Matrix (Fin d) (Fin d) L) a - G := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.nonsing_inv_mul _ hG, smul_sub, smul_smul, neg_mul,
      mul_inv_cancel₀ h0, neg_smul, neg_smul, one_smul]
    abel
  rw [← e]
  refine ((Matrix.isUnit_transpose _).2 hu).mul ?_
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
  exact ((IsUnit.mk0 _ (neg_ne_zero.2 h0)).pow _).mul hG

private theorem wt_aeval (K : FinExt l) (ψ : Bcr l →ₐ[ℚ_[l]] Bcr l)
    (hψ : ∀ c : ↥(K0 K), ψ (algebraMap ↥(K0 K) (Bcr l) c) = algebraMap ↥(K0 K) (Bcr l) c) {d : ℕ}
    (M : Matrix (Fin d) (Fin d) (Bcr l)) (F : Matrix (Fin d) (Fin d) ↥(K0 K))
    (h : M.map ψ = M * F.map (algebraMap ↥(K0 K) (Bcr l))) (Q : ℚ_[l][X]) :
    M.map (aeval (ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) Q) =
      M * (aeval F (Q.map (algebraMap ℚ_[l] ↥(K0 K)))).map (algebraMap ↥(K0 K) (Bcr l)) := by
  have hp : ∀ n : ℕ, M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ n) =
      M * (F ^ n).map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      rfl
    | succ n ih =>
      have e : M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ (n + 1)) =
          (M.map ((ψ.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ n)).map ψ := by
        ext i j
        rw [pow_succ']
        rfl
      rw [e, ih, Matrix.map_mul, h, pow_succ', Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext i j
      exact hψ _
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, map_add, Matrix.map_add _ (map_add _), Matrix.mul_add, ← hp, ← hq]
    rfl
  | monomial n a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
    ext i j
    have := congrFun (congrFun (hp n) i) j
    simp only [Matrix.map_apply, Matrix.mul_apply] at this
    simp only [Matrix.map_apply, Matrix.mul_apply, LinearMap.smul_apply, this, Matrix.smul_apply, smul_eq_mul,
      map_mul, ← IsScalarTower.algebraMap_apply]
    rw [Algebra.smul_def, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

private theorem wt_matFix (K : FinExt l) {d : ℕ} (M M' : Matrix (Fin d) (Fin d) (Bcr l))
    (A : Matrix (Fin d) (Fin d) ↥(K0 K)) (hMM : M * M' = 1) (hM : ∀ i j, M i j ∈ wtS l)
    (hM' : ∀ i j, M' i j ∈ wtS l) (hA : IsUnit A.det)
    (h : M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l))) :
    ∀ g ∈ Iq l, M.map ((PP l).actQ g) = M := by
  haveI := ((PP l).PD K).finK₀
  let s : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) := AlgEquiv.ofBijective ((PP l).PD K).σ ((PP l).PD K).σ_bij
  have hf : 0 < orderOf s := orderOf_pos s
  have hσ : ∀ x : ↥(K0 K), (((PP l).PD K).σ)^[orderOf s] x = x := fun x => by
    have := AlgEquiv.congr_fun (pow_orderOf_eq_one s) x
    rw [AlgEquiv.coe_pow] at this
    exact this
  generalize orderOf s = f at hf hσ
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  have hc : ∀ k : ℕ, ((PP l).φB)^[k] = ⇑((PP l).φB ^ k) := fun k => (AlgHom.coe_pow _ _).symm
  choose F hF hMF using wt_iter K M A hA h
  have hinv : ∀ k, M'.transpose.map (((PP l).φB)^[k]) =
      M'.transpose * ((F k)⁻¹).transpose.map (algebraMap ↥(K0 K) (Bcr l)) := by
    intro k
    rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul]
    congr 1
    have e1 : M'.map (((PP l).φB)^[k]) * M.map (((PP l).φB)^[k]) = 1 := by
      rw [hc, ← Matrix.map_mul, hMM', Matrix.map_one _ (map_zero _) (map_one _)]
    have e2 : (F k).map (algebraMap ↥(K0 K) (Bcr l)) * ((F k)⁻¹).map (algebraMap ↥(K0 K) (Bcr l)) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (hF k), Matrix.map_one _ (map_zero _) (map_one _)]
    calc M'.map (((PP l).φB)^[k]) = M'.map (((PP l).φB)^[k]) * (M * ((F k).map (algebraMap ↥(K0 K) (Bcr l)) *
          ((F k)⁻¹).map (algebraMap ↥(K0 K) (Bcr l))) * M') := by rw [e2, Matrix.mul_one, hMM, Matrix.mul_one]
      _ = _ := by
        rw [← Matrix.mul_assoc M, ← hMF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hS : ∀ (N : Matrix (Fin d) (Fin d) (Bcr l)) (E : Matrix (Fin d) (Fin d) ↥(K0 K)) (k : ℕ),
      (∀ i j, N i j ∈ wtS l) → N.map (((PP l).φB)^[k]) = N * E.map (algebraMap ↥(K0 K) (Bcr l)) →
      ∀ i j, ((PP l).φB)^[k] (N i j) ∈ wtS l := by
    intro N E k hN e i j
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    rw [this]
    exact Subring.sum_mem _ fun r _ => Subring.mul_mem _ (hN _ _) (wt_alg K _)
  have h1 := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ M M' (F f) hMM' (fun k => hS M (F k) k hM (hMF k)) (hMF f)
  have h2 := UpperTheory.norm_le_one_of_mem_spectrum_frobenius_matrix_fil_zero K f hf hσ M'.transpose M.transpose ((F f)⁻¹).transpose
    (by rw [← Matrix.transpose_mul, hMM', Matrix.transpose_one])
    (fun k => hS M'.transpose _ k (fun i j => hM' j i) (hinv k)) (hinv f)
  obtain ⟨P, hP, hP0, hPF⟩ := UpperTheory.exists_monic_unit_coeff_zero_annihilating_of_spectrum_norm_one (K0 K) (F f) (fun a ha => by
    have hu : IsUnit ((F f).map (algebraMap ↥(K0 K) (Om l))).det := by
      have := (hF f).map (algebraMap ↥(K0 K) (Om l))
      rw [RingHom.map_det] at this
      exact this
    obtain ⟨h0, ha'⟩ := wt_spec _ hu ha
    have e : ((F f).map (algebraMap ↥(K0 K) (Om l)))⁻¹ = ((F f)⁻¹).map (algebraMap ↥(K0 K) (Om l)) := by
      apply Matrix.inv_eq_right_inv
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (hF f), Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e, ← Matrix.transpose_map] at ha'
    have h3 := h2 _ ha'
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.2 h0)] at h3
    exact le_antisymm (h1 a ha) h3)
  have hfix : ∀ (k : ℕ) (c : ↥(K0 K)), ((PP l).φB)^[k] (algebraMap ↥(K0 K) (Bcr l) c) =
      algebraMap ↥(K0 K) (Bcr l) ((((PP l).PD K).σ)^[k] c) := by
    intro k
    induction k with
    | zero => intro c; rfl
    | succ k ih => intro c; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, wt_phi]
  have h4 := wt_aeval K ((PP l).φB ^ f) (fun c => by rw [← hc, hfix, hσ]) M (F f) (by rw [← hc]; exact hMF f)
    (P.map (algebraMap ℤ_[l] ℚ_[l]))
  rw [Polynomial.map_map, hPF, Matrix.map_zero _ (map_zero _), Matrix.mul_zero] at h4
  intro g hg
  ext i j
  refine UpperTheory.inertia_fixes_of_frobenius_annihilated_mem_fil_zero (expand ℤ_[l] f P) (hP.expand hf) (by rwa [coeff_expand hf, if_pos (dvd_zero _), Nat.zero_div])
    (M i j) ?_ (fun k => hS M (F k) k hM (hMF k) i j) g hg
  have e : ((PP l).φB.toLinearMap : Module.End ℚ_[l] (Bcr l)) ^ f = ((PP l).φB ^ f).toLinearMap := by
    ext x
    rw [Module.End.pow_apply, AlgHom.toLinearMap_apply, ← hc]
    rfl
  rw [Polynomial.map_expand, expand_aeval, e]
  exact congrFun (congrFun h4 i) j

end UpperTheory.V.Loc

section Coord

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V]
    (ρ : Representation Qp G V) {d : ℕ} (e : Basis (Fin d) Qp V)

private theorem coord_sum (c : Fin d → BdR) (i : Fin d) :
    (TensorProduct.lid Qp BdR) (LinearMap.rTensor BdR (e.coord i) (∑ j, e j ⊗ₜ[Qp] c j)) = c i := by
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply, Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj]
  · simp

private theorem sum_mem_fil_iff (a : ℤ) (c : Fin d → BdR) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ FilV PD (LL := Qp) (V := V) a ↔ ∀ i, c i ∈ PD.Fil a := by
  constructor
  · rintro ⟨z, hz⟩ i
    rw [← coord_sum e c i, ← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v x =>
      have := ((PD.Fil a).restrictScalars Qp).smul_mem (e.coord i v) x.2
      simpa using this
    | add x y hx hy =>
      simp only [map_add]
      exact Submodule.add_mem _ hx hy
  · intro h
    exact Submodule.sum_mem _ fun j _ => ⟨e j ⊗ₜ ⟨c j, h j⟩, rfl⟩

private theorem sum_mem_DdR (c : Fin d → BdR)
    (h : ∀ g, ((LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)).mulVec (fun j => PD.actdR g (c j)) = c) :
    ∑ j, e j ⊗ₜ[Qp] c j ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  intro g
  conv_rhs => rw [← h g]
  simp only [map_sum, Matrix.mulVec, dotProduct, tmul_sum, Matrix.map_apply, LinearMap.toMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ρ g (e j) ⊗ₜ[Qp] PD.actdR g (c j) = _
  conv_lhs => rw [← e.sum_repr (ρ g (e j))]
  rw [sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_tmul, Algebra.smul_def]

private theorem core
    (hinv : ∀ a b, b ∈ PD.Fil a → b ∉ PD.Fil (a + 1) → ∃ β ∈ PD.Fil (-a), β * b - 1 ∈ PD.Fil 1)
    (hT : ∀ n x, x ∈ PD.Fil n → (∀ g, PD.actdR g x - x ∈ PD.Fil (n + 1)) →
      ∃ κ ∈ PD.Fil 0, (∀ g, PD.actdR g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ x - κ ∈ PD.Fil (n + 1))
    (h0 : DdR PD ρ ≤ FilV PD (LL := Qp) (V := V) 0) (h1 : DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) 1 = ⊥)
    (N N' : Matrix (Fin d) (Fin d) BdR) (hN : N * N' = 1)
    (hg : ∀ g, (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR) * N.map (PD.actdR g) = N) :
    (∀ i j, N i j ∈ PD.Fil 0) ∧ ∀ i j, N' i j ∈ PD.Fil 0 := by
  let A : G → Matrix (Fin d) (Fin d) BdR := fun g => (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp BdR)
  have hA : ∀ g i j, A g i j ∈ PD.Fil 0 := fun g i j => by
    change algebraMap Qp BdR _ ∈ _
    rw [IsScalarTower.algebraMap_apply Qp K BdR, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ PD.one_mem
  have hcol : ∀ j g, (A g).mulVec (fun i => PD.actdR g (N i j)) = fun i => N i j := fun j g => by
    funext i
    exact congrFun (congrFun (hg g) i) j
  have hN' : N' * N = 1 := mul_eq_one_comm.1 hN
  have hA' : ∀ g, N' * A g = N'.map (PD.actdR g) := fun g => by
    have h2 : N.map (PD.actdR g) * N'.map (PD.actdR g) = 1 := by
      have := congrArg (fun X : Matrix (Fin d) (Fin d) BdR => X.map (PD.actdR g : BdR →+* BdR)) hN
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    calc N' * A g = N' * A g * (N.map (PD.actdR g) * N'.map (PD.actdR g)) := by rw [h2, mul_one]
      _ = N' * (A g * N.map (PD.actdR g)) * N'.map (PD.actdR g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg g, hN', one_mul]
  refine ⟨fun i j => (sum_mem_fil_iff PD e 0 (fun i => N i j)).1 (h0 (sum_mem_DdR PD ρ e _ (hcol j))) i,
    fun i j => ?_⟩
  have hFa : Antitone fun a => (PD.Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => PD.Fil_anti a
  let R : G → (Fin d → BdR) →+ (Fin d → BdR) := fun g =>
    { toFun := fun c => (A g).mulVec (fun j => PD.actdR g (c j))
      map_zero' := by simp [← Pi.zero_def]
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]
        congr 1
        funext j
        simp }
  let FM : ℤ → AddSubgroup (Fin d → BdR) := fun a => AddSubgroup.pi Set.univ fun _ => (PD.Fil a).toAddSubgroup
  have hFM : ∀ a c, c ∈ FM a ↔ ∀ i, c i ∈ PD.Fil a := fun a c => by
    simp [FM, AddSubgroup.mem_pi]
  obtain ⟨m, k, b, c, h, hs⟩ := GlobalTheory.DRFil.filtered (G := G) (fun g => (PD.actdR g : BdR →+* BdR)) R
    (fun a => (PD.Fil a).toAddSubgroup) FM
    (fun g b x => by
      change (A g).mulVec _ = _ • (A g).mulVec _
      rw [← Matrix.mulVec_smul]
      congr 1
      funext j
      simp)
    PD.Fil_mul
    (fun a c x z hx hz => (hFM _ _).2 fun i => PD.Fil_mul _ _ _ _ hx ((hFM _ _).1 hz i))
    PD.Fil_G
    (fun g a z hz => (hFM _ _).2 fun i => by
      change ∑ j, A g i j * PD.actdR g (z j) ∈ _
      refine Submodule.sum_mem _ fun j _ => ?_
      have := PD.Fil_mul _ _ _ _ (hA g i j) (PD.Fil_G g _ _ ((hFM _ _).1 hz j))
      rwa [zero_add] at this)
    hinv hT hFa (fun a a' h z hz => (hFM _ _).2 fun i => hFa h ((hFM _ _).1 hz i)) PD.Fil_exh
    (fun x => by
      choose r hr using fun i => PD.Fil_exh (x i)
      obtain ⟨a, ha⟩ := (Set.finite_range r).bddBelow
      exact ⟨a, (hFM _ _).2 fun i => hFa (ha ⟨i, rfl⟩) (hr i)⟩)
    0 (fun i => (1 : Matrix (Fin d) (Fin d) BdR) i j)
    ((hFM _ _).2 fun i => by
      rw [Matrix.one_apply]
      split_ifs
      exacts [PD.one_mem, Submodule.zero_mem _])
    d (fun i => N' i j) (fun j i => N i j) (fun j g => hcol j g)
    (by
      funext i
      rw [← hN, Matrix.mul_apply, Finset.sum_apply]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _)
  have h3 : N' i j = ∑ n, b n * N'.mulVec (c n) i := by
    have h4 := congrFun (congrArg N'.mulVec hs) i
    rw [Matrix.mulVec_sum, Finset.sum_apply] at h4
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h4
    rw [← h4]
    exact (congrFun (congrFun (mul_one N') i) j).symm
  rw [h3]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨hc, hk, hb⟩ := h n
  by_cases hk1 : 1 ≤ k n
  · have h5 : ∑ j, e j ⊗ₜ[Qp] c n j ∈ DdR PD ρ ⊓ FilV PD (LL := Qp) (V := V) 1 :=
      ⟨sum_mem_DdR PD ρ e _ hc, (sum_mem_fil_iff PD e 1 _).2 fun i => hFa hk1 ((hFM _ _).1 hk i)⟩
    rw [h1, Submodule.mem_bot] at h5
    have h6 : c n = 0 := funext fun i => by
      rw [← coord_sum e (c n) i, h5]
      simp
    rw [h6]
    simp
  · have h5 : b n ∈ PD.Fil 0 := hFa (show (0 : ℤ) ≤ 0 - k n by omega) hb
    obtain ⟨κ, hκ⟩ := PD.invdR (N'.mulVec (c n) i) fun g => by
      have h6 : (A g).mulVec (fun j => PD.actdR g (c n j)) = c n := hc g
      conv_rhs => rw [← h6, Matrix.mulVec_mulVec, hA' g]
      simp [Matrix.mulVec, dotProduct]
    have h6 : N'.mulVec (c n) i ∈ PD.Fil 0 := by
      rw [← hκ, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ PD.one_mem
    simpa using PD.Fil_mul _ _ _ _ h5 h6

end Coord

section GenMat

private theorem genMat {Q B G V : Type} [Field Q] [CommRing B] [IsDomain B] [Algebra Q B] [AddCommGroup V]
    [Module Q V] (a : G → B →ₐ[Q] B) (r : G → V →ₗ[Q] V) (hr : ∀ g, LinearMap.det (r g) ≠ 0)
    (hu : ∀ b : B, b ≠ 0 → (∀ g, ∃ x : Q, a g b = algebraMap Q B x * b) → IsUnit b)
    {d : ℕ} (v : Basis (Fin d) Q V) (w : Fin d → B ⊗[Q] V)
    (hw : ∀ g i, TensorProduct.map (a g).toLinearMap (r g) (w i) = w i) (hi : LinearIndependent B w) :
    ∃ M M' : Matrix (Fin d) (Fin d) B, M * M' = 1 ∧
      ∀ g, (LinearMap.toMatrix v v (r g)).map (algebraMap Q B) * M.map (a g) = M := by
  classical
  let e := Algebra.TensorProduct.basis B v
  let A := e.toMatrix w
  have hA : A.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc
    funext i
    refine Fintype.linearIndependent_iff.1 hi c ?_ i
    apply e.repr.injective
    ext j
    have := congrFun hc0 j
    simp only [Matrix.mulVec, dotProduct, A, Basis.toMatrix_apply, Pi.zero_apply] at this
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_zero, Finsupp.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hs : ∀ g (b : B) (x : B ⊗[Q] V), TensorProduct.map (a g).toLinearMap (r g) (b • x) =
      a g b • TensorProduct.map (a g).toLinearMap (r g) x := by
    intro g b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hrep : ∀ g (x : B ⊗[Q] V) k, e.repr (TensorProduct.map (a g).toLinearMap (r g) x) k =
      ∑ j, algebraMap Q B (v.repr (r g (v j)) k) * a g (e.repr x j) := by
    intro g x k
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, hs, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    simp [e, Algebra.algebraMap_eq_smul_one]
  have h1 : ∀ g, (LinearMap.toMatrix v v (r g)).map (algebraMap Q B) * A.map (a g) = A := by
    intro g
    ext k i
    rw [Matrix.mul_apply]
    change _ = e.repr (w i) k
    conv_rhs => rw [← hw g i, hrep]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply, A]
  have hdet : IsUnit A.det := by
    refine hu _ hA fun g => ?_
    have h2 := congrArg Matrix.det (h1 g)
    have e1 : (A.map (a g)).det = a g A.det := ((a g : B →+* B).map_det A).symm
    have e2 : ((LinearMap.toMatrix v v (r g)).map (algebraMap Q B)).det = algebraMap Q B (LinearMap.det (r g)) := by
      rw [← LinearMap.det_toMatrix v, RingHom.map_det]; rfl
    rw [Matrix.det_mul, e1, e2] at h2
    refine ⟨(LinearMap.det (r g))⁻¹, ?_⟩
    conv_rhs => rw [← h2]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hr g), map_one, one_mul]
  exact ⟨A, A⁻¹, Matrix.mul_nonsing_inv _ hdet, h1⟩

private theorem det_rep {Q G V : Type} [Field Q] [Group G] [AddCommGroup V] [Module Q V]
    (ρ : Representation Q G V) (g : G) : LinearMap.det (ρ g) ≠ 0 :=
  (((Group.isUnit g).map ρ).map LinearMap.det).ne_zero

private theorem inv_law {B n : Type} [CommRing B] [Fintype n] [DecidableEq n] (f : B →+* B)
    {R M M' : Matrix n n B} (hM : M * M' = 1) (h : R * M.map f = M) : M'.map f = M' * R := by
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  have h1 : M.map f * M'.map f = 1 := by
    rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
  have : R * (M.map f * M'.map f) = M * M'.map f := by
    rw [← Matrix.mul_assoc, h]
  rw [h1, Matrix.mul_one] at this
  rw [this, ← Matrix.mul_assoc, hM', Matrix.one_mul]

private theorem coeff_mem {Q B D : Type} [Field Q] [CharZero Q] [CommRing B] [CommRing D] [Algebra Q D]
    (S : Subalgebra Q D) (ι : B →+* D) (u : D) (hu : u ∈ S) (p : Polynomial B)
    (h : ∀ k : ℕ, Polynomial.eval₂ ι u (Polynomial.derivative^[k] p) ∈ S) (n : ℕ) : ι (p.coeff n) ∈ S := by
  have h1 : ∀ k, (Polynomial.taylor u (p.map ι)).coeff k ∈ S := by
    intro k
    have h2 := h k
    rw [← Polynomial.eval_map, ← Polynomial.iterate_derivative_map, ← Polynomial.factorial_smul_hasseDeriv,
      LinearMap.smul_apply, Polynomial.eval_smul, ← Polynomial.taylor_coeff, ← Nat.cast_smul_eq_nsmul Q] at h2
    have h3 := S.smul_mem h2 ((k.factorial : Q)⁻¹)
    rwa [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 k.factorial_ne_zero), one_smul] at h3
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts (f := (S.val : S →+* D)) _).1
    ((Polynomial.lifts_iff_coeff_lifts (f := (S.val : S →+* D)) _).2 fun k => ⟨⟨_, h1 k⟩, rfl⟩)
  have h4 : p.map ι = (Polynomial.taylor (⟨-u, S.neg_mem hu⟩ : S) q).map (S.val : S →+* D) := by
    rw [Polynomial.map_taylor, hq]
    exact (Polynomial.taylor_taylor _ _ _).trans (by simp) |>.symm
  rw [← Polynomial.coeff_map, h4, Polynomial.coeff_map]
  exact Subtype.prop _

end GenMat

section Log

open Formalism GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

private theorem exists_log (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) : ∃ U ∈ (P.PD K).Fil 0,
      ∀ g : GQ l, P.actQdR g U = U + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus l (beta ϖ) (by
    rw [GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer l P Co hC.ζ ϖ hr hϖ u hu
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u), ?_, fun g => ?_⟩
  · rw [T.fil, RingEquiv.apply_symm_apply]
    exact GlobalTheory.RingIface.alg_mem_FilD_zero l u
  · apply T.eD.injective
    rw [T.actD, RingEquiv.apply_symm_apply, map_add, RingEquiv.apply_symm_apply, hct]
    rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from GlobalTheory.RingIface.sigD_alg l _ _, hg, map_add]

end Log

section DrMat

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V]

private theorem drMat (hF : IsField BdR) (ρ : Representation Qp G V)
    {d : ℕ} (v : Basis (Fin d) Qp V) (h : IsDR PD ρ) :
    ∃ N N' : Matrix (Fin d) (Fin d) BdR, N * N' = 1 ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp BdR) * N.map (PD.actdR g) = N := by
  haveI : IsDomain BdR := hF.isDomain
  obtain ⟨_, hr⟩ := GlobalTheory.Per.DeRhamSpan.finrank_DdRK PD ρ h
  rw [finrank_eq_card_basis v, Fintype.card_fin] at hr
  let e := Module.finBasisOfFinrankEq K _ hr
  let a : G → BdR →ₐ[Qp] BdR := fun g => (PD.actdR g).toAlgHom.restrictScalars Qp
  have hσ : ∀ g (b : BdR) (w : BdR ⊗[Qp] V), TensorProduct.map (a g).toLinearMap (ρ g) (b • w) =
      a g b • TensorProduct.map (a g).toLinearMap (ρ g) w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hc : ∀ g x, TensorProduct.map (a g).toLinearMap (ρ g) (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hw : ∀ g k, TensorProduct.map (a g).toLinearMap (ρ g) (e k : BdR ⊗[Qp] V) = e k := by
    intro g k
    have h1 := hc g ((TensorProduct.comm Qp V BdR).symm (e k))
    have h2 : (TensorProduct.comm Qp V BdR).symm (e k) ∈ DdR PD ρ := (e k).2
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at h2
    rw [h2 g, LinearEquiv.apply_symm_apply] at h1
    exact h1
  have hi : LinearIndependent BdR fun k => (e k : BdR ⊗[Qp] V) := by
    letI := hF.toField
    exact GlobalTheory.Per.linearIndependent_of_invariant _ _ _ _ (fun g => (a g : BdR →+* BdR))
      (fun g => (TensorProduct.map (a g).toLinearMap (ρ g)).toAddMonoidHom) hσ _ hw
      (fun c hcg hsum k => by
        choose x hx using fun p => PD.invdR (c p) fun g => hcg g p
        have h1 : ∑ i, x i • e i = 0 := by
          apply Subtype.ext
          rw [Submodule.coe_zero, ← hsum]
          simp only [Submodule.coe_sum, Submodule.coe_smul, ← hx, algebraMap_smul]
        rw [← hx, Fintype.linearIndependent_iff.1 e.linearIndependent x h1 k, map_zero])
  exact genMat a (fun g => ρ g) (det_rep ρ) (fun b hb _ => by
    obtain ⟨c, hc⟩ := hF.mul_inv_cancel hb
    exact IsUnit.of_mul_eq_one c hc) v _ hw hi

end DrMat

section Mats

open GlobalTheory.Pst Polynomial

variable {l : ℕ} [Fact l.Prime]

private theorem stMat {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (K : FinExt l) {V : Type}
    [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V)
    {d : ℕ} (v : Basis (Fin d) ℚ_[l] V) (h : IsPst P ρ) :
    ∃ (K' : FinExt l) (hK : K.1 ≤ K'.1) (M M' : Matrix (Fin d) (Fin d) (Bst P)), M * M' = 1 ∧
      ∀ g : ↥(GK K'), (LinearMap.toMatrix v v (ρ ⟨g, GK_le hK g.2⟩)).map (algebraMap ℚ_[l] (Bst P)) *
        M.map (actSt P (g : GQ l)) = M := by
  obtain ⟨hdom, hreg, hu⟩ := stRegular l P AI ⟨T⟩
  obtain ⟨_, hdim⟩ := (isPst_iff P ρ).mp h
  rw [finrank_eq_card_basis v, Fintype.card_fin] at hdim
  let b := Module.finBasisOfFinrankEq ↥(MaximalUnramifiedExtension l) _ hdim
  choose F hF using fun i => (mem_Dpst P ρ).mp ((toUr P ρ).symm (b i)).2
  have hFd := fun i => (F i).2
  let K' : FinExt l := supExt K ⟨⨆ i, (F i).1, inferInstance⟩
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hFK' : ∀ i, (F i).1 ≤ K'.1 := fun i => (le_iSup (fun i => (F i).1) i).trans le_sup_right
  let w : Fin d → Bst P ⊗[ℚ_[l]] V := fun i => GlobalTheory.PstRank.toB P ρ (b i)
  have hv : ∀ (g : ↥(GK K')) i, GlobalTheory.PstRank.sigSt P ρ ⟨g, GK_le hKK' g.2⟩ (w i) = w i := by
    intro g i
    change GlobalTheory.PstRank.sigSt P ρ _ (TensorProduct.comm ℚ_[l] V (Bst P) _) = _
    rw [GlobalTheory.PstRank.sigSt_comm, hF i ⟨g, GK_le hKK' g.2⟩ (GK_le (hFK' i) g.2)]
    rfl
  have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) w := b.linearIndependent.map' (GlobalTheory.PstRank.toB P ρ)
    (LinearMap.ker_eq_bot.mpr (GlobalTheory.PstRank.toB_injective P ρ))
  have hB : LinearIndepOn (Bst P) w ((Finset.univ : Finset (Fin d)) : Set (Fin d)) :=
    GlobalTheory.RegularRing.linearIndepOn_of_invariant (K := ↥(MaximalUnramifiedExtension l)) (B := Bst P) (G := ↥(GK K'))
      (fun g b => actSt P (g : GQ l) b)
      (fun g => (GlobalTheory.PstRank.sigSt P ρ ⟨g, GK_le hKK' g.2⟩).toAddMonoidHom)
      (fun g b w => GlobalTheory.PstRank.sigSt_smul P ρ _ b w)
      (fun b b' hb h => by
        obtain ⟨c, -, hc⟩ := hreg K' b b' hb h
        exact ⟨c, hc⟩)
      w hv Finset.univ (hli.linearIndepOn _)
  have hB' : LinearIndependent (Bst P) w := by
    rw [← linearIndepOn_univ]; rw [Finset.coe_univ] at hB; exact hB
  obtain ⟨M, M', h1, h2⟩ := genMat (fun g : ↥(GK K') => actSt P (g : GQ l)) (fun g => ρ ⟨g, GK_le hKK' g.2⟩)
    (fun g => det_rep ρ _) (hu K') v w hv hB'
  exact ⟨K', hKK', M, M', h1, h2⟩

private def fil0 (P : LocPrime l) (K : FinExt l) : Subalgebra ℚ_[l] P.R.BdR where
  carrier := (P.PD K).Fil 0
  mul_mem' := fun {a b} ha hb => by
    have := (P.PD K).Fil_mul 0 0 _ _ ha hb
    rwa [add_zero] at this
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  algebraMap_mem' := fun c => by
    rw [IsScalarTower.algebraMap_apply ℚ_[l] ↥K.1 P.R.BdR]
    exact GlobalTheory.DRFil.alg_mem_fil_zero K _

private theorem mul_mem_deRhamPeriodFiltration_of_mem_zero {Q D n : Type} [CommRing Q] [CommRing D] [Algebra Q D] [Fintype n] (S : Subalgebra Q D)
    {X Y : Matrix n n D} (hX : ∀ i j, X i j ∈ S) (hY : ∀ i j, Y i j ∈ S) (i j : n) : (X * Y) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact Subalgebra.sum_mem _ fun k _ => S.mul_mem (hX _ _) (hY _ _)

private theorem inverse_matrix_entries_mem_fil0 (P : LocPrime l) (K : FinExt l) {n : Type} [Fintype n] [DecidableEq n]
    (R : ↥(GK K) → Matrix n n P.R.BdR) (N N' : Matrix n n P.R.BdR) (hN : N * N' = 1)
    (hg : ∀ g : ↥(GK K), R g * N.map (P.actQdR (g : GQ l)) = N)
    (h1 : ∀ i j, N i j ∈ fil0 P K) (h2 : ∀ i j, N' i j ∈ fil0 P K) :
    (∀ Y : Matrix n n P.R.BdR, (∀ g : ↥(GK K), R g * Y.map (P.actQdR (g : GQ l)) = Y) →
      ∀ i j, Y i j ∈ fil0 P K) ∧
    (∀ Y : Matrix n n P.R.BdR, (∀ g : ↥(GK K), Y.map (P.actQdR (g : GQ l)) = Y * R g) →
      ∀ i j, Y i j ∈ fil0 P K) := by
  have hfix : ∀ Z : Matrix n n P.R.BdR, (∀ g : ↥(GK K), Z.map (P.actQdR (g : GQ l)) = Z) →
      ∀ i j, Z i j ∈ fil0 P K := by
    intro Z hZ i j
    obtain ⟨c, hc⟩ := (P.PD K).invdR (Z i j) fun g => by
      rw [P.PD_actdR]; exact congrFun (congrFun (hZ g) i) j
    rw [← hc]
    exact GlobalTheory.DRFil.alg_mem_fil_zero K _
  refine ⟨fun Y hY => ?_, fun Y hY => ?_⟩
  · have e : Y = N * (N' * Y) := by rw [← Matrix.mul_assoc, hN, Matrix.one_mul]
    rw [e]
    refine mul_mem_deRhamPeriodFiltration_of_mem_zero _ h1 (hfix _ fun g => ?_)
    have h3 : N'.map (P.actQdR (g : GQ l)) = N' * R g :=
      inv_law (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR) hN (hg g)
    rw [Matrix.map_mul, h3, Matrix.mul_assoc, hY]
  · have e : Y = (Y * N) * N' := by rw [Matrix.mul_assoc, hN, Matrix.mul_one]
    rw [e]
    refine mul_mem_deRhamPeriodFiltration_of_mem_zero _ (hfix _ fun g => ?_) h2
    rw [Matrix.map_mul, hY, Matrix.mul_assoc, hg]

private theorem der_actSt (P : LocPrime l) (g : GQ l) (k : ℕ) (p : Bst P) :
    derivative^[k] (actSt P g p) = actSt P g (derivative^[k] p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    have := monSt_actSt P g (derivative^[k] p)
    rw [monSt_apply, monSt_apply, map_neg] at this
    exact neg_injective this

private theorem iota_act (P : LocPrime l) (g : GQ l) (z : P.R.B) : P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
  have := (P.PD (GlobalTheory.Pst.botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
  rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this

private theorem ev_actSt (P : LocPrime l) (U : P.R.BdR) (g : GQ l)
    (hU : P.actQdR g U = U + P.ιB ((kummer P g : ℚ_[l]) • P.tB)) (p : Bst P) :
    eval₂ (P.ιB : P.R.B →+* P.R.BdR) U (actSt P g p) = P.actQdR g (eval₂ (P.ιB : P.R.B →+* P.R.BdR) U p) := by
  have : (eval₂RingHom (P.ιB : P.R.B →+* P.R.BdR) U).comp (actSt P g : Bst P →+* Bst P) =
      (P.actQdR g : P.R.BdR →+* P.R.BdR).comp (eval₂RingHom (P.ιB : P.R.B →+* P.R.BdR) U) := by
    refine Polynomial.ringHom_ext (fun b => ?_) ?_
    · simp [iota_act]
    · simp [hU]
  exact RingHom.congr_fun this p

private theorem coeff_mem_fil0_of_invertible_period (P : LocPrime l) (K : FinExt l) {n : Type} [Fintype n] [DecidableEq n]
    (U : P.R.BdR) (hU0 : U ∈ fil0 P K)
    (hU : ∀ g : GQ l, P.actQdR g U = U + P.ιB ((kummer P g : ℚ_[l]) • P.tB))
    (R : ↥(GK K) → Matrix n n ℚ_[l]) (N N' : Matrix n n P.R.BdR) (hN : N * N' = 1)
    (hg : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] P.R.BdR) * N.map (P.actQdR (g : GQ l)) = N)
    (h1 : ∀ i j, N i j ∈ fil0 P K) (h2 : ∀ i j, N' i j ∈ fil0 P K)
    (M M' : Matrix n n (Bst P)) (hM : M * M' = 1)
    (hMg : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] (Bst P)) * M.map (actSt P (g : GQ l)) = M) :
    (∀ i j k, P.ιB ((M i j).coeff k) ∈ fil0 P K) ∧ ∀ i j k, P.ιB ((M' i j).coeff k) ∈ fil0 P K := by
  obtain ⟨a1, a2⟩ := inverse_matrix_entries_mem_fil0 P K _ N N' hN hg h1 h2
  let E : ℕ → Bst P →+ P.R.BdR := fun k =>
    { toFun := fun p => eval₂ (P.ιB : P.R.B →+* P.R.BdR) U (derivative^[k] p)
      map_zero' := by simp
      map_add' := fun p q => by rw [iterate_map_add, eval₂_add] }
  have hE1 : ∀ k (c : ℚ_[l]) p, E k (algebraMap ℚ_[l] (Bst P) c * p) = algebraMap ℚ_[l] P.R.BdR c * E k p := by
    intro k c p
    change eval₂ _ U (derivative^[k] _) = _ * eval₂ _ U (derivative^[k] _)
    rw [Polynomial.algebraMap_apply, iterate_derivative_C_mul, eval₂_mul, eval₂_C]
    congr 1
    exact P.ιB.commutes c
  have hE2 : ∀ k (g : GQ l) p, E k (actSt P g p) = P.actQdR g (E k p) := by
    intro k g p
    change eval₂ _ U (derivative^[k] _) = P.actQdR g (eval₂ _ U (derivative^[k] _))
    rw [der_actSt, ev_actSt P U g (hU g)]
  refine ⟨fun i j => coeff_mem (fil0 P K) (P.ιB : P.R.B →+* P.R.BdR) U hU0 _ fun k => ?_,
    fun i j => coeff_mem (fil0 P K) (P.ιB : P.R.B →+* P.R.BdR) U hU0 _ fun k => ?_⟩
  · refine a1 (M.map (E k)) (fun g => ?_) i j
    ext i j
    conv_rhs => rw [← hMg g]
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hE1, hE2]
  · refine a2 (M'.map (E k)) (fun g => ?_) i j
    have h3 : M'.map (actSt P (g : GQ l)) = _ := inv_law (actSt P (g : GQ l) : Bst P →+* Bst P) hM (hMg g)
    ext i j
    have h4 := congrArg (E k) (congrFun (congrFun h3 i) j)
    rw [Matrix.map_apply, hE2] at h4
    rw [Matrix.map_apply, Matrix.map_apply, h4]
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [mul_comm, hE1, mul_comm]

end Mats

namespace UpperTheory.V.Loc

open GlobalTheory.Pst Polynomial

variable {l : ℕ} [Fact l.Prime]

private theorem evaluation_zero_frobenius (P : LocPrime l) (p : Bst P) : (phiSt P p).coeff 0 = P.φB (p.coeff 0) := by
  have : (constantCoeff : Bst P →+* P.R.B).comp (phiSt P : Bst P →+* Bst P) =
      (P.φB : P.R.B →+* P.R.B).comp constantCoeff := by
    refine Polynomial.ringHom_ext (fun b => ?_) ?_
    · simp
    · simp
  exact RingHom.congr_fun this p

private theorem evaluation_zero_galois_action_fil1 (P : LocPrime l) (K : FinExt l) (g : ↥(GK K)) (p : Bst P)
    (hp : ∀ k, P.ιB (p.coeff k) ∈ fil0 P K) :
    P.ιB ((actSt P (g : GQ l) p).coeff 0) - P.ιB (P.actQ (g : GQ l) (p.coeff 0)) ∈ (P.PD K).Fil 1 := by
  have e : actSt P (g : GQ l) p = (p.map (P.actQ (g : GQ l) : P.R.B →+* P.R.B)).comp
      (X + C ((kummer P (g : GQ l) : ℚ_[l]) • P.tB)) := stHom_apply P (P.actQ (g : GQ l)) _ p
  have ht : P.ιB ((kummer P (g : GQ l) : ℚ_[l]) • P.tB) ∈ (P.PD K).Fil 1 := by
    have h1 := (P.PD K).mem_filtration_one
    rw [P.PD_ι, P.period_datum_t_eq] at h1
    rw [map_smul]
    exact (((P.PD K).Fil 1).restrictScalars ℚ_[l]).smul_mem _ h1
  generalize (kummer P (g : GQ l) : ℚ_[l]) • P.tB = y at e ht
  have hy0 : P.ιB y ∈ fil0 P K := (P.PD K).Fil_anti 0 ht
  rw [e, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add, eval_eq_sum_range,
    Finset.sum_range_succ', map_add, pow_zero, mul_one, coeff_map]
  erw [add_sub_cancel_right]
  rw [map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [coeff_map, pow_succ, ← mul_assoc, map_mul, map_mul, map_pow]
  have h2 : P.ιB (P.actQ (g : GQ l) (p.coeff (k + 1))) ∈ fil0 P K := by
    rw [iota_act, ← P.PD_actdR K g]
    exact (P.PD K).Fil_G g 0 _ (hp _)
  have h3 := (P.PD K).Fil_mul 0 1 _ _ ((fil0 P K).mul_mem h2 ((fil0 P K).pow_mem hy0 k)) ht
  rwa [zero_add] at h3

private theorem eq_zero_of_mem_fil1 (P : LocPrime l) (K : FinExt l) (x : ℚ_[l])
    (hx : algebraMap ℚ_[l] P.R.BdR x ∈ (P.PD K).Fil 1) : x = 0 := by
  by_contra h0
  apply (P.PD K).not_mem_filtration_two
  have h1 := (P.PD K).Fil_mul 1 1 _ _ hx (P.PD K).mem_filtration_one
  have h2 := (((P.PD K).Fil (1 + 1)).restrictScalars ℚ_[l]).smul_mem x⁻¹ h1
  rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ h0, one_smul] at h2
  exact h2

private theorem st_inertia (K : FinExt l) {d : ℕ} (R : ↥(GK K) → Matrix (Fin d) (Fin d) ℚ_[l])
    (M M' : Matrix (Fin d) (Fin d) (Bst (PP l))) (hM : M * M' = 1)
    (hMg : ∀ g : ↥(GK K), (R g).map (algebraMap ℚ_[l] (Bst (PP l))) * M.map (actSt (PP l) (g : GQ l)) = M)
    (h1 : ∀ i j k, (PP l).ιB ((M i j).coeff k) ∈ fil0 (PP l) K)
    (h2 : ∀ i j k, (PP l).ιB ((M' i j).coeff k) ∈ fil0 (PP l) K)
    (g : ↥(GK K)) (hg : (g : GQ l) ∈ Iq l) : R g = 1 := by
  obtain ⟨hdom, hreg, -⟩ := stRegular l (PP l) (AIP l) (tiedP l)
  haveI := nontrivial_B (PP l)
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  have hinv : ∀ g : ↥(GK K), (M' * M.map (phiSt (PP l))).map (actSt (PP l) (g : GQ l)) =
      M' * M.map (phiSt (PP l)) := by
    intro g
    have h3 : M'.map (actSt (PP l) (g : GQ l)) = _ :=
      inv_law (actSt (PP l) (g : GQ l) : Bst (PP l) →+* Bst (PP l)) hM (hMg g)
    have h4 : ((R g).map (algebraMap ℚ_[l] (Bst (PP l)))).map (phiSt (PP l)) =
        (R g).map (algebraMap ℚ_[l] (Bst (PP l))) := by
      ext1 i j
      exact (phiSt (PP l)).commutes _
    have h5 : (M.map (phiSt (PP l))).map (actSt (PP l) (g : GQ l)) =
        (M.map (actSt (PP l) (g : GQ l))).map (phiSt (PP l)) := by
      ext1 i j
      exact (phiSt_actSt (PP l) _ _).symm
    rw [Matrix.map_mul, h3, Matrix.mul_assoc, h5, ← h4, ← Matrix.map_mul, hMg g]
  choose c hc hA using fun i j => hreg K 1 ((M' * M.map (phiSt (PP l))) i j) one_ne_zero fun g => by
    rw [map_one, one_mul, one_mul]
    exact congrFun (congrFun (hinv g) i) j
  let A : Matrix (Fin d) (Fin d) ↥(K0 K) := Matrix.of fun i j => ⟨c i j, hc i j, (c i j).2⟩
  let ev : Bst (PP l) →+* Bcr l := constantCoeff
  have hM0 : M.map ev * M'.map ev = 1 := by
    rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hM0' : M'.map ev * M.map ev = 1 := mul_eq_one_comm.1 hM0
  have hA' : A.map (algebraMap ↥(K0 K) (Bcr l)) = M'.map ev * (M.map ev).map (PP l).φB := by
    have e1 : (M.map ev).map (PP l).φB = (M.map (phiSt (PP l))).map ev := by
      ext1 i j
      exact (evaluation_zero_frobenius (PP l) _).symm
    rw [e1, ← Matrix.map_mul]
    ext1 i j
    rw [Matrix.map_apply, Matrix.map_apply, hA i j, mul_one, Polynomial.algebraMap_apply]
    exact (coeff_C_zero (R := Bcr l)).symm
  have hdet : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h3 : (A.map (algebraMap ↥(K0 K) (Bcr l))).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    have h4 : (M'.map ev * (M.map ev).map (PP l).φB) * ((M'.map ev).map (PP l).φB * M.map ev) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((M.map ev).map (PP l).φB), ← Matrix.map_mul, hM0,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, hM0']
    have h5 := congrArg Matrix.det h4
    rw [Matrix.det_mul, ← hA', h3, zero_mul, Matrix.det_one] at h5
    exact zero_ne_one h5
  have hfix := wt_matFix K (M.map ev) (M'.map ev) A hM0
    (fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (h1 i j 0)) (fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (h2 i j 0))
    hdet (by rw [hA', ← Matrix.mul_assoc, hM0, Matrix.one_mul]) _ hg
  let ι : Bcr l →+* Bdr l := ((PP l).ιB : Bcr l →+* Bdr l)
  let Z := ((M.map (actSt (PP l) (g : GQ l))).map ev).map ι
  let Y := (M.map ev).map ι
  let Y' := (M'.map ev).map ι
  let S := (R g).map (algebraMap ℚ_[l] (Bdr l))
  have hYY : Y * Y' = 1 := by
    rw [← Matrix.map_mul, hM0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hSZ : S * Z = Y := by
    have e1 : S = (((R g).map (algebraMap ℚ_[l] (Bst (PP l)))).map ev).map ι := by
      ext1 i j
      simp only [S, Matrix.map_apply, Polynomial.algebraMap_apply, ev, constantCoeff_apply, coeff_C_zero]
      exact ((PP l).ιB.commutes _).symm
    rw [e1, ← Matrix.map_mul, ← Matrix.map_mul, hMg g]
  have hZY : ∀ i j, (Z - Y) i j ∈ ((PP l).PD K).Fil 1 := by
    intro i j
    have e1 := evaluation_zero_galois_action_fil1 (PP l) K g (M i j) (h1 i j)
    have e2 : (PP l).actQ (g : GQ l) ((M i j).coeff 0) = (M i j).coeff 0 := congrFun (congrFun hfix i) j
    rw [e2] at e1
    exact e1
  have e3 : 1 - S = S * (Z - Y) * Y' := by
    rw [Matrix.mul_sub, hSZ, Matrix.sub_mul, hYY, Matrix.mul_assoc, hYY, Matrix.mul_one]
  have e4 : ∀ i j, (1 - S) i j ∈ ((PP l).PD K).Fil 1 := by
    intro i j
    rw [e3, Matrix.mul_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Submodule.sum_mem _ fun m _ => ?_
    have h3 := ((PP l).PD K).Fil_mul _ _ _ _ (((PP l).PD K).Fil_mul 0 1 _ _
      ((fil0 (PP l) K).algebraMap_mem (R g i m)) (hZY m k)) (show _ ∈ ((PP l).PD K).Fil 0 from h2 k j 0)
    rw [zero_add, add_zero] at h3
    exact h3
  symm
  rw [← sub_eq_zero]
  ext i j
  apply eq_zero_of_mem_fil1 (PP l) K
  have e5 : (1 - S) = (1 - R g).map (algebraMap ℚ_[l] (Bdr l)) := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  have := e4 i j
  rw [e5] at this
  exact this

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.drWt0 :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → IsDr φ ρ → FilD φ ρ 0 = Ddr φ ρ → FilD φ ρ 1 = ⊥ → ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g ∈ U, φ g ∈ Iq l → ρ g = 1 := by
  intro hP l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ hcont hdr h0 h1
  obtain ⟨K, e, -, hec, he, -, hidx, -⟩ := openField φ hφ
  have he' : ∀ x, ((e x : ↥(GK K)) : GQ l) = φ x := fun x => DFunLike.congr_fun he x
  let ρ' : Representation ℚ_[l] ↥(GK K) V := (resCoef ℚ_[l] ρ).comp e.symm.toMonoidHom
  have hD : ∀ x y, actVdR ((PP l).PD K) ρ' (e x) y = actD φ ρ x y := by
    intro x y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b =>
      change ρ (e.symm (e x)) v ⊗ₜ[ℚ_[l]] ((PP l).PD K).actdR (e x) b = ρ x v ⊗ₜ[ℚ_[l]] (PP l).actQdR (φ x) b
      rw [(PP l).PD_actdR, he', e.symm_apply_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hD' : ∀ x y, actD φ (resCoef ℚ_[l] ρ) x y = actD φ ρ x y := by
    intro x y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  have hDD : ∀ y, y ∈ DdR ((PP l).PD K) ρ' ↔ y ∈ Ddr φ ρ := by
    intro y
    simp only [DdR, Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      e.surjective.forall, hD]
  have hC : DdR ((PP l).PD K) ρ' = Ddr φ (resCoef ℚ_[l] ρ) := by
    ext y
    simp only [DdR, Ddr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      e.surjective.forall, hD, hD']
  have hFil : ∀ a, (((PP l).PD K).Fil a).restrictScalars ℚ_[l] =
      (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] := fun a =>
    SetLike.coe_injective ((PP l).PD_Fil K (botExt l) a)
  have hF : ∀ a y, y ∈ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a ↔ y ∈ FilT A V a := by
    intro a y
    unfold FilV FilT
    rw [hFil]
    exact Iff.rfl
  have hDR : IsDR ((PP l).PD K) ρ' := by
    unfold IsDR
    rw [hC, ← hidx]
    exact hdr
  have hpst := hP l (PP l) (AIP l) (tiedP l) K V ρ'
    (fun v => hcont.comp (hec.prodMk continuous_const)) hDR
  obtain ⟨T⟩ := tiedP l
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l _ _ T
  let b := Module.finBasis ℚ_[l] V
  obtain ⟨N, N', hN, hNg⟩ := drMat ((PP l).PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ' b hDR
  obtain ⟨n1, n2⟩ := core ((PP l).PD K) ρ' b (GlobalTheory.DRFil.graded_inv Θ K) (GlobalTheory.DRFil.graded_invariants T Θ K)
    (fun y hy => (hF 0 y).2 ((h0.ge ((hDD y).1 hy)).2))
    (eq_bot_iff.2 fun y hy => h1.le ⟨(hDD y).1 hy.1, (hF 1 y).1 hy.2⟩) N N' hN hNg
  obtain ⟨K', hK, M, M', hM, hMg⟩ := stMat T K ρ' b hpst
  obtain ⟨U, hU0, hU⟩ := exists_log l (PP l) (AIP l) T K'
  obtain ⟨c1, c2⟩ := coeff_mem_fil0_of_invertible_period (PP l) K' U hU0 hU (fun g => LinearMap.toMatrix b b (ρ' ⟨g, GK_le hK g.2⟩))
    N N' hN (fun g => by
      have e1 : N.map ((PP l).actQdR (g : GQ l)) = N.map (((PP l).PD K).actdR ⟨g, GK_le hK g.2⟩) := by
        ext1 i j
        exact ((PP l).PD_actdR K ⟨g, GK_le hK g.2⟩ _).symm
      rw [e1, hNg])
    (fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (n1 i j)) (fun i j => (GlobalTheory.DRFil.fil_iff K _ _ _).1 (n2 i j))
    M M' hM hMg
  haveI := K'.2
  refine ⟨(GK K').comap φ, (IntermediateField.fixingSubgroup_isOpen K'.1).preimage hφ.continuous,
    fun g hg hI => ?_⟩
  have h4 := st_inertia K' _ M M' hM hMg c1 c2 ⟨φ g, hg⟩ hI
  have h3 : (⟨φ g, GK_le hK hg⟩ : ↥(GK K)) = e g := Subtype.ext (he' g).symm
  change LinearMap.toMatrix b b (ρ' ⟨φ g, GK_le hK hg⟩) = 1 at h4
  rw [h3, ← LinearMap.toMatrix_one b] at h4
  have h5 := (LinearMap.toMatrix b b).injective h4
  ext v
  have h6 : ρ (e.symm (e g)) v = v := LinearMap.congr_fun h5 v
  rwa [e.symm_apply_apply] at h6
