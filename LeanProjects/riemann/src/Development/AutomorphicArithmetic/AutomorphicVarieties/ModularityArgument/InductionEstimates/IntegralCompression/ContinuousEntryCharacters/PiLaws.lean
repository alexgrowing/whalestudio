import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.CoLaws

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

private theorem T_cont (n : ℕ) (q : ℤ) : Continuous (T n q) :=
  continuous_const.mul (KT.continuous_conj_psi n q n)

private theorem T_inv (n : ℕ) (q : ℤ) (k : U2) : T n q k⁻¹ = conj (T n q k) := by
  simp only [T, KT.psi_self_inv, map_mul, map_inv₀, Complex.conj_ofReal, starRingEnd_self_apply]

private theorem T_idem (n : ℕ) (q : ℤ) (k : U2) : ∫ h, T n q h * T n q (h⁻¹ * k) ∂μK = T n q k := by
  have hc := KT.collapse (H := ℂ) n q (fun i => conj (KT.psi n q i k))
  have e : ∀ h, T n q h * T n q (h⁻¹ * k) = ((KT.normSqInt n q : ℂ))⁻¹ * (((KT.normSqInt n q : ℂ))⁻¹ *
      (conj (KT.psi n q n h) • ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℂ) * KT.psi n q i h) • conj (KT.psi n q i k))) := by
    intro h
    simp only [T, KT.psi_inv_mul, map_sum, map_mul, map_natCast, starRingEnd_self_apply, smul_eq_mul]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_const_mul]
  simp only [smul_eq_mul] at hc ⊢
  rw [hc]
  rfl

private theorem int_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {ι : Type} [Fintype ι]
    (j : ι) {G : (ι → U2) → E} (hG : Continuous G) :
    ∫ m, G m ∂(Measure.pi fun _ : ι => μK) =
      ∫ m, ∫ u, G (Function.update m j u) ∂μK ∂(Measure.pi fun _ : ι => μK) := by
  have h1 : ∀ u : U2, ∫ m, G (m * Pi.mulSingle j u) ∂(Measure.pi fun _ : ι => μK) = ∫ m, G m ∂(Measure.pi fun _ : ι => μK) :=
    fun u => integral_mul_right_eq_self G _
  have h2 : ∫ m, G m ∂(Measure.pi fun _ : ι => μK) =
      ∫ u, ∫ m, G (m * Pi.mulSingle j u) ∂(Measure.pi fun _ : ι => μK) ∂μK := by
    simp only [h1, integral_const, probReal_univ, one_smul]
  rw [h2, integral_integral_swap]
  · congr 1; funext m
    rw [← integral_mul_left_K (fun u => G (Function.update m j u)) (m j)]
    congr 1; funext u; congr 1
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [hi]
  · refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    exact hG.comp (continuous_snd.mul ((continuous_mulSingle j).comp continuous_fst))

section

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {ι : Type} [Fintype ι] (C : Co K ι)

private noncomputable def glH (i : ι) : GL2C →* G1 K 2 :=
  MonoidHom.mk' (fun g => C.gl i g.1) fun a b => (coLaws K ι C).2.2.2.2.1 i a.1 b.1

private theorem glH_cont (i : ι) : Continuous (glH C i) :=
  ((coLaws K ι C).2.2.2.1 i).comp continuous_subtype_val

private theorem continuous_arch_compact_inclusion : Continuous (arc1 : archCompact K 2 → G1 K 2) :=
  continuous_archP.comp continuous_subtype_val

private theorem int_κ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : archCompact K 2 → E) :
    ∫ k, f k ∂C.κ₂ = ∫ m, f ((C.Φ 2).symm m) ∂(Measure.pi fun _ : ι => μK) :=
  (C.Φ 2).symm.toHomeomorph.measurableEmbedding.integral_map f

private theorem idemA (n : ι → ℕ) (q : ι → ℤ) : IdemA C.κ₂ (C.p n q) where
  haar := (coLaws K ι C).1
  cont := continuous_finset_prod _ fun i _ => (T_cont _ _).comp ((continuous_apply i).comp (C.Φ 2).continuous)
  star k := by simp only [Co.p, map_inv, Pi.inv_apply, T_inv, map_prod]
  idem k := by
    rw [int_κ]
    have e : ∀ m : ι → U2, C.p n q ((C.Φ 2).symm m) * C.p n q (((C.Φ 2).symm m)⁻¹ * k) =
        ∏ i, (T (n i) (q i) (m i) * T (n i) (q i) ((m i)⁻¹ * C.Φ 2 k i)) := by
      intro m
      simp only [Co.p, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply, Pi.mul_apply, Pi.inv_apply, Finset.prod_mul_distrib]
    simp_rw [e]
    rw [integral_fintype_prod_eq_prod (fun i x => T (n i) (q i) x * T (n i) (q i) (x⁻¹ * C.Φ 2 k i))]
    simp only [T_idem]
    rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : UnitaryRep (G1 K 2) H)

private noncomputable def PiH (i : ι) (n : ℕ) (q : ℤ) (v : H) : H := ∫ m, T n q m • ρ (C.un i m) v ∂μK

private noncomputable def sg (i : ι) : UnitaryRep GL2C H := ρ.compHom (glH C i) (glH_cont C i)

private theorem sg_apply (i : ι) (g : GL2C) (v : H) : sg C ρ i g v = ρ (C.gl i g.1) v := rfl

private theorem sg_kC (i : ι) (m : U2) (v : H) : sg C ρ i (kC m) v = ρ (C.un i m) v := by
  rw [sg_apply, (coLaws K ι C).2.2.1 i m]

private theorem PiH_eq (i : ι) (n : ℕ) (q : ℤ) (v : H) : PiH C ρ i n q v = KT.P (sg C ρ i) n q v := by
  simp only [PiH, KT.P, KT.Q, KT.Kint, T, mul_smul, sg_kC]
  rw [integral_smul]

private theorem PiH_int (i : ι) (n : ℕ) (q : ℤ) (v : H) :
    Integrable (fun m => T n q m • ρ (C.un i m) v) μK := by
  refine KT.integrable_of_continuous ((T_cont n q).smul ?_)
  simp only [← sg_kC]
  exact KT.continuous_orbit_K (sg C ρ i) v

private theorem PiH_mem (i : ι) (n : ℕ) (q : ℤ) (τ : Submodule ℂ H) (hc : IsClosed (τ : Set H))
    (hi : ∀ g, ∀ v ∈ τ, ρ g v ∈ τ) (v : H) (hv : v ∈ τ) : PiH C ρ i n q v ∈ τ :=
  Convex.integral_mem (τ.restrictScalars ℝ).convex hc
    (Eventually.of_forall fun m => τ.smul_mem _ (hi _ _ hv)) (PiH_int C ρ i n q v)

private theorem PiH_comm (i : ι) (n : ℕ) (q : ℤ) (h : G1 K 2) (hh : ∀ b, Commute h (C.gl i b)) (v : H) :
    PiH C ρ i n q (ρ h v) = ρ h (PiH C ρ i n q v) := by
  simp only [PiH]
  rw [← ContinuousLinearMap.integral_comp_comm _ (PiH_int C ρ i n q v)]
  congr 1; funext m
  rw [map_smul, ← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, (coLaws K ι C).2.2.1 i m, (hh _).eq]

private theorem part1 (i : ι) (n : ℕ) (q : ℤ) : ∃ P : H →L[ℂ] H, (∀ v, P v = PiH C ρ i n q v) ∧ IsSelfAdjoint P ∧ P ∘L P = P ∧
        (∀ a b, Commute (P ∘L ρ (C.gl i a) ∘L P) (P ∘L ρ (C.gl i b) ∘L P)) ∧
        (∀ h : G1 K 2, (∀ b, Commute h (C.gl i b)) → Commute P (ρ h)) ∧
        ∀ τ : Submodule ℂ H, IsClosed (τ : Set H) → (∀ g, ∀ v ∈ τ, ρ g v ∈ τ) → ∀ v ∈ τ, P v ∈ τ := by
  have hP : ∀ v, KT.PL (sg C ρ i) n q v = PiH C ρ i n q v := fun v => (PiH_eq C ρ i n q v).symm
  refine ⟨KT.PL (sg C ρ i) n q, hP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    exact KT.inner_P_left (sg C ρ i) n q x y
  · ext1 v
    exact KT.P_P (sg C ρ i) n q v
  · intro a b
    ext1 v
    have key := congrArg (fun T => ((T ⟨KT.P (sg C ρ i) n q v, KT.P_mem_alt _ n q v⟩ : KT.W (sg C ρ i) n q) : H))
      (KT.compr_comm (sg C ρ i) n q ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)
    simp only [ContinuousLinearMap.mul_apply, KT.coe_compr_apply, sg_apply] at key
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, KT.PL_apply, KT.P_P]
    simpa only [KT.P_P, sg_apply] using key
  · intro h hh
    ext1 v
    simp only [ContinuousLinearMap.mul_apply, hP]
    exact PiH_comm C ρ i n q h hh v
  · intro τ hc hi v hv
    rw [hP]
    exact PiH_mem C ρ i n q τ hc hi v hv

private theorem part4 (i : ι) (v : H) (hv : ∀ n q g, PiH C ρ i n q (ρ g v) = 0) : v = 0 := by
  let Wd : Submodule ℂ H :=
    { carrier := {y | ∀ (n : ℕ) (q : ℤ) (g : G1 K 2), KT.P (sg C ρ i) n q (ρ g y) = 0}
      add_mem' := fun {x y} hx hy n q g => by rw [map_add, KT.P_add, hx, hy, add_zero]
      zero_mem' := fun n q g => by rw [map_zero]; simpa using KT.P_smul (sg C ρ i) n q 0 0
      smul_mem' := fun c x hx n q g => by rw [map_smul, KT.P_smul, hx, smul_zero] }
  have hcl : IsClosed (Wd : Set H) := by
    have : (Wd : Set H) = ⋂ (n : ℕ) (q : ℤ) (g : G1 K 2), {y | KT.PL (sg C ρ i) n q (ρ g y) = 0} := by
      ext y; simp [Wd]
    rw [this]
    exact isClosed_iInter fun n => isClosed_iInter fun q => isClosed_iInter fun g =>
      isClosed_eq ((KT.PL (sg C ρ i) n q).continuous.comp (ρ g).continuous) continuous_const
  haveI : CompleteSpace Wd := hcl.completeSpace_coe
  have hinv : ρ.IsInvariant Wd := fun g y hy n q g' => by
    rw [← UnitaryRep.map_mul_apply]; exact hy n q (g' * g)
  let σ' : UnitaryRep GL2C Wd := (ρ.restrict Wd hinv).compHom (glH C i) (glH_cont C i)
  have hQ : ∀ (n : ℕ) (q : ℤ) (y : Wd), KT.Q σ' n q n y = 0 := by
    intro n q y
    apply Subtype.ext
    have h1 : ((KT.Q σ' n q n y : Wd) : H) = KT.Q (sg C ρ i) n q n (y : H) := by
      simp only [KT.Q, KT.Kint]
      exact (ContinuousLinearMap.integral_comp_comm Wd.subtypeL (KT.integrable_Kint σ' (KT.continuous_conj_psi n q n) y)).symm
    have h2 := y.2 n q 1
    rw [UnitaryRep.map_one_apply, KT.P] at h2
    have hne : ((KT.normSqInt n q : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (KT.normSqInt_pos n q).ne')
    rw [h1, (smul_eq_zero.1 h2).resolve_left hne]
    rfl
  have hvW : v ∈ Wd := fun n q g => by rw [← PiH_eq]; exact hv n q g
  exact congrArg Subtype.val (KT.eq_zero_of_forall_Q_eq_zero σ' hQ ⟨v, hvW⟩)

variable (n : ι → ℕ) (q : ι → ℤ)

private theorem arch_compact_inclusion_mul (a b : archCompact K 2) : (arc1 (a * b) : G1 K 2) = arc1 a * arc1 b :=
  map_mul (archP K 2) _ _

private noncomputable def pH (e : archCompact K 2 → ℂ) (v : H) : H := ∫ k, e k • ρ (arc1 k) v ∂C.κ₂

private noncomputable def cS (S : Finset ι) (m : ι → U2) : archCompact K 2 := (C.Φ 2).symm (S.piecewise m 1)

private noncomputable def wS (S : Finset ι) (v : H) (m : ι → U2) : H :=
  (∏ i ∈ S, T (n i) (q i) (m i)) • ρ (arc1 (cS C S m)) v

private theorem cS_cont (S : Finset ι) : Continuous (cS C S) :=
  (C.Φ 2).symm.continuous.comp (continuous_pi fun i => by
    by_cases hi : i ∈ S
    · simpa [Finset.piecewise, hi] using continuous_apply i
    · simpa [Finset.piecewise, hi] using continuous_const)

private theorem wS_cont (S : Finset ι) (v : H) : Continuous (wS C ρ n q S v) :=
  (continuous_finset_prod _ fun i _ => (T_cont _ _).comp (continuous_apply i)).smul
    ((ρ.continuous_orbit v).comp (continuous_arch_compact_inclusion.comp (cS_cont C S)))

private noncomputable def AS (S : Finset ι) (v : H) : H := ∫ m, wS C ρ n q S v m ∂(Measure.pi fun _ : ι => μK)

private theorem AS_empty (v : H) : AS C ρ n q ∅ v = v := by
  have : ∀ m, wS C ρ n q ∅ v m = v := by
    intro m
    have h1 : cS C ∅ m = 1 := by
      rw [cS, Finset.piecewise_empty]; exact map_one (C.Φ 2).symm
    have h2 : (arc1 (1 : archCompact K 2) : G1 K 2) = 1 := map_one (archP K 2)
    rw [wS, h1, h2, Finset.prod_empty, one_smul, UnitaryRep.map_one_apply]
  simp only [AS, this, integral_const, probReal_univ, one_smul]

private theorem cS_insert {S : Finset ι} {j : ι} (hj : j ∉ S) (u : U2) (m : ι → U2) :
    cS C (insert j S) (Function.update m j u) = (C.Φ 2).symm (Pi.mulSingle j u) * cS C S m := by
  rw [cS, cS, ← map_mul]
  congr 1
  funext i
  by_cases hi : i = j
  · subst hi; simp [Finset.piecewise, hj]
  · by_cases hs : i ∈ S <;> simp [Finset.piecewise, hi, hs]

private theorem AS_insert {S : Finset ι} {j : ι} (hj : j ∉ S) (v : H) :
    AS C ρ n q (insert j S) v = PiH C ρ j (n j) (q j) (AS C ρ n q S v) := by
  have e : ∀ m, ∫ u, wS C ρ n q (insert j S) v (Function.update m j u) ∂μK =
      KT.PL (sg C ρ j) (n j) (q j) (wS C ρ n q S v m) := by
    intro m
    rw [KT.PL_apply, ← PiH_eq, PiH]
    congr 1; funext u
    have hp : ∏ i ∈ S, T (n i) (q i) (Function.update m j u i) = ∏ i ∈ S, T (n i) (q i) (m i) :=
      Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
    rw [wS, wS, Finset.prod_insert hj, Function.update_self, cS_insert C hj, hp, arch_compact_inclusion_mul, UnitaryRep.map_mul_apply,
      mul_smul, map_smul]
    rfl
  simp only [AS]
  rw [int_update j (wS_cont C ρ n q _ v)]
  simp_rw [e]
  rw [ContinuousLinearMap.integral_comp_comm _
    ((wS_cont C ρ n q S v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), KT.PL_apply, ← PiH_eq]

private theorem AS_univ (v : H) : AS C ρ n q Finset.univ v = pH C ρ (C.p n q) v := by
  rw [pH, int_κ, AS]
  congr 1; funext m
  simp only [wS, cS, Co.p, Finset.piecewise_univ, ContinuousMulEquiv.apply_symm_apply]

private theorem part2 (v : H) : pH C ρ (C.p n q) v = v ↔ ∀ i, PiH C ρ i (n i) (q i) v = v := by
  constructor
  · intro h j
    have h1 : AS C ρ n q Finset.univ v = PiH C ρ j (n j) (q j) (AS C ρ n q (Finset.univ.erase j) v) := by
      rw [← AS_insert C ρ n q (Finset.notMem_erase j _), Finset.insert_erase (Finset.mem_univ j)]
    rw [AS_univ, h] at h1
    have h2 : ∀ x, PiH C ρ j (n j) (q j) (PiH C ρ j (n j) (q j) x) = PiH C ρ j (n j) (q j) x := fun x => by
      simp only [PiH_eq]; exact KT.P_P _ _ _ x
    exact (congrArg _ h1).trans ((h2 _).trans h1.symm)
  · intro h
    have : ∀ S : Finset ι, AS C ρ n q S v = v := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact AS_empty C ρ n q v
      | insert j S hj ih => rw [AS_insert C ρ n q hj, ih, h]
    rw [← AS_univ, this]

end

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.piLaws :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι) (μ : Measure (G1 K 2)) [μ.IsHaarMeasure], (∀ i n q, ∃ P : LL μ →L[ℂ] LL μ, (∀ v, P v = C.Pi μ i n q v) ∧ IsSelfAdjoint P ∧ P ∘L P = P ∧
        (∀ a b, Commute (P ∘L rightRegularRep (Gam K 2) μ (C.gl i a) ∘L P) (P ∘L rightRegularRep (Gam K 2) μ (C.gl i b) ∘L P)) ∧
        (∀ h : G1 K 2, (∀ b, Commute h (C.gl i b)) → Commute P (rightRegularRep (Gam K 2) μ h)) ∧
        ∀ τ : Submodule ℂ (LL μ), CuspIrr μ τ → ∀ v ∈ τ, P v ∈ τ) ∧
      (∀ n q v, pOp μ C.κ₂ (C.p n q) v = v ↔ ∀ i, C.Pi μ i (n i) (q i) v = v) ∧ (∀ n q, IdemA C.κ₂ (C.p n q)) ∧
      ∀ i (v : LL μ), (∀ n q (g : G1 K 2), C.Pi μ i n q (rightRegularRep (Gam K 2) μ g v) = 0) → v = 0 := by
  intro K _ _ _ ι _ C μ _
  refine ⟨fun i n q => ?_, fun n q v => part2 C (rightRegularRep (Gam K 2) μ) n q v, fun n q => idemA C n q,
    fun i v hv => part4 C (rightRegularRep (Gam K 2) μ) i v hv⟩
  obtain ⟨P, h1, h2, h3, h4, h5, h6⟩ := part1 C (rightRegularRep (Gam K 2) μ) i n q
  exact ⟨P, h1, h2, h3, h4, h5, fun τ hτ v hv => h6 τ hτ.closed hτ.inv v hv⟩
