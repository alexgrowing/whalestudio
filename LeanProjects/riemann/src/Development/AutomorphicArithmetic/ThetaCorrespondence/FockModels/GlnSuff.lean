import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientHeckeDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableOfHeckeSpectral

open Filter Topology MeasureTheory GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel GlobalTheory.CompanionTheory.CoeffBound

namespace UpperTheory.Lit.Cas

def HeckeWeak {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ j : ℕ, 0 < j → j < N → ∀ T : Module.End ℂ (fixed π (Zls.Km k N m)),
    Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N j)) T → ∀ μ : ℂ, T.HasEigenvalue μ →
      ‖μ‖ ≤ (Nat.card 𝓀[k] : ℝ) ^ (-(((j * (N - j) : ℕ) : ℝ) / 2))

theorem exists_radius_rpow {q p : ℝ} (hq : 1 < q) (hp : 2 < p) (a : ℕ) (ha : 0 < a) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ q ^ (-((a : ℝ) / 2)) < ρ ∧ q ^ a * ρ ^ p < 1 := by
  have hq0 : 0 < q := by linarith
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hs : (0 : ℝ) < (2 + p) / 2 := by linarith
  refine ⟨q ^ (-((a : ℝ) / ((2 + p) / 2))), (Real.rpow_pos_of_pos hq0 _).le, ?_, ?_⟩
  · refine Real.rpow_lt_rpow_of_exponent_lt hq (neg_lt_neg ?_)
    exact div_lt_div_of_pos_left ha' (by norm_num) (by linarith)
  · rw [← Real.rpow_mul hq0.le, ← Real.rpow_natCast, ← Real.rpow_add hq0]
    refine Real.rpow_lt_one_of_one_lt_of_neg hq ?_
    have : (a : ℝ) < (a : ℝ) / ((2 + p) / 2) * p := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hs]
      exact mul_lt_mul_of_pos_left (by linarith) ha'
    linarith

theorem norm_le_of_norm_mul_cpow_le (q e : ℕ) (hq : 0 < q) (μ : ℂ)
    (h : ‖μ * (q : ℂ) ^ ((e : ℂ) / 2)‖ ≤ 1) : ‖μ‖ ≤ (q : ℝ) ^ (-((e : ℝ) / 2)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hre : (((e : ℂ) / 2)).re = (e : ℝ) / 2 := by
    have : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, hre] at h
  have hp : 0 < (q : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_pos_of_pos hq' _
  rw [Real.rpow_neg hq'.le, ← one_div, le_div_iff₀ hp]
  exact h

theorem heckeWeak_of_maxExpWeak (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hM : MaxExpWeak π) : HeckeWeak π := by
  intro m hm j hj hjN T hT μ hμ
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  by_cases hμ0 : μ = 0
  · subst hμ0
    simpa using (Real.rpow_pos_of_pos (by exact_mod_cast hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ)) _).le
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  let d : Fin 2 → ℕ := ![j, N - j]
  have hd : ∑ a, d a = N := by
    simp only [d, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have d0 : d 0 = j := rfl
  have d1 : d 1 = N - j := rfl
  have hd0 : 0 < d 0 := hj
  have hd1 : 0 < d 1 := by rw [d1]; omega
  have hT' : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T := hT
  have hTw : T w = μ • w := hw.apply_eq_smul
  have hmk : (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := GlobalTheory.T.hecke_operator_jacquet_eigen_left k N V π hs m hm d hd hd0 hd1 T hT' w h0
    rw [hw.pow_apply r] at hr
    exact (smul_ne_zero (pow_ne_zero r hμ0) hw.2) hr
  have hjac := GlobalTheory.T.hecke_operator_jacquet_eigen_right k N V π hs m hm d hd hd0 hd1 T hT' w
  have heig : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (w : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) := by
    rw [← hjac, hTw]
    rfl
  obtain ⟨x, hx, hxd, hjm, hs0, c1, hs1⟩ :=
    GlobalTheory.T.jacquet_quotient_eigenvector k N V π hs hi hA hF d hd hd0 hd1 μ w hmk heig
  have hpos : ∀ a, 0 < (x a).1 := by
    intro a
    rw [hxd a]
    fin_cases a
    · exact hd0
    · exact hd1
  have hE := hM x hx hpos hjm
  have hc := (hE (Zls.unifU k) (GlobalTheory.T.uniformizer_pow_tendsto_zero k)
    ![μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2), c1]
    (by
      intro i
      fin_cases i
      · exact hs0
      · exact hs1)).1 0 (by simp)
  have hfil : Finset.univ.filter (· ≤ (0 : Fin 2)) = {0} := by decide
  rw [hfil, Finset.prod_singleton] at hc
  have := norm_le_of_norm_mul_cpow_le (Nat.card 𝓀[k]) (d 0 * d 1) hq μ hc
  simpa [d0, d1] using this

theorem coeff_bound_rpow (p : ℝ) (hp : 2 < p) : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → IsAdmissible π → HeckeWeak π → ∀ m : ℕ, 1 ≤ m → ∀ v ∈ fixed π (Zls.Km k N m), ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧ (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ p < 1) ∧ ∀ g : Fin (N - 1) → ℕ, ‖l (π (Zls.diagPow k N (Zls.lamOf g)) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
  intro k _ _ _ _ N V _ _ π hsm hadm hsp m hm v hv l hl
  have hfd : FiniteDimensional ℂ (fixed π (Zls.Km k N m)) :=
    hadm.2 _ (GlobalTheory.CompanionTheory.KmTop.isOpen_Km N m) (GlobalTheory.CompanionTheory.KmTop.isCompact_Km N m)
  have hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ) := by
    exact_mod_cast Nat.card_pos
  obtain ⟨d, e, φ, hφ, hev⟩ := exists_coordinates (fixed π (Zls.Km k N m))
  choose T hT using fun j : Fin (N - 1) =>
    GlobalTheory.CompanionTheory.HeckeKm.exists_isHeckeOp k N V π hsm m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1)))
  have hq1 : (1 : ℝ) < (Nat.card 𝓀[k] : ℝ) := by
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[k])
  have hrad := fun j : Fin (N - 1) => exists_radius_rpow hq1 hp (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))
    (Nat.mul_pos (by omega) (by omega))
  choose ρ hρ0 hρb hρp using hrad
  have hρe : ∀ (j : Fin (N - 1)) (μ : ℂ), (T j).HasEigenvalue μ → ‖μ‖ < ρ j := fun j μ hμ =>
    (hsp m hm ((j : ℕ) + 1) (by omega) (by omega) (T j) (hT j) μ hμ).trans_lt (hρb j)
  have hC := fun j : Fin (N - 1) => GlobalTheory.CompanionTheory.SpecBound.norm_pow_le_of_eigenvalues_lt (Fin d → ℂ) (φ (T j)) (ρ j)
    (fun μ hμ => hρe j μ (hev _ _ hμ))
  choose C hC using hC
  have hprod : ∀ (g : Fin (N - 1) → ℕ) (s : Finset (Fin (N - 1))),
      ∃ S : Module.End ℂ (fixed π (Zls.Km k N m)),
        Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf fun j => if j ∈ s then g j else 0)) S ∧
        ‖φ S‖ ≤ ∏ j ∈ s, C j * ρ j ^ g j := by
    classical
    intro g s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_, ?_⟩
      · have h0 : (fun j : Fin (N - 1) => if j ∈ (∅ : Finset (Fin (N - 1))) then g j else 0) = 0 := by
          funext j; simp
        rw [h0, lamOf_zero, diagPow_zero]
        intro v l _
        simp
      · rw [map_one, Finset.prod_empty]
        exact ContinuousLinearMap.norm_id_le
    | insert a s ha ih =>
      obtain ⟨S, hS, hn⟩ := ih
      refine ⟨T a ^ g a * S, ?_, ?_⟩
      · have hsplit : (fun j : Fin (N - 1) => if j ∈ insert a s then g j else 0) =
            (Pi.single a (g a) : Fin (N - 1) → ℕ) + fun j => if j ∈ s then g j else 0 := by
          funext j
          by_cases hj : j = a
          · subst hj
            simp [ha]
          · simp [hj]
        rw [hsplit, (GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1]
        exact GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _
          (hecke_pow π hsm hm a (T a) (hT a) (g a)) hS
      · rw [map_mul, map_pow, Finset.prod_insert ha]
        exact (norm_mul_le _ _).trans (mul_le_mul (hC a (g a)) hn (norm_nonneg _)
          ((norm_nonneg _).trans (hC a (g a))))
  let L : (Fin d → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (l ∘ₗ (fixed π (Zls.Km k N m)).subtype ∘ₗ (e.symm : (Fin d → ℂ) →ₗ[ℂ] _))
  let w : Fin d → ℂ := e ⟨v, hv⟩
  refine ⟨‖L‖ * ‖w‖ * ∏ j, C j, ρ, hρ0, fun j => ?_, fun g => ?_⟩
  · exact hρp j
  · obtain ⟨S, hS, hn⟩ := hprod g Finset.univ
    have hg : (fun j : Fin (N - 1) => if j ∈ (Finset.univ : Finset (Fin (N - 1))) then g j else 0) = g := by
      funext j; simp
    rw [hg] at hS
    have h1 : l (π (Zls.diagPow k N (Zls.lamOf g)) v) = L (φ S w) := by
      rw [show π (Zls.diagPow k N (Zls.lamOf g)) v = π (Zls.diagPow k N (Zls.lamOf g)) ((⟨v, hv⟩ : fixed π (Zls.Km k N m)) : V) from rfl,
        hS ⟨v, hv⟩ l hl, hφ]
      simp [L]
    rw [h1, Finset.prod_mul_distrib] at *
    calc ‖L (φ S w)‖ ≤ ‖L‖ * ‖φ S w‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖φ S‖ * ‖w‖) := by gcongr; exact (φ S).le_opNorm _
      _ ≤ ‖L‖ * ((∏ j, C j) * (∏ j, ρ j ^ g j) * ‖w‖) := by gcongr
      _ = ‖L‖ * ‖w‖ * (∏ j, C j) * ∏ j, ρ j ^ g j := by ring

theorem lintegral_rpow_lt_top_of_cover {p : ℝ} (hp : 0 ≤ p) {X ι κ : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ) [Finite ι]
    [Countable κ] (A : ι → κ → Set X) (hcov : ∀ x, ∃ i j, x ∈ A i j) (b w : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hb : ∀ i j, 0 ≤ b i j)
    (E : ENNReal) (hE : E < ⊤) (hF : ∀ i j, ∀ x ∈ A i j, ‖F x‖ ≤ b i j)
    (hμ : ∀ i j, μ (A i j) ≤ ENNReal.ofReal (w i j) * E)
    (hsum : ∀ i, Summable fun j => b i j ^ p * w i j) :
    ∫⁻ x, ‖F x‖ₑ ^ p ∂μ < ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have hu : (⋃ r : ι × κ, A r.1 r.2) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, j, h⟩ := hcov x
    exact ⟨(i, j), h⟩
  have h1 : ∫⁻ x, ‖F x‖ₑ ^ p ∂μ ≤ ∑' r : ι × κ, ∫⁻ x in A r.1 r.2, ‖F x‖ₑ ^ p ∂μ := by
    conv_lhs => rw [← setLIntegral_univ, ← hu]
    exact lintegral_iUnion_le _ _
  have h2 : ∀ r : ι × κ, ∫⁻ x in A r.1 r.2, ‖F x‖ₑ ^ p ∂μ ≤
      ENNReal.ofReal (b r.1 r.2 ^ p * w r.1 r.2) * E := by
    rintro ⟨i, j⟩
    have h3 : ∫⁻ x in A i j, ‖F x‖ₑ ^ p ∂μ ≤ ∫⁻ x in A i j, ENNReal.ofReal (b i j ^ p) ∂μ := by
      refine setLIntegral_mono measurable_const fun x hx => ?_
      rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (hF i j x hx) hp)
    refine h3.trans ?_
    rw [setLIntegral_const, ENNReal.ofReal_mul (Real.rpow_nonneg (hb i j) _), mul_assoc]
    gcongr
    exact hμ i j
  refine (h1.trans (ENNReal.tsum_le_tsum h2)).trans_lt ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (b i j ^ p * w i j))]
  refine ENNReal.mul_lt_top ?_ hE
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (Real.rpow_nonneg (hb i j) _) (hw i j)) (hsum i)]
  exact ENNReal.ofReal_lt_top

theorem rpow_mul_pow_eq {r : ℕ} (q p : ℝ) (e g : Fin r → ℕ) (ρ : Fin r → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (C : ℝ) (hC : 0 ≤ C) :
    (C * ∏ j, ρ j ^ g j) ^ p * q ^ (∑ j, g j * e j) = C ^ p * ∏ j, (q ^ e j * ρ j ^ p) ^ g j := by
  have h1 : ∏ j, (q ^ e j) ^ g j = q ^ (∑ j, g j * e j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have h2 : ∏ j, (ρ j ^ p) ^ g j = (∏ j, ρ j ^ g j) ^ p := by
    rw [← Real.finset_prod_rpow _ _ (fun j _ => pow_nonneg (hρ j) _)]
    exact Finset.prod_congr rfl fun j _ => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hρ j), mul_comm, Real.rpow_mul (hρ j), Real.rpow_natCast]
  simp only [mul_pow _ _ (g _)]
  rw [Finset.prod_mul_distrib, h1, h2, Real.mul_rpow hC (Finset.prod_nonneg fun j _ => pow_nonneg (hρ j) _), mul_assoc,
    mul_comm (q ^ _)]

theorem coeffLp_of_heckeWeak (p : ℝ) (hp : 2 < p) : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π →
    HeckeWeak π → CoeffLp p π := by
  intro k _ _ _ _ N V _ _ π hs hi ha hu hH
  have hp0 : 0 ≤ p := by linarith
  unfold CoeffLp
  intro _ _ μ hμ v l hl
  have hcen : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ w, ‖l (π z w)‖ = ‖l w‖ := by
    intro z hz w
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨c, hc⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k N V π hs hi ha t
    rw [hc, map_smul, norm_smul, hu t c hc, one_mul]
  have hF : ∀ g : GL (Fin N) k, ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
    intro g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    rw [hz, Subgroup.mem_center_iff.1 z.2 g, map_mul, Module.End.mul_apply, hcen _ z.2]
  refine ⟨fun q => ‖l (π q.out v)‖, hF, ?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k N => ‖l (π q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (π g v)‖ from funext hF]
    exact ((SqIntBridge.isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simpa using (by linarith : 0 < p)) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (GL (Fin 0) k) := inferInstance
    have h1 : Subsingleton (AdGL k 0) := inferInstance
    have h2 : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
    refine lintegral_rpow_lt_top_of_cover hp0 μ _ (fun _ _ : Unit => Set.univ) (fun _ => ⟨(), (), trivial⟩)
      (fun _ _ => ‖l (π (1 : AdGL k 0).out v)‖) (fun _ _ => 1) (fun _ _ => zero_le_one) (fun _ _ => norm_nonneg _) _ h2 ?_ (by simp)
      (fun _ => (hasSum_fintype _).summable)
    intro _ _ x _
    rw [Subsingleton.elim x 1, norm_norm]
  obtain ⟨m1, hm1, hK1⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ (hs v) (by simp)
  obtain ⟨m2, hm2, hK2⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ hl (by simp [Module.End.one_eq_id])
  have hm : 1 ≤ max m1 m2 := hm1.trans (le_max_left _ _)
  obtain ⟨m, hmm⟩ : ∃ m, m = max m1 m2 := ⟨_, rfl⟩
  rw [← hmm] at hm
  have hv : v ∈ fixed π (Zls.Km k N m) := by
    rintro ⟨x, hx⟩
    have : π x v = v := hK1 (GlobalTheory.T.congruence_subgroup_antitone k N m1 m (hmm ▸ le_max_left _ _) hx)
    simpa using this
  have hlK : ∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l := fun x hx =>
    hK2 (GlobalTheory.T.congruence_subgroup_antitone k N m2 m (hmm ▸ le_max_right _ _) hx)
  obtain ⟨s, hsK, hcov⟩ := GlobalTheory.T.cartan_decomposition_congruence k N m hm hN
  have key : ∀ u : s, ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), 0 ≤ C ∧ (∀ j, 0 ≤ ρ j) ∧
      (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ p < 1) ∧
      ∀ g : Fin (N - 1) → ℕ, ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m,
        ‖l (π (u.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * u.1.2) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
    rintro ⟨u, hu'⟩
    obtain ⟨h1, h2⟩ := hsK u hu'
    obtain ⟨hf, hli, heq⟩ := GlobalTheory.T.matrix_coefficient_cartan_translate k N V π m v hv l hlK u.1 u.2 h1 h2
    obtain ⟨C, ρ, hρ0, hρ1, hb⟩ := coeff_bound_rpow p hp k N V π hs ha hH m hm (π u.2 v) hf (l ∘ₗ π u.1) hli
    have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 0)
    refine ⟨C, ρ, hC, hρ0, hρ1, fun g x hx y hy => ?_⟩
    rw [heq _ x hx y hy]
    exact hb g
  choose C ρ hC0 hρ0 hρ1 hbound using key
  refine lintegral_rpow_lt_top_of_cover hp0 μ _
    (fun (u : s) (g : Fin (N - 1) → ℕ) => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = u.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * u.1.2})
    ?_ (fun u g => C u * ∏ j, ρ u j ^ g j)
    (fun _ g => (Nat.card 𝓀[k] : ℝ) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))))
    (fun _ _ => by positivity)
    (fun u g => mul_nonneg (hC0 u) (Finset.prod_nonneg fun j _ => pow_nonneg (hρ0 u j) _))
    (μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))))
    (GlobalTheory.T.congruence_subgroup_finite_volume k N μ hμ m) ?_ ?_ ?_
  · intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨u, hu', g, a, ha', b, hb, z, hz, rfl⟩ := hcov h
    exact ⟨⟨u, hu'⟩, g, _, ⟨a, ha', b, hb, rfl⟩, (QuotientGroup.mk_mul_of_mem _ hz).symm⟩
  · rintro u g _ ⟨h, ⟨a, ha', b, hb, rfl⟩, rfl⟩
    show ‖‖l (π (QuotientGroup.mk _ : AdGL k N).out v)‖‖ ≤ _
    rw [norm_norm, hF]
    exact hbound u g a ha' b hb
  · intro u g
    obtain ⟨h1, h2⟩ := hsK u.1 u.2
    refine (GlobalTheory.T.double_coset_volume_le k N μ hμ m hm u.1.1 u.1.2 h1 h2 g).trans_eq ?_
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro u
    have h := GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex (N - 1)
      (fun j => (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ u j ^ p)
      (fun j => mul_nonneg (by positivity) (Real.rpow_nonneg (hρ0 u j) _)) (hρ1 u)
    exact (h.mul_left (C u ^ p)).congr fun g => (rpow_mul_pow_eq _ p _ g _ (hρ0 u) _ (hC0 u)).symm

theorem casselmanSuffTemp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : CasselmanSuffTemp k := by
  intro N V _ _ π _ hs hi hu he ε hε
  exact @coeffLp_of_heckeWeak (2 + ε) (by linarith) k _ _ _ _ N V _ _ π hs hi (hA k N V π hs hi) hu
    (heckeWeak_of_maxExpWeak k N V π hs hi hA hF he)

end UpperTheory.Lit.Cas
