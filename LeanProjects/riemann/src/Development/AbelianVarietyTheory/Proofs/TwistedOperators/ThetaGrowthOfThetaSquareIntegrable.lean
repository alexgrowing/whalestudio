import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaKernelGrowth
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped Topology Pointwise ENNReal NNReal TensorProduct

namespace GlobalTheory.KernelSeminorm

theorem exists_nsmul_mem {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] {U : AddSubgroup G}
    (hU : IsOpen (U : Set G)) {K : Set G} (hK : IsCompact K) :
    ∃ m : ℕ, 0 < m ∧ ∀ x, (∀ k : ℕ, k • x ∈ K) → m • x ∈ U := by
  have : DiscreteTopology (G ⧸ U) := QuotientAddGroup.discreteTopology hU
  have hT : ((QuotientAddGroup.mk : G → G ⧸ U) '' K).Finite :=
    (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine ⟨(hT.toFinset.card).factorial, Nat.factorial_pos _, fun x hx => ?_⟩
  obtain ⟨a, ha, b, hb, hab, e⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (hT.toFinset.card + 1)) (t := hT.toFinset) (by simp)
    (f := fun k => (QuotientAddGroup.mk (k • x) : G ⧸ U)) fun k _ => by simpa using ⟨_, hx k, rfl⟩
  wlog h : a < b generalizing a b
  · exact this b hb a ha hab.symm e.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)
  have h1 : (b - a) • x ∈ U := by
    have := QuotientAddGroup.eq.1 e
    rwa [← Nat.add_sub_cancel' h.le, add_nsmul, neg_add_cancel_left] at this
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt h)
    ((Nat.sub_le b a).trans (Nat.le_of_lt_succ (Finset.mem_range.1 hb)))
  rw [hc, mul_nsmul]
  exact nsmul_mem h1 c

theorem lintegral_comp_aut {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) (hc : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K)
    (e : G ≃ₜ+ G) (he : ∀ x, e x ∈ Γ ↔ x ∈ Γ) {μ μ' : Measure G} {𝓕 𝓕' : Set G} (h : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) (h' : μ'.IsAddHaarMeasure)
    (h𝓕' : IsAddFundamentalDomain Γ 𝓕' μ') (h1' : μ' 𝓕' = 1) {f : G → ℂ} (hf : Continuous f)
    (hp : ∀ γ ∈ Γ, ∀ w, ‖f (γ + w)‖ = ‖f w‖) : ∫⁻ w in 𝓕, ‖f (e w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂μ' := by
  obtain ⟨N, hN⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hc).2 f hf hp
  let E : G ≃ᵐ G := e.toHomeomorph.toMeasurableEquiv
  have hm : MeasurePreserving E μ (μ.map E) := ⟨E.measurable, rfl⟩
  have h2 : (μ.map E).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have h3 : IsAddFundamentalDomain Γ (E.symm ⁻¹' 𝓕) (μ.map E) :=
    h𝓕.preimage_of_equiv (hm.symm E).quasiMeasurePreserving (e := fun γ : Γ => (⟨e γ, (he _).2 γ.2⟩ : Γ))
      ⟨fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨e.symm b, (he _).1 (by simp)⟩, Subtype.ext (e.apply_symm_apply _)⟩⟩
      fun γ x => by
        change e.symm (e γ + x) = γ + e.symm x
        rw [map_add, e.symm_apply_apply]
  have h4 : E ⁻¹' (E.symm ⁻¹' 𝓕) = 𝓕 := by ext x; simp
  have h5 := (hN _ _ h2 h3).2.2.1
  rw [E.map_apply, h4, h1, E.restrict_map, lintegral_map_equiv, h4] at h5
  rw [(hN _ _ h' h𝓕').2.2.1, h1']
  exact h5

section Denominators

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.AdelicU.HeightProper

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_compact_denom : ∃ C : Set (AF F ⊗[F] E), IsCompact C ∧ ∀ H : HeightOneSpectrum (𝓞 F) → ℝ≥0,
    (∀ v, 1 ≤ H v) → (Function.mulSupport H).Finite → ∃ d : ℕ, 0 < d ∧ (d : ℝ≥0) ≤ ∏ᶠ v, H v ∧ ∀ z : AF F ⊗[F] E,
      Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z = 0 → (∀ v, absFin F v (compFin F E v z) ≤ H v) →
      ∀ k : ℕ, k • d • z ∈ C := by
  classical
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  obtain ⟨C, hC, hC'⟩ := exists_compact_adeles (F := F) 0 1
  let e := (Algebra.TensorProduct.basis (AF F) b.traceDual).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  refine ⟨e.symm '' Set.pi Set.univ fun _ => C, (isCompact_univ_pi fun _ => hC).image he, fun H h1 hf => ?_⟩
  obtain ⟨d, hd, hdc, hv⟩ := GlobalTheory.SmoothForms.denom_global H h1 hf
  refine ⟨d, hd, hdc, fun z h0 hz k => ⟨e (k • d • z), fun i _ => ?_, e.symm_apply_apply _⟩⟩
  rw [map_nsmul, map_nsmul, Pi.smul_apply, Pi.smul_apply]
  refine hC' _ (fun w => ?_) 1 one_pos (by simp) fun v => ?_
  · have h2 := repr_map b.traceDual (fstA F) z i
    rw [h0, map_zero, Finsupp.zero_apply] at h2
    have h3 : evInf F w (e z i) = 0 := by
      change GlobalTheory.AutFunCompare.evW w (fstA F ((Algebra.TensorProduct.basis (AF F) b.traceDual).repr z i)) = 0
      rw [← h2, map_zero]
    rw [map_nsmul, map_nsmul, h3]
    simp
  · rw [Nat.cast_one, one_mul, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, norm_mul]
    refine mul_le_one₀ (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k) (norm_nonneg _) (hv v _ ?_)
    exact (congrArg nnnorm (repr_map b.traceDual (evFin F v) z i)).symm.trans_le
      ((nnnorm_repr_le_absFin b hb' v _ i).trans (hz v))

theorem absFin_mul_mul_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (a : GL m (AF F ⊗[F] E))
    (b : GL n (AF F ⊗[F] E)) (u : Matrix m n (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F))
    (hu : ∀ i j, absFin F v (compFin F E v (u i j)) ≤ 1) (i : m) (j : n) :
    absFin F v (compFin F E v ((a.1 * u * b.1) i j)) ≤ htFin F v (bc (compFin F E v) a) * htFin F v (bc (compFin F E v) b) := by
  refine (absFin_le_normFin F v ((a.1 * u * b.1).map (compFin F E v)) i j).trans ?_
  rw [Matrix.map_mul, Matrix.map_mul]
  refine (normFin_mul_le _ v _ _).trans (mul_le_mul' ((normFin_mul_le _ v _ _).trans ?_) (le_htOf _ (bc (compFin F E v) b)))
  exact (mul_le_of_le_one_right' ((normFin_le_iff _ v).2 hu)).trans (le_htOf _ (bc (compFin F E v) a))

end Denominators

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth GlobalTheory.Grow GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem actO_nsmul (g : GA D S) (h : GA D T) (n : ℕ) (u : WO S T) : actO S T g h (n • u) = n • actO S T g h u := by
  induction n with
  | zero => unfold actO; rw [zero_nsmul, zero_nsmul, Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, ← ih]; unfold actO; rw [Matrix.mul_add, Matrix.add_mul]

open GlobalTheory.AdelicU Formalism.UG in

theorem exists_level_multiple {U : AddSubgroup (WO S T)} (hU : IsOpen (U : Set (WO S T))) :
    ∃ K₀ ∈ 𝓝 (0 : WO S T), IsCompact K₀ ∧ ∃ m : ℕ, ∀ (g : GA D S) (h : GA D T), ∃ n : ℕ, 0 < n ∧
      (n : ℝ) ≤ m * (height S g * height T h) ∧ ∀ u ∈ K₀, u.map (infPart D) = 0 → actO S T g⁻¹ h⁻¹ (n • u) ∈ U := by
  obtain ⟨i1, i2, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have hev : ∀ᶠ u in 𝓝 (0 : WO S T), ∀ i j v, absFin D.host.F v (compFin D.host.F D.host.E v (u i j)) ≤ 1 :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      ((continuous_id.matrix_elem i j).tendsto' (0 : WO S T) 0 rfl).eventually (eventually_absFin_le_one_nhds D.host.F)
  obtain ⟨K₀, h0, hsub, hK₀⟩ := LocallyCompactSpace.local_compact_nhds (X := WA T S) 0 _ hev
  obtain ⟨C, hC, hden⟩ := exists_compact_denom D.host.F D.host.E
  have hK : IsCompact (X := WA T S) (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  obtain ⟨m, hm, hmul⟩ := exists_nsmul_mem (G := WA T S) hU hK
  refine ⟨K₀, h0, hK₀, m, fun g h => ?_⟩
  have f1 := finite_mulSupport_htFin D.host.F (Formalism.L2.Theta.matHom S g)
  have f2 := finite_mulSupport_htFin D.host.F (Formalism.L2.Theta.matHom T h⁻¹)
  obtain ⟨d, hd, hdc, hz⟩ := hden (fun v => htFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom T h⁻¹)) *
    htFin D.host.F v (bc (compFin D.host.F D.host.E v) (Formalism.L2.Theta.matHom S g)))
    (fun v => one_le_mul_of_one_le_of_one_le (one_le_htOf _ _) (one_le_htOf _ _))
    ((f2.union f1).subset (Function.mulSupport_mul _ _))
  refine ⟨m * d, by positivity, ?_, fun u hu hinf => ?_⟩
  · rw [finprod_mul_distrib f2 f1] at hdc
    have h1 : (d : ℝ≥0) ≤ heightGL D.host.F (Formalism.L2.Theta.matHom T h⁻¹) * heightGL D.host.F (Formalism.L2.Theta.matHom S g) :=
      hdc.trans (mul_le_mul' (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _))
        (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _)))
    have h2 : (d : ℝ) ≤ height T h⁻¹ * height S g := by unfold GlobalTheory.Grow.height; exact_mod_cast h1
    rw [GlobalTheory.Grow.height_inv, mul_comm] at h2
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left h2 m.cast_nonneg
  · have e : actO S T g⁻¹ h⁻¹ ((m * d) • u) = m • d • actO S T g⁻¹ h⁻¹ u := by
      rw [actO_nsmul, mul_nsmul']
    rw [e]
    refine hmul _ fun k i _ j _ => hz (actO S T g⁻¹ h⁻¹ u i j) ?_ (fun v => ?_) k
    · have hv : (actO S T g⁻¹ h⁻¹ u).map (infPart D) = 0 := by
        unfold actO
        rw [Matrix.map_mul, Matrix.map_mul, hinf, Matrix.mul_zero, Matrix.zero_mul]
      exact congrFun (congrFun hv i) j
    · unfold actO
      rw [inv_inv]
      exact absFin_mul_mul_le D.host.F D.host.E (Formalism.L2.Theta.matHom T h⁻¹) (Formalism.L2.Theta.matHom S g) u v
        (fun i j => hsub hu i j v) i j

theorem sum_norm_compAt_le (τ : D.what₂.Tau) (g : GA D T) :
    ∑ i, ∑ j, ‖compAt θ τ (Formalism.L2.Theta.mt T g) i j‖ ≤ normInf θ T g :=
  (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    le_add_of_nonneg_right (norm_nonneg (infMat D.sp.cm.sig T.gram (θ τ) g⁻¹ i j))).trans
    (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig T.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig T.gram (θ τ) g⁻¹ i j‖)) (fun _ _ => by positivity) (Finset.mem_univ τ))

theorem norm_mov_le_normInf (g : GA D S) (h : GA D T) (u : RW T S) :
    ‖mov θ g h u‖ ≤ normInf θ T h * ‖u‖ * normInf θ S g⁻¹ := by
  have h0 : 0 ≤ normInf θ T h := by unfold normInf; positivity
  have h0' : 0 ≤ normInf θ S g⁻¹ := by unfold normInf; positivity
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have h1 : ∑ k, ‖compAt θ τ (Formalism.L2.Theta.mt T h) i k‖ ≤ normInf θ T h :=
    (Finset.single_le_sum (f := fun i => ∑ k, ‖compAt θ τ (Formalism.L2.Theta.mt T h) i k‖) (fun _ _ => by positivity)
      (Finset.mem_univ i)).trans (sum_norm_compAt_le τ h)
  have h2 : ∑ l, ‖compAt θ τ (Formalism.L2.Theta.mt S g⁻¹) l j‖ ≤ normInf θ S g⁻¹ :=
    (Finset.sum_le_sum fun l _ => Finset.single_le_sum (f := fun j => ‖compAt θ τ (Formalism.L2.Theta.mt S g⁻¹) l j‖)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans (sum_norm_compAt_le τ g⁻¹)
  change ‖∑ l, (∑ k, compAt θ τ (Formalism.L2.Theta.mt T h) i k * u τ k l) * compAt θ τ (Formalism.L2.Theta.mt S g⁻¹) l j‖ ≤ _
  refine (norm_sum_le _ _).trans (le_trans ?_ (mul_le_mul_of_nonneg_left h2 (by positivity)))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (le_trans ?_ (mul_le_mul_of_nonneg_right h1 (norm_nonneg u))))
    (norm_nonneg _)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ l).trans ((norm_le_pi_norm _ k).trans (norm_le_pi_norm u τ)))
    (norm_nonneg _)

open Classical in

def letter (a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) : RW T S :=
  fun τ i j => if τ = a.1 then if i = a.2.1 then if j = a.2.2.1 then (if a.2.2.2 then Complex.I else 1) else 0 else 0 else 0

theorem dv_letter (hc : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (a : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)
    (f : WO S T → ℂ) : dv θ σ S T (letter a) f = heisDer ψ θ a f := by
  classical
  obtain ⟨L, hL, e, e'⟩ := exists_line hc hψ (letter a)
  have : L = lineAt θ a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)) := by
    refine GlobalTheory.RealLineAt.lineAt_unique D θ hc.inf _ _ a.1 _ _ _ ⟨hL.1, hL.2, fun t τ => ?_⟩ (isLineAt_lineAt hc.inf _ _)
    rw [e]
    refine (congrFun (hc.pi_iota T S (t • letter a)) τ).trans ?_
    funext i j
    by_cases h1 : τ = a.1 <;> simp [letter, Matrix.single, h1, ite_and, @eq_comm _ i, @eq_comm _ j]
  rw [e', this]
  rfl

theorem exists_coord (z : RW T S) : ∃ c : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → ℝ,
    (∀ a, |c a| ≤ ‖z‖) ∧ z = ∑ a, c a • letter a := by
  classical
  refine ⟨fun a => if a.2.2.2 then (z a.1 a.2.1 a.2.2.1).im else (z a.1 a.2.1 a.2.2.1).re, fun a => ?_, ?_⟩
  · have : ‖z a.1 a.2.1 a.2.2.1‖ ≤ ‖z‖ := (norm_le_pi_norm _ _).trans ((norm_le_pi_norm _ _).trans (norm_le_pi_norm z _))
    beta_reduce
    split_ifs
    exacts [(Complex.abs_im_le_norm _).trans this, (Complex.abs_re_le_norm _).trans this]
  · funext τ i j
    simp [letter, Fintype.sum_prod_type, Finset.sum_apply, Finset.sum_add_distrib, Finset.sum_ite_irrel, add_comm]

variable {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem sobO_dvL_le (hc : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (p : ℕ) {ρ : ℝ≥0} {z : RW T S} (hz : ‖z‖ ≤ ρ)
    (m : thetaSub ψ S T) : sobO ψ θ μ 𝓕 p (dvL hc hψ S T z m).1 ≤
      (Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) * sobO ψ θ μ 𝓕 (p + 1) m.1 := by
  obtain ⟨c, h1, rfl⟩ := exists_coord z
  rw [map_sum, LinearMap.sum_apply]
  refine (Finset.le_sum_of_subadditive (fun m : thetaSub ψ S T => sobO ψ θ μ 𝓕 p m.1) ?_
    (fun x y => sobO_add_le hψ hc.inf x.2 y.2 p) _ _).trans ((Finset.sum_le_card_nsmul _ _
      (ρ * sobO ψ θ μ 𝓕 (p + 1) m.1) fun a _ => ?_).trans_eq ?_)
  · have := sobO_smul (ψ := ψ) (θ := θ) (μ := μ) (𝓕 := 𝓕) (f := 0) p 0
    rw [zero_smul, enorm_zero, zero_mul] at this
    exact this.le
  · rw [map_smul, LinearMap.smul_apply]
    change sobO ψ θ μ 𝓕 p ((c a : ℂ) • dv θ σ S T (letter a) m.1) ≤ _
    rw [sobO_smul, dv_letter hc hψ]
    refine mul_le_mul' ?_ (sobO_heisDer_le p a)
    rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Complex.norm_real]
    exact (h1 a).trans hz
  · rw [nsmul_eq_mul, Finset.card_univ, ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc]

theorem l2O_foldl_dvL_le_pow_mul_sobO (hc : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {ρ : ℝ≥0} (p : ℕ) : ∀ (l : List (RW T S)), l.length ≤ p →
    (∀ z ∈ l, ‖z‖ ≤ ρ) → ∀ m : thetaSub ψ S T, l2O μ 𝓕 (l.foldl (fun m z => dvL hc hψ S T z m) m).1 ≤
      ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) ^ p * sobO ψ θ μ 𝓕 p m.1 := by
  have h0 : ∀ (p : ℕ) (f : WO S T → ℂ), l2O μ 𝓕 f ≤
      ((1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * ρ : ℝ≥0) : ℝ≥0∞) ^ p * sobO ψ θ μ 𝓕 p f :=
    fun p f => ((sobO_zero (ψ := ψ) (θ := θ)).ge.trans (sobO_mono p.zero_le)).trans
      (le_mul_of_one_le_left' (one_le_pow₀ (ENNReal.one_le_coe_iff.2 le_self_add)))
  induction p with
  | zero =>
    intro l hl _ m
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)]
    exact h0 0 _
  | succ p ih =>
    intro l hl hz m
    cases l with
    | nil => exact h0 _ _
    | cons z l =>
      refine (ih l (by simpa using hl) (fun v hv => hz v (List.mem_cons_of_mem _ hv)) _).trans ?_
      rw [pow_succ, mul_assoc]
      exact mul_le_mul_right ((sobO_dvL_le hc hψ p (hz z List.mem_cons_self) m).trans
        (mul_le_mul_left (ENNReal.coe_le_coe.2 le_add_self) _)) _

theorem exists_dilation {n : ℕ} (hn : 0 < n) :
    ∃ e : WA T S ≃ₜ+ WA T S, (∀ x, e x = n • x) ∧ ∀ x, e x ∈ ratL T S ↔ x ∈ ratL T S := by
  obtain ⟨i1, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : IsModuleTopology (AF D.host.F) (Formalism.L2.Theta.AE D) := ⟨rfl⟩
  have : IsTopologicalRing (Formalism.L2.Theta.AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have hn' : (n : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h1 : incA D (n : D.host.E)⁻¹ * (n : Formalism.L2.Theta.AE D) = 1 := by
    rw [← map_natCast (incA D), ← map_mul, inv_mul_cancel₀ hn', map_one]
  have hl : ∀ x : WA T S, (n • x).map (incA D (n : D.host.E)⁻¹ * ·) = x := fun x => by
    ext i j
    change incA D (n : D.host.E)⁻¹ * (n • x i j) = _
    rw [nsmul_eq_mul, ← mul_assoc, h1, one_mul]
  refine ⟨{ toFun := fun x => n • x
            invFun := fun x => x.map (incA D (n : D.host.E)⁻¹ * ·)
            left_inv := hl
            right_inv := fun x => ?_
            map_add' := fun x y => nsmul_add x y n
            continuous_toFun := continuous_nsmul n
            continuous_invFun := continuous_id.matrix_map (continuous_const.mul continuous_id) }, fun _ => rfl,
    fun x => ⟨?_, fun h => nsmul_mem h n⟩⟩
  · ext i j
    change n • (incA D (n : D.host.E)⁻¹ * x i j) = _
    rw [nsmul_eq_mul, ← mul_assoc, mul_comm (n : Formalism.L2.Theta.AE D), h1, one_mul]
  · rintro ⟨γ, hγ⟩
    refine ⟨γ.map ((n : D.host.E)⁻¹ * ·), ?_⟩
    rw [← hl x]
    ext i j
    exact (map_mul (incA D) _ _).trans (congrArg (incA D (n : D.host.E)⁻¹ * ·) (congrFun (congrFun hγ i) j))

theorem cube_dilate_bound (hψ : IsStdChar D ψ (-1)) (hc : Chart θ σ) {N : ℕ} (b : Module.Basis (Fin N) ℝ (RW T S))
    {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ≥0, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ n : ℕ, 0 < n →
      ∀ φ, IsThetaFunO ψ S T φ → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) φ = φ) →
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖φ (0 + ∑ i, iotaW σ T S (t i • n • b i))‖ ^ 2 ≤ c * (l2O μ 𝓕 φ).toReal ^ 2 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ₀, 𝓕₀, hμ, h𝓕, h1⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hcov
  have : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let ι : (Fin N → ℝ) →+ WA T S := (iotaW σ T S).comp b.equivFun.symm.toLinearMap.toAddMonoidHom
  let π : WA T S →+ (Fin N → ℝ) := b.equivFun.toLinearMap.toAddMonoidHom.comp (piW θ T S)
  have hι : Continuous ι := (hc.continuous_iota T S).comp b.equivFunL.symm.continuous
  have hπ : Continuous π := b.equivFunL.continuous.comp (continuous_pi' hc.inf T S)
  have hπι : ∀ t, π (ι t) = t := fun t => by
    show b.equivFun (piW θ T S (iotaW σ T S (b.equivFun.symm t))) = t
    rw [hc.pi_iota, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ w, ι (π w) = iotaW σ T S (piW θ T S w) := fun w => by
    show iotaW σ T S (b.equivFun.symm (b.equivFun (piW θ T S w))) = _
    rw [LinearEquiv.symm_apply_apply]
  obtain ⟨c, K₁, hK₁, hreal⟩ := lintegral_real_le (G := WA T S) μ₀ ι π hι hπ hπι hK₀ h0
    (isCompact_univ_pi fun _ : Fin N => isCompact_Icc (a := (0 : ℝ)) (b := 1))
  obtain ⟨M, hM⟩ := lintegral_compact_le (G := WA T S) (ratL T S) μ₀ h𝓕 hK₁
  refine ⟨c * M, fun μ 𝓕 hm n hn φ hφ hl => ?_⟩
  obtain ⟨e, he, heL⟩ := exists_dilation (S := S) (T := T) hn
  have hsum : ∀ t : Fin N → ℝ, 0 + ∑ i, iotaW σ T S (t i • n • b i) = e (ι t) := fun t => by
    rw [he]
    show _ = n • iotaW σ T S (b.equivFun.symm t)
    rw [zero_add, Module.Basis.equivFun_symm_apply, ← map_nsmul, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm]
  have en : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hmeas : Measurable fun w : WA T S => ‖φ (e w)‖ₑ ^ 2 := (hφ.cont.comp e.continuous).measurable.enorm.pow_const 2
  have a1 := hreal _ hmeas fun w hw => by
    have hinf : (w - ι (π w)).map (infPart D) = 0 := by
      have hp : piW θ T S (w - ι (π w)) = 0 := by rw [hιπ, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
      ext i j
      exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
    have := GlobalTheory.HeisOrtho.norm_heisO hψ.1 φ (n • (w - ι (π w))) (e (ι (π w)))
    rw [hl _ hw hinf, ← he, ← map_add, add_sub_cancel] at this
    rw [← en, ← en, this]
  have a2 := hM _ hmeas fun γ hγ w => by
    rw [← en, ← en, map_add, theta_norm_periodic hψ hφ _ ((heL γ).2 hγ)]
  have a3 := lintegral_comp_aut (G := WA T S) (ratL T S) hK hcov e heL hμ h𝓕 h1 hm.1 hm.2.1 hm.2.2 hφ.cont
    (theta_norm_periodic hψ hφ)
  simp only [hsum]
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖φ (e (ι t))‖ ^ 2)
    (Filter.Eventually.of_forall fun w => by positivity)
    ((hφ.cont.comp (e.continuous.comp hι)).norm.pow 2).aestronglyMeasurable]
  simp only [en]
  have a4 := a1.trans (mul_le_mul_right (a2.trans_eq (congrArg _ (a3.trans (l2O_sq_eq_lintegral μ 𝓕 φ).symm))) _)
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
    (ENNReal.pow_ne_top (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hm.1 hm.2.1 hφ)))) a4).trans_eq ?_
  simp [mul_assoc]

theorem norm_mov_nsmul_le {CS CT m κ : ℝ} (hCS : ∀ g : GA D S, normInf θ S g ≤ CS * height S g)
    (hCT : ∀ h : GA D T, normInf θ T h ≤ CT * height T h) (g : GA D S) (h : GA D T) {n : ℕ}
    (hn : (n : ℝ) ≤ m * (height S g * height T h)) {u : RW T S} (hu : ‖u‖ ≤ κ) :
    ‖mov θ g⁻¹ h⁻¹ (n • u)‖ ≤ ‖CT‖ * (m * κ) * ‖CS‖ * (height S g * height T h) ^ 2 := by
  refine (norm_mov_le_normInf _ _ _).trans ?_
  have a1 : normInf θ T h⁻¹ ≤ ‖CT‖ * height T h :=
    (hCT h⁻¹).trans (by rw [height_inv]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (height_pos T h).le)
  have a2 : normInf θ S g⁻¹⁻¹ ≤ ‖CS‖ * height S g :=
    (hCS _).trans (by rw [inv_inv]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (height_pos S g).le)
  have a3 : ‖n • u‖ ≤ m * (height S g * height T h) * κ :=
    norm_nsmul_le.trans (mul_le_mul hn hu (norm_nonneg _) (n.cast_nonneg.trans hn))
  have a4 : 0 ≤ normInf θ S g⁻¹⁻¹ := by unfold normInf; positivity
  have a5 : 0 ≤ ‖CT‖ * height T h := mul_nonneg (norm_nonneg _) (height_pos T h).le
  refine (mul_le_mul (mul_le_mul a1 a3 (norm_nonneg _) a5) a2 a4 (mul_nonneg a5 ((norm_nonneg _).trans a3))).trans_eq ?_
  ring

theorem kernelBound (S T : HSp D) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.KernelBound S T (2 * Module.finrank ℝ (RW T S)) (Module.finrank ℝ (RW T S)) := by
  intro ψ θ hθ U hU
  by_cases hψ : IsStdChar D ψ (-1)
  swap
  · exact ⟨0, fun _ _ _ h => absurd h.std hψ⟩
  obtain ⟨σ, hc⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have b := Module.finBasis ℝ (RW T S)
  generalize Module.finrank ℝ (RW T S) = N at b ⊢
  obtain ⟨K₀, h0, hK₀, m, hlev⟩ := exists_level_multiple hU
  obtain ⟨c, hcube⟩ := cube_dilate_bound hψ hc b h0 hK₀
  obtain ⟨CS, hCS⟩ := normInf_le_height S hθ
  obtain ⟨CT, hCT⟩ := normInf_le_height T hθ
  let R : ℝ≥0 := ‖CT‖₊ * (m * ‖fun i => b i‖₊) * ‖CS‖₊
  let Q : ℝ≥0 := 1 + Fintype.card (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) * R
  refine ⟨NNReal.sqrt (4 ^ N * c) * Q ^ N, fun χS χT om hom μ 𝓕 hm f hf g h => ?_⟩
  obtain ⟨n, hn, hnle, hlev⟩ := hlev g h
  have hg := height_pos S g
  have hh := height_pos T h
  obtain ⟨X, hX⟩ : ∃ X : ℝ≥0, height S g * height T h = X := ⟨⟨_, (mul_pos hg hh).le⟩, rfl⟩
  have hX1 : 1 ≤ X := by
    rw [← NNReal.coe_le_coe, ← hX]
    exact one_le_mul_of_one_le_of_one_le (one_le_height S g) (one_le_height T h)
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, sobO ψ θ μ 𝓕 N f = s :=
    ⟨_, (ENNReal.coe_toNNReal (sobO_ne_top hψ hθ hm.1 hm.2.1 hf.1 N)).symm⟩
  let wd : List (RW T S) → thetaSub ψ S T := fun l => l.foldl (fun m z => dvL hc hψ S T z m) ⟨f, hf.1⟩
  let A : ℕ → Set (WO S T → ℂ) := fun p =>
    {F | ∃ l : List (RW T S), l.length ≤ p ∧ (∀ u ∈ l, ‖u‖ ≤ (R * X ^ 2 : ℝ≥0)) ∧ F = om (g, h) (wd l).1}
  have key := sobolev_iter N 0 (fun i r => iotaW σ T S (r • n • b i)) A (c * ((Q * X ^ 2) ^ N * s : ℝ≥0) ^ 2) 0
    (fun i => (hc.continuous_iota T S).comp (continuous_id.smul continuous_const))
    (fun p q hpq F ⟨l, h1, h2⟩ => ⟨l, h1.trans hpq, h2⟩) ?_ ?_ (om (g, h) f) ⟨[], le_rfl, by simp, rfl⟩
  · rw [hs, hX, ← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_mul, ← ENNReal.coe_mul, enorm_eq_nnnorm,
      ENNReal.coe_le_coe, ← pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero]
    have e : ∀ Q : ℝ≥0, (NNReal.sqrt (4 ^ N * c) * Q ^ N * s * X ^ (2 * N)) ^ 2 = 4 ^ N * (c * ((Q * X ^ 2) ^ N * s) ^ 2) := by
      intro Q
      rw [mul_assoc, mul_assoc, mul_pow (NNReal.sqrt _), NNReal.sq_sqrt]
      ring
    rw [e]
    exact_mod_cast key
  · rintro p _ ⟨l, h1, h2, rfl⟩
    have hF := hom.om_pres (g, h) _ (wd l).2
    refine ⟨hF.cont, fun i => ⟨_, ⟨l ++ [mov θ g⁻¹ h⁻¹ (n • b i)], by simpa using h1, fun u hu => ?_, ?_⟩,
      sobolev_step hc hψ (n • b i) hF⟩⟩
    · rcases List.mem_append.1 hu with hu | hu
      · exact h2 u hu
      · rw [List.mem_singleton.1 hu]
        refine (norm_mov_nsmul_le hCS hCT g h hnle (norm_le_pi_norm (fun i => b i) i)).trans_eq ?_
        rw [hX]
        rfl
    · rw [dv_om hom hc g h (n • b i) (wd l).2]
      simp only [wd, List.foldl_append]
      rfl
  · rintro _ ⟨l, h1, h2, rfl⟩
    refine (hcube μ 𝓕 hm n hn _ (hom.om_pres (g, h) _ (wd l).2) fun u hu hinf => ?_).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg ?_ 2) c.coe_nonneg)
    · have hv : (actO S T g⁻¹ h⁻¹ (n • u)).map (infPart D) = 0 := by
        have : (n • u).map (infPart D) = 0 := by
          ext i j
          have h3 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
          exact (map_nsmul (infPart D) n (u i j)).trans ((congrArg (n • ·) h3).trans (nsmul_zero n))
        unfold actO
        rw [Matrix.map_mul, Matrix.map_mul, this, Matrix.mul_zero, Matrix.zero_mul]
      have e := hom.om_heis g h (actO S T g⁻¹ h⁻¹ (n • u)) _ (wd l).2
      rw [words_level hc hψ hv l _ (hf.2 _ (hlev u hu hinf) hv), actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one] at e
      exact e.symm
    · rw [l2O_om_apply_eq_of_isThetaFunO hom hm.1 hm.2.1 (wd l).2]
      refine ENNReal.toReal_le_coe_of_le_coe ((l2O_foldl_dvL_le_pow_mul_sobO hc hψ N l (by simpa using h1) h2 _).trans ?_)
      rw [hs, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
      refine mul_le_mul_left (pow_le_pow_left₀ zero_le ?_ N) _
      exact (add_le_add (one_le_pow₀ hX1) (mul_assoc _ R _).ge).trans_eq (by rw [add_mul, one_mul])

theorem thetaGrowthUnif : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowthUnif := fun r N => by
  refine ⟨2 * (2 * r * N), 2 * r * N, fun D V W hr hN => ?_⟩
  have e : Module.finrank ℝ (RW W V) = 2 * r * N := by
    have h1 : Fintype.card D.what₂.Tau = r := by
      have := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1.1
      rw [Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D), ← hr, IsTotallyReal.finrank,
        InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, h1, ← hN]
    ring
  exact e ▸ kernelBound V W

theorem thetaGrowth (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth.ThetaGrowth D := thetaGrowthUnif.thetaGrowth D

end GlobalTheory.KernelSeminorm

end
