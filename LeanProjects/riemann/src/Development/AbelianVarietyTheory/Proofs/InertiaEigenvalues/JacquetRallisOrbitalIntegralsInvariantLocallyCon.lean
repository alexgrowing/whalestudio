import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitInvariantMapProperStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantImageOpenClosedLocalSectionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodulaStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralLinearHaarIsMulRightInvariantUnramifiedStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OrbLC

theorem eventually_eq_fun {A G β : Type} [TopologicalSpace A] [TopologicalSpace G] (Φ : A → G → β) (a₀ : A)
    (K : Set G) (hK : IsCompact K) (hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g)
    (hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g) : ∀ᶠ a in 𝓝 a₀, Φ a = Φ a₀ := by
  have h := hK.eventually_forall_of_forall_eventually (x₀ := a₀) (P := fun a g => Φ a g = Φ a₀ g) (by
    intro g hg
    have h1 := hloc g hg
    have hT : Tendsto (fun z : A × G => (a₀, z.2)) (𝓝 (a₀, g)) (𝓝 (a₀, g)) := by
      have : Continuous (fun z : A × G => (a₀, z.2)) := by fun_prop
      simpa using this.tendsto (a₀, g)
    have h2 := hT.eventually h1
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2])
  filter_upwards [h, hout] with a h1 h2
  funext g
  by_cases hg : g ∈ K
  · exact h1 g hg
  · exact h2 g hg

theorem act_mul {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  simp only [act, Units.val_mul, _root_.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem actU_mul {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g h : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : actU (g * h) X = actU g (actU h X) := by
  simp only [actU]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · apply Subtype.ext
    simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  · simp only [Submonoid.coe_mul, Matrix.mulVec_mulVec]

theorem part1 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F) :
    orbG M f' (act g Y) = orbG M f' Y := by
  letI := M.mG
  haveI := M.bG
  haveI := GlobalTheory.T.generalLinear_haar_isMulRightInvariant_unramified F E r M
  unfold orbG
  simp only [← act_mul]
  exact integral_mul_right_eq_self (fun h => f' (act h Y) * omega (act h Y)) g

theorem part2 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) :
    orbU M f (actU g X) = orbU M f X := by
  letI := M.mU
  haveI := M.bU
  haveI := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M
  unfold orbU
  simp only [← actU_mul]
  exact integral_mul_right_eq_self (fun h => f (actU h X)) g

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem companion_pow_mulVec {r : ℕ} {k : Type} [CommRing k] (p : Fin r → k) :
    ∀ (j : ℕ) (hj : j < r), (companion p) ^ j *ᵥ (fun i : Fin r => if (i : ℕ) = 0 then (1 : k) else 0) =
      Pi.single (⟨j, hj⟩ : Fin r) 1 := by
  intro j
  induction j with
  | zero =>
    intro hj
    funext i
    simp only [pow_zero, Matrix.one_mulVec, Pi.single_apply, Fin.ext_iff]
  | succ j ih =>
    intro hj
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih (by omega)]
    funext i
    rw [Matrix.mulVec_single]
    simp only [companion, Matrix.of_apply, mul_one, Pi.single_apply, Fin.ext_iff]
    have : j + 1 ≠ r := by omega
    simp [this]

theorem Cm_sec {r : ℕ} {k : Type} [CommRing k] (a : Inv r k) : Cm (sec a) = hankel a := by
  ext i j
  simp only [Cm, hankel, mom, Matrix.of_apply]
  rw [pow_add, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have h := companion_pow_mulVec a.1 j j.2
  simp only [sec] at h ⊢
  rw [h, Fin.eta, dotProduct_single, mul_one]

theorem lastDet_act_sec {r : ℕ} {k : Type} [CommRing k] (g : GL (Fin r) k) (a : Inv r k) :
    lastDet (act g (sec a)) = (-1) ^ r * (Delta a * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).det) := by
  rw [(GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det k r).1, (GlobalTheory.T.jacquetRallis_transfer_factor_krylov_det k r).2, Matrix.det_mul, Cm_sec]
  rfl

theorem eta_eventually {F : Type} [NormedField F] [IsUltrametricDist F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, eta y = eta x := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  have hn : ‖y‖ = ‖x‖ := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := y - x) (y := x) hy.ne
    rw [sub_add_cancel] at this
    rw [this, max_eq_right hy.le]
  unfold eta
  rw [hn]

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem part3 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f' : Gl r F → ℂ) (hf : IsTest f') (a₀ : Inv r F) (hΔ : Delta a₀ ≠ 0) :
    ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀) := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : IsUltrametricDist F := Unram.ultraF (E := E)
  obtain ⟨hcont, -, hDc, hprop⟩ := GlobalTheory.T.jacquetRallis_orbit_invariant_map_proper F E r
  have hopen : IsOpen {a : Inv r F | Delta a ≠ 0} := isOpen_ne_fun hDc continuous_const
  obtain ⟨Ω, hΩn, hΩsub, hΩc⟩ := local_compact_nhds (hopen.mem_nhds hΔ)
  set K : Set (GL (Fin r) F) :=
    Prod.fst '' {p : GL (Fin r) F × Inv r F | p.2 ∈ Ω ∧ act p.1 (sec p.2) ∈ tsupport f'} with hKdef
  have hK : IsCompact K := (hprop (tsupport f') Ω hf.2 hΩc (fun a ha => hΩsub ha)).image continuous_fst
  have hzero : ∀ a ∈ Ω, ∀ g ∉ K, f' (act g (sec a)) = 0 := by
    intro a ha g hg
    by_contra h
    exact hg ⟨(g, a), ⟨ha, subset_tsupport _ h⟩, rfl⟩
  set Φ : Inv r F → GL (Fin r) F → ℂ := fun a g => f' (act g (sec a)) * omega (act g (sec a)) with hΦ
  have ha₀ : a₀ ∈ Ω := mem_of_mem_nhds hΩn
  have hc2 : Continuous (fun z : Inv r F × GL (Fin r) F => act z.2 (sec z.1)) :=
    hcont.comp continuous_swap
  have hdet : Continuous (fun z : Inv r F × GL (Fin r) F =>
      (-1 : F) ^ r * (Delta z.1 * ((z.2⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det)) := by
    have h1 : Continuous (fun z : Inv r F × GL (Fin r) F => ((z.2⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_snd)
    exact continuous_const.mul ((hDc.comp continuous_fst).mul h1.matrix_det)
  have hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g := by
    intro g _
    have h1 : ∀ᶠ z in 𝓝 (a₀, g), f' (act z.2 (sec z.1)) = f' (act g (sec a₀)) :=
      (hc2.tendsto (a₀, g)).eventually ((IsLocallyConstant.iff_eventually_eq f').1 hf.1 _)
    have hne : (-1 : F) ^ r * (Delta a₀ * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det) ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (mul_ne_zero hΔ ?_)
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (g⁻¹ : GL (Fin r) F))).ne_zero
    have h2 := (hdet.tendsto (a₀, g)).eventually (eta_eventually _ hne)
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hΦ, omega, lastDet_act_sec]
    rw [hz1]
    rw [hz2]
  have hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g := by
    filter_upwards [hΩn] with a ha g hg
    simp only [hΦ, hzero a ha g hg, hzero a₀ ha₀ g hg, zero_mul]
  filter_upwards [eventually_eq_fun Φ a₀ K hK hloc hout] with a h
  have h' : ∀ g, f' (act g (sec a)) * omega (act g (sec a)) = f' (act g (sec a₀)) * omega (act g (sec a₀)) :=
    fun g => congrFun h g
  simp only [orbG, h']

end GlobalTheory.JR.OrbLC

namespace GlobalTheory.JR.OrbLC

theorem continuous_star_of_unram (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] : Continuous (star : E → E) :=
  (AddMonoidHomClass.isometry_of_norm (starAddEquiv (R := E)) (fun x => Unram.norm_star (F := F) x)).continuous

theorem continuous_actU (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU p.1 p.2) := by
  haveI : ContinuousStar E := ⟨continuous_star_of_unram F E⟩
  have hg : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => (p.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp continuous_fst
  have hA : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => (p.2.1 : Matrix (Fin r) (Fin r) E)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hb : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => p.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hl : Continuous (fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => p.2.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  refine Continuous.prodMk ?_ (Continuous.prodMk (hg.matrix_mulVec hb) hl)
  exact Continuous.subtype_mk ((hg.mul hA).mul hg.star) _

theorem part4 (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (r : ℕ) (M : Meas r F E) (f : Hn r F E → ℂ) (hf : IsTest f) (a₀ : Inv r F) (X₀ : Hn r F E)
    (hΔ : Delta a₀ ≠ 0) (hX₀ : HasInv X₀ a₀) :
    ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  obtain ⟨Ω, s, hΩc, hΩo, ha₀, hs, hsinv, hprop⟩ := (GlobalTheory.T.invariant_image_openClosed_local_sections F E r a₀ hΔ).2 ⟨X₀, hX₀⟩
  have huniq := (GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r).2.2.1
  set K : Set (Matrix.unitaryGroup (Fin r) E) :=
    Prod.fst '' {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ tsupport f} with hKdef
  have hK : IsCompact K := (hprop (tsupport f) hf.2).image continuous_fst
  have hzero : ∀ a ∈ Ω, ∀ g ∉ K, f (actU g (s a)) = 0 := by
    intro a ha g hg
    by_contra h
    exact hg ⟨(g, a), ⟨ha, subset_tsupport _ h⟩, rfl⟩
  set Φ : Inv r F → Matrix.unitaryGroup (Fin r) E → ℂ := fun a g => f (actU g (s a)) with hΦ
  have hloc : ∀ g ∈ K, ∀ᶠ z in 𝓝 (a₀, g), Φ z.1 z.2 = Φ a₀ g := by
    intro g _
    have hsa : ContinuousAt s a₀ := hs.continuousAt (hΩo.mem_nhds ha₀)
    have h1 : ContinuousAt (fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => (z.2, s z.1)) (a₀, g) :=
      continuousAt_snd.prodMk (hsa.comp continuousAt_fst)
    have hT : ContinuousAt (fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => actU z.2 (s z.1)) (a₀, g) :=
      ContinuousAt.comp (g := fun p : Matrix.unitaryGroup (Fin r) E × Hn r F E => actU p.1 p.2)
        (f := fun z : Inv r F × Matrix.unitaryGroup (Fin r) E => (z.2, s z.1))
        ((continuous_actU F E r).continuousAt) h1
    exact hT.tendsto.eventually ((IsLocallyConstant.iff_eventually_eq f).1 hf.1 _)
  have hout : ∀ᶠ a in 𝓝 a₀, ∀ g ∉ K, Φ a g = Φ a₀ g := by
    filter_upwards [hΩo.mem_nhds ha₀] with a ha g hg
    simp only [hΦ, hzero a ha g hg, hzero a₀ ha₀ g hg]
  have horb : ∀ a ∈ Ω, ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f (s a) := by
    intro a ha X hX
    obtain ⟨g, hg, -⟩ := huniq (s a) X a (hsinv a ha).1 (hsinv a ha).2 hX
    rw [← hg, part2]
  filter_upwards [eventually_eq_fun Φ a₀ K hK hloc hout, hΩo.mem_nhds ha₀] with a h ha
  refine ⟨⟨s a, (hsinv a ha).2⟩, fun X hX => ?_⟩
  have h' : ∀ g, f (actU g (s a)) = f (actU g (s a₀)) := fun g => congrFun h g
  rw [horb a ha X hX, horb a₀ ha₀ X₀ hX₀]
  simp only [orbU, h']

theorem orbital_integrals_invariant_locally_constant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E), (∀ (f' : Gl r F → ℂ) (g : GL (Fin r) F) (Y : Gl r F), orbG M f' (act g Y) = orbG M f' Y) ∧ (∀ (f : Hn r F E → ℂ) (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E), orbU M f (actU g X) = orbU M f X) ∧ (∀ (f' : Gl r F → ℂ), IsTest f' → ∀ a₀ : Inv r F, Delta a₀ ≠ 0 → ∀ᶠ a in 𝓝 a₀, orbG M f' (sec a) = orbG M f' (sec a₀)) ∧ ∀ (f : Hn r F E → ℂ), IsTest f → ∀ (a₀ : Inv r F) (X₀ : Hn r F E), Delta a₀ ≠ 0 → HasInv X₀ a₀ → ∀ᶠ a in 𝓝 a₀, (∃ X : Hn r F E, HasInv X a) ∧ ∀ X : Hn r F E, HasInv X a → orbU M f X = orbU M f X₀ := by
  intro F E _ _ _ _ _ r M
  exact ⟨part1 F E r M, part2 F E r M, fun f' hf a₀ hΔ => part3 F E r M f' hf a₀ hΔ,
    fun f hf a₀ X₀ hΔ hX₀ => part4 F E r M f hf a₀ X₀ hΔ hX₀⟩

end GlobalTheory.JR.OrbLC
