import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalDecompositionNormal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellUnipotentUniquenessClosed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConjugationMeasureInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellFunctionCompactSupportUnipotentStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupOfFinset
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Rodier.RadInt

open MeasureTheory

theorem isLocallyConstant_of_right {X Y : Type} [TopologicalSpace X] [Group X] [IsTopologicalGroup X] (φ : X → Y)
    (S : Set X) (hS : IsOpen S) (h1 : (1 : X) ∈ S) (h : ∀ x, ∀ s ∈ S, φ (x * s) = φ x) : IsLocallyConstant φ := by
  refine (IsLocallyConstant.iff_eventually_eq φ).2 fun x => ?_
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' S) := hS.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (by simpa using h1)] with y hy
  have := h x _ hy
  simpa using this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} {d : Fin h → ℕ} {hd : ∑ a, d a = N}
variable {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

theorem unipU_le : unipU k d hd ≤ unipB k (Fin N) := inf_le_left

theorem unipL_le : unipL k d hd ≤ unipB k (Fin N) := inf_le_left

def thetaU (ψ : AddChar k Circle) : unipU k d hd →* ℂˣ :=
  (whitChar ψ N).comp (Subgroup.inclusion unipU_le)

def phi (ψ : AddChar k Circle) (f : IndSp (stdBlocks d hd) ρ) (u : unipU k d hd) : W :=
  (((thetaU ψ u)⁻¹ : ℂˣ) : ℂ) • f.1.1 (pm k (wOpen d hd) * u.1)

theorem phi_add (ψ : AddChar k Circle) (f g : IndSp (stdBlocks d hd) ρ) :
    phi ψ (f + g) = phi ψ f + phi ψ g := by
  funext u
  show _ • (f.1.1 _ + g.1.1 _) = _
  simp [phi, smul_add]

theorem phi_smul (ψ : AddChar k Circle) (c : ℂ) (f : IndSp (stdBlocks d hd) ρ) :
    phi ψ (c • f) = (c • LinearMap.id : W →ₗ[ℂ] W) ∘ phi ψ f := by
  funext u
  exact smul_comm _ c _

theorem isLocallyConstant_phi {ψ : AddChar k Circle} (hψ : Continuous ψ) (f : IndSp (stdBlocks d hd) ρ) :
    IsLocallyConstant (phi ψ f) := by
  have h1 : IsOpen {g | parInd (stdBlocks d hd) ρ g f = f} := isSmooth_parInd _ _ f
  have h2 : IsOpen ((whitChar ψ N).ker : Set (unipB k (Fin N))) := GlobalTheory.Whittaker.isSmoothChar_whitChar hψ
  have hi : Continuous (Subgroup.inclusion (unipU_le (k := k) (d := d) (hd := hd))) :=
    continuous_subtype_val.subtype_mk _
  refine isLocallyConstant_of_right _
    ((Subtype.val ⁻¹' {g | parInd (stdBlocks d hd) ρ g f = f}) ∩
      (Subgroup.inclusion (unipU_le (k := k) (d := d) (hd := hd)) ⁻¹' ((whitChar ψ N).ker : Set _)))
    ((h1.preimage continuous_subtype_val).inter (h2.preimage hi)) ?_ ?_
  · refine ⟨?_, ?_⟩
    · simp
    · simp [one_mem]
  · rintro x s ⟨hs1, hs2⟩
    have e1 : thetaU ψ s = 1 := hs2
    have e2 : f.1.1 (pm k (wOpen d hd) * x.1 * s.1) = f.1.1 (pm k (wOpen d hd) * x.1) := by
      have : parInd (stdBlocks d hd) ρ s.1 f = f := hs1
      conv_rhs => rw [← this]
      rfl
    simp only [phi, map_mul, e1, mul_one, Subgroup.coe_mul, ← mul_assoc, e2]

theorem isClosed_unipU : IsClosed (unipU k d hd : Set (GL (Fin N) k)) := (GlobalTheory.CompanionTheory.Rodier.unipU_open_cell k h N d hd).2.2

theorem hasCompactSupport_phi (ψ : AddChar k Circle) (hρ : IsSmooth ρ) (f : IndSp (stdBlocks d hd) ρ)
    (hf : f ∈ openFns d hd ρ) : HasCompactSupport (phi ψ f) := by
  obtain ⟨L, hLU, hLc, -, hL⟩ := GlobalTheory.T.open_cell_function_compact_support_unipotent k h N d hd ρ hρ f hf
  refine HasCompactSupport.of_support_subset_isCompact (K := Subtype.val ⁻¹' (L : Set (GL (Fin N) k)))
    ((isClosed_unipU (k := k) (d := d) (hd := hd)).isClosedEmbedding_subtypeVal.isCompact_preimage hLc) ?_
  intro u hu
  have h0 : f.1.1 (pm k (wOpen d hd) * u.1) ≠ 0 := by
    intro e
    exact hu (by simp [phi, e])
  obtain ⟨p, hp, l, hl, e⟩ := hL _ h0
  have := (GlobalTheory.CompanionTheory.Rodier.unipU_open_cell k h N d hd).2.1 p hp l (hLU hl) u.1 u.2 e.symm
  show u.1 ∈ L
  rw [← this]
  exact hl

variable [MeasurableSpace (unipU k d hd)] [BorelSpace (unipU k d hd)]

def conjU (n : GL (Fin N) k) (hn : n ∈ unipB k (Fin N)) (u : unipU k d hd) : unipU k d hd :=
  ⟨n * u.1 * n⁻¹, (GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad k h N d hd).2 n hn u.1 u.2⟩

theorem measurePreserving_conjU (μ : Measure (unipU k d hd)) [μ.IsHaarMeasure] (n : GL (Fin N) k)
    (hn : n ∈ unipB k (Fin N)) : MeasurePreserving (conjU (d := d) (hd := hd) n hn) μ μ := by
  refine GlobalTheory.CompanionTheory.HaarConj.conj_measurePreserving (unipU k d hd) (unipB k (Fin N)) isClosed_unipU (GlobalTheory.CompanionTheory.Rodier.unipB_eq_levi_mul_rad k h N d hd).2 ?_ μ n hn _
    fun _ => rfl
  intro n hn
  obtain ⟨L, h1, h2, h3⟩ := GlobalTheory.CompanionTheory.UnipExhaust.exists_compact_subgroup_of_finset k N {n} (by simpa using hn)
  exact ⟨L, h2 (by simp), h1, h3⟩

theorem measurePreserving_mul_right' (μ : Measure (unipU k d hd)) [μ.IsHaarMeasure] (u₀ : unipU k d hd) :
    MeasurePreserving (fun u => u * u₀) μ μ := by
  have h1 := measurePreserving_conjU μ (u₀.1)⁻¹ (inv_mem (unipU_le u₀.2))
  have h2 := measurePreserving_mul_left μ u₀
  convert h2.comp h1 using 1
  funext u
  apply Subtype.ext
  simp [conjU, mul_assoc]

theorem smInt_comp {X W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [AddCommGroup W'] [Module ℂ W'] (T : W →ₗ[ℂ] W') (c : X → X) (φ : X → W)
    (hc : MeasurePreserving c μ μ) (h1 : IsLocallyConstant φ) (h2 : HasCompactSupport φ) :
    smInt μ (fun x => T (φ (c x))) = T (smInt μ φ) := by
  have a := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W) (W' := W') μ).2.1 T φ h1 h2
  have b := (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W') (W' := W') μ).2.2.1 c (T ∘ φ) hc (h1.comp T)
  rw [← a, ← b]
  rfl

def radInt {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd)) [μ.IsHaarMeasure] :
    openFns d hd ρ →ₗ[ℂ] W where
  toFun f := smInt μ (phi ψ f.1)
  map_add' f g := by
    show smInt μ (phi ψ (f.1 + g.1)) = _
    rw [phi_add]
    exact (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W) (W' := W) μ).1 _ _ (isLocallyConstant_phi hψ _)
      (hasCompactSupport_phi ψ hρ _ f.2) (isLocallyConstant_phi hψ _) (hasCompactSupport_phi ψ hρ _ g.2)
  map_smul' c f := by
    show smInt μ (phi ψ (c • f.1)) = _
    rw [phi_smul]
    exact (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W) (W' := W) μ).2.1 _ _ (isLocallyConstant_phi hψ _)
      (hasCompactSupport_phi ψ hρ _ f.2)

theorem phi_right (ψ : AddChar k Circle) (f f' : IndSp (stdBlocks d hd) ρ) (u₀ : unipU k d hd)
    (hf' : f' = parInd (stdBlocks d hd) ρ u₀.1 f) :
    phi ψ f' = fun x => (((thetaU ψ u₀ : ℂˣ) : ℂ) • LinearMap.id : W →ₗ[ℂ] W) (phi ψ f (x * u₀)) := by
  subst hf'
  funext x
  have e : ((thetaU ψ x)⁻¹ : ℂˣ) = thetaU ψ u₀ * (thetaU ψ (x * u₀))⁻¹ := by
    rw [map_mul, mul_inv, mul_left_comm, mul_inv_cancel, mul_one]
  have e2 : (parInd (stdBlocks d hd) ρ u₀.1 f).1.1 (pm k (wOpen d hd) * x.1) =
      f.1.1 (pm k (wOpen d hd) * (x * u₀).1) := by
    rw [parInd_apply, Subgroup.coe_mul, mul_assoc]
  show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • (parInd (stdBlocks d hd) ρ u₀.1 f).1.1 (pm k (wOpen d hd) * x.1) =
    ((thetaU ψ u₀ : ℂˣ) : ℂ) • ((((thetaU ψ (x * u₀))⁻¹ : ℂˣ) : ℂ) • f.1.1 (pm k (wOpen d hd) * (x * u₀).1))
  rw [e, e2, Units.val_mul, mul_smul]

theorem radInt_right {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd))
    [μ.IsHaarMeasure] (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N))
    (f f' : openFns d hd ρ) (hf : (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f) :
    radInt hψ hρ μ f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • radInt hψ hρ μ f := by
  have key := smInt_comp μ (((thetaU ψ ⟨u, hu⟩ : ℂˣ) : ℂ) • LinearMap.id : W →ₗ[ℂ] W) (fun x => x * ⟨u, hu⟩)
    (phi ψ f.1) (measurePreserving_mul_right' μ _) (isLocallyConstant_phi hψ _) (hasCompactSupport_phi ψ hρ _ f.2)
  show smInt μ (phi ψ f'.1) = _
  rw [phi_right ψ f.1 f'.1 ⟨u, hu⟩ hf, key]
  rfl

theorem deltaHalf_unipM (m : unipM k d) : deltaHalf k (fun a => Fin (d a)) m.1 = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [det_eq_one_of_mem_unipRad k (e := points (Fin (d a))) (m.2 a (Set.mem_univ a)), map_one]

theorem thetaU_conjU (ψ : AddChar k Circle) (n : GL (Fin N) k) (hn : n ∈ unipB k (Fin N)) (x : unipU k d hd) :
    thetaU ψ (conjU n hn x) = thetaU ψ x := by
  have e : Subgroup.inclusion (unipU_le (k := k) (d := d) (hd := hd)) (conjU n hn x) =
      (⟨n, hn⟩ : unipB k (Fin N)) * Subgroup.inclusion unipU_le x * (⟨n, hn⟩ : unipB k (Fin N))⁻¹ := rfl
  show whitChar ψ N (Subgroup.inclusion _ _) = whitChar ψ N (Subgroup.inclusion _ _)
  rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem phi_levi (ψ : AddChar k Circle) (f f' : IndSp (stdBlocks d hd) ρ) (a : GL (Fin N) k)
    (ha : a ∈ unipL k d hd) (m : unipM k d)
    (hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1)
    (hf' : f' = parInd (stdBlocks d hd) ρ a f) :
    phi ψ f' = fun x => ρ m.1 (phi ψ f (conjU a⁻¹ (inv_mem (unipL_le ha)) x)) := by
  subst hf'
  funext x
  have e1 : pm k (wOpen d hd) * x.1 * a = leviEmb k (stdBlocks d hd) m.1 *
      (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1) := by
    rw [← hm]
    show _ = pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ * (pm k (wOpen d hd) * (a⁻¹ * x.1 * a⁻¹⁻¹))
    group
  have e2 := parInd_law (stdBlocks d hd) ρ f
    ⟨leviEmb k (stdBlocks d hd) m.1, leviEmb_mem_parab k (stdBlocks d hd) m.1⟩
    (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1)
  rw [leviProj_leviEmb, deltaHalf_unipM m, Units.val_one, one_smul] at e2
  show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • (parInd (stdBlocks d hd) ρ a f).1.1 (pm k (wOpen d hd) * x.1) =
    ρ m.1 ((((thetaU ψ (conjU a⁻¹ (inv_mem (unipL_le ha)) x))⁻¹ : ℂˣ) : ℂ) •
      f.1.1 (pm k (wOpen d hd) * (conjU (d := d) (hd := hd) a⁻¹ (inv_mem (unipL_le ha)) x).1))
  rw [parInd_apply, e1, thetaU_conjU, map_smul]
  exact congrArg _ e2

theorem radInt_levi {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd))
    [μ.IsHaarMeasure] (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d)
    (hm : pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1)
    (f f' : openFns d hd ρ) (hf : (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f) :
    radInt hψ hρ μ f' = ρ m.1 (radInt hψ hρ μ f) := by
  have key := smInt_comp μ (ρ m.1) (conjU a⁻¹ (inv_mem (unipL_le ha))) (phi ψ f.1)
    (measurePreserving_conjU μ _ _) (isLocallyConstant_phi hψ _) (hasCompactSupport_phi ψ hρ _ f.2)
  show smInt μ (phi ψ f'.1) = _
  rw [phi_levi ψ f.1 f'.1 a ha m hm hf, key]
  rfl

def volU (μ : Measure (unipU k d hd)) (L₀ : Subgroup (GL (Fin N) k)) : ℝ :=
  (μ (Subtype.val ⁻¹' (L₀ : Set (GL (Fin N) k)))).toReal

theorem radInt_indicator {ψ : AddChar k Circle} (hψ : Continuous ψ) (hρ : IsSmooth ρ) (μ : Measure (unipU k d hd))
    [μ.IsHaarMeasure] (L₀ : Subgroup (GL (Fin N) k)) (hLU : L₀ ≤ unipU k d hd) (hLc : IsCompact (L₀ : Set (GL (Fin N) k)))
    (hLo : ∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) :
    0 < volU μ L₀ ∧ ∀ (f : openFns d hd ρ) (v : W),
      (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) →
      (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → radInt hψ hρ μ f = (volU μ L₀ : ℂ) • v := by
  set A : Set (unipU k d hd) := Subtype.val ⁻¹' (L₀ : Set (GL (Fin N) k)) with hA
  have hAc : IsCompact A :=
    (isClosed_unipU (k := k) (d := d) (hd := hd)).isClosedEmbedding_subtypeVal.isCompact_preimage hLc
  have hAo : IsOpen A := by
    obtain ⟨O, hO, e⟩ := hLo
    have : A = Subtype.val ⁻¹' O := by
      ext x
      simp only [hA, Set.mem_preimage, SetLike.mem_coe, ← e, Set.mem_inter_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    rw [this]
    exact hO.preimage continuous_subtype_val
  refine ⟨?_, fun f v h1 h2 => ?_⟩
  · have hne : A.Nonempty := ⟨1, one_mem L₀⟩
    exact ENNReal.toReal_pos (hAo.measure_pos μ hne).ne' hAc.measure_lt_top.ne
  · have e : phi ψ f.1 = A.indicator fun _ => v := by
      funext x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • f.1.1.1 (pm k (wOpen d hd) * x.1) = v
        rw [h1 x.1 (unipU_le x.2) hx, smul_smul]
        have : (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) * ((thetaU ψ x : ℂˣ) : ℂ) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        exact (congrArg (· • v) this).trans (one_smul _ _)
      · rw [Set.indicator_of_notMem hx]
        show (((thetaU ψ x)⁻¹ : ℂˣ) : ℂ) • f.1.1.1 (pm k (wOpen d hd) * x.1) = 0
        rw [h2 x.1 x.2 hx, smul_zero]
    show smInt μ (phi ψ f.1) = _
    rw [e]
    exact (GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_properties (W := W) (W' := W) μ).2.2.2 A v hAc hAo hAc.isClosed

end GlobalTheory.CompanionTheory.Rodier.RadInt

theorem GlobalTheory.CompanionTheory.Rodier.radical_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W), IsSmooth ρ → ∃ (J : openFns d hd ρ →ₗ[ℂ] W) (vol : Subgroup (GL (Fin N) k) → ℝ), (∀ (u : GL (Fin N) k) (hu : u ∈ unipU k d hd) (hb : u ∈ unipB k (Fin N)) (f f' : openFns d hd ρ), (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ u f → J f' = (whitChar ψ N ⟨u, hb⟩ : ℂ) • J f) ∧ (∀ (a : GL (Fin N) k) (ha : a ∈ unipL k d hd) (m : unipM k d), pm k (wOpen d hd) * a * (pm k (wOpen d hd))⁻¹ = leviEmb k (stdBlocks d hd) m.1 → ∀ f f' : openFns d hd ρ, (f' : IndSp (stdBlocks d hd) ρ) = parInd (stdBlocks d hd) ρ a f → J f' = ρ m.1 (J f)) ∧ ∀ L₀ : Subgroup (GL (Fin N) k), L₀ ≤ unipU k d hd → IsCompact (L₀ : Set (GL (Fin N) k)) → (∃ O : Set (GL (Fin N) k), IsOpen O ∧ O ∩ (unipU k d hd : Set (GL (Fin N) k)) = L₀) → 0 < vol L₀ ∧ ∀ (f : openFns d hd ρ) (v : W), (∀ (u : GL (Fin N) k) (hb : u ∈ unipB k (Fin N)), u ∈ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = (whitChar ψ N ⟨u, hb⟩ : ℂ) • v) → (∀ u ∈ unipU k d hd, u ∉ L₀ → f.1.1.1 (pm k (wOpen d hd) * u) = 0) → J f = (vol L₀ : ℂ) • v := by
  intro k _ _ _ _ ψ hψ h N d hd W _ _ ρ hρ
  letI : MeasurableSpace (unipU k d hd) := borel _
  haveI : BorelSpace (unipU k d hd) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unipU k d hd) :=
    (RadInt.isClosed_unipU (k := k) (d := d) (hd := hd)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : MeasureTheory.Measure (unipU k d hd) := MeasureTheory.Measure.haar
  exact ⟨RadInt.radInt hψ hρ μ, RadInt.volU μ,
    fun u hu hb f f' hf => RadInt.radInt_right hψ hρ μ u hu hb f f' hf,
    fun a ha m hm f f' hf => RadInt.radInt_levi hψ hρ μ a ha m hm f f' hf,
    fun L₀ h1 h2 h3 => RadInt.radInt_indicator hψ hρ μ L₀ h1 h2 h3⟩
