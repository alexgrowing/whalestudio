import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicLatticeOpenCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorAdelicLatticeCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxFourierIntegralBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicVectorIntegralProductStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteVectorMeasureIsAddHaarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterRealPairingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiffStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

section Gen

variable {R : Type} [CommRing R] {k : ℕ}

theorem eventually_rowGL [TopologicalSpace R] [IsTopologicalRing R]
    (hU : ∀ᶠ x in 𝓝 (1 : R), IsUnit x) (hinv : ContinuousAt Ring.inverse (1 : R)) (hk : 1 ≤ k)
    {W : Set (GL (Fin k) R)} (hW : W ∈ 𝓝 (1 : GL (Fin k) R)) :
    ∀ᶠ r in 𝓝 (eRow R k), IsUnit (lastEnt r) ∧ rowGL r ∈ W := by
  have hl : Continuous (lastEnt : (Fin k → R) → R) := by
    refine continuous_finset_sum _ fun c _ => ?_
    split_ifs
    · exact continuous_apply c
    · exact continuous_const
  have h1 : lastEnt (eRow R k) = 1 := lastEnt_eRow hk
  have hM : Continuous (rowM : (Fin k → R) → Matrix (Fin k) (Fin k) R) := by
    refine continuous_pi fun i => continuous_pi fun c => ?_
    simp only [rowM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply c
    · exact continuous_const
  have hinv' : ContinuousAt (fun r : Fin k → R => Ring.inverse (lastEnt r)) (eRow R k) :=
    ContinuousAt.comp (f := lastEnt) (g := Ring.inverse) (by rw [h1]; exact hinv) hl.continuousAt
  have hI : ContinuousAt (rowI : (Fin k → R) → Fin k → R) (eRow R k) := by
    refine continuousAt_pi.2 fun c => ?_
    simp only [rowI]
    split_ifs
    · exact hinv'
    · exact (((continuous_apply c).continuousAt).mul hinv').neg
  have hu : ∀ᶠ r in 𝓝 (eRow R k), IsUnit (lastEnt r) :=
    (hl.tendsto (eRow R k)).eventually (by rw [h1]; exact hU)
  have hIe : rowM (rowI (eRow R k)) = 1 := by
    have h := rowM_mul_rowI (r := eRow R k) (by rw [h1]; exact isUnit_one)
    rwa [rowM_eRow, one_mul] at h
  have hind := Units.isEmbedding_embedProduct (M := Matrix (Fin k) (Fin k) R) |>.isInducing
  rw [hind.nhds_eq_comap] at hW
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hW
  have hT : Tendsto (fun r : Fin k → R => (rowM r, MulOpposite.op (rowM (rowI r)))) (𝓝 (eRow R k))
      (𝓝 (Units.embedProduct _ (1 : GL (Fin k) R))) := by
    have e : Units.embedProduct _ (1 : GL (Fin k) R) =
        (rowM (eRow R k), MulOpposite.op (rowM (rowI (eRow R k)))) := by
      rw [hIe, rowM_eRow]; rfl
    rw [e]
    exact ((hM.tendsto _).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp ((hM.tendsto _).comp hI)))
  filter_upwards [hu, hT.eventually_mem ht] with r h1 h2
  refine ⟨h1, hts ?_⟩
  change Units.embedProduct _ (rowGL r) ∈ t
  have e : Units.embedProduct _ (rowGL r) = (rowM r, MulOpposite.op (rowM (rowI r))) := by
    refine Prod.ext (rowGL_val h1) ?_
    exact congrArg MulOpposite.op (rowGL_inv_val h1)
  rw [e]
  exact h2

end Gen

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem exists_openSub (w : Pl E) {N : Set (w.adicCompletion E)} (hN : N ∈ 𝓝 (0 : w.adicCompletion E)) :
    ∃ B : AddSubgroup (w.adicCompletion E), IsOpen (B : Set (w.adicCompletion E)) ∧
      (B : Set (w.adicCompletion E)) ⊆ N ∧ (B : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E)) := by
  have hO : (Formalism.UG.Ov E w : Set (w.adicCompletion E)) ∈ 𝓝 (0 : w.adicCompletion E) :=
    (Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ (Filter.inter_mem hN hO)
  exact ⟨V.toAddSubgroup, V.isOpen, fun x hx => (hV hx).1, fun x hx => (hV hx).2⟩

theorem cInf_prod (h0 : PositivityTheory.jumpWindows.G0) (l : List (Pl E)) (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) :
    cInf (l.map fun w => fl k w (u w)).prod = 1 := by
  obtain ⟨-, -, hIF, -⟩ := h0 E k
  induction l with
  | nil => simp
  | cons w t ih => simp [ih, hIF]

theorem cLoc_prod_not (h0 : PositivityTheory.jumpWindows.G0) (l : List (Pl E)) (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E))
    (v : Pl E) (hv : v ∉ l) : cLoc v (l.map fun w => fl k w (u w)).prod = 1 := by
  obtain ⟨-, -, -, -, hLN, -⟩ := h0 E k
  induction l with
  | nil => simp
  | cons w t ih =>
    have h1 : v ≠ w := fun h => hv (h ▸ List.mem_cons_self)
    have h2 : v ∉ t := fun h => hv (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, List.prod_cons, map_mul, ih h2, hLN w v _ h1, one_mul]

theorem cLoc_prod_mem (h0 : PositivityTheory.jumpWindows.G0) (l : List (Pl E)) (hl : l.Nodup)
    (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) (v : Pl E) (hv : v ∈ l) :
    cLoc v (l.map fun w => fl k w (u w)).prod = u v := by
  have h0' := h0
  obtain ⟨-, -, -, hLL, hLN, -⟩ := h0 E k
  induction l with
  | nil => simp at hv
  | cons w t ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.prod_cons, map_mul]
    by_cases hvw : v = w
    · subst hvw
      rw [hLL, cLoc_prod_not h0' t u v hl.1, mul_one]
    · rw [hLN w v _ hvw, one_mul]
      exact ih hl.2 (List.mem_of_ne_of_mem hvw hv)

theorem glue_cInf (h0 : PositivityTheory.jumpWindows.G0) (S : Finset (Pl E)) (a : GL (Fin k) (Cinf E))
    (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) : cInf (glue S a u) = a := by
  have h0' := h0
  obtain ⟨hII, -⟩ := h0 E k
  rw [glue, map_mul, cInf_prod h0', hII, one_mul]

theorem glue_cLoc_mem (h0 : PositivityTheory.jumpWindows.G0) (S : Finset (Pl E)) (a : GL (Fin k) (Cinf E))
    (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) (w : Pl E) (hw : w ∈ S) : cLoc w (glue S a u) = u w := by
  have h0' := h0
  obtain ⟨-, hLI, -⟩ := h0 E k
  rw [glue, map_mul, hLI, mul_one, cLoc_prod_mem h0' _ S.nodup_toList u w (Finset.mem_toList.2 hw)]

theorem glue_cLoc_not (h0 : PositivityTheory.jumpWindows.G0) (S : Finset (Pl E)) (a : GL (Fin k) (Cinf E))
    (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) (w : Pl E) (hw : w ∉ S) : cLoc w (glue S a u) = 1 := by
  have h0' := h0
  obtain ⟨-, hLI, -⟩ := h0 E k
  rw [glue, map_mul, hLI, mul_one, cLoc_prod_not h0' _ u w (fun h => hw (Finset.mem_toList.1 h))]

theorem glue_congr (S : Finset (Pl E)) (a : GL (Fin k) (Cinf E))
    (u u' : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) (h : ∀ w ∈ S, u w = u' w) : glue S a u = glue S a u' := by
  rw [glue, glue]
  congr 2
  exact List.map_congr_left fun w hw => by rw [h w (Finset.mem_toList.1 hw)]

theorem prod_rt (l : List (Pl E)) (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) (φ : XB E k)
    (h : ∀ w ∈ l, repW k w (u w) φ = φ) : Rt E k (l.map fun w => fl k w (u w)).prod φ = φ := by
  induction l with
  | nil => simp
  | cons w t ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ContinuousLinearMap.mul_apply]
    rw [ih fun v hv => h v (List.mem_cons_of_mem _ hv)]
    exact h w List.mem_cons_self

theorem glue_rt (S : Finset (Pl E)) (a : GL (Fin k) (Cinf E))
    (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) (φ : XB E k) (h : ∀ w ∈ S, repW k w (u w) φ = φ) (g : GA E k) :
    φ (g * (glue S a u)⁻¹) = φ (g * (infGL E k a)⁻¹) := by
  set P := (S.toList.map fun w => fl k w (u w)).prod with hP
  have h1 : Rt E k P φ = φ := prod_rt _ u φ fun w hw => h w (Finset.mem_toList.1 hw)
  have h2 : Rt E k P⁻¹ φ = φ := by
    conv_lhs => rw [← h1]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have e : φ (g * (glue S a u)⁻¹) = Rt E k P⁻¹ φ (g * (infGL E k a)⁻¹) := by
    rw [Rt_apply, glue, _root_.mul_inv_rev, mul_assoc]
  rw [e, h2]

theorem prod_nhds (h0 : PositivityTheory.jumpWindows.G0) (l : List (Pl E)) {W : Set (GA E k)} (hW : W ∈ 𝓝 (1 : GA E k)) :
    ∃ N : ∀ w : Pl E, Set (GL (Fin k) (w.adicCompletion E)), (∀ w, N w ∈ 𝓝 (1 : GL (Fin k) (w.adicCompletion E))) ∧
      ∀ u : (∀ w : Pl E, GL (Fin k) (w.adicCompletion E)), (∀ w ∈ l, u w ∈ N w) →
        (l.map fun w => fl k w (u w)).prod ∈ W := by
  have hfl : ∀ w : Pl E, Continuous (fl k w : GL (Fin k) (w.adicCompletion E) → GA E k) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hF, -⟩ := h0 E k
    exact hF
  induction l generalizing W with
  | nil => exact ⟨fun _ => Set.univ, fun _ => Filter.univ_mem, fun _ _ => by simpa using mem_of_mem_nhds hW⟩
  | cons w t ih =>
    obtain ⟨V, hV, hVV⟩ := exists_nhds_one_split hW
    obtain ⟨N, hN, hu⟩ := ih hV
    refine ⟨fun v => N v ∩ (fl k v) ⁻¹' V, fun v => Filter.inter_mem (hN v) ?_, fun u h => ?_⟩
    · refine (hfl v).continuousAt.preimage_mem_nhds ?_
      rw [map_one]; exact hV
    · simp only [List.map_cons, List.prod_cons]
      exact hVV _ (h w List.mem_cons_self).2 _ (hu u fun v hv => (h v (List.mem_cons_of_mem _ hv)).1)

theorem glue_nhds (h0 : PositivityTheory.jumpWindows.G0) (S : Finset (Pl E)) {W : Set (GA E k)} (hW : W ∈ 𝓝 (1 : GA E k)) :
    ∃ Wi ∈ 𝓝 (1 : GL (Fin k) (Cinf E)), ∃ N : ∀ w : Pl E, Set (GL (Fin k) (w.adicCompletion E)),
      (∀ w, N w ∈ 𝓝 (1 : GL (Fin k) (w.adicCompletion E))) ∧
        ∀ a ∈ Wi, ∀ u : (∀ w : Pl E, GL (Fin k) (w.adicCompletion E)), (∀ w ∈ S, u w ∈ N w) → glue S a u ∈ W := by
  have hi : Continuous (infGL E k) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hI⟩ := h0 E k
    exact hI
  obtain ⟨V, hV, hVV⟩ := exists_nhds_one_split hW
  obtain ⟨N, hN, hu⟩ := prod_nhds h0 S.toList hV
  refine ⟨infGL E k ⁻¹' V, hi.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hV), N, hN, fun a ha u h => ?_⟩
  exact hVV _ (hu u fun w hw => h w (Finset.mem_toList.1 hw)) _ ha

theorem inf_ft (h4 : S4) (h8 : S8) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {φ : XB E k} (hφ : SmV (repI E k) φ)
    {b : (Fin k → Cinf E) → ℝ} (hb : ContDiff ℝ ∞ b) (hc : HasCompactSupport b)
    (hu : ∀ x ∈ tsupport b, IsUnit (lastEnt x)) (M : ℕ) :
    ∃ C : ℝ, ∀ (z : Fin k → Cinf E) (g : GA E k),
      ‖∫ x, (b x : ℂ) * φ (g * (infGL E k (rowGL x))⁻¹) * ψ (sInf E (∑ i, x i * z i)) ∂nuInf E k‖ ≤
        C * ((1 + ‖z‖) ^ M)⁻¹ := by
  obtain ⟨β, hβ, hψβ⟩ := GlobalTheory.T.archimedean_character_real_pairing (E := E) (k := k) h8 hψ
  haveI := GlobalTheory.T.infinite_vector_measure_isAddHaar E k
  set F : (Fin k → Cinf E) → XB E k := fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ with hF
  have hFs : ContDiff ℝ ∞ F := GlobalTheory.T.smooth_cutoff_translate_contDiff hφ hb hu
  have hFc : HasCompactSupport F := by
    refine HasCompactSupport.mono hc fun x hx h0 => hx ?_
    simp only [hF]
    rw [h0]
    simp
  obtain ⟨-, hdec⟩ := h4 (Fin k → Cinf E) (nuInf E k) β hβ (XB E k) F hFs hFc
  obtain ⟨C, hC⟩ := hdec M
  refine ⟨C, fun z g => ?_⟩
  have hint : Integrable (fun x => Complex.exp (-(β x z : ℝ) * Complex.I) • F x) (nuInf E k) := by
    have hcs : HasCompactSupport (fun x => Complex.exp (-(β x z : ℝ) * Complex.I) • F x) :=
      HasCompactSupport.mono hFc fun x hx h0 => hx (by
        change Complex.exp (-(β x z : ℝ) * Complex.I) • F x = 0
        rw [h0, smul_zero])
    have hex : Continuous fun x : Fin k → Cinf E => Complex.exp (-(β x z : ℝ) * Complex.I) := by
      have : Continuous fun x : Fin k → Cinf E => β x z := (β.flip z).continuous
      fun_prop
    have hcont : Continuous fun x => Complex.exp (-(β x z : ℝ) * Complex.I) • F x := hex.smul hFs.continuous
    exact hcont.integrable_of_hasCompactSupport hcs
  have key : ∫ x, (b x : ℂ) * φ (g * (infGL E k (rowGL x))⁻¹) * ψ (sInf E (∑ i, x i * z i)) ∂nuInf E k =
      FT (nuInf E k) β F z g := by
    have e := (BoundedContinuousFunction.evalCLM ℂ g).integral_comp_comm hint
    rw [FT]
    refine Eq.trans ?_ e
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hψβ, hF]
    simp [BoundedContinuousFunction.evalCLM, mul_comm, mul_assoc]
  rw [key]
  have h1 : (0 : ℝ) < (1 + ‖z‖) ^ M := by positivity
  refine (BoundedContinuousFunction.norm_coe_le_norm _ g).trans ?_
  rw [← div_eq_mul_inv, le_div_iff₀ h1, mul_comm]
  exact hC z

end GlobalTheory.CompanionTheory.CutOff

namespace GlobalTheory.CompanionTheory.CutOff

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem lastRowM_map {R T : Type} [CommRing R] [CommRing T] (p : R →+* T) (A : GL (Fin k) R) (c : Fin k) :
    p (lastRowM A.val c) = lastRowM (GeneralLinearGroup.map p A).val c := by
  simp only [lastRowM, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · exact map_zero p

theorem lastRowM_one {R : Type} [CommRing R] : lastRowM (1 : Matrix (Fin k) (Fin k) R) = eRow R k := by
  funext c
  by_cases hc : (c : ℕ) + 1 = k
  · rw [lastRowM, Finset.sum_eq_single c]
    · simp [hc, eRow]
    · intro b _ hb
      split_ifs
      · exact Matrix.one_apply_ne hb
      · rfl
    · simp
  · rw [lastRowM, eRow, if_neg hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h
    · exact Matrix.one_apply_ne (fun e : i = c => hc (e ▸ h))
    · rfl

theorem map_eRow {R T : Type} [CommRing R] [CommRing T] (p : R →+* T) (c : Fin k) : p (eRow R k c) = eRow T k c := by
  simp only [eRow]
  split_ifs
  · exact map_one p
  · exact map_zero p

theorem boxL_isClopen {L : Set (Af E)} (h1 : IsOpen L) (h2 : IsClosed L) (c : Fin k → Af E) :
    IsClopen (boxL L c) := by
  have e : boxL L c = ⋂ i, (fun f : Fin k → Af E => f i - c i) ⁻¹' L := by
    ext f; simp [boxL]
  rw [e]
  exact isClopen_iInter_of_finite fun i =>
    (IsClopen.preimage ⟨h2, h1⟩ ((continuous_apply i).sub continuous_const))

theorem boxL_isCompact {L : Set (Af E)} (h : IsCompact L) (c : Fin k → Af E) : IsCompact (boxL L c) := by
  have e : boxL L c = Set.pi Set.univ fun i => (fun t => t + c i) '' L := by
    ext f
    simp only [boxL, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_image]
    exact forall_congr' fun i => ⟨fun hf => ⟨_, hf, by simp⟩, by rintro ⟨t, ht, e⟩; rw [← e]; simpa using ht⟩
  rw [e]
  exact isCompact_univ_pi fun i => h.image (continuous_id.add continuous_const)

theorem etaOf_ne {b : (Fin k → Cinf E) → ℝ} {L : Set (Af E)} {y : Fin k → Ad E} (h : etaOf b L y ≠ 0) :
    b (fun i => pInf E (y i)) ≠ 0 ∧ (fun i => pFin E (y i)) ∈ boxL L (eRow (Af E) k) := by
  have h2 : (fun i => pFin E (y i)) ∈ boxL L (eRow (Af E) k) := by
    by_contra h3
    exact h (by rw [etaOf, Set.indicator_of_notMem h3, mul_zero])
  exact ⟨fun h3 => h (by rw [etaOf, h3, zero_mul]), h2⟩

theorem etaOf_eq {b : (Fin k → Cinf E) → ℝ} {L : Set (Af E)} {y : Fin k → Ad E}
    (h : (fun i => pFin E (y i)) ∈ boxL L (eRow (Af E) k)) : etaOf b L y = b (fun i => pInf E (y i)) := by
  rw [etaOf, Set.indicator_of_mem h, mul_one]

theorem continuous_etaOf {b : (Fin k → Cinf E) → ℝ} (hb : Continuous b) {L : Set (Af E)} (h1 : IsOpen L)
    (h2 : IsClosed L) : Continuous (etaOf (k := k) b L) := by
  have hp : Continuous fun y : Fin k → Ad E => fun i => pInf E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (continuous_apply i)
  have hf : Continuous fun y : Fin k → Ad E => fun i => pFin E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pFin E).comp (continuous_apply i)
  have hi : Continuous ((boxL L (eRow (Af E) k)).indicator (fun _ => (1 : ℝ))) :=
    (IsClopen.continuous_indicator (boxL_isClopen h1 h2 _) continuous_const)
  exact (hb.comp hp).mul (hi.comp hf)

theorem hasCompactSupport_etaOf {b : (Fin k → Cinf E) → ℝ} (hb : HasCompactSupport b) {L : Set (Af E)}
    (h : IsCompact L) : HasCompactSupport (etaOf (k := k) b L) := by
  let Ψ : (Fin k → Cinf E) × (Fin k → Af E) → (Fin k → Ad E) :=
    fun p i => ((infEq E (p.1 i), p.2 i) : InfiniteAdeleRing E × Af E)
  have hΨ : Continuous Ψ := continuous_pi fun i =>
    (((continuous_infEq E).comp (by fun_prop : Continuous fun p : (Fin k → Cinf E) × (Fin k → Af E) => p.1 i)).prodMk
      (by fun_prop : Continuous fun p : (Fin k → Cinf E) × (Fin k → Af E) => p.2 i) :)
  refine HasCompactSupport.intro (((hb.isCompact).prod (boxL_isCompact h (eRow (Af E) k))).image hΨ) fun y hy => ?_
  by_contra h0
  obtain ⟨h1, h2⟩ := etaOf_ne h0
  refine hy ⟨((fun i => pInf E (y i)), fun i => pFin E (y i)), ⟨subset_tsupport _ h1, h2⟩, ?_⟩
  funext i
  exact ad_ext ((infEq E).symm_apply_apply _) rfl

theorem pLoc_sLoc_self (w : Pl E) (t : w.adicCompletion E) : pLoc E w (sLoc E w t) = t := by
  classical
  change (Pi.single w t : ∀ v : Pl E, v.adicCompletion E) w = t
  simp

theorem pLoc_sLoc_ne {v w : Pl E} (h : v ≠ w) (t : w.adicCompletion E) : pLoc E v (sLoc E w t) = 0 := by
  classical
  change (Pi.single w t : ∀ v : Pl E, v.adicCompletion E) v = 0
  simp [h]

theorem eRow_mem_Ov (w : Pl E) (i : Fin k) : eRow (w.adicCompletion E) k i ∈ Formalism.UG.Ov E w := by
  simp only [eRow]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem ad_split (a : Ad E) : a = sInf E (pInf E a) + sFin E (pFin E a) :=
  Prod.ext (by
    change a.1 = infEq E ((infEq E).symm a.1) + 0
    simp) (by
    change a.2 = 0 + a.2
    simp)

theorem cut_of (h0 : PositivityTheory.jumpWindows.G0) (h4 : S4) (h8 : S8) (hk : 1 ≤ k) {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ)
    {S : Finset (Pl E)} (hS : ∀ w, w ∉ S → Cond ψ w) {U C₀ : Set (GA E k)} (hC : IsCompact C₀) (hCU : C₀ ⊆ U)
    {φ : XB E k} (hφ : SmV (repI E k) φ) {b : (Fin k → Cinf E) → ℝ} (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (hb0 : ∀ x, 0 ≤ b x) (hbe : 0 < b (eRow _ k)) (hbz : b 0 = 0)
    (hbu : ∀ x ∈ tsupport b, IsUnit (lastEnt x)) {B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)}
    (hBo : ∀ w ∈ S, IsOpen (B w : Set (w.adicCompletion E)))
    (hBI : ∀ w ∈ S, (B w : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E)))
    (hBu : ∀ w ∈ S, ∀ t : Fin k → w.adicCompletion E, (∀ i, t i - eRow _ k i ∈ B w) →
      IsUnit (lastEnt t) ∧ repW k w (rowGL t) φ = φ)
    (hsm : ∀ y, etaOf b (latS S B : Set (Af E)) y ≠ 0 → sOf S y ∈ C₀) :
    Cut ψ S U φ (etaOf b (latS S B : Set (Af E))) (sOf S) := by
  obtain ⟨hLo, hLc⟩ := GlobalTheory.T.finite_adelic_lattice_open_compact S B hBo hBI
  have hLcl : IsClosed (latS S B : Set (Af E)) := AddSubgroup.isClosed_of_isOpen _ hLo
  have hf : Continuous fun y : Fin k → Ad E => fun i => pFin E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pFin E).comp (continuous_apply i)
  have hp : Continuous fun y : Fin k → Ad E => fun i => pInf E (y i) :=
    continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (continuous_apply i)
  have hloc : ∀ y, etaOf b (latS S B : Set (Af E)) y ≠ 0 → ∀ w ∈ S, ∀ i,
      pLoc E w (pFin E (y i)) - eRow _ k i ∈ B w := fun y hy w hw i => by
    have h := ((etaOf_ne hy).2 i).2 w hw
    rwa [map_sub, map_eRow] at h
  have hrt : ∀ y g, etaOf b (latS S B : Set (Af E)) y ≠ 0 →
      φ (g * (sOf S y)⁻¹) = φ (g * (infGL E k (rowGL fun i => pInf E (y i)))⁻¹) := fun y g hy =>
    glue_rt S _ _ φ (fun w hw => (hBu w hw _ (hloc y hy w hw)).2) g
  have hcast : ∀ y, ((etaOf b (latS S B : Set (Af E)) y : ℝ) : ℂ) = (b (fun i => pInf E (y i)) : ℂ) *
      (((boxL (latS S B : Set (Af E)) (eRow (Af E) k)).indicator (fun _ => (1 : ℝ)) fun i => pFin E (y i) : ℝ) : ℂ) := by
    intro y
    rw [etaOf, Complex.ofReal_mul]
  have hind : Continuous ((boxL (latS S B : Set (Af E)) (eRow (Af E) k)).indicator (fun _ => (1 : ℝ))) :=
    IsClopen.continuous_indicator (boxL_isClopen hLo hLcl _) continuous_const
  refine ⟨fun y => mul_nonneg (hb0 _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _),
    continuous_etaOf hb.continuous hLo hLcl, hasCompactSupport_etaOf hbc hLc, ?_, ?_, ?_,
    ⟨C₀, hC, hCU, fun y hy => ⟨hsm y hy, fun w hw => glue_cLoc_not h0 _ _ _ w hw⟩⟩, ?_, ?_, ?_, ?_⟩
  · have e : (fun i => pInf E ((0 : Fin k → Ad E) i)) = 0 := by
      funext i
      exact map_zero _
    rw [etaOf, e, hbz, zero_mul]
  ·
    have hF := (GlobalTheory.T.smooth_cutoff_translate_contDiff hφ hb hbu).continuous
    have e : (fun y : Fin k → Ad E => ((etaOf b (latS S B : Set (Af E)) y : ℝ) : ℂ) • Rt E k (sOf S y)⁻¹ φ) =
        fun y => ((((boxL (latS S B : Set (Af E)) (eRow (Af E) k)).indicator (fun _ => (1 : ℝ))
            fun i => pFin E (y i) : ℝ)) : ℂ) •
          ((b (fun i => pInf E (y i)) : ℂ) • Rt E k (infGL E k (rowGL fun i => pInf E (y i)))⁻¹ φ) := by
      funext y
      rw [smul_smul, mul_comm, ← hcast]
      by_cases h : etaOf b (latS S B : Set (Af E)) y = 0
      · rw [h]; simp
      · congr 1
        refine BoundedContinuousFunction.ext fun g => ?_
        rw [Rt_apply, Rt_apply]
        exact hrt y g h
    rw [e]
    exact (Complex.continuous_ofReal.comp (hind.comp hf)).smul (hF.comp hp)
  ·
    have he : ∀ i, lastRow (1 : GA E k) i = eRow (Ad E) k i := fun i => congrFun lastRowM_one i
    have h1 : (fun i => pInf E (lastRow (1 : GA E k) i)) = eRow (Cinf E) k := by
      funext i; rw [he, map_eRow]
    have h2 : (fun i => pFin E (lastRow (1 : GA E k) i)) = eRow (Af E) k := by
      funext i; rw [he, map_eRow]
    have h3 : ∀ w, (fun i => pLoc E w (pFin E (lastRow (1 : GA E k) i))) = eRow _ k := fun w => by
      funext i; rw [he, map_eRow, map_eRow]
    constructor
    · have hm : (fun i => pFin E (lastRow (1 : GA E k) i)) ∈ boxL (latS S B : Set (Af E)) (eRow (Af E) k) := by
        rw [h2]
        intro i
        rw [sub_self]
        exact zero_mem _
      rw [etaOf_eq hm, h1]
      exact hbe
    · simp only [sOf, glue, h1, h3, rowGL_eRow hk, map_one]
      simp
  ·
    intro g _ hy
    have hy' := etaOf_ne hy
    refine ⟨?_, fun w hw => ?_⟩
    · rw [map_mul, map_inv, sOf, glue_cInf h0]
      refine lastRow_mul_rowGL_inv _ (hbu _ (subset_tsupport _ hy'.1)) ?_
      funext c
      exact (lastRowM_map (pInf E) g c).symm
    · rw [map_mul, map_inv, sOf, glue_cLoc_mem h0 _ _ _ w hw]
      refine lastRow_mul_rowGL_inv _ (hBu w hw _ (hloc _ hy w hw)).1 ?_
      funext c
      exact (lastRowM_map ((pLoc E w).comp (pFin E)) g c).symm
  ·
    intro y hy w hw i
    have h := ((etaOf_ne hy).2 i).1 w hw
    rw [map_sub, map_eRow] at h
    have := add_mem h (eRow_mem_Ov (k := k) w i)
    rwa [sub_add_cancel] at this
  ·
    intro y y' h1 h2
    have e1 : (fun i => pInf E (y i)) = fun i => pInf E (y' i) := funext h1
    refine ⟨?_, fun h3 hne => ?_⟩
    · rw [sOf, sOf, e1]
      exact glue_congr _ _ _ _ fun w hw => congrArg rowGL (funext (h2 w hw))
    · have hbox := (etaOf_ne hne).2
      have hbox' : (fun i => pFin E (y' i)) ∈ boxL (latS S B : Set (Af E)) (eRow (Af E) k) := fun i => by
        refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rw [map_sub, map_eRow]
          exact sub_mem (h3 w hw i) (eRow_mem_Ov w i)
        · have h := (hbox i).2 w hw
          rw [map_sub] at h ⊢
          rwa [← h2 w hw i]
      rw [etaOf_eq hbox', etaOf_eq hbox, e1]
  ·
    have hsl : ∀ w t, (w ∉ S → t ∈ Formalism.UG.Ov E w) → (w ∈ S → t ∈ B w) → sLoc E w t ∈ latS S B := by
      intro w t h1 h2
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · by_cases e : v = w
        · subst e; rw [pLoc_sLoc_self]; exact h1 hv
        · rw [pLoc_sLoc_ne e]; exact zero_mem _
      · by_cases e : v = w
        · subst e; rw [pLoc_sLoc_self]; exact h2 hv
        · rw [pLoc_sLoc_ne e]; exact zero_mem _
    obtain ⟨C₁, hC₁, hann⟩ := GlobalTheory.T.annihilator_adelic_lattice_compact hψ S hS (latS S B : Set (Af E))
      (fun w hw t ht => hsl w t (fun _ => ht) (fun h => absurd h hw))
      (fun w hw => ⟨_, (hBo w hw).mem_nhds (zero_mem (B w)), fun t ht =>
        hsl w t (fun h => absurd hw h) (fun _ => ht)⟩)
    refine ⟨Set.pi Set.univ fun _ => C₁, isCompact_univ_pi fun _ => hC₁, fun M => ?_⟩
    obtain ⟨C, hCb⟩ := inf_ft h4 h8 hψ hφ hb hbc hbu M
    refine ⟨C * (nuFin E k).real (boxL (latS S B : Set (Af E)) (eRow (Af E) k)), fun z g => ?_⟩
    set zi : Fin k → Cinf E := fun i => pInf E (z i) with hzi
    set zf : Fin k → Af E := fun i => pFin E (z i) with hzf
    let A : (Fin k → Cinf E) → ℂ := fun x =>
      (b x : ℂ) * φ (g * (infGL E k (rowGL x))⁻¹) * ψ (sInf E (∑ i, x i * zi i))
    let Bf : (Fin k → Af E) → ℂ := fun f =>
      (((boxL (latS S B : Set (Af E)) (eRow (Af E) k)).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) *
        ψ (sFin E (∑ i, f i * zf i))
    have key : ∫ y, (etaOf b (latS S B : Set (Af E)) y : ℂ) * φ (g * (sOf S y)⁻¹) * ψ (∑ i, y i * z i)
        ∂vecMeasure E (Fin k) = (∫ x, A x ∂nuInf E k) * ∫ f, Bf f ∂nuFin E k := by
      rw [← GlobalTheory.T.adelic_vector_integral_product A Bf]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have hψs : ψ (∑ i, y i * z i) = ψ (sInf E (∑ i, pInf E (y i) * zi i)) * ψ (sFin E (∑ i, pFin E (y i) * zf i)) := by
        have e1 : pInf E (∑ i, y i * z i) = ∑ i, pInf E (y i) * zi i := by
          rw [map_sum]; exact Finset.sum_congr rfl fun i _ => map_mul _ _ _
        have e2 : pFin E (∑ i, y i * z i) = ∑ i, pFin E (y i) * zf i := by
          rw [map_sum]; exact Finset.sum_congr rfl fun i _ => map_mul _ _ _
        rw [← e1, ← e2, ← AddChar.map_add_eq_mul, ← ad_split]
      have hφ' : (etaOf b (latS S B : Set (Af E)) y : ℂ) * φ (g * (sOf S y)⁻¹) =
          (etaOf b (latS S B : Set (Af E)) y : ℂ) * φ (g * (infGL E k (rowGL fun i => pInf E (y i)))⁻¹) := by
        by_cases h : etaOf b (latS S B : Set (Af E)) y = 0
        · rw [h]; simp
        · rw [hrt y g h]
      change (etaOf b (latS S B : Set (Af E)) y : ℂ) * φ (g * (sOf S y)⁻¹) * ψ (∑ i, y i * z i) =
        ((b (fun i => pInf E (y i)) : ℂ) * φ (g * (infGL E k (rowGL fun i => pInf E (y i)))⁻¹) *
          ψ (sInf E (∑ i, pInf E (y i) * zi i))) *
        ((((boxL (latS S B : Set (Af E)) (eRow (Af E) k)).indicator (fun _ => (1 : ℝ))
          fun i => pFin E (y i) : ℝ) : ℂ) * ψ (sFin E (∑ i, pFin E (y i) * zf i)))
      rw [hψs]
      rw [hcast] at hφ'
      rw [hcast]
      linear_combination (ψ (sInf E (∑ i, pInf E (y i) * zi i)) * ψ (sFin E (∑ i, pFin E (y i) * zf i))) * hφ'
    rw [key, norm_mul]
    have hA : ‖∫ x, A x ∂nuInf E k‖ ≤ C * ((1 + ‖zi‖) ^ M)⁻¹ := hCb zi g
    obtain ⟨hB1, hB2⟩ := GlobalTheory.T.box_fourier_integral_bound (k := k) hψ.norm hψ.cont (latS S B) hLc hLo (eRow (Af E) k) zf
    by_cases hz : zf ∈ Set.pi Set.univ fun _ : Fin k => C₁
    · rw [Set.indicator_of_mem hz]
      calc ‖∫ x, A x ∂nuInf E k‖ * ‖∫ f, Bf f ∂nuFin E k‖
          ≤ (C * ((1 + ‖zi‖) ^ M)⁻¹) * (nuFin E k).real (boxL (latS S B : Set (Af E)) (eRow (Af E) k)) :=
            mul_le_mul hA hB1 (norm_nonneg _) ((norm_nonneg _).trans hA)
        _ = _ := by ring
    · have h0' : ∫ f, Bf f ∂nuFin E k = 0 := by
        by_contra hne
        exact hz fun i _ => hann _ fun a ha => hB2 hne i a ha
      rw [Set.indicator_of_notMem hz, h0']
      simp

theorem exists_cut : S4 → S8 → PositivityTheory.jumpWindows.G0 → LastRowCutoff := by
  intro h4 h8 h0 E _ _ _ k hk ψ hψ S hS U hU φ hφ hLv
  haveI : LocallyCompactSpace (GA E k) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨C₀, hC₀n, hC₀U, hC₀c⟩ := local_compact_nhds hU
  obtain ⟨Wi, hWi, N, hN, hglue⟩ := glue_nhds h0 S hC₀n
  have hCi : ∀ᶠ x in 𝓝 (eRow (Cinf E) k), IsUnit (lastEnt x) ∧ rowGL x ∈ Wi :=
    eventually_rowGL (show ∀ᶠ x in 𝓝 (1 : Cinf E), IsUnit x from Units.isOpen.mem_nhds isUnit_one) (by
      simpa using NormedRing.inverse_continuousAt (1 : (Cinf E)ˣ)) hk hWi
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hCi
  have hr : 0 < min ρ 1 := lt_min hρ one_pos
  let f : ContDiffBump (eRow (Cinf E) k) := ⟨min ρ 1 / 4, min ρ 1 / 2, by positivity, by linarith⟩
  have hrO : f.rOut = min ρ 1 / 2 := rfl
  have hrρ : f.rOut < ρ := by
    rw [hrO]; have := min_le_left ρ 1; linarith
  have hr1 : f.rOut < 1 := by
    rw [hrO]; have := min_le_right ρ 1; linarith
  have hnorm : 1 ≤ ‖eRow (Cinf E) k‖ := by
    have hl : ((⟨k - 1, by omega⟩ : Fin k) : ℕ) + 1 = k := by simp; omega
    have h1 := norm_le_pi_norm (eRow (Cinf E) k) ⟨k - 1, by omega⟩
    rw [eRow, if_pos hl, norm_one] at h1
    exact h1
  have hloc : ∀ w ∈ S, ∃ B : AddSubgroup (w.adicCompletion E), IsOpen (B : Set (w.adicCompletion E)) ∧
      (B : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E)) ∧
      ∀ t : Fin k → w.adicCompletion E, (∀ i, t i - eRow _ k i ∈ B) →
        (IsUnit (lastEnt t) ∧ repW k w (rowGL t) φ = φ) ∧ rowGL t ∈ N w := by
    intro w hw
    have hW : N w ∩ {u | repW k w u φ = φ} ∈ 𝓝 (1 : GL (Fin k) (w.adicCompletion E)) :=
      Filter.inter_mem (hN w) (hLv w hw)
    have hT := eventually_rowGL (R := w.adicCompletion E)
      ((show ∀ᶠ x in 𝓝 (1 : w.adicCompletion E), x ≠ 0 from isOpen_ne.mem_nhds one_ne_zero).mono fun x hx => IsUnit.mk0 x hx)
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ one_ne_zero) hk hW
    have hT' : ∀ᶠ v in 𝓝 (0 : Fin k → w.adicCompletion E),
        IsUnit (lastEnt (v + eRow _ k)) ∧ rowGL (v + eRow _ k) ∈ N w ∩ {u | repW k w u φ = φ} := by
      have hc : Tendsto (fun v : Fin k → w.adicCompletion E => v + eRow _ k) (𝓝 0) (𝓝 (eRow _ k)) := by
        simpa using (continuous_add_right (eRow (w.adicCompletion E) k)).tendsto 0
      exact hc.eventually hT
    rw [nhds_pi, Filter.eventually_iff, Filter.mem_pi'] at hT'
    obtain ⟨I, t, ht, hts⟩ := hT'
    have hN0 : (⋂ i, t i) ∈ 𝓝 (0 : w.adicCompletion E) := Filter.iInter_mem.2 ht
    obtain ⟨B, hBo, hB1, hB2⟩ := exists_openSub w hN0
    refine ⟨B, hBo, hB2, fun u hu => ?_⟩
    have hm : (u - eRow _ k) ∈ (I : Set (Fin k)).pi t := fun i _ => Set.mem_iInter.1 (hB1 (hu i)) i
    have := hts hm
    simp only [Set.mem_setOf_eq, sub_add_cancel] at this
    exact ⟨⟨this.1, this.2.2⟩, this.2.1⟩
  choose! B hBo hBI hBu using hloc
  refine ⟨etaOf f (latS S B : Set (Af E)), sOf S, ?_⟩
  have hsub : ∀ x ∈ tsupport f, x ∈ Metric.ball (eRow (Cinf E) k) ρ := fun x hx => by
    rw [f.tsupport_eq] at hx
    exact Metric.closedBall_subset_ball hrρ hx
  refine cut_of h0 h4 h8 hk hψ hS hC₀c hC₀U hφ f.contDiff f.hasCompactSupport (fun _ => f.nonneg) ?_ ?_
    (fun x hx => (hball x (hsub x hx)).1) hBo hBI (fun w hw t ht => (hBu w hw t ht).1) fun y hy => ?_
  · exact f.pos_of_mem_ball (Metric.mem_ball_self f.rOut_pos)
  · refine f.zero_of_le_dist ?_
    rw [dist_comm, dist_zero_right]
    exact hr1.le.trans hnorm
  · have h1 := etaOf_ne hy
    refine hglue _ (hball _ (hsub _ (subset_tsupport _ h1.1))).2 _ fun w hw => (hBu w hw _ fun i => ?_).2
    have h := (h1.2 i).2 w hw
    rwa [map_sub, map_eRow] at h

end GlobalTheory.CompanionTheory.CutOff

end
