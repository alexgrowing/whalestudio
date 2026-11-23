import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShape
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRational
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT GlobalTheory.Mem.Col2.JetEx GlobalTheory.MomT.ThShape

noncomputable section

namespace GlobalTheory.Mem.Col2.IndEq

section Lat

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

theorem apply_mem_gmap (φ : W ≃ₗ[E] W) (M : Submodule (𝓞 E) W) (x : W) : φ x ∈ gmap φ M ↔ x ∈ M :=
  ⟨fun ⟨y, hy, e⟩ => by rwa [← φ.injective e], fun h => ⟨x, h, rfl⟩⟩

theorem apply_mem_locP (φ : W ≃ₗ[E] W) (M : Submodule (𝓞 E) W) (Q : HeightOneSpectrum (𝓞 E)) (x : W) :
    φ x ∈ localization₂ Q.asIdeal (gmap φ M) ↔ x ∈ localization₂ Q.asIdeal M := by
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [← apply_mem_gmap φ M, ← algebraMap_smul E s x, map_smul, algebraMap_smul]

theorem twO_gmap (φ : W ≃ₗ[E] W) (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) :
    twist₂ (gmap φ M) c e = gmap φ (twist₂ M c e) := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [apply_mem_gmap, ThShape.mem_twO, ThShape.mem_twO]
  exact forall_congr' fun Q => by rw [← map_smul, apply_mem_locP]

theorem gmap_toAddSubgroup (φ : W ≃ₗ[E] W) (M : Submodule (𝓞 E) W) :
    (gmap φ M).toAddSubgroup = M.toAddSubgroup.map φ.toLinearMap.toAddMonoidHom := rfl

variable {a b : ℕ} (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b)

def conjH : HomE E a b ≃ₗ[E] HomE E a b := LinearEquiv.arrowCongr γ γ'

theorem conjH_apply (x : HomE E a b) : conjH γ γ' x = γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap := rfl

theorem conjH_mem_homO (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    conjH γ γ' x ∈ homO (gmap γ N) (gmap γ' N') ↔ x ∈ homO N N' := by
  constructor
  · intro h y hy
    have := h (γ y) ((apply_mem_gmap γ N y).2 hy)
    rw [conjH_apply] at this
    simpa [apply_mem_gmap] using this
  · rintro h _ ⟨y, hy, rfl⟩
    rw [conjH_apply]
    simpa [apply_mem_gmap] using h y hy

theorem perO_gmap (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) :
    perO AA (gmap γ N) (gmap γ' N') = gmap (conjH γ γ') (perO AA N N') := by
  refine Eq.trans ?_ (Submodule.map_span _ _).symm
  rw [perO]
  congr 1
  ext z
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (conjH γ γ').surjective y
    exact ⟨r • x, ⟨r, hr, x, (conjH_mem_homO γ γ' N N' x).1 hy, rfl⟩, map_smul (conjH γ γ') r x⟩
  · rintro ⟨_, ⟨r, hr, x, hx, rfl⟩, rfl⟩
    exact ⟨r, hr, conjH γ γ' x, (conjH_mem_homO γ γ' N N' x).2 hx, map_smul (conjH γ γ') r x⟩

variable [StarRing E]

theorem toMatrix_unitary {n : ℕ} {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) :
    ((LinearMap.toMatrix' g.toLinearMap).map τ).conjTranspose * (LinearMap.toMatrix' g.toLinearMap).map τ = 1 := by
  ext i j
  have h := congrArg τ (hg (Pi.single i 1) (Pi.single j 1))
  simp only [Formalism.L2.Col.hStd, LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, hτ] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply, apply_ite]
    · simp [Pi.single_apply, hij, apply_ite, Ne.symm hij]

end Lat

section Pull

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem pullV_eq (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b) (z : VCx X.Tau a b) (τ : X.Tau) :
    Matrix.of (A.pullV a b γ γ' z τ) = (LinearMap.toMatrix' γ'.symm.toLinearMap).map (X.embC A.σ₀ τ) * Matrix.of (z τ) *
      (LinearMap.toMatrix' γ.toLinearMap).map (X.embC A.σ₀ τ) := by
  ext i j
  simp only [Amb.pullV, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem emb_eq (x : HomE X.E a b) (τ : X.Tau) :
    Matrix.of (emb A x τ) = A.δ • (LinearMap.toMatrix' x).map (X.embC A.σ₀ τ) := by
  ext i j
  rfl

theorem pullV_emb (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b) (x : HomE X.E a b) :
    A.pullV a b γ γ' (emb A (conjH γ γ' x)) = emb A x := by
  funext τ
  apply Matrix.of.injective
  rw [pullV_eq, emb_eq, emb_eq, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← LinearMap.toMatrix'_comp,
    ← LinearMap.toMatrix'_comp]
  congr 3
  ext
  simp [conjH_apply]

theorem pullV_add (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b) (z w : VCx X.Tau a b) :
    A.pullV a b γ γ' (z + w) = A.pullV a b γ γ' z + A.pullV a b γ γ' w := by
  funext τ i j
  simp only [Amb.pullV, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem HV_trace (sc : ℝ) (z w : VCx X.Tau a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, (Matrix.of (z τ) * (Matrix.of (w τ)).conjTranspose).trace := rfl

theorem HV_pullV (hX : X.Ok) (γ : UF X.E a) (γ' : UF X.E b) (z w : VCx X.Tau a b) :
    HV A.sc (A.pullV a b γ.1 γ'.1 z) (A.pullV a b γ.1 γ'.1 w) = HV A.sc z w := by
  rw [HV_trace, HV_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h1 := mul_eq_one_comm.1 (toMatrix_unitary γ.2 (X.embC A.σ₀ τ) (hX.conjE _))
  have h2 := toMatrix_unitary (γ'⁻¹).2 (X.embC A.σ₀ τ) (hX.conjE _)
  change ((LinearMap.toMatrix' γ'.1.symm.toLinearMap).map _).conjTranspose * (LinearMap.toMatrix' γ'.1.symm.toLinearMap).map _ = 1 at h2
  rw [pullV_eq, pullV_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc (Matrix.map _ _) (Matrix.conjTranspose _), h1, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, h2, Matrix.mul_one]

theorem Wx_pull (hX : X.Ok) (γ : UF X.E a) (γ' : UF X.E b) (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) (z : VCx X.Tau a b) :
    Wx A (conjH γ.1 γ'.1 x) (fun v => F (A.pullV a b γ.1 γ'.1 v)) z = Wx A x F (A.pullV a b γ.1 γ'.1 z) := by
  simp only [Wx, opU, alV, alphaQ, Formalism.L2.Th1.H.qOf]
  rw [pullV_add, ← HV_pullV A hX γ γ' z, ← HV_pullV A hX γ γ' (emb A _), pullV_emb]

end Pull

theorem thInd_index : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), X.Ok → A.LaHyp a b S → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∀ x ∈ divLat cA (homAt S N N'), ∀ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') → ∀ R : Finset (HomE X.E a b), IsReps (per A N N').toAddSubgroup (halfBO S (per A N N') c).toAddSubgroup R → A.thInd S N N' c x = fun z => (((halfBO S (per A N N') c).toAddSubgroup.relIndex ((per A N N').toAddSubgroup ⊓ (halfAO S (per A N N') c).toAddSubgroup) : ℕ) : ℂ)⁻¹ * Wx A (-t) (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) z := by
  intro X A a b S N N' cA c hX ⟨hδ, hT, hS, hU, hFG, hLa⟩ hAA hN hN' hcA hc
  obtain ⟨hfix, hL⟩ := hLa N N' hN hN'
  obtain ⟨-, -, hidx, hloc⟩ := GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff X A a b N N' hFG hAA hN hN'
  have hinj := embH_injective A (a := a) (b := b) hδ hT
  have hc0 : (c : X.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hBB : ∀ x ∈ halfBO S (per A N N') c, ∀ y ∈ halfBO S (per A N N') c, ∃ n : ℤ, coc A x y = n :=
    fun x hx y hy => coc_int_twO A hX hδ hL hc (expS_conj hS) hx hy

  have hBM : (halfBO S (per A N N') c).toAddSubgroup.relIndex (per A N N').toAddSubgroup ≠ 0 := by
    intro h0
    refine hidx (c : 𝓞 X.E) (Nat.cast_ne_zero.2 hc.ne') (AddSubgroup.relIndex_eq_zero_of_le_left ?_ h0)
    rintro _ ⟨m, hm, rfl⟩
    refine (ThShape.mem_twO _ _ _ _).2 fun Q => mem_loc_self Q ?_
    change _ • (((c : 𝓞 X.E) : X.E) • m) ∈ _
    rw [show ((c : 𝓞 X.E) : X.E) = (c : X.E) from map_natCast (algebraMap (𝓞 X.E) X.E) c]
    rcases expS_cases S hS Q with ⟨-, e1, -⟩ | ⟨-, e1, -⟩ | ⟨e1, -⟩
    · rw [e1, zpow_one, inv_smul_smul₀ hc0]; exact hm
    · rw [e1, zpow_neg, inv_inv, zpow_one]; exact nat_smul_mem (nat_smul_mem hm c) c
    · rw [e1, zpow_zero, inv_one, one_smul]; exact nat_smul_mem hm c
  have hdvd := relIndex_dvd_of_le (halfBO S (per A N N') c).toAddSubgroup
    ((per A N N').toAddSubgroup ⊓ (halfAO S (per A N N') c).toAddSubgroup) (per A N N').toAddSubgroup inf_le_left
  set n := (halfBO S (per A N N') c).toAddSubgroup.relIndex
    ((per A N N').toAddSubgroup ⊓ (halfAO S (per A N N') c).toAddSubgroup) with hn
  have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero hBM hdvd
  intro x hx t ht htx R hR

  obtain ⟨RA, hRA⟩ := (GlobalTheory.RepsMod.reps_facts _).1 _ _ hn0
  have hRA' := reps_map _ hinj hRA
  rw [AddSubgroup.map_inf _ _ _ hinj] at hRA'
  have hSA : IsReps (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c)
      (repsOf _ _) := repsOf_spec ⟨_, hRA'⟩
  have hcard : (repsOf (BC (X.embC A.σ₀) A.δ A.AA S N N' c)
      (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c)).card = n := by
    rw [(GlobalTheory.RepsMod.reps_facts _).2.1 _ _ _ hSA, hn, ← AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
      AddSubgroup.map_inf _ _ _ hinj]
    rfl
  have hR' : IsReps (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c) _ := reps_map _ hinj hR
  have hSB : IsReps (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (repsOf _ _) :=
    repsOf_spec ⟨_, hR'⟩

  have hinv : ∀ y ∈ (halfBO S (per A N N') c).toAddSubgroup, ∀ l ∈ (per A N N').toAddSubgroup,
      l ∈ (halfBO S (per A N N') c).toAddSubgroup → Wx A (y + l) (A.e a b N N') = Wx A y (A.e a b N N') := by
    intro y hy l hl hl'
    rw [← Wx_mul A (hBB y hy l hl')]
    congr 1
    funext z
    exact hfix _ ⟨l, hl, rfl⟩ z
  have hshift : ∀ u ∈ halfBO S (per A N N') c, Wx A u (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) =
      fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z := by
    intro u hu
    rw [Wx_sum]
    funext z
    rw [sum_reps_eq (fun y => Wx A y (A.e a b N N') z) hR (reps_shift hR hu)
      (fun y hy l hl hl' => by rw [hinv y hy l hl hl']), Finset.sum_map]
    exact Finset.sum_congr rfl fun y hy => by rw [Wx_mul A (hBB u hu y (hR.1 y hy))]; rfl

  have hxi : xiS (HV A.sc) (alV A.d A.sc) (volC A.AA S N N')
      (repsOf (BC (X.embC A.σ₀) A.δ A.AA S N N' c) (LamC (X.embC A.σ₀) A.δ A.AA N N' ⊓ AC (X.embC A.σ₀) A.δ A.AA S N N' c))
      (repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c))
      (indL (BC (X.embC A.σ₀) A.δ A.AA S N N' c)) (A.e a b N N') =
      fun z => ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ)⁻¹ * (((volC A.AA S N N' : ℝ) : ℂ) / (n : ℂ)) *
        ∑ y ∈ R, Wx A y (A.e a b N N') z := by
    funext z
    have e1 : ∑ y ∈ R, Wx A y (A.e a b N N') z =
        ∑ v ∈ repsOf (LamC (X.embC A.σ₀) A.δ A.AA N N') (BC (X.embC A.σ₀) A.δ A.AA S N N' c),
          alV A.d A.sc v * opU (HV A.sc) v (A.e a b N N') z := by
      rw [sum_reps_eq (fun v => alV A.d A.sc v * opU (HV A.sc) v (A.e a b N N') z) hSB hR' ?_, Finset.sum_map]
      · rfl
      · rintro _ ⟨y, hy, rfl⟩ _ ⟨l, hl, rfl⟩ ⟨l', hl', e⟩
        obtain rfl := hinj e
        rw [← map_add]
        exact congrFun (hinv y hy l' hl hl') z
    rw [e1, Finset.mul_sum, xiS, sumU]
    refine Finset.sum_congr rfl fun v hv => ?_
    obtain ⟨y, hy, rfl⟩ := hSB.1 v hv
    rw [hatS_ind _ _ hSA, hcard, mul_assoc]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨n₁, h₁⟩ := hBB u hu y hy
    obtain ⟨n₂, h₂⟩ := hBB y hy u hu
    exact ((GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.2.2.2.1 y u).2
      ⟨n₁ - n₂, by rw [(GlobalTheory.T.weylHeisenbergOperator_calculus_rational X A a b).2.2.1, h₁, h₂]; push_cast; ring⟩

  have hlift : A.IsLift S N N' c x (A.liftW S N N' c x) :=
    Classical.epsilon_spec (p := A.IsLift S N N' c x) ⟨t, ⟨cA * c, Nat.mul_pos hcA hc, ht⟩, htx⟩
  obtain ⟨⟨c', hc', hs⟩, hsx⟩ := hlift
  set s := A.liftW S N N' c x with hs_def
  obtain ⟨hB, hcoc⟩ := two_lifts A hX hδ hL hS hc hc' (Nat.mul_pos hcA hc) hs ht (by
    intro P hP
    obtain ⟨h, hh, e⟩ := sub_mem htx hsx
    have e' : t - s = (c : X.E) • h := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 X.E), ← sub_sub_sub_cancel_right t s x]
      exact e.symm
    rw [e', inv_smul_smul₀ hc0]
    exact (hloc P (hU P hP) h).2 (hh P hP))
  have hW : Wx A (-t) (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) = Wx A (-s) (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) := by
    conv_lhs => rw [← hshift _ hB, Wx_mul A hcoc]
    congr 1
    abel
  rw [hW]
  funext z
  have hv := volC_pos A hFG hAA S hN hN'
  have hsq : ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ) * ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ) = (volC A.AA S N N' : ℝ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hv.le]
  have hsq0 : ((Real.sqrt (volC A.AA S N N') : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hv).ne'
  have hα : alV A.d A.sc (emb A (-s)) = alV A.d A.sc (embH (X.embC A.σ₀) A.δ s) := by
    simp [emb, alV, alphaQ, Formalism.L2.Th1.H.qOf]
  have hem : emb A (-s) = -embH (X.embC A.σ₀) A.δ s := map_neg _ _
  rw [Amb.thInd, xiInd, ← hs_def, hxi, Wx]
  simp only [hα]
  rw [hem, opU, opU, ← hsq]
  field_simp

theorem index_per_ne_zero {X : Fields} (A : Amb X) {a b : ℕ} {S : Finset (HeightOneSpectrum (𝓞 X.E))}
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} {c : ℕ} (hL : A.LaHyp a b S)
    (hN : IsSdLat N) (hN' : IsSdLat N') (hc : 0 < c) :
    (per A N N').toAddSubgroup.relIndex (halfBO S (per A N N') c).toAddSubgroup ≠ 0 := by
  have h := (((heisHyp_of A a b S hL).2.2.2.2 N N' hN hN').2 c hc).2.2.1
  rwa [← AddSubgroup.relIndex_map_map_of_injective _ _ (embH_injective A hL.1 hL.2.1)]

theorem thIndEq_of_vacEq : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ),
    X.Ok → A.LaHyp a b S → A.AA ≠ ⊥ → 0 < M → VacEq A a b → A.ThIndEq a b S M := by
  intro X A a b S M hX hL hAA hM hV γ γ' N N' c x ⟨hN, hN', hc, _, hx⟩ z
  have hgN : IsSdLat (gmap γ.1 N) := ⟨gmap_lattice _ _ hN.1, by rw [IsUnimodular, dual_gmap _ γ.2, hN.2]⟩
  have hgN' : IsSdLat (gmap γ'.1 N') := ⟨gmap_lattice _ _ hN'.1, by rw [IsUnimodular, dual_gmap _ γ'.2, hN'.2]⟩
  obtain ⟨t, ht, htx⟩ := exists_lift_halfAO X A a b S N N' M c hL.2.2.2.2.1 hAA hL.2.2.1 hL.2.2.2.1 hN hN' hM hc x hx
  obtain ⟨R, hR⟩ := GlobalTheory.RepsMod.exists_reps _ _ (index_per_ne_zero A hL hN hN' hc)
  have hinj : Function.Injective (conjH γ.1 γ'.1).toLinearMap.toAddMonoidHom := (conjH γ.1 γ'.1).injective
  have hP : per A (gmap γ.1 N) (gmap γ'.1 N') = gmap (conjH γ.1 γ'.1) (per A N N') := perO_gmap _ _ _ _ _
  have hA : ∀ k, halfAO S (per A (gmap γ.1 N) (gmap γ'.1 N')) k = gmap (conjH γ.1 γ'.1) (halfAO S (per A N N') k) :=
    fun k => by rw [hP, halfAO, twO_gmap]; rfl
  have hB : halfBO S (per A (gmap γ.1 N) (gmap γ'.1 N')) c = gmap (conjH γ.1 γ'.1) (halfBO S (per A N N') c) := by
    rw [hP, halfBO, twO_gmap]; rfl
  have h1 := thInd_index X A a b S N N' M c hX hL hAA hN hN' hM hc x hx t ht htx R hR
  have h2 := thInd_index X A a b S _ _ M c hX hL hAA hgN hgN' hM hc (conjH γ.1 γ'.1 x)
    ((divLat_gmap_iff S M γ.1 γ'.1 N N' x).2 hx) (conjH γ.1 γ'.1 t) (by rw [hA, apply_mem_gmap]; exact ht)
    (by
      obtain ⟨h, hh, e⟩ := htx
      refine ⟨conjH γ.1 γ'.1 h, (homAt_gmap_iff S γ.1 γ'.1 N N' h).2 hh, ?_⟩
      rw [← map_sub, ← e]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, map_nsmul])
    (R.map ⟨_, hinj⟩) (by rw [hB, hP]; exact reps_map _ hinj hR)
  rw [← conjH_apply, h1, h2, hA, hB, hP]
  simp only [gmap_toAddSubgroup]
  rw [← AddSubgroup.map_inf _ _ _ hinj, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, ← map_neg, ← Wx_pull A hX γ γ']
  congr 2
  funext v
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Wx_pull A hX γ γ', funext (hV γ γ' N N' hN hN')]
  rfl

end GlobalTheory.Mem.Col2.IndEq

end
