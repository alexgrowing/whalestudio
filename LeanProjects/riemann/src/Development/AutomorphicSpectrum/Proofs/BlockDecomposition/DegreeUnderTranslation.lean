import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.DegMoveProof

theorem log_step {a b c : ℝ} {k n : ℕ} (hkn : k ≤ n) (ha : 0 < a) (hb : 0 < b) (h : a ≤ c ^ k * b) :
    Real.log a ≤ n * Real.posLog c + Real.log b := by
  have hp : 0 < c ^ k * b := lt_of_lt_of_le ha h
  have hck : c ^ k ≠ 0 := fun h0 => by simp [h0] at hp
  have h1 : Real.log a ≤ Real.log (c ^ k * b) := Real.log_le_log ha h
  rw [Real.log_mul hck hb.ne', Real.log_pow] at h1
  have h2 : Real.log c ≤ Real.posLog c := le_max_right 0 (Real.log c)
  have h3 : (0 : ℝ) ≤ Real.posLog c := Real.posLog_nonneg
  have h4 : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have h5 : (k : ℝ) * Real.log c ≤ n * Real.posLog c :=
    (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)).trans (mul_le_mul_of_nonneg_right h4 h3)
  linarith

theorem finsum_bound {α : Type} {f g s : α → ℝ} {c : ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (hs : (Function.support s).Finite) (h : ∀ a, f a ≤ c * s a + g a) :
    ∑ᶠ a, f a ≤ c * ∑ᶠ a, s a + ∑ᶠ a, g a := by
  classical
  let T : Finset α := hf.toFinset ∪ hg.toFinset ∪ hs.toFinset
  rw [finsum_eq_sum_of_support_subset f (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset g (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    finsum_eq_sum_of_support_subset s (s := T) (fun a ha => by simp [T, Set.mem_toFinset] at ha ⊢; tauto),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => h a

theorem sz_sq_le {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : sz g ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖g p.1 p.2‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Fin n × Fin n) with he | hne
  · simp [sz, Real.iSup_of_isEmpty]
  · obtain ⟨p, hp⟩ := exists_eq_ciSup_of_finite (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖)
    rw [sz, ← hp]
    exact le_ciSup (f := fun p : Fin n × Fin n => ‖g p.1 p.2‖ ^ 2) (Set.finite_range _).bddAbove p

theorem nI_nonneg {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℂ) : 0 ≤ nI A := by
  open ComplexOrder in
  have h : 0 ≤ (Aᴴ * A).det := (Matrix.posSemidef_conjTranspose_mul_self A).det_nonneg
  exact (Complex.le_def.1 h).1

theorem nF_nonneg {K ι κ : Type} [NormedField K] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem exists_left_inv {K : Type} [Field K] {n k : ℕ} (M : Matrix (Fin n) (Fin k) K)
    (h : LinearIndependent K Mᵀ) : ∃ N : Matrix (Fin k) (Fin n) K, N * M = 1 := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_iff.2 h
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  have h1 : LinearMap.toMatrix' (f ∘ₗ M.mulVecLin) = 1 := by rw [hf]; exact LinearMap.toMatrix'_id
  rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at h1

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n k : ℕ}

theorem ultra (w : HeightOneSpectrum (𝓞 E)) : IsUltrametricDist (w.adicCompletion E) :=
  inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
    (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)

theorem inf_step (hI : MulI) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (v : InfinitePlace E) (h0 : nI ((h * A).map (cV v)) ≠ 0) (h1 : nI (A.map (cV v)) ≠ 0) :
    Real.log (nI ((h * A).map (cV v))) ≤
      n * (Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2)) +
        Real.log (nI (A.map (cV v))) := by
  have hm : (h * A).map (cV v) = h.map (cV v) * A.map (cV v) := Matrix.map_mul
  have hle := (hI (Fin n) (Fin n) (Fin k) (A.map (cV v))).1 (h.map (cV v))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  have hs := log_step hkn (lt_of_le_of_ne (nI_nonneg _) h0.symm) (lt_of_le_of_ne (nI_nonneg _) h1.symm) hle
  refine hs.trans ?_
  have h2 : Real.posLog ((n : ℝ) * n * sz (h.map (cV v)) ^ 2) ≤
      Real.posLog ((n : ℝ) * n) + Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h p.1 p.2)‖ ^ 2) :=
    Real.posLog_mul.trans (add_le_add le_rfl (Real.posLog_le_posLog (by positivity) (sz_sq_le _)))
  have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) n)
  linarith

theorem fin_step (hF : MulF) (hkn : k ≤ n) (h : Matrix (Fin n) (Fin n) (Ad E)) (A : Matrix (Fin n) (Fin k) (Ad E))
    (w : HeightOneSpectrum (𝓞 E)) (h0 : nF ((h * A).map (cW w)) ≠ 0) (h1 : nF (A.map (cW w)) ≠ 0) :
    Real.log (nF ((h * A).map (cW w))) ≤
      n * Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h p.1 p.2)‖) + Real.log (nF (A.map (cW w))) := by
  haveI := ultra w
  have hm : (h * A).map (cW w) = h.map (cW w) * A.map (cW w) := Matrix.map_mul
  have hle := (hF (w.adicCompletion E) (Fin n) (Fin n) (Fin k) (A.map (cW w))).1 (h.map (cW w))
  simp only [Fintype.card_fin] at hle
  rw [← hm] at hle
  exact log_step hkn (lt_of_le_of_ne (nF_nonneg _) h0.symm) (lt_of_le_of_ne (nF_nonneg _) h1.symm) hle

theorem logSizeM_nonneg (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem frame_move (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) :
    (x⁻¹ * ratGL E n g * x : GA E n).val * ((x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E))) =
      (x⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) := by
  have h1 : (ratGL E n g).val = g.val.map (algebraMap E (Ad E)) := rfl
  rw [Matrix.map_mul, ← h1, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem core (hF : MulF) (hI : MulI) (hSz : SzFin) (hFS : FinSupp) (hkn : k ≤ n) (h : GA E n)
    (A : Matrix (Fin n) (Fin k) (Ad E)) (Y : Matrix (Fin k) (Fin n) (Ad E)) (hY : Y * A = 1) :
    ∑ v, Real.log (nI ((h.val * A).map (cV v))) + ∑ᶠ w, Real.log (nF ((h.val * A).map (cW w))) ≤
      (∑ v, Real.log (nI (A.map (cV v))) + ∑ᶠ w, Real.log (nF (A.map (cW w)))) +
        n * ((Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)) + n * logSizeM h.val := by
  have hY' : (Y * (h⁻¹ : GA E n).val) * (h.val * A) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (h⁻¹ : GA E n).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, hY]
  obtain ⟨a1, a2, a3⟩ := hFS E (Fin n) (Fin k) A Y hY
  obtain ⟨b1, b2, b3⟩ := hFS E (Fin n) (Fin k) (h.val * A) _ hY'
  have hinf := Finset.sum_le_sum (s := Finset.univ) fun v (_ : v ∈ Finset.univ) =>
    inf_step (E := E) hI hkn h.val A v (b1 v) (a1 v)
  have hfin := finsum_bound (c := (n : ℝ))
    (f := fun w => Real.log (nF ((h.val * A).map (cW w))))
    (g := fun w => Real.log (nF (A.map (cW w))))
    (s := fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖))
    (b3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    (a3.subset fun w hw hne => hw ((congrArg Real.log hne).trans Real.log_one))
    ((hSz E (Fin n) (Fin n) h.val).subset fun w hw => by
      by_contra hc
      apply hw
      exact max_eq_left (Real.log_nonpos (Real.iSup_nonneg fun _ => norm_nonneg _) (not_lt.1 hc)))
    fun w => fin_step hF hkn h.val A w (b2 w) (a2 w)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hinf
  have hS : logSizeM h.val = ∑ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (h.val p.1 p.2)‖ ^ 2) +
      ∑ᶠ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (h.val p.1 p.2)‖) := rfl
  rw [hS]
  nlinarith [hinf, hfin]

theorem lin_basisMat (W : Submodule E (Fin n → E)) : LinearIndependent E (basisMat W)ᵀ ∧
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  have hM : (basisMat W)ᵀ = W.subtype ∘ (Module.finBasis E W) := by
    funext j i
    rfl
  rw [hM]
  refine ⟨(Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype, ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem linearIndependent_image_span (g : GL (Fin n) E) (f : Fin k → Fin n → E) (hf : LinearIndependent E f) :
    LinearIndependent E (Matrix.toLin' g.val ∘ f) ∧
      Submodule.span E (Set.range (Matrix.toLin' g.val ∘ f)) = img g (Submodule.span E (Set.range f)) := by
  have inj : Function.Injective (Matrix.toLin' g.val) := fun a b hab => by
    have h1 := congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using h1
  refine ⟨hf.map' _ (LinearMap.ker_eq_bot.2 inj), ?_⟩
  rw [Set.range_comp, ← Submodule.map_span]
  rfl

theorem lin_moved (g : GL (Fin n) E) (M : Matrix (Fin n) (Fin k) E) (hM : LinearIndependent E Mᵀ) :
    LinearIndependent E (g.val * M)ᵀ ∧
      Submodule.span E (Set.range (g.val * M)ᵀ) = img g (Submodule.span E (Set.range Mᵀ)) := by
  have hG : (Matrix.toLin' g.val ∘ (Mᵀ : Fin k → Fin n → E)) = ((g.val * M)ᵀ : Fin k → Fin n → E) := by
    funext j i
    change (Matrix.toLin' g.val (fun i' => M i' j)) i = (g.val * M) i j
    rw [Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have h1 := linearIndependent_image_span g Mᵀ hM
  rw [hG] at h1
  exact h1

theorem degMove_of : MulF → MulI → SzFin → FinSupp → DegBasisG → DegMove := by
  intro hF hI hSz hFS hB E _ _ _ n
  refine ⟨n * (1 + (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n)), fun x g W => ?_⟩
  obtain ⟨hLI, hspan⟩ := lin_basisMat W
  obtain ⟨hLI', hspan'⟩ := lin_moved g (basisMat W) hLI
  rw [hspan] at hspan'
  have hkn : Module.finrank E W ≤ n := by simpa using Submodule.finrank_le W
  obtain ⟨N, hN⟩ := exists_left_inv (basisMat W) hLI
  have e1 : deg x (img g W) = degG x (g.val * basisMat W) := by rw [hB E n _ x _ hLI', hspan']
  have e2 : deg x W = degG x (basisMat W) := rfl
  have hY : (N.map (algebraMap E (Ad E)) * x.val) * ((x⁻¹ : GA E n).val * (basisMat W).map (algebraMap E (Ad E))) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
      ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc := core hF hI hSz hFS hkn (x⁻¹ * ratGL E n g * x) _ _ hY
  rw [frame_move] at hc
  rw [e1, e2]
  simp only [degG]
  have hS := logSizeM_nonneg (x⁻¹ * ratGL E n g * x : GA E n).val
  have hS' := logSizeM_nonneg ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val
  have hL : (0 : ℝ) ≤ (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) :=
    mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  have hsz : logSize (x⁻¹ * ratGL E n g * x) = logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val +
    logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val := rfl
  rw [hsz]
  generalize logSizeM (x⁻¹ * ratGL E n g * x : GA E n).val = S at *
  generalize logSizeM ((x⁻¹ * ratGL E n g * x)⁻¹ : GA E n).val = S' at *
  generalize (Fintype.card (InfinitePlace E) : ℝ) * Real.posLog ((n : ℝ) * n) = b at *
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpos : 0 ≤ (n : ℝ) * (1 + S' + b * S + b * S') := by positivity
  nlinarith [hc, hpos]

end GlobalTheory.CompanionTheory.DegMoveProof

end
