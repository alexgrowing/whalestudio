import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisRestrictInf

open Formalism.UG (cT)

section Gen

variable {R : Type} [CommRing R] (s : R →+* R)

theorem cT_cT (hs : ∀ a, s (s a) = a) {k l : Type} (X : Matrix k l R) : cT s (cT s X) = X :=
  Matrix.ext fun _ _ => hs _

theorem mul_comm_one (u v : Matrix (Fin 1) (Fin 1) R) : u * v = v * u := by
  ext i j
  simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]

theorem key (hs : ∀ a, s (s a) = a) {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    {A B Jw D : Matrix n n R} {x y : Matrix n (Fin 1) R} {P : Matrix n m R} {Lm : Matrix m n R}
    {d0 : Matrix (Fin 1) (Fin 1) R}
    (hAB : A * B = 1) (hBA : B * A = 1) (hDD : D * D = 1)
    (hmaj : cT s A * Jw * A = D) (hJ : cT s Jw = Jw)
    (hLP : Lm * P = 1)
    (hPi : P * Lm * (1 - x * (cT s y * Jw) - y * (cT s x * Jw)) = 1 - x * (cT s y * Jw) - y * (cT s x * Jw))
    (hxP : cT s x * Jw * P = 0) (hyP : cT s y * Jw * P = 0) (hyx : cT s y * Jw * x = 1)
    (hcar : cT s B * B * x = Jw * y * d0) :
    (Lm * (A * D * B) * P) * (Lm * (A * D * B) * P) = 1 ∧
    cT s (B * P) * (B * P) = (cT s P * Jw * P) * (Lm * (A * D * B) * P) ∧
    (Lm * A) * (B * P) = 1 := by
  have hc1 : cT s B * cT s A = 1 := by rw [← Formalism.UG.cT_mul, hAB, Formalism.UG.cT_one]
  have hJw : Jw = cT s B * D * B := by
    rw [← hmaj]
    calc Jw = (cT s B * cT s A) * Jw * (A * B) := by rw [hc1, hAB, Matrix.one_mul, Matrix.mul_one]
      _ = cT s B * (cT s A * Jw * A) * B := by simp only [Matrix.mul_assoc]
  set θ := A * D * B with hθdef
  set M := cT s B * B with hMdef
  have hθM : Jw * θ = M := by
    calc Jw * θ = cT s B * D * (B * A) * D * B := by rw [hJw, hθdef]; simp only [Matrix.mul_assoc]
      _ = cT s B * (D * D) * B := by rw [hBA]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = M := by rw [hDD, Matrix.mul_one]
  have hθθ : θ * θ = 1 := by
    calc θ * θ = A * D * (B * A) * D * B := by simp only [hθdef, Matrix.mul_assoc]
      _ = A * (D * D) * B := by rw [hBA]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hDD, Matrix.mul_one, hAB]
  have hAJ : cT s A * Jw = D * B := by
    calc cT s A * Jw = cT s A * Jw * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = D * B := by rw [← hmaj]; simp only [Matrix.mul_assoc]
  have hinv : A * D * cT s A * Jw = 1 := by
    calc A * D * cT s A * Jw = A * D * (cT s A * Jw) := by simp only [Matrix.mul_assoc]
      _ = A * (D * D) * B := by rw [hAJ]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDD, Matrix.mul_one, hAB]
  have hθx : θ * x = y * d0 := by
    calc θ * x = (A * D * cT s A * Jw) * θ * x := by rw [hinv, Matrix.one_mul]
      _ = A * D * cT s A * ((Jw * θ) * x) := by simp only [Matrix.mul_assoc]
      _ = (A * D * cT s A * Jw) * (y * d0) := by rw [hθM, hMdef, hcar]; simp only [Matrix.mul_assoc]
      _ = y * d0 := by rw [hinv, Matrix.one_mul]
  have hJx : Jw * x = M * y * d0 := by
    calc Jw * x = Jw * (θ * θ * x) := by rw [hθθ, Matrix.one_mul]
      _ = (Jw * θ) * (θ * x) := by simp only [Matrix.mul_assoc]
      _ = M * y * d0 := by rw [hθM, hθx]; simp only [Matrix.mul_assoc]
  set s1 := cT s y * M * y with hs1def
  have hs1 : s1 * d0 = 1 := by
    rw [← hyx, Matrix.mul_assoc (cT s y), hJx]; simp only [hs1def, Matrix.mul_assoc]
  have hMy : M * y = Jw * x * s1 := by
    rw [hJx, Matrix.mul_assoc, Matrix.mul_assoc, mul_comm_one d0 s1, hs1, Matrix.mul_one]
  have hMh : cT s M = M := by rw [hMdef, Formalism.UG.cT_mul, cT_cT s hs]
  have hxθP : cT s x * Jw * (θ * P) = 0 := by
    calc cT s x * Jw * (θ * P) = cT s (M * x) * P := by
          rw [Formalism.UG.cT_mul, hMh, ← hθM]; simp only [Matrix.mul_assoc]
      _ = cT s d0 * (cT s y * Jw * P) := by
          rw [hMdef, hcar, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hyP, Matrix.mul_zero]
  have hyθP : cT s y * Jw * (θ * P) = 0 := by
    calc cT s y * Jw * (θ * P) = cT s (M * y) * P := by
          rw [Formalism.UG.cT_mul, hMh, ← hθM]; simp only [Matrix.mul_assoc]
      _ = cT s s1 * (cT s x * Jw * P) := by
          rw [hMy, Formalism.UG.cT_mul s (Jw * x) s1, Formalism.UG.cT_mul s Jw x, hJ]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hxP, Matrix.mul_zero]
  have hPiθ : (1 - x * (cT s y * Jw) - y * (cT s x * Jw)) * (θ * P) = θ * P := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc x, Matrix.mul_assoc y, hxθP, hyθP, Matrix.mul_zero, Matrix.mul_zero, sub_zero, sub_zero]
  have hkey : P * (Lm * θ * P) = θ * P := by
    calc P * (Lm * θ * P) = P * Lm * (1 - x * (cT s y * Jw) - y * (cT s x * Jw)) * (θ * P) := by
          rw [Matrix.mul_assoc (P * Lm), hPiθ]; simp only [Matrix.mul_assoc]
      _ = θ * P := by rw [hPi, hPiθ]
  refine ⟨?_, ?_, ?_⟩
  · calc Lm * θ * P * (Lm * θ * P) = Lm * θ * (P * (Lm * θ * P)) := by simp only [Matrix.mul_assoc]
      _ = Lm * (θ * θ) * P := by rw [hkey]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hθθ, Matrix.mul_one, hLP]
  · calc cT s (B * P) * (B * P) = cT s P * (Jw * θ) * P := by
          rw [Formalism.UG.cT_mul, hθM, hMdef]; simp only [Matrix.mul_assoc]
      _ = cT s P * Jw * (P * (Lm * θ * P)) := by rw [hkey]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · calc Lm * A * (B * P) = Lm * (A * B) * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, hLP]

end Gen

section Core

open Matrix
open scoped ComplexOrder

theorem herm_diag {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian) :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      Uᴴ * A * U = diagonal (fun i => (d i : ℂ)) ∧ (A.PosDef → ∀ i, 0 < d i) := by
  have h1 := Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  have h2 := Matrix.mem_unitaryGroup_iff.1 hA.eigenvectorUnitary.2
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ), hA.eigenvalues, h1, h2, ?_, fun hp i => hp.eigenvalues_pos i⟩
  have e := congrArg (fun X : Matrix (Fin m) (Fin m) ℂ => (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ * X *
    (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)) hA.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at e
  rw [e]
  calc _ = ((hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)) *
        diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
        ((hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]; rfl

theorem core_C : ∀ (n m : ℕ) (C : Matrix (Fin n) (Fin m) ℂ) (L : Matrix (Fin m) (Fin n) ℂ) (J0 θ0 : Matrix (Fin m) (Fin m) ℂ),
    L * C = 1 → J0ᴴ = J0 → θ0 * θ0 = 1 → Cᴴ * C = J0 * θ0 →
    ∃ g : GL (Fin m) ℂ, (∃ ε : Fin m → Bool, g.1ᴴ * J0 * g.1 = Matrix.diagonal fun i => if ε i then 1 else -1) ∧
      (g⁻¹).1ᴴ * (g⁻¹).1 = Cᴴ * C := by
  intro n m C L J0 θ0 hLC hJ hθ hCC
  have hinj : Function.Injective C.mulVec := fun u v huv => by
    have := congrArg L.mulVec huv
    simpa [Matrix.mulVec_mulVec, hLC] using this
  have hpd := Matrix.PosDef.conjTranspose_mul_self C hinj
  obtain ⟨U, μ, hU1, hU2, hUd, hpos⟩ := herm_diag hpd.1
  have hμ := hpos hpd
  set M0 := Cᴴ * C with hM0
  obtain ⟨h, hdef⟩ : ∃ h : Matrix (Fin m) (Fin m) ℂ, h = U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := ⟨_, rfl⟩
  obtain ⟨h', hdef'⟩ : ∃ h' : Matrix (Fin m) (Fin m) ℂ, h' = diagonal (fun i => ((Real.sqrt (μ i) : ℝ) : ℂ)) * Uᴴ :=
    ⟨_, rfl⟩
  have hsq : ∀ i, ((Real.sqrt (μ i) : ℝ) : ℂ) * ((Real.sqrt (μ i))⁻¹ : ℂ) = 1 := fun i => by
    have : (Real.sqrt (μ i) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hμ i)).ne'
    field_simp
  have hhh' : h * h' = 1 := by
    calc h * h' = U * (diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * diagonal (fun i => ((Real.sqrt (μ i) : ℝ) : ℂ))) * Uᴴ := by
          simp only [hdef, hdef', Matrix.mul_assoc]
      _ = 1 := by
          rw [diagonal_mul_diagonal]
          simp only [fun i => mul_comm ((Real.sqrt (μ i))⁻¹ : ℂ) ((Real.sqrt (μ i) : ℝ) : ℂ), hsq, diagonal_one, Matrix.mul_one, hU2]
  have hh'h : h' * h = 1 := by
    calc h' * h = diagonal (fun i => ((Real.sqrt (μ i) : ℝ) : ℂ)) * (Uᴴ * U) * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
          simp only [hdef, hdef', Matrix.mul_assoc]
      _ = 1 := by rw [hU1, Matrix.mul_one, diagonal_mul_diagonal]; simp only [hsq, diagonal_one]
  have hhc : hᴴ = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * Uᴴ := by
    simp only [hdef, conjTranspose_mul, diagonal_conjTranspose]
    congr 2
    funext i
    simp [Complex.conj_ofReal]
  have hh : hᴴ * M0 * h = 1 := by
    rw [hhc]
    calc _ = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * (Uᴴ * M0 * U) * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
          rw [hdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hUd, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          funext i
          have h0 : (Real.sqrt (μ i) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hμ i)).ne'
          have h1 : ((Real.sqrt (μ i) : ℝ) : ℂ) * (Real.sqrt (μ i) : ℝ) = μ i := by
            rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hμ i).le]
          rw [← h1]
          field_simp
  have hhM : h * hᴴ * M0 = 1 := by
    calc h * hᴴ * M0 = h * (hᴴ * M0 * h) * h' := by
          simp only [Matrix.mul_assoc, hhh', Matrix.mul_one]
      _ = 1 := by rw [hh, Matrix.mul_one, hhh']
  have hJM : J0 = M0 * θ0 := by rw [hCC, Matrix.mul_assoc, hθ, Matrix.mul_one]
  set K := hᴴ * J0 * h with hKdef
  have hKh : K.IsHermitian := by
    change (hᴴ * J0 * h)ᴴ = _
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ]; simp only [hKdef, Matrix.mul_assoc]
  have hKK : K * K = 1 := by
    calc K * K = hᴴ * M0 * θ0 * (h * hᴴ * M0) * θ0 * h := by
          rw [hKdef, hJM]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hhM, Matrix.mul_one, Matrix.mul_assoc (hᴴ * M0), hθ, Matrix.mul_one, hh]
  obtain ⟨V, lam, hV1, hV2, hVd, -⟩ := herm_diag hKh
  have hlam : ∀ i, lam i = 1 ∨ lam i = -1 := fun i => by
    have e : diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ)) = 1 := by
      rw [← hVd]
      calc _ = Vᴴ * K * (V * Vᴴ) * K * V := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hV2, Matrix.mul_one, Matrix.mul_assoc Vᴴ K K, hKK, Matrix.mul_one, hV1]
    have := congrFun (congrFun e i) i
    simp only [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at this
    have h2 : lam i * lam i = 1 := by exact_mod_cast this
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨g, hg1, hg2⟩ : ∃ g : GL (Fin m) ℂ, g.1 = h * V ∧ (g⁻¹).1 = Vᴴ * h' := ⟨⟨h * V, Vᴴ * h', by
    calc h * V * (Vᴴ * h') = h * (V * Vᴴ) * h' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV2, Matrix.mul_one, hhh'], by
    calc Vᴴ * h' * (h * V) = Vᴴ * (h' * h) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh'h, Matrix.mul_one, hV1]⟩, rfl, rfl⟩
  have hgM : g.1ᴴ * M0 * g.1 = 1 := by
    rw [hg1, conjTranspose_mul]
    calc _ = Vᴴ * (hᴴ * M0 * h) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, Matrix.mul_one, hV1]
  refine ⟨g, ⟨fun i => decide (lam i = 1), ?_⟩, ?_⟩
  · rw [hg1, conjTranspose_mul]
    calc _ = Vᴴ * K * V := by simp only [hKdef, Matrix.mul_assoc]
      _ = _ := by
        rw [hVd]
        congr 1
        funext i
        rcases hlam i with e | e <;> simp [e] <;> norm_num
  · have hgg : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (g⁻¹).1ᴴ * (g⁻¹).1 = (g⁻¹).1ᴴ * (g.1ᴴ * M0 * g.1) * (g⁻¹).1 := by rw [hgM, Matrix.mul_one]
      _ = (g.1 * (g⁻¹).1)ᴴ * M0 * (g.1 * (g⁻¹).1) := by rw [conjTranspose_mul g.1]; simp only [Matrix.mul_assoc]
      _ = M0 := by rw [hgg, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

end Core

section Transport

theorem simulR_pf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (n m : ℕ) (C : Matrix (Fin n) (Fin m) (w.Completion ⊗[F] E))
    (L : Matrix (Fin m) (Fin n) (w.Completion ⊗[F] E)) (J0 θ0 : Matrix (Fin m) (Fin m) (w.Completion ⊗[F] E)),
    IsCMExt F E σ → L * C = 1 → Formalism.UG.cT (sigR _ σ) J0 = J0 → θ0 * θ0 = 1 → Formalism.UG.cT (sigR _ σ) C * C = J0 * θ0 →
    ∃ g : GL (Fin m) (w.Completion ⊗[F] E), (∃ ε : Fin m → Bool, Formalism.UG.cT (sigR _ σ) g.1 * J0 * g.1 =
      Matrix.diagonal fun i => if ε i then 1 else -1) ∧ Formalism.UG.cT (sigR _ σ) (g⁻¹).1 * (g⁻¹).1 = Formalism.UG.cT (sigR _ σ) C * C := by
  intro F E _ _ _ _ _ σ w n m C L J0 θ0 hσ hLC hJ hθ hCC
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  have hb := infEmb_bijective hσ τ
  let e : (w.Completion ⊗[F] E) ≃+* ℂ := RingEquiv.ofBijective (infEmb τ) hb
  have hcT : ∀ {k l : ℕ} (Z : Matrix (Fin k) (Fin l) (w.Completion ⊗[F] E)),
      (Formalism.UG.cT (sigR _ σ) Z).map (infEmb τ) = (Z.map (infEmb τ))ᴴ := fun Z =>
    Matrix.ext fun i j => (infEmb_sigR hσ τ (Z j i)).symm
  have hm : ∀ {k l p : ℕ} (Z : Matrix (Fin k) (Fin l) (w.Completion ⊗[F] E)) (Z' : Matrix (Fin l) (Fin p) (w.Completion ⊗[F] E)),
      (Z * Z').map (infEmb τ) = Z.map (infEmb τ) * Z'.map (infEmb τ) := fun _ _ => Matrix.map_mul
  have h1 : ∀ {k : ℕ}, (1 : Matrix (Fin k) (Fin k) (w.Completion ⊗[F] E)).map (infEmb τ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  obtain ⟨g', ⟨ε, hg1⟩, hg2⟩ := core_C n m (C.map (infEmb τ)) (L.map (infEmb τ)) (J0.map (infEmb τ)) (θ0.map (infEmb τ))
    (by rw [← hm, hLC, h1]) (by rw [← hcT, hJ]) (by rw [← hm, hθ, h1]) (by rw [← hcT, ← hm, hCC, hm])
  have hgm : ∀ x : GL (Fin m) ℂ, (Formalism.UG.bc e.symm.toRingHom x).1.map (infEmb τ) = x.1 := fun x =>
    Matrix.ext fun i j => e.apply_symm_apply (x.1 i j)
  have hinj : ∀ {k l : ℕ} {Z Z' : Matrix (Fin k) (Fin l) (w.Completion ⊗[F] E)}, Z.map (infEmb τ) = Z'.map (infEmb τ) → Z = Z' :=
    fun h => Matrix.map_injective hb.1 h
  refine ⟨Formalism.UG.bc e.symm.toRingHom g', ⟨ε, hinj ?_⟩, hinj ?_⟩
  · simp only [hm, hcT, hgm]
    rw [hg1, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  · have hgi : ((Formalism.UG.bc e.symm.toRingHom g')⁻¹).1 = (Formalism.UG.bc e.symm.toRingHom g'⁻¹).1 := by rw [map_inv]
    simp only [hm, hcT, hgi, hgm]
    exact hg2
end Transport

section ESide

theorem eside_pf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    (∃ Lm : Matrix (Fin (dim σ J X Y)) (Fin n) E, Lm * P σ J X Y = 1 ∧
      P σ J X Y * Lm * (1 - X.submatrix id (fun _ : Fin 1 => 0) * (Formalism.UG.cT (σ : E →+* E) (Y.submatrix id (fun _ : Fin 1 => 0)) * J) -
        Y.submatrix id (fun _ : Fin 1 => 0) * (Formalism.UG.cT (σ : E →+* E) (X.submatrix id (fun _ : Fin 1 => 0)) * J)) =
      1 - X.submatrix id (fun _ : Fin 1 => 0) * (Formalism.UG.cT (σ : E →+* E) (Y.submatrix id (fun _ : Fin 1 => 0)) * J) -
        Y.submatrix id (fun _ : Fin 1 => 0) * (Formalism.UG.cT (σ : E →+* E) (X.submatrix id (fun _ : Fin 1 => 0)) * J)) ∧
    Formalism.UG.cT (σ : E →+* E) (X.submatrix id (fun _ : Fin 1 => 0)) * J * P σ J X Y = 0 ∧
    Formalism.UG.cT (σ : E →+* E) (Y.submatrix id (fun _ : Fin 1 => 0)) * J * P σ J X Y = 0 ∧
    P σ J X Y * X0 σ J X Y = X.submatrix id Fin.succ ∧ P σ J X Y * Y0 σ J X Y = Y.submatrix id Fin.succ := by
  intro F E _ _ _ _ _ σ n J r X Y hσ hJ hW
  have hb : ∀ (Z Z' : Matrix (Fin n) (Fin (r + 1)) E) (i j : Fin (r + 1)),
      hE σ J (fun k => Z k i) (fun k => Z' k j) = (Formalism.UG.cT (σ : E →+* E) Z * J * Z') i j := by
    intro Z Z' i j
    rw [hE_eq_dot]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp [mul_assoc]
  have hv : ∀ (Z : Matrix (Fin n) (Fin (r + 1)) E) (z : Fin n → E),
      hE σ J (GlobalTheory.EisMidHt.firstColumn Z) z = ((Formalism.UG.cT (σ : E →+* E) (Z.submatrix id (fun _ : Fin 1 => 0)) * J) *ᵥ z) 0 := by
    intro Z z
    rw [hE_eq_dot, ← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Formalism.UG.cT, GlobalTheory.EisMidHt.firstColumn]
  have h11 : ∀ (Z Z' : Matrix (Fin n) (Fin (r + 1)) E),
      Formalism.UG.cT (σ : E →+* E) (Z.submatrix id (fun _ : Fin 1 => 0)) * J * Z'.submatrix id (fun _ : Fin 1 => 0) =
        Matrix.of fun _ _ => (Formalism.UG.cT (σ : E →+* E) Z * J * Z') 0 0 := by
    intro Z Z'
    ext i j
    simp [Matrix.mul_apply, Formalism.UG.cT]
  have hyx := GlobalTheory.StdPar.yx hσ hJ hW
  have exx : Formalism.UG.cT (σ : E →+* E) (X.submatrix id (fun _ : Fin 1 => 0)) * J * X.submatrix id (fun _ : Fin 1 => 0) = 0 := by
    rw [h11, hW.xx]; rfl
  have eyy : Formalism.UG.cT (σ : E →+* E) (Y.submatrix id (fun _ : Fin 1 => 0)) * J * Y.submatrix id (fun _ : Fin 1 => 0) = 0 := by
    rw [h11, hW.yy]; rfl
  have exy : Formalism.UG.cT (σ : E →+* E) (X.submatrix id (fun _ : Fin 1 => 0)) * J * Y.submatrix id (fun _ : Fin 1 => 0) = 1 := by
    rw [h11, hW.xy]; ext i j; fin_cases i; fin_cases j; simp
  have eyx : Formalism.UG.cT (σ : E →+* E) (Y.submatrix id (fun _ : Fin 1 => 0)) * J * X.submatrix id (fun _ : Fin 1 => 0) = 1 := by
    rw [h11, hyx]; ext i j; fin_cases i; fin_cases j; simp
  set x0 := X.submatrix id (fun _ : Fin 1 => (0 : Fin (r + 1))) with hx0
  set y0 := Y.submatrix id (fun _ : Fin 1 => (0 : Fin (r + 1))) with hy0
  set Pr := 1 - x0 * (Formalism.UG.cT (σ : E →+* E) y0 * J) - y0 * (Formalism.UG.cT (σ : E →+* E) x0 * J) with hPr
  have hxPr : Formalism.UG.cT (σ : E →+* E) x0 * J * Pr = 0 := by
    rw [hPr, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ x0, ← Matrix.mul_assoc _ y0, exx, exy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hyPr : Formalism.UG.cT (σ : E →+* E) y0 * J * Pr = 0 := by
    rw [hPr, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ x0, ← Matrix.mul_assoc _ y0, eyx, eyy,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hmem : ∀ z, (Formalism.UG.cT (σ : E →+* E) x0 * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) y0 * J) *ᵥ z = 0 →
      z ∈ V0 σ J X Y := fun z h1 h2 => (mem_invariant_forms σ J X Y).2 ⟨by rw [hv, h1]; rfl, by rw [hv, h2]; rfl⟩
  have hmem' : ∀ z, z ∈ V0 σ J X Y → (Formalism.UG.cT (σ : E →+* E) x0 * J) *ᵥ z = 0 ∧ (Formalism.UG.cT (σ : E →+* E) y0 * J) *ᵥ z = 0 := by
    intro z hz
    obtain ⟨h1, h2⟩ := (mem_invariant_forms σ J X Y).1 hz
    rw [hv] at h1 h2
    exact ⟨funext fun i => by rw [Subsingleton.elim i 0]; exact h1, funext fun i => by rw [Subsingleton.elim i 0]; exact h2⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (ι σ J X Y) (LinearMap.ker_eq_bot.2 (ι_injective σ J X Y))
  have hgι : ∀ u, g (ι σ J X Y u) = u := fun u => by
    have := LinearMap.congr_fun hg u
    simpa using this
  have hLv : ∀ v, LinearMap.toMatrix' g *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec g v
  refine ⟨⟨LinearMap.toMatrix' g, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, hLv, ← ι_apply, hgι, Matrix.one_mulVec]
  · refine Matrix.ext_of_mulVec_single fun i => ?_
    have hz : Pr *ᵥ Pi.single i 1 ∈ V0 σ J X Y := hmem _
      (by rw [Matrix.mulVec_mulVec, hxPr, Matrix.zero_mulVec]) (by rw [Matrix.mulVec_mulVec, hyPr, Matrix.zero_mulVec])
    obtain ⟨u, hu⟩ := exists_ι_eq σ J X Y hz
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu, hLv, hgι, ι_apply]
  · refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← ι_apply, (hmem' _ (ι_mem σ J X Y _)).1, Matrix.zero_mulVec]
  · refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← ι_apply, (hmem' _ (ι_mem σ J X Y _)).2, Matrix.zero_mulVec]
  · ext i j
    have hc : (fun k => X k j.succ) ∈ V0 σ J X Y := (mem_invariant_forms σ J X Y).2
      ⟨(hb X X 0 j.succ).trans (by rw [hW.xx]; rfl), (hb Y X 0 j.succ).trans (by rw [hyx, Matrix.one_apply_ne (Fin.succ_ne_zero j).symm])⟩
    have := congrFun (ι_coordTail σ J X Y X j hc) i
    rw [ι_apply] at this
    exact this
  · ext i j
    have hc : (fun k => Y k j.succ) ∈ V0 σ J X Y := (mem_invariant_forms σ J X Y).2
      ⟨(hb X Y 0 j.succ).trans (by rw [hW.xy, Matrix.one_apply_ne (Fin.succ_ne_zero j).symm]), (hb Y Y 0 j.succ).trans (by rw [hW.yy]; rfl)⟩
    have := congrFun (ι_coordTail σ J X Y Y j hc) i
    rw [ι_apply] at this
    exact this

end ESide

theorem restrict_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), GlobalTheory.EisLine.IsAdapted σ J X Y L a →
    ∀ w : InfinitePlace F, ∃ g : GL (Fin (dim σ J X Y)) (w.Completion ⊗[F] E),
      (∃ ε : Fin (dim σ J X Y) → Bool, Formalism.UG.cT (sigR _ σ) g.1 * JR (F := F) w.Completion (J0 σ J X Y) * g.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧
      (∃ c : Fin r → w.Completion ⊗[F] E, Formalism.UG.cT (sigR _ σ) (g⁻¹).1 * (g⁻¹).1 * (X0 σ J X Y).map (inclR (F := F) w.Completion) =
        (JR (F := F) w.Completion (J0 σ J X Y) * (Y0 σ J X Y).map (inclR (F := F) w.Completion) : Matrix _ _ (w.Completion ⊗[F] E)) * Matrix.diagonal c) ∧
      Formalism.UG.cT (sigR _ σ) (g⁻¹).1 * (g⁻¹).1 = Formalism.UG.cT (sigR _ σ) ((P σ J X Y).map (inclR (F := F) w.Completion)) *
        (Formalism.UG.cT (sigR _ σ) (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1) * (P σ J X Y).map (inclR (F := F) w.Completion) := by
  intro F E _ _ _ _ _ σ n J r X Y hσ hJ hW L a hA w
  obtain ⟨⟨Lm, hLP, hPi⟩, hxP, hyP, hPX, hPY⟩ := eside_pf σ n J r X Y hσ hJ hW
  obtain ⟨ε, hε⟩ := hA.maj w
  obtain ⟨c, hc⟩ := hA.cartan w
  have hs : ∀ y, sigR w.Completion σ (sigR w.Completion σ y) = y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma hσ x)
  have hmc : ∀ {k l : ℕ} (Z : Matrix (Fin k) (Fin l) E),
      cT (sigR w.Completion σ) (Z.map (inclR (F := F) w.Completion)) = (cT (σ : E →+* E) Z).map (inclR (F := F) w.Completion) :=
    fun _ => rfl
  have hAB : (Formalism.UG.bc (compInf F E w) a).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hBA : (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hDD : (Matrix.diagonal fun i => if ε i then (1 : w.Completion ⊗[F] E) else -1) *
      (Matrix.diagonal fun i => if ε i then (1 : w.Completion ⊗[F] E) else -1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> simp
  have hJh : cT (sigR w.Completion σ) (JR (F := F) w.Completion J) = JR (F := F) w.Completion J := by
    rw [JR, hmc]; congr 1; exact Matrix.ext fun i j => hJ.1 i j
  have hyx : cT (σ : E →+* E) (Y.submatrix id (fun _ : Fin 1 => 0)) * J * X.submatrix id (fun _ : Fin 1 => 0) = 1 := by
    have h := congrFun (congrFun (GlobalTheory.StdPar.yx hσ hJ hW) 0) 0
    ext i j
    fin_cases i; fin_cases j
    simpa [Matrix.mul_apply, cT] using h
  have hcar0 : cT (sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1 *
      (X.submatrix id (fun _ : Fin 1 => 0)).map (inclR (F := F) w.Completion) =
      (JR (F := F) w.Completion J * (Y.submatrix id (fun _ : Fin 1 => 0)).map (inclR (F := F) w.Completion) :
        Matrix (Fin n) (Fin 1) (w.Completion ⊗[F] E)) * Matrix.diagonal (fun _ : Fin 1 => c 0) := by
    ext i j
    fin_cases j
    have h := congrFun (congrFun hc i) 0
    rw [Matrix.mul_diagonal] at h
    rw [Matrix.mul_diagonal]
    exact h
  have hcarT : cT (sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1 *
      (X.submatrix id Fin.succ).map (inclR (F := F) w.Completion) =
      (JR (F := F) w.Completion J * (Y.submatrix id Fin.succ).map (inclR (F := F) w.Completion) :
        Matrix (Fin n) (Fin r) (w.Completion ⊗[F] E)) * Matrix.diagonal (c ∘ Fin.succ) := by
    ext i j
    have h := congrFun (congrFun hc i) j.succ
    rw [Matrix.mul_diagonal] at h
    rw [Matrix.mul_diagonal]
    exact h
  have hmap : ∀ {k l p : ℕ} (Z : Matrix (Fin k) (Fin l) E) (Z' : Matrix (Fin l) (Fin p) E),
      (Z * Z').map (inclR (F := F) w.Completion) = Z.map (inclR (F := F) w.Completion) * Z'.map (inclR (F := F) w.Completion) :=
    fun _ _ => Matrix.map_mul
  have hmap0 : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) E).map (inclR (F := F) w.Completion) = 0 :=
    Matrix.map_zero _ (map_zero _)
  have hmap1 : ∀ {k : ℕ}, (1 : Matrix (Fin k) (Fin k) E).map (inclR (F := F) w.Completion) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hmapsub : ∀ {k l : ℕ} (Z Z' : Matrix (Fin k) (Fin l) E),
      (Z - Z').map (inclR (F := F) w.Completion) = Z.map (inclR (F := F) w.Completion) - Z'.map (inclR (F := F) w.Completion) :=
    fun Z Z' => Matrix.map_sub _ (map_sub _) Z Z'
  have hPiw := congrArg (Matrix.map · (inclR (F := F) w.Completion)) hPi
  have hLPw := congrArg (Matrix.map · (inclR (F := F) w.Completion)) hLP
  have hxPw := congrArg (Matrix.map · (inclR (F := F) w.Completion)) hxP
  have hyPw := congrArg (Matrix.map · (inclR (F := F) w.Completion)) hyP
  have hyxw := congrArg (Matrix.map · (inclR (F := F) w.Completion)) hyx
  have hk := key (sigR w.Completion σ) hs (A := (Formalism.UG.bc (compInf F E w) a).1) (B := (Formalism.UG.bc (compInf F E w) a⁻¹).1)
    (Jw := JR (F := F) w.Completion J) (D := Matrix.diagonal fun i => if ε i then (1 : w.Completion ⊗[F] E) else -1)
    (x := (X.submatrix id (fun _ : Fin 1 => 0)).map (inclR (F := F) w.Completion))
    (y := (Y.submatrix id (fun _ : Fin 1 => 0)).map (inclR (F := F) w.Completion))
    (P := (P σ J X Y).map (inclR (F := F) w.Completion)) (Lm := Lm.map (inclR (F := F) w.Completion))
    (d0 := Matrix.diagonal (fun _ : Fin 1 => c 0)) hAB hBA hDD hε hJh (by simpa only [JR, hmc, hmap, hmapsub, hmap1, hmap0] using hLPw)
    (by simpa only [JR, hmc, hmap, hmapsub, hmap1, hmap0] using hPiw)
    (by simpa only [JR, hmc, hmap, hmapsub, hmap1, hmap0] using hxPw)
    (by simpa only [JR, hmc, hmap, hmapsub, hmap1, hmap0] using hyPw)
    (by simpa only [JR, hmc, hmap, hmapsub, hmap1, hmap0] using hyxw) (by exact hcar0)
  obtain ⟨h1, h2, h3⟩ := hk
  have hJ0 : JR (F := F) w.Completion (J0 σ J X Y) = cT (sigR w.Completion σ) ((P σ J X Y).map (inclR (F := F) w.Completion)) *
      JR (F := F) w.Completion J * (P σ J X Y).map (inclR (F := F) w.Completion) := by
    rw [JR, J0, hmap, hmap, hmc]; rfl
  have hJ0h : cT (sigR w.Completion σ) (JR (F := F) w.Completion (J0 σ J X Y)) = JR (F := F) w.Completion (J0 σ J X Y) := by
    rw [hJ0, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT _ hs, hJh, Matrix.mul_assoc]
  obtain ⟨g, hg1, hg2⟩ := simulR_pf σ w n _ _ _ (JR (F := F) w.Completion (J0 σ J X Y)) _ hσ h3 hJ0h h1 (h2.trans (by rw [hJ0]))
  refine ⟨g, hg1, ⟨c ∘ Fin.succ, ?_⟩, ?_⟩
  · show cT (sigR w.Completion σ) (g⁻¹).1 * (g⁻¹).1 * (X0 σ J X Y).map (inclR (F := F) w.Completion) =
      (JR (F := F) w.Completion (J0 σ J X Y) * (Y0 σ J X Y).map (inclR (F := F) w.Completion) :
        Matrix (Fin (dim σ J X Y)) (Fin r) (w.Completion ⊗[F] E)) * Matrix.diagonal (c ∘ Fin.succ)
    rw [hg2, hJ0, Formalism.UG.cT_mul]
    have hX := congrArg (Matrix.map · (inclR (F := F) w.Completion)) hPX
    have hY := congrArg (Matrix.map · (inclR (F := F) w.Completion)) hPY
    simp only [hmap] at hX hY
    calc _ = cT (sigR w.Completion σ) ((P σ J X Y).map (inclR (F := F) w.Completion)) *
          (cT (sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1 *
          ((P σ J X Y).map (inclR (F := F) w.Completion) * (X0 σ J X Y).map (inclR (F := F) w.Completion))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hX, hcarT, ← hY]; simp only [Matrix.mul_assoc]
  · rw [hg2, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]

end GlobalTheory.EisRestrictInf

end
