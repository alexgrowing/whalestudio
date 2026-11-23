import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.JInvJumpGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbeddingIdempotentTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvMemDeRhamFilNegOfExactDegree
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.exists_letter_vector_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (x : P.R.B), IsUnit x → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ₀' τ' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) (j : ℕ), (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀' ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1) → (∀ a : ↥(K0 K), τ' ((⇑(P.PD K).σ)^[j] a) = τ₀' a) → ∀ d : ℤ, P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil d → P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil (d + 1) → ∃ w ∈ DcrisL (P.PD K) (charRep μ) τ', ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) d ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1) := by
  intro l _ P AI hT K LL x hx c hc μ τ₀' τ' j hμ hτ d hd hd1
  have := (P.PD K).finK₀
  obtain ⟨m, cc, kk, h1, hsum⟩ := GlobalTheory.exists_embedding_idempotent_tensor ℚ_[l] ↥(K0 K) ↥LL.1 τ'
  set y := (⇑P.φB)^[j] x with hy
  set z := P.ιB y with hzdef
  clear_value z y
  let f : ↥(K0 K) →ₗ[ℚ_[l]] P.R.B := (LinearMap.mulRight ℚ_[l] y) ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hB : ∀ s : ↥(K0 K), ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) = ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by
    intro s
    have := congrArg (LinearMap.lTensor ↥LL.1 f) (hsum s)
    simpa [f, map_sum, LinearMap.lTensor_tmul] using this
  have hφK : ∀ k : ↥(K0 K), P.φB (algebraMap ↥(K0 K) P.R.B k) = algebraMap ↥(K0 K) P.R.B ((P.PD K).σ k) := by
    intro k; rw [← P.PD_φ K]; exact (P.PD K).φ_K₀ k
  have hact : ∀ g : ↥(GK K), ∀ n : ℕ, P.actQ (g : GQ l) ((⇑P.φB)^[n] x) = algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[n] (c g : ↥(K0 K))) * (⇑P.φB)^[n] x := by
    intro g n
    have hcomm : ∀ b, P.actQ (g : GQ l) (P.φB b) = P.φB (P.actQ (g : GQ l) b) := by
      intro b
      have := (P.PD K).φ_comm g b
      rw [P.PD_φ, P.PD_φ, P.PD_actB, P.PD_actB] at this
      exact this.symm
    induction n with
    | zero => simpa using hc g
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [hcomm, ih, map_mul, hφK]
  have hterm : ∀ (g : ↥(GK K)) (a : ↥LL.1) (k : ↥(K0 K)),
      actVB (P.PD K) (charRep μ) g (a ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B k * y)) =
        (((μ g : (↥LL.1)ˣ) : ↥LL.1) * a) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[j] (c g : ↥(K0 K)) * k) * y) := by
    intro g a k
    simp only [actVB, AlgebraTensorModule.map_tmul]
    congr 1
    change (P.PD K).actB g (algebraMap ↥(K0 K) P.R.B k * y) = _
    rw [map_mul, AlgEquiv.commutes, P.PD_actB, hy, hact g j, map_mul]
    ring
  obtain ⟨w, hw⟩ : ∃ w : ↥LL.1 ⊗[ℚ_[l]] P.R.B, w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := ⟨_, rfl⟩
  have hinv : ∀ g : ↥(GK K), actVB (P.PD K) (charRep μ) g w = w := by
    intro g
    set s := (⇑(P.PD K).σ)^[j] (c g : ↥(K0 K))
    simp only [hw, map_sum, hterm]
    calc ∑ i, (((μ g : (↥LL.1)ˣ) : ↥LL.1) * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y)
        = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) := by
          rw [Finset.smul_sum]; simp only [TensorProduct.smul_tmul', smul_eq_mul]
      _ = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by rw [hB]
      _ = _ := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul', smul_eq_mul, ← mul_assoc, hτ, hμ, one_mul]

  have hlet : ∀ a : ↥(K0 K), mulVB (K₀ := ↥(K0 K)) (B := P.R.B) (V := ↥LL.1) (LL := ↥LL.1) a w = τ' a • w := by
    intro a
    simp only [hw, map_sum, mulVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    have : ∀ i, algebraMap ↥(K0 K) P.R.B a * (algebraMap ↥(K0 K) P.R.B (kk i) * y) = algebraMap ↥(K0 K) P.R.B (a * kk i) * y := by
      intro i; rw [map_mul, mul_assoc]
    simp only [this]
    rw [hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  have hι : ∀ k : ↥(K0 K), (P.PD K).ι (algebraMap ↥(K0 K) P.R.B k * y) = algebraMap ↥(K0 K) P.R.BdR k * z := by
    intro k; rw [map_mul, AlgHom.commutes, P.PD_ι, ← hzdef]
  have hιw : ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.BdR (kk i) * z) := by
    simp only [hw, map_sum, ιV, AlgebraTensorModule.map_tmul, LinearMap.id_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact hι (kk i)
  have hmem : ∀ k : ↥(K0 K), algebraMap ↥(K0 K) P.R.BdR k * z ∈ (P.PD K).Fil d := by
    intro k
    rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR, ← Algebra.smul_def]
    exact (P.PD K).Fil d |>.smul_mem _ hd
  refine ⟨w, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold Dcris
    refine (Submodule.mem_iInf _).2 fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hinv g, LinearMap.id_apply, sub_self]
  · refine (Submodule.mem_iInf _).2 fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hlet a, LinearMap.smul_apply, LinearMap.id_apply, sub_self]
  · rw [hιw]
    refine ⟨∑ i, cc i ⊗ₜ[ℚ_[l]] (⟨algebraMap ↥(K0 K) P.R.BdR (kk i) * z, hmem (kk i)⟩ : ↥(((P.PD K).Fil d).restrictScalars ℚ_[l])), ?_⟩
    simp [map_sum, AlgebraTensorModule.map_tmul]
  · intro hcon
    have hyu : ∀ n : ℕ, IsUnit ((⇑P.φB)^[n] x) := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih => rw [Function.iterate_succ_apply']; exact ih.map P.φB
    have hz : IsUnit z := by rw [hzdef, hy]; exact (hyu j).map P.ιB
    obtain ⟨v, hzv⟩ := hz.exists_right_inv
    have hvz : v * z = 1 := by rw [mul_comm]; exact hzv
    have hv : v ∈ (P.PD K).Fil (-d) := GlobalTheory.FilInv.inv_mem_Fil_neg l P AI hT K d z v hzv hd hd1
    let Mv : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] ↥LL.1 ⊗[ℚ_[l]] P.R.BdR :=
      AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) (LinearMap.mulLeft ℚ_[l] v)
    have hvmul : ∀ b ∈ ((P.PD K).Fil (d + 1)).restrictScalars ℚ_[l], LinearMap.mulLeft ℚ_[l] v b ∈ ((P.PD K).Fil 1).restrictScalars ℚ_[l] := by
      intro b hb
      have := (P.PD K).Fil_mul (-d) (d + 1) v b hv hb
      rw [show -d + (d + 1) = 1 by ring] at this
      exact this
    have hMv : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1), Mv t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1 := by
      rintro t ⟨s, rfl⟩
      refine ⟨AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) ((LinearMap.mulLeft ℚ_[l] v).restrict hvmul) s, ?_⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Mv, AlgebraTensorModule.map_tmul]
      | add s t hs ht => simp only [map_add, hs, ht]
    have hE : Mv (ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w) = ∑ i, cc i ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.BdR (kk i) := by
      rw [hιw, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Mv, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
      rw [mul_left_comm, hvz, mul_one]
    have hF1 := hMv _ hcon
    rw [hE] at hF1
    let q := (((P.PD K).Fil 1).restrictScalars ℚ_[l]).mkQ
    let h0 : ↥(K0 K) →ₗ[ℚ_[l]] P.R.BdR ⧸ (((P.PD K).Fil 1).restrictScalars ℚ_[l]) :=
      q ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.BdR).toLinearMap
    have hinj : Function.Injective h0 := by
      rw [injective_iff_map_eq_zero]
      intro k hk
      have hk' : algebraMap ↥(K0 K) P.R.BdR k ∈ (P.PD K).Fil 1 := by
        have := (Submodule.Quotient.mk_eq_zero _).1 hk
        exact this
      rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR] at hk'
      have := JsetEmb.field_inter_filtration_one_eq_zero (P.PD K) _ hk'
      exact (map_eq_zero_iff _ (algebraMap ↥(K0 K) ↥K.1).injective).1 this
    have hq : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1, LinearMap.lTensor ↥LL.1 q t = 0 := by
      rintro t ⟨s, rfl⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.lTensor_tmul]
        rw [show q ((((P.PD K).Fil 1).restrictScalars ℚ_[l]).subtype b) = 0 from (Submodule.Quotient.mk_eq_zero _).2 b.2, tmul_zero]
      | add s t hs ht => rw [map_add, map_add, hs, ht, add_zero]
    have hzero : LinearMap.lTensor ↥LL.1 h0 (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 0 := by
      have := hq _ hF1
      simpa [h0, map_sum, LinearMap.lTensor_tmul] using this
    have he : (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K)) = 0 :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := ↥LL.1) h0 hinj (hzero.trans (map_zero _).symm)
    let Λ : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K) →ₗ[ℚ_[l]] ↥LL.1 := TensorProduct.lift ((LinearMap.mul ℚ_[l] ↥LL.1).compl₂ τ'.toLinearMap)
    have hΛ : Λ (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 1 := by
      simp [Λ, map_sum, h1]
    rw [he, map_zero] at hΛ
    exact zero_ne_one hΛ
