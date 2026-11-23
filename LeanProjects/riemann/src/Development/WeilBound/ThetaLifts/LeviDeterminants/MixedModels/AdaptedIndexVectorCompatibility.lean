import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneC
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Vaceigen
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfActs

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace PositivityTheory.Mix

open Adapt GlobalTheory.LatVac
open scoped GlobalTheory.VacAny

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {n n₁ d j₀ j₁ r s r' s' : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {W : Spc F E d} {H : Plane E n n₁}

theorem hTens_frame (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hH : H.IsAdapted σ B X X₁ j₀ j₁) (J' : Matrix (Fin d) (Fin d) (AE F E))
    (w w' : Matrix (Fin n₁ ⊕ Fin 2) (Fin d) (AE F E)) : hTens (cA σ) (incM F X.J) J' (incM F (frame H) * w) (incM F (frame H) * w') =
      ∑ j, ∑ l, w (.inr 1) j * J' j l * cA σ (w' (.inr 0) l) + ∑ j, ∑ l, w (.inr 0) j * J' j l * cA σ (w' (.inr 1) l) +
        hTens (cA σ) (incM F X₁.J) J' (w.submatrix .inl id) (w'.submatrix .inl id) := by
  have hG : (incM F (frame H))ᵀ * incM F X.J * (incM F (frame H)).map (cA σ) =
      Matrix.fromBlocks (incM F X₁.J) 0 0 !![0, 1; 1, 0] := by
    have h := congrArg (incM F) (frame_gram hB hH (η := 1) (one_mul 1) fun i j => by rw [one_mul]; exact hX.herm i j)
    rw [incM_mul, incM_mul] at h
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · ext (i | i) (j | j)
      · rfl
      · simp [incM]
      · simp [incM]
      · fin_cases i <;> fin_cases j <;> simp [incM]
  have := hTens_mul (cA σ) (incM F X.J) J' (incM F (frame H)) (1 : Matrix (Fin d) (Fin d) (AE F E)) w w'
  rw [hG, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.mul_one, hTens_plane_left, one_mul] at this
  exact this

theorem chi_indep (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {θ θ' : 𝓞 E} (h : (θ : E) + σ θ = 1)
    (h' : (θ' : E) + σ θ' = 1) {v : Pl F} {γ} (hγ : γ ∈ latAtV X W v) :
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) := by
  have h0 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v (θ * (θ - θ')) 1 (by rw [map_one]; exact one_mem _)
    γ hγ γ hγ
  rw [← mul_one (B.ψ (_ * symp _ (inclR (F := F) (AF F) (θ' : E)) _ _ _ _)), ← h0, ← AddChar.map_add_eq_mul]
  congr 1
  have hc := cA_cA (σ := σ) hB
  have hh := GlobalTheory.VacCocycle.conj_hTens (cA σ) hc (JA := incM F X.J) (JB := incM F W.J) (fun i j => by
      show cA σ (inclR (F := F) (AF F) _) = inclR (F := F) (AF F) _
      rw [GlobalTheory.VacIndic.cA_inclR, hX.herm]) (fun i j => by
      show cA σ (inclR (F := F) (AF F) _) = -inclR (F := F) (AF F) _
      rw [GlobalTheory.VacIndic.cA_inclR, hW.skew, map_neg]) γ γ
  have e1 : cA σ (inclR (F := F) (AF F) (θ : E)) = 1 - inclR (F := F) (AF F) (θ : E) := by
    rw [GlobalTheory.VacIndic.cA_inclR, eq_sub_of_add_eq' h, map_sub, map_one]
  have e2 : cA σ (inclR (F := F) (AF F) (θ' : E)) = 1 - inclR (F := F) (AF F) (θ' : E) := by
    rw [GlobalTheory.VacIndic.cA_inclR, eq_sub_of_add_eq' h', map_sub, map_one]
  simp only [symp, one_mul]
  rw [show ((θ * (θ - θ') : 𝓞 E) : E) = θ * (θ - θ') by simp, map_mul (inclR (F := F) (AF F)), map_sub (inclR (F := F) (AF F))]
  generalize hTens (cA σ) (incM F X.J) (incM F W.J) γ γ = T at hh ⊢
  generalize inclR (F := F) (AF F) (θ : E) = a at e1 ⊢
  generalize inclR (F := F) (AF F) (θ' : E) = a' at e2 ⊢
  have t := GlobalTheory.VacCocycle.trace_conj (R := AF F) (cA σ) hc (a * (a - a') * T)
  rw [map_mul (cA σ), map_mul (cA σ), map_sub (cA σ), e1, e2, hh, show (1 - a) * (1 - a - (1 - a')) * -T = a * T - a' * T - a * (a - a') * T by ring,
    map_sub, map_sub] at t
  have h3 : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
  generalize (⅟(2 : AF F)) = u at h3 ⊢
  linear_combination u * t + (Algebra.trace (AF F) (AE F E) (a * (a - a') * T)) * h3

theorem loc_eig {ψ : AddChar (AF F) ℂ} (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    {v : Pl F} {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) {γ} (hγ : γ ∈ latAtV X W v) {c : ℂ}
    (h : Acts (evFin F v) (co.rho ψ γ) φ (c • φ)) : schr (psiAt ψ v) (locCo co v γ) φ = c • φ :=
  PositivityTheory.KCo.action_uniqueness F _ v _ φ hφ _ _ (GlobalTheory.VacBridge.rho_acts_locCo co ψ v γ ((latAtV_at_stable X W v).1 γ hγ) φ) h

theorem ext_ind {α β : Type} {j : α → β} {P : β → Prop} (h1 : ∀ a, P (j a)) (h2 : ∀ k, (¬ ∃ a, j a = k) → P k) (k : β) : P k := by
  by_cases h : ∃ a, j a = k
  · obtain ⟨a, rfl⟩ := h
    exact h1 a
  · exact h2 k h

theorem dot_extend {α β R : Type} [Fintype α] [Fintype β] {j : α → β} (hj : Function.Injective j) [CommRing R] (a : α → R) (q : β → R) :
    Function.extend j a 0 ⬝ᵥ q = a ⬝ᵥ fun i => q (j i) := by
  classical
  unfold dotProduct
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨j, hj⟩)) (fun k _ hk => by
      rw [Function.extend_apply' (f := j) a (0 : β → R) k (fun ⟨i, hi⟩ => hk (Finset.mem_map.2 ⟨i, Finset.mem_univ _, hi⟩))]; simp),
    Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ => by simp [hj.extend_apply]

theorem adapted_index_vector_compatibility : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (r₁ s₁ : ℕ), X₁.IsHerm σ B r₁ s₁ →
      H.IsAdapted σ B X X₁ j₀ j₁ → M₁.IsGood B.ψ →
      ∀ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)),
        Function.Injective j →
        (∀ z, co.e (incM F H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) →
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) →
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0) →
        ∀ (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ), (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v φ →
          ∃ c : ℂ, c ≠ 0 ∧ (fun y => φ (Function.extend j y 0)) = c • M₁.vac v
:= by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hX₁ hH hM₁ j co hj hι hx hy v φ hφ
  classical
  obtain ⟨hs, h0, θ, hθ, hA⟩ := hφ
  obtain ⟨hs₁, h0₁, θ₁, hθ₁, hA₁⟩ := hM₁.vac v
  have E0 := fun γ hγ => loc_eig co hs hγ (hA γ hγ)
  obtain ⟨Q, hPQ, hQP, hQ⟩ := exists_frame_inv hH hX.lat
  have hQ2 : incM F (frame H) * incM F Q = 1 := by rw [← incM_mul, hPQ, incM_one]
  have hW1 : ∀ u ∈ W.L, (1 : Matrix (Fin d) (Fin d) E) *ᵥ u ∈ W.L := fun u hu => by rwa [Matrix.one_mulVec]
  have hcont : Continuous fun y : Fin n₁ × Fin d → Fv F v => Function.extend j y (0 : Fin n × Fin d → Fv F v) :=
    continuous_pi (ext_ind (j := j) (fun a => by simpa only [hj.extend_apply] using continuous_apply a)
      fun k hk => by simpa only [Function.extend_apply' _ _ _ hk] using continuous_const)
  have hs' : (fun y => φ (Function.extend j y 0)) ∈ SB (Fin n₁ × Fin d → Fv F v) := by
    have hinv : Function.LeftInverse (fun (x : Fin n × Fin d → Fv F v) k => x (j k)) fun y => Function.extend j y 0 :=
      fun y => funext fun k => hj.extend_apply _ _ _
    exact ⟨hs.1.comp_continuous hcont, hs.2.comp_isClosedEmbedding (hinv.isClosedEmbedding (by fun_prop) hcont)⟩
  obtain ⟨c, hc⟩ := PositivityTheory.ThK.Vac.local_line M₁.co hB.std v (latAtV X₁ W v) (latAtV_at_stable X₁ W v).1
    (fun z hz h => PositivityTheory.ThK.Vac.mem_latAtV hB hX₁ hW v hz h) _ hs₁ hs' h0₁ (fun γ hγ => loc_eig M₁.co hs₁ hγ (hA₁ γ hγ))
    fun γ hγ => by
      have hγ' := lat_map (X₁ := X) (W₁ := W) (A := H.ι) (fun u hu => (hH.low u).1 hu) hW1 hγ
      rw [incM_one, Matrix.transpose_one, Matrix.mul_one] at hγ'
      have e1 : symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) (incM F H.ι * γ) (incM F H.ι * γ) =
          symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W.J) γ γ := by
        rw [symp, ← frame_iota, hTens_frame hB hX hH]
        simp [symp]
      funext y
      have := congrFun (E0 _ hγ') (Function.extend j y 0)
      rw [e1, chi_indep hB hX₁ hW hθ hθ₁ hγ] at this
      have l1 : (locCo co v (incM F H.ι * γ)).1 = Function.extend j (locCo M₁.co v γ).1 0 := funext (ext_ind (j := j)
        (fun a => by simp [locCo, hι, hj.extend_apply]) fun k hk => by simp [locCo, hι, Function.extend_apply' _ _ _ hk])
      have l2 : ∀ a, (locCo co v (incM F H.ι * γ)).2 (j a) = (locCo M₁.co v γ).2 a := fun a => by simp [locCo, hι, hj.extend_apply]
      have l3 : Function.extend j y 0 + Function.extend j (locCo M₁.co v γ).1 0 = Function.extend j (y + (locCo M₁.co v γ).1) 0 :=
        funext (ext_ind (j := j) (fun a => by simp [hj.extend_apply]) fun k hk => by simp [Function.extend_apply' _ _ _ hk])
      simp only [schr, l1, dot_extend hj, l2, l3] at this
      exact this
  refine ⟨c, fun hc0 => ?_, hc⟩
  rw [hc0, zero_smul] at hc
  obtain ⟨x, hx0⟩ := Function.ne_iff.1 h0
  let a : Fin n × Fin d → Fv F v := x - Function.extend j (fun i => x (j i)) 0
  have ha : ∀ i, a (j i) = 0 := fun i => by simp [a, hj.extend_apply]
  let u := co.e.symm (fun k => liftV v (a k), 0)
  have hu : co.e u = (fun k => liftV v (a k), 0) := co.e.apply_symm_apply _
  have huL : u ∈ latAtV X W v := by
    refine PositivityTheory.ThK.Vac.mem_latAtV hB hX hW v (fun t ht => ?_) fun γ hγ => ?_
    · rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      exact Prod.ext (funext fun i => at_liftV v _ t ht) (smul_zero _)
    · set w := incM F Q * γ with hw
      have hg := lat_map (X₁ := X) (W₁ := W) (mask_mem hH hQ 0 1 0) hW1 hγ
      have em : mask (AE F E) n₁ 0 1 0 * w = what₂ (0 : Matrix (Fin n₁) (Fin d) (AE F E)) (w (.inr 0)) 0 := by
        ext (i | i) l
        · simp [mask]
        · fin_cases i <;> simp [mask]
      have eg := frame_alt (F := F) (H := H) (w (.inr 0))
      rw [incM_one, Matrix.transpose_one, Matrix.mul_one, incM_mul, incM_mul, incM_mask, Matrix.mul_assoc, Matrix.mul_assoc, ← hw,
        em, eg] at hg
      have ed : γ = _ := (by rw [hw, ← Matrix.mul_assoc, hQ2, Matrix.one_mul] : γ = incM F (frame H) * w).trans (dec w)
      have h2 : (fun k => liftV v (a k)) ⬝ᵥ (co.e γ).2 =
          (fun k => liftV v (a k)) ⬝ᵥ (co.e (Matrix.vecMulVec (incV F H.x) (w (.inr 0)))).2 := by
        conv_lhs => rw [ed, map_add, map_add, Prod.snd_add, Prod.snd_add, hι, (hy _).1, add_zero, dotProduct_add]
        rw [dotProduct_comm _ (Function.extend _ _ _), dot_extend hj]
        simp [ha, dotProduct]
      have h3 := congrFun (E0 _ hg) x
      have h4 : symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J)
          (Matrix.vecMulVec (incV F H.x) (w (.inr 0))) (Matrix.vecMulVec (incV F H.x) (w (.inr 0))) = 0 := by
        rw [symp, ← eg, hTens_frame hB hX hH]
        simp [hTens]
      have l1 : (locCo co v (Matrix.vecMulVec (incV F H.x) (w (.inr 0)))).1 = 0 := funext fun k => by simp [locCo, (hx _).1]
      have l2 : x ⬝ᵥ (locCo co v (Matrix.vecMulVec (incV F H.x) (w (.inr 0)))).2 =
          a ⬝ᵥ (locCo co v (Matrix.vecMulVec (incV F H.x) (w (.inr 0)))).2 := by
        simp only [a, sub_dotProduct, dot_extend hj]
        simp [locCo, (hx _).2, dotProduct]
      simp only [schr, l1, l2, h4, zero_dotProduct, mul_zero, add_zero, AddChar.map_zero_eq_one, one_smul] at h3
      have h5 := mul_right_cancel₀ hx0 (h3.trans (one_mul _).symm)
      rw [co.form, hu, dotProduct_zero, zero_sub, h2, AddChar.map_neg_eq_inv, inv_eq_one, ← h5]
      change _ = B.ψ (liftV v _)
      congr 1
      simp only [dotProduct, map_sum, PositivityTheory.ThK.Vac.liftV_mul]
      rfl
  have h6 := congrFun (E0 _ (neg_mem huL)) x
  have l1 : (locCo co v (-u)).1 = -a := funext fun k => by simp [locCo, hu, evFin_liftV]
  have l3 : x + -a = Function.extend j (fun i => x (j i)) 0 := by simp [a]
  have h7 := congrFun hc fun i => x (j i)
  simp only [Pi.zero_apply] at h7
  simp only [schr, l1, l3, h7, mul_zero, Pi.smul_apply, smul_eq_mul] at h6
  exact mul_ne_zero (B.ψ.val_isUnit _).ne_zero hx0 h6.symm

end PositivityTheory.Mix
