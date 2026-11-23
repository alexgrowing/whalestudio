import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.AdmissibleVectors

open Matrix Topology
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open Formalism.BasicNotions.TH (GrpData URep GKMod Mat upq KFin)

variable {p q : ℕ} {T : GrpData p q}

theorem inner_piC (πU : URep T) (g : T.G) (a b : πU.H) : ⟪πU.π g a, πU.π g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (LinearIsometry.mk (πU.π g : πU.H →ₗ[ℂ] πU.H) (πU.isom g)).inner_map_map a b

theorem pi_mulC (πU : URep T) (g h : T.G) (v : πU.H) : πU.π (g * h) v = πU.π g (πU.π h v) := by rw [map_mul]; rfl

theorem sig_repC (πU : URep T) {σ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ → (πU.H →L[ℂ] πU.H)}
    (hσ : ∀ x, σ (rx (covC T x)) = ((((T.sq x : ℂˣ) : ℂ))⁻¹ ^ 0) • πU.π x) :
    Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (epq p q)) σ := by
  have hσ' : ∀ x, σ (rx (covC T x)) = πU.π x := fun x => by rw [hσ, pow_zero, one_smul]
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => sigC_contC πU hσ v⟩
  · simpa [covC, rx_oneC] using hσ' 1
  · obtain ⟨x, rfl⟩ := exists_lift'C T ha
    obtain ⟨y, rfl⟩ := exists_lift'C T hb
    rw [← rx_mulC, show covC T x * covC T y = covC T (x * y) by simp [covC], hσ', hσ', hσ', map_mul]
    rfl
  · obtain ⟨x, rfl⟩ := exists_lift'C T hg
    rw [hσ', πU.isom]

theorem kset_ofC {k : T.G} (hk : k ∈ T.Kset) : rx (covC T k) ∈ Formalism.REAL.Kset (epq p q) := by
  have hU : (rx (covC T k))ᴴ * Formalism.REAL.Jm (epq p q) * rx (covC T k) = Formalism.REAL.Jm (epq p q) := mem_UJC T k
  have hc : rx (covC T k) * Formalism.REAL.Jm (epq p q) = Formalism.REAL.Jm (epq p q) * rx (covC T k) := by
    rw [← rx_JC, ← rx_mulC, ← rx_mulC, (comm_iff_KC _).2 hk]
  refine ⟨?_, hc⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  calc (rx (covC T k))ᴴ * rx (covC T k)
      = (rx (covC T k))ᴴ * (rx (covC T k) * Formalism.REAL.Jm (epq p q)) * Formalism.REAL.Jm (epq p q) := by
        simp only [Matrix.mul_assoc, Jm_sqC, Matrix.mul_one]
    _ = 1 := by rw [hc, ← Matrix.mul_assoc, hU, Jm_sqC]

theorem kfinDense_coverC
    (hD : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
      Dense {v : H | Formalism.MainNotions.S.IsKFin ε σ v})
    (πU : URep T) : Dense {x | KFin T πU.π x} := by
  obtain ⟨z, hz⟩ := exists_zC T
  have hzz : z * z = 1 := eq_of_covC T (by rw [map_mul, hz.1, one_mul, map_one]) (by rw [map_mul, hz.2, map_one]; simp)
  have hzc : ∀ x, z * x = x * z := fun x =>
    eq_of_covC T (by rw [map_mul, map_mul, hz.1, one_mul, mul_one]) (by rw [map_mul, map_mul, mul_comm])
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = πU.π z := ⟨_, rfl⟩
  have hZZ : Z * Z = 1 := by rw [hZ, ← map_mul, hzz, map_one]
  have hZc : ∀ x, πU.π x * Z = Z * πU.π x := fun x => by rw [hZ, ← map_mul, ← map_mul, hzc]
  let D : ℂ → (πU.H →L[ℂ] πU.H) := fun c => ((1 + c) / 2) • 1 + ((1 - c) / 2) • Z
  have hDD : ∀ c d, D c * D d = D (c * d) := fun c d => by
    simp only [D, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hZZ]
    module
  have hD1 : D 1 = 1 := by simp [D]
  have hDc : ∀ c x, πU.π x * D c = D c * πU.π x := fun c x => by
    simp only [D, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hZc]
  have hZi : ∀ a b, ⟪Z a, Z b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b => hZ ▸ inner_piC πU z a b
  have hZa : ∀ a b, ⟪Z a, b⟫_ℂ = ⟪a, Z b⟫_ℂ := fun a b => by
    rw [← hZi a (Z b), ← ContinuousLinearMap.mul_apply Z Z, hZZ]; rfl
  have hDi : ∀ c : ℂ, ‖c‖ = 1 → ∀ v, ‖D c v‖ = ‖v‖ := fun c hc v => by
    have h1 : (starRingEnd ℂ) c * c = 1 := by rw [Complex.conj_mul', hc]; simp
    have h2 : ⟪D c v, D c v⟫_ℂ = ⟪v, v⟫_ℂ := by
      simp only [D, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hZi, hZa v v, map_div₀, map_add, map_sub,
        map_one, map_ofNat]
      linear_combination ((⟪v, v⟫_ℂ - ⟪v, Z v⟫_ℂ) / 2) * h1
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by exact_mod_cast h2)
  let s : T.G → ℂ := fun x => ((T.sq x : ℂˣ) : ℂ)
  have hs0 : ∀ x, s x ≠ 0 := fun x => Units.ne_zero _
  let π' : URep T :=
    { H := πU.H
      π :=
        { toFun := fun x => D (s x)⁻¹ * πU.π x
          map_one' := by simp [s, hD1]
          map_mul' := fun x y => by
            rw [show s (x * y) = s x * s y by simp [s], mul_inv, ← hDD, map_mul, mul_assoc, mul_assoc,
              ← mul_assoc (D (s y)⁻¹), ← hDc, mul_assoc] }
      isom := fun g v => by
        show ‖D (s g)⁻¹ (πU.π g v)‖ = _
        rw [hDi _ (by rw [norm_inv, norm_sqC, inv_one]), πU.isom]
      cont := fun v => by
        have h1 : Continuous fun g => (s g)⁻¹ := (sq_contC T).inv₀ hs0
        have h2 := πU.cont v
        show Continuous fun g => ((1 + (s g)⁻¹) / 2) • πU.π g v + ((1 - (s g)⁻¹) / 2) • Z (πU.π g v)
        fun_prop }
  have hP : π'.π z = ((-1 : ℂ) ^ 0) • 1 := by
    show D (s z)⁻¹ * πU.π z = _
    rw [← hZ, show s z = -1 by simp [s, hz.2]]
    simp [D, hZZ]
  have hσ := sigC_eq π' hz hP
  refine (hD _ _ _ _ (sig_repC π' hσ)).mono ?_
  rintro v ⟨S, hSf, hv, hSK⟩
  refine Submodule.finiteDimensional_of_le (S₂ := S ⊔ S.map (Z : πU.H →ₗ[ℂ] πU.H)) (Submodule.span_le.2 ?_)
  rintro _ ⟨⟨k, hk⟩, rfl⟩
  have h1 := hSK _ (kset_ofC hk) v hv
  rw [hσ, pow_zero, one_smul] at h1
  have h2 : πU.π k v = D (s k) (π'.π k v) := by
    show _ = (D (s k) * (D (s k)⁻¹ * πU.π k)) v
    rw [← mul_assoc, hDD, mul_inv_cancel₀ (hs0 k), hD1, one_mul]
  show πU.π k v ∈ _
  rw [h2]
  exact Submodule.add_mem_sup (S.smul_mem _ h1) (Submodule.smul_mem _ _ ⟨_, h1, rfl⟩)

theorem harish_chandra_third_clause (hD : ∀ (p q : ℕ) (T : GrpData p q) (πU : URep T), Dense {x | KFin T πU.π x}) : Clause3 := by
  rintro p q _ T πU M io ⟨hinj, hran, hd⟩ - ⟨hnt, hirr⟩
  refine ⟨hinj.nontrivial, fun S hS hinv => ?_⟩
  have : CompleteSpace S := hS.completeSpace_coe
  have hP : ∀ g v, S.starProjection (πU.π g v) = πU.π g (S.starProjection v) := fun g v => by
    refine Submodule.eq_starProjection_of_mem_orthogonal (hinv g _ (S.starProjection_apply_mem v)) fun w hw => ?_
    rw [← map_sub, ← inner_piC πU g⁻¹, ← pi_mulC, inv_mul_cancel, map_one]
    exact S.sub_starProjection_mem_orthogonal v _ (hinv _ w hw)
  have hK : ∀ v : M.V, ∃ u, io u = S.starProjection (io v) := fun v => by
    refine (hran _).2 ?_
    have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : T.Kset => πU.π k (io v))) := (hran _).1 ⟨v, rfl⟩
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : T.Kset => πU.π k (io v))).map
      (S.starProjection : πU.H →ₗ[ℂ] πU.H)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, hP _ _⟩
  have hN : ∀ Z, ∀ y ∈ S.comap io, M.act Z y ∈ S.comap io := fun Z y hy => by
    have key : ∀ Y ∈ upq p q, M.act Y y ∈ S.comap io := fun Y hY =>
      deriv_memC hS (hd Y hY y) fun t => hinv _ _ hy
    obtain ⟨Y₁, h₁, Y₂, h₂, e, -⟩ := upq_decC Z
    rw [e, map_add, map_smul]
    exact add_mem (key Y₁ h₁) (Submodule.smul_mem _ _ (key Y₂ h₂))
  rcases hirr _ hN with h | h
  · refine Or.inl (eq_bot_iff.2 fun v hv => ?_)
    have h0 : ∀ x, S.starProjection x = 0 := fun x => by
      refine (isClosed_eq S.starProjection.continuous continuous_const).closure_subset_iff.2 ?_ (hD p q T πU x)
      intro y hy
      obtain ⟨w, rfl⟩ := (hran y).2 hy
      obtain ⟨u, hu⟩ := hK w
      have : u ∈ S.comap io := show io u ∈ S from hu ▸ S.starProjection_apply_mem _
      rw [h] at this
      show S.starProjection (io w) = 0
      rw [← hu, (Submodule.mem_bot ℂ).1 this, map_zero]
    rw [← Submodule.starProjection_eq_self_iff.2 hv, h0]
    exact Submodule.zero_mem _
  · refine Or.inr (eq_top_iff.2 fun x _ => hS.closure_subset_iff.2 ?_ (hD p q T πU x))
    intro y hy
    obtain ⟨w, rfl⟩ := (hran y).2 hy
    exact show w ∈ S.comap io from h ▸ Submodule.mem_top

end CompanionTheory.D.gk.HC
