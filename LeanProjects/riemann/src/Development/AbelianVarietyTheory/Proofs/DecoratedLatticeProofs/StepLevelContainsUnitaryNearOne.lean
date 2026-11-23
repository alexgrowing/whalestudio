import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruent
import Formalism.LocalToGlobal.Columns.RecLevelTop
open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped Topology

noncomputable section

namespace GlobalTheory.LevelApprox

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.ColAd

theorem eq_zero_of_le_pow {γ t : WithZero (Multiplicative ℤ)} (hγ : γ < 1) (h : ∀ m : ℕ, t ≤ γ ^ m) : t = 0 := by
  by_contra ht
  by_cases hγ0 : γ = 0
  · have := h 1
    rw [hγ0, pow_one] at this
    exact ht (le_antisymm this zero_le')
  have hg : γ.log < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log hγ0]
    simpa using hγ
  set N : ℕ := (-t.log).toNat + 1 with hN
  have hm : t.log ≤ (N : ℤ) * γ.log := by
    have h3 : WithZero.exp t.log ≤ WithZero.exp (N • γ.log) := by
      rw [WithZero.exp_nsmul, WithZero.exp_log ht, WithZero.exp_log hγ0]
      exact h N
    rw [WithZero.exp_le_exp, nsmul_eq_mul] at h3
    exact h3
  have h1 : (N : ℤ) * γ.log ≤ -(N : ℤ) := by
    have : (0 : ℤ) ≤ (N : ℤ) := by positivity
    nlinarith
  have h2 := Int.self_le_toNat (-t.log)
  have h4 : (N : ℤ) = ((-t.log).toNat : ℤ) + 1 := by rw [hN]; push_cast; ring
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def SmallAt (Q : Finset (HeightOneSpectrum (𝓞 E))) (d : ℕ) : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  {a | (∀ w ∉ Q, adAt F w a = 0) ∧ ∀ w ∈ Q, Valued.v (adAt F w a) ≤ WithZero.exp (-(d : ℤ))}

theorem exists_smallAt_subset (Q : Finset (HeightOneSpectrum (𝓞 E))) {V : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hV : letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
      V ∈ 𝓝 (0 : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : ℕ, SmallAt (F := F) Q d ⊆ V := by
  classical
  letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  haveI := Formalism.L2.Col.adeles_t2Space (F := F) (E := E)
  obtain ⟨β, hβ0, hβ⟩ : ∃ β : 𝓞 E, β ≠ 0 ∧ ∀ P ∈ Q, β ∈ P.asIdeal := by
    choose f hf hf0 using fun P : HeightOneSpectrum (𝓞 E) => Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact ⟨∏ P ∈ Q, f P, Finset.prod_ne_zero_iff.2 fun P _ => hf0 P, fun P hP =>
      Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem f hP) (hf P)⟩
  set b : E := algebraMap (𝓞 E) E β with hb
  have hb0 : b ≠ 0 := by simpa [hb] using hβ0
  let ι : E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F := Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
  set e : E ⊗[F] FiniteAdeleRing (𝓞 F) F := ∑ P ∈ Q, PtExist.idem F P with he_def
  have he : ∀ w, adAt F w e = if w ∈ Q then 1 else 0 := by
    intro w
    rw [he_def, map_sum]
    simp only [PtExist.adAt_idem]
    exact Finset.sum_ite_eq Q w (fun _ => (1 : w.adicCompletion E))
  have hint : ∀ y ∈ Formalism.L2.Herm.intAf F E, ∀ w, Valued.v (adAt F w y) ≤ 1 := fun y hy w =>
    (mem_rInt_iff F E y).1 hy w
  have hbw : ∀ w ∈ Q, Valued.v (adAt F w (ι b)) < 1 := fun w hw => by
    rw [adAt_inclE, valued_algebraMap]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 (hβ w hw)
  have hbne : ∀ w, adAt F w (ι b) ≠ 0 := fun w => by
    rw [adAt_inclE]
    exact (map_ne_zero _).2 hb0
  let c : ℕ → E ⊗[F] FiniteAdeleRing (𝓞 F) F := fun m => e * ι b ^ m
  let K : ℕ → Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := fun m => (c m * ·) '' (Formalism.L2.Herm.intAf F E : Set _)
  have hKc : ∀ m, IsCompact (K m) := fun m => Formalism.L2.Col.rlt_isCompact_intAf.image (continuous_mul_left (c m))
  have hKa : Antitone K := by
    refine antitone_nat_of_succ_le fun m => ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨ι b * y, mul_mem (Formalism.L2.Col.iA_mem β) hy, ?_⟩
    simp only [c, pow_succ]
    ring
  have hK0 : ∀ x ∈ ⋂ m, K m, V ∈ 𝓝 x := by
    intro x hx
    have : x = 0 := by
      refine PtExist.ad_ext fun w => ?_
      rw [map_zero]
      by_cases hw : w ∈ Q
      · have h0 : Valued.v (adAt F w x) = 0 := eq_zero_of_le_pow (hbw w hw) fun m => by
          obtain ⟨y, hy, hxy⟩ := Set.mem_iInter.1 hx m
          rw [← hxy]
          simp only [c, map_mul, map_pow, he, if_pos hw, one_mul]
          exact mul_le_of_le_one_right' (hint y hy w)
        exact (Valuation.zero_iff _).1 h0
      · obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.1 hx 0
        simp only [c, map_mul, he, if_neg hw, zero_mul]
    rw [this]
    exact hV
  obtain ⟨m, hm⟩ := exists_subset_nhds_of_isCompact hKa.directed_ge hKc hK0

  let D : ℕ := ∑ w ∈ Q, (-(Valued.v (adAt F w (ι b))).log).toNat
  have hD : ∀ w ∈ Q, WithZero.exp (-(D : ℤ)) ≤ Valued.v (adAt F w (ι b)) := fun w hw => by
    have h0 : Valued.v (adAt F w (ι b)) ≠ 0 := (Valuation.ne_zero_iff _).2 (hbne w)
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    have h1 : (-(Valued.v (adAt F w (ι b))).log).toNat ≤ D :=
      Finset.single_le_sum (f := fun w => (-(Valued.v (adAt F w (ι b))).log).toNat) (fun _ _ => Nat.zero_le _) hw
    have h2 := Int.self_le_toNat (-(Valued.v (adAt F w (ι b))).log)
    omega
  refine ⟨m * D, fun a ha => hm ?_⟩
  have hinv : ∀ w, adAt F w (ι b⁻¹) = (adAt F w (ι b))⁻¹ := fun w => by
    rw [adAt_inclE, adAt_inclE, map_inv₀]
  refine ⟨e * ι b⁻¹ ^ m * a, (mem_rInt_iff F E _).2 fun w => ?_, ?_⟩
  · show Valued.v (adAt F w _) ≤ 1
    by_cases hw : w ∈ Q
    · simp only [map_mul, map_pow, he, hinv, if_pos hw, one_mul, map_inv₀, inv_pow, map_one]
      have hv : 0 < Valued.v (adAt F w (ι b)) ^ m :=
        pow_pos (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (hbne w))) m
      rw [inv_mul_le_one₀ hv]
      refine (ha.2 w hw).trans ?_
      have : WithZero.exp (-((m * D : ℕ) : ℤ)) = WithZero.exp (-(D : ℤ)) ^ m := by
        rw [← WithZero.exp_nsmul]
        congr 1
        push_cast
        ring
      rw [this]
      exact pow_le_pow_left₀ zero_le' (hD w hw) m
    · rw [map_mul, ha.1 w hw, mul_zero, map_zero]
      exact zero_le'
  · refine PtExist.ad_ext fun w => ?_
    simp only [c, map_mul, map_pow, he, hinv]
    by_cases hw : w ∈ Q
    · rw [if_pos hw, one_mul, one_mul, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (hbne w), one_pow, one_mul]
    · rw [ha.1 w hw, mul_zero, mul_zero]

end GlobalTheory.LevelApprox

namespace GlobalTheory.LevelApprox

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.ColAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_entry_sub_one {n : ℕ} (w : HeightOneSpectrum (𝓞 E)) (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (i j : Fin n) :
    adAt F w ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) = (locM w z - 1) i j := by
  rw [map_sub, Matrix.sub_apply]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem entry_mem_smallAt {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} {d : ℕ}
    {z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h1 : ∀ w ∉ Q, locM w z = 1)
    (h2 : ∀ w ∈ Q, Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z - 1)) (i j : Fin n) :
    (z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j ∈ SmallAt (F := F) Q d := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [adAt_entry_sub_one, h1 w hw, sub_self, Matrix.zero_apply]
  · rw [adAt_entry_sub_one]
    exact h2 w hw i j

theorem mem_U_of_near_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad)
    (Q : Finset (HeightOneSpectrum (𝓞 E))), ∃ d : ℕ, ∀ z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F),
    z ∈ Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ w ∉ Q, GlobalTheory.Mem.ColAd.locM w z = 1) →
    (∀ w ∈ Q, GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z - 1) ∧
      GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z⁻¹ - 1)) → z ∈ S.U := by
  intro F E _ _ _ _ _ σ n J T f bad S Q
  classical
  letI := Formalism.BasicNotions.tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  let A : ℕ → Set (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := fun d => {z | (∀ w ∉ Q, locM w z = 1) ∧
    ∀ w ∈ Q, Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z - 1) ∧ Sm Valued.v (WithZero.exp (-(d : ℤ))) (locM w z⁻¹ - 1)}
  have hexp : Antitone fun d : ℕ => WithZero.exp (-(d : ℤ)) := fun a b h =>
    WithZero.exp_le_exp.2 (by simpa using h)
  have hA : Antitone A := fun a b h z hz => ⟨hz.1, fun w hw => ⟨(hz.2 w hw).1.mono (hexp h), (hz.2 w hw).2.mono (hexp h)⟩⟩
  have hinv1 : ∀ z ∈ A 0, ∀ w ∉ Q, locM w z⁻¹ = 1 := fun z hz w hw => by
    have := locM_mul (P := w) z z⁻¹
    rw [mul_inv_cancel, locM_one, hz.1 w hw, one_mul] at this
    exact this.symm
  let G : Filter (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := ⨅ d, Filter.principal (A d)
  have hsmall : ∀ g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ d, ∀ z ∈ A d, g z ∈ SmallAt (F := F) Q d) → Filter.Tendsto g G (𝓝 0) := fun g hg V hV => by
    obtain ⟨d, hd⟩ := exists_smallAt_subset (F := F) Q hV
    exact Filter.mem_iInf_of_mem d (Filter.mem_principal.2 fun z hz => hd (hg d z hz))
  have hentry : ∀ (M : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) → Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      (∀ i j, Filter.Tendsto (fun z => M z i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j) G (𝓝 0)) →
      Filter.Tendsto M G (𝓝 1) := fun M hM =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => by
      have := (hM i j).add_const ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) i j)
      simpa using this
  have hT : Filter.Tendsto id G (𝓝 (1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Filter.Tendsto.prodMk_nhds ?_ ((MulOpposite.continuous_op.tendsto _).comp ?_)
    · refine hentry _ fun i j => hsmall _ fun d z hz => entry_mem_smallAt hz.1 (fun w hw => (hz.2 w hw).1) i j
    · refine hentry (fun z => ((z⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) fun i j => hsmall _ fun d z hz => ?_
      exact entry_mem_smallAt (fun w hw => hinv1 z (hA (Nat.zero_le d) hz) w hw) (fun w hw => (hz.2 w hw).2) i j
  have h1 : {x : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ S.U} ∈
      𝓝 (1 : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) := S.U_open.mem_nhds S.U.one_mem
  obtain ⟨t, ht, hts⟩ := (mem_nhds_subtype _ _ _).1 h1
  have hdir : Directed (· ≥ ·) fun d => Filter.principal (A d) :=
    Antitone.directed_ge (f := fun d => Filter.principal (A d)) fun a b h => Filter.principal_mono.2 (hA h)
  obtain ⟨d, hd⟩ := (Filter.mem_iInf_of_directed hdir _).1 (hT ht)
  exact ⟨d, fun z hz h1 h2 => hts (show (⟨z, hz⟩ : Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∈ Subtype.val ⁻¹' t from
    hd ⟨h1, h2⟩)⟩

end GlobalTheory.LevelApprox

end
