import Development.WeilBound.ThetaLifts.TowerModels.PlaneCodiff
import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicOfIndefinite

noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_skew (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra H
    push Not at H
    exact comp_conj_ne h τ (AlgHom.ext fun a => congrArg τ (H a))
  exact ⟨a - σ a, sub_ne_zero.2 ha.symm, by rw [map_sub, sigma_sigma h, neg_sub]⟩

theorem denseRange_emb (h : IsCMExt F E σ) (e : E →+* ℂ) : DenseRange e := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_skew h
  have h1 : star (e δ) = -e δ := by rw [← h.2.2.2 e, hδ, map_neg]
  have hre : (e δ).re = 0 := by
    have := congrArg Complex.re h1
    simp at this
    linarith
  have him : (e δ).im ≠ 0 := fun h0 => (map_ne_zero e).2 hδ0 (Complex.ext hre h0)
  let f : ℝ × ℝ → ℂ := fun p => p.1 + p.2 * e δ
  have hf : Function.Surjective f := fun z => ⟨(z.re, z.im / (e δ).im), Complex.ext (by simp [f, hre]) (by
    simp only [f, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul]
    field_simp
    simp)⟩
  have hd : DenseRange (f ∘ Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    hf.denseRange.comp (Rat.denseRange_cast.prodMap Rat.denseRange_cast) (by fun_prop)
  refine hd.mono ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact ⟨a + b * δ, by simp [f]⟩

theorem exists_pos_neg (h : IsCMExt F E σ) (e : E →+* ℂ) {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : HasSig M r s)
    (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (∃ x : Fin n → E, 0 < ((fun i => e (x i)) ⬝ᵥ M *ᵥ star fun i => e (x i)).re) ∧
      ∃ x : Fin n → E, ((fun i => e (x i)) ⬝ᵥ M *ᵥ star fun i => e (x i)).re < 0 := by
  obtain ⟨-, A, hA⟩ := hM
  have hd : DenseRange fun (x : Fin n → E) i => e (x i) := DenseRange.piMap fun _ => denseRange_emb h e
  have hc : Continuous fun Z : Fin n → ℂ => (Z ⬝ᵥ M *ᵥ star Z).re := by fun_prop
  have ent : ∀ a, (A *ᵥ Pi.single a 1) ⬝ᵥ M *ᵥ star (A *ᵥ Pi.single a 1) =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) a a := fun a => by
    rw [gram_vec, hA, ← Pi.single_star]; simp
  constructor
  · exact hd.exists_mem_open (isOpen_lt continuous_const hc)
      ⟨A *ᵥ Pi.single (Sum.inl ⟨0, hr⟩) 1, by simp only [Set.mem_setOf_eq, ent]; simp⟩
  · exact hd.exists_mem_open (isOpen_lt hc continuous_const)
      ⟨A *ᵥ Pi.single (Sum.inr ⟨0, hs⟩) 1, by simp only [Set.mem_setOf_eq, ent]; simp⟩

theorem exists_isotropic (h : IsCMExt F E σ) (emb : ∀ w : InfinitePlace F, EmbOver E w) {n r s : ℕ} (hn : 3 ≤ n)
    (hr : 1 ≤ r) (hs : 1 ≤ s) {J : Matrix (Fin n) (Fin n) E} (hdet : J.det ≠ 0) {ε : E} (hε : ε = 1 ∨ ε = -1)
    (hJ : ∀ i j, σ (J j i) = ε * J i j) {κ : ℂ} (hκ0 : κ ≠ 0) (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ)
    (hsig : ∀ w, HasSig (κ • J.map (emb w).1) r s) : ∃ x : Fin n → E, x ≠ 0 ∧ form σ J x x = 0 := by
  haveI := h.1
  haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ := exists_skew h
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : E, δ ≠ 0 ∧ σ δ * ε = δ := by
    rcases hε with rfl | rfl
    · exact ⟨1, one_ne_zero, by simp⟩
    · exact ⟨δ₀, hδ₀0, by simp [hδ₀]⟩
  have hf : ∀ x y, GlobalTheory.UTrans.hf (σ : E →+* E) (δ • J) x y = δ * form σ J x y := fun x y => by
    simp only [GlobalTheory.UTrans.hf, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul,
      RingHom.coe_coe]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.UTrans.exists_isotropic_of_indefinite E n (σ : E →+* E) (δ • J) (fun a => by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      apply τ.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact h.2.2.2 τ a)
    { invol := sigma_sigma h
      ne_id := ⟨δ₀, fun e => hδ₀0 (by
        have : σ δ₀ = δ₀ := e
        linear_combination (hδ₀ - this) / 2)⟩
      herm := fun a b => by
        change σ (δ * J a b) = δ * J b a
        rw [map_mul, hJ, ← mul_assoc, hδ]
      det_ne := by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hδ0) hdet } hn (fun τ => by
      let w : InfinitePlace F := InfinitePlace.mk (τ.comp (algebraMap F E))
      have hw : w.embedding = τ.comp (algebraMap F E) :=
        InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _)
      set e := (emb w).1 with he
      have k1 : ∀ a : E, σ a = a → τ a = e a := fun a ha => by
        have : a = algebraMap F E (Algebra.trace F E a / 2) := by
          rw [map_div₀, trace_cm h, ha, map_ofNat]; ring
        rw [this]
        exact (RingHom.congr_fun hw _).symm.trans (RingHom.congr_fun (emb w).2 _).symm
      have hε0 : e ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
      have hsκ : star κ ≠ 0 := star_ne_zero.2 hκ0
      have ht : star (e δ / κ) = e δ / κ := by
        rw [star_div₀, ← h.2.2.2 e, div_eq_div_iff hsκ hκ0]
        have a1 := congrArg e hδ
        rw [map_mul] at a1
        linear_combination star κ * a1 - e (σ δ) * hκ e
      obtain ⟨t, ht'⟩ : ∃ t : ℝ, (t : ℂ) = e δ / κ := ⟨_, Complex.conj_eq_iff_re.1 ht⟩
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact div_ne_zero ((map_ne_zero e).2 hδ0) hκ0 (by simpa using ht'.symm)
      have k2 : ∀ x, (τ (GlobalTheory.UTrans.hf (σ : E →+* E) (δ • J) x x)).re =
          t * ((fun i => e (x i)) ⬝ᵥ (κ • J.map e) *ᵥ star fun i => e (x i)).re := fun x => by
        rw [hf, k1 _ (by rw [map_mul, form_swap h hJ, ← mul_assoc, hδ]), map_mul, map_form h, Matrix.smul_mulVec,
          dotProduct_smul, smul_eq_mul, ← Complex.re_ofReal_mul, ht', ← mul_assoc, div_mul_cancel₀ _ hκ0]
      simp only [k2]
      obtain ⟨⟨x, hx⟩, y, hy⟩ := exists_pos_neg h e (hsig w) hr hs
      rcases lt_or_gt_of_ne ht0 with ht | ht
      · exact ⟨⟨y, mul_pos_of_neg_of_neg ht hy⟩, x, mul_neg_of_neg_of_pos ht hx⟩
      · exact ⟨⟨x, mul_pos ht hx⟩, y, mul_neg_of_pos_of_neg ht hy⟩)
  rw [hf] at hz
  exact ⟨z, hz0, (mul_eq_zero.1 hz).resolve_left hδ0⟩

end PositivityTheory.ThKG.Tow.Pln

end
