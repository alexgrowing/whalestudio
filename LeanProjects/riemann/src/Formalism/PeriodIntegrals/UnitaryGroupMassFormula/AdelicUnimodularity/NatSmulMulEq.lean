import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.IsCompactCset

noncomputable section

namespace PI.WAU

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

private theorem intC_smul_entry_of_preserves_Lf (d D D1 : ℕ)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hg : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F,
      v ∈ I.Lf ↔ (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf)
    (i j : Fin I.n) :
    IntC (bs I) ((D * (d * D1)) • (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j) := by
  classical
  have hy : ∀ j', IntC (bs I)
      ((Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F) j') := by
    intro j'
    by_cases h : j' = j
    · rw [h, Pi.single_eq_same]; exact h1
    · rw [Pi.single_eq_of_ne h]
      intro k
      simp only [map_zero, Pi.zero_apply]
      exact (Formalism.UG.intAd I.F).zero_mem
  have hL := (hg _).mp (hlow _ hy)
  have hI := hup _ hL i
  have hs : ((g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ
      (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F)) i =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j * (D1 • (1 : I.E ⊗[I.F] Af I.F)) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : D • ((g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ
      (d • (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F))) i =
      (D * (d * D1)) • (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j := by
    rw [Matrix.mulVec_smul, Pi.smul_apply, hs]
    simp only [nsmul_eq_mul, Nat.cast_mul, mul_one]
    ring
  rwa [key] at hI

private theorem coord_mem_Bx_of_intC_nsmul (N : ℕ) (hN : 0 < N) (z : I.E ⊗[I.F] Af I.F)
    (hz : IntC (bs I) (N • z)) (k : ιb I) : coord (bs I) z k ∈ Bx I N := by
  simp only [Bx, Set.mem_image]
  refine ⟨N • coord (bs I) z k, ?_, ?_⟩
  · have := hz k
    rwa [map_nsmul, Pi.smul_apply] at this
  · have hN' : (N : I.F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)) N, ← map_mul,
      inv_mul_cancel₀ hN', map_one, one_mul]

theorem mem_range_psi (d D D1 : ℕ) (hN : 0 < D * (d * D1))
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    {x : I.Gf} (hx : x ∈ I.Kset) : ∃ p, psi I (D * (d * D1)) p = x := by
  classical
  have h0 : (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf := hx
  have h0i : ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹) ∈ Formalism.UG.stabGL I.Lf := inv_mem h0
  have hx' : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F, v ∈ I.Lf ↔
      ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v
        ∈ I.Lf := h0
  have hxi' : ∀ v : Fin I.n → I.E ⊗[I.F] Af I.F, v ∈ I.Lf ↔
      (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) *ᵥ v ∈ I.Lf := h0i
  have hm1 : matOf I (fun i j => coord (bs I) (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)) =
      ((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) := by
    funext i j; simp only [matOf, emb_coord]
  have hm2 : matOf I (fun i j => coord (bs I)
      ((((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)) =
      (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) := by
    funext i j; simp only [matOf, emb_coord]
  refine ⟨⟨(fun i j => coord (bs I) (((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j), fun i j => coord (bs I)
      ((((x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
        Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j)), ?_⟩, ?_⟩
  · simp only [Cset, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j k
      exact ⟨coord_mem_Bx_of_intC_nsmul I _ hN _ (intC_smul_entry_of_preserves_Lf I d D D1 hlow hup h1 _ hx' i j) k,
        coord_mem_Bx_of_intC_nsmul I _ hN _ (intC_smul_entry_of_preserves_Lf I d D D1 hlow hup h1 _ hxi' i j) k⟩
    · rw [hm1, hm2]; exact Units.mul_inv _
    · rw [hm1, hm2]; exact Units.inv_mul _
    · rw [hm1]; exact x.2
    · intro l hl
      rw [hm1]
      exact (hx' _).mp (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
    · intro l hl
      rw [hm2]
      exact (hxi' _).mp (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
  · exact Subtype.ext (Units.ext hm1)

theorem nat_smul_mul_eq (g d D m : ℕ) (a y : I.E ⊗[I.F] Af I.F) :
    ((g * d * D * m) • a) * y = (g * d) • (m • (a * (D • y))) := by
  simp only [nsmul_eq_mul, Nat.cast_mul]
  ring

theorem continuous_psi (N d D m : ℕ) (hd : 0 < d) (hD : 0 < D) (hm : 0 < m)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j))
    (hmul : ∀ x y : I.E ⊗[I.F] Af I.F, IntC (bs I) x → IntC (bs I) y → IntC (bs I) (m • (x * y))) :
    Continuous (psi I N) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  intro U hU
  have hV : (fun z => psi I N p * z) ⁻¹' U ∈ 𝓝 (1 : I.Gf) := by
    have := (continuous_mul_left (psi I N p)).tendsto 1
    rw [mul_one] at this
    exact this hU
  obtain ⟨g, hg1, hsub⟩ := I.topf_basis _ hV
  have hN1' : ((g * d * D * m : ℕ) : I.F) ≠ 0 := by
    have : 0 < g * d * D * m := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hg1 hd) hD) hm
    exact_mod_cast this.ne'
  let c : I.F := ((g * d * D * m : ℕ) : I.F)⁻¹
  let W : Set (Cset I N) := {p' | ∀ i j k, algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k) ∈ Ohat I.F}
  have hW : W ∈ 𝓝 p := by
    have hWo : IsOpen W := by
      have : W = ⋂ i, ⋂ j, ⋂ k, (fun p' : Cset I N => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)) ⁻¹'
          Ohat I.F := by
        ext; simp [W]
      rw [this]
      refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_
      have h0 : Continuous (fun p' : Cset I N => p'.1.1 i j k) := by fun_prop
      have hc : Continuous (fun p' : Cset I N => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)) :=
        continuous_const.mul (h0.sub continuous_const)
      exact hc.isOpen_preimage _ isOpen_Ohat
    exact hWo.mem_nhds (fun i j k => by simpa using ohat_zero)
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hW fun p' hp' => ?_
  have hQM : matOf I p.1.2 * matOf I p.1.1 = 1 := p.2.2.2.1
  let x := (psi I N p)⁻¹ * psi I N p'
  have hxK : x ∈ I.Kset :=
    (Formalism.UG.stabGL I.Lf).mul_mem ((Formalism.UG.stabGL I.Lf).inv_mem (psi_mem I N p)) (psi_mem I N p')
  have hfx : I.fmat x = matOf I p.1.2 * matOf I p'.1.1 := rfl
  have hcond : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat x - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    let u : Co I := fun i j k => algebraMap I.F (Af I.F) c * (p'.1.1 i j k - p.1.1 i j k)
    have hu : ∀ i j k, u i j k ∈ Ohat I.F := hp'
    have hδ : ∀ i j, matOf I p'.1.1 i j - matOf I p.1.1 i j = (g * d * D * m) • emb (bs I) (u i j) := by
      intro i j
      simp only [matOf]
      rw [← emb_sub, ← emb_nsmul]
      congr 1; funext k
      simp only [u, Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, c]
      rw [← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, mul_inv_cancel₀ hN1', map_one,
        one_mul]
    let w : Fin I.n → I.E ⊗[I.F] Af I.F := fun i => ∑ j, m • (emb (bs I) (u i j) * (D • y j))
    have hw : ∀ i, IntC (bs I) (w i) := fun i => intC_sum _ fun j _ =>
      hmul _ _ (fun k => by rw [coord_emb]; exact hu i j k) (hup y hy j)
    have hdw := hlow w hw
    have hmv : (matOf I p'.1.1 - matOf I p.1.1) *ᵥ y = (g * d) • w := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, hδ, nat_smul_mul_eq I, Pi.smul_apply,
        Finset.smul_sum, w]
    refine ⟨matOf I p.1.2 *ᵥ (d • w), mulVec_mem_Lf I _ p.2.2.2.2.2.2 _ hdw, ?_⟩
    rw [hfx, ← hQM, ← Matrix.mul_sub, ← Matrix.mulVec_mulVec, hmv, mul_smul, Matrix.mulVec_smul,
      Nat.cast_smul_eq_nsmul]
  have hx := hsub ⟨hxK, hcond⟩
  show psi I N p' ∈ U
  have : psi I N p * x = psi I N p' := mul_inv_cancel_left _ _
  rw [← this]; exact hx

theorem isCompact_Kset : IsCompact I.Kset := by
  obtain ⟨d, hd, hlow⟩ := exists_lower (bs I) I.L I.L_span
  obtain ⟨D, hD, hup⟩ := exists_upper (bs I) I.L I.L_fg
  obtain ⟨m, hm, hmul⟩ := exists_den_mul (bs I)
  obtain ⟨D1, hD1, h1F⟩ := exists_den_fin (fun k : ιb I => (bs I).repr 1 k)
  have h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)) := by
    intro k
    rw [map_nsmul, ← map_one (Algebra.TensorProduct.includeLeftRingHom (R := I.F) (A := I.E) (B := Af I.F)),
      coord_incl, Pi.smul_apply, nsmul_eq_mul, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul]
    exact h1F k
  have hN : 0 < D * (d * D1) := Nat.mul_pos hD (Nat.mul_pos hd hD1)
  haveI : CompactSpace (Cset I (D * (d * D1))) :=
    isCompact_iff_compactSpace.mp (isCompact_Cset I _ d hd hlow)
  have : I.Kset = Set.range (psi I (D * (d * D1))) := by
    ext x
    constructor
    · intro hx; exact mem_range_psi I d D D1 hN hlow hup h1 hx
    · rintro ⟨p, rfl⟩; exact psi_mem I _ p
  rw [this]
  exact isCompact_range (continuous_psi I _ d D m hd hD hm hlow hup hmul)

end Cpt

end PI.WAU
