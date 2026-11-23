import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private def zGL {L : Type} [Field L] (r : ℕ) {π : L} (hπ : π ≠ 0) : GL (Fin r) L :=
  Units.map ((Matrix.scalar (Fin r) : L →+* Matrix (Fin r) (Fin r) L) : L →* Matrix (Fin r) (Fin r) L) (Units.mk0 π hπ)

private theorem zGL_val {L : Type} [Field L] (r : ℕ) {π : L} (hπ : π ≠ 0) :
    ((zGL r hπ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) = Matrix.diagonal fun _ => π := rfl

private theorem zGL_comm {L : Type} [Field L] (r : ℕ) {π : L} (hπ : π ≠ 0) (g : GL (Fin r) L) :
    zGL r hπ * g = g * zGL r hπ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, zGL_val]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

private theorem card_top {r a : ℕ} (h : a ≤ r) :
    ((Finset.univ.filter fun i : Fin r => (i : ℕ) < r - a)ᶜ).card = a := by
  rw [Finset.card_compl, Fintype.card_fin, Fin.card_filter_val_lt]
  omega

private theorem inv_mem {E : Type} [Field E] [NumberField E] (w : Pl E) {r a : ℕ} (har : a ≤ r)
    {ϖ : w.adicCompletion E} (hπ : ϖ ≠ 0) {b : GL (Fin r) (w.adicCompletion E)}
    (hb : b ∈ satakeTset w ϖ (r - a)) : b⁻¹ * zGL r hπ ∈ satakeTset w ϖ a := by
  classical
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hb
  set S : Finset (Fin r) := (Finset.univ.filter fun i : Fin r => (i : ℕ) < r - a)ᶜ with hSdef
  have hS : S.card = a := card_top har
  set G := satakeGL (Ov E w) hπ S (fun _ => 0) with hGdef
  have hG : G ∈ satakeTset w ϖ a := by
    obtain ⟨x, hx, y, hy, e'⟩ := satakeGL_mem_doset (Ov E w) hπ S (fun _ => 0)
    rw [hS] at e'
    exact ⟨x, hx, y, hy, e'⟩
  have hGv : (G : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = satakeD ϖ S := by
    have h0 : satakeN (Ov E w) S (fun _ => 0) = 0 := by
      ext i j
      simp [satakeN]
    show (1 + satakeN (Ov E w) S (fun _ => 0)) * satakeD ϖ S = _
    rw [h0, add_zero, Matrix.one_mul]
  set d : GL (Fin r) (w.adicCompletion E) := k₁⁻¹ * b * k₂⁻¹ with hddef
  have hd : (d : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = diagJ r ϖ (r - a) := by
    rw [hddef, Units.val_mul, Units.val_mul, e]
    have h1 : ((k₁⁻¹ : GL (Fin r) (w.adicCompletion E)) : Matrix (Fin r) (Fin r) (w.adicCompletion E)) *
        (k₁ : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (k₂ : Matrix (Fin r) (Fin r) (w.adicCompletion E)) *
        ((k₂⁻¹ : GL (Fin r) (w.adicCompletion E)) : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hGd : G * d = zGL r hπ := by
    apply Units.ext
    rw [Units.val_mul, hGv, hd, zGL_val]
    unfold satakeD diagJ
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : (i : ℕ) < r - a
    · simp [hSdef, h]
      intro h'
      omega
    · simp [hSdef, h]
      intro h'
      omega
  have hb' : b = k₁ * d * k₂ := by
    rw [hddef]; group
  have hz : d⁻¹ * zGL r hπ = G := by
    rw [← zGL_comm, ← hGd]; group
  have hfin : b⁻¹ * zGL r hπ = k₂⁻¹ * G * k₁⁻¹ := by
    rw [← hz, hb', mul_inv_rev, mul_inv_rev]
    have := zGL_comm r hπ k₁⁻¹
    simp only [mul_assoc]
    rw [← this]
  rw [hfin]
  exact satake_Tset_right w (satake_Tset_left w hG ((GLint _ _).inv_mem hk₂)) ((GLint _ _).inv_mem hk₁)

theorem UpperTheory.exists_satakeTset_sum_eigenvector :
    ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r a : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → a ≤ r →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (f : V) (B : Multiset ℂˣ), IsSatVecGL w ρ f B →
      ∃ (n : ℕ) (c : Fin n → GL (Fin r) (w.adicCompletion E)) (μ : ℂ), 0 < n ∧ (∀ i, (c i)⁻¹ ∈ satakeTset w ϖ a) ∧ ∑ i, ρ (c i) f = μ • f := by
  intro E _ _ w r a ϖ hu har V _ _ ρ f B hf
  classical
  obtain ⟨hf0, hfix, -, hT⟩ := hf
  have hϖ := mem_Ov_of_isUnifV hu
  have hπ : ϖ ≠ 0 := satake_unif_ne_zero w hu
  letI : Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) := @Fintype.ofFinite _ (satake_res_finite w hϖ hu)
  have hne : ∀ j, j ≤ r → Nonempty (SatakeIdx w hϖ (n := r) j) := by
    intro j hj
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin r))) (n := j)
      (by simpa using hj)
    exact ⟨⟨⟨S, hS⟩, fun _ => 0⟩⟩
  have hsum : ∀ j, j ≤ r → ∑ i : SatakeIdx w hϖ (n := r) j, ρ (satakeB w hϖ hu i) f =
      satEig (qV E w) r B j • f := fun j hj => by
    rw [← UpperTheory.V.Cj.S.hkSum E w r V ρ ϖ hϖ hu j hj f hfix, hT ϖ hu j hj]
  set z := zGL r hπ with hzdef
  have hfx : ∀ k ∈ KGL w r, ρ k f = f := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hfix _ hk
  have hB : ∀ i : SatakeIdx w hϖ (n := r) r, ρ (satakeB w hϖ hu i) f = ρ z f := by
    intro i
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := satakeB_mem w hϖ hu i
    have hdz : diagJ r ϖ r = (z : Matrix (Fin r) (Fin r) (w.adicCompletion E)) := by
      rw [hzdef, zGL_val]
      unfold diagJ
      congr 1
      funext i
      simp
    have : satakeB w hϖ hu i = z * (k₁ * k₂) := by
      apply Units.ext
      rw [e, hdz, ← Units.val_mul, ← Units.val_mul, hzdef, ← zGL_comm, mul_assoc]
    rw [this, map_mul, Module.End.mul_apply, hfx _ ((KGL w r).mul_mem hk₁ hk₂)]
  obtain ⟨i₀⟩ := hne r le_rfl
  have hcard : (Fintype.card (SatakeIdx w hϖ (n := r) r) : ℂ) ≠ 0 := by
    have : Fintype.card (SatakeIdx w hϖ (n := r) r) ≠ 0 := by
      haveI : Nonempty (SatakeIdx w hϖ (n := r) r) := ⟨i₀⟩
      exact Fintype.card_ne_zero
    exact_mod_cast this
  set c : ℂ := (Fintype.card (SatakeIdx w hϖ (n := r) r) : ℂ)⁻¹ * satEig (qV E w) r B r with hcdef
  have hzf : ρ z f = c • f := by
    have h := hsum r le_rfl
    simp only [hB, Finset.sum_const, Finset.card_univ] at h
    rw [hcdef, mul_smul, ← h, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hzf
    apply hf0
    have : ρ z⁻¹ (ρ z f) = f := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hzf, map_zero]
  have hzi : ρ z⁻¹ f = c⁻¹ • f := by
    have : ρ z⁻¹ (ρ z f) = f := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hzf, map_smul] at this
    rw [eq_inv_smul_iff₀ hc]
    exact this
  obtain ⟨i₁⟩ := hne (r - a) (Nat.sub_le _ _)
  let e := Fintype.equivFin (SatakeIdx w hϖ (n := r) (r - a))
  refine ⟨Fintype.card (SatakeIdx w hϖ (n := r) (r - a)), fun i => z⁻¹ * satakeB w hϖ hu (e.symm i),
    satEig (qV E w) r B (r - a) * c⁻¹, Fintype.card_pos_iff.2 ⟨i₁⟩, fun i => ?_, ?_⟩
  · rw [mul_inv_rev, inv_inv]
    exact inv_mem w har hπ (satakeB_mem w hϖ hu _)
  · rw [Equiv.sum_comp e.symm (fun i => ρ (z⁻¹ * satakeB w hϖ hu i) f)]
    simp only [map_mul, Module.End.mul_apply]
    rw [← map_sum, hsum _ (Nat.sub_le _ _), map_smul, hzi, smul_smul]
