import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Arith

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SpectralGap.GlueM

instance instLCSL (n : ℕ) : LocallyCompactSpace (Matrix.SpecialLinearGroup (Fin n) ℂ) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance instSCSL (n : ℕ) : SecondCountableTopology (Matrix.SpecialLinearGroup (Fin n) ℂ) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.secondCountableTopology

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

instance instCountSL : Countable (Matrix.SpecialLinearGroup (Fin N) L) := by
  have : Countable L := Countable.of_equiv _ (Module.finBasis ℚ L).equivFun.symm.toEquiv
  have : Countable (Matrix (Fin N) (Fin N) L) := inferInstanceAs (Countable (Fin N → Fin N → L))
  exact inferInstanceAs (Countable (Subtype _))

theorem continuous_ofS : Continuous (ofS L N) := by
  show Continuous fun x : Sp L N => fun w => Matrix.SpecialLinearGroup.toGL (x w)
  exact continuous_pi fun w => Matrix.SpecialLinearGroup.continuous_toGL.comp (continuous_apply w)

theorem coe_jS (g : Matrix.SpecialLinearGroup (Fin N) L) (w : InfinitePlace L) :
    ((jS L N g w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      (g : Matrix (Fin N) (Fin N) L).map w.embedding := rfl

theorem jS_injective : Function.Injective (jS L N) := by
  intro g g' h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have h1 := congrArg (fun x : Sp L N => ((x w : Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) h
  simp only [coe_jS] at h1
  ext i j
  exact w.embedding.injective (congrFun (congrFun h1 i) j)

theorem scal_comm (s : InfinitePlace L → ℂˣ) (g : Gp L N) : scal L N s * g = g * scal L N s := by
  funext w
  apply Units.ext
  show Matrix.scalar (Fin N) (s w : ℂ) * ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
    ((g w : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * Matrix.scalar (Fin N) (s w : ℂ)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ _) _).eq

theorem det_dg_ne (π : 𝓞 L) (hπ : π ≠ 0) (r : ℕ) : (dg L N π r).det ≠ 0 := by
  rw [dg, det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  split_ifs
  · exact_mod_cast hπ
  · exact one_ne_zero

theorem exists_q (π : 𝓞 L) (hπ : π ≠ 0) (r : ℕ) (hN : 0 < N) : ∃ (q : Sp L N) (s : InfinitePlace L → ℂˣ),
    ∀ w, (q w : Matrix (Fin N) (Fin N) ℂ) = (s w : ℂ) • (dg L N π r).map w.embedding := by
  have hc : ∀ w : InfinitePlace L, ((dg L N π r).map w.embedding).det ≠ 0 := fun w => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (det_dg_ne L N π hπ r)
  choose t ht using fun w : InfinitePlace L => IsAlgClosed.exists_pow_nat_eq (((dg L N π r).map w.embedding).det) hN
  have ht0 : ∀ w, t w ≠ 0 := fun w h0 => hc w (by rw [← ht w, h0, zero_pow hN.ne'])
  let s : InfinitePlace L → ℂˣ := fun w => Units.mk0 (t w)⁻¹ (inv_ne_zero (ht0 w))
  refine ⟨fun w => ⟨(s w : ℂ) • (dg L N π r).map w.embedding, ?_⟩, s, fun w => rfl⟩
  rw [Matrix.det_smul, Fintype.card_fin, ← ht w]
  simp only [s, Units.val_mk0, inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero _ (ht0 w))

theorem coe_latS (γ : Matrix.SpecialLinearGroup (Fin N) (𝓞 L)) (w : InfinitePlace L) :
    ((((MonoidHom.pi fun w : InfinitePlace L => Matrix.SpecialLinearGroup.map (n := Fin N) (embO w)) γ) w :
      Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = (mo L N γ).map w.embedding := by
  ext i j
  simp [mo, mt, embO]

theorem mem_map_congruence_iff_conj_mem_lattice_of_inverse (π : 𝓞 L) (r : ℕ) (Di : Matrix (Fin N) (Fin N) L) (hDiD : Di * dg L N π r = 1)
    (hDDi : dg L N π r * Di = 1) (q : Sp L N) (s : InfinitePlace L → ℂˣ)
    (hq : ∀ w, (q w : Matrix (Fin N) (Fin N) ℂ) = (s w : ℂ) • (dg L N π r).map w.embedding) (y : Sp L N) :
    y ∈ (Kg L N π r).map (jS L N) ↔ q * y * q⁻¹ ∈ latS L N := by
  have key : ∀ l : Sp L N, q * y * q⁻¹ = l ↔ q * y = l * q := fun l => mul_inv_eq_iff_eq_mul
  constructor
  · rintro ⟨g, ⟨γ, hγ⟩, rfl⟩
    refine ⟨γ, ?_⟩
    rw [eq_comm, key]
    funext w
    apply Subtype.ext
    show (q w : Matrix (Fin N) (Fin N) ℂ) * (jS L N g w : Matrix (Fin N) (Fin N) ℂ) =
      ((((MonoidHom.pi fun w : InfinitePlace L => Matrix.SpecialLinearGroup.map (n := Fin N) (embO w)) γ) w :
        Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (q w : Matrix (Fin N) (Fin N) ℂ)
    rw [hq, coe_latS, coe_jS, smul_mul_assoc, mul_smul_comm, ← Matrix.map_mul, ← Matrix.map_mul]
    rw [show dg L N π r * (g : Matrix (Fin N) (Fin N) L) = mo L N γ * dg L N π r from hγ]
  · rintro ⟨γ, hγ⟩
    rw [eq_comm, key] at hγ
    have hw : ∀ w : InfinitePlace L, (dg L N π r).map w.embedding * (y w : Matrix (Fin N) (Fin N) ℂ) =
        (mo L N γ).map w.embedding * (dg L N π r).map w.embedding := by
      intro w
      have h1 := congrArg (fun x : Sp L N => ((x w : Matrix.SpecialLinearGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ)) hγ
      change (q w : Matrix (Fin N) (Fin N) ℂ) * (y w : Matrix (Fin N) (Fin N) ℂ) =
        ((((MonoidHom.pi fun w : InfinitePlace L => Matrix.SpecialLinearGroup.map (n := Fin N) (embO w)) γ) w :
          Matrix.SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) * (q w : Matrix (Fin N) (Fin N) ℂ) at h1
      rw [hq, coe_latS, smul_mul_assoc, mul_smul_comm] at h1
      exact smul_right_injective _ (s w).ne_zero h1
    have hdet : (Di * mo L N γ * dg L N π r).det = 1 := by
      rw [det_mul, det_mul, show (mo L N γ).det = 1 from (Matrix.SpecialLinearGroup.map (algebraMap (𝓞 L) L) γ).2,
        mul_one, ← det_mul, hDiD, det_one]
    refine ⟨⟨Di * mo L N γ * dg L N π r, hdet⟩, ⟨γ, ?_⟩, ?_⟩
    · show dg L N π r * (Di * mo L N γ * dg L N π r) = mo L N γ * dg L N π r
      rw [← mul_assoc, ← mul_assoc, hDDi, one_mul]
    · funext w
      apply Subtype.ext
      show (Di * mo L N γ * dg L N π r).map w.embedding = (y w : Matrix (Fin N) (Fin N) ℂ)
      have hDw : Di.map w.embedding * (dg L N π r).map w.embedding = 1 := by
        rw [← Matrix.map_mul, hDiD]
        exact map_one w.embedding.mapMatrix
      rw [Matrix.map_mul, Matrix.map_mul, mul_assoc, ← hw, ← mul_assoc, hDw, one_mul]

theorem mem_map_Kg (π : 𝓞 L) (hπ : π ≠ 0) (r : ℕ) (q : Sp L N) (s : InfinitePlace L → ℂˣ)
    (hq : ∀ w, (q w : Matrix (Fin N) (Fin N) ℂ) = (s w : ℂ) • (dg L N π r).map w.embedding) (y : Sp L N) :
    y ∈ (Kg L N π r).map (jS L N) ↔ q * y * q⁻¹ ∈ latS L N := by
  have hπL : (π : L) ≠ 0 := by exact_mod_cast hπ
  refine mem_map_congruence_iff_conj_mem_lattice_of_inverse L N π r (diagonal fun i : Fin N => if (i : ℕ) < r then (π : L)⁻¹ else 1) ?_ ?_ q s hq y
  · rw [dg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [hπL]
  · rw [dg, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp [hπL]

theorem map_Kg_zero (π : 𝓞 L) : (Kg L N π 0).map (jS L N) = latS L N := by
  have hdg : dg L N π 0 = 1 := by simp [dg]
  ext y
  rw [mem_map_congruence_iff_conj_mem_lattice_of_inverse L N π 0 1 (by rw [hdg, one_mul]) (by rw [hdg, one_mul]) 1 1 (fun w => by simp [hdg]) y]
  simp

theorem latS_emb (x : Sp L N) (hx : x ∈ latS L N) : ∃ γ : Gm L N, ofS L N x = emb L N γ := by
  obtain ⟨γ, rfl⟩ := hx
  refine ⟨Matrix.SpecialLinearGroup.toGL γ, ?_⟩
  funext w
  apply Units.ext
  ext i j
  simp [ofS, emb, toP, toK, embO]

theorem ofS_q (π : 𝓞 L) (hπ : π ≠ 0) (q : Sp L N) (s : InfinitePlace L → ℂˣ)
    (hq : ∀ w, (q w : Matrix (Fin N) (Fin N) ℂ) = (s w : ℂ) • (dg L N π 1).map w.embedding) :
    ofS L N q = scal L N s * toP L N (qel L N π hπ) := by
  funext w
  apply Units.ext
  show (q w : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (s w : ℂ) *
    ((qel L N π hπ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L).map w.embedding
  rw [hq, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  congr 2
  show dg L N π 1 = diagonal fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1
  simp only [dg, Nat.lt_one_iff]

end PositivityTheory.KB.SpectralGap.GlueM

end
