import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKC

noncomputable section

open scoped TensorProduct NNReal
open Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cj_fromBlocks {R : Type} [CommRing R] (s : R →+* R) (a b c d : Matrix n n R) :
    cj s (fromBlocks a b c d) = fromBlocks (cj s a) (cj s c) (cj s b) (cj s d) := by
  unfold cj
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem cj_neg {R : Type} [CommRing R] (s : R →+* R) {m p : Type} (M : Matrix m p R) : cj s (-M) = -cj s M := by
  ext i j; simp [cj]

theorem cj_zero {R : Type} [CommRing R] (s : R →+* R) {m p : Type} : cj s (0 : Matrix m p R) = 0 := by
  ext i j; simp [cj]

theorem unit_rel {R : Type} [CommRing R] (s : R →+* R) (a b c d : Matrix n n R)
    (h : cj s (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d = fromBlocks 0 1 (-1) 0) :
    a * cj s d - b * cj s c = 1 ∧ c * cj s d = d * cj s c ∧ d * cj s a - c * cj s b = 1 := by
  set M := fromBlocks a b c d with hM
  set J : Matrix (n ⊕ n) (n ⊕ n) R := fromBlocks 0 1 (-1) 0 with hJ
  have hJJ : J * J = -1 := by
    rw [hJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  have h1 : (-(J * cj s M * J)) * M = 1 := by
    calc (-(J * cj s M * J)) * M = -(J * (cj s M * J * M)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [h, hJJ, neg_neg]
  have h2 : M * (-(J * cj s M * J)) = 1 := mul_eq_one_comm.mp h1
  have e : M * J * cj s M * J = -1 := by
    rw [Matrix.mul_neg] at h2
    simp only [Matrix.mul_assoc] at h2 ⊢
    exact neg_eq_iff_eq_neg.mp h2
  have h3 : M * J * cj s M = J := by
    calc M * J * cj s M = -(M * J * cj s M * (J * J)) := by rw [hJJ]; simp
      _ = -(M * J * cj s M * J * J) := by simp [Matrix.mul_assoc]
      _ = J := by rw [e]; simp
  rw [hM, hJ, cj_fromBlocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h3
  simp at h3
  obtain ⟨-, k1, k2, k3⟩ := h3
  rw [neg_add_eq_sub] at k1 k2 k3
  refine ⟨k1, sub_eq_zero.mp k3, ?_⟩
  rw [← neg_sub, k2, neg_neg]

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

theorem local_choice (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ AlgHom.id F E)
    (hfr : Module.finrank F E = 2) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (a b c d : Matrix n n (Fv F v ⊗[F] E))
    (ha : ∀ i j, a i j ∈ intLoc F E v) (hb : ∀ i j, b i j ∈ intLoc F E v) (hc : ∀ i j, c i j ∈ intLoc F E v)
    (hd : ∀ i j, d i j ∈ intLoc F E v)
    (hu : cj (sigR (Fv F v) σ) (fromBlocks a b c d) * fromBlocks 0 1 (-1) 0 * fromBlocks a b c d =
      fromBlocks 0 1 (-1) 0) :
    ∃ x : Matrix n n (Fv F v ⊗[F] E), (∀ i j, x i j ∈ intLoc F E v) ∧ cj (sigR (Fv F v) σ) x = x ∧
      ∃ z ∈ intLoc F E v, (d + c * x).det * z = 1 := by
  have hinv : ∀ y : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul p q => simp [sigR, hσ]
    | add p q hp hq => simp only [map_add, hp, hq]
  set s := sR v σ with hs
  have hss : ∀ y, s (s y) = y := by
    intro y
    apply Subtype.ext
    rw [hs, coe_sR, coe_sR, hinv]
  have hπ : ∀ y, (intLoc F E v).subtype (s y) = sigR (Fv F v) σ ((intLoc F E v).subtype y) := by
    intro y
    exact coe_sR v σ y
  let a' : Matrix n n (intLoc F E v) := fun i j => ⟨a i j, ha i j⟩
  let b' : Matrix n n (intLoc F E v) := fun i j => ⟨b i j, hb i j⟩
  let c' : Matrix n n (intLoc F E v) := fun i j => ⟨c i j, hc i j⟩
  let d' : Matrix n n (intLoc F E v) := fun i j => ⟨d i j, hd i j⟩
  have ea : a'.map (intLoc F E v).subtype = a := rfl
  have eb : b'.map (intLoc F E v).subtype = b := rfl
  have ec : c'.map (intLoc F E v).subtype = c := rfl
  have ed : d'.map (intLoc F E v).subtype = d := rfl
  have h1m : (1 : Matrix n n (intLoc F E v)).map (intLoc F E v).subtype = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hJm : (fromBlocks 0 1 (-1) 0 : Matrix (n ⊕ n) (n ⊕ n) (intLoc F E v)).map (intLoc F E v).subtype
      = fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.fromBlocks_map, Matrix.map_neg _ (map_neg (intLoc F E v).subtype), h1m]
    simp
  have hu' : cj s (fromBlocks a' b' c' d') * fromBlocks 0 1 (-1) 0 * fromBlocks a' b' c' d' =
      fromBlocks 0 1 (-1) 0 := by
    apply Matrix.map_injective Subtype.val_injective
    have key := hu
    rw [← ea, ← eb, ← ec, ← ed, ← Matrix.fromBlocks_map, ← map_cj s _ _ hπ, ← hJm,
      ← Matrix.map_mul, ← Matrix.map_mul] at key
    exact key
  obtain ⟨k1, k2, k3⟩ := unit_rel s a' b' c' d' hu'
  obtain ⟨𝔭, h𝔭, hloc⟩ := exists_max v σ hσ1 hfr
  obtain ⟨B, hB, hdet⟩ := core s hss 𝔭 (isUnit_two v h2) hloc a' b' c' d' k1 k2 k3
  obtain ⟨w, hw⟩ := hdet.exists_right_inv
  refine ⟨B.map (intLoc F E v).subtype, fun i j => (B i j).2, ?_, w, w.2, ?_⟩
  · rw [← map_cj s _ _ hπ, hB]
  · have hm : (d' + c' * B).map (intLoc F E v).subtype = d + c * B.map (intLoc F E v).subtype := by
      rw [Matrix.map_add _ (map_add (intLoc F E v).subtype), Matrix.map_mul, ec, ed]
    rw [← hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    simpa using congrArg Subtype.val hw

end Local

end PositivityTheory.Rg.Rsw.L.LGenK
