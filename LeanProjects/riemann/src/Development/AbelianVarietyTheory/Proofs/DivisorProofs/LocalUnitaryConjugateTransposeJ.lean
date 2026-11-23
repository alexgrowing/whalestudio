import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne

noncomputable section

namespace GlobalTheory.TamOne

section Frame

variable {A : Type} [CommRing A] {r : ℕ}

theorem gram_eq_of_frame (σ : A →+* A) (J : Matrix (Fin r) (Fin r) A) (h : GL (Fin r) A)
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = 1) : J = Formalism.UG.cT σ (h⁻¹).1 * (h⁻¹).1 := by
  have e1 : Formalism.UG.cT σ (h⁻¹).1 * Formalism.UG.cT σ h.1 = 1 := by
    rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
  calc J = (Formalism.UG.cT σ (h⁻¹).1 * Formalism.UG.cT σ h.1) * J * (h.1 * (h⁻¹).1) := by
        rw [e1, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
    _ = Formalism.UG.cT σ (h⁻¹).1 * (Formalism.UG.cT σ h.1 * J * h.1) * (h⁻¹).1 := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hh, Matrix.mul_one]

theorem cT_conj_mul_self (σ : A →+* A) (J : Matrix (Fin r) (Fin r) A) (h : GL (Fin r) A)
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = 1) (X : Matrix (Fin r) (Fin r) A) (hX : Formalism.UG.cT σ X * J * X = J) :
    Formalism.UG.cT σ ((h⁻¹).1 * X * h.1) * ((h⁻¹).1 * X * h.1) = 1 := by
  have hJ := gram_eq_of_frame σ J h hh
  calc _ = Formalism.UG.cT σ h.1 * (Formalism.UG.cT σ X * (Formalism.UG.cT σ (h⁻¹).1 * (h⁻¹).1) * X) * h.1 := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [← hJ, hX, hh]

theorem cT_mul_conj_eq (σ : A →+* A) (J : Matrix (Fin r) (Fin r) A) (h : GL (Fin r) A)
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = 1) (M : Matrix (Fin r) (Fin r) A) (hM : Formalism.UG.cT σ M * M = 1) :
    Formalism.UG.cT σ (h.1 * M * (h⁻¹).1) * J * (h.1 * M * (h⁻¹).1) = J := by
  have hJ := gram_eq_of_frame σ J h hh
  calc _ = Formalism.UG.cT σ (h⁻¹).1 * (Formalism.UG.cT σ M * (Formalism.UG.cT σ h.1 * J * h.1) * M) * (h⁻¹).1 := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hh, Matrix.mul_one, hM, Matrix.mul_one, ← hJ]

variable (S : Subring A) (P : (Fin r → A) → Prop) (h : GL (Fin r) A)

theorem frame_col_mem (hP : ∀ z, P z ↔ ∀ i, ((h⁻¹).1 *ᵥ z) i ∈ S) (j : Fin r) : P (h.1 *ᵥ Pi.single j 1) := by
  rw [hP, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  intro k
  by_cases e : k = j
  · subst e; simpa using S.one_mem
  · simpa [e] using S.zero_mem

theorem frame_entries (hP : ∀ z, P z ↔ ∀ i, ((h⁻¹).1 *ᵥ z) i ∈ S) (X : Matrix (Fin r) (Fin r) A)
    (hX : ∀ y, P y ↔ P (X *ᵥ y)) (i j : Fin r) : ((h⁻¹).1 * X * h.1) i j ∈ S := by
  have h2 := (hP _).1 ((hX _).1 (frame_col_mem S P h hP j)) i
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h2

variable (I : Ideal S) (Q : (Fin r → A) → Prop)

theorem frame_rel_fwd (hP : ∀ z, P z ↔ ∀ i, ((h⁻¹).1 *ᵥ z) i ∈ S)
    (hQ : ∀ z, Q z ↔ ∀ i, ∃ t ∈ I, (t : A) = ((h⁻¹).1 *ᵥ z) i) (X Y : Matrix (Fin r) (Fin r) A)
    (hXY : ∀ z, P z → Q ((X - Y) *ᵥ z)) (i j : Fin r) :
    ∃ t ∈ I, (t : A) = ((h⁻¹).1 * X * h.1 - (h⁻¹).1 * Y * h.1) i j := by
  obtain ⟨t, ht, e⟩ := (hQ _).1 (hXY _ (frame_col_mem S P h hP j)) i
  refine ⟨t, ht, e.trans ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mul_sub, Matrix.sub_mul]
  rfl

theorem frame_rel_bwd (hP : ∀ z, P z ↔ ∀ i, ((h⁻¹).1 *ᵥ z) i ∈ S)
    (hQ : ∀ z, Q z ↔ ∀ i, ∃ t ∈ I, (t : A) = ((h⁻¹).1 *ᵥ z) i) (X Y : Matrix (Fin r) (Fin r) A)
    (hD : ∀ i j, ∃ t ∈ I, (t : A) = ((h⁻¹).1 * X * h.1 - (h⁻¹).1 * Y * h.1) i j) (z : Fin r → A) (hz : P z) :
    Q ((X - Y) *ᵥ z) := by
  rw [hQ]
  intro i
  have hw := (hP z).1 hz
  choose t ht e using hD
  refine ⟨∑ j, t i j * ⟨((h⁻¹).1 *ᵥ z) j, hw j⟩, Ideal.sum_mem _ fun j _ => I.mul_mem_right _ (ht i j), ?_⟩
  have key : (h⁻¹).1 *ᵥ ((X - Y) *ᵥ z) = ((h⁻¹).1 * X * h.1 - (h⁻¹).1 * Y * h.1) *ᵥ ((h⁻¹).1 *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [key, Matrix.mulVec, dotProduct]
  simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [e i j]

theorem frame_stab (hP : ∀ z, P z ↔ ∀ i, ((h⁻¹).1 *ᵥ z) i ∈ S) (σ : A →+* A) (hσ : ∀ a ∈ S, σ a ∈ S)
    (M : Matrix (Fin r) (Fin r) A) (hMS : ∀ i j, M i j ∈ S) (hM : Formalism.UG.cT σ M * M = 1) (y : Fin r → A) :
    P y ↔ P ((h.1 * M * (h⁻¹).1) *ᵥ y) := by
  have key : ∀ N : Matrix (Fin r) (Fin r) A, (∀ i j, N i j ∈ S) → ∀ w : Fin r → A, (∀ i, w i ∈ S) →
      ∀ i, (N *ᵥ w) i ∈ S := fun N hN w hw i => show ∑ j, N i j * w j ∈ S from Subring.sum_mem _ fun j _ => S.mul_mem (hN i j) (hw j)
  rw [hP, hP, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  constructor
  · exact key M hMS _
  · intro hw
    have e : (h⁻¹).1 *ᵥ y = Formalism.UG.cT σ M *ᵥ (M *ᵥ ((h⁻¹).1 *ᵥ y)) := by
      rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
    rw [e]
    exact key _ (fun i j => hσ _ (hMS j i)) _ hw

end Frame

theorem card_quot_congRel_eq_card_suMat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (h : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)), Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv (maximalRealSubfield E) v) (cj E)) (h : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) * JR (F := maximalRealSubfield E) (Fv (maximalRealSubfield E) v) Gᵀ * (h : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) = 1 → (∀ z : Fin r → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E, z ∈ latLoc (maximalRealSubfield E) Λ v ↔ ∀ i, (((h⁻¹ : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) *ᵥ z) i ∈ intLoc (maximalRealSubfield E) E v) → (∀ z : Fin r → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E, z ∈ latLoc (maximalRealSubfield E) (extIdeal v • Λ) v ↔ ∀ i, ∃ t ∈ (extIdeal v).map (intLocIncl (E := E) v), ((t : intLoc (maximalRealSubfield E) E v) : Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) = (((h⁻¹ : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) : Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) *ᵥ z) i) → ∀ ρ : intLoc (maximalRealSubfield E) E v →+* 𝓞 E ⧸ extIdeal v, (∀ z, ρ z = 0 ↔ z ∈ (extIdeal v).map (intLocIncl v)) → (∀ z, ρ (intLocConj v z) = resConj v (ρ z)) → (∀ g ∈ suMat (𝓞 E ⧸ extIdeal v) (resConj v) r, ∃ g' ∈ suMat (intLoc (maximalRealSubfield E) E v) (intLocConj v) r, g'.map ρ = g) → Nat.card (Quot (congRel (cj E) Gᵀ Λ v (extIdeal v))) = Nat.card (suMat (𝓞 E ⧸ extIdeal v) (resConj v) r) := by
  intro E _ _ _ r G Λ v h hh hΛ hvΛ ρ hρ hρc hlift
  let S := intLoc (maximalRealSubfield E) E v
  let σA := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv (maximalRealSubfield E) v) (cj E)
  let I : Ideal S := (extIdeal v).map (intLocIncl v)
  let Xm : stabOne (cj E) Gᵀ Λ v →
      Matrix (Fin r) (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) :=
    fun x => ((matHom _ (cj E) Gᵀ x.1 : GL (Fin r) _) : Matrix (Fin r) (Fin r) _)
  have hent : ∀ x : stabOne (cj E) Gᵀ Λ v, ∀ i j, ((h⁻¹).1 * Xm x * h.1) i j ∈ S := fun x =>
    frame_entries S (fun z => z ∈ latLoc (maximalRealSubfield E) Λ v) h hΛ (Xm x) (mem_stabLoc.1 x.2.2)
  let Gm : stabOne (cj E) Gᵀ Λ v → Matrix (Fin r) (Fin r) S := fun x => Matrix.of fun i j => ⟨_, hent x i j⟩
  have hU : ∀ x : stabOne (cj E) Gᵀ Λ v,
      Formalism.UG.cT σA (Xm x) * JR (F := maximalRealSubfield E) (Fv (maximalRealSubfield E) v) Gᵀ * Xm x =
        JR (F := maximalRealSubfield E) (Fv (maximalRealSubfield E) v) Gᵀ := fun x =>
    (show ↥(HR (Fv (maximalRealSubfield E) v) (cj E) Gᵀ) from x.1).2
  have hunitG : ∀ x, ((Gm x).map (intLocConj v))ᵀ * Gm x = 1 := fun x => by
    refine Matrix.map_injective (f := S.subtype) Subtype.val_injective ?_
    dsimp only
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero _) (map_one _)]
    exact cT_conj_mul_self σA _ h hh (Xm x) (hU x)
  have hdetG : ∀ x, (Gm x).det = 1 := fun x => by
    apply Subtype.val_injective
    have e := RingHom.map_det S.subtype (Gm x)
    rw [RingHom.mapMatrix_apply] at e
    have hdx : (Xm x).det = 1 := x.2.1
    change S.subtype (Gm x).det = 1
    rw [e, show (Gm x).map S.subtype = (h⁻¹).1 * Xm x * h.1 from rfl, Matrix.det_mul, Matrix.det_mul, hdx, mul_one,
      ← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
  have hmem : ∀ x, (Gm x).map ρ ∈ suMat (𝓞 E ⧸ extIdeal v) (resConj v) r := fun x => by
    refine ⟨?_, ?_⟩
    · have e : ((Gm x).map ρ).map (resConj v) = ((Gm x).map (intLocConj v)).map ρ := by
        ext i j; exact (hρc _).symm
      rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, hunitG x, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdetG x, map_one]
  have hcond : ∀ x y, (∀ i j, Gm x i j - Gm y i j ∈ I) ↔ (Gm x).map ρ = (Gm y).map ρ := fun x y => by
    constructor
    · intro hd
      ext i j
      change ρ _ = ρ _
      rw [← sub_eq_zero, ← map_sub, hρ]
      exact hd i j
    · intro he i j
      have := congrFun (congrFun he i) j
      change ρ _ = ρ _ at this
      rw [← hρ, map_sub, this, sub_self]
  have hcr : ∀ x y, congRel (cj E) Gᵀ Λ v (extIdeal v) x y ↔ ∀ i j, Gm x i j - Gm y i j ∈ I := fun x y => by
    constructor
    · intro hc i j
      obtain ⟨t, ht, e⟩ := frame_rel_fwd S (fun z => z ∈ latLoc (maximalRealSubfield E) Λ v) h I
        (fun z => z ∈ latLoc (maximalRealSubfield E) (extIdeal v • Λ) v) hΛ hvΛ (Xm x) (Xm y) hc i j
      have : Gm x i j - Gm y i j = t := Subtype.ext e.symm
      rw [this]
      exact ht
    · intro hd
      exact frame_rel_bwd S (fun z => z ∈ latLoc (maximalRealSubfield E) Λ v) h I
        (fun z => z ∈ latLoc (maximalRealSubfield E) (extIdeal v • Λ) v) hΛ hvΛ (Xm x) (Xm y)
        (fun i j => ⟨_, hd i j, rfl⟩)
  let Φ : Quot (congRel (cj E) Gᵀ Λ v (extIdeal v)) → suMat (𝓞 E ⧸ extIdeal v) (resConj v) r :=
    Quot.lift (fun x => ⟨(Gm x).map ρ, hmem x⟩) fun x y hxy => Subtype.ext ((hcond x y).1 ((hcr x y).1 hxy))
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨?_, ?_⟩)
  · rintro ⟨x⟩ ⟨y⟩ heq
    exact Quot.sound ((hcr x y).2 ((hcond x y).2 (congrArg Subtype.val heq)))
  · rintro ⟨g, hg⟩
    obtain ⟨g', hg', hρg⟩ := hlift g hg
    let M := g'.map S.subtype
    have hMS : ∀ i j, M i j ∈ S := fun i j => (g' i j).2
    have hM : Formalism.UG.cT σA M * M = 1 := by
      have e : ((g'.map (intLocConj v))ᵀ * g').map S.subtype = Formalism.UG.cT σA M * M := by
        rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map]; rfl
      rw [← e, hg'.1, Matrix.map_one _ (map_zero _) (map_one _)]
    have hdM : M.det = 1 := by
      have e := RingHom.map_det S.subtype g'
      rw [hg'.2, map_one, RingHom.mapMatrix_apply] at e
      exact e.symm
    have hXd : (h.1 * M * (h⁻¹).1).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_mul, hdM, mul_one, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    let xg : GL (Fin r) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) :=
      Matrix.nonsingInvUnit (h.1 * M * (h⁻¹).1) (by rw [hXd]; exact isUnit_one)
    have hxU : xg ∈ HR (Fv (maximalRealSubfield E) v) (cj E) Gᵀ := cT_mul_conj_eq σA _ h hh M hM
    let xH : GLoc (cj E) Gᵀ v := (⟨xg, hxU⟩ : HR (Fv (maximalRealSubfield E) v) (cj E) Gᵀ)
    have hx1 : xH ∈ stabOne (cj E) Gᵀ Λ v :=
      ⟨hXd, mem_stabLoc.2 (frame_stab S (fun z => z ∈ latLoc (maximalRealSubfield E) Λ v) h hΛ σA
        (fun _ ha => sigR_mem_intLoc (cj E) ha) M hMS hM)⟩
    refine ⟨Quot.mk _ ⟨xH, hx1⟩, Subtype.ext ?_⟩
    change (Gm ⟨xH, hx1⟩).map ρ = g
    rw [← hρg]
    congr 1
    ext i j
    change ((h⁻¹).1 * (h.1 * M * (h⁻¹).1) * h.1) i j = M i j
    rw [show (h⁻¹).1 * (h.1 * M * (h⁻¹).1) * h.1 = M by
      simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]]

end GlobalTheory.TamOne
