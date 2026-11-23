import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf

noncomputable section

namespace GlobalTheory.CompanionTheory.CMMirror

open Matrix PositivityTheory.RgEis
open scoped NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

section Ring

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem map_mem_stab (e : R ≃+* R') (g : GL ι R) (s : Set ι) :
    Matrix.GeneralLinearGroup.map e.toRingHom g ∈ stab R' s ↔ g ∈ stab R s := by
  have key : ∀ (x : GL ι R) (r c : ι),
      ((Matrix.GeneralLinearGroup.map e.toRingHom x : GL ι R') : Matrix ι ι R') r c = 0 ↔ (x : Matrix ι ι R) r c = 0 := by
    intro x r c
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact map_eq_zero_iff e e.injective
  constructor
  · intro h r hr c hc
    have := h r hr c hc
    rw [← map_inv] at this
    exact ⟨(key _ _ _).1 this.1, (key _ _ _).1 this.2⟩
  · intro h r hr c hc
    rw [← map_inv]
    exact ⟨(key _ _ _).2 (h r hr c hc).1, (key _ _ _).2 (h r hr c hc).2⟩

theorem tInv_coe (g : GL ι R) : ((tInv g : GL ι R) : Matrix ι ι R) = ((g⁻¹ : GL ι R) : Matrix ι ι R)ᵀ := rfl

theorem tInv_inv_coe (g : GL ι R) : (((tInv g)⁻¹ : GL ι R) : Matrix ι ι R) = (g : Matrix ι ι R)ᵀ := by
  rw [← map_inv, tInv_coe, inv_inv]

theorem tInv_mem_stab (g : GL ι R) (s : Set ι) : tInv g ∈ stab R s ↔ g ∈ stab R sᶜ := by
  constructor
  · intro h r hr c hc
    have hr' : r ∈ s := by simpa using hr
    have := h c hc r hr'
    rw [tInv_inv_coe, tInv_coe] at this
    exact ⟨this.2, this.1⟩
  · intro h r hr c hc
    have := h c (by simpa using hc) r hr
    rw [tInv_inv_coe, tInv_coe]
    exact ⟨this.2, this.1⟩

theorem tInv_map (f : R →+* R') (g : GL ι R) :
    tInv (Matrix.GeneralLinearGroup.map f g) = Matrix.GeneralLinearGroup.map f (tInv g) := by
  ext r c
  rw [tInv_coe, ← map_inv, Matrix.transpose_apply, Matrix.GeneralLinearGroup.map_apply,
    Matrix.GeneralLinearGroup.map_apply, tInv_coe, Matrix.transpose_apply]

theorem tInv_tInv (g : GL ι R) : tInv (tInv g) = g := by
  ext r c
  rw [tInv_coe, tInv_inv_coe, Matrix.transpose_transpose]

theorem bdet_map (e : R ≃+* R') (s : Set ι) (g : GL ι R) :
    bdet s (Matrix.GeneralLinearGroup.map e.toRingHom g) = Units.map e.toRingHom.toMonoidHom (bdet s g) := by
  classical
  have hd : (((Matrix.GeneralLinearGroup.map e.toRingHom g : GL ι R') : Matrix ι ι R').submatrix
      (Subtype.val : s → ι) Subtype.val).det =
      e.toRingHom ((g : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
    rw [RingHom.map_det]
    congr 1
  unfold bdet
  by_cases h : IsUnit ((g : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det
  · have h' : IsUnit (((Matrix.GeneralLinearGroup.map e.toRingHom g : GL ι R') : Matrix ι ι R').submatrix
        (Subtype.val : s → ι) Subtype.val).det := by
      rw [hd]; exact h.map e.toRingHom
    rw [dif_pos h, dif_pos h']
    ext
    simpa using hd
  · have h' : ¬ IsUnit (((Matrix.GeneralLinearGroup.map e.toRingHom g : GL ι R') : Matrix ι ι R').submatrix
        (Subtype.val : s → ι) Subtype.val).det := by
      rw [hd]; intro hu
      exact h ((isUnit_map_iff e _).1 hu)
    rw [dif_neg h, dif_neg h', map_one]

theorem bdet_tInv (s : Set ι) (g : GL ι R) : bdet s (tInv g) = bdet s g⁻¹ := by
  classical
  have hd : (((tInv g : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det =
      (((g⁻¹ : GL ι R) : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
    rw [tInv_coe, ← Matrix.transpose_submatrix, Matrix.det_transpose]
  unfold bdet
  simp only [hd]

theorem bdet_val {t : Set ι} [Fintype t] {g : GL ι R} {x : R}
    (hx : ((g : Matrix ι ι R).submatrix (Subtype.val : t → ι) Subtype.val).det = x) (hu : IsUnit x) :
    ((bdet t g : Rˣ) : R) = x := by
  classical
  unfold bdet
  have h : IsUnit ((g : Matrix ι ι R).submatrix (Subtype.val : t → ι) Subtype.val).det := by rw [hx]; exact hu
  split_ifs with h'
  · rw [IsUnit.unit_spec]
    convert hx
  · exact absurd (by convert h) h'

theorem det_eq_bdet_mul (s : Set ι) (p : GL ι R) (hp : p ∈ stab R s) :
    Matrix.GeneralLinearGroup.det p = bdet s p * bdet sᶜ p := by
  classical
  have tb := Matrix.twoBlockTriangular_det (p : Matrix ι ι R) (· ∈ s) (fun r hr c hc => (hp r hr c hc).1)
  have e1 : (Matrix.toSquareBlockProp (p : Matrix ι ι R) (· ∈ s)).det =
      ((p : Matrix ι ι R).submatrix (Subtype.val : s → ι) Subtype.val).det := by
    unfold Matrix.toSquareBlockProp
    congr!
  have e2 : (Matrix.toSquareBlockProp (p : Matrix ι ι R) fun i => ¬ i ∈ s).det =
      ((p : Matrix ι ι R).submatrix (Subtype.val : (sᶜ : Set ι) → ι) Subtype.val).det := by
    unfold Matrix.toSquareBlockProp
    congr!
  rw [e1, e2] at tb
  have hu : IsUnit (p : Matrix ι ι R).det := (Matrix.isUnit_iff_isUnit_det _).1 p.isUnit
  rw [tb] at hu
  obtain ⟨h1, h2⟩ := IsUnit.mul_iff.1 hu
  ext
  rw [Units.val_mul, bdet_val rfl h1, bdet_val rfl h2]
  simpa using tb

theorem transpose_mem_unitary {ι : Type} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι ℂ} (h : U ∈ Matrix.unitaryGroup ι ℂ) :
    Uᵀ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h2 := Matrix.mem_unitaryGroup_iff'.1 h
  rw [Matrix.star_eq_conjTranspose] at h2 ⊢
  have : (Uᵀ)ᴴ = Uᴴᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [this, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

end Ring

section Data

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {ι : Type} [Fintype ι] [DecidableEq ι]

variable (F E ι) in

abbrev mpp : GL ι (AE F E) →* GL ι 𝔸[E] := Matrix.GeneralLinearGroup.map (eqv F E).toRingHom

theorem tInv_mem_kGL {E R : Type} [Field E] [CommRing R] (A : Ad E R) (κ : GL ι R) (h : κ ∈ A.kGL ι) :
    tInv κ ∈ A.kGL ι := by
  have hi : κ⁻¹ ∈ A.kGL ι := inv_mem h
  refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · rw [tInv_coe]; exact (h.1 c r).2
  · rw [tInv_inv_coe]; exact (h.1 c r).1
  · rw [tInv_coe, Matrix.transpose_map]
    exact transpose_mem_unitary (hi.2 w)

theorem map_mem_kGL (σ : E →ₐ[F] E) (χ : Chr F E) (κ : GL ι (AE F E)) (h : κ ∈ (adCM σ χ).kGL ι) :
    mpp F E ι κ ∈ (adStd E).kGL ι := by
  refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · rw [Matrix.GeneralLinearGroup.map_apply]; exact (h.1 r c).1
  · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply]; exact (h.1 r c).2
  · exact h.2 w

theorem map_i (σ : E →ₐ[F] E) (χ : Chr F E) (hi : ∀ x : E, eqv F E (inclR (F := F) (AF F) x) = algebraMap E 𝔸[E] x) (x : GL ι E) :
    mpp F E ι (Matrix.GeneralLinearGroup.map (adCM σ χ).i x) = Matrix.GeneralLinearGroup.map (adStd E).i x := by
  ext r c
  simp only [Matrix.GeneralLinearGroup.map_apply]
  exact hi _

theorem lg_bdet (σ : E →ₐ[F] E) (χ : Chr F E) (s : Set ι) (g : GL ι (AE F E)) :
    (adStd E).lg (bdet s (mpp F E ι g)) = (adCM σ χ).lg (bdet s g) := by
  rw [bdet_map]; rfl

theorem lg_det (σ : E →ₐ[F] E) (χ : Chr F E) (g : GL ι (AE F E)) :
    (adStd E).lg (Matrix.GeneralLinearGroup.det (mpp F E ι g)) = (adCM σ χ).lg (Matrix.GeneralLinearGroup.det g) := by
  have : Matrix.GeneralLinearGroup.det (mpp F E ι g) = Units.map (eqv F E).toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
    ext
    simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]
  rw [this]; rfl

theorem comap_map (s : Set ι) : (stab 𝔸[E] s).comap (mpp F E ι) = stab (AE F E) s := by
  ext g; exact map_mem_stab _ g s

theorem comap_tInv (s : Set ι) : (stab 𝔸[E] s).comap (tInv.comp (mpp F E ι)) = stab (AE F E) sᶜ := by
  ext g
  rw [Subgroup.mem_comap, MonoidHom.comp_apply, tInv_mem_stab, map_mem_stab]

theorem cont_mp (hc : Continuous (eqv F E)) : Continuous (mpp F E ι) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_map hc)
  · have : (fun g : GL ι (AE F E) => ((mpp F E ι g)⁻¹ : GL ι 𝔸[E]).val) = fun g => (((g⁻¹ : GL ι (AE F E)) : Matrix ι ι (AE F E))).map (eqv F E) := by
      funext g
      rw [← map_inv]; rfl
    exact (this ▸ (Units.continuous_val.comp continuous_inv).matrix_map hc)

theorem cont_tInv {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] : Continuous (tInv (ι := ι) (R := R)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · have : (fun g : GL ι R => ((tInv g)⁻¹ : GL ι R).val) = fun g : GL ι R => (g : Matrix ι ι R)ᵀ := by
      funext g; exact tInv_inv_coe g
    exact this ▸ Units.continuous_val.matrix_transpose

theorem one_toIdele (x : GroundTheory.Global.IdeleGroup E) : (((1 : GroundTheory.Global.HeckeCharacter E).toIdele x : Circle) : ℂ) = 1 := by
  simp [GroundTheory.Global.HeckeCharacter.toIdele_apply]

end Data

section Vals

theorem isHt_sub {G : Type} [Group G] [TopologicalSpace G] {Γ K P : Subgroup G} {a b : G → ℝ} (h1 : IsHt Γ K P a)
    (h2 : IsHt Γ K ⊤ b) : IsHt Γ K P fun g => a g - b g where
  left p hp g := by
    have e1 := h1.left p hp g
    have e2 := h2.left p (Subgroup.mem_top p) g
    simp only [e1, e2]; ring
  right g k hk := by simp only [h1.right g k hk, h2.right g k hk]
  rat γ hγ hp := by simp only [h1.rat γ hγ hp, h2.rat γ hγ (Subgroup.mem_top γ), sub_zero]
  cont := h1.cont.sub h2.cont

theorem isHt_neg {G : Type} [Group G] [TopologicalSpace G] {Γ K : Subgroup G} {b : G → ℝ}
    (h : IsHt Γ K ⊤ b) : IsHt Γ K ⊤ fun g => - b g where
  left p hp g := by
    have e := h.left p hp g
    simp only [e]; ring
  right g k hk := by simp only [h.right g k hk]
  rat γ hγ hp := by simp only [h.rat γ hγ hp, neg_zero]
  cont := h.cont.neg

theorem isHt_inv {G : Type} [Group G] [TopologicalSpace G] {Γ K P : Subgroup G} {a : G → ℝ} (h : IsHt Γ K P a)
    (p : G) (hp : p ∈ P) : a p⁻¹ = - a p := by
  have e := h.left p hp p⁻¹
  rw [mul_inv_cancel, h.rat 1 (one_mem _) (one_mem _)] at e
  linarith

variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem htGL_val (A : Ad E R) (hA : A.GoodL) (hB : BdetLaw) (hE : ExtLaw) [T2Space (GL ι R)] (s : Set ι)
    (p : GL ι R) (hp : p ∈ stab R s) : A.htGL s p = A.lg (bdet s p) := by
  obtain ⟨hcl, hmul, hcont, hrat, hk, -⟩ := hB E R A hA ι s
  have := (hE (GL ι R) (A.ratGL ι) (A.kGL ι) (stab R s) (fun p => A.lg (bdet s p)) (hA.kcpt ι) hcl (hA.iwa ι s)
    (fun p hp q hq => by simp only [hmul p hp q hq, hA.lgmul]) (hA.lgcont.comp_continuousOn hcont) hk
    (fun p hp hr => by obtain ⟨x, hx⟩ := hrat p hp hr; simp only [hx]; exact hA.lgi x)).2 p hp 1 (one_mem _)
  rw [mul_one] at this
  exact this

theorem htGL_univ (A : Ad E R) (hA : A.GoodL) (hB : BdetLaw) (hE : ExtLaw) [T2Space (GL ι R)] (p : GL ι R) :
    A.htGL Set.univ p = A.lg (Matrix.GeneralLinearGroup.det p) := by
  have hp : p ∈ stab R (Set.univ : Set ι) := fun r hr => absurd (Set.mem_univ r) hr
  rw [htGL_val A hA hB hE _ p hp, (hB E R A hA ι Set.univ).2.2.2.2.2 p]

theorem ht_mirror (A : Ad E R) (hA : A.GoodL) (hB : BdetLaw) (hE : ExtLaw) [T2Space (GL ι R)] (i : ι) (p : GL ι R)
    (hp : p ∈ stab R ({i}ᶜ : Set ι)) : A.htGL {i}ᶜ p - A.htGL Set.univ p = - A.lg (bdet {i} p) := by
  rw [htGL_val A hA hB hE _ p hp, htGL_univ A hA hB hE, det_eq_bdet_mul _ p hp, hA.lgmul, compl_compl]
  ring

end Vals

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem diag_one : Matrix.diagonal (fun i : ι => (((1 : ι → GroundTheory.Global.IdeleGroup E) i : GroundTheory.Global.IdeleGroup E) : 𝔸[E])) = 1 := by
  simp

theorem mirData_map (hc : Continuous (eqv F E))
    (hi : ∀ x : E, eqv F E (inclR (F := F) (AF F) x) = algebraMap E 𝔸[E] x) (σ : E →ₐ[F] E) (χ : Chr F E)
    (hG : (adCM σ χ).Good) (hB : BdetLaw) (hE : ExtLaw) (hP : ParLaw) [T2Space (GL ι (AE F E))]
    (two : 2 ≤ Fintype.card ι) (i₀ i₁ : ι) :
    MirData (mpp F E ι) ((adCM σ χ).ratGL ι) ((adCM σ χ).kGL ι) i₀ i₁ 1 1 1 ((adCM σ χ).htGL {i₀})
      (fun g => (adCM σ χ).htGL {i₁}ᶜ g - (adCM σ χ).htGL Set.univ g) ((adCM σ χ).htGL Set.univ) := by
  have hP0 := fun s : Set ι => (hP E (AE F E) (adCM σ χ) hG ι 1 s).1
  have hL := hG.toGoodL
  have htop : IsHt ((adCM σ χ).ratGL ι) ((adCM σ χ).kGL ι) ⊤ ((adCM σ χ).htGL Set.univ) := by
    have h := hP0 Set.univ
    rw [h.2.2.2.2] at h
    exact h.2.2.2.1
  refine
    { two := two
      sq := mul_one 1
      cont := cont_mp hc
      cpt := hL.kcpt ι
      piK := fun κ hκ => ⟨mpp F E ι κ, map_mem_kGL σ χ κ hκ, by rw [diag_one, mul_one, one_mul]⟩
      piΓ := ?_
      trans := ?_
      par := by rw [comap_map]; exact (hP0 _).1
      par' := by rw [comap_map]; exact (hP0 _).1
      ht := by rw [comap_map]; exact (hP0 _).2.2.2.1
      ht' := by rw [comap_map]; exact isHt_sub (hP0 _).2.2.2.1 htop
      htl := htop
      val := fun p hp => ⟨(one_toIdele _).symm, by
        rw [htGL_val _ hL hB hE _ p ((map_mem_stab _ p _).1 hp), lg_bdet σ χ]⟩
      val' := fun p hp => ⟨(one_toIdele _).symm,
        (ht_mirror _ hL hB hE i₁ p ((map_mem_stab _ p _).1 hp)).trans (by rw [lg_bdet σ χ])⟩
      vall := fun g => by rw [htGL_univ _ hL hB hE, lg_det σ χ] }
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, (map_i σ χ hi x).symm⟩
  · rintro s - g ⟨x, rfl⟩
    refine ⟨_, ⟨x, rfl⟩, ?_⟩
    rw [map_i σ χ hi, mul_inv_cancel]
    exact one_mem _

theorem mirData_tInv (hc : Continuous (eqv F E))
    (hi : ∀ x : E, eqv F E (inclR (F := F) (AF F) x) = algebraMap E 𝔸[E] x) (σ : E →ₐ[F] E) (χ : Chr F E)
    (hG : (adCM σ χ).Good) (hB : BdetLaw) (hE : ExtLaw) (hP : ParLaw) [T2Space (GL ι (AE F E))]
    (two : 2 ≤ Fintype.card ι) (i₀ i₁ : ι) :
    MirData (tInv.comp (mpp F E ι)) ((adCM σ χ).ratGL ι) ((adCM σ χ).kGL ι) i₁ i₀ 1 1 1
      (fun g => (adCM σ χ).htGL {i₁}ᶜ g - (adCM σ χ).htGL Set.univ g) ((adCM σ χ).htGL {i₀})
      (fun g => - (adCM σ χ).htGL Set.univ g) := by
  have hP0 := fun s : Set ι => (hP E (AE F E) (adCM σ χ) hG ι 1 s).1
  have hL := hG.toGoodL
  have htop : IsHt ((adCM σ χ).ratGL ι) ((adCM σ χ).kGL ι) ⊤ ((adCM σ χ).htGL Set.univ) := by
    have h := hP0 Set.univ
    rw [h.2.2.2.2] at h
    exact h.2.2.2.1
  have hη : IsHt ((adCM σ χ).ratGL ι) ((adCM σ χ).kGL ι) (stab (AE F E) ({i₁}ᶜ : Set ι))
      (fun g => (adCM σ χ).htGL {i₁}ᶜ g - (adCM σ χ).htGL Set.univ g) := isHt_sub (hP0 _).2.2.2.1 htop
  have hη' := (hP0 {i₀}).2.2.2.1
  have htp : ∀ p : GL ι (AE F E), (tInv.comp (mpp F E ι)) p = mpp F E ι (tInv p) := fun p => tInv_map _ p
  have hmem : ∀ (s : Set ι) (p : GL ι (AE F E)), (tInv.comp (mpp F E ι)) p ∈ stab 𝔸[E] s → p ∈ stab (AE F E) sᶜ :=
    fun s p hp => by
      have : p ∈ (stab 𝔸[E] s).comap (tInv.comp (mpp F E ι)) := hp
      rwa [comap_tInv] at this
  have hr : ∀ x : GL ι E, (tInv.comp (mpp F E ι)) (Matrix.GeneralLinearGroup.map (adCM σ χ).i x) =
      Matrix.GeneralLinearGroup.map (adStd E).i (tInv x) := fun x => by
    rw [htp, ← tInv_map, map_i σ χ hi]
    exact tInv_map _ _
  refine
    { two := two
      sq := mul_one 1
      cont := cont_tInv.comp (cont_mp hc)
      cpt := hL.kcpt ι
      piK := fun κ hκ => ⟨tInv (mpp F E ι κ), tInv_mem_kGL _ _ (map_mem_kGL σ χ κ hκ), by
        rw [diag_one, mul_one, one_mul]; rfl⟩
      piΓ := ?_
      trans := ?_
      par := by rw [comap_tInv]; exact (hP0 _).1
      par' := by rw [comap_tInv, compl_compl]; exact (hP0 _).1
      ht := by rw [comap_tInv]; exact hη
      ht' := by rw [comap_tInv, compl_compl]; exact hη'
      htl := isHt_neg htop
      val := ?_
      val' := ?_
      vall := ?_ }
  · rintro _ ⟨x, rfl⟩
    exact ⟨tInv x, (hr x).symm⟩
  · rintro s - g ⟨x, rfl⟩
    refine ⟨_, ⟨tInv x, rfl⟩, ?_⟩
    rw [hr, tInv_tInv, mul_inv_cancel]
    exact one_mem _
  · intro p hp
    have hp' := hmem _ p hp
    refine ⟨(one_toIdele _).symm, ?_⟩
    rw [htp, lg_bdet σ χ, bdet_tInv]
    have h1 := ht_mirror _ hL hB hE i₁ p⁻¹ (inv_mem hp')
    have h2 := isHt_inv hη p hp'
    linarith
  · intro p hp
    have hp' := hmem _ p hp
    rw [compl_compl] at hp'
    refine ⟨(one_toIdele _).symm, ?_⟩
    rw [htp, lg_bdet σ χ, bdet_tInv, ← htGL_val _ hL hB hE _ p⁻¹ (inv_mem hp'), isHt_inv hη' p hp', neg_neg]
  · intro g
    have hb := fun x : GL ι (AE F E) => (hB E (AE F E) (adCM σ χ) hL ι Set.univ).2.2.2.2.2 x
    rw [htp, lg_det σ χ, ← hb, bdet_tInv, hb, ← htGL_univ _ hL hB hE, isHt_inv htop g (Subgroup.mem_top g)]

theorem cmMir : Dict → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → MirGen → CMMir := by
  intro hD hCM hT hB hE hP hM F E _ _ _ _ _ σ χ c h1 h2 h3 h4 ι _ _ i₀ i₁ two
  have hG := hCM F E σ χ c h1 h2 h3 h4
  obtain ⟨hc, -, hi, -, -⟩ := hD F E
  obtain ⟨t2, lc, sc, -⟩ := hT E (AE F E) (adCM σ χ) hG ι 1
  have hK := hG.toGoodL.kcpt ι
  have hm := mirData_map hc hi σ χ hG hB hE hP two i₀ i₁
  have ht := mirData_tInv hc hi σ χ hG hB hE hP two i₀ i₁
  refine ⟨?_, ?_, ?_⟩
  · intro W _ _ _ ρ hρ
    have h := ((hM (GL ι (AE F E)) W ((adCM σ χ).kGL ι) ρ hK hρ E ι _ _ i₀ i₁ 1 1 1 _ _ _ sc hm).2 rfl rfl).1
    rwa [comap_map, comap_map] at h
  · intro W _ _ _ ρ hρ
    have h := (hM (GL ι (AE F E)) W ((adCM σ χ).kGL ι) ρ hK hρ E ι _ _ i₁ i₀ 1 1 1 _ _ _ sc ht).1
    rw [comap_tInv, comap_tInv, compl_compl] at h
    convert h using 2
    ring
  · intro W _ _ _ ρ hρ
    have h := ((hM (GL ι (AE F E)) W ((adCM σ χ).kGL ι) ρ hK hρ E ι _ _ i₀ i₁ 1 1 1 _ _ _ sc hm).2 rfl rfl).2
    rwa [comap_map, comap_map] at h

end Main

end GlobalTheory.CompanionTheory.CMMirror
