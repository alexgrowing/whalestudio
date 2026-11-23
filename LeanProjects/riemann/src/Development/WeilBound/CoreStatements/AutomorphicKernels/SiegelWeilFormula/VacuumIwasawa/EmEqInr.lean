import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IsParOfFrame

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open GlobalTheory.Doubling (absE)

section Gen

variable {ι κ R : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Semiring R]

def IdI (S : Set ι) (H : Matrix ι ι R) : Prop := ∀ u ∈ S, ∀ v, H u v = (1 : Matrix ι ι R) u v ∧ H v u = (1 : Matrix ι ι R) v u

theorem IdI.mul {S : Set ι} {H H' : Matrix ι ι R} (h : IdI S H) (h' : IdI S H') : IdI S (H * H') := by
  intro u hu v
  refine ⟨?_, ?_⟩
  · rw [mul_row_one (fun v => (h u hu v).1)]; exact (h' u hu v).1
  · rw [mul_col_one (fun v => (h' u hu v).2)]; exact (h u hu v).2

theorem IdI.sub_mul {S : Set ι} {H : Matrix ι ι R} (h : IdI S H) (H' : Matrix ι ι R) {e : κ → ι} (he : Function.Injective e)
    (hr : ∀ c, c ∉ S ↔ c ∈ Set.range e) : (H * H').submatrix e e = H.submatrix e e * H'.submatrix e e := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine (Fintype.sum_of_injective e he _ _ (fun c hc => ?_) (fun c => rfl)).symm
  have hcS : c ∈ S := by by_contra h'; exact hc ((hr c).1 h')
  have hne : e a ≠ c := by rintro rfl; exact (hr _).2 ⟨a, rfl⟩ hcS
  rw [(h c hcS (e a)).2, Matrix.one_apply_ne hne, zero_mul]

theorem IdI.eq_one {S : Set ι} {X : Matrix ι ι R} (h : IdI S X) {e : κ → ι} (he : Function.Injective e)
    (hr : ∀ c, c ∉ S ↔ c ∈ Set.range e) (h1 : X.submatrix e e = 1) : X = 1 := by
  ext u v
  by_cases hu : u ∈ S
  · exact (h u hu v).1
  by_cases hv : v ∈ S
  · exact (h v hv u).2
  obtain ⟨a, rfl⟩ := (hr u).1 hu
  obtain ⟨b, rfl⟩ := (hr v).1 hv
  have := congrFun (congrFun h1 a) b
  rw [Matrix.submatrix_apply] at this
  rw [this]
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (he.ne hab)]

end Gen

theorem IdI.map {ι R R' : Type} [Fintype ι] [DecidableEq ι] [Semiring R] [Semiring R'] {S : Set ι} {H : Matrix ι ι R}
    (h : IdI S H) (f : R →+* R') : IdI S (H.map f) := by
  intro u hu v
  simp only [Matrix.map_apply, (h u hu v).1, (h u hu v).2, Matrix.one_apply]
  constructor <;> split_ifs <;> simp

theorem IdI.ct {ι : Type} [Fintype ι] [DecidableEq ι] {S : Set ι} {H : Matrix ι ι ℂ} (h : IdI S H) : IdI S Hᴴ := by
  intro u hu v
  simp only [Matrix.conjTranspose_apply, (h u hu v).1, (h u hu v).2]
  by_cases huv : u = v
  · subst huv; simp
  · simp [Matrix.one_apply_ne huv, Matrix.one_apply_ne (Ne.symm huv)]

def emEq {d : SD σ} (L : LD d) : Fin L.n ⊕ Unit ≃ Fin d.n :=
  Equiv.ofBijective (Sum.elim L.em fun _ => L.i₀) ⟨by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (L.inj h)
    · exact absurd h ((L.rng (L.em a)).2 ⟨a, rfl⟩)
    · exact absurd h.symm ((L.rng (L.em b)).2 ⟨b, rfl⟩)
    · rfl, fun i => by
    by_cases h : i = L.i₀
    · exact ⟨Sum.inr (), h.symm⟩
    · obtain ⟨a, ha⟩ := (L.rng i).1 h
      exact ⟨Sum.inl a, ha⟩⟩

theorem emEq_inl {d : SD σ} (L : LD d) (a : Fin L.n) : emEq L (Sum.inl a) = L.em a := rfl

theorem emEq_inr {d : SD σ} (L : LD d) (u : Unit) : emEq L (Sum.inr u) = L.i₀ := rfl

theorem det_emb {d : SD σ} (L : LD d) (N : Matrix (Fin d.n) (Fin d.n) (AE F E)) (N' : Matrix (Fin L.n) (Fin L.n) (AE F E))
    (h0 : ∀ k, N L.i₀ k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) L.i₀ k ∧
      N k L.i₀ = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) k L.i₀)
    (h1 : N.submatrix L.em L.em = N') : N.det = N'.det := by
  rw [← Matrix.det_submatrix_equiv_self (emEq L) N]
  have hne : ∀ a, L.em a ≠ L.i₀ := fun a => (L.rng (L.em a)).2 ⟨a, rfl⟩
  have : N.submatrix (emEq L) (emEq L) = Matrix.fromBlocks N' 0 0 1 := by
    ext (a | a) (b | b)
    · rw [Matrix.submatrix_apply, emEq_inl, emEq_inl, Matrix.fromBlocks_apply₁₁, ← h1, Matrix.submatrix_apply]
    · rw [Matrix.submatrix_apply, emEq_inl, emEq_inr, Matrix.fromBlocks_apply₁₂, (h0 (L.em a)).2,
        Matrix.one_apply_ne (hne a), Matrix.zero_apply]
    · rw [Matrix.submatrix_apply, emEq_inl, emEq_inr, Matrix.fromBlocks_apply₂₁, (h0 (L.em b)).1,
        Matrix.one_apply_ne (hne b).symm, Matrix.zero_apply]
    · rw [Matrix.submatrix_apply, emEq_inr, Matrix.fromBlocks_apply₂₂, (h0 L.i₀).1, Matrix.one_apply_eq,
        Matrix.one_apply_eq]
  rw [this, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem emm_inj {d : SD σ} (L : LD d) : Function.Injective (Sum.map L.em L.em) := Sum.map_injective.2 ⟨L.inj, L.inj⟩

theorem emm_rng {d : SD σ} (L : LD d) : ∀ c, c ∉ I0 L.i₀ ↔ c ∈ Set.range (Sum.map L.em L.em) := by
  rintro (c | c)
  · simp only [I0, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq, reduceCtorEq, or_false]
    rw [show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩
    · rintro ⟨(a | a), h⟩
      · exact ⟨a, Sum.inl_injective h⟩
      · simp at h
  · simp only [I0, Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inr.injEq, reduceCtorEq, false_or]
    rw [show (¬c = L.i₀) ↔ c ∈ Set.range L.em from L.rng c]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩
    · rintro ⟨(a | a), h⟩
      · simp at h
      · exact ⟨a, Sum.inr_injective h⟩

theorem idI_j {d : SD σ} (L : LD d) (g : L.sd.G) : IdI (I0 L.i₀) (inFrame d.b (L.j g)) := fun u hu v => L.j_out g u hu v

theorem j_K {d : SD σ} (L : LD d) {k : L.sd.G} (hk : k ∈ L.sd.K) : L.j k ∈ d.K := by
  have hL := (L.ok.stdK k).1 hk
  refine (d.ok.stdK (L.j k)).2 ⟨fun w => ?_, fun k'' hk'' i j => ?_⟩
  · have hI := (idI_j L k).map (piInf (d.B.emb w))
    refine (hI.mul hI.ct).eq_one (emm_inj L) (emm_rng L) ?_
    rw [hI.sub_mul _ (emm_inj L) (emm_rng L), ← Matrix.conjTranspose_submatrix, Matrix.submatrix_map, L.j_in]
    exact hL.1 w
  · obtain ⟨k₀, hk₀, rfl⟩ : ∃ k₀ ∈ ({k, k⁻¹} : Set L.sd.G), k'' = L.j k₀ := by
      rcases hk'' with rfl | rfl
      · exact ⟨k, Or.inl rfl, rfl⟩
      · exact ⟨k⁻¹, Or.inr rfl, (map_inv L.j k).symm⟩
    by_cases hi : i ∈ I0 L.i₀
    · rw [(idI_j L k₀ i hi j).1]; exact KSplitW.finOne_one_mem d i j
    by_cases hj : j ∈ I0 L.i₀
    · rw [(idI_j L k₀ j hj i).2]; exact KSplitW.finOne_one_mem d i j
    obtain ⟨a, rfl⟩ := (emm_rng L i).1 hi
    obtain ⟨b, rfl⟩ := (emm_rng L j).1 hj
    have e := congrFun (congrFun (L.j_in k₀) a) b
    rw [Matrix.submatrix_apply] at e
    rw [e]
    exact hL.2 k₀ hk₀ a b

theorem a_j {d : SD σ} (L : LD d) (h : L.sd.G) : d.a (L.j h) = L.a h := by
  obtain ⟨p', t', hp', k', hk', rfl⟩ := L.ok.hgt.iwa h
  have h21L := KWhit.parabolic_lower_block_zero L.sd p' t' hp'
  obtain ⟨t₂, hp₂, hdet₂⟩ := isPar_of_frame L.sd p' h21L
  have hI := idI_j L p'
  have h21 : (inFrame d.b (L.j p')).toBlocks₂₁ = 0 := by
    ext a b
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
    by_cases ha : Sum.inr a ∈ I0 L.i₀
    · rw [(hI _ ha _).1]; simp
    by_cases hb : Sum.inl b ∈ I0 L.i₀
    · rw [(hI _ hb _).2]; simp
    obtain ⟨a', ha'⟩ := (emm_rng L _).1 ha
    obtain ⟨b', hb'⟩ := (emm_rng L _).1 hb
    rcases a' with a' | a'
    · simp at ha'
    rcases b' with b' | b'
    · have e := congrFun (congrFun (L.j_in p') (Sum.inr a')) (Sum.inl b')
      simp only [Matrix.submatrix_apply] at e
      rw [← ha', ← hb', e]
      have := congrFun (congrFun h21L a') b'
      simpa [Matrix.toBlocks₂₁] using this
    · simp at hb'
  obtain ⟨t₁, hp₁, hdet₁⟩ := isPar_of_frame d (L.j p') h21
  have hdet : Matrix.GeneralLinearGroup.det t₁ = Matrix.GeneralLinearGroup.det t₂ := by
    refine Units.ext ?_
    rw [hdet₁, hdet₂]
    refine det_emb L _ _ (fun k => ⟨?_, ?_⟩) ?_
    · simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
      rw [(hI _ (Or.inl rfl) _).1]; simp [Matrix.one_apply]
    · simp only [Matrix.toBlocks₁₁, Matrix.of_apply]
      rw [(hI _ (Or.inl rfl) _).2]; simp [Matrix.one_apply]
    · ext a b
      have e := congrFun (congrFun (L.j_in p') (Sum.inl a)) (Sum.inl b)
      simpa [Matrix.toBlocks₁₁] using e
  rw [map_mul, d.ok.hgt.val _ _ hp₁ _ (j_K L hk'), L.ok.hgt.val _ _ hp₂ _ hk', hdet]

theorem q_ht' {d : SD σ} (L : LD d) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E L.i₀ (inFrame d.b q) lam) (h : L.sd.G) :
    d.a (q * L.j h) = (absE F E lam : ℝ) * L.a h := by
  obtain ⟨t, hp, hdet⟩ := isPar_of_frame d q (isQ_21 hq)
  have e : Matrix.GeneralLinearGroup.det t = lam :=
    Units.ext (by rw [hdet, det_row (isQ_11 hq).1, (isQ_11 hq).2])
  rw [a_mul_par d hp, e, a_j L h]

end PositivityTheory.SiegelWeilFormula.Avac

end
