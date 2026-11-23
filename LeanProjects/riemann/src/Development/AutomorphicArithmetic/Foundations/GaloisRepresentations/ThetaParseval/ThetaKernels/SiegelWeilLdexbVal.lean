import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.DetLast
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldDefs

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Ldexb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem jpar_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {j : G2 σ Y →* d.G}
    (hJ : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) {p : G2 σ Y} (hp : ParF b p) :
    ParF d.b (j p) ∧ (inFrame d.b (j p)).toBlocks₁₁.det = (inFrame b p).toBlocks₁₁.det := by
  obtain ⟨-, h2, h3⟩ := hJ
  set X := inFrame d.b (j p) with hX
  have hsub : ∀ x y, X (Sum.map (Ald.em0 h) (Ald.em0 h) x) (Sum.map (Ald.em0 h) (Ald.em0 h) y) = inFrame b p x y :=
    fun x y => by rw [← h2 p]; rfl
  have hl : ∀ v, X (Sum.inl (Ald.i0 h)) v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inl (Ald.i0 h)) v :=
    fun v => (h3 p _ (by simp) v).1
  have hl' : ∀ v, X v (Sum.inl (Ald.i0 h)) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) v (Sum.inl (Ald.i0 h)) :=
    fun v => (h3 p _ (by simp) v).2
  have hr : ∀ v, X (Sum.inr (Ald.i0 h)) v = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) (Sum.inr (Ald.i0 h)) v :=
    fun v => (h3 p _ (by simp) v).1
  constructor
  · show X.toBlocks₂₁ = 0
    ext a c
    show X (Sum.inr a) (Sum.inl c) = 0
    by_cases ha : a = Ald.i0 h
    · subst ha; rw [hr]; simp [Matrix.one_apply]
    by_cases hc : c = Ald.i0 h
    · subst hc; rw [hl']; simp [Matrix.one_apply]
    obtain ⟨a', rfl⟩ := (Ald.ne_last_iff_mem_range h a).1 ha
    obtain ⟨c', rfl⟩ := (Ald.ne_last_iff_mem_range h c).1 hc
    have e := hsub (Sum.inr a') (Sum.inl c')
    simp only [Sum.map_inr, Sum.map_inl] at e
    rw [e]
    exact congrFun (congrFun hp a') c'
  · rw [det_last h X.toBlocks₁₁ (fun c => by
      show X (Sum.inl (Ald.i0 h)) (Sum.inl c) = _
      rw [hl]; by_cases hc : c = Ald.i0 h
      · subst hc; simp
      · simp [Matrix.one_apply, hc, Ne.symm hc])]
    congr 1
    ext a c
    have e := hsub (Sum.inl a) (Sum.inl c)
    simp only [Sum.map_inl] at e
    exact e
theorem val_pull_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {j : G2 σ Y →* d.G}
    (hJ : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) (hb : IsFrame2 σ Y b) :
    ∀ (p : G2 σ Y) (t : GL (Fin n) (AE F E)), IsPar p t → ∀ k ∈ d.K.comap j,
      (d.a ∘ j) (p * k) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
  intro p t hpt k hk
  obtain ⟨hpf, hdet⟩ := par_to hb hpt
  obtain ⟨hbig, hdet2⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ldexb.jpar_k h hJ hpf
  obtain ⟨t', ht', hdt'⟩ := par_of d.ok.frame hbig
  show d.a (j (p * k)) = _
  rw [map_mul, d.ok.hgt.val (j p) t' ht' (j k) hk]
  congr 2
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  rw [hdt', hdet2, hdet]
end PositivityTheory.SiegelWeilFormula.Ldexb
end
end
