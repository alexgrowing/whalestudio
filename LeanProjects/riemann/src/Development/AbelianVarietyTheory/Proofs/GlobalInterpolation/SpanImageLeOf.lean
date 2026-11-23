import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.IdealTransport

section General

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
  (φ : R ≃+* R') (f : M ≃+ M') (h : ∀ r m, f (r • m) = φ r • f m)

include h

theorem span_image_le_of (N : Submodule R M) (N' : Submodule R' M') (S : Set M) (hS : N = Submodule.span R S)
    (hN : ∀ m ∈ S, f m ∈ N') : Submodule.span R' (f '' (N : Set M)) ≤ N' := by
  rw [Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  show f m ∈ N'
  have hm' : m ∈ Submodule.span R S := hS ▸ hm
  clear hm
  induction hm' using Submodule.span_induction with
  | mem x hx => exact hN x hx
  | zero => rw [map_zero]; exact N'.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact N'.add_mem hx hy
  | smul r x _ hx => rw [h]; exact N'.smul_mem _ hx

theorem span_image_span (S : Set M) :
    Submodule.span R' (f '' (Submodule.span R S : Set M)) = Submodule.span R' (f '' S) := by
  apply le_antisymm
  · exact span_image_le_of φ f h _ _ S rfl fun m hm => Submodule.subset_span ⟨m, hm, rfl⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem mem_span_image (N : Submodule R M) (x : M') :
    x ∈ Submodule.span R' (f '' (N : Set M)) ↔ f.symm x ∈ N := by
  have hsm : ∀ (r : R') (y : M'), f.symm (r • y) = φ.symm r • f.symm y := by
    intro r y
    apply f.injective
    rw [h, AddEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      simpa using hm
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact N.add_mem hy hz
    | smul r y _ hy => rw [hsm]; exact N.smul_mem _ hy
  · intro hx
    exact Submodule.subset_span ⟨f.symm x, hx, by simp⟩

end General

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E')

theorem map_smul_int (r : 𝓞 E) (x : E) : e (r • x) = RingOfIntegers.mapRingEquiv e r • e x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

abbrev trI (I : Submodule (𝓞 E) E) : Submodule (𝓞 E') E' := Submodule.span (𝓞 E') (e '' (I : Set E))

abbrev trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E') (Fin n → E') :=
  Submodule.span (𝓞 E') ((fun (x : Fin n → E) (i : Fin n) => e (x i)) '' (N : Set (Fin n → E)))

theorem mem_trI (I : Submodule (𝓞 E) E) (x : E') : x ∈ trI e I ↔ e.symm x ∈ I := mem_span_image (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) I x

theorem trI_span (S : Set E) : trI e (Submodule.span (𝓞 E) S) = Submodule.span (𝓞 E') (e '' S) := span_image_span (RingOfIntegers.mapRingEquiv e) e.toAddEquiv (map_smul_int e) S

theorem mem_trL {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E') :
    x ∈ trL e N ↔ (fun i => e.symm (x i)) ∈ N := mem_span_image (RingOfIntegers.mapRingEquiv e) (AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv)
    (fun r v => funext fun i => map_smul_int e r (v i)) N x

theorem trI_mul (I J : Submodule (𝓞 E) E) : trI e (I * J) = trI e I * trI e J := by
  rw [Submodule.mul_eq_span_mul_set I J, trI_span, Set.image_mul]
  exact (Submodule.span_mul_span _ _ _).symm

theorem trI_singleton (y : E) : trI e (Submodule.span (𝓞 E) {y}) = Submodule.span (𝓞 E') {e y} := by
  rw [trI_span, Set.image_singleton]

theorem trI_one : trI e 1 = 1 := by
  conv_lhs => rw [Submodule.one_eq_span]
  rw [trI_singleton, map_one, ← Submodule.one_eq_span]

theorem trI_surj (J : Submodule (𝓞 E') E') : ∃ I, trI e I = J := by
  refine ⟨Submodule.span (𝓞 E) (e.symm '' (J : Set E')), ?_⟩
  rw [trI_span, Set.image_image]
  simp only [RingEquiv.apply_symm_apply, Set.image_id']
  exact Submodule.span_eq J

theorem mem_one_iff (x : E') : x ∈ (1 : Submodule (𝓞 E') E') ↔ e.symm x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← trI_one e, mem_trI]

theorem map_mulVec' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (A.map e).mulVec (fun i => e (v i)) = fun i => e (A.mulVec v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem det_map' {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : (A.map e).det = e A.det := (RingHom.map_det (e : E →+* E') A).symm

theorem carries_iff {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) (A : Matrix (Fin n) (Fin n) E) :
    (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')), (A.map e).mulVec v ∈ trL e N) ↔
      ∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)), A.mulVec v ∈ N := by
  constructor
  · intro H v hv
    have hv' : (fun i => e (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [mem_one_iff e, RingEquiv.symm_apply_apply]
      exact hv i hi
    have hA := H _ hv'
    rw [map_mulVec' e A v, mem_trL] at hA
    simpa using hA
  · intro H v hv
    have hv' : (fun i => e.symm (v i)) ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      rw [Submodule.mem_pi] at hv ⊢
      intro i hi
      rw [← mem_one_iff e]
      exact hv i hi
    have hmv : (A.map e).mulVec v = fun i => e (A.mulVec (fun i => e.symm (v i)) i) := by
      have hk := map_mulVec' e A (fun i => e.symm (v i))
      simp only [RingEquiv.apply_symm_apply] at hk
      exact hk
    rw [hmv, mem_trL]
    simpa using H _ hv'

theorem det_set {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E)) :
    {x | ∃ A : Matrix (Fin n) (Fin n) E', (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E') E')),
        A.mulVec v ∈ trL e N) ∧ x = A.det} =
      e '' {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)),
        A.mulVec v ∈ N) ∧ x = A.det} := by
  ext x
  constructor
  · rintro ⟨A', hA', rfl⟩
    have hmap : (A'.map e.symm).map e = A' := by
      ext i j
      simp
    refine ⟨(A'.map e.symm).det, ⟨A'.map e.symm, ?_, rfl⟩, ?_⟩
    · rw [← carries_iff e N, hmap]
      exact hA'
    · rw [← det_map', hmap]
  · rintro ⟨y, ⟨A, hA, rfl⟩, rfl⟩
    exact ⟨A.map e, (carries_iff e N A).mpr hA, (det_map' e A).symm⟩

end Fields

theorem transport : ∀ (D : D7) (X : Fields) (s : Seam D X), (∀ (I : Submodule (𝓞 X.E) X.E) (x : D.host.E), x ∈ idTo s I ↔ s.iE.symm x ∈ I) ∧ (∀ I J : Submodule (𝓞 X.E) X.E, idTo s (I * J) = idTo s I * idTo s J) ∧ idTo s 1 = 1 ∧ (∀ y : X.E, idTo s (Submodule.span (𝓞 X.E) {y}) = Submodule.span (𝓞 D.host.E) {s.iE y}) ∧ (∀ 𝔞 : TaylorLogMetric.IdE D, ∃ I, idTo s I = 𝔞) ∧ ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = idTo s (detLat N) := by
  intro D X s
  refine ⟨fun I x => mem_trI s.iE I x, fun I J => trI_mul s.iE I J, trI_one s.iE,
    fun y => trI_singleton s.iE y, trI_surj s.iE, fun n N => ?_⟩
  calc TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)
      = Submodule.span (𝓞 D.host.E) (s.iE '' {x | ∃ A : Matrix (Fin n) (Fin n) X.E,
          (∀ v ∈ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 X.E) X.E)), A.mulVec v ∈ N) ∧
            x = A.det}) := by
        rw [← det_set s.iE N]
        rfl
    _ = idTo s (detLat N) := (trI_span s.iE _).symm

end GlobalTheory.IdealTransport
