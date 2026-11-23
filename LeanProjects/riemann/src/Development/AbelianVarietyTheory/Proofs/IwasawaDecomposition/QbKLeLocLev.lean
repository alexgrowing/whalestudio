import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Formalism.LocalToGlobal.Columns.RecLevelTop

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct Topology

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
attribute [local instance] rlt_top rlt_topRing

namespace GlobalTheory.Mem.Col2.TopCh

section Nhd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_nhds (P : HeightOneSpectrum (𝓞 E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ y in 𝓝 (0 : AfE F E), ∃ z ∈ P.adicCompletionIntegers E, adAt F P y = algebraMap E (P.adicCompletion E) c * z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
  have hb0 : algebraMap (𝓞 E) E b ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hb
  have ha0 : algebraMap (𝓞 E) E a ≠ 0 := fun h => hc (by rw [h, zero_div])
  set A : AfE F E := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) with hA
  set B : AfE F E := inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a)⁻¹ with hB
  have hAB : A * B = 1 := by
    rw [hA, hB, ← map_mul, mul_inv_cancel₀ ha0, map_one]
  have hop : IsOpen ((fun y : AfE F E => B * y) ⁻¹' (Formalism.L2.Herm.intAf F E : Set (AfE F E))) :=
    rlt_isOpen_intAf.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : AfE F E) ∈ (fun y : AfE F E => B * y) ⁻¹' (Formalism.L2.Herm.intAf F E : Set (AfE F E)) := by
    simp
  filter_upwards [hop.mem_nhds h0] with y hy
  have hw : ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (afIso F E (B * y) Q) ≤ 1 := (mem_rInt_iff F E (B * y)).1 hy
  have hy' : y = A * (B * y) := by rw [← mul_assoc, hAB, one_mul]
  refine ⟨algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E b) * adAt F P (B * y), ?_, ?_⟩
  · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
    rw [map_mul]
    exact mul_le_one' (by rw [valued_algebraMap]; exact P.valuation_le_one b) (by rw [adAt_apply]; exact hw P)
  · have e : adAt F P y = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a) * adAt F P (B * y) := by
      conv_lhs => rw [hy', map_mul, hA, adAt_inclE]
    rw [e, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hb0]

variable {n : ℕ}

theorem bc_adAt_sub (P : HeightOneSpectrum (𝓞 E)) (w : GL (Fin n) (AfE F E)) (i j : Fin n) :
    ((rhoP F P w : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j -
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j =
    adAt F P ((w : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have e : ((rhoP F P w : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j =
      adAt F P ((w : Matrix (Fin n) (Fin n) (AfE F E)) i j) := rfl
  rw [e, map_sub, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem int_of_sub {P : HeightOneSpectrum (𝓞 E)} {A : Matrix (Fin n) (Fin n) (P.adicCompletion E)}
    (h : ∀ i j, A i j - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) i j ∈ P.adicCompletionIntegers E) : qbInt A := fun i j => by
  have := Subring.add_mem _ (h i j) (qbInt_one (v := P) (F := E) (n := n) i j)
  simpa using this

theorem eventually_localComponent_mem (P : HeightOneSpectrum (𝓞 E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, rhoP F P u ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hval : ∀ (c' : E), c' ≠ 0 → ∀ i j : Fin n, ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, ∃ z ∈ P.adicCompletionIntegers E,
      adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E (P.adicCompletion E) c' * z := by
    intro c' hc' i j
    have hcont : Continuous fun u : GL (Fin n) (AfE F E) =>
        (u : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j :=
      (Units.continuous_val.matrix_elem i j).sub continuous_const
    have ht := hcont.tendsto 1
    simp only [Units.val_one, sub_self] at ht
    exact ht.eventually (adAt_nhds P hc')
  have hinv : ∀ i j : Fin n, ∀ᶠ u : GL (Fin n) (AfE F E) in 𝓝 1, ∃ z ∈ P.adicCompletionIntegers E,
      adAt F P (((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E (P.adicCompletion E) 1 * z := by
    intro i j
    have ht : Filter.Tendsto (fun u : GL (Fin n) (AfE F E) => u⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := GL (Fin n) (AfE F E))).tendsto 1
    exact ht.eventually (hval 1 one_ne_zero i j)
  have h1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hval c hc i j
  have h2 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hval 1 one_ne_zero i j
  have h3 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hinv i j
  filter_upwards [h1, h2, h3] with u a1 a2 a3
  refine ⟨int_of_sub fun i j => ?_, int_of_sub fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨z, hz, e⟩ := a2 i j
    rw [bc_adAt_sub, e, map_one, one_mul]
    exact hz
  · obtain ⟨z, hz, e⟩ := a3 i j
    rw [← map_inv, bc_adAt_sub, e, map_one, one_mul]
    exact hz
  · obtain ⟨z, hz, e⟩ := a1 i j
    exact ⟨z, hz, by rw [Matrix.sub_apply, bc_adAt_sub, e]⟩

theorem rhoT_nhds (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E)) {c : E} (hc : c ≠ 0) :
    ∀ᶠ x : GL (Fin n) (AfE F E) in 𝓝 1, rhoT F P t x ∈ qbK (algebraMap E (P.adicCompletion E) c) := by
  have hcont : Continuous fun x : GL (Fin n) (AfE F E) => t⁻¹ * x * t⁻¹⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have ht := hcont.tendsto 1
  simp only [mul_one, inv_inv, inv_mul_cancel] at ht
  exact ht.eventually (eventually_localComponent_mem P hc)

end Nhd

theorem qbK_le_locLev {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (Θ : LevI E K n P) (d : E) : qbK (algebraMap E (P.adicCompletion E) d) ≤ locLev P Θ d := fun k hk =>
  ⟨hk.1, hk.2.1, 1, Θ.H.one_mem, by simpa using hk⟩

theorem topU_open : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Q : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E), (∀ P, d P ≠ 0) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ U}) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ topU U t Θ d}) := by
  intro F E K _ _ _ _ _ _ _ σ n J Q U t Θ d hd hU
  have hW : ∀ P : Q, IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) |
      (x : GL (Fin n) (AfE F E)) ∈ (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)} := by
    intro P
    let W : Subgroup (UPts σ J (FiniteAdeleRing (𝓞 F) F)) :=
      ((locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))
    have hn : (W : Set (UPts σ J (FiniteAdeleRing (𝓞 F) F))) ∈ 𝓝 (1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) := by
      have ht : Filter.Tendsto (fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => (x : GL (Fin n) (AfE F E))) (𝓝 1) (𝓝 1) :=
        continuous_subtype_val.tendsto 1
      filter_upwards [ht.eventually (rhoT_nhds P.1 t (hd P))] with x hx
      exact qbK_le_locLev P.1 (Θ P) (d P) hx
    exact Subgroup.isOpen_of_mem_nhds W hn
  have e : {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL (Fin n) (AfE F E)) ∈ topU U t Θ d} =
      {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL (Fin n) (AfE F E)) ∈ U} ∩
        ⋂ P : Q, {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) |
          (x : GL (Fin n) (AfE F E)) ∈ (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)} := by
    ext x
    simp only [topU, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact hU.inter (isOpen_iInter_of_finite hW)

end GlobalTheory.Mem.Col2.TopCh

end
