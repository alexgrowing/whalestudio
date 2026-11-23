import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocallyFiniteOfAlgModCriterion
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingFiniteAdelicGLCompatContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingCommInfEmbAndExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingAdelicNormCompat

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

private theorem st_emb_val {R : Type} [CommRing R] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) R) (i j : Fin a) :
    (emb e g).val (e i) (e j) = g.val i j := by
  rw [coe_emb, Matrix.add_apply, matrixExtendByZero_apply, Matrix.sub_apply]
  simp [Matrix.one_apply]

private theorem st_mem_of_emb {L : Type} [Field L] (O : Subring L) {a n : ℕ} (e : Fin a ↪ Fin n) {h : GL (Fin a) L}
    (hk : emb e h ∈ GLint (Fin n) O) : h ∈ GLint (Fin a) O := by
  obtain ⟨k, hk⟩ := hk
  have hk' : bc O.subtype k⁻¹ = emb e h⁻¹ := by rw [map_inv, hk, map_inv]
  let A : Matrix (Fin a) (Fin a) O := fun i j => k.val (e i) (e j)
  let B : Matrix (Fin a) (Fin a) O := fun i j => (k⁻¹).val (e i) (e j)
  have hA : A.map O.subtype = h.val := by
    ext i j
    rw [← st_emb_val e h, ← hk]
    rfl
  have hB : B.map O.subtype = (h⁻¹).val := by
    ext i j
    rw [← st_emb_val e h⁻¹, ← hk']
    rfl
  have inj : Function.Injective (fun M : Matrix (Fin a) (Fin a) O => M.map O.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hAB : A * B = 1 := inj (by
    change (A * B).map O.subtype = (1 : Matrix (Fin a) (Fin a) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg Units.val (mul_inv_cancel h))
  have hBA : B * A = 1 := inj (by
    change (B * A).map O.subtype = (1 : Matrix (Fin a) (Fin a) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congrArg Units.val (inv_mul_cancel h))
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

variable {R S : Type} [CommRing R] [CommRing S]

private theorem st_corner_sub {a : ℕ} (s : R →ₙ+* S) (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a s g).val - 1) i j = s ((g.val - 1) i j) := by
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j)
    - (1 : Matrix (Fin a) (Fin a) S) i j = s (g.val i j - (1 : Matrix (Fin a) (Fin a) R) i j)
  rw [map_sub]
  ring

private theorem st_corner_emb {a n : ℕ} (e : Fin a ↪ Fin n) (s : R →ₙ+* S) (g : GL (Fin a) R) :
    cornerGL n s (emb e g) = emb e (cornerGL a s g) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [st_corner_sub, coe_emb, coe_emb, add_sub_cancel_left, add_sub_cancel_left]
  by_cases hi : ∃ k, i = e k
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : ∃ l, j = e l
    · obtain ⟨l, rfl⟩ := hj
      rw [matrixExtendByZero_apply, matrixExtendByZero_apply, st_corner_sub]
    · push Not at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ _ hj, matrixExtendByZero_apply_of_outside_col e _ _ hj, map_zero]
  · push Not at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, extendByZero_apply_eq_zero_of_row_not_mem e _ hi, map_zero]

end SlopeTestRemainingChoices

section Main

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm
open PositivityTheory.Rg.BcB.SpectralAccumulation (TypeB)
open UpperTheory.V.Cj.S (res)

variable {E : Type} [Field E] [NumberField E]

private theorem st_emb_fin {a n : ℕ} (e : Fin a ↪ Fin n) (u : GL (Fin a) (Af E)) :
    emb e (finGL E a u) = finGL E n (emb e u) := by
  simp only [finGL, st_corner_emb]

private theorem st_emb_loc {a n : ℕ} (e : Fin a ↪ Fin n) (w) (k : GL (Fin a) (HeightOneSpectrum.adicCompletion E w)) :
    emb e (locGL E a w k) = locGL E n w (emb e k) := by
  simp only [locGL, st_corner_emb]

variable [IsCMField E]

private theorem st_lev {a n : ℕ} (e : Fin a ↪ Fin n) {bad : Set (UpperTheory.V.Cj.S.Pl E)} {K : Subgroup (GL (Fin n) (Af E))}
    (hK : Lev bad K) : Lev bad (K.comap (emb e)) where
  isOpen := hK.isOpen.preimage (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous E a n e).2.2
  int u hu w := by
    have h := hK.int _ hu w
    rw [emb_map] at h
    exact st_mem_of_emb _ e h
  loc w hw k hk := by
    change emb e (locGL E a w k) ∈ K
    rw [st_emb_loc]
    refine hK.loc w hw _ ?_
    obtain ⟨k, rfl⟩ := hk
    exact ⟨emb e k, emb_map e _ k⟩

private theorem st_arch {a n : ℕ} (e : Fin a ↪ Fin n) (k : archCompact E a) : embArch e k.1 ∈ archCompact E n := by
  have h := UpperTheory.blockEmbedding_adelic_norm_compat E a n e _ (Subgroup.mem_comap.1 k.2)
  rw [(UpperTheory.blockEmbedding_comm_infEmb_and_exp E a n e).1] at h
  exact Subgroup.mem_comap.2 h

private noncomputable def stJ {a n : ℕ} (e : Fin a ↪ Fin n) (k : Kinf E a) : Kinf E n :=
  (UpperTheory.V.Cm.cptEq E n).symm ⟨embArch e (UpperTheory.V.Cm.cptEq E a k).1, st_arch e _⟩

private theorem st_emb_inf {a n : ℕ} (e : Fin a ↪ Fin n) (k : Kinf E a) :
    emb e (infGL E a (Unitary.toUnits k)) = infGL E n (Unitary.toUnits (stJ e k)) := by
  rw [← UpperTheory.V.Cm.infEmb_cptEq, ← UpperTheory.V.Cm.infEmb_cptEq, stJ, MulEquiv.apply_symm_apply]
  exact (UpperTheory.blockEmbedding_comm_infEmb_and_exp E a n e).1 _

private theorem st_ct_fin {n r : ℕ} {K : Subgroup (GL (Fin n) (Af E))} {φ : Sm E n}
    (h : ∀ u ∈ K, ∀ g, φ.1 (g * finGL E n u) = φ.1 g) :
    ∀ u ∈ K, ∀ g, constantTerm r φ.1 (g * finGL E n u) = constantTerm r φ.1 g := by
  intro u hu g
  unfold constantTerm
  simp only [← mul_assoc, h u hu]

private theorem st_ct_inf {n r : ℕ} (W : Submodule ℂ (Kinf E n → ℂ)) (hW : FiniteDimensional ℂ W) {φ : Sm E n}
    (hc : Continuous φ.1) (h : ∀ g, (fun k : Kinf E n => φ.1 (g * infGL E n (Unitary.toUnits k))) ∈ W) (g : GA E n) :
    (fun k : Kinf E n => constantTerm r φ.1 (g * infGL E n (Unitary.toUnits k))) ∈ W := by
  refine @UpperTheory.locallyFinite_of_algMod_criterion _ (Kinf E n) (_) _ W hW (fun X k => φ.1 (unipGL X * (g * infGL E n (Unitary.toUnits k)))) (fun X => ?_)
    (fun k => integrableOn_constantTerm hc _)
  simpa only [mul_assoc] using h (unipGL X * g)

private theorem st_slice {a n : ℕ} (e : Fin a ↪ Fin n) {K : Subgroup (GL (Fin n) (Af E))} {W : Submodule ℂ (Kinf E n → ℂ)}
    {Φ : GA E n → ℂ} (h1 : ∀ u ∈ K, ∀ g, Φ (g * finGL E n u) = Φ g)
    (h2 : ∀ g, (fun k : Kinf E n => Φ (g * infGL E n (Unitary.toUnits k))) ∈ W) (f : Sm E a) (g₀ : GA E n)
    (hf : ∀ m, f.1 m = Φ (g₀ * emb e m)) :
    TypeB (K.comap (emb e)) (W.map (LinearMap.funLeft ℂ ℂ (stJ e))) f := by
  refine ⟨fun u hu g => ?_, fun g => ⟨_, h2 (g₀ * emb e g), funext fun k => ?_⟩⟩
  · rw [hf, hf, map_mul, st_emb_fin, ← mul_assoc]
    exact h1 _ hu _
  · simp only [LinearMap.funLeft_apply]
    rw [hf, map_mul, st_emb_inf, mul_assoc]

end Main

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.sliceT :
    SliceT := by
  intro E _ _ _ r s bad K W hL hW
  refine ⟨K.comap (emb (e1 r s)), W.map (LinearMap.funLeft ℂ ℂ (stJ (e1 r s))), K.comap (emb (e2 r s)),
    W.map (LinearMap.funLeft ℂ ℂ (stJ (e2 r s))), st_lev _ hL, Module.Finite.map W _, st_lev _ hL, Module.Finite.map W _,
    fun φ hφ hT => ?_⟩
  have hc : Continuous φ.1 := ((UpperTheory.V.Cm.isAutForm_iff φ).1 hφ).continuous
  have h1 := st_ct_fin (r := r) hT.1
  have h2 := st_ct_inf (r := r) W hW hc hT.2
  refine ⟨fun y f hf => st_slice _ h1 h2 f (emb (e2 r s) y) fun m => ?_,
    fun x f hf => st_slice _ h1 h2 f (emb (e1 r s) x) fun m => ?_⟩
  · rw [hf, ← emb_comm]
    rfl
  · rw [hf]
    rfl
