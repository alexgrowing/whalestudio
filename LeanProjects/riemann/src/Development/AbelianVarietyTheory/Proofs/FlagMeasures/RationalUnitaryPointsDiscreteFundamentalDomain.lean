import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology

open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open Matrix Topology Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RatDiscrete

theorem finite_bounded {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) (B : ℝ) :
    {x : n → E | x ∈ Λ ∧ ∀ (τ : E →+* ℂ) i, ‖τ (x i)‖ ≤ B}.Finite := by
  classical
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  have hm' : (m : E) ≠ 0 := Int.cast_ne_zero.2 hm0
  have h1 := (NumberField.Embeddings.finite_of_norm_le E ℂ (‖(m : ℂ)‖ * B)).preimage
    (f := fun a : E => (m : E) * a) (mul_right_injective₀ hm').injOn
  refine (Set.Finite.pi' fun _ : n => h1).subset fun x hx i => ⟨hΛ x hx.1 i, fun τ => ?_⟩
  simp only [map_mul, map_intCast, norm_mul]
  exact mul_le_mul_of_nonneg_left (hx.2 τ i) (norm_nonneg _)

variable (I : AutInst)

theorem exists_place (τ : I.E →+* ℂ) : ∃ v, ∀ a, ‖τ a‖ = ‖I.φ v a‖ := by
  haveI := I.cm.totReal
  let ψ : I.F →+* ℂ := τ.comp (algebraMap I.F I.E)
  have hψ : ComplexEmbedding.IsReal ψ :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk ψ))
  refine ⟨InfinitePlace.mk ψ, fun a => ?_⟩
  obtain ⟨b, hb⟩ := (I.cm.fixed (a * star a)).1 (by rw [star_mul, star_star])
  have h1 : τ (a * star a) = I.φ (InfinitePlace.mk ψ) (a * star a) := by
    rw [← hb, I.φ_over, InfinitePlace.embedding_mk_eq_of_isReal hψ]
    rfl
  have h2 := congrArg norm h1
  simp only [map_mul, I.cm.cmUnram.2.1, norm_mul, Complex.norm_conj] at h2
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h2

def IsImage (γ : Matrix (Fin I.n) (Fin I.n) I.E) (x : I.GA) : Prop :=
  (∀ v, uMat (x.1 v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v) ∧
    I.fmat x.2 = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))

theorem subsingleton_isImage (γ : Matrix (Fin I.n) (Fin I.n) I.E) :
    {x | IsImage I γ x}.Subsingleton := fun _ hx _ hy =>
  Prod.ext (funext fun v => Subtype.ext (Units.ext ((hx.1 v).trans (hy.1 v).symm)))
    (Subtype.ext (Units.ext (hx.2.trans hy.2.symm)))

theorem P_det (v) : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)

theorem isImage_one : IsImage I 1 1 := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (P_det I v)]
    rfl
  · rw [Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

theorem isImage_mul {γ δ x y} (hx : IsImage I γ x) (hy : IsImage I δ y) :
    IsImage I (γ * δ) (x * y) := by
  refine ⟨fun v => ?_, ?_⟩
  · have : uMat ((x * y).1 v) = uMat (x.1 v) * uMat (y.1 v) := rfl
    rw [this, hx.1, hy.1, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v)]
  · have : I.fmat (x * y).2 = I.fmat x.2 * I.fmat y.2 := rfl
    rw [this, hx.2, hy.2, Matrix.map_mul]

theorem isImage_inv {γ : GL (Fin I.n) I.E} {x} (hx : IsImage I γ x) :
    IsImage I (γ⁻¹ : GL (Fin I.n) I.E) x⁻¹ := by
  refine ⟨fun v => ?_, ?_⟩
  · refine Units.inv_eq_of_mul_eq_one_right (u := (x.1 v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) ?_
    have := hx.1 v
    unfold uMat at this
    rw [this]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v)]
    rw [← Matrix.mul_assoc (Matrix.map _ _), ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.nonsing_inv_mul _ (P_det I v)]
  · refine Units.inv_eq_of_mul_eq_one_right (u := (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) ?_
    have := hx.2
    unfold AutInst.fmat at this
    rw [this, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

def ratSub : Subgroup I.GA where
  carrier := I.GFset
  one_mem' := ⟨1, one_mem _, isImage_one I⟩
  mul_mem' := fun ⟨γ, hγ, hx⟩ ⟨δ, hδ, hy⟩ => ⟨γ * δ, mul_mem hγ hδ, isImage_mul I hx hy⟩
  inv_mem' := fun ⟨γ, hγ, hx⟩ => ⟨γ⁻¹, inv_mem hγ, isImage_inv I hx⟩

theorem countable_GFset : I.GFset.Countable := by
  haveI : Countable I.E := Countable.of_equiv _ (Module.finBasis ℚ I.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin I.n) (Fin I.n) I.E) :=
    inferInstanceAs (Countable (Fin I.n → Fin I.n → I.E))
  refine (Set.countable_iUnion fun γ => (subsingleton_isImage I γ).countable).mono ?_
  rintro x ⟨γ, -, hx⟩
  exact Set.mem_iUnion.2 ⟨γ, hx⟩

theorem exists_bound {C : Set I.GA} (hC : IsCompact C) : ∃ B : ℝ, ∀ x ∈ C, ∀ v i j,
    ‖(I.P v * uMat (x.1 v) * (I.P v)⁻¹) i j‖ ≤ B := by
  have hc : Continuous fun x : I.GA => fun v i j => (I.P v * uMat (x.1 v) * (I.P v)⁻¹) i j := by
    refine continuous_pi fun v => ?_
    exact (continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp
      ((continuous_apply v).comp continuous_fst)))).matrix_mul continuous_const
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨B, fun x hx v i j => (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans
    ((norm_le_pi_norm _ v).trans (hB x hx)))⟩

theorem finite_coset (g : I.Gf) (B : ℝ) :
    {γ : Matrix (Fin I.n) (Fin I.n) I.E | (∀ v i j, ‖I.φ v (γ i j)‖ ≤ B) ∧
      ∃ y : I.Gf, g⁻¹ * y ∈ I.Kset ∧ I.fmat y = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))}.Finite := by
  classical
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  obtain ⟨c, hc0, hlow⟩ := Formalism.UG.P.adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨d, hd0, hup⟩ := Formalism.UG.P.adelstabL_upper (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)
  rw [← hL] at hlow hup
  set G : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := g.1 with hGdef
  obtain ⟨e, he, s, hs, hsg, -⟩ := Formalism.UG.P.levelaf_exists_denom (E := I.E) G
  have hfin := Formalism.UG.P.adelstab_finite G I.Lf d e hd0 he hup (Formalism.UG.P.adelstab_entries G e s hs hsg)
  set u : I.E := algebraMap (𝓞 I.F) I.E c with hu
  have hu0 : u ≠ 0 := Formalism.UG.P.adelstab_algebraMap_ne_zero c hc0
  obtain ⟨Bu, hBu⟩ : ∃ Bu : ℝ, ∀ τ : I.E →+* ℂ, ‖τ u‖ ≤ Bu :=
    ⟨_, fun τ => Finite.le_ciSup (fun τ : I.E →+* ℂ => ‖τ u‖) τ⟩
  have h1 := (Set.Finite.pi' fun _ : Fin I.n => finite_bounded _ hfin (Bu * B)).preimage
    (f := fun (γ : Matrix (Fin I.n) (Fin I.n) I.E) j i => u * γ i j) (by
      intro a _ b _ h
      ext i j
      exact mul_left_cancel₀ hu0 (congrFun (congrFun h j) i))
  refine h1.subset ?_
  rintro γ ⟨hb, y, hy, hγ⟩ j
  refine ⟨?_, fun τ i => ?_⟩
  · have hs : (Pi.single j (Formalism.UG.P.levelafC I.E c) : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ I.Lf := by
      convert hlow (Pi.single j 1) fun i => ?_ using 1
      · funext i
        by_cases h : i = j <;> simp [h]
      · rw [Pi.single_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
    have h2 := (hy _).1 hs
    rw [Formalism.UG.P.adelstab_mem_iff]
    convert h2 using 1
    change _ = (((G⁻¹ : GL _ _) : Matrix _ _ _) * I.fmat y) *ᵥ _
    rw [← Matrix.mulVec_mulVec, hγ]
    congr 1
    funext i
    simp [hu, Formalism.UG.P.adelstab_incl_C, mul_comm]
  · obtain ⟨v, hv⟩ := exists_place I τ
    simp only [map_mul, norm_mul]
    rw [hv (γ i j)]
    exact mul_le_mul (hBu τ) (hb v i j) (norm_nonneg _) ((norm_nonneg _).trans (hBu τ))

theorem finite_inter {C : Set I.GA} (hC : IsCompact C) : (C ∩ I.GFset).Finite := by
  obtain ⟨-, -, -, -, hKo, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨B, hB⟩ := exists_bound I hC
  obtain ⟨t, -, ht⟩ := (hC.image continuous_snd).elim_nhds_subcover
    (fun g => {y | g⁻¹ * y ∈ I.Kset}) fun g _ =>
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by
        show g⁻¹ * g ∈ I.Kset
        rw [inv_mul_cancel, ← hK]
        exact K.one_mem)
  refine ((t.finite_toSet.biUnion fun g _ => finite_coset I g B).biUnion
    fun γ _ => (subsingleton_isImage I γ).finite).subset ?_
  rintro x ⟨hx, γ, -, hγ⟩
  obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 (ht ⟨x, hx, rfl⟩)
  refine Set.mem_iUnion₂.2 ⟨γ, Set.mem_iUnion₂.2 ⟨g, hg, fun v i j => ?_, x.2, hgx, hγ.2⟩, hγ⟩
  have := hB x hx v i j
  rw [hγ.1 v] at this
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v),
    Matrix.mul_nonsing_inv _ (P_det I v), Matrix.mul_one, Matrix.map_apply] using this

theorem isFundamentalDomain (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (h : I.IsFundDom (I.muA μf) fund) : IsFundamentalDomain (ratSub I) fund (I.muA μf) := by
  refine IsFundamentalDomain.mk'' h.1.nullMeasurableSet (ae_of_all _ fun y => ?_) (fun γ hγ => ?_)
    fun γ => ((measurePreserving_mul_left (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) (γ : I.GA).1).prod
      (measurePreserving_mul_left μf (γ : I.GA).2)).quasiMeasurePreserving
  · obtain ⟨γ, hγ, hy⟩ := h.2.1 y
    exact ⟨⟨γ, hγ⟩, hy⟩
  · exact h.2.2 γ γ.2 fun e => hγ (Subtype.ext e)

theorem rational_points : ∀ I : AutInst, ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ Countable Γ ∧ (∀ C : Set I.GA, IsCompact C → (C ∩ I.GFset).Finite) ∧ ∀ (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → IsFundamentalDomain Γ fund (I.muA μf) :=
  fun I => ⟨ratSub I, rfl, (countable_GFset I).to_subtype, fun _ hC => finite_inter I hC,
    fun μf _ _ fund h => isFundamentalDomain I μf fund h⟩

end GlobalTheory.RatDiscrete
