import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField Matrix IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.Tau

namespace TraceIntegralityAlt

theorem exists_nat_eq_mul {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c : 𝓞 K, (m : 𝓞 K) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
    omega
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

theorem exists_nat_mul_mem {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : K) * e ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) e
  obtain ⟨m, hm, c, hc⟩ := exists_nat_eq_mul (b : 𝓞 K) (nonZeroDivisors.ne_zero b.2)
  refine ⟨m, hm, a * c, ?_⟩
  have h1 : (m : K) = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K c := by
    rw [← map_mul, ← hc, map_natCast]
  simp only at h
  rw [map_mul, h1, ← h]
  ring

def evalAt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.MainNotions.S.Af F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exists_nat_mul_intAd {F : Type} [Field F] [NumberField F] (t : Formalism.MainNotions.S.Af F) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : Formalism.MainNotions.S.Af F) * t ∈ Formalism.UG.intAd F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | t v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 t.2
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m : ℕ, 1 ≤ m ∧
      (m : v.adicCompletion F) * t v ∈ v.adicCompletionIntegers F := by
    intro v
    obtain ⟨b, hb, hbt⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (t v)
    obtain ⟨m, hm, c, hc⟩ := exists_nat_eq_mul b (nonZeroDivisors.ne_zero hb)
    refine ⟨m, hm, ?_⟩
    have h1 : (m : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) b *
        algebraMap (𝓞 F) (v.adicCompletion F) c := by
      rw [← map_mul, ← hc, map_natCast]
    rw [h1, show algebraMap (𝓞 F) (v.adicCompletion F) b * algebraMap (𝓞 F) (v.adicCompletion F) c * t v
      = t v * algebraMap (𝓞 F) (v.adicCompletion F) b * algebraMap (𝓞 F) (v.adicCompletion F) c by ring]
    exact mul_mem hbt ((HeightOneSpectrum.coe_mem_adicCompletionIntegers (v := v) c))
  choose mv hmv hmt using hloc
  refine ⟨∏ v ∈ hfin.toFinset, mv v, Finset.one_le_prod' fun v _ => hmv v, fun v => ?_⟩
  have hev : ((((∏ w ∈ hfin.toFinset, mv w : ℕ) : Formalism.MainNotions.S.Af F) * t) v) =
      ((∏ w ∈ hfin.toFinset, mv w : ℕ) : v.adicCompletion F) * t v := by
    show evalAt v (((∏ w ∈ hfin.toFinset, mv w : ℕ) : Formalism.MainNotions.S.Af F) * t) = _
    rw [map_mul, map_natCast]
    rfl
  show _ ∈ _
  rw [hev]
  by_cases hv : v ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv]
    push_cast
    have e1 : ((mv v : v.adicCompletion F) * ∏ i ∈ hfin.toFinset.erase v, (mv i : v.adicCompletion F)) *
        t v = (∏ i ∈ hfin.toFinset.erase v, (mv i : v.adicCompletion F)) *
          ((mv v : v.adicCompletion F) * t v) := by ring
    rw [e1]
    exact mul_mem (prod_mem fun w _ => natCast_mem _ _) (hmt v)
  · have ht : t v ∈ v.adicCompletionIntegers F := by simpa using hv
    exact mul_mem (natCast_mem _ _) ht

theorem mem_integers_of_mem_intAd {F : Type} [Field F] [NumberField F] (f : F)
    (h : algebraMap F (Formalism.MainNotions.S.Af F) f ∈ Formalism.UG.intAd F) : f ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F f fun v => ?_
  have hv := h v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  exact hv

theorem uniform_nat_mul {A : Type} [CommRing A] (R : Subring A) {ι : Type} [Fintype ι] (f : ι → A)
    (h : ∀ i, ∃ m : ℕ, 1 ≤ m ∧ (m : A) * f i ∈ R) : ∃ m : ℕ, 1 ≤ m ∧ ∀ i, (m : A) * f i ∈ R := by
  classical
  choose m hm hmf using h
  refine ⟨∏ i, m i, Finset.one_le_prod' fun i _ => hm i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  push_cast
  rw [show (m i : A) * (∏ j ∈ Finset.univ.erase i, (m j : A)) * f i =
    (∏ j ∈ Finset.univ.erase i, (m j : A)) * ((m i : A) * f i) by ring]
  exact mul_mem (prod_mem fun j _ => natCast_mem _ _) (hmf i)

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mul_IntAf (a : E ⊗[F] Formalism.MainNotions.S.Af F) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : E ⊗[F] Formalism.MainNotions.S.Af F) * a ∈ Formalism.MainNotions.S.IntAf F E := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨1, le_rfl, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e t =>
    obtain ⟨m₁, hm₁, he⟩ := exists_nat_mul_mem e
    obtain ⟨m₂, hm₂, ht⟩ := exists_nat_mul_intAd t
    refine ⟨m₁ * m₂, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    have hgen1 : ((m₁ : E) * e) ⊗ₜ[F] (1 : Formalism.MainNotions.S.Af F) ∈ Formalism.MainNotions.S.IntAf F E :=
      Subring.subset_closure (Or.inl ⟨⟨_, he⟩, rfl⟩)
    have hgen2 : (1 : E) ⊗ₜ[F] ((m₂ : Formalism.MainNotions.S.Af F) * t) ∈ Formalism.MainNotions.S.IntAf F E :=
      Subring.subset_closure (Or.inr ⟨⟨_, ht⟩, rfl⟩)
    have heq : ((m₁ * m₂ : ℕ) : E ⊗[F] Formalism.MainNotions.S.Af F) * e ⊗ₜ[F] t =
        ((m₁ : E) * e) ⊗ₜ[F] (1 : Formalism.MainNotions.S.Af F) * (1 : E) ⊗ₜ[F] ((m₂ : Formalism.MainNotions.S.Af F) * t) := by
      rw [Nat.cast_mul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.natCast_def,
        Algebra.TensorProduct.natCast_def' (n := m₂), Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp
    rw [heq]
    exact mul_mem hgen1 hgen2
  | add x y hx hy =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hy
    refine ⟨m₁ * m₂, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    rw [show ((m₁ * m₂ : ℕ) : E ⊗[F] Formalism.MainNotions.S.Af F) * (x + y) =
      (m₂ : E ⊗[F] Formalism.MainNotions.S.Af F) * ((m₁ : E ⊗[F] Formalism.MainNotions.S.Af F) * x) +
        (m₁ : E ⊗[F] Formalism.MainNotions.S.Af F) * ((m₂ : E ⊗[F] Formalism.MainNotions.S.Af F) * y) by push_cast; ring]
    exact add_mem (mul_mem (natCast_mem _ _) h₁) (mul_mem (natCast_mem _ _) h₂)

variable (F E) in

def trT : E ⊗[F] Formalism.MainNotions.S.Af F →ₗ[F] Formalism.MainNotions.S.Af F :=
  TensorProduct.lift ((LinearMap.lsmul F (Formalism.MainNotions.S.Af F)).comp (Algebra.trace F E))

theorem trT_tmul (e : E) (t : Formalism.MainNotions.S.Af F) :
    trT F E (e ⊗ₜ[F] t) = algebraMap F (Formalism.MainNotions.S.Af F) (Algebra.trace F E e) * t := by
  simp [trT, Algebra.smul_def]

theorem algebraMap_int_mem_intAd (c : 𝓞 F) :
    algebraMap F (Formalism.MainNotions.S.Af F) (algebraMap (𝓞 F) F c) ∈ Formalism.UG.intAd F := fun v => by
  show algebraMap F (Formalism.MainNotions.S.Af F) (algebraMap (𝓞 F) F c) v ∈ _
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one c

theorem trT_mem (z : E ⊗[F] Formalism.MainNotions.S.Af F) (hz : z ∈ Formalism.MainNotions.S.IntAf F E) :
    trT F E z ∈ Formalism.UG.intAd F := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let f : 𝓞 E →ₐ[ℤ] E ⊗[F] Formalism.MainNotions.S.Af F :=
    ((Algebra.TensorProduct.includeLeftRingHom).comp (algebraMap (𝓞 E) E)).toIntAlgHom
  let g : Formalism.UG.intAd F →ₐ[ℤ] E ⊗[F] Formalism.MainNotions.S.Af F :=
    ((Algebra.TensorProduct.includeRight (R := F) (A := E) (B := Formalism.MainNotions.S.Af F)).toRingHom.comp
      (Formalism.UG.intAd F).subtype).toIntAlgHom
  let ψ := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have hle : Formalism.MainNotions.S.IntAf F E ≤ ψ.toRingHom.range := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, ⟨o, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)
    · refine ⟨o ⊗ₜ 1, ?_⟩
      show ψ (o ⊗ₜ 1) = _
      rw [Algebra.TensorProduct.lift_tmul]
      show (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : Formalism.MainNotions.S.Af F)) * ((1 : E) ⊗ₜ[F] (((1 : Formalism.UG.intAd F) : Formalism.MainNotions.S.Af F))) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, OneMemClass.coe_one]
    · refine ⟨1 ⊗ₜ y, ?_⟩
      show ψ (1 ⊗ₜ y) = _
      rw [Algebra.TensorProduct.lift_tmul]
      show (algebraMap (𝓞 E) E 1 ⊗ₜ[F] (1 : Formalism.MainNotions.S.Af F)) * ((1 : E) ⊗ₜ[F] ((y : Formalism.MainNotions.S.Af F))) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, map_one]
  obtain ⟨w, rfl⟩ := hle hz
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o y =>
    have h1 : ψ.toRingHom (o ⊗ₜ y) = (algebraMap (𝓞 E) E o) ⊗ₜ[F] (y : Formalism.MainNotions.S.Af F) := by
      show ψ (o ⊗ₜ y) = _
      rw [Algebra.TensorProduct.lift_tmul]
      show (algebraMap (𝓞 E) E o ⊗ₜ[F] (1 : Formalism.MainNotions.S.Af F)) * ((1 : E) ⊗ₜ[F] ((y : Formalism.MainNotions.S.Af F))) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h1, trT_tmul]
    have hint : IsIntegral ℤ (Algebra.trace F E (algebraMap (𝓞 E) E o)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
    obtain ⟨c, hc⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 F).1 hint
    rw [← hc]
    exact mul_mem (algebraMap_int_mem_intAd c) y.2
  | add x y hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy

theorem mem_OE_of_inclE_mem (e : E) (he : Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) e ∈ Formalism.MainNotions.S.IntAf F E) :
    e ∈ (algebraMap (𝓞 E) E).range := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let S : Subring E := (Formalism.MainNotions.S.IntAf F E).comap (Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F))
  have hOE : ∀ o : 𝓞 E, algebraMap (𝓞 E) E o ∈ S := fun o =>
    Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)
  have htrF : ∀ z ∈ S, Algebra.trace F E z ∈ (algebraMap (𝓞 F) F).range := by
    intro z hz
    refine mem_integers_of_mem_intAd _ ?_
    have h1 := trT_mem _ hz
    have h2 : Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) z = z ⊗ₜ[F] (1 : Formalism.MainNotions.S.Af F) := rfl
    rwa [h2, trT_tmul, mul_one] at h1
  have htrQ : ∀ z ∈ S, ∃ k : ℤ, Algebra.trace ℚ E z = k := by
    intro z hz
    obtain ⟨c, hc⟩ := htrF z hz
    rw [← Algebra.trace_trace (S := F), ← hc]
    have hint : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F c)) :=
      Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe c)
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact ⟨k, by rw [← hk]; simp⟩
  let b := NumberField.integralBasis E
  have hB : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  let bd := (Algebra.traceForm ℚ E).dualBasis hB b
  have hSN : ∀ z ∈ S, z ∈ Submodule.span ℤ (Set.range bd) := by
    intro z hz
    rw [← bd.sum_repr z]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    obtain ⟨k, hk⟩ := htrQ (z * b i) (S.mul_mem hz (by rw [integralBasis_apply]; exact hOE _))
    rw [hk, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let SA : Subalgebra ℤ E :=
    { S with algebraMap_mem' := fun k => by rw [algebraMap_int_eq, eq_intCast]; exact intCast_mem S k }
  have hfg : (Subalgebra.toSubmodule SA).FG :=
    (Submodule.fg_span (Set.finite_range bd)).of_le fun z hz => hSN z hz
  have hint : IsIntegral ℤ e := IsIntegral.of_mem_of_fg SA hfg e he
  obtain ⟨y, hy⟩ := IsIntegralClosure.isIntegral_iff (A := 𝓞 E).1 hint
  exact ⟨y, hy⟩

end Tens

theorem uniform_nat {ι : Type} [Fintype ι] (P : ι → ℕ → Prop) (hP : ∀ i m k, P i m → P i (k * m))
    (h : ∀ i, ∃ m : ℕ, 1 ≤ m ∧ P i m) : ∃ m : ℕ, 1 ≤ m ∧ ∀ i, P i m := by
  classical
  choose m hm hmP using h
  refine ⟨∏ i, m i, Finset.one_le_prod' fun i _ => hm i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP i _ _ (hmP i)

section Lat

variable (I : Formalism.MainNotions.S.AutInst)

theorem natCast_smul_mem (k : ℕ) {l : Fin I.n → I.E} (hl : l ∈ I.L) : (k : I.E) • l ∈ I.L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact I.L.nsmul_mem hl k

theorem inclE_int_mem (o : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (algebraMap (𝓞 I.E) I.E o) ∈ Formalism.MainNotions.S.IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, o, rfl⟩, rfl⟩)

theorem Lf_upper : ∃ d : ℕ, 1 ≤ d ∧ ∀ y ∈ I.Lf, ∀ i,
    (d : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y i ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
  obtain ⟨s, hs⟩ := I.L_fg
  obtain ⟨d, hd, hds⟩ := uniform_nat (fun (p : s × Fin I.n) (d : ℕ) =>
      (d : I.E) * (p.1 : Fin I.n → I.E) p.2 ∈ (algebraMap (𝓞 I.E) I.E).range)
    (fun p m k hp => by
      rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) hp)
    (fun p => exists_nat_mul_mem _)
  have hL : ∀ l ∈ I.L, ∀ i, (d : I.E) * l i ∈ (algebraMap (𝓞 I.E) I.E).range := by
    intro l hl
    rw [← hs] at hl
    induction hl using Submodule.span_induction with
    | mem v hv => exact fun i => hds (⟨v, hv⟩, i)
    | zero => intro i; rw [Pi.zero_apply, mul_zero]; exact zero_mem _
    | add v w _ _ hv hw => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hv i) (hw i)
    | smul a v _ hv =>
      intro i
      rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
      exact mul_mem ⟨a, rfl⟩ (hv i)
  refine ⟨d, hd, fun y hy => ?_⟩
  have hy' : y ∈ Submodule.span (Formalism.MainNotions.S.IntAf I.F I.E)
      (Set.range fun x : I.L => fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((x : Fin I.n → I.E) i)) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hv
    intro i
    obtain ⟨o, ho⟩ := hL l hl i
    rw [← map_natCast (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) d, ← map_mul, ← ho]
    exact inclE_int_mem I o
  | zero => intro i; rw [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add v w _ _ hv hw => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hv i) (hw i)
  | smul a v _ hv =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem a.2 (hv i)

theorem exists_nat_smul_mem_L (v : Fin I.n → I.E) : ∃ d : ℕ, 1 ≤ d ∧ (d : I.E) • v ∈ I.L := by
  have hv : v ∈ Submodule.span I.E (I.L : Set (Fin I.n → I.E)) := by rw [I.L_span]; trivial
  induction hv using Submodule.span_induction with
  | mem w hw => exact ⟨1, le_rfl, by rw [Nat.cast_one, one_smul]; exact hw⟩
  | zero => exact ⟨1, le_rfl, by rw [smul_zero]; exact zero_mem _⟩
  | add w w' _ _ hw hw' =>
    obtain ⟨d₁, hd₁, h₁⟩ := hw
    obtain ⟨d₂, hd₂, h₂⟩ := hw'
    refine ⟨d₂ * d₁, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    rw [smul_add, Nat.cast_mul, mul_smul, mul_comm, mul_smul]
    exact add_mem (natCast_smul_mem I _ h₁) (natCast_smul_mem I _ h₂)
  | smul c w _ hw =>
    obtain ⟨d, hd, h⟩ := hw
    obtain ⟨d', hd', a, ha⟩ := exists_nat_mul_mem c
    refine ⟨d' * d, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    have : ((d' * d : ℕ) : I.E) • (c • w) = (algebraMap (𝓞 I.E) I.E a) • ((d : I.E) • w) := by
      rw [ha, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    rw [this, algebraMap_smul]
    exact I.L.smul_mem a h

theorem Lf_lower : ∃ d : ℕ, 1 ≤ d ∧ ∀ y : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F,
    (∀ i, y i ∈ Formalism.MainNotions.S.IntAf I.F I.E) → (d : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • y ∈ I.Lf := by
  classical
  obtain ⟨d, hd, hdi⟩ := uniform_nat (fun (i : Fin I.n) (d : ℕ) =>
      (d : I.E) • (Pi.single i 1 : Fin I.n → I.E) ∈ I.L)
    (fun i m k hp => by rw [Nat.cast_mul, mul_smul]; exact natCast_smul_mem I k hp)
    (fun i => exists_nat_smul_mem_L I _)
  refine ⟨d, hd, fun y hy => ?_⟩
  have heq : (d : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • y = ∑ i, (⟨y i, hy i⟩ : Formalism.MainNotions.S.IntAf I.F I.E) •
      (fun k => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
        (((d : I.E) • (Pi.single i 1 : Fin I.n → I.E)) k)) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Subring.smul_def, Pi.single_apply,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, mul_zero])
      (fun h => absurd (Finset.mem_univ k) h), if_pos rfl, map_natCast, mul_comm]
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨_, hdi i⟩, rfl⟩)

theorem Lf_mat {d₁ d₂ : ℕ}
    (H₁ : ∀ y ∈ I.Lf, ∀ i, (d₁ : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y i ∈ Formalism.MainNotions.S.IntAf I.F I.E)
    (H₂ : ∀ y : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F,
      (∀ i, y i ∈ Formalism.MainNotions.S.IntAf I.F I.E) → (d₂ : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • y ∈ I.Lf)
    (m : ℕ) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
    (hM : ∀ i j, (m : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * M i j ∈ Formalism.MainNotions.S.IntAf I.F I.E)
    (y : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (hy : y ∈ I.Lf) :
    ((m * d₁ * d₂ : ℕ) : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (M *ᵥ y) ∈ I.Lf := by
  have hw := H₂ (fun i => ∑ j, ((m : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * M i j) *
      ((d₁ : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y j))
    (fun i => sum_mem fun j _ => mul_mem (hM i j) (H₁ y hy j))
  convert hw using 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem mem_L_of_inclE_mem (u : Fin I.n → I.E)
    (hu : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf) : u ∈ I.L := by
  rw [I.L_dual]
  intro y hy
  let ι := Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (E := I.E)
  let Φ : (Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := fun w =>
    ∑ i, ∑ j, ι (starRingEnd I.E (y i)) * ι (I.J i j) * w j
  have hΦ : ∀ w ∈ I.Lf, Φ w ∈ Formalism.MainNotions.S.IntAf I.F I.E := by
    intro w hw
    have hw' : w ∈ Submodule.span (Formalism.MainNotions.S.IntAf I.F I.E)
        (Set.range fun x : I.L => fun i => ι ((x : Fin I.n → I.E) i)) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨l, hl⟩, rfl⟩ := hv
      obtain ⟨o, ho⟩ := (I.L_dual l).1 hl y hy
      have : Φ (fun i => ι (l i)) = ι (Formalism.UG.hform (starRingEnd I.E) I.J y l) := by
        simp only [Φ, Formalism.UG.hform, map_sum, map_mul]
      rw [this, ← ho]
      exact inclE_int_mem I o
    | zero => simp [Φ]
    | add v w _ _ hv hw =>
      have : Φ (v + w) = Φ v + Φ w := by
        simp only [Φ, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [this]
      exact add_mem hv hw
    | smul a v _ hv =>
      have : Φ (a • v) = (a : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * Φ v := by
        simp only [Φ, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this]
      exact mul_mem a.2 hv
  have h1 := hΦ _ hu
  have : Φ (fun i => ι (u i)) = ι (Formalism.UG.hform (starRingEnd I.E) I.J y u) := by
    simp only [Φ, Formalism.UG.hform, map_sum, map_mul]
  rw [this] at h1
  exact mem_OE_of_inclE_mem _ h1

end Lat

end TraceIntegralityAlt

open TraceIntegralityAlt in

theorem t0 : LatticeCommensurable := by
  intro I x
  obtain ⟨d₁, hd₁, H₁⟩ := Lf_upper I
  obtain ⟨d₂, hd₂, H₂⟩ := Lf_lower I
  obtain ⟨m, hm, Hm⟩ := uniform_nat_mul (Formalism.MainNotions.S.IntAf I.F I.E)
    (fun p : Bool × Fin I.n × Fin I.n => if p.1 then I.fmat x.2 p.2.1 p.2.2 else I.fmat x.2⁻¹ p.2.1 p.2.2)
    (fun p => exists_nat_mul_IntAf _)
  have hg : ∀ i j, (m : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * I.fmat x.2 i j ∈ Formalism.MainNotions.S.IntAf I.F I.E :=
    fun i j => by simpa using Hm (true, i, j)
  have hh : ∀ i j, (m : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * I.fmat x.2⁻¹ i j ∈ Formalism.MainNotions.S.IntAf I.F I.E :=
    fun i j => by simpa using Hm (false, i, j)
  have hgh : I.fmat x.2 * I.fmat x.2⁻¹ = 1 := by simp [Formalism.MainNotions.S.AutInst.fmat]
  have hι : ∀ (k : ℕ) (u : Fin I.n → I.E), (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (((k : I.E) • u) i)) = (k : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) •
        (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) := by
    intro k u
    funext i
    simp [map_mul, map_natCast]
  refine ⟨m * d₁ * d₂, Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega)), ?_, ?_⟩
  · intro u hu
    have hu' : I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf := hu
    have h1 := Lf_mat I H₁ H₂ m (I.fmat x.2) hg _ hu'
    rw [Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec, ← hι] at h1
    exact mem_L_of_inclE_mem I _ h1
  · intro u hu
    show I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((((m * d₁ * d₂ : ℕ) : I.E) • u) i)) ∈ I.Lf
    rw [hι, Matrix.mulVec_smul]
    exact Lf_mat I H₁ H₂ m (I.fmat x.2⁻¹) hh _ (Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩)

end Formalism.L2.SG.Pf.Tau
