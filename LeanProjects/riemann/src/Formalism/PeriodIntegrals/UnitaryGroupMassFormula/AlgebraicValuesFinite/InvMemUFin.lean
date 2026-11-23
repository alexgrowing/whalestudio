import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.ClassSame

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Neutral.B1 Topology

namespace PI.AlgValsFin.W

variable {L : Type} [Field L] [NumberField L]

theorem locNb (v : HeightOneSpectrum (𝓞 L))
    (s : Set ((v.adicCompletionIntegers L : Set (v.adicCompletion L))))
    (hs : s ∈ 𝓝 (⟨1, (v.adicCompletionIntegers L).one_mem⟩ : (v.adicCompletionIntegers L : Set (v.adicCompletion L)))) :
    ∃ n : ℕ, ∀ y : (v.adicCompletionIntegers L : Set (v.adicCompletion L)),
      Valued.v ((y : v.adicCompletion L) - 1) ≤ exp (-(n : ℤ)) → y ∈ s := by
  rw [mem_nhds_subtype] at hs
  obtain ⟨u, hu, hsub⟩ := hs
  rw [Valued.mem_nhds] at hu
  obtain ⟨γ, hγ⟩ := hu
  obtain ⟨n, hn⟩ := exists_exp_neg_natCast_lt (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
  refine ⟨n, fun y hy => hsub (hγ ?_)⟩
  show Valued.v.restrict ((y : v.adicCompletion L) - 1) < γ.1
  rw [← MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.lt_iff_lt, Valuation.embedding_restrict]
  exact lt_of_le_of_lt hy hn

def toInt (x : Ideles L) (hx : x ∈ UFin L) (v : HeightOneSpectrum (𝓞 L)) :
    (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
  ⟨(x : AdeleRing (𝓞 L) L).2 v, (mem_adicCompletionIntegers _ _ _).2 (hx.2 v).le⟩

theorem inv_mem_UFin {x : Ideles L} (hx : x ∈ UFin L) : x⁻¹ ∈ UFin L := by
  have hmul : (x : AdeleRing (𝓞 L) L) * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = 1 := x.mul_inv
  refine ⟨?_, fun v => ?_⟩
  · have h2 : (x : AdeleRing (𝓞 L) L).1 * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 :=
      congrArg (fun y : AdeleRing (𝓞 L) L => y.1) hmul
    rw [hx.1, one_mul] at h2
    exact h2
  · have h2 : (x : AdeleRing (𝓞 L) L).2 v * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) hmul
    have h3 := congrArg Valued.v h2
    rw [map_mul, hx.2 v, one_mul, map_one] at h3
    exact h3

theorem val_inv_sub {x : Ideles L} (hx : x ∈ UFin L) (v : HeightOneSpectrum (𝓞 L)) :
    Valued.v ((x⁻¹ : Ideles L).val.2 v - 1) = Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) := by
  have hmul : (x : AdeleRing (𝓞 L) L) * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = 1 := x.mul_inv
  have h2 : (x : AdeleRing (𝓞 L) L).2 v * ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v = 1 :=
    congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) hmul
  have hz : Valued.v (((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v) = 1 := (inv_mem_UFin hx).2 v
  have heq : (x⁻¹ : Ideles L).val.2 v - 1 =
      ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v * (1 - (x : AdeleRing (𝓞 L) L).2 v) := by
    rw [mul_sub, mul_one, mul_comm (((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v), h2]
  rw [heq, map_mul, hz, one_mul, Valuation.map_sub_swap]

theorem exists_nbhd (W : Set (Ideles L)) (hW : IsOpen W) (h1 : (1 : Ideles L) ∈ W) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), ∀ x ∈ UFin L,
      (∀ v ∈ S, Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) ≤ exp (-(n : ℤ))) → x ∈ W := by
  classical
  obtain ⟨t, ht, rfl⟩ := (Units.isInducing_embedProduct).isOpen_iff.1 hW
  let one' : Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
    fun v => ⟨1, (v.adicCompletionIntegers L).one_mem⟩
  let sm : (Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L))) →
      FiniteAdeleRing (𝓞 L) L :=
    RestrictedProduct.structureMap _ _ Filter.cofinite
  have hsm : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
  let g : (Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L))) ×
      (Π v : HeightOneSpectrum (𝓞 L), (v.adicCompletionIntegers L : Set (v.adicCompletion L))) →
      AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    fun p => (((1 : InfiniteAdeleRing L), sm p.1), MulOpposite.op ((1 : InfiniteAdeleRing L), sm p.2))
  have hg : Continuous g :=
    Continuous.prodMk (Continuous.prodMk continuous_const (hsm.comp continuous_fst))
      (MulOpposite.continuous_op.comp (Continuous.prodMk continuous_const (hsm.comp continuous_snd)))
  have hsm1 : sm one' = 1 := FiniteAdeleRing.ext _ fun v => rfl
  have hg1 : g (one', one') = Units.embedProduct _ (1 : Ideles L) := by
    simp only [g, hsm1]
    rfl
  have hmem : g ⁻¹' t ∈ 𝓝 (one', one') :=
    hg.continuousAt.preimage_mem_nhds (ht.mem_nhds (by rw [hg1]; exact h1))
  rw [nhds_prod_eq] at hmem
  obtain ⟨t1, ht1, t2, ht2, hsub⟩ := Filter.mem_prod_iff.1 hmem
  rw [nhds_pi, Filter.mem_pi] at ht1 ht2
  obtain ⟨I1, hI1, s1, hs1, hsub1⟩ := ht1
  obtain ⟨I2, hI2, s2, hs2, hsub2⟩ := ht2
  choose n1 hn1 using fun v => locNb v (s1 v) (hs1 v)
  choose n2 hn2 using fun v => locNb v (s2 v) (hs2 v)
  let S : Finset (HeightOneSpectrum (𝓞 L)) := hI1.toFinset ∪ hI2.toFinset
  refine ⟨S, ∑ v ∈ S, (n1 v + n2 v), fun x hx hS => ?_⟩
  have hle : ∀ v ∈ S, ∀ k : ℕ, k ≤ n1 v + n2 v →
      exp (-((∑ v ∈ S, (n1 v + n2 v) : ℕ) : ℤ)) ≤ exp (-(k : ℤ)) := by
    intro v hv k hk
    apply exp_le_exp.2
    have := Finset.single_le_sum (f := fun v => n1 v + n2 v) (fun _ _ => Nat.zero_le _) hv
    omega
  have hy : (fun v => toInt x hx v, fun v => toInt x⁻¹ (inv_mem_UFin hx) v) ∈ t1 ×ˢ t2 := by
    refine ⟨hsub1 fun v hv => hn1 v _ ?_, hsub2 fun v hv => hn2 v _ ?_⟩
    · have hvS : v ∈ S := Finset.mem_union_left _ (hI1.mem_toFinset.2 hv)
      exact (hS v hvS).trans (hle v hvS _ (Nat.le_add_right _ _))
    · have hvS : v ∈ S := Finset.mem_union_right _ (hI2.mem_toFinset.2 hv)
      show Valued.v ((x⁻¹ : Ideles L).val.2 v - 1) ≤ _
      rw [val_inv_sub hx v]
      exact (hS v hvS).trans (hle v hvS _ (Nat.le_add_left _ _))
  have hgx : g (fun v => toInt x hx v, fun v => toInt x⁻¹ (inv_mem_UFin hx) v) = Units.embedProduct _ x := by
    have e1 : (((1 : InfiniteAdeleRing L), sm fun v => toInt x hx v) : AdeleRing (𝓞 L) L) = (x : AdeleRing (𝓞 L) L) :=
      Prod.ext hx.1.symm (FiniteAdeleRing.ext _ fun v => rfl)
    have e2 : (((1 : InfiniteAdeleRing L), sm fun v => toInt x⁻¹ (inv_mem_UFin hx) v) : AdeleRing (𝓞 L) L) =
        ((x⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) :=
      Prod.ext (inv_mem_UFin hx).1.symm (FiniteAdeleRing.ext _ fun v => rfl)
    simp only [g]
    rw [e1, e2]
    rfl
  have := hsub hy
  rw [Set.mem_preimage, hgx] at this
  exact this

end PI.AlgValsFin.W
