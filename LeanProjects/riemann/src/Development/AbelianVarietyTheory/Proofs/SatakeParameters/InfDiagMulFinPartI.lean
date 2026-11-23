import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits

noncomputable section

namespace GlobalTheory.UnUnitCmp.Val

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

def intFin (L : Type) [Field L] [NumberField L] : Subring (FiniteAdeleRing (𝓞 L) L) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers L}
  one_mem' := fun _ => one_mem _
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (intFin L ⧸ Ideal.span {(N : intFin L)}) := by
  let ι : 𝓞 L →+* intFin L :=
    ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap (𝓞 L) L)).codRestrict _
      fun x v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v x
  have : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 L)})
    (Ideal.span {(N : intFin L)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : intFin L)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat L N hN).2 z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : FiniteAdeleRing (𝓞 L) L) - algebraMap L _ (x : L) = ((N : intFin L) : FiniteAdeleRing (𝓞 L) L) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp

theorem finUnit_pow (χ : HChar L) (hχ : χ.IsUnitary) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Ideles L, IsFinIdele u → u ∈ unitIdl L → ((χ.1 u : ℂˣ) : ℂ) ^ m = 1 := by
  let ψ : Ideles L →* Circle :=
    { toFun := fun x => ⟨(χ.1 x : ℂˣ), by simpa [Submonoid.unitSphere] using hχ x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => Subtype.ext (congrArg Units.val (map_mul χ.1 x y)) }
  have hψ : Continuous ψ := (Units.continuous_val.comp χ.2.1).subtype_mk _
  obtain ⟨-, -, -, m, hm, h⟩ := GlobalTheory.CharFin.finite_order_of_small (R := AdeleRing (𝓞 L) L)
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (RingHom.snd _ _) id continuous_id (fun _ => rfl) (intFin L)
    (fun W hW => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele L W hW) finite_quot ψ hψ
  refine ⟨m, hm, fun u h1 h2 => ?_⟩
  have := h u ⟨funext h1, fun v => (h2 v).le, fun v => ((unitIdl L).inv_mem h2 v).le⟩
  exact congrArg (fun z : Circle => (z : ℂ)) this

theorem infDiag_mul_finPartI (k : Lˣ) : infDiag k * finPartI L (diagUnits L k) = diagUnits L k := by
  classical
  have h : ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) = ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem exists_pow_eq (x : Ideles L) (hx : IsFinIdele x) :
    ∃ h : ℕ, 0 < h ∧ ∃ (u : Ideles L) (k : Lˣ), IsFinIdele u ∧ u ∈ unitIdl L ∧ x ^ h * infDiag k = u * diagUnits L k := by
  have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨_, Nat.pos_of_ne_zero this.index_ne_zero, ?_⟩
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (diagUnits L).range).pow_index_mem x)
  have hf : finPartI L x = x := Units.ext (Prod.ext (funext hx).symm rfl)
  refine ⟨finPartI L u, k, fun _ => rfl, hu, ?_⟩
  rw [← hf, ← map_pow, ← e, map_mul, mul_assoc, mul_comm _ (infDiag k), infDiag_mul_finPartI]

theorem exists_pow_mem {I : Type} [Fintype I] (φ : I → L →+* ℂ) (K : Subfield ℂ) (h1 : ∀ i x, φ i x ∈ K)
    (h2 : ∀ i x, starRingEnd ℂ (φ i x) ∈ K) (χ : HChar L) (hχ : χ.IsUnitary) (n : I → ℤ) (hn : χ.HasInf φ n)
    (x : Ideles L) (hx : IsFinIdele x) : ∃ m : ℕ, 0 < m ∧ ((χ.1 x : ℂˣ) : ℂ) ^ m ∈ K := by
  obtain ⟨m, hm, hu⟩ := finUnit_pow χ hχ
  obtain ⟨h, hh, u, k, u1, u2, e⟩ := exists_pow_eq x hx
  have e1 := congrArg χ.1 e
  rw [map_mul, map_mul, map_pow, χ.2.2 k, mul_one, ← eq_mul_inv_iff_mul_eq] at e1
  have hK : ((χ.1 (infDiag k) : ℂˣ) : ℂ) ^ 2 ∈ K := by
    have : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _ := hn k
    rw [this, ← Finset.prod_pow]
    refine prod_mem fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, div_pow, ← Complex.mul_conj']
    exact zpow_mem (div_mem (pow_mem (h1 _ _) _) (mul_mem (h1 _ _) (h2 _ _))) _
  refine ⟨h * (m * 2), by positivity, ?_⟩
  rw [pow_mul, ← Units.val_pow_eq_pow_val (χ.1 x), e1, Units.val_mul, mul_pow, pow_mul, hu u u1 u2, one_pow, one_mul,
    Units.val_inv_eq_inv_val, inv_pow, mul_comm, pow_mul]
  exact inv_mem (pow_mem hK _)

theorem exists_pow_mem_host {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (hχ : χ.IsUnitary)
    (n : R.Psi → ℤ) (hn : χ.HasInf (embPsi H) n) (x : Ideles H.E) (hx : IsFinIdele x) :
    ∃ m : ℕ, 0 < m ∧ ((χ.1 x : ℂˣ) : ℂ) ^ m ∈ H.φ₀.fieldRange := by
  have hcm : IsCMField H.E := H.isCMField_hostE
  refine exists_pow_mem (embPsi H) H.φ₀.fieldRange (fun i y => ⟨H.sigmaOf _ y, rfl⟩) (fun i y => ?_) χ hχ n hn x hx
  exact ⟨IsCMField.complexConj H.E (H.sigmaOf _ y), IsCMField.complexEmbedding_complexConj H.E H.φ₀ _⟩

end GlobalTheory.UnUnitCmp.Val
