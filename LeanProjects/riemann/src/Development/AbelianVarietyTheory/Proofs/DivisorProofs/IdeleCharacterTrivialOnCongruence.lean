import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.HeckeSignLevel

theorem sign_char_trivial_on_congruence : ∀ (F : Type) [Field F] [NumberField F] (φ : (AdeleRing (𝓞 F) F)ˣ →* Circle),
    Continuous φ → (∀ b, φ b = 1 ∨ φ b = -1) → (∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → φ b = 1) →
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ∀ b : (AdeleRing (𝓞 F) F)ˣ,
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, (b : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      (∃ t ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 + (n : FiniteAdeleRing (𝓞 F) F) * t) →
      φ b = 1 := by
  intro F _ _ φ hφ hpm hinf
  classical

  have hK : {u : (AdeleRing (𝓞 F) F)ˣ | φ u = 1} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) := by
    have hopen : IsOpen {z : Circle | 0 < (z : ℂ).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
    have h1 : φ ⁻¹' {z : Circle | 0 < (z : ℂ).re} ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) :=
      hφ.continuousAt.preimage_mem_nhds (hopen.mem_nhds (by simp [map_one]))
    refine Filter.mem_of_superset h1 fun u hu => ?_
    rcases hpm u with h | h
    · exact h
    · exfalso
      have : (0 : ℝ) < ((φ u : Circle) : ℂ).re := hu
      rw [h] at this
      norm_num at this
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap] at hK
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hK
  let g : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F →
      AdeleRing (𝓞 F) F × (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    fun p => (((1 : InfiniteAdeleRing F), 1 + p.1), MulOpposite.op ((1 : InfiniteAdeleRing F), 1 + p.2))
  have hg : Continuous g :=
    (continuous_const.prodMk (continuous_const.add continuous_fst)).prodMk
      (MulOpposite.continuous_op.comp (continuous_const.prodMk (continuous_const.add continuous_snd)))
  have hg0 : g (0, 0) = Units.embedProduct _ 1 := by
    rw [map_one]
    simp [g]
    rfl
  have h1 : g ⁻¹' t ∈ 𝓝 ((0, 0) : FiniteAdeleRing (𝓞 F) F × FiniteAdeleRing (𝓞 F) F) :=
    hg.continuousAt.preimage_mem_nhds (by rw [hg0]; exact ht)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨N, hN, hNuv⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F (u ∩ v) (Filter.inter_mem hu hv)
  refine ⟨N, hN, fun n hn hdvd b hb hb' => ?_⟩
  obtain ⟨q, rfl⟩ := hdvd
  obtain ⟨s, hs, hbs⟩ := hb
  obtain ⟨s', hs', hbs'⟩ := hb'

  have hint : ∀ x ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, ∀ w : HeightOneSpectrum (𝓞 F),
      ((q : FiniteAdeleRing (𝓞 F) F) * x) w ∈ w.adicCompletionIntegers F := by
    intro x hx w
    have hxw : x w ∈ w.adicCompletionIntegers F := hx w
    have : ((q : FiniteAdeleRing (𝓞 F) F) * x) w = (q : w.adicCompletion F) * x w := by
      rfl
    rw [this]
    exact mul_mem (natCast_mem _ q) hxw
  have key : ∀ x ∈ HeckeCharacterZeroLocus.ThmBIn.intAf F, (((N * q : ℕ) : FiniteAdeleRing (𝓞 F) F) * x) ∈ u ∩ v := by
    intro x hx
    have e : ((N * q : ℕ) : FiniteAdeleRing (𝓞 F) F) * x = N • ((q : FiniteAdeleRing (𝓞 F) F) * x) := by
      rw [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
    rw [e]
    exact hNuv _ (hint x hx)

  have hinv : (b : AdeleRing (𝓞 F) F).2 * ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
    have h := congrArg Prod.snd b.mul_inv
    exact h
  have hinv' : ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * (b : AdeleRing (𝓞 F) F).2 = 1 := by
    have h := congrArg Prod.snd b.inv_mul
    exact h
  let bf : (AdeleRing (𝓞 F) F)ˣ :=
    { val := ((1 : InfiniteAdeleRing F), (b : AdeleRing (𝓞 F) F).2)
      inv := ((1 : InfiniteAdeleRing F), ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2)
      val_inv := Prod.ext (mul_one _) hinv
      inv_val := Prod.ext (mul_one _) hinv' }
  have hbf : φ bf = 1 := by
    have hmem : Units.embedProduct _ bf ∈ t := by
      have : Units.embedProduct _ bf = g (((N * q : ℕ) : FiniteAdeleRing (𝓞 F) F) * s,
          ((N * q : ℕ) : FiniteAdeleRing (𝓞 F) F) * s') := by
        show (((1 : InfiniteAdeleRing F), (b : AdeleRing (𝓞 F) F).2),
          MulOpposite.op ((1 : InfiniteAdeleRing F), ((b⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2)) = _
        rw [hbs, hbs']
        rfl
      rw [this]
      exact huv ⟨(key s hs).1, (key s' hs').2⟩
    exact hts hmem
  have hrest : φ (b * bf⁻¹) = 1 := by
    apply hinf
    show (b : AdeleRing (𝓞 F) F).2 * ((bf⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1
    exact hinv
  have : b = (b * bf⁻¹) * bf := by group
  rw [this, map_mul, hrest, hbf, one_mul]

end GlobalTheory.HeckeSignLevel
