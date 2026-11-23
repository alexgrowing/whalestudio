import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RefCharValues

theorem exists_finset_of_ker {G C : Type} [CommGroup G] [Group C] [Finite C] (f : G →* ℂ) (cl : G →* C)
    (S₀ : Finset ℂ) (h₀ : ∀ z ∈ S₀, IsAlgebraic ℚ z)
    (hk : ∀ F : Subfield ℂ, (∀ z ∈ S₀, z ∈ F) → ∀ x, cl x = 1 → f x ∈ F) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) → ∀ x, f x ∈ F := by
  classical
  haveI := Fintype.ofFinite C
  let r : C → G := Function.invFun cl
  refine ⟨S₀ ∪ Finset.univ.image fun c => f (r c), fun z hz => ?_, fun F hF x => ?_⟩
  · rcases Finset.mem_union.1 hz with h | h
    · exact h₀ z h
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h
      have h1 := hk (algebraicClosure ℚ ℂ).toSubfield (fun z hz => mem_algebraicClosure_iff.2 (h₀ z hz))
        (r c ^ Nat.card C) (by rw [map_pow, pow_card_eq_one'])
      rw [map_pow] at h1
      exact IsAlgebraic.of_pow Nat.card_pos (mem_algebraicClosure_iff.1 h1)
  · have h1 : cl (r (cl x)) = cl x := Function.invFun_eq ⟨x, rfl⟩
    have h2 := hk F (fun z hz => hF z (Finset.mem_union_left _ hz)) (x * (r (cl x))⁻¹)
      (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    have h3 : f (r (cl x)) ∈ F :=
      hF _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩))
    have h4 := mul_mem h2 h3
    rwa [← map_mul, inv_mul_cancel_right] at h4

theorem exists_finset_emb (E : Type) [Field E] [NumberField E] :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) →
      ∀ (φ : E →+* ℂ) (x : E), φ x ∈ F := by
  classical
  let b := Module.finBasis ℚ E
  refine ⟨Finset.univ.image fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2), fun z hz => ?_,
    fun F hF φ x => ?_⟩
  · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b p.2)).algHom p.1.toRatAlgHom
  · rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def]
    exact mul_mem (SubfieldClass.ratCast_mem F _) (hF _ (Finset.mem_image.2 ⟨(φ, i), Finset.mem_univ _, rfl⟩))

theorem exists_principal (L : Type) [Field L] [NumberField L] (a : (FiniteAdeleRing (𝓞 L) L)ˣ)
    (h1 : ClassGroup.mk L ((GlobalTheory.Mem.UnitIndex.idealHom L).toHomUnits a) = 1) : ∃ e : Lˣ, ∀ v, Valued.v
      ((a * (FiniteAdeleRing.unitEmbedding (𝓞 L) L e)⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ).1 v) = 1 := by
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf a = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  refine ⟨Units.mk0 x hx0, (GlobalTheory.Idele.smul_eq_self_iff (R := 𝓞 L) (K := L) _ (I := 1) one_ne_zero).1 ?_⟩
  rw [GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, GlobalTheory.Idele.idealOf_unitEmbedding, hx']
  exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)

theorem exists_class (D : D7) : ∃ cl : (AE D)ˣ →* ClassGroup (𝓞 D.host.E), ∀ x, cl x = 1 → ∃ e : D.host.Eˣ,
    finPart D ((x * (Units.map (incA D).toMonoidHom e)⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧
    finPart D (((x * (Units.map (incA D).toMonoidHom e)⁻¹)⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  let φ : (AE D)ˣ →* (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom
  refine ⟨(ClassGroup.mk D.host.E).comp ((GlobalTheory.Mem.UnitIndex.idealHom D.host.E).toHomUnits.comp φ), fun x hx => ?_⟩
  obtain ⟨e, he⟩ := exists_principal D.host.E (φ x) hx
  have hφ : φ (Units.map (incA D).toMonoidHom e) = FiniteAdeleRing.unitEmbedding (𝓞 D.host.E) D.host.E e :=
    Units.ext (h1 e)
  rw [← hφ, ← map_inv, ← map_mul] at he
  refine ⟨e, ?_⟩
  generalize x * (Units.map (incA D).toMonoidHom e)⁻¹ = u at he
  refine ⟨(h2 _).2 fun P => (he P).le, (h2 _).2 fun P => ?_⟩
  have h3 : (φ u).1 P * (φ u⁻¹).1 P = 1 := by
    have : (φ u).1 * (φ u⁻¹).1 = 1 := by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) this
  have h4 := congrArg Valued.v h3
  rw [map_mul, he P, one_mul, map_one] at h4
  exact h4.le

theorem sign_zpow_even (z : ℂ) (h : z ≠ 0) (k : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * k) = (z / starRingEnd ℂ z) ^ k := by
  rw [zpow_mul]
  congr 1
  have h1 : (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using h
  rw [zpow_ofNat, div_pow, h1]
  field_simp

theorem exists_finset_char (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq c χ)
    {I : Type} [Fintype I] (φ : I → D.host.E →+* ℂ) (k : I → ℤ) (hi : χ.HasInf φ fun i => 2 * k i) :
    ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) →
      ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((c x : Circle) : ℂ) ∈ F := by
  classical
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  obtain ⟨N, -, -, m, hm, hm1⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1.1
  obtain ⟨cl, hcl⟩ := exists_class D
  obtain ⟨S₁, hS₁, hE⟩ := exists_finset_emb D.host.E
  obtain ⟨S, hS, h⟩ := exists_finset_of_ker (Circle.coeHom.comp (c.comp b)) cl
    (S₁ ∪ Polynomial.nthRootsFinset m (1 : ℂ))
    (fun z hz => by
      rcases Finset.mem_union.1 hz with h | h
      · exact hS₁ z h
      · refine IsAlgebraic.of_pow hm ?_
        rw [(Polynomial.mem_nthRootsFinset hm _).1 h]
        exact isAlgebraic_one)
    (fun F hF x hx => by
      obtain ⟨e, he1, he2⟩ := hcl x hx
      have hF1 := hE F fun z hz => hF z (Finset.mem_union_left _ hz)
      let y : (AE D)ˣ := Units.map (incA D).toMonoidHom e
      have hu : FinUnit (b (x * y⁻¹)) := ⟨(hb _).1, by rw [(hb _).2]; exact he1, by rw [← map_inv, (hb _).2]; exact he2⟩
      have h1 : ((c (b (x * y⁻¹)) : Circle) : ℂ) ∈ F :=
        hF _ (Finset.mem_union_right _ ((Polynomial.mem_nthRootsFinset hm _).2 (by
          rw [← Circle.coe_pow, hm1 _ hu, Circle.coe_one])))
      have h2 : ((c (a y) : Circle) : ℂ) ∈ F := by
        rw [GlobalTheory.HeckeInfExp.eq_inf D c χ hc e _ _ (hab _) (hb _).1 (hb _).2, hi e]
        refine prod_mem fun i _ => ?_
        rw [sign_zpow_even _ ((map_ne_zero _).2 e.ne_zero)]
        exact zpow_mem (div_mem (hF1 _ _) (hF1 ((starRingEnd ℂ).comp (φ i)) _)) _
      have h3 : c (a y) * c (b y) = 1 := by rw [← map_mul, ← hab y]; exact hc.1.2 e
      have h4 : c (b x) = c (b (x * y⁻¹)) * (c (a y))⁻¹ := by
        rw [← eq_inv_of_mul_eq_one_right h3, ← map_mul, ← map_mul, inv_mul_cancel_right]
      show ((c (b x) : Circle) : ℂ) ∈ F
      rw [h4, Circle.coe_mul, Circle.coe_inv]
      exact mul_mem h1 (inv_mem h2))
  refine ⟨S, hS, fun F hF x hx => ?_⟩
  have h1 : b x = x := Units.ext (GlobalTheory.PlaceIdem.parts_inj D _ _ ((hb x).1.trans hx.symm) (hb x).2)
  have h2 : ((c (b x) : Circle) : ℂ) ∈ F := h F hF x
  rwa [h1] at h2

theorem exists_finset_values : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) → ∀ (i : Fin D.R.m) (x : (AE D)ˣ), infPart D (x : AE D) = 1 → ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ F := by
  intro D T0 L μ0 hL
  classical
  have key : ∀ i : Fin D.R.m, ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ F : Subfield ℂ, (∀ z ∈ S, z ∈ F) →
      ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) ∈ F := by
    intro i
    obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
    choose z hz using fun g => (D.hc (D.eTau.symm g)).e_int i
    refine exists_finset_char D _ _ (hL.mu0 i) (Formalism.L2.Host.embPsi D.host) (fun g => -z g) ?_
    have : n = fun g => 2 * -z g := funext fun g => by
      have h1 := hn g
      simp only [Formalism.L2.Host.eExp, hz] at h1
      exact_mod_cast h1
    rwa [this] at hi
  choose S hS h using key
  refine ⟨Finset.univ.biUnion S, fun z hz => ?_, fun F hF i => h i F fun z hz => hF z ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hS i z hi
  · exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hz⟩

end GlobalTheory.RefCharValues
