import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CosetRepresentativeTraceFixedProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumMulCosetRepresentativeTraceEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostPurityOfNormalFiniteIndexSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataTowerUnionAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionInvariantRealValuationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemInertiaInvariantsCyclotomicAlgebraIffStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxRootFixedFieldInertiaCyclotomicKernelStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.TrCyc

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem orbit_finite [Algebra.IsAlgebraic ℚ Ω] (H : Subgroup (G ℚ Ω)) (s : Ω) :
    (MulAction.orbit H s).Finite := by
  classical
  obtain ⟨P, hP0, hPs⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s)
  have hQ : P.map (algebraMap ℚ Ω) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ Ω).injective).2 hP0
  refine (P.map (algebraMap ℚ Ω)).roots.toFinset.finite_toSet.subset ?_
  rintro _ ⟨g, rfl⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hQ, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  show Polynomial.aeval ((g : G ℚ Ω) s) P = 0
  rw [Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  simp [hPs]

theorem fix_top (H : Subgroup (G ℚ Ω)) : Fix Ω (⊤ : Subgroup H) = Fix Ω H := by
  ext x
  constructor
  · intro hx g
    exact hx ⟨g, Subgroup.mem_top g⟩
  · intro hx g
    exact hx g.1

def fixSub {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (V : Subgroup (ineCyc l A)) :
    Subalgebra (fixA A) A where
  carrier := {s | ∀ g : V, g • (s : Ω) = s}
  mul_mem' {x y} hx hy g := by
    show g • ((x : Ω) * (y : Ω)) = (x : Ω) * (y : Ω)
    rw [smul_mul', hx g, hy g]
  add_mem' {x y} hx hy g := by
    show g • ((x : Ω) + (y : Ω)) = (x : Ω) + (y : Ω)
    rw [smul_add, hx g, hy g]
  algebraMap_mem' r g := r.2 ((g : ineCyc l A) : G ℚ Ω) (g : ineCyc l A).2.1

theorem exists_trData_cycAlg : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ F : Finset A, ∃ (C : Subalgebra (fixA A) A) (tr : A → A) (n : ℕ) (a b : Fin n → A), (↑F : Set A) ⊆ C ∧ IsTrData (cycAlg l A) C tr a b (l : A) := by
  intro l _ hl2 Ω _ _ _ A hA F
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hpcoe : ((l : A) : Ω) = l := map_natCast A.subtype l
  obtain ⟨v, hvint, hvinv, hp0, hp1⟩ := GlobalTheory.T.exists_decomposition_invariant_real_valuation l Ω A hA
  have hint := GlobalTheory.T.mem_inertiaInvariantsCyclotomicAlgebra_iff l Ω A hA
  have hR := GlobalTheory.T.approxRoot_fixedField_inertiaCyclotomicKernel l hl2 Ω A hA v hvint hp0 hp1
  have hvinv' : ∀ (g : ineCyc l A) (x : Ω), v (g • x) = v x :=
    fun g x => hvinv g (Ine_le_Dec A g.2.1) x
  have hfixB : ∀ s ∈ cycAlg l A, ∀ g : ineCyc l A, g • (s : Ω) = s :=
    fun s hs g => (hint s).1 hs g g.2
  obtain ⟨U, hUn, hUfin, hUfix, hUfaith⟩ := exists_normal_finiteIndex_fixing Ω (ineCyc l A)
    (F.image Subtype.val) (fun s _ => orbit_finite _ s)
  have hl0 : (l : Ω) ≠ 0 := by
    intro h; rw [h, map_zero] at hp0; exact lt_irrefl _ hp0
  haveI : NeZero (l : Ω) := ⟨hl0⟩
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hζA : ζ ∈ A := mem_of_pow_mem A (Fact.out : l.Prime).ne_zero (by rw [hζ.pow_eq_one]; exact A.one_mem)
  have hζB : (⟨ζ, hζA⟩ : A) ∈ cycAlg l A :=
    mem_cycAlg_of_pow (n := 1) (Subtype.ext (by simpa using hζ.pow_eq_one))
  have hUsep : AlmostSep v U :=
    almostSep_of_normal_finiteIndex Ω v l Fact.out hp0 hp1 (ineCyc l A) hvinv' ζ hζ
      (hfixB _ hζB) (by rw [fix_top]; exact hR) U hUn hUfin hUfaith
  obtain ⟨n, a, b, c, hsep, hc⟩ := hUsep (v l) hp1
  haveI := hUfin
  haveI : Fintype (ineCyc l A ⧸ U) := Fintype.ofFinite _
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact (not_lt_zero' hc)
  have hpfix : ∀ (g : ineCyc l A), g • (l : Ω) = l := fun g => by
    change ((g : G ℚ Ω)) (l : Ω) = l
    exact map_natCast _ l
  have hd : (l : Ω) / c ∈ Fix Ω U := div_mem (fun g => hpfix g) hsep.c_mem
  have hdv : v ((l : Ω) / c) ≤ 1 := by
    rw [map_div₀]; exact div_le_one_of_le₀ hc.le (by positivity)
  have hsep' : IsSep v U (fun i => a i * ((l : Ω) / c)) b (l : Ω) := by
    have := TrTower.isSep_mul_right hsep hd hdv (by rw [mul_div_cancel₀ _ hc0]; exact hp1.le)
    rwa [mul_div_cancel₀ _ hc0] at this
  have hsw := TrTower.isSep_swap hsep'
  let a' : Fin n → A := fun i => ⟨_, (hvint _).1 (hsep'.a_le i)⟩
  let b' : Fin n → A := fun i => ⟨_, (hvint _).1 (hsep'.b_le i)⟩
  have htrint : ∀ s : A, cosetTrace U (s : Ω) ∈ A := fun s =>
    sum_mem fun q _ => (hvint _).1 (by rw [hvinv']; exact (hvint _).2 s.2)
  let tr : A → A := fun s => ⟨_, htrint s⟩
  have htr : ∀ s, (tr s : Ω) = cosetTrace U (s : Ω) := fun s => rfl
  have hle : cycAlg l A ≤ fixSub U := fun s hs g => hfixB s hs (g : ineCyc l A)
  have cadd : ∀ x y : A, ((x + y : A) : Ω) = x + y := fun _ _ => rfl
  have cmul : ∀ x y : A, ((x * y : A) : Ω) = x * y := fun _ _ => rfl
  refine ⟨fixSub U, tr, n, a', b', ?_, ?_⟩
  · intro s hs
    exact hUfix _ (Finset.mem_image_of_mem _ hs)
  refine
    { le := hle
      e_mem := Subalgebra.natCast_mem _ l
      a_mem := fun i => hsep'.a_mem i
      b_mem := fun i => hsep'.b_mem i
      tr_mem := ?_
      tr_add := ?_
      tr_mul := ?_
      left := ?_
      right := ?_
      sum := ?_ }
  · intro x hx
    refine (hint _).2 ?_
    intro g hg
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).1 ⟨g, hg⟩
  · intro x _ y _
    apply Subtype.ext
    simp only [htr, cadd, cosetTrace, smul_add, Finset.sum_add_distrib]
  · intro β hβ x hx
    apply Subtype.ext
    simp only [htr, cmul]
    exact (cosetTrace_fixed_props Ω v _ hvinv' U _ hx).2.2 _ (hfixB β hβ)
  · intro x hx
    apply Subtype.ext
    simp only [cmul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact sum_mul_cosetTrace_eq Ω v _ U n _ _ _ hsep' _ hx
  · intro x hx
    apply Subtype.ext
    simp only [cmul, hpcoe, AddSubmonoidClass.coe_finsetSum, htr]
    exact sum_mul_cosetTrace_eq Ω v _ U n _ _ _ hsw _ hx
  · apply Subtype.ext
    simp only [cmul, hpcoe, AddSubmonoidClass.coe_finsetSum]
    simpa using hsep'.sum_in 1 (one_mem _)

end GlobalTheory.RecOne.TrCyc
