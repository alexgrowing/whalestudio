import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
namespace GlobalTheory.EigLine

theorem finrank_common_eigenspace_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] (O : Subring E), (∀ x : E, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ O) →
    ∀ (L : AddSubgroup E), (∀ a ∈ O, ∀ x ∈ L, a * x ∈ L) →
    ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (P : L →+ W), Submodule.span ℂ (Set.range P) = ⊤ →
      Module.finrank ℂ W = Module.finrank ℚ E →
    ∀ (T : O → Module.End ℂ W), (∀ (a : O) (x y : L), (y : E) = a * x → T a (P x) = P y) →
    ∀ τ : E →+* ℂ, Module.finrank ℂ (⨅ a : O, Module.End.eigenspace (T a) (τ a) : Submodule ℂ W) = 1 := by
  intro E _ _ O hO L hL W _ _ P hspan hdim T hT τ
  have hext : ∀ f g : Module.End ℂ W, (∀ x : L, f (P x) = g (P x)) → f = g := fun f g h =>
    LinearMap.ext_on_range hspan h
  let mulL : O → L → L := fun a x => ⟨(a : E) * x, hL a a.2 x x.2⟩
  have hT' : ∀ (a : O) (x : L), T a (P x) = P (mulL a x) := fun a x => hT a x _ rfl
  let TR : O →+* Module.End ℂ W :=
    { toFun := T
      map_one' := hext _ _ fun x => by
        rw [hT', Module.End.one_apply]; congr 1; ext; simp [mulL]
      map_mul' := fun a b => hext _ _ fun x => by
        rw [Module.End.mul_apply, hT', hT', hT']; congr 1; ext; simp [mulL]; ring
      map_zero' := hext _ _ fun x => by
        rw [hT', LinearMap.zero_apply]; convert P.map_zero; ext; simp [mulL]
      map_add' := fun a b => hext _ _ fun x => by
        rw [LinearMap.add_apply, hT', hT', hT', ← map_add]; congr 1; ext; simp [mulL, add_mul] }

  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨n, hn0, hnO⟩ := hO α
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn0
  set θ : E := (n : E) * α with hθdef
  let θO : O := ⟨θ, hnO⟩
  have hint : IsIntegral ℚ θ := Algebra.IsIntegral.isIntegral θ
  have hθtop : IntermediateField.adjoin ℚ {θ} = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_simple_le_iff]
    have : α = θ / (n : E) := by rw [hθdef]; field_simp
    rw [this]
    exact div_mem (IntermediateField.mem_adjoin_simple_self ℚ θ) (natCast_mem _ n)
  have hadj : Algebra.adjoin ℚ {θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθtop,
      IntermediateField.top_toSubalgebra]
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hpbdim : pb.dim = Module.finrank ℚ E := pb.finrank.symm
  have hpbgen : pb.gen = θ := rfl

  let Zd : Submodule ℤ O := Submodule.span ℤ (Set.range fun k : Fin pb.dim => θO ^ (k : ℕ))
  have hA : ∀ y : E, ∃ N : ℕ, N ≠ 0 ∧ ∃ z ∈ Zd, (z : E) = N * y := by
    intro y
    have hy : y ∈ Submodule.span ℚ (Set.range fun k : Fin pb.dim => θ ^ (k : ℕ)) := by
      have h := pb.basis.span_eq
      rw [pb.coe_basis, hpbgen] at h
      rw [h]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨1, one_ne_zero, θO ^ (k : ℕ), Submodule.subset_span ⟨k, rfl⟩, by simp [θO]⟩
    | zero => exact ⟨1, one_ne_zero, 0, Zd.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1, z1, hz1, e1⟩ := hx
      obtain ⟨N2, h2, z2, hz2, e2⟩ := hy
      refine ⟨N1 * N2, mul_ne_zero h1 h2, (N2 : ℤ) • z1 + (N1 : ℤ) • z2,
        Zd.add_mem (Zd.smul_mem _ hz1) (Zd.smul_mem _ hz2), ?_⟩
      simp only [Subring.coe_add, AddSubgroupClass.coe_zsmul, zsmul_eq_mul]
      push_cast
      rw [e1, e2]; ring
    | smul q x _ hx =>
      obtain ⟨N, h, z, hz, e⟩ := hx
      refine ⟨q.den * N, mul_ne_zero q.den_nz h, q.num • z, Zd.smul_mem _ hz, ?_⟩
      have hq : ((q.num : ℚ) : E) = (q.den : E) * (q : E) := by
        rw [← Rat.den_mul_eq_num q]; push_cast; ring
      simp only [AddSubgroupClass.coe_zsmul, zsmul_eq_mul, Rat.smul_def]
      push_cast
      rw [e]
      have hq' : (q.num : E) = (q.den : E) * (q : E) := by exact_mod_cast hq
      rw [hq']; push_cast; ring

  have hdpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  obtain ⟨e0, he0⟩ : ∃ e0 : L, (e0 : E) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : Submodule.span ℂ (Set.range P) = ⊥ := by
      rw [Submodule.span_eq_bot]; rintro _ ⟨x, rfl⟩
      have : x = 0 := Subtype.ext (hcon x)
      rw [this, map_zero]
    rw [hspan] at hbot
    have h0 : Module.finrank ℂ W = 0 := by
      rw [← finrank_top ℂ W, hbot, finrank_bot]
    omega
  set w0 : W := P e0 with hw0
  set A : Module.End ℂ W := T θO with hAdef
  let v : Fin pb.dim → W := fun k => (A ^ (k : ℕ)) w0
  have hψ : ∀ z : O, TR z w0 = P (mulL z e0) := fun z => hT' z e0
  have hZ : ∀ z ∈ Zd, TR z w0 ∈ Submodule.span ℂ (Set.range v) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [map_pow]; exact Submodule.subset_span ⟨k, rfl⟩
    | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
    | smul m x _ hx =>
      rw [map_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul ℂ]
      exact Submodule.smul_mem _ _ hx
  have hSd : Submodule.span ℂ (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨N, hN, z, hz, hzE⟩ := hA ((x : E) / e0)
    have hmul : mulL z e0 = N • x := by
      apply Subtype.ext
      show (z : E) * e0 = _
      rw [AddSubgroup.coe_nsmul, nsmul_eq_mul, hzE, _root_.mul_assoc, div_mul_cancel₀ _ he0]
    have h1 : (N : ℂ) • P x ∈ Submodule.span ℂ (Set.range v) := by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← hmul, ← hψ]; exact hZ z hz
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
    have h2 := Submodule.smul_mem _ (N : ℂ)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hNc, one_smul] at h2
  have hcard : Fintype.card (Fin pb.dim) = Module.finrank ℂ W := by
    rw [Fintype.card_fin, hdim, hpbdim]
  have hli : LinearIndependent ℂ v := linearIndependent_of_top_le_span_of_card_eq_finrank hSd.ge hcard

  set f := minpoly ℚ θ with hf
  set fC : Polynomial ℂ := f.map (algebraMap ℚ ℂ) with hfC
  have hfA : Polynomial.aeval A fC = 0 := by
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) f
    set g := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f with hg
    have hb0 : ((b : ℤ) : ℂ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero b.2
    have hgθ : Polynomial.aeval θO g = 0 := by
      apply Subtype.ext
      have h1 : ((Polynomial.aeval θO g : O) : E) = Polynomial.aeval θ g :=
        (Polynomial.aeval_algHom_apply (O.subtype : O →+* E).toIntAlgHom θO g).symm
      rw [h1, ← Polynomial.aeval_map_algebraMap ℚ, hb, map_zsmul, minpoly.aeval, smul_zero]
      rfl
    have h2 : Polynomial.aeval A g = 0 := by
      have := Polynomial.aeval_algHom_apply TR.toIntAlgHom θO g
      rw [hgθ, map_zero] at this
      exact this
    have h3 : g.map (algebraMap ℤ ℂ) = (b : ℤ) • fC := by
      rw [IsScalarTower.algebraMap_eq ℤ ℚ ℂ, ← Polynomial.map_map, hb, zsmul_eq_mul, zsmul_eq_mul,
        Polynomial.map_mul, Polynomial.map_intCast]
    have h4 : Polynomial.aeval A (g.map (algebraMap ℤ ℂ)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]; exact h2
    rw [h3, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ] at h4
    exact (smul_eq_zero.mp h4).resolve_left hb0

  set r : ℂ := τ θ with hr
  have hroot : fC.IsRoot r := by
    rw [Polynomial.IsRoot, hfC, Polynomial.eval_map_algebraMap, show r = τ.toRatAlgHom θ from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hsep : fC.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ θ)
  set f₁ := fC /ₘ (Polynomial.X - Polynomial.C r) with hf₁
  have hfac : (Polynomial.X - Polynomial.C r) * f₁ = fC :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hf1r : f₁.eval r ≠ 0 := by
    have h := hsep.aeval_derivative_ne_zero (x := r) (by rw [Polynomial.coe_aeval_eq_eval]; exact hroot)
    rw [Polynomial.coe_aeval_eq_eval, ← hfac, Polynomial.derivative_mul] at h
    simpa using h
  have hfC0 : fC ≠ 0 := (Polynomial.Monic.map _ (minpoly.monic hint)).ne_zero
  have hf1ne : f₁ ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hfac; exact hfC0 hfac.symm
  have hdegC : fC.natDegree = pb.dim := by
    rw [hfC, Polynomial.natDegree_map, hf, ← hpbgen, PowerBasis.natDegree_minpoly]
  have hdeg1 : f₁.natDegree + 1 = pb.dim := by
    rw [← hdegC, ← hfac, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hf1ne,
      Polynomial.natDegree_X_sub_C, add_comm]
  set S : Module.End ℂ W := Polynomial.aeval A f₁ with hSdef
  have hS : ∀ w, A (S w) = r • S w := by
    intro w
    have h : (Polynomial.aeval A fC) w = 0 := by rw [hfA]; rfl
    rw [← hfac, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h
    exact h
  have hpow : ∀ (u : W) (c : ℂ), A u = c • u → ∀ k : ℕ, (A ^ k) u = c ^ k • u := by
    intro u c hu k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hu, smul_smul, pow_succ]
  have hne : S w0 ≠ 0 := by
    intro h0
    have hlt : f₁.natDegree < pb.dim := by omega
    have hsum : ∑ k : Fin pb.dim, f₁.coeff k • v k = 0 := by
      rw [← h0, hSdef, Polynomial.aeval_eq_sum_range' hlt, LinearMap.sum_apply]
      simp only [LinearMap.smul_apply]
      exact Fin.sum_univ_eq_sum_range (fun i => f₁.coeff i • (A ^ i) w0) pb.dim
    have h := (Fintype.linearIndependent_iff.mp hli) _ hsum ⟨f₁.natDegree, hlt⟩
    exact hf1ne (Polynomial.leadingCoeff_eq_zero.mp h)
  have hcomm : Commute S A := by
    have := (Commute.all f₁ Polynomial.X).map (Polynomial.aeval A)
    rwa [Polynomial.aeval_X] at this
  have hSall : ∀ w, S w ∈ Submodule.span ℂ {S w0} := by
    have hle : Submodule.span ℂ (Set.range v) ≤ (Submodule.span ℂ {S w0}).comap S := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      show S ((A ^ (k : ℕ)) w0) ∈ _
      rw [← Module.End.mul_apply, (hcomm.pow_right _).eq, Module.End.mul_apply, hpow _ r (hS w0)]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    intro w
    exact hle (hSd ▸ Submodule.mem_top)
  have hle : Module.End.eigenspace A r ≤ Submodule.span ℂ {S w0} := by
    intro u hu
    rw [Module.End.mem_eigenspace_iff] at hu
    have hSu : S u = f₁.eval r • u := by
      by_cases hu0 : u = 0
      · simp [hu0]
      · exact Module.End.aeval_apply_of_hasEigenvector
          (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hu, hu0⟩)
    have h2 := Submodule.smul_mem _ (f₁.eval r)⁻¹ (hSall u)
    rwa [hSu, smul_smul, inv_mul_cancel₀ hf1r, one_smul] at h2
  have heq : Module.End.eigenspace A r = Submodule.span ℂ {S w0} :=
    le_antisymm hle ((Submodule.span_singleton_le_iff_mem _ _).mpr
      (Module.End.mem_eigenspace_iff.mpr (hS w0)))

  have hcommon : (⨅ a : O, Module.End.eigenspace (T a) (τ a)) = Module.End.eigenspace A r := by
    apply le_antisymm
    · exact iInf_le (fun a : O => Module.End.eigenspace (T a) (τ a)) θO
    · intro u hu
      rw [Module.End.mem_eigenspace_iff] at hu
      rw [Submodule.mem_iInf]; intro a
      rw [Module.End.mem_eigenspace_iff]
      have hZu : ∀ z ∈ Zd, TR z u = τ z • u := by
        intro z hz
        induction hz using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, rfl⟩ := hx
          rw [map_pow]
          show (A ^ (k : ℕ)) u = _
          rw [hpow u r hu]
          simp [θO, r]
        | zero => simp
        | add x y _ _ hx hy =>
          rw [map_add, LinearMap.add_apply, hx, hy, Subring.coe_add, map_add, add_smul]
        | smul m x _ hx =>
          rw [map_zsmul, LinearMap.smul_apply, hx, AddSubgroupClass.coe_zsmul, map_zsmul, smul_assoc]
      obtain ⟨N, hN, z, hz, hzE⟩ := hA a
      have hza : z = N • a := Subtype.ext (by rw [hzE, AddSubmonoidClass.coe_nsmul, nsmul_eq_mul])
      have h1 := hZu z hz
      rw [hza, map_nsmul, LinearMap.smul_apply, AddSubmonoidClass.coe_nsmul, map_nsmul, smul_assoc,
        ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ N (τ a • u)] at h1
      have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
      exact smul_right_injective W hNc h1
  rw [hcommon, heq, finrank_span_singleton hne]

end GlobalTheory.EigLine
