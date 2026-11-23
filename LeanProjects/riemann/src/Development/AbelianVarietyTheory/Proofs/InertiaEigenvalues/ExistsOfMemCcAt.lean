import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

noncomputable section

namespace GlobalTheory.CutFam

theorem exists_of_mem_ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X)
    {c : O} (hc : c ∈ ccAt T Z π) : ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π = c := by
  unfold ccAt Ideal.map at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    exact ⟨f, hf, rfl⟩
  | zero => exact ⟨0, zero_mem _, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨g, hg, rfl⟩ := hy
    exact ⟨f + g, add_mem hf hg, rfl⟩
  | smul r x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    refine ⟨algebraMap O T r * f, Ideal.mul_mem_left _ _ hf, ?_⟩
    simp [smul_eq_mul]

theorem mem_ccIdeal_iff {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (f : T) :
    f ∈ ccIdeal T Z ↔ ∀ y, y ∉ Z → (f : X → O) y = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h y hy
    have := congrFun h ⟨y, hy⟩
    simpa using this
  · intro h
    funext y
    simpa using h y.1 y.2

theorem exists_ne_zero {O X : Type} [CommRing O] [IsDomain O] [Fintype X] (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (Z : Finset X) (π : X) (hπ : π ∈ Z) :
    ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π ≠ 0 := by
  classical
  have h : ∀ x : {x // x ∉ Z}, ∃ f : T, (f : X → O) x.1 ≠ (f : X → O) π := by
    intro x
    obtain ⟨f, hfT, hf⟩ := hsep x.1 π (fun h => x.2 (h ▸ hπ))
    exact ⟨⟨f, hfT⟩, hf⟩
  choose g hg using h
  refine ⟨∏ x : {x // x ∉ Z}, (g x - algebraMap O T ((g x : X → O) x.1)), ?_, ?_⟩
  · rw [mem_ccIdeal_iff]
    intro y hy
    rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨y, hy⟩) ?_
    simp
  · rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun x _ => ?_
    have e : ∀ c : O, ((algebraMap O T c : T) : X → O) π = c := fun c => by simp
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, e]
    exact sub_ne_zero.mpr (hg x).symm

theorem length_span {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : t ≠ 0) :
    Module.length O (O ⧸ Ideal.span {t}) = IsDiscreteValuationRing.addVal O t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n]
  have : Ideal.span {(u : O) * ϖ ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

theorem lenUnit_mul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) {a b : O}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    lenUnit (O := O) l (O ⧸ Ideal.span {a * b}) =
      lenUnit (O := O) l (O ⧸ Ideal.span {a}) + lenUnit (O := O) l (O ⧸ Ideal.span {b}) := by
  unfold lenUnit
  rw [length_span _ (mul_ne_zero ha hb), length_span _ ha, length_span _ hb,
    IsDiscreteValuationRing.addVal_mul]
  have h1 : IsDiscreteValuationRing.addVal O a ≠ ⊤ := fun h =>
    ha (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  have h2 : IsDiscreteValuationRing.addVal O b ≠ ⊤ := fun h =>
    hb (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  rw [ENat.toNat_add h1 h2]
  push_cast
  rw [add_div]

variable {D : D7}

theorem act_bc_eig (i : D.nd.Loc) (f : D.nd.T i) (x : D.nd.X i)
    {u : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)}
    (hu : u ∈ heckeEig (D.nd.T i) (D.nd.act i) x) :
    (D.nd.act i f).baseChange (FractionRing (D.nd.O i)) u = ((f : D.nd.X i → D.nd.O i) x) • u := by
  have h := (Submodule.mem_iInf _).mp hu f
  rw [Module.End.mem_eigenspace_iff] at h
  rw [h, algebraMap_smul]

theorem bc_mem_eig (i : D.nd.Loc) (β : Module.End (D.nd.O i) (D.nd.Mt i))
    (hβ : ∀ f : D.nd.T i, β * D.nd.act i f = D.nd.act i f * β) (x : D.nd.X i)
    {u : TensorProduct (D.nd.O i) (FractionRing (D.nd.O i)) (D.nd.Mt i)}
    (hu : u ∈ heckeEig (D.nd.T i) (D.nd.act i) x) :
    β.baseChange (FractionRing (D.nd.O i)) u ∈ heckeEig (D.nd.T i) (D.nd.act i) x := by
  refine (Submodule.mem_iInf _).mpr fun f => ?_
  have h := (Submodule.mem_iInf _).mp hu f
  rw [Module.End.mem_eigenspace_iff] at h ⊢
  have e : (D.nd.act i f).baseChange (FractionRing (D.nd.O i)) (β.baseChange (FractionRing (D.nd.O i)) u) =
      β.baseChange (FractionRing (D.nd.O i)) ((D.nd.act i f).baseChange (FractionRing (D.nd.O i)) u) := by
    rw [← Module.End.mul_apply, ← LinearMap.baseChange_mul, ← hβ f, LinearMap.baseChange_mul,
      Module.End.mul_apply]
  rw [e, h, map_smul]

theorem perPoint (i : D.nd.Loc) (k : Fin 2) (π : D.nd.X i) (Xs : Set (D.nd.X i))
    (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i) (h : CutAt i k π Xs β b) :
    ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.O i),
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      (∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
      a ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, α.baseChange (FractionRing (D.nd.O i)) u = a • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) ≤
        vccCut i Xs π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard := by
  classical
  obtain ⟨_, hπZ, hXZ, hcomm, hb0, hbπ, hbout, hblen⟩ := h
  have hπc : π ∈ cutLocus i Xs := by simp [cutLocus, hπZ]
  obtain ⟨f0, hf0, hf0π⟩ := exists_ne_zero (D.nd.T i) (D.nd.T_sep i) _ π hπc
  obtain ⟨c, hc⟩ : ∃ c, ccAt (D.nd.T i) (cutLocus i Xs) π = Ideal.span {c} :=
    ⟨Submodule.IsPrincipal.generator _, (Ideal.span_singleton_generator _).symm⟩
  have hcI : c ∈ ccAt (D.nd.T i) (cutLocus i Xs) π := hc ▸ Ideal.mem_span_singleton_self c
  obtain ⟨g, hg, hgπ⟩ := exists_of_mem_ccAt _ _ _ hcI
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hm : ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) π).comp (D.nd.T i).val.toRingHom) f0 ∈
        ccAt (D.nd.T i) (cutLocus i Xs) π := Ideal.mem_map_of_mem _ hf0
    rw [hc, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hm
    exact hf0π hm
  refine ⟨D.nd.act i g * β, c * b, ?_, ?_, mul_ne_zero hc0 hb0, ?_, ?_⟩
  · intro f
    rw [mul_assoc, hcomm f, ← mul_assoc, ← map_mul, mul_comm g f, map_mul, mul_assoc]
  · intro x hx u hu
    rw [LinearMap.baseChange_mul, Module.End.mul_apply]
    by_cases hxs : x ∈ Xs
    · have hxZ : x ∉ D.nd.Z i := fun hz => hx (hXZ x hxs hz)
      have hxc : x ∉ cutLocus i Xs := by simp [cutLocus, hxZ, hxs]
      rw [act_bc_eig i g x (bc_mem_eig i β hcomm x hu), (mem_ccIdeal_iff _ _ g).mp hg x hxc, zero_smul]
    · rw [hbout x hxs u hu, map_zero]
  · intro u hu
    rw [LinearMap.baseChange_mul, Module.End.mul_apply, hbπ u hu, LinearMap.map_smul_of_tower,
      act_bc_eig i g π hu, hgπ, smul_smul, mul_comm]
  · unfold vccCut
    rw [lenUnit_mul _ hc0 hb0, ← hc]
    linarith

theorem fam_of_cut : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ),
    CongruenceLocalDecomposition CT i k ρ eta → CongruenceFamilyEndomorphisms CT i k ρ eta := by
  intro D CT i k ρ eta hcut
  classical
  obtain ⟨Xs, β, b, h⟩ := hcut
  have hp : ∀ π ∈ D.nd.Zgood i, ∃ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (a : D.nd.O i),
      (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) ∧
      (∀ x, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
        α.baseChange (FractionRing (D.nd.O i)) u = 0) ∧
      a ≠ 0 ∧
      (∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) π, α.baseChange (FractionRing (D.nd.O i)) u = a • u) ∧
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) ≤
        vccCut i (Xs π) π + padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard :=
    fun π hπ => perPoint i k π (Xs π) (β π) (b π) (h π hπ).1
  choose! α a hα using hp
  refine ⟨α '' ((D.nd.Zgood i : Finset (D.nd.X i)) : Set (D.nd.X i)), a, fun π => vccCut i (Xs π) π, ?_, ?_⟩
  · rintro _ ⟨π, hπ, rfl⟩
    exact ⟨(hα π hπ).1, (hα π hπ).2.1⟩
  · intro π hπ
    obtain ⟨_, _, h3, h4, h5⟩ := hα π hπ
    exact ⟨h3, ⟨α π, ⟨π, hπ, rfl⟩, h4⟩, h5, (h π hπ).2⟩

end GlobalTheory.CutFam
