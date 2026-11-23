import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

section Semilinear

theorem exists_equiv_map_lattice {O K U U' : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U]
    [AddCommGroup U'] [Module K U'] [Module O U'] [IsScalarTower O K U']
    (A : Submodule O U) (B : Submodule O U') [A.IsLattice K] [B.IsLattice K]
    (h : Module.finrank K U = Module.finrank K U') :
    ∃ g : U ≃ₗ[K] U', A.map (g.toLinearMap.restrictScalars O) = B := by
  have key : ∀ {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (C : Submodule O V)
      [C.IsLattice K], ∃ c : Module.Basis (Fin (Module.finrank K V)) K V, Submodule.span O (Set.range c) = C := by
    intro V _ _ _ _ C _
    let c₀ := Module.finBasis O C
    let c₁ := c₀.extendOfIsLattice K
    have hn : Module.finrank K V = Module.finrank O C := by
      rw [Module.finrank_eq_card_basis c₁, Fintype.card_fin]
    refine ⟨c₁.reindex (finCongr hn.symm), ?_⟩
    rw [Module.Basis.range_reindex]
    have h1 : Set.range c₁ = C.subtype '' Set.range c₀ := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact c₀.extendOfIsLattice_apply K i
    rw [h1, ← Submodule.map_span, c₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨a, ha⟩ := key A
  obtain ⟨b, hb⟩ := key B
  refine ⟨a.equiv b (finCongr h), ?_⟩
  rw [← ha, ← hb, Submodule.map_span, ← Set.range_comp, ← (finCongr h).surjective.range_comp b]
  congr 2
  funext i
  simp

theorem exists_semilinear {L V O K U : Type} [Field L] [AddCommGroup V] [Module L V] [Module.Finite L V]
    [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U] (e : L →+* K)
    (S : Set V) (hS : S.Finite) (hspan : Submodule.span L S = ⊤) (B : Submodule O U) [B.IsLattice K]
    (h : Module.finrank L V = Module.finrank K U) :
    ∃ f : V →ₛₗ[e] U,
      (∀ (ι : Type) (b : Module.Basis ι L V), LinearIndependent K (fun i => f (b i)) ∧
        Submodule.span K (Set.range fun i => f (b i)) = ⊤) ∧ Submodule.span O (f '' S) = B := by
  classical
  let b₀ := Module.finBasis L V
  let f₀ : V →ₛₗ[e] (Fin (Module.finrank L V) → K) :=
    { toFun := fun x i => e (b₀.repr x i)
      map_add' := fun x y => by funext i; simp
      map_smul' := fun c x => by funext i; simp }
  have hf₀ : ∀ T : Set V, Submodule.span L T = ⊤ → Submodule.span K (f₀ '' T) = ⊤ := by
    intro T hT
    have h1 : ∀ x, f₀ x ∈ Submodule.span K (f₀ '' T) := fun x => by
      have hx : x ∈ Submodule.span L T := hT ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
      | smul c y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
    rw [eq_top_iff, ← (Pi.basisFun K (Fin (Module.finrank L V))).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h2 : Pi.basisFun K (Fin (Module.finrank L V)) i = f₀ (b₀ i) := by
      funext j
      show _ = e (b₀.repr (b₀ i) j)
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [h2]
    exact h1 _
  let A : Submodule O (Fin (Module.finrank L V) → K) := Submodule.span O (f₀ '' S)
  haveI : A.IsLattice K :=
    ⟨Submodule.fg_span (hS.image _), by rw [Submodule.span_span_of_tower, hf₀ S hspan]⟩
  obtain ⟨g, hg⟩ := exists_equiv_map_lattice (K := K) A B (by rw [← h]; simp)
  refine ⟨g.toLinearMap.comp f₀, fun ι b => ?_, ?_⟩
  · haveI : Finite ι := Module.Finite.finite_basis b
    haveI := Fintype.ofFinite ι
    have h1 : Submodule.span K (Set.range fun i => (g.toLinearMap.comp f₀) (b i)) = ⊤ := by
      have h2 : (Set.range fun i => (g.toLinearMap.comp f₀) (b i)) = g.toLinearMap '' (f₀ '' Set.range b) := by
        rw [← Set.range_comp, ← Set.range_comp]; rfl
      rw [h2, ← Submodule.map_span, hf₀ _ b.span_eq, Submodule.map_top]
      exact g.range
    exact ⟨linearIndependent_of_top_le_span_of_card_eq_finrank h1.ge
      (by rw [← h, Module.finrank_eq_card_basis b]), h1⟩
  · rw [← hg, Submodule.map_span, Set.image_image]
    rfl

theorem form_gen {L V M ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] {σ : L →+* ℂ} (j : V →ₛₗ[σ] M) (b : Module.Basis ι L V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤)
    (T : Finset M) (hT : Submodule.span ℂ (T : Set M) = ⊤) (hsub : ∀ x ∈ T, x ∈ Set.range j) :
    Module.Finite L V ∧ {x | j x ∈ T}.Finite ∧ Submodule.span L {x | j x ∈ T} = ⊤ := by
  haveI : Finite ι := hb.1.finite
  haveI := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ M := Module.Basis.mk hb.1 hb.2.ge
  have hB : ∀ i, B i = j (b i) := fun i => by simp [B]
  have key : ∀ l : V →ₗ[L] L, ∃ l' : M →ₗ[ℂ] ℂ, ∀ x, l' (j x) = σ (l x) := fun l => by
    refine ⟨B.constr ℂ fun i => σ (l (b i)), fun x => ?_⟩
    conv_lhs => rw [← b.sum_repr x]
    conv_rhs => rw [← b.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, ← hB, Module.Basis.constr_basis, smul_eq_mul, map_mul, RingHom.id_apply]
  have hinj : Function.Injective j := fun x y hxy => by
    refine b.ext_elem fun i => σ.injective ?_
    obtain ⟨l', hl'⟩ := key (b.coord i)
    have h1 := hl' x
    rw [hxy, hl' y] at h1
    exact h1.symm
  refine ⟨Module.Finite.of_basis b, T.finite_toSet.preimage hinj.injOn, ?_⟩
  by_contra hne
  obtain ⟨l, hl0, hl⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨l', hl'⟩ := key l
  have h1 : l' = 0 := by
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hT, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := hsub y hy
    have hx : l x = 0 := hl (Submodule.subset_span hy)
    show l' (j x) = 0
    rw [hl', hx, map_zero]
  refine hl0 (LinearMap.ext fun x => σ.injective ?_)
  rw [← hl', h1]
  simp

theorem baseChange_lattice {A B V : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) [AddCommGroup V] [Module (FractionRing A) V] [Module A V]
    [IsScalarTower A (FractionRing A) V] (Λ : Submodule A V) (hfg : Λ.FG)
    (hspan : Submodule.span (FractionRing A) (Λ : Set V) = ⊤) :
    Module.finrank (FractionRing B) (FractionRing B ⊗[A] V) = Module.finrank (FractionRing A) V ∧
      (Submodule.span B ((TensorProduct.mk A (FractionRing B) V 1) '' (Λ : Set V))).IsLattice (FractionRing B) := by
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  haveI : IsScalarTower A (FractionRing A) (FractionRing B) := FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  refine ⟨?_, ?_, ?_⟩
  · rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange A (FractionRing A) (FractionRing B) (FractionRing B) V).finrank_eq,
      Module.finrank_baseChange, (NChoice.fracEquiv A V).finrank_eq]
  · obtain ⟨T, rfl⟩ := hfg
    rw [← Submodule.map_coe, ← Submodule.span_image, Submodule.span_span_of_tower]
    exact Submodule.fg_span (T.finite_toSet.image _)
  · rw [Submodule.span_span_of_tower, eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add y z hy hz => exact Submodule.add_mem _ hy hz
    | tmul a v =>
      obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors A) (FractionRing A) (Λ : Set V) v
        (hspan ▸ Submodule.mem_top)
      rw [Submodule.span_eq] at hd
      have hd0 : algebraMap A (FractionRing B) d ≠ 0 :=
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A (FractionRing B))).2 (nonZeroDivisors.coe_ne_zero d)
      have h1 : a ⊗ₜ[A] v = (a * (algebraMap A (FractionRing B) d)⁻¹) • ((1 : FractionRing B) ⊗ₜ[A] ((d : A) • v)) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def (d : A), mul_one, smul_eq_mul,
          mul_assoc, inv_mul_cancel₀ hd0, mul_one]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hd, rfl⟩)

end Semilinear

section Series

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (E : IntegralHeckeForms.ExpDat Y)

theorem twOK_one (i : X.Tw) (k : ℕ) : IntegralHeckeForms.TwOK i k ∅ (1 : G D.host.E N.Om →* (X.Ok i k)ˣ) := by
  refine ⟨by simp, by simp, by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ, fun g g' _ => by simp, fun g => Subgroup.one_mem _, fun v A _ => by simp,
    fun v _ A _ σ _ => rfl⟩

theorem th_fg (h : IntegralHeckeForms.admT4 Y E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    (IntegralHeckeForms.Th Y i j b (IntegralHeckeForms.SgJ Y E i j b)).FG := by
  have h1 := h i hi j hj b 0 ∅ 1 (twOK_one i 0) _ subset_rfl
  haveI := X.Ok_fin i 0
  haveI : FaithfulSMul (X.O i) (X.Ok i 0) := (faithfulSMul_iff_algebraMap_injective _ _).2 (X.Ok_inj i 0)
  haveI : Module.FaithfullyFlat (X.O i) (X.Ok i 0) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h2 : (((Y.MtLat i j b 0 ∅ 1).map (Y.thP i j b 0 ∅ 1)).restrictScalars (X.O i)).FG :=
    ((Y.MtLat_fg i j b 0 ∅ 1).map _).restrictScalars
  let m := TensorProduct.mk (X.O i) (X.Ok i 0) (Y.Fm i j b) 1
  refine Submodule.fg_of_fg_map_injective m (Module.FaithfullyFlat.tensorProduct_mk_injective _) (h2.of_le ?_)
  rw [IntegralHeckeForms.Th, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  refine h1 (Submodule.subset_span (Set.mem_iUnion₂.2 ⟨a, ha, ?_⟩))
  rw [Y.thPsi_one]
  rfl

theorem exists_basisOf (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) (h : (IntegralHeckeForms.Th Y i j b Sg).FG) :
    ∃ S : Finset (Y.Dat i j b), IntegralHeckeForms.BasisOf Y i j b Sg S := by
  classical
  have hr : Submodule.span (X.O i) (Set.range fun a : Sg => IntegralHeckeForms.AO Y i j b (Y.th i j b a)) =
      (IntegralHeckeForms.Th Y i j b Sg).map (IntegralHeckeForms.AO Y i j b) := by
    rw [IntegralHeckeForms.Th, Submodule.map_span, Set.image_image, Set.image_eq_range]
  obtain ⟨S, h1, h2⟩ := exists_subbasis (X.O i) (Y.Fm i j b) Sg (fun a => IntegralHeckeForms.AO Y i j b (Y.th i j b a))
    (fun c w hc hw => by
      rw [← algebraMap_smul (FractionRing (X.O i)) c w, smul_eq_zero] at hw
      exact hw.resolve_left ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hc))
    (hr ▸ h.map _)
  refine ⟨S.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a', -, rfl⟩ := Finset.mem_map.1 ha
    exact a'.2
  · let e : S ≃ (S.map (Function.Embedding.subtype (· ∈ Sg)) : Finset _) :=
      Equiv.ofBijective (fun a => ⟨a.1.1, Finset.mem_map.2 ⟨a.1, a.2, rfl⟩⟩)
        ⟨fun a a' h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)), fun ⟨y, hy⟩ => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hy
          exact ⟨⟨a, ha⟩, rfl⟩⟩
    exact (linearIndependent_equiv e).1 h1
  · rw [← hr, ← h2, Finset.coe_map, Set.image_image]
    rfl

end Series

end GlobalTheory.TwistChoice

end
