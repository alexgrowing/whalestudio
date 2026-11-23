import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem exists_fnMap {F : Type} [Field F] {Y B : Var F} (f : Y.X ⟶ B.X) (hf : f ≫ B.str = Y.str)
    (hs : genericPoint B.X ∈ Set.range f) :
    ∃ φ : B.Fn →+* Y.Fn, genericPt Y ≫ f = spMap φ ≫ genericPt B ∧
      algebraMap F Y.Fn = φ.comp (algebraMap F B.Fn) := by
  obtain ⟨y, hy⟩ := hs
  have h : f (genericPoint Y.X) ⤳ genericPoint B.X := hy ▸ (genericPoint_specializes y).map f.continuous
  let φ : B.Fn →+* Y.Fn := (B.X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint Y.X)).hom
  have h₁ : genericPt Y ≫ f = spMap φ ≫ genericPt B := by
    change Y.X.fromSpecStalk _ ≫ f =
      Spec.map (B.X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint Y.X)) ≫ B.X.fromSpecStalk _
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  refine ⟨φ, h₁, EigLoc.spMap_inj ?_⟩
  have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (GlobalTheory.FlagBundle.ratOf Y).pt_s
  have h2 : genericPt B ≫ B.str = spMap (algebraMap F B.Fn) := (GlobalTheory.FlagBundle.ratOf B).pt_s
  have h3 : spMap (φ.comp (algebraMap F B.Fn)) = spMap φ ≫ spMap (algebraMap F B.Fn) := by
    rw [← Spec.map_comp]; rfl
  rw [h3, ← h1, ← h2, ← hf, ← Category.assoc, h₁, Category.assoc]

private theorem onComp_π {D : D7} (O : Setup D) (k : O.s.Comp) (y : (O.Φ.C k).Y.X) :
    OnComp O.s k ((O.Φ.C k).π y) := by
  obtain ⟨z, hz⟩ : ((O.s.U O.κ.σ₀).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
  refine ⟨⟨z, hz⟩, fun pt => ?_⟩
  exact (isPreconnected_range (O.Φ.C k).π.continuous).subset_connectedComponent ⟨y, rfl⟩
    (O.Φ.label k ⟨z, hz⟩ pt)

theorem UpperTheory.flag_polynomial_dimension :
    ∀ (D : D7) (O : Setup D) (c₀ : O.s.Comp), ∃ (B : Var D.what₂.LL) (ρB : B.X ⟶ gen O.s.T.Z) (f : (O.Φ.C c₀).Y.X ⟶ B.X) (φ : B.Fn →+* (O.Φ.C c₀).Y.Fn), ρB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = B.str ∧ IsOver O.κ.e ρB (O.Φ.C c₀).π f φ ∧ B.dim = GlobalTheory.FlagPoly.dimGr D.what₂.Tau O.N O.j ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : O.κ.c.F →+* K) (x : Sp K ⟶ B.X), x ≫ ρB ≫ genStr O.s.T.Z = spMap χ → ∀ k : EigFrame O.s.T.Z χ (x ≫ ρB ≫ genι O.s.T.Z), ∃! p : Sp K ⟶ (O.Φ.C c₀).Y.X, p ≫ f = x ∧ (O.Φ.C c₀).Carries p k) := by
  intro D O c₀
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e O.s.geo O.s.T.smooth
  let η := genericPoint (O.Φ.C c₀).Y.X
  obtain ⟨i, hi, -⟩ := hcov ((O.Φ.C c₀).π η)
  have hop : ∀ i', IsOpen (Set.range (j i')) := fun i' =>
    haveI := (hB i').1
    (j i').isOpenEmbedding.isOpen_range
  have hcl : IsClopen (Set.range (j i)) := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, hop i⟩
    obtain ⟨i', h1, h2⟩ := hcov z
    refine ⟨Set.range (j i'), fun w hw hw' => hz ?_, hop i', h1⟩
    rwa [(hcov w).unique hw' hw]
  have hsub : Set.range (O.Φ.C c₀).π ⊆ Set.range (j i) :=
    (isPreconnected_range (O.Φ.C c₀).π.continuous).subset_isClopen hcl ⟨_, ⟨η, rfl⟩, hi⟩
  have := (hB i).1
  let f : (O.Φ.C c₀).Y.X ⟶ (B i).X := IsOpenImmersion.lift (j i) (O.Φ.C c₀).π hsub
  have hf : f ≫ j i = (O.Φ.C c₀).π := IsOpenImmersion.lift_fac _ _ _
  have hstr : f ≫ (B i).str = (O.Φ.C c₀).Y.str := by
    rw [← (hB i).2.2.1, ← Category.assoc, hf, (O.Φ.C c₀).π_str]
  have hl : ∀ (K : Type) [Field K] [IsAlgClosed K] (χ : O.κ.c.F →+* K) (x : Sp K ⟶ (B i).X),
      (x ≫ j i) ≫ genStr O.s.T.Z = spMap χ → ∀ k : EigFrame O.s.T.Z χ ((x ≫ j i) ≫ genι O.s.T.Z),
      ∃! p : Sp K ⟶ (O.Φ.C c₀).Y.X, p ≫ f = x ∧ (O.Φ.C c₀).Carries p k := by
    intro K _ _ χ x hx k
    obtain ⟨⟨i', p⟩, ⟨hp1, hp2⟩, hu⟩ := O.Φ.lifts K χ (x ≫ j i) hx k
    dsimp only at hp1 hp2
    let o : Sp K := IsLocalRing.closedPoint K
    obtain rfl : i' = c₀ := by
      have h1 := onComp_π O i' (p o)
      have h2 := onComp_π O c₀ η
      have h3 : (O.Φ.C i').π (p o) ∈ Set.range (j i) := ⟨x o, by
        rw [← Scheme.Hom.comp_apply, ← hp1, Scheme.Hom.comp_apply]⟩
      have h4 : connectedComponent ((O.Φ.C c₀).π η) = connectedComponent ((O.Φ.C i').π (p o)) :=
        connectedComponent_eq ((isPreconnected_range (j i).continuous).subset_connectedComponent hi h3)
      unfold OnComp at h2
      rw [h4] at h2
      exact (PtComp.existsUnique_onComp O.s _).unique h1 h2
    refine ⟨p, ⟨(cancel_mono (j i)).1 (by rw [Category.assoc, hf, hp1]), hp2⟩, ?_⟩
    rintro q ⟨h1, h2⟩
    exact eq_of_heq (Sigma.mk.inj (hu ⟨_, q⟩ ⟨by rw [← hf, ← Category.assoc, h1], h2⟩)).2
  have hs : genericPoint (B i).X ∈ Set.range f := by
    let K := AlgebraicClosure (B i).Fn
    let x : Sp K ⟶ (B i).X := spMap (algebraMap (B i).Fn K) ≫ genericPt (B i)
    let χ : O.κ.c.F →+* K := (Spec.preimage ((x ≫ j i) ≫ genStr O.s.T.Z)).hom
    have hχ : (x ≫ j i) ≫ genStr O.s.T.Z = spMap χ := (Spec.map_preimage _).symm
    obtain ⟨k⟩ := EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ O.s.T.Z K χ _ hχ
    obtain ⟨p, ⟨hp, -⟩, -⟩ := hl K χ x hχ k
    let o : Sp K := IsLocalRing.closedPoint K
    refine ⟨p o, ?_⟩
    rw [← Scheme.Hom.comp_apply, hp]
    change (B i).X.fromSpecStalk _ (spMap (algebraMap (B i).Fn K) o) = _
    rw [show spMap (algebraMap (B i).Fn K) o = IsLocalRing.closedPoint ((B i).X.presheaf.stalk (genericPoint (B i).X)) from
      Subsingleton.elim (α := PrimeSpectrum (B i).Fn) _ _]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨φ, hφ1, hφ2⟩ := exists_fnMap f hstr hs
  refine ⟨B i, j i, f, φ, (hB i).2.2.1, ⟨hf, hstr, hφ1, ?_⟩, ?_, fun K _ _ χ x hx k => ?_⟩
  · rw [constF, constF, hφ2, RingHom.comp_assoc]
  · have h1 := O.S.p_eq
    have h2 := O.S.rank_eq
    have h3 : O.S.Dw.q = O.N - O.j := by omega
    have h4 : Module.finrank ℚ D.host.E / 2 = Fintype.card D.what₂.Tau := by
      have h5 : D.R.f = 2 * D.R.ord := rfl
      rw [D.host.finrank_cmField, D.what₂.card_Tau, h5]
      omega
    rw [(hB i).2.1, Datum.dim, GlobalTheory.FlagPoly.dimGr, h4, h1, h3, mul_assoc]
  · exact hl K χ x hx k
