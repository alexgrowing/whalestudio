import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPullbackOfNormalFlatProj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModels

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.LocM.Diag

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (x : Sp B ⟶ Sp A) : ∃ g : A →+* B, spMap g = x :=
  ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩

theorem exists_closed (P : Scheme.{0}) (Q : ∀ (k : Type) [Field k], (Sp k ⟶ P) → Prop)
    (h : ∀ x : P, ∃ (R : Type) (_ : CommRing R) (ι : Sp R ⟶ P) (J : Set R), IsOpenImmersion ι ∧ x ∈ Set.range ι ∧
      ∀ (k : Type) [Field k] (ψ : R →+* k), Q k (spMap ψ ≫ ι) ↔ ∀ r ∈ J, ψ r = 0) :
    ∃ (S : Scheme.{0}) (c : S ⟶ P), IsClosedImmersion c ∧ IsReduced S ∧
      ∀ (k : Type) [Field k] (z : Sp k ⟶ P), Q k z ↔ ∃ z' : Sp k ⟶ S, z' ≫ c = z := by
  choose R iR ι J ho hx hQ using h
  have key : ∀ (x : P) (k : Type) [Field k] (z : Sp k ⟶ P) (y : Sp (R x)), z (IsLocalRing.closedPoint k) = ι x y →
      (Q k z ↔ y ∈ PrimeSpectrum.zeroLocus (J x)) := fun x k _ z y hy => by
    have := ho x
    have h' : Set.range z ⊆ Set.range (ι x) := by
      rintro _ ⟨s, rfl⟩
      rw [Subsingleton.elim s (IsLocalRing.closedPoint k), hy]
      exact ⟨y, rfl⟩
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift (ι x) z h')
    have e : spMap ψ.hom ≫ ι x = z := by
      show Spec.map ψ ≫ _ = _
      rw [hψ, IsOpenImmersion.lift_fac]
    have e' : spMap ψ.hom (IsLocalRing.closedPoint k) = y :=
      (ι x).isOpenEmbedding.injective ((Scheme.Hom.comp_apply (spMap ψ.hom) (ι x) _).symm.trans
        ((congrArg (fun q : Sp k ⟶ P => q (IsLocalRing.closedPoint k)) e).trans hy))
    rw [← e, hQ, ← e']
    refine forall₂_congr fun r _ => ?_
    show _ ↔ ψ.hom r ∈ IsLocalRing.maximalIdeal k
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]
  let C : Set P := {x | Q (P.residueField x) (P.fromSpecResidueField x)}
  have hC : ∀ (x : P) (y : Sp (R x)), ι x y ∈ C ↔ y ∈ PrimeSpectrum.zeroLocus (J x) := fun x y =>
    key x _ _ y (Scheme.fromSpecResidueField_apply _ _)
  have hcl : IsClosed C := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hxC
    have := ho x
    obtain ⟨y, hy⟩ := hx x
    refine ⟨ι x '' (PrimeSpectrum.zeroLocus (J x))ᶜ, ?_, (ι x).isOpenEmbedding.isOpenMap _
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl, y, fun h => hxC (hy ▸ (hC x y).2 h), hy⟩
    rintro _ ⟨y', hy', rfl⟩ h
    exact hy' ((hC x y').1 h)
  let I := Scheme.IdealSheafData.vanishingIdeal (X := P) ⟨C, hcl⟩
  have hr : Set.range I.subschemeι = C := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ReducedSubgroup.isReduced_subscheme_vanishingIdeal _, fun k _ z => ?_⟩
  obtain ⟨y, hy⟩ := hx (z (IsLocalRing.closedPoint k))
  rw [key _ k z y hy.symm, ← hC, hy, ← hr]
  refine ⟨fun h => AbelianSubgroupFinite.exists_lift_of_range_subset z _ ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    rwa [Subsingleton.elim s (IsLocalRing.closedPoint k)]
  · rintro ⟨z', rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem normal (Z : Mdl Y i₀) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z.X := by
  first
    | exact Z.normal
    | exact @GlobalTheory.IsNormalScheme.pred _ Z.normal

theorem frame_at (Z : Mdl Y i₀) {R : Type} [CommRing R] (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* R) :
    GlobalTheory.LocM.IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ) :=
  GlobalTheory.LocM.isFrame_bc E H Dw _ _ _ _ _ _ _ φ _ _ (Z.frame a)

theorem flagAt_chart (Z : Mdl Y i₀) {k : Type} [Field k] (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) :
    Z.FlagAt (spMap φ ≫ Z.chart a) ((Z.fr a).bc φ) :=
  ⟨a, φ, rfl, by rw [Category.assoc]; exact frame_at Z a φ,
    SameFlag.refl fun τ i => by rw [Category.assoc]; exact ((frame_at Z a φ).1 τ i).1⟩

theorem natImg_refl (Z : Mdl Y i₀) {k : Type} [Field k] (w : Sp k ⟶ Z.X) (h : Set.range w ⊆ Z.opn) : NatImg Z Z w w := by
  obtain ⟨a, φ, rfl⟩ := Z.exists_chart w h
  obtain ⟨mu, hmu, hT⟩ := exists_isTrans_id (Y := Y) Z.i
  refine ⟨_, mu, _, hT, by rw [Category.comp_id], flagAt_chart Z a φ, ?_⟩
  simp only [hmu, Category.comp_id]
  exact flagAt_chart Z a φ

theorem j_s (i : Idx H p) : (Y i).j ≫ (Y i).s = pullback.snd _ _ ≫ spMap (i.c.V W).subtype := by
  rw [Model.j, Category.assoc, pullback.condition, reassoc_of% (Y i).jQ_over]

variable {Z₁ Z₂ : Mdl Y i₀} {τ : (Y Z₁.i).X ⟶ (Y Z₂.i).X} (mu : SABMap (Y Z₁.i).t (Y Z₂.i).t τ)

abbrev pfr {R : Type} [CommRing R] (a : Fin Z₁.m) (φ : Γ(Z₁.X, (Z₁.U a).1) →+* R) : Vecs Dw (Y Z₂.i).t R :=
  fun σ i => (Z₁.fr a).bc φ σ i ≫ mu.φ

def Rel {k : Type} [Field k] (w₁ : Sp k ⟶ Z₁.X) (w₂ : Sp k ⟶ Z₂.X) : Prop :=
  ∃ (a : Fin Z₁.m) (φ : Γ(Z₁.X, (Z₁.U a).1) →+* k), spMap φ ≫ Z₁.chart a = w₁ ∧ Z₂.FlagAt w₂ (pfr mu a φ)

variable (hc : GlobalTheory.LocM.Corr Z₁ Z₂) {b : Z₂.i.c.V W →+* Z₁.i.c.V W} (hb : IsIncl b)
  (hτ : τ ≫ (Y Z₂.i).s = (Y Z₁.i).s ≫ spMap b)

include hb hτ in

theorem local_model_chart_section_comp {R : Type} [CommRing R] (a : Fin Z₁.m) (φ : Γ(Z₁.X, (Z₁.U a).1) →+* R) :
    spMap φ ≫ Z₁.chart a ≫ Z₁.π ≫ τ ≫ (Y Z₂.i).s = spMap (((φ.comp (Z₁.alg a)).comp
      (IntermediateField.inclusion hc.2.1).toRingHom).comp (Z₂.i.c.V W).subtype) := by
  rw [hτ, reassoc_of% Z₁.π_s, reassoc_of% (Z₁.affineOpenChart_comp_structure_eq_spMap a φ), spMap_comp']
  congr 1
  exact RingHom.ext fun x => congrArg (φ.comp (Z₁.alg a)) (Subtype.ext (hb x))

include hc hb hτ in

theorem frame_pfr {R : Type} [CommRing R] {a : Fin Z₁.m} {φ : Γ(Z₁.X, (Z₁.U a).1) →+* R} {a₂ : Fin Z₂.m}
    {φ₂ : Γ(Z₂.X, (Z₂.U a₂).1) →+* R} (h : spMap φ₂ ≫ Z₂.chart a₂ ≫ Z₂.π = spMap φ ≫ Z₁.chart a ≫ Z₁.π ≫ τ) :
    GlobalTheory.LocM.IsFrame (Y Z₂.i).t (φ₂.comp (Z₂.alg a₂)) (spMap φ₂ ≫ Z₂.chart a₂ ≫ Z₂.π) (pfr mu a φ) := by
  have e : φ₂.comp (Z₂.alg a₂) = (φ.comp (Z₁.alg a)).comp (IntermediateField.inclusion hc.2.1).toRingHom :=
    coeff_ext (W := W) (by rw [← local_model_chart_section_comp hc hb hτ, ← Z₂.affineOpenChart_comp_structure_eq_spMap, ← Z₂.π_s, reassoc_of% h])
  have := (frame_at Z₁ a φ).push hc.2.1 mu
  simp only [Category.assoc] at this
  rw [e, h]
  exact this

include hc hb hτ in

theorem rel_iff {k : Type} [Field k] {a : Fin Z₁.m} {φ : Γ(Z₁.X, (Z₁.U a).1) →+* k} {a₂ : Fin Z₂.m}
    {φ₂ : Γ(Z₂.X, (Z₂.U a₂).1) →+* k} (h : spMap φ₂ ≫ Z₂.chart a₂ ≫ Z₂.π = spMap φ ≫ Z₁.chart a ≫ Z₁.π ≫ τ) :
    Rel mu (spMap φ ≫ Z₁.chart a) (spMap φ₂ ≫ Z₂.chart a₂) ↔
      SameFlag Z₂.ty (Y Z₂.i).t (spMap φ₂ ≫ Z₂.chart a₂ ≫ Z₂.π) ((Z₂.fr a₂).bc φ₂) (pfr mu a φ) := by
  constructor
  · rintro ⟨a', φ', h₁, a₂', φ₂', h₂, -, hs⟩
    rw [Category.assoc] at hs
    have f₀ := frame_at Z₂ a₂ φ₂
    have f₁ := frame_at Z₂ a₂' φ₂'
    rw [Z₂.alg_eq h₂, reassoc_of% h₂] at f₁
    have f₂ := frame_pfr mu hc hb hτ (a := a') (φ := φ') (h.trans (by rw [reassoc_of% h₁]))
    have g₁ := frame_at Z₁ a φ
    rw [← reassoc_of% h₁] at g₁
    have s₁ := ((Z₁.glue k a' a φ' φ h₁).push mu (fun τ i => ((frame_at Z₁ a' φ').1 τ i).1)
      fun τ i => (g₁.1 τ i).1).mono hc.2.2
    simp only [Category.assoc] at s₁
    rw [reassoc_of% h₁, ← h] at s₁
    exact ((Z₂.glue k a₂ a₂' φ₂ φ₂' h₂.symm).trans (fun τ i => (f₀.1 τ i).1) (fun τ i => (f₀.exists_comb f₁ τ i).exists)
      hs).trans (fun τ i => (f₀.1 τ i).1) (fun τ i => (f₀.exists_comb f₂ τ i).exists) s₁
  · intro hs
    exact ⟨a, φ, rfl, a₂, φ₂, rfl, by rw [Category.assoc]; exact frame_pfr mu hc hb hτ h, by rw [Category.assoc]; exact hs⟩

include hc hb hτ in

theorem Rel.flagAt {k : Type} [Field k] {a : Fin Z₁.m} {φ : Γ(Z₁.X, (Z₁.U a).1) →+* k} {w₂ : Sp k ⟶ Z₂.X}
    (hr : Rel mu (spMap φ ≫ Z₁.chart a) w₂) (h : w₂ ≫ Z₂.π = spMap φ ≫ Z₁.chart a ≫ Z₁.π ≫ τ) :
    Z₂.FlagAt w₂ (pfr mu a φ) := by
  obtain ⟨_, _, _, a₂, φ₂, rfl, -⟩ := id hr
  rw [Category.assoc] at h
  exact ⟨a₂, φ₂, rfl, by rw [Category.assoc]; exact frame_pfr mu hc hb hτ h,
    by rw [Category.assoc]; exact (rel_iff mu hc hb hτ h).1 hr⟩

include hc hb hτ in

theorem exists_equations {R : Type} [CommRing R] {a : Fin Z₁.m} {φ : Γ(Z₁.X, (Z₁.U a).1) →+* R} {a₂ : Fin Z₂.m}
    {φ₂ : Γ(Z₂.X, (Z₂.U a₂).1) →+* R} (h : spMap φ₂ ≫ Z₂.chart a₂ ≫ Z₂.π = spMap φ ≫ Z₁.chart a ≫ Z₁.π ≫ τ) :
    ∃ J : Set R, ∀ (k : Type) [Field k] (ψ : R →+* k),
      Rel mu (spMap ψ ≫ spMap φ ≫ Z₁.chart a) (spMap ψ ≫ spMap φ₂ ≫ Z₂.chart a₂) ↔ ∀ r ∈ J, ψ r = 0 := by
  choose A hA using fun σ i => ((frame_at Z₂ a₂ φ₂).exists_comb (frame_pfr mu hc hb hτ h) σ i).exists
  refine ⟨{r | ∃ σ, ∃ n ∈ Z₂.ty σ, ∃ i j : Fin (Dw.mult σ), (i : ℕ) < n ∧ n ≤ (j : ℕ) ∧ r = A σ i j}, fun k _ ψ => ?_⟩
  have h' : spMap (ψ.comp φ₂) ≫ Z₂.chart a₂ ≫ Z₂.π = spMap (ψ.comp φ) ≫ Z₁.chart a ≫ Z₁.π ≫ τ := by
    rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, h]
  have hA' : ∀ σ i, IsCombAtG (Y Z₂.i).t (spMap (ψ.comp φ₂) ≫ Z₂.chart a₂ ≫ Z₂.π) ((Z₂.fr a₂).bc (ψ.comp φ₂) σ)
      (fun j => ψ (A σ i j)) (pfr mu a (ψ.comp φ) σ i) := fun σ i => by
    have := comb_bc ψ (hA σ i)
    rw [← Category.assoc, spMap_comp'] at this
    rw [← Vecs.bc_bc, pfr, ← Vecs.bc_bc]
    have e : (Vecs.bc ψ ((Z₁.fr a).bc φ)) σ i ≫ mu.φ = spMap (dualMap ψ) ≫ pfr mu a φ σ i := Category.assoc _ _ _
    rw [e]
    exact this
  rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', rel_iff mu hc hb hτ h']
  constructor
  · rintro hs _ ⟨σ, n, hn, i, j, hi, hj, rfl⟩
    obtain ⟨cf, h0, hcf⟩ := hs σ n hn i hi
    have := ((frame_at Z₂ a₂ _).exists_comb (frame_pfr mu hc hb hτ h') σ i).unique (hA' σ i) hcf
    exact (congrFun this j).trans (h0 j hj)
  · exact fun h0 σ n hn i hi => ⟨_, fun j hj => h0 _ ⟨σ, n, hn, i, j, hi, hj, rfl⟩, hA' σ i⟩

theorem exists_lift_j (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (i : Idx H p) {T : Scheme.{0}} (x : T ⟶ (Y i).X)
    (h : Set.range x ⊆ Set.range (Y i).j) : ∃ y, y ≫ (Y i).j = x := by
  have := isDiscreteValuationRing_V i.c W hp hW
  obtain ⟨-, -, -, hj₁, hj₂, -⟩ := genericPart_dense_proOpen (i.c.V W) i.c.F _ _ (Y i).s (Y i).jQ
    (Y i).flat (Y i).proj (Y i).jQ_open (Y i).jQ_dense
  have : IsPreimmersion (Y i).j := hj₁
  have : Flat (Y i).j := hj₂
  exact HomExt.exists_lift_of_range_subset _ x h

theorem isProper_π (Z : Mdl Y i₀) : IsProper Z.π := by
  have : IsProper (Y Z.i).s := JoinModels.isProper_of_proj (Y Z.i).proj
  have : IsProper (Z.π ≫ (Y Z.i).s) := by
    rw [Z.π_s]; exact JoinModels.isProper_of_proj ⟨_, _, inferInstance, rfl⟩
  exact IsProper.of_comp _ (Y Z.i).s

theorem isLocallyNoetherian (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : IsLocallyNoetherian Z.X := by
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  have : IsProper Z.s := JoinModels.isProper_of_proj ⟨_, _, inferInstance, rfl⟩
  exact LocallyOfFiniteType.isLocallyNoetherian Z.s

variable {r : (Xo Z₁.i.l).XF Z₁.i.c ⟶ (Xo Z₂.i.l).XF Z₂.i.c} (hr : (Y Z₁.i).j ≫ τ = r ≫ (Y Z₂.i).j)

include hc hb hτ hr in

theorem exists_local_equations {P : Scheme.{0}} (q₁ : P ⟶ Z₁.X) (q₂ : P ⟶ Z₂.X) (hq : q₂ ≫ Z₂.π = q₁ ≫ Z₁.π ≫ τ)
    (ho : ∀ x, q₁ x ∈ Z₁.opn) (x : P) :
    ∃ (R : Type) (_ : CommRing R) (ι : Sp R ⟶ P) (J : Set R), IsOpenImmersion ι ∧ x ∈ Set.range ι ∧
      ∀ (k : Type) [Field k] (ψ : R →+* k), Rel mu ((spMap ψ ≫ ι) ≫ q₁) ((spMap ψ ≫ ι) ≫ q₂) ↔ ∀ r ∈ J, ψ r = 0 := by
  have m₁ := ho x
  have m₂ : q₂ x ∈ Z₂.opn := by
    obtain ⟨y, hy⟩ := m₁
    refine ⟨r y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hr, ← Scheme.Hom.comp_apply, hq]
    simp only [Scheme.Hom.comp_apply, hy]
  rw [← Z₁.cover] at m₁
  rw [← Z₂.cover] at m₂
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 m₁
  obtain ⟨a₂, ha₂⟩ := Set.mem_iUnion.1 m₂
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := q₁ ⁻¹ᵁ (Z₁.U a).1 ⊓ q₂ ⁻¹ᵁ (Z₂.U a₂).1) ⟨ha, ha₂⟩
  have hm : ∀ y, hV.fromSpec y ∈ V := fun y => hV.range_fromSpec.le ⟨y, rfl⟩
  obtain ⟨φ, hφ⟩ := Z₁.exists_chart_fac (R := Γ(P, V)) (hV.fromSpec ≫ q₁) a (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (hle (hm y)).1)
  obtain ⟨φ₂, hφ₂⟩ := Z₂.exists_chart_fac (R := Γ(P, V)) (hV.fromSpec ≫ q₂) a₂ (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact (hle (hm y)).2)
  obtain ⟨J, hJ⟩ := exists_equations mu hc hb hτ (φ := φ) (φ₂ := φ₂) (by
    rw [reassoc_of% hφ, reassoc_of% hφ₂, hq])
  refine ⟨Γ(P, V), inferInstance, hV.fromSpec, J, hV.isOpenImmersion_fromSpec, hV.range_fromSpec.ge hxV,
    fun k _ ψ => ?_⟩
  rw [← hJ, hφ, hφ₂, Category.assoc, Category.assoc]

include hc hb hτ hr in

theorem existsUnique_rel (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) {k : Type} [Field k] (w : Sp k ⟶ Z₁.X)
    (hw : Set.range w ⊆ Z₁.opn) : ∃! w₂ : Sp k ⟶ Z₂.X, w₂ ≫ Z₂.π = w ≫ Z₁.π ≫ τ ∧ Rel mu w w₂ := by
  obtain ⟨y, hy⟩ := exists_lift_j hp hW Z₁.i (w ≫ Z₁.π) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hw ⟨x, rfl⟩)
  obtain ⟨a, φ, rfl⟩ := Z₁.exists_chart w hw
  have hyr : (y ≫ r) ≫ (Y Z₂.i).j = spMap φ ≫ Z₁.chart a ≫ Z₁.π ≫ τ := by
    rw [Category.assoc, ← hr, reassoc_of% hy]
  obtain ⟨g, hg⟩ : ∃ g : Z₂.i.c.F →+* k, spMap g = (y ≫ r) ≫ pullback.snd _ _ :=
    exists_spMap _
  have hg' : g = (φ.comp (Z₁.alg a)).comp (IntermediateField.inclusion hc.2.1).toRingHom :=
    coeff_ext (W := W) (by rw [← local_model_chart_section_comp hc hb hτ, ← reassoc_of% hyr, j_s, ← spMap_comp', hg]; simp only [Category.assoc])
  have fr := (frame_at Z₁ a φ).push hc.2.1 mu
  simp only [Category.assoc] at fr
  rw [← hyr, ← hg'] at fr
  obtain ⟨w₂, ⟨h₁, h₂⟩, hu⟩ := Z₂.bij k g (y ≫ r) hg.symm _ fr
  rw [Category.assoc]
  exact ⟨w₂, ⟨h₁.trans hyr, a, φ, rfl, h₂⟩, fun w' h => hu _ ⟨h.1.trans hyr.symm, h.2.flagAt mu hc hb hτ h.1⟩⟩

theorem exists_hom_of_rel {U Z B : Scheme.{0}} (u : U ⟶ B) (π : Z ⟶ B) [IsProper π] [IsLocallyNoetherian U]
    (hU : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme U) (Q : ∀ (k : Type) [Field k], (Sp k ⟶ U) → (Sp k ⟶ Z) → Prop)
    (h₁ : ∀ x : ↥(pullback u π), ∃ (R : Type) (_ : CommRing R) (ι : Sp R ⟶ pullback u π) (J : Set R),
      IsOpenImmersion ι ∧ x ∈ Set.range ι ∧ ∀ (k : Type) [Field k] (ψ : R →+* k),
        Q k ((spMap ψ ≫ ι) ≫ pullback.fst u π) ((spMap ψ ≫ ι) ≫ pullback.snd u π) ↔ ∀ r ∈ J, ψ r = 0)
    (h₂ : ∀ (k : Type) [Field k] (w : Sp k ⟶ U), ∃! w₂ : Sp k ⟶ Z, w₂ ≫ π = w ≫ u ∧ Q k w w₂) :
    ∃ g : U ⟶ Z, g ≫ π = u ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ U), Q k w (w ≫ g) := by
  obtain ⟨S, c, hc₁, hS, hQ⟩ := exists_closed _ (fun k _ z => Q k (z ≫ pullback.fst u π) (z ≫ pullback.snd u π)) h₁
  have : IsIso (c ≫ pullback.fst u π) := by
    refine GlobalTheory.isIso_of_isProper_of_existsUnique_field_point _ _ _ inferInstance hS hU inferInstance fun k _ w => ?_
    obtain ⟨w₂, ⟨e, hq⟩, hu⟩ := h₂ k w
    obtain ⟨z, hz⟩ := (hQ k (pullback.lift w w₂ e.symm)).1 (by rwa [pullback.lift_fst, pullback.lift_snd])
    refine ⟨z, show z ≫ c ≫ _ = w by rw [reassoc_of% hz, pullback.lift_fst],
      fun z' (hz' : z' ≫ c ≫ pullback.fst u π = w) => ?_⟩
    have hrel := (hQ k (z' ≫ c)).2 ⟨z', rfl⟩
    rw [Category.assoc, hz'] at hrel
    rw [← cancel_mono c, hz]
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, hz']
    · rw [pullback.lift_snd]
      exact hu _ ⟨by rw [← hz']; simp only [Category.assoc, pullback.condition], hrel⟩
  refine ⟨inv (c ≫ pullback.fst u π) ≫ c ≫ pullback.snd u π, ?_, fun k _ w => ?_⟩
  · rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc c, IsIso.inv_hom_id_assoc]
  · have h := (hQ k ((w ≫ inv (c ≫ pullback.fst u π)) ≫ c)).2 ⟨_, rfl⟩
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using h

theorem exists_natMap (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (h2 : N2 Y) (hc : GlobalTheory.LocM.Corr Z₁ Z₂)
    (U : Z₁.X.Opens) (hU : (U : Set Z₁.X) = Z₁.opn) :
    ∃ (b : Z₂.i.c.V W →+* Z₁.i.c.V W) (g : U.toScheme ⟶ Z₂.X), g ≫ Z₂.s = U.ι ≫ Z₁.s ≫ spMap b ∧
      ∀ (k : Type) [Field k] (w : Sp k ⟶ U.toScheme), NatImg Z₁ Z₂ (w ≫ U.ι) (w ≫ g) := by
  obtain ⟨τ, mu, hT⟩ := exists_isTrans h2 hc.1 hc.2.1
  obtain ⟨b, π', r, hb, e₁, e₂, -, hr, -⟩ := id hT
  have hτ : τ ≫ (Y Z₂.i).s = (Y Z₁.i).s ≫ spMap b := by
    rw [← e₁, ← e₂, Category.assoc, Category.assoc, pullback.condition]
  have := isProper_π Z₂
  have := isLocallyNoetherian hp hW Z₁
  have hUo : ∀ x : U.toScheme, U.ι x ∈ Z₁.opn := fun x => by
    rw [← hU, ← U.range_ι]
    exact ⟨x, rfl⟩
  obtain ⟨g, hg, hQ⟩ := exists_hom_of_rel (U.ι ≫ Z₁.π ≫ τ) Z₂.π
    (JoinModels.isNormalScheme_of_flat_preimmersion U.ι (normal Z₁)) (fun k _ w w₂ => Rel mu (w ≫ U.ι) w₂)
    (fun x => by
      simpa only [Category.assoc] using exists_local_equations mu hc hb hτ hr (pullback.fst _ _ ≫ U.ι) (pullback.snd _ _)
        (by rw [← pullback.condition, Category.assoc]) (fun x => by rw [Scheme.Hom.comp_apply]; exact hUo _) x)
    fun k _ w => by
      simpa only [Category.assoc] using existsUnique_rel mu hc hb hτ hr hp hW (w ≫ U.ι) (by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Hom.comp_apply]
        exact hUo _)
  refine ⟨b, g, ?_, fun k _ w => ?_⟩
  · rw [← Z₂.π_s, reassoc_of% hg, hτ, reassoc_of% Z₁.π_s]
  · obtain ⟨a, φ, h₁, h₂⟩ := hQ k w
    refine ⟨τ, mu, (Z₁.fr a).bc φ, hT, by rw [Category.assoc, hg, Category.assoc], ?_, h₂⟩
    rw [← h₁]
    exact flagAt_chart Z₁ a φ

theorem isDiag_diagCl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), N2 Y → ∀ Z₁ Z₂ : Mdl Y i₀, GlobalTheory.LocM.Corr Z₁ Z₂ → IsDiag Z₁ Z₂ (diagCl Z₁ Z₂) := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ h2 Z₁ Z₂ hc
  have hex : ∃ Z', IsDiag Z₁ Z₂ Z' := by
    let U : Z₁.X.Opens := ⨆ a, (Z₁.U a).1
    have hU : (U : Set Z₁.X) = Z₁.opn := by
      rw [← Z₁.cover]; exact TopologicalSpace.Opens.coe_iSup _
    obtain ⟨b, g, hg, hn⟩ := exists_natMap hp hW h2 hc U hU
    have := isDiscreteValuationRing_V Z₁.i.c W hp hW
    obtain ⟨X', f₁, f₂, j, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.GraphClosure.exists_normalised_graph_closure _ _ b _ _ Z₁.s Z₂.s U g
      ⟨_, _, inferInstance, rfl⟩ ⟨_, _, inferInstance, rfl⟩ (normal Z₁) Z₁.flat hg
    obtain ⟨Z', e, e1, e2, hm⟩ := GlobalTheory.LocM.Recode.exists_model_of_modification E H Dw Xo p W Y i₀ Z₁ X' f₁ U j hU h1 h2 h3 h4 h5
    refine ⟨Z', e1, e2, e.hom ≫ f₁, e.hom ≫ f₂,
      hm Z₁ f₁ ⟨⟨dvd_rfl, le_rfl, dvd_rfl⟩, le_rfl, fun _ => subset_rfl⟩ fun k _ w => ?_,
      hm Z₂ f₂ hc fun k _ w => h6 ▸ hn k w, ?_⟩
    · rw [h4.w, Category.id_comp]
      refine natImg_refl Z₁ _ ?_
      rintro _ ⟨x, rfl⟩
      rw [← hU]
      exact (w x).2
    · rw [← prod.comp_lift]
      infer_instance
  rw [diagCl, dif_pos hex]
  exact hex.choose_spec

end GlobalTheory.LocM.Diag
