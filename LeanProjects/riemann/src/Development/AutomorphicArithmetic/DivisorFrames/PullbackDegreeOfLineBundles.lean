import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.CovCmp
import Development.AutomorphicArithmetic.DivisorFrames.PdegEqOfIsDeg
import Development.AutomorphicArithmetic.DivisorFrames.IntersectionNumberPullbackDegree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetDimDropClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSubschemePrimeFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.CovCmp
open scoped Classical

section
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.QCoh GlobalTheory.Twist

private theorem closure_eq_top {X : Scheme.{0}} [IsLocallyNoetherian X] {A : LB X}
    (hA : IsAmpleLB A) {S : Set X} (hS : S.Finite) :
    AddSubgroup.closure {c : Pic X | ∃ (N : LB X) (hN : N.IsLB) (t : N.Sec),
      S ⊆ nonzeroLocus t ∧ c = cls N hN} = ⊤ := by
  refine eq_top_iff.2 fun c _ => ?_
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨n, h₁, h₂⟩ := ((hA.eventually_exists_finite_subset_nonzeroLocus hM hS).and
    (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv X) hS)).exists
  obtain ⟨P, hP, eP⟩ := cls_surj (cls M hM + n • cls A hA.isLB)
  obtain ⟨Q, hQ, eQ⟩ := cls_surj (cls _ (LB.isLB_triv X) + n • cls A hA.isLB)
  obtain ⟨s, hs⟩ := h₁ P hP eP
  obtain ⟨t, ht⟩ := h₂ Q hQ eQ
  have e : cls M hM = cls P hP - cls Q hQ := by
    rw [eP, eQ, cls_triv, zero_add, add_sub_cancel_right]
  rw [e]
  exact sub_mem (AddSubgroup.subset_closure ⟨P, hP, s, hs, rfl⟩)
    (AddSubgroup.subset_closure ⟨Q, hQ, t, ht, rfl⟩)

private theorem diffVanish_pull {k : Type} [Field k] {X X' : Scheme.{0}} [IsLocallyNoetherian X]
    [AlgebraicGeometry.IsNoetherian X'] [Algebra k Γ(X', ⊤)] (f : X' ⟶ X) {A : LB X} (hA : IsAmpleLB A) (n : ℕ) :
    ∀ (F : X'.Modules) [IsFiniteQC F], FiniteCohTwists k F → ∀ S : Set X, IsClosed S →
      (∀ x ∈ support F, f x ∈ S) → topologicalKrullDim S < n → DiffVanish n (chiPic k F ∘ pull f) := by
  have := hA.noetherianSpace
  induction n with
  | zero =>
    intro F _ hF S hS hFS hn
    have hS0 : IsEmpty S := by
      rw [← topologicalKrullDim_eq_bot_iff]
      exact (WithBot.lt_zero_iff_eq_bot _).1 hn
    have h0 : support F = ∅ := Set.eq_empty_iff_forall_notMem.2 fun x hx => hS0.false ⟨_, hFS x hx⟩
    rw [diffVanish_zero_iff]
    funext c
    obtain ⟨M, hM, e⟩ := cls_surj (pull f c)
    rw [Function.comp_apply, ← e]
    exact chi_eq_zero_of_isZero k ((isZero_twist_iff hM).2 (support_eq_empty_iff.1 h0))
  | succ n ih =>
    intro F _ hF S hS hFS hn
    obtain ⟨S₃, hS₃, hS₃'⟩ := GlobalTheory.T.exists_finite_set_dim_drop_closed S hS
    have hT : (f '' assPoints F ∪ S₃).Finite := ((finite_assPoints F).image _).union hS₃
    refine diffVanish_of_generators (closure_eq_top hA hT) fun g hg => ?_
    obtain ⟨N, hN, t, hSt, e⟩ := hg 0
    have hN' := Semi.LB.isLB_pull hN f
    haveI : Mono (cutHom F hN' (GlobalTheory.secPull t f)) :=
      (mono_cutHom_iff F hN' _).2 fun x hx => by
        rw [GlobalTheory.nonzeroLocus_secPull]
        exact hSt (Or.inl ⟨x, hx, rfl⟩)
    have key : bwdDiff (cls N hN) (chiPic k F ∘ pull f) = chiPic k (cut F hN' (GlobalTheory.secPull t f)) ∘ pull f := by
      funext c
      rw [← bwdDiff_chiPic_eq_chiPic_cut hN' _ hF]
      simp only [bwdDiff_apply, Function.comp_apply, map_sub, cls_pull hN f hN']
    rw [← Fin.cons_self_tail g, multiDiff_cons', e, key]
    refine ih _ (hF.cut hN' _) (S ∩ (nonzeroLocus t : Set X)ᶜ) (hS.inter (nonzeroLocus t).isOpen.isClosed_compl)
      (fun x hx => ?_) ?_ _
    · rw [support_cut, GlobalTheory.nonzeroLocus_secPull] at hx
      exact ⟨hFS x hx.1, hx.2⟩
    · have := (hS₃' (nonzeroLocus t : Set X)ᶜ (nonzeroLocus t).isOpen.isClosed_compl
        (Set.disjoint_compl_right_iff_subset.2 fun x hx => hSt (Or.inr hx))).trans_lt hn
      by_contra hc
      rw [not_lt] at hc
      refine this.not_ge ?_
      push_cast
      exact add_le_add_left hc 1

private theorem interNum_pull_eq_zero {k : Type} [Field k] {X X' : Scheme.{0}} [IsLocallyNoetherian X]
    [Algebra k Γ(X', ⊤)] (hp : IsProjOver (strHom k X')) (f : X' ⟶ X) {A : LB X} (hA : IsAmpleLB A) {n : ℕ}
    {S : Set X} (hS : IsClosed S) (hf : ∀ x, f x ∈ S) (hn : topologicalKrullDim S < n) {L : Fin n → LB X}
    (hL : ∀ i, (L i).IsLB) : interNum k (GlobalTheory.structureModule X') (fun i => (L i).pull f) = 0 := by
  have := isNoetherian_of_isProjOver hp
  have H := diffVanish_pull f hA n (GlobalTheory.structureModule X')
    (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k X') _ hp) S hS (fun x _ => hf x) hn
  have h := congrFun (H fun i => cls (L i) (hL i)) 0
  rw [multiDiff_comap] at h
  rw [interNum_eq_multiDiff k _ fun i => pull_isLB (hL i) f]
  simpa [cls_pull (hL _) f, Function.comp_def] using h

end

private theorem trdeg_residueField_eq (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (d : ℕ)
    (hd : topologicalKrullDim X = d) (x : X) (hx : x = genericPoint X) :
    letI := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    Algebra.trdeg k (X.residueField x) = d := by
  subst hx
  letI := (Spec.preimage (X.fromSpecResidueField (genericPoint X) ≫ f)).hom.toAlgebra
  letI : Algebra k X.functionField := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ f)).hom.toAlgebra
  obtain ⟨A, _, _, _, _, _, j, _, -, -, hA⟩ := GlobalTheory.exists_affine_chart_trdeg_eq f (genericPoint X)
  obtain ⟨e, he⟩ := GlobalTheory.exists_trdeg_eq_natCast k (A := A)
  rw [hA] at he
  have h1 := GlobalTheory.topologicalKrullDim_preimage_genericPoint_eq f he
  have h2 : (f ⁻¹' {genericPoint (Spec (CommRingCat.of k))} : Set X) = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
  rw [h2, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph, hd] at h1
  obtain rfl : d = e := by exact_mod_cast h1
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  have hc : Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ f) ≫ X.residue _ =
      Spec.preimage (X.fromSpecResidueField (genericPoint X) ≫ f) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Scheme.fromSpecResidueField, Category.assoc]
  let ε : X.functionField ≃ₐ[k] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun a => congr($(hc).hom a) }
  exact ε.trdeg_eq.symm.trans he

private theorem residueDegree_ne_zero (k : Type) [Field k] {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    (s : X ⟶ Spec (CommRingCat.of k)) (f : X' ⟶ X) [LocallyOfFiniteType s] [LocallyOfFiniteType f] (d : ℕ)
    (hd : topologicalKrullDim X = d) (hd' : topologicalKrullDim X' = d)
    (hg : f (genericPoint X') = genericPoint X) : f.residueDegree (genericPoint X') ≠ 0 := by
  have h₁ := trdeg_residueField_eq k X s d hd _ hg
  have h₂ := trdeg_residueField_eq k X' (f ≫ s) d hd' _ rfl
  letI := (Spec.preimage (X.fromSpecResidueField (f (genericPoint X')) ≫ s)).hom.toAlgebra
  letI := (Spec.preimage (X'.fromSpecResidueField (genericPoint X') ≫ f ≫ s)).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint X')).hom.toAlgebra
  have hc : Spec.preimage (X.fromSpecResidueField (f (genericPoint X')) ≫ s) ≫ f.residueFieldMap _ =
      Spec.preimage (X'.fromSpecResidueField (genericPoint X') ≫ f ≫ s) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
  haveI : IsScalarTower k (X.residueField (f (genericPoint X'))) (X'.residueField (genericPoint X')) :=
    IsScalarTower.of_algebraMap_eq fun a => congr($(hc).hom a).symm
  have h₃ := trdeg_add_eq k (X.residueField (f (genericPoint X'))) (A := X'.residueField (genericPoint X'))
  rw [h₁, h₂] at h₃
  have h₄ : Algebra.trdeg (X.residueField (f (genericPoint X'))) (X'.residueField (genericPoint X')) = 0 :=
    Cardinal.eq_of_add_eq_add_left (h₃.trans (add_zero _).symm) (Cardinal.natCast_lt_aleph0)
  haveI := trdeg_eq_zero_iff.1 h₄
  haveI : Algebra.EssFiniteType (X.residueField (f (genericPoint X'))) (X'.residueField (genericPoint X')) := by
    have h : (f.stalkMap (genericPoint X') ≫ X'.residue _).hom.EssFiniteType :=
      (LocallyOfFiniteType.stalkMap f _).comp (RingHom.FiniteType.of_surjective _ (X'.residue_surjective _)).essFiniteType
    rw [← Scheme.residue_residueFieldMap] at h
    exact RingHom.EssFiniteType.of_comp _ h
  haveI := Algebra.finite_of_essFiniteType_of_isAlgebraic (F := X.residueField (f (genericPoint X'))) (E := X'.residueField (genericPoint X'))
  exact Module.finrank_pos.ne'

private theorem ord_pos {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {l : ℕ} (hl : (l : Γ(X, ⊤)) ≠ 0)
    {z : X} (hz : Order.coheight z = 1) (h : z ∉ X.basicOpen (l : Γ(X, ⊤))) :
    0 < Scheme.ord (l : X.functionField) z := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have h₀ : (l : X.presheaf.stalk z) ≠ 0 := fun e =>
    hl (germ_injective_of_isIntegral X (U := ⊤) z trivial (by rw [map_natCast, map_zero, e]))
  have h₁ : ¬ IsUnit (l : X.presheaf.stalk z) := fun e =>
    h ((X.mem_basicOpen (U := ⊤) _ z trivial).2 (by rwa [map_natCast]))
  have h₂ : (l : X.functionField) = algebraMap (X.presheaf.stalk z) X.functionField l := (map_natCast _ _).symm
  have h₃ : (l : X.functionField) ≠ 0 := by
    rw [h₂]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 h₀
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero h₀))
  have h₄ : Scheme.ord (l : X.functionField) z = m := by
    rw [Scheme.ord_eq_iff hz h₃, Scheme.ordHom, h₂, Ring.ordFrac_eq_ord _ h₀]
    exact Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero h₀) hm.symm
  rw [h₄]
  refine Int.natCast_pos.2 (Nat.pos_of_ne_zero fun e => h₁ ?_)
  rw [e, Nat.cast_zero, eq_comm, Ring.ord, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top] at hm
  exact hm

private theorem dim_closure_lt {X : Scheme.{0}} [IsIntegral X] {d : ℕ} (hd : topologicalKrullDim X = (d + 1 : ℕ))
    {z : X} (h₀ : z ≠ genericPoint X) (h₁ : Order.coheight z ≠ 1) :
    topologicalKrullDim (closure ({z} : Set X)) < d := by
  have hgen : ∀ x : X, x ≠ genericPoint X → genericPoint X ∉ closure ({x} : Set X) := fun x hx h =>
    hx ((genericPoint_specializes x).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
  obtain ⟨x, hx, hx'⟩ : ∃ x : X, z < x ∧ x ≠ genericPoint X := by
    by_contra hc
    push Not at hc
    have hlt : z < genericPoint X := ⟨genericPoint_specializes z, fun h => hgen z h₀ (specializes_iff_mem_closure.1 h)⟩
    refine h₁ (le_antisymm ?_ (le_add_self.trans (Order.coheight_add_one_le hlt)))
    rw [Order.coheight_eq_iSup_gt_coheight]
    refine iSup₂_le fun y hy => ?_
    rw [hc y hy, Order.coheight_eq_zero.2 (fun y _ => genericPoint_specializes y), zero_add]
  have hX1 : topologicalKrullDim (Set.univ : Set X) = (d + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hd
  have a₁ : topologicalKrullDim (closure ({x} : Set X)) + 1 ≤ (d + 1 : ℕ) :=
    hX1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun y _ => ⟨genericPoint X, trivial, hgen x hx', genericPoint_specializes y⟩
  have a₂ : topologicalKrullDim (closure ({z} : Set X)) + 1 ≤ topologicalKrullDim (closure ({x} : Set X)) :=
    topologicalKrullDim_add_one_le isClosed_closure isClosed_closure
      fun y hy => ⟨x, subset_closure rfl, fun h => hx.2 (specializes_iff_mem_closure.2 h),
        Specializes.trans hx.1 (specializes_iff_mem_closure.2 hy)⟩
  have a₃ : topologicalKrullDim (closure ({x} : Set X)) ≤ d :=
    ENat.WithBot.add_le_add_one_right_iff.1 (a₁.trans_eq (Nat.cast_succ d))
  by_contra hc
  rw [not_lt] at hc
  have a₄ : (d : WithBot ℕ∞) + 1 ≤ d := (add_le_add_left hc 1).trans (a₂.trans a₃)
  have a₅ : d + 1 ≤ d := by exact_mod_cast a₄
  omega

private theorem range_eq_closure {X Z : Scheme.{0}} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i] :
    Set.range i = closure {i (genericPoint Z)} := by
  have h₁ := (genericPoint_spec Z).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  exact h₁.def.symm

private theorem interNum_pull_pull {k : Type} [Field k] {X Y Z : Scheme.{0}} [Algebra k Γ(Z, ⊤)] (f : Z ⟶ Y) (g : Y ⟶ X)
    {d : ℕ} {N : Fin d → LB X} (hN : ∀ j, (N j).IsLB) :
    interNum k (structureModule Z) (fun j => ((N j).pull g).pull f) =
      interNum k (structureModule Z) (fun j => (N j).pull (f ≫ g)) := by
  refine interNum_congr_cls _ _ (fun j => pull_isLB (pull_isLB (hN j) g) f) (fun j => pull_isLB (hN j) _) fun j => ?_
  refine (cls_pull (pull_isLB (hN j) g) f _).trans ?_
  refine Eq.trans ?_ (cls_pull (hN j) _ _).symm
  refine (congrArg (pull f) (cls_pull (hN j) g _)).trans ?_
  exact (pull_comp f g (cls (N j) (hN j))).symm

theorem UpperTheory.pullback_degree_of_line_bundles :
    ∀ (R : Type) [CommRing R] (X X' : Scheme.{0}) (q : X ⟶ Sp R) (q' : X' ⟶ Sp R) (d : ℕ), IsArithVar q d → IsArithVar q' d → ∀ (g : X' ⟶ X), g ≫ q = q' → ∀ (p : ℕ) [Fact p.Prime] (N : Fin d → LB X), (∀ k, (N k).IsLB) → ∀ ζ : X', (p : R) ∈ (q' ζ).asIdeal → Order.coheight ζ = 1 → pdeg p (fun k => (N k).pull g) ζ = if Order.coheight (g ζ) = 1 then (g.residueDegree ζ : ℤ) * pdeg p N (g ζ) else 0 := by
  intro R _ X X' q q' d hQ hX' g _ p hp N hN ζ hpζ hζ
  have := hQ.isIntegral
  have := hQ.isNoetherian
  have := hQ.charZero
  have := hX'.isIntegral
  have := hX'.isNoetherian
  have := hX'.charZero
  have hζp : ζ ∉ X'.basicOpen (p : Γ(X', ⊤)) := fun h => by
    have h₃ : ζ ∈ q' ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (p : R)) := by
      rwa [Scheme.preimage_basicOpen_top, map_natCast, map_natCast]
    have h₁ : q' ζ ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (p : R)) := h₃
    rw [basicOpen_eq_of_affine] at h₁
    exact h₁ hpζ
  have hηp : g ζ ∉ X.basicOpen (p : Γ(X, ⊤)) := fun h => by
    refine hζp ?_
    rw [← map_natCast g.appTop.hom]
    exact (Scheme.preimage_basicOpen_top g (p : Γ(X, ⊤))).le h
  have hp0 : (p : Γ(X, ⊤)) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hp0' : (p : Γ(X', ⊤)) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hproj : ∀ (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)],
      i (genericPoint Z) = ζ → IsProjOver (strHom (ZMod p) Z) := fun Z i _ _ _ _ =>
    GlobalTheory.T.closed_subscheme_mod_l_projective _ _ _ _ hX' _ i p
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hQ.isProjOver).1
  split_ifs with hη
  · obtain ⟨Z, i, _, _, hz⟩ := exists_isClosedImmersion_genericPoint ζ
    have hZl : (p : Γ(Z, ⊤)) = 0 := by
      rw [← basicOpen_eq_bot_iff]
      by_contra hne
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
      have h1 := ((genericPoint_spec Z).mem_open_set_iff (Z.basicOpen (p : Γ(Z, ⊤))).isOpen).2 ⟨x, trivial, hx⟩
      rw [← map_natCast i.appTop.hom] at h1
      exact hζp (hz ▸ (Scheme.preimage_basicOpen_top i (p : Γ(X', ⊤))).ge h1)
    have : CharP Γ(Z, ⊤) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hZl
    letI inst : Algebra (ZMod p) Γ(Z, ⊤) := ZMod.algebra _ p
    have hZ := hproj Z i hz
    have : IsProper (strHom (ZMod p) Z) := (isProper_and_exists_isAmpleLB_of_isProjOver hZ).1
    have := isNoetherian_of_isProjOver hZ
    let γ := i ≫ g
    have : QuasiCompact γ := inferInstance
    let φ : Z ⟶ γ.image := γ.toImage
    have e : φ ≫ γ.imageι = γ := γ.toImage_imageι
    have hdense : DenseRange φ := γ.toImage.denseRange
    have hgen : φ (genericPoint Z) = genericPoint γ.image := by
      have h₁ := (genericPoint_spec Z).image φ.continuous
      rw [Set.image_univ, hdense.closure_range] at h₁
      exact h₁.eq (genericPoint_spec _)
    have hz' : γ.imageι (genericPoint γ.image) = g ζ := by
      rw [← hgen, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, hz]
    have hinj := ArInt.appTop_injective_of_denseRange φ hdense
    have : CharP Γ(γ.image, ⊤) p := φ.appTop.hom.charP hinj p
    letI inst' : Algebra (ZMod p) Γ(γ.image, ⊤) := ZMod.algebra _ p
    have hZ' := GlobalTheory.T.closed_subscheme_mod_l_projective _ _ _ _ hQ _ γ.imageι p
    have : IsProper (strHom (ZMod p) γ.image) := (isProper_and_exists_isAmpleLB_of_isProjOver hZ').1
    have hs : φ ≫ strHom (ZMod p) γ.image = strHom (ZMod p) Z := by
      letI := algebraΓOfHom (φ ≫ strHom (ZMod p) γ.image)
      refine (strHom_eq fun _ => rfl).symm.trans ?_
      congr 1
      exact Subsingleton.elim _ _
    have : IsProper (φ ≫ strHom (ZMod p) γ.image) := hs ▸ inferInstance
    have : IsProper φ := .of_comp φ (strHom (ZMod p) γ.image)
    have hd' : topologicalKrullDim γ.image = d := by
      obtain ⟨W, j, _, _, _, hj, hW⟩ := GlobalTheory.T.exists_integral_subscheme_prime_fibre _ _ _ _ hQ p _ (ord_pos hp0 hη hηp)
      rw [← hW, ← topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding (range_eq_closure j),
        ← topologicalKrullDim_eq_of_isEmbedding γ.imageι.isClosedEmbedding.isEmbedding (range_eq_closure _), hj, hz']
    have hd : topologicalKrullDim Z = d := by
      obtain ⟨W, j, _, _, _, hj, hW⟩ := GlobalTheory.T.exists_integral_subscheme_prime_fibre _ _ _ _ hX' p _ (ord_pos hp0' hζ hζp)
      rw [← hW, ← topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding (range_eq_closure j),
        ← topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding (range_eq_closure _), hj, hz]
    have hdeg : φ.residueDegree (genericPoint Z) = g.residueDegree ζ := by
      have a₁ := CurveDegreesCompare.residueDegree_comp φ γ.imageι (genericPoint Z)
      have a₂ := CurveDegreesCompare.residueDegree_comp i g (genericPoint Z)
      rw [ProperCut.residueDegree_of_isClosedImmersion γ.imageι, one_mul, e] at a₁
      rw [ProperCut.residueDegree_of_isClosedImmersion i, mul_one, hz] at a₂
      exact a₁.symm.trans a₂
    have H := UpperTheory.intersection_number_pullback_degree (ZMod p) _ _ (strHom (ZMod p) γ.image) φ d hZ' (hs ▸ hZ) hd' hgen
      (residueDegree_ne_zero (ZMod p) (strHom (ZMod p) γ.image) φ d hd' hd hgen) (fun k => (N k).pull γ.imageι)
      fun k => pull_isLB (hN k) _
    rw [Subsingleton.elim (algebraΓOfHom (φ ≫ strHom (ZMod p) γ.image)) inst,
      Subsingleton.elim (algebraΓOfHom (strHom (ZMod p) γ.image)) inst', interNum_pull_pull _ _ hN, e, hdeg] at H
    rw [UpperTheory.pdeg_eq_of_isDeg p X' d _ (fun k => pull_isLB (hN k) g) ζ _ ⟨Z, i, ‹_›, ‹_›, inst, hz, hd, rfl⟩,
      UpperTheory.pdeg_eq_of_isDeg p X d N hN _ _ ⟨_, γ.imageι, inferInstance, inferInstance, inst', hz', hd', rfl⟩,
      interNum_pull_pull _ _ hN]
    exact H
  · rw [pdeg]
    split_ifs with h
    · obtain ⟨Z, i, _, _, _, hz, -, ha⟩ := h.choose_spec
      rw [ha, interNum_pull_pull _ _ hN]
      obtain ⟨A, hA⟩ := (isProper_and_exists_isAmpleLB_of_isProjOver hQ.isProjOver).2
      refine interNum_pull_eq_zero (hproj Z i hz) _ hA (S := closure {g ζ}) isClosed_closure (fun x => ?_)
        (dim_closure_lt hQ.dim_eq (fun e => hηp ?_) hη) hN
      · rw [← hz, ← Scheme.Hom.comp_apply]
        exact specializes_iff_mem_closure.1 ((genericPoint_specializes x).map (i ≫ g).continuous)
      · obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 (mt (basicOpen_eq_bot_iff _).1 hp0)
        rw [e]
        exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (p : Γ(X, ⊤))).isOpen).2 ⟨x, trivial, hx⟩
    · rfl
