import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapCompSpMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionGenericComplexFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightEqOfMemMinimalPrimesMap
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
open GlobalTheory.HorComp

set_option autoImplicit false

namespace GlobalTheory.HorComp

section Algebra

open TensorProduct ReciprocityTheory.CA

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem height_comap_le_one_of_flat (O K A : Type) [CommRing O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [Module.Flat O K] [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A]
    (P Q : Ideal (K ⊗[O] A)) (f : K ⊗[O] A) (hP : P ∈ minimalPrimes (K ⊗[O] A))
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    (Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[O] K ⊗[O] A)).height ≤ 1 := by
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType O A)
  haveI : Module.Flat (MvPolynomial (Fin n) O) (MvPolynomial (Fin n) K) :=
    Module.Flat.isBaseChange O (MvPolynomial (Fin n) O) K (MvPolynomial (Fin n) K)
      (Algebra.IsPushout.out (R := O) (S := MvPolynomial (Fin n) O) (R' := K)
        (S' := MvPolynomial (Fin n) K))
  let e := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) O K).toRingEquiv
  let m := Algebra.TensorProduct.map (AlgHom.id O K) π
  have hm : Function.Surjective m :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hπ
  have he : ∀ p : MvPolynomial (Fin n) O,
      e.symm (algebraMap _ (MvPolynomial (Fin n) K) p) = 1 ⊗ₜ p := by
    intro p
    rw [RingEquiv.symm_apply_eq]
    simp [e, MvPolynomial.algebraTensorAlgEquiv_tmul]
  have hkm : RingHom.ker m = (RingHom.ker π).map
      (Algebra.TensorProduct.includeRight : _ →ₐ[O] K ⊗[O] MvPolynomial (Fin n) O) :=
    Algebra.TensorProduct.lTensor_ker π hπ
  refine GlobalTheory.FieldExtHeight.height_comap_le_one (S := MvPolynomial (Fin n) K) π.toRingHom
    (m.toRingHom.comp e.symm.toRingHom)
    (Algebra.TensorProduct.includeRight : A →ₐ[O] K ⊗[O] A).toRingHom hπ
    (hm.comp e.symm.surjective) ?_ ?_ ?_ P Q f hP hQ
  · refine RingHom.ext fun p => ?_
    change m (e.symm (algebraMap _ _ p)) = 1 ⊗ₜ π p
    rw [he]
    simp [m]
  · have h1 : RingHom.ker (m.toRingHom.comp e.symm.toRingHom) = (RingHom.ker m).comap e.symm := rfl
    rw [h1, hkm, Ideal.comap_symm]
    have h2 : algebraMap (MvPolynomial (Fin n) O) (MvPolynomial (Fin n) K) = e.toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          _ →ₐ[O] K ⊗[O] MvPolynomial (Fin n) O).toRingHom := by
      apply RingHom.ext
      intro p
      exact (e.symm_apply_eq.mp (he p))
    rw [h2, ← Ideal.map_map]
    rfl
  · intro 𝔔 h𝔔
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔔 h𝔔.ne_top
    exact GlobalTheory.FinTypeIntCatenary.isCM_atPrime_of_le 𝔔 M hle
      (height_maximal_mvPolynomial_field K n M).1

end Algebra

open Limits TensorProduct in

theorem coheight_fst_le_one {O K : Type} [CommRing O] [IsNoetherianRing O] [Field K] [Algebra O K] [Module.Flat O K]
    {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp O) [LocallyOfFiniteType q] (V : Y.Opens) (f : Γ(Y, V))
    (c w : (pullback q (spMap (algebraMap O K)) : Scheme.{0})) (hc : ∀ c', c' ⤳ c → c ⤳ c') (hcw : c ⤳ w)
    (hV : pullback.fst q (spMap (algebraMap O K)) w ∈ V)
    (hf : pullback.fst q (spMap (algebraMap O K)) w ∉ Y.basicOpen f)
    (hw : ∀ w', c ⤳ w' → w' ⤳ w → pullback.fst q (spMap (algebraMap O K)) w' ∉ Y.basicOpen f → w ⤳ w') :
    Order.coheight (pullback.fst q (spMap (algebraMap O K)) w) ≤ 1 := by
  obtain ⟨U, hU, hx, hUV⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hx⟩⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ q)
  letI : Algebra O Γ(Y, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType O Γ(Y, U) := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hp := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct O K Γ(Y, U))).flip
  let r : Sp (K ⊗[O] Γ(Y, U)) ⟶ Spec Γ(Y, U) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : Γ(Y, U) →ₐ[O] K ⊗[O] Γ(Y, U)).toRingHom)
  let l : Sp (K ⊗[O] Γ(Y, U)) ⟶ Sp K :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[O] Γ(Y, U)))
  have hp' : IsPullback r l (hU.fromSpec ≫ q) (spMap (algebraMap O K)) := by
    rw [← hφ]; exact hp
  let h : Sp (K ⊗[O] Γ(Y, U)) ⟶ pullback q (spMap (algebraMap O K)) :=
    pullback.lift (r ≫ hU.fromSpec) l (by rw [Category.assoc]; exact hp'.w)
  have hh : IsPullback r h hU.fromSpec (pullback.fst q (spMap (algebraMap O K))) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
    rw [pullback.lift_snd]; exact hp'
  have ho : IsOpenImmersion h := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hh inferInstance
  have hfr : ∀ z, pullback.fst q (spMap (algebraMap O K)) (h z) = hU.fromSpec (r z) := fun z =>
    congrArg (fun g : Sp (K ⊗[O] Γ(Y, U)) ⟶ Y => g z) hh.w.symm
  obtain ⟨Q, rfl⟩ : w ∈ Set.range h := by
    obtain ⟨u, hu⟩ : pullback.fst q (spMap (algebraMap O K)) w ∈ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]; exact hx
    obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback hh u w hu
    exact ⟨z, hz⟩
  obtain ⟨P, rfl⟩ : c ∈ Set.range h := hcw.mem_open h.isOpenEmbedding.isOpen_range ⟨Q, rfl⟩
  have hs : ∀ a b : Sp (K ⊗[O] Γ(Y, U)), h a ⤳ h b ↔ a.asIdeal ≤ b.asIdeal := fun a b =>
    h.isOpenEmbedding.isInducing.specializes_iff.trans (PrimeSpectrum.le_iff_specializes a b).symm
  let g : Γ(Y, U) := Y.presheaf.map (homOfLE hUV).op f
  have hg : ∀ z, pullback.fst q (spMap (algebraMap O K)) (h z) ∉ Y.basicOpen f ↔ (1 : K) ⊗ₜ[O] g ∈ z.asIdeal := by
    intro z
    have h1 : hU.fromSpec (r z) ∈ U := by
      have := Set.mem_range_self (f := hU.fromSpec) (r z)
      rwa [hU.range_fromSpec] at this
    have h2 : hU.fromSpec (r z) ∈ Y.basicOpen g ↔ r z ∈ PrimeSpectrum.basicOpen g := by
      rw [← hU.fromSpec_preimage_basicOpen]; rfl
    rw [hfr, ← not_iff_not, not_not]
    refine Iff.trans ?_ h2
    simp only [g, Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h1, h⟩, fun h => h.2⟩
  have hP : P.asIdeal ∈ minimalPrimes (K ⊗[O] Γ(Y, U)) :=
    ⟨⟨P.2, bot_le⟩, fun J hJ hle => (hs P ⟨J, hJ.1⟩).1 (hc _ ((hs ⟨J, hJ.1⟩ P).2 hle))⟩
  have hQ : Q.asIdeal ∈ (P.asIdeal ⊔ Ideal.span {(1 : K) ⊗ₜ[O] g}).minimalPrimes := by
    refine ⟨⟨Q.2, sup_le ((hs _ _).1 hcw) ((Ideal.span_singleton_le_iff_mem _).2 ((hg Q).1 hf))⟩, fun J hJ hle => ?_⟩
    exact (hs Q ⟨J, hJ.1⟩).1 (hw _ ((hs P ⟨J, hJ.1⟩).2 (le_sup_left.trans hJ.2)) ((hs ⟨J, hJ.1⟩ Q).2 hle)
      ((hg ⟨J, hJ.1⟩).2 ((Ideal.span_singleton_le_iff_mem _).1 (le_sup_right.trans hJ.2))))
  have key := height_comap_le_one_of_flat O K Γ(Y, U) _ _ _ hP hQ
  rw [hfr, GlobalTheory.coheight_apply_of_isOpenImmersion, ← idealHeight_eq_coheight]
  exact key

open Limits in

theorem ptOf_up_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
    {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {Y : Scheme.{0}} {q : Y ⟶ Sp Oz}
    (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) (p : Sp ℂ ⟶ cxFib β q σ)
    (hp : p ≫ pullback.snd q (spMap (σ.comp β)) = 𝟙 _) (y : CxPts q (σ.comp β))
    (hy : y.1 = p ≫ pullback.fst q (spMap (σ.comp β))) :
    ptOf Z (up j hj σ y) = toGenCx j hj σ (p (IsLocalRing.closedPoint ℂ)) := by
  refine congrArg (fun g : Sp ℂ ⟶ genCx Z σ => g (IsLocalRing.closedPoint ℂ)) (a₂ := p ≫ toGenCx j hj σ) ?_
  have e1 : toGenCx j hj σ ≫ pullback.fst (genStr Z) (spMap σ) = toGen j hj σ := pullback.lift_fst _ _ _
  have e2 : toGenCx j hj σ ≫ pullback.snd (genStr Z) (spMap σ) = pullback.snd q (spMap (σ.comp β)) :=
    pullback.lift_snd _ _ _
  have e3 : toGen j hj σ ≫ pullback.fst Z.s (spMap β) = pullback.fst q (spMap (σ.comp β)) ≫ j :=
    pullback.lift_fst _ _ _
  have e4 : toGen j hj σ ≫ pullback.snd Z.s (spMap β) = pullback.snd q (spMap (σ.comp β)) ≫ spMap σ :=
    pullback.lift_snd _ _ _
  refine pullback.hom_ext ((pullback.lift_fst _ _ _).trans ?_) ((pullback.lift_snd _ _ _).trans ?_)
  · rw [Category.assoc, e1]
    refine pullback.hom_ext ((pullback.lift_fst _ _ _).trans ?_) ((pullback.lift_snd _ _ _).trans ?_)
    · rw [Category.assoc, e3, hy, Category.assoc]
    · rw [Category.assoc, e4, ← Category.assoc, hp, Category.id_comp]
  · rw [Category.assoc, e2, hp]

open Limits in

theorem exists_coheight_eq_one_of_maximal : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) [IsClosedImmersion jm] (hq : jm ≫ s.T.Z.s = q) (n : ℕ), IsArithVar q n → jm (genericPoint Y) ∈ abLocus s.T.Z.t.G → ∀ C ∈ irreducibleComponents (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ), ∀ W : Set (genCx s.T.Z σ), Maximal (fun W : Set (genCx s.T.Z σ) => _root_.IsIrreducible W ∧ W ⊆ toGenCx jm hq σ '' C ∩ bdCx s.T.Z σ) W → ∀ T : Set Y, IsClosed T → (∀ y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)), up jm hq σ y ∈ ptsOf s.T.Z W → y.1 (IsLocalRing.closedPoint ℂ) ∈ T) → ∃ v ∈ T, jm v ∉ abLocus s.T.Z.t.G ∧ CharZero (Y.residueField v) ∧ Order.coheight v = 1 := by
  intro D A N j S κ s x σ Y _ q jm hjm hq n hY hgen C hC W hW T hT hWT
  letI : Algebra (𝓞 κ.c.F) ℂ := (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)).toAlgebra
  have hinj : Function.Injective (algebraMap (𝓞 κ.c.F) ℂ) :=
    σ.injective.comp (IsFractionRing.injective (𝓞 κ.c.F) κ.c.F)
  have : FaithfulSMul (𝓞 κ.c.F) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.Flat (𝓞 κ.c.F) ℂ := inferInstance
  have : IsProper s.T.Z.s := isProper_toroidalModel_structureMap s.T.Z
  have : LocallyOfFiniteType q := by rw [← hq]; infer_instance
  have hi : IsClosedImmersion (toGenCx jm hq σ) := isClosedImmersion_toGenCx D A N j S κ s σ Y q jm hq n hY
  have hemb := (toGenCx jm hq σ).isClosedEmbedding
  set π := pullback.fst q (spMap (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))) with hπ
  have hsq : ∀ z, genι s.T.Z (pullback.fst (genStr s.T.Z) (spMap σ) (toGenCx jm hq σ z)) = jm (π z) := fun z =>
    congrArg (fun g : cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ ⟶ s.T.Z.X => g z) (isPullback_toGenCx jm hq σ).w.symm
  have hbd : ∀ z, toGenCx jm hq σ z ∈ bdCx s.T.Z σ ↔ jm (π z) ∉ abLocus s.T.Z.t.G := fun z => by
    rw [← hsq]; exact mem_genBd_iff
  have hbd' : ∀ z, toGenCx jm hq σ z ∈ bdCx s.T.Z σ ↔ jm (π z) ∈ s.T.BD.idealSheaf.support := fun z =>
    ⟨fun h => hsq z ▸ s.T.BD_pos _ h, fun h => (hbd z).2 (s.T.BD_supp _ h)⟩
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hK : IsClosed (toGenCx jm hq σ '' C ∩ bdCx s.T.Z σ) :=
    (hemb.isClosedMap _ hCc).inter ((genBd s.T.Z).isClosed.preimage (pullback.fst (genStr s.T.Z) (spMap σ)).continuous)
  have hWc : IsClosed W := by
    have := hW.eq_of_le (y := closure W) ⟨hW.1.1.closure, closure_minimal hW.1.2 hK⟩ subset_closure
    rw [this]; exact isClosed_closure
  obtain ⟨w₀, hw₀⟩ := QuasiSober.sober hW.1.1 hWc
  obtain ⟨⟨w, hwC, rfl⟩, hwb⟩ := hW.1.2 hw₀.mem
  obtain ⟨c, hc⟩ := QuasiSober.sober hC.1 hCc
  have hnab := (hbd w).1 hwb
  refine ⟨π w, ?_, hnab, ?_, le_antisymm ?_ ?_⟩
  · have : JacobsonSpace (cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ) :=
      LocallyOfFiniteType.jacobsonSpace (pullback.snd q (spMap (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))))
    have h1 := closure_inter_closedPoints (isClosed_closure (s := {w}))
    refine closure_minimal (t := π ⁻¹' T) ?_ (hT.preimage π.continuous) (h1.ge (subset_closure rfl))
    rintro z ⟨hz, hzc⟩
    let p := pointOfClosedPoint (pullback.snd q (spMap (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)))) z hzc
    have hp : p ≫ pullback.snd q (spMap (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))) = 𝟙 _ := pointOfClosedPoint_comp _ z hzc
    have hpz : p (IsLocalRing.closedPoint ℂ) = z := pointOfClosedPoint_apply _ z hzc _
    let y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) :=
      ⟨p ≫ π, by rw [Category.assoc, hπ, pullback.condition, ← Category.assoc, hp, Category.id_comp]⟩
    have e : ptOf s.T.Z (up jm hq σ y) = toGenCx jm hq σ z :=
      (ptOf_up_eq jm hq σ p hp y rfl).trans (congrArg _ hpz)
    have h2 : toGenCx jm hq σ z ∈ W :=
      hw₀.specializes_iff_mem.1 ((specializes_iff_mem_closure.2 hz).map (toGenCx jm hq σ).continuous)
    have h3 := hWT y (show ptOf s.T.Z (up jm hq σ y) ∈ W from e ▸ h2)
    rw [Set.mem_preimage, ← hpz]
    exact h3
  · let t := pullback.snd q (spMap (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)))
    have : CharZero ((cxFib (algebraMap (𝓞 κ.c.F) κ.c.F) q σ).residueField w) :=
      charZero_of_injective_ringHom (f := ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ t.appTop ≫ Scheme.Γevaluation _ w).hom)
        (RingHom.injective _)
    exact (π.residueFieldMap w).hom.charZero
  · obtain ⟨i, hi⟩ := s.T.BD.exists_mem (jm (π w))
    have hloc : ∀ z, π z ∈ jm ⁻¹ᵁ s.T.BD.U i →
        (toGenCx jm hq σ z ∈ bdCx s.T.Z σ ↔ π z ∉ Y.basicOpen (jm.app _ (s.T.BD.f i))) := fun z hz => by
      rw [hbd', s.T.BD.mem_support_iff i hz, ← Scheme.preimage_basicOpen]; rfl
    refine coheight_fst_le_one q (jm ⁻¹ᵁ s.T.BD.U i) (jm.app _ (s.T.BD.f i)) c w (fun c' h => ?_)
      (hc.specializes hwC) hi ((hloc w hi).1 hwb) fun w' h1 h2 h3 => ?_
    · refine hc.specializes (hC.2 (isIrreducible_singleton.closure (s := {c'})) ?_ (subset_closure rfl))
      rw [← hc.def]
      exact specializes_iff_closure_subset.1 h
    · have h4 : π w' ∈ jm ⁻¹ᵁ s.T.BD.U i := (h2.map π.continuous).mem_open (jm ⁻¹ᵁ s.T.BD.U i).isOpen hi
      have h5 : toGenCx jm hq σ w' ∈ toGenCx jm hq σ '' C ∩ bdCx s.T.Z σ :=
        ⟨⟨w', hc.specializes_iff_mem.1 h1, rfl⟩, (hloc w' h4).2 h3⟩
      refine hemb.isInducing.specializes_iff.1 (hw₀.specializes (hW.2 (y := closure {toGenCx jm hq σ w'})
        ⟨isIrreducible_singleton.closure, closure_minimal (Set.singleton_subset_iff.2 h5) hK⟩ ?_ (subset_closure rfl)))
      rw [← hw₀.def]
      exact specializes_iff_closure_subset.1 (h2.map (toGenCx jm hq σ).continuous)
  · refine Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 fun h0 => hnab ?_)
    have h1 : π w ⤳ genericPoint Y := Order.coheight_eq_zero.1 h0 (genericPoint_specializes (π w))
    rw [(h1.antisymm (genericPoint_specializes _)).eq]
    exact hgen

end GlobalTheory.HorComp
