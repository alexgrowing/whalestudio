import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackey
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.Splitting
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

open scoped NumberField.LiesOver

local notation "ℚ̄" => AlgebraicClosure ℚ

section Place

variable {K : FiniteSubfield} {v : InfinitePlace K.1} (L : FiniteSubfield) [Fact (K ≤ L)]

theorem infPlaceOfEmbedding_eq_of_forall (ι ι' : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (h : ∀ l : L.1, ι l = ι' l) : infPlaceOfEmbedding ι L = infPlaceOfEmbedding ι' L :=
  eq_infPlaceOfEmbedding ι' L (infCompletionEmbedding ι L) fun l =>
    (infCompletionEmbedding_algebraMap ι L l).trans (h l)

theorem infPlaceOfEmbedding_gal_comp (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (h : Gal(AlgebraicClosure v.Completion / v.Completion)) :
    infPlaceOfEmbedding (((h : AlgebraicClosure v.Completion ≃ₐ[v.Completion]
      AlgebraicClosure v.Completion).toAlgHom.restrictScalars K.1).comp ι) L = infPlaceOfEmbedding ι L :=
  (eq_infPlaceOfEmbedding _ L ((h : AlgebraicClosure v.Completion ≃ₐ[v.Completion]
      AlgebraicClosure v.Completion).toAlgHom.comp (infCompletionEmbedding ι L)) fun l => by
    rw [AlgHom.comp_apply, infCompletionEmbedding_algebraMap]
    rfl).symm

theorem isReal_infPlaceOfEmbedding_iff (hv : v.IsReal) (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion) :
    (infPlaceOfEmbedding ι L : InfinitePlace L.1).IsReal ↔
      ∀ (σ : Gal(AlgebraicClosure v.Completion / v.Completion)) (l : L.1), σ (ι l) = ι l := by
  have : (infPlaceOfEmbedding ι L : InfinitePlace L.1).LiesOver v := (infPlaceOfEmbedding ι L).2
  constructor
  · intro hw σ l
    have hf : Module.finrank v.Completion (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion = 1 :=
      (InfinitePlace.finrank_completion_eq_one_iff _).2 fun h =>
        (InfinitePlace.not_isReal_iff_isComplex.2 h.2) hw
    obtain ⟨a, ha⟩ : ∃ a : v.Completion, algebraMap v.Completion
        (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion a =
        algebraMap L.1 (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion l := by
      have hmem : algebraMap L.1 (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion l ∈
          (⊥ : Subalgebra v.Completion (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion) := by
        rw [Subalgebra.bot_eq_top_of_finrank_eq_one hf]
        exact Algebra.mem_top
      exact Algebra.mem_bot.1 hmem
    rw [← infCompletionEmbedding_algebraMap ι L l, ← ha, AlgHom.commutes]
    exact σ.commutes a
  · intro hfix
    have hc : ∀ σ : Gal(AlgebraicClosure v.Completion / v.Completion),
        (σ : AlgebraicClosure v.Completion ≃ₐ[v.Completion] AlgebraicClosure v.Completion).toAlgHom.comp
          (infCompletionEmbedding ι L) = infCompletionEmbedding ι L := fun σ =>
      algHom_ext_infCompletion L fun l => by
        rw [AlgHom.comp_apply, infCompletionEmbedding_algebraMap]
        exact hfix σ l
    by_contra hw
    have hcx := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have h2 := (InfinitePlace.finrank_completion_eq_two_iff
      (infPlaceOfEmbedding ι L : InfinitePlace L.1)).2 ⟨hv, hcx⟩
    have hrange : LinearMap.range (infCompletionEmbedding ι L).toLinearMap ≤
        Subalgebra.toSubmodule (⊥ : Subalgebra v.Completion (AlgebraicClosure v.Completion)) := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
        ((infCompletionEmbedding ι L) y)).2 fun σ => DFunLike.congr_fun (hc σ) y
      exact ⟨a, ha⟩
    have hmono := Submodule.finrank_mono hrange
    rw [LinearMap.finrank_range_of_inj (infCompletionEmbedding ι L).toRingHom.injective,
      Subalgebra.finrank_toSubmodule, Subalgebra.finrank_bot, h2] at hmono
    omega

theorem apply_eq_algebraMap_of_infPlaceOfEmbedding_eq (w : v.placesOver L.1) (a : v.Completion) (l : L.1)
    (ha : algebraMap v.Completion (w : InfinitePlace L.1).Completion a =
      algebraMap L.1 (w : InfinitePlace L.1).Completion l)
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion) (hι : infPlaceOfEmbedding ι L = w) :
    ι l = algebraMap v.Completion (AlgebraicClosure v.Completion) a := by
  subst hι
  rw [← infCompletionEmbedding_algebraMap ι L l, ← ha, AlgHom.commutes]

theorem apply_eq_of_infPlaceOfEmbedding_eq (ι ι' : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (h : infPlaceOfEmbedding ι L = infPlaceOfEmbedding ι' L)
    (hw : (infPlaceOfEmbedding ι L : InfinitePlace L.1).IsReal) (l : L.1) : ι l = ι' l := by
  have : (infPlaceOfEmbedding ι L : InfinitePlace L.1).LiesOver v := (infPlaceOfEmbedding ι L).2
  have hf : Module.finrank v.Completion (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion = 1 :=
    (InfinitePlace.finrank_completion_eq_one_iff _).2 fun h =>
      (InfinitePlace.not_isReal_iff_isComplex.2 h.2) hw
  obtain ⟨a, ha⟩ : ∃ a : v.Completion, algebraMap v.Completion
      (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion a =
      algebraMap L.1 (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion l := by
    have hmem : algebraMap L.1 (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion l ∈
        (⊥ : Subalgebra v.Completion (infPlaceOfEmbedding ι L : InfinitePlace L.1).Completion) := by
      rw [Subalgebra.bot_eq_top_of_finrank_eq_one hf]
      exact Algebra.mem_top
    exact Algebra.mem_bot.1 hmem
  rw [apply_eq_algebraMap_of_infPlaceOfEmbedding_eq L _ a l ha ι rfl,
    apply_eq_algebraMap_of_infPlaceOfEmbedding_eq L _ a l ha ι' h.symm]

end Place

section Members

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

def gsRealEmbedding (v : {v : InfinitePlace K.1 // v.IsReal}) (x : galUnramifiedOutside K.1 ℚ̄ S) :
    ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion :=
  (ιr v).comp ((gsAutLift S x)⁻¹ : Gal(ℚ̄/K.1)).toAlgHom

theorem gsRealEmbedding_apply (v : {v : InfinitePlace K.1 // v.IsReal}) (x : galUnramifiedOutside K.1 ℚ̄ S)
    (z : maxUnramifiedOutside K.1 ℚ̄ S) :
    gsRealEmbedding S ιr v x (z : ℚ̄) =
      ιr v (((x⁻¹ : galUnramifiedOutside K.1 ℚ̄ S) z : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) := by
  change ιr v ((gsAutLift S x)⁻¹ (z : ℚ̄)) = _
  rw [gsAutLift_inv_apply]

theorem gsRealEmbedding_conj (v : {v : InfinitePlace K.1 // v.IsReal}) (x : galUnramifiedOutside K.1 ℚ̄ S)
    (g : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) (z : maxUnramifiedOutside K.1 ℚ̄ S) :
    gsRealEmbedding S ιr v x (((x * gsRealFamily S ιr v g * x⁻¹) z : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) =
      g (gsRealEmbedding S ιr v x (z : ℚ̄)) := by
  rw [gsRealEmbedding_apply, gsRealEmbedding_apply, ← AlgEquiv.mul_apply,
    show x⁻¹ * (x * gsRealFamily S ιr v g * x⁻¹) = gsRealFamily S ιr v g * x⁻¹ by group,
    AlgEquiv.mul_apply]
  exact gsRealFamily_apply S ιr v g _

variable {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

theorem mem_mackeySubgroup_real_iff (v : {v : InfinitePlace K.1 // v.IsReal})
    (x : galUnramifiedOutside K.1 ℚ̄ S) (σ : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) :
    σ ∈ mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (gsRealFamily S ιr v).toMonoidHom x ↔
      ∀ l : L.1, σ (gsRealEmbedding S ιr v x l) = gsRealEmbedding S ιr v x l := by
  rw [mem_mackeySubgroup]
  change _ ∈ gsOpenSubgroup S hL ↔ _
  rw [mem_gsOpenSubgroup_iff]
  refine forall_congr' fun l => ?_
  have key := gsRealFamily_apply S ιr v σ ((x⁻¹ : galUnramifiedOutside K.1 ℚ̄ S) (gsEmbedding hL l))
  rw [show ((l : L.1) : ℚ̄) = ((gsEmbedding hL l : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) from rfl,
    gsRealEmbedding_apply, ← key]
  change x (gsRealFamily S ιr v σ (x⁻¹ (gsEmbedding hL l))) = gsEmbedding hL l ↔ _
  constructor
  · intro h
    have h' := congrArg (⇑(x⁻¹ : galUnramifiedOutside K.1 ℚ̄ S)) h
    rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h'
    rw [h']
  · intro h
    have h' := Subtype.ext ((ιr v).injective h)
    rw [h', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem gsRealEmbedding_mul (v : {v : InfinitePlace K.1 // v.IsReal}) (x : galUnramifiedOutside K.1 ℚ̄ S)
    {u : galUnramifiedOutside K.1 ℚ̄ S} (hu : u ∈ gsOpenSubgroup S hL)
    (h : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) (l : L.1) :
    gsRealEmbedding S ιr v (u * x * gsRealFamily S ιr v h) l = h⁻¹ (gsRealEmbedding S ιr v x l) := by
  have hul := (mem_gsOpenSubgroup_iff S hL u).1 hu l
  have hu' : u⁻¹ (gsEmbedding hL l) = gsEmbedding hL l := by
    rw [AlgEquiv.aut_inv]
    exact u.symm_apply_eq.2 hul.symm
  have hinv : (u * x * gsRealFamily S ιr v h)⁻¹ = gsRealFamily S ιr v h⁻¹ * x⁻¹ * u⁻¹ := by
    rw [map_inv]
    group
  have e1 : (u * x * gsRealFamily S ιr v h)⁻¹ (gsEmbedding hL l) =
      gsRealFamily S ιr v h⁻¹ ((x⁻¹ : galUnramifiedOutside K.1 ℚ̄ S) (gsEmbedding hL l)) := by
    rw [hinv, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hu']
  calc gsRealEmbedding S ιr v (u * x * gsRealFamily S ιr v h) l
      = ιr v ((((u * x * gsRealFamily S ιr v h)⁻¹) (gsEmbedding hL l) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
        gsRealEmbedding_apply S ιr v _ (gsEmbedding hL l)
    _ = ιr v ((gsRealFamily S ιr v h⁻¹ ((x⁻¹ : galUnramifiedOutside K.1 ℚ̄ S) (gsEmbedding hL l)) :
          maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) :=
        congrArg (fun z : maxUnramifiedOutside K.1 ℚ̄ S => ιr v (z : ℚ̄)) e1
    _ = h⁻¹ (ιr v (((x⁻¹ : galUnramifiedOutside K.1 ℚ̄ S) (gsEmbedding hL l) : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄)) :=
        gsRealFamily_apply S ιr v h⁻¹ _
    _ = h⁻¹ (gsRealEmbedding S ιr v x l) :=
        congrArg (fun y => (h⁻¹ : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) y)
          (gsRealEmbedding_apply S ιr v x (gsEmbedding hL l)).symm

def realMemberPlace (p : MackeyTopIndex (gsRealFamily S ιr) (gsOpenSubgroup S hL)) :
    {w : InfinitePlace L.1 // w.IsReal} :=
  ⟨(infPlaceOfEmbedding (gsRealEmbedding S ιr p.1.1 p.1.2.out) L : InfinitePlace L.1),
    (isReal_infPlaceOfEmbedding_iff L p.1.1.2 _).2 fun σ l =>
      (mem_mackeySubgroup_real_iff S ιr hL p.1.1 p.1.2.out σ).1 ((Subgroup.eq_top_iff' _).1 p.2 σ) l⟩

theorem realMemberPlace_injective : Function.Injective (realMemberPlace S ιr hL) := by
  rintro ⟨⟨v, d⟩, hd⟩ ⟨⟨v', d'⟩, hd'⟩ h
  have h1 : (infPlaceOfEmbedding (gsRealEmbedding S ιr v d.out) L : InfinitePlace L.1) =
      (infPlaceOfEmbedding (gsRealEmbedding S ιr v' d'.out) L : InfinitePlace L.1) :=
    congrArg Subtype.val h
  have ha : (infPlaceOfEmbedding (gsRealEmbedding S ιr v d.out) L : InfinitePlace L.1).comap
      (algebraMap K.1 L.1) = v.1 := by
    have := (infPlaceOfEmbedding (gsRealEmbedding S ιr v d.out) L).2
    exact NumberField.InfinitePlace.LiesOver.comap_eq _ _
  have hb : (infPlaceOfEmbedding (gsRealEmbedding S ιr v' d'.out) L : InfinitePlace L.1).comap
      (algebraMap K.1 L.1) = v'.1 := by
    have := (infPlaceOfEmbedding (gsRealEmbedding S ιr v' d'.out) L).2
    exact NumberField.InfinitePlace.LiesOver.comap_eq _ _
  have hv : v = v' := Subtype.ext (by rw [← ha, ← hb, h1])
  subst hv
  have h2 : infPlaceOfEmbedding (gsRealEmbedding S ιr v d.out) L =
      infPlaceOfEmbedding (gsRealEmbedding S ιr v d'.out) L := Subtype.ext h1
  have heq : ∀ l : L.1, gsRealEmbedding S ιr v d.out l = gsRealEmbedding S ιr v d'.out l :=
    apply_eq_of_infPlaceOfEmbedding_eq L _ _ h2 (realMemberPlace S ιr hL ⟨⟨v, d⟩, hd⟩).2
  have hmem : d'.out * d.out⁻¹ ∈ gsOpenSubgroup S hL := by
    rw [mem_gsOpenSubgroup_iff]
    intro l
    have e := heq l
    rw [show ((l : L.1) : ℚ̄) = ((gsEmbedding hL l : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) from rfl,
      gsRealEmbedding_apply, gsRealEmbedding_apply] at e
    have hinj : d.out⁻¹ (gsEmbedding hL l) = d'.out⁻¹ (gsEmbedding hL l) :=
      Subtype.ext ((ιr v).injective e)
    rw [AlgEquiv.mul_apply, hinj, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hdd : d = d' := by
    rw [← DoubleCoset.out_eq' _ _ d, ← DoubleCoset.out_eq' _ _ d', DoubleCoset.eq]
    exact ⟨_, hmem, 1, one_mem _, by group⟩
  subst hdd
  rfl

theorem realMemberPlace_surjective : Function.Surjective (realMemberPlace S ιr hL) := by
  rintro ⟨w, hw⟩
  let v : {v : InfinitePlace K.1 // v.IsReal} := ⟨w.comap (algebraMap K.1 L.1), hw.comap _⟩
  let w' : v.1.placesOver L.1 := ⟨w, ⟨rfl⟩⟩
  obtain ⟨ι'', hι''⟩ := exists_infPlaceOfEmbedding_eq (E := L) w'
  obtain ⟨g, hg⟩ := exists_eq_comp_of_normal (ιr v) ι''
  let x : galUnramifiedOutside K.1 ℚ̄ S := (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K.1 ℚ̄ S) g)⁻¹
  have hx : ∀ l : L.1, gsRealEmbedding S ιr v x l = ι'' l := by
    intro l
    rw [show ((l : L.1) : ℚ̄) = ((gsEmbedding hL l : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) from rfl,
      gsRealEmbedding_apply, inv_inv, hg, AlgHom.comp_apply]
    congr 1
    exact AlgEquiv.restrictNormal_commutes g (maxUnramifiedOutside K.1 ℚ̄ S) _
  let d : MackeyDoubleCoset (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom :=
    DoubleCoset.mk _ _ x
  obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul
    (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) (gsRealFamily S ιr v).toMonoidHom.range x
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.1 hb
  have hout : d.out = a * x * gsRealFamily S ιr v h := hab
  have hplace : infPlaceOfEmbedding (gsRealEmbedding S ιr v d.out) L = w' :=
    (congrArg (fun y => infPlaceOfEmbedding (gsRealEmbedding S ιr v y) L) hout).trans <|
      (infPlaceOfEmbedding_eq_of_forall L (gsRealEmbedding S ιr v (a * x * gsRealFamily S ιr v h))
        ((((h⁻¹ : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) :
          AlgebraicClosure v.1.Completion ≃ₐ[v.1.Completion] AlgebraicClosure v.1.Completion).toAlgHom.restrictScalars
            K.1).comp (gsRealEmbedding S ιr v x))
        (fun l => gsRealEmbedding_mul S ιr hL v x ha h l)).trans <|
      (infPlaceOfEmbedding_gal_comp L (gsRealEmbedding S ιr v x) h⁻¹).trans <|
      (infPlaceOfEmbedding_eq_of_forall L _ ι'' hx).trans hι''
  have hreal : (infPlaceOfEmbedding (gsRealEmbedding S ιr v d.out) L : InfinitePlace L.1).IsReal :=
    (congrArg (fun y : v.1.placesOver L.1 => (y : InfinitePlace L.1).IsReal) hplace).mpr hw
  have htop : mackeySubgroup (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
      (gsRealFamily S ιr v).toMonoidHom d.out = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun σ =>
      (mem_mackeySubgroup_real_iff S ιr hL v d.out σ).2 ((isReal_infPlaceOfEmbedding_iff L v.2 _).1 hreal σ)
  have hval : ((infPlaceOfEmbedding (gsRealEmbedding S ιr v d.out) L : v.1.placesOver L.1) :
      InfinitePlace L.1) = w := congrArg Subtype.val hplace
  exact ⟨⟨⟨v, d⟩, htop⟩, Subtype.ext hval⟩

end Members

end GroundTheory.ProfCoh
