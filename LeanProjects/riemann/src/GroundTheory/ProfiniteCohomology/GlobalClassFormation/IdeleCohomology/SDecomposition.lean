import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Decomposition
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Infinite
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Integral
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.ExistsSIdelesCohomologyEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

universe u

section Generic

variable {k G : Type u} [CommRing k] [Monoid G]

def homToSubrep (A : Rep.{u} k G) (W : Submodule k A) (hW : ∀ g, W ≤ W.comap (A.ρ g))
    {B : Rep.{u} k G} (f : B ⟶ A) (hf : ∀ b, f.hom b ∈ W) : B ⟶ A.subrepresentation W hW :=
  Rep.ofHom ⟨LinearMap.codRestrict W f.hom.toLinearMap hf, fun g => LinearMap.ext fun b =>
    Subtype.ext (Rep.hom_comm_apply f g b)⟩

@[simp]
theorem homToSubrep_hom_apply (A : Rep.{u} k G) (W : Submodule k A)
    (hW : ∀ g, W ≤ W.comap (A.ρ g)) {B : Rep.{u} k G} (f : B ⟶ A) (hf : ∀ b, f.hom b ∈ W)
    (b : B) : ((homToSubrep A W hW f hf).hom b : A) = f.hom b :=
  rfl

theorem homToSubrep_comp_subtype (A : Rep.{u} k G) (W : Submodule k A)
    (hW : ∀ g, W ≤ W.comap (A.ρ g)) {B : Rep.{u} k G} (f : B ⟶ A) (hf : ∀ b, f.hom b ∈ W) :
    homToSubrep A W hW f hf ≫ Rep.subtype A W hW = f :=
  rfl

end Generic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

variable (K L) in

noncomputable abbrev sIdeleRep : Rep ℤ Gal(L/K) :=
  (ideleRep K L).subrepresentation (sIdelesSubmodule K L S) (sIdelesSubmodule_stable K L S)

variable (K) in

abbrev SIndex : Type :=
  InfinitePlace K ⊕ ((S : Set (HeightOneSpectrum (𝓞 K))) ⊕ ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)

variable (L) in

noncomputable def sComp : SIndex K S → Rep ℤ Gal(L/K)
  | .inl v => Rep.of (infiniteUnitsAboveRep L v)
  | .inr (.inl v) => Rep.of (finiteUnitsAboveRep L v.1)
  | .inr (.inr v) => Rep.of (integerUnitsAboveRep L v.1)

def toSIdele (a : ↥(sIdelesSubmodule K L S)) :
    sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) :=
  ⟨a.1.toMul, mem_sIdelesSubmodule.1 a.2⟩

omit [NumberField K] in
theorem toSIdele_add (a b : ↥(sIdelesSubmodule K L S)) : toSIdele S (a + b) = toSIdele S a * toSIdele S b :=
  rfl

omit [NumberField K] in
theorem toSIdele_zero : toSIdele (L := L) S 0 = 1 :=
  rfl

omit [NumberField K] in
theorem toSIdele_ρ (σ : Gal(L/K)) (a : ↥(sIdelesSubmodule K L S)) :
    toSIdele S ((sIdeleRep K L S).ρ σ a) = σ • toSIdele S a :=
  rfl

omit [NumberField K] in
theorem toSIdele_bijective : Function.Bijective (toSIdele (L := L) S) :=
  ⟨fun a b h => Subtype.ext (by
      have := congrArg (fun x : sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) =>
        Additive.ofMul (x : IdeleGroup L)) h
      exact this),
    fun x => ⟨⟨Additive.ofMul (x : IdeleGroup L), mem_sIdelesSubmodule.2 x.2⟩, rfl⟩⟩

noncomputable def sIntegerProj (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    sIdeleRep K L S ⟶ Rep.of (integerUnitsAboveRep L v.1) :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun a w => Additive.ofMul (sIdelesIntegerPart _ (toSIdele S a) v w)
      map_zero' := by
        funext w
        change Additive.ofMul (sIdelesIntegerPart _ 1 v w) = 0
        rw [map_one]
        rfl
      map_add' := fun a b => by
        funext w
        change Additive.ofMul (sIdelesIntegerPart _ (toSIdele S a * toSIdele S b) v w) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun a => by
      funext w
      change Additive.ofMul (sIdelesIntegerPart _ (σ • toSIdele S a) v w) = _
      have h := congrArg (fun p : SIdelesProduct L (S : Set (HeightOneSpectrum (𝓞 K))) => p.2.2 v)
        (sIdelesToProduct_smul _ σ (toSIdele S a))
      simp only [sIdelesToProduct_snd_snd] at h
      rw [h]
      rfl⟩

theorem integerUnitsAboveIncl_sIntegerProj (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)
    (a : ↥(sIdelesSubmodule K L S)) :
    integerUnitsAboveIncl v.1 (fun w => ((sIntegerProj S v).hom a w).toMul) =
      finiteProjAbove v.1 a.1.toMul :=
  integerUnitsAboveIncl_sIdelesIntegerPart _ (toSIdele S a) v

noncomputable def sProj : ∀ i : SIndex K S, sIdeleRep K L S ⟶ sComp L S i
  | .inl v => Rep.subtype _ _ _ ≫ infiniteProjAboveRep v
  | .inr (.inl v) => Rep.subtype _ _ _ ≫ finiteProjAboveRep v.1
  | .inr (.inr v) => sIntegerProj S v

omit [NumberField K] in
theorem mem_sIdeles_of_mem_standardOpenSubgroup {x : IdeleGroup L}
    (hx : x ∈ standardOpenSubgroup L) : x ∈ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) :=
  standardOpenSubgroup_le_sIdeles _ hx

omit [NumberField K] in
theorem infiniteEmbedAbove_mem_standardOpenSubgroup (v : InfinitePlace K)
    (y : (w : v.placesOver L) → (w.1.Completion)ˣ) :
    infiniteEmbedAbove v y ∈ standardOpenSubgroup L := by
  refine (mem_standardOpenSubgroup L).2 fun w => ?_
  rw [← map_inv, coe_infiniteEmbedAbove_snd, coe_infiniteEmbedAbove_snd]
  exact ⟨(w.adicCompletionIntegers L).one_mem, (w.adicCompletionIntegers L).one_mem⟩

theorem finiteEmbedAbove_mem_sIdeles (v : (S : Set (HeightOneSpectrum (𝓞 K))))
    (y : (w : PlacesOver L v.1) → (w.1.adicCompletion L)ˣ) :
    finiteEmbedAbove v.1 y ∈ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) := by
  intro w hw
  have h : ¬ w.asIdeal.LiesOver v.1.asIdeal := fun h =>
    hw (by rw [mem_placesAbove, (below_eq_iff w v.1).2 h]; exact v.2)
  rw [ord_eq_zero_iff, ← map_inv, coe_finiteEmbedAbove_snd_of_not v.1 _ h,
    coe_finiteEmbedAbove_snd_of_not v.1 _ h]
  exact ⟨(w.adicCompletionIntegers L).one_mem, (w.adicCompletionIntegers L).one_mem⟩

noncomputable def integerEmbedAboveRep (v : HeightOneSpectrum (𝓞 K)) :
    Rep.of (integerUnitsAboveRep L v) ⟶ ideleRep K L :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun z => Additive.ofMul (finiteEmbedAbove v (integerUnitsAboveIncl v
        fun w => (z w).toMul))
      map_zero' := by
        change Additive.ofMul (finiteEmbedAbove v (integerUnitsAboveIncl v 1)) = 0
        rw [map_one, map_one]
        rfl
      map_add' := fun y z => by
        change Additive.ofMul (finiteEmbedAbove v (integerUnitsAboveIncl v
          ((fun w => (y w).toMul) * fun w => (z w).toMul))) = _
        rw [map_mul, map_mul]
        rfl },
    fun σ => LinearMap.ext fun z => by
      change Additive.ofMul (finiteEmbedAbove v (integerUnitsAboveIncl v
        (σ • fun w => (z w).toMul))) = _
      rw [integerUnitsAboveIncl_smul, finiteEmbedAbove_smul]
      rfl⟩

noncomputable def sEmbInf (v : InfinitePlace K) : Rep.of (infiniteUnitsAboveRep L v) ⟶ sIdeleRep K L S :=
  homToSubrep _ _ _ (infiniteEmbedAboveRep v) fun _ =>
    mem_sIdeles_of_mem_standardOpenSubgroup S (infiniteEmbedAbove_mem_standardOpenSubgroup v _)

noncomputable def sEmbFin (v : (S : Set (HeightOneSpectrum (𝓞 K)))) :
    Rep.of (finiteUnitsAboveRep L v.1) ⟶ sIdeleRep K L S :=
  homToSubrep _ _ _ (finiteEmbedAboveRep v.1) fun _ => finiteEmbedAbove_mem_sIdeles S v _

noncomputable def sEmbInt (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    Rep.of (integerUnitsAboveRep L v.1) ⟶ sIdeleRep K L S :=
  homToSubrep _ _ _ (integerEmbedAboveRep v.1) fun _ =>
    mem_sIdeles_of_mem_standardOpenSubgroup S (finiteEmbedAbove_integerUnitsAboveIncl_mem v.1 _)

noncomputable def sEmb : ∀ i : SIndex K S, sComp L S i ⟶ sIdeleRep K L S
  | .inl v => sEmbInf S v
  | .inr (.inl v) => sEmbFin S v
  | .inr (.inr v) => sEmbInt S v

theorem sEmbInf_comp_subtype (v : InfinitePlace K) :
    sEmbInf (L := L) S v ≫ Rep.subtype _ _ _ = infiniteEmbedAboveRep v :=
  rfl

theorem sEmbFin_comp_subtype (v : (S : Set (HeightOneSpectrum (𝓞 K)))) :
    sEmbFin (L := L) S v ≫ Rep.subtype _ _ _ = finiteEmbedAboveRep v.1 :=
  rfl

theorem subtype_comp_infiniteProjAboveRep (v : InfinitePlace K) :
    Rep.subtype _ _ _ ≫ infiniteProjAboveRep v = sProj (L := L) S (.inl v) :=
  rfl

theorem subtype_comp_finiteProjAboveRep (v : (S : Set (HeightOneSpectrum (𝓞 K)))) :
    Rep.subtype _ _ _ ≫ finiteProjAboveRep v.1 = sProj (L := L) S (.inr (.inl v)) :=
  rfl

def productToFamily (p : SIdelesProduct L (S : Set (HeightOneSpectrum (𝓞 K)))) :
    ∀ i : SIndex K S, sComp L S i
  | .inl v => fun w => Additive.ofMul (p.1 v w)
  | .inr (.inl v) => fun w => Additive.ofMul (p.2.1 v w)
  | .inr (.inr v) => fun w => Additive.ofMul (p.2.2 v w)

theorem productToFamily_bijective : Function.Bijective (productToFamily (L := L) S) := by
  constructor
  · intro p q h
    refine Prod.ext (funext fun v => funext fun w => ?_)
      (Prod.ext (funext fun v => funext fun w => ?_) (funext fun v => funext fun w => ?_))
    · exact congrArg Additive.toMul (congrFun (congrFun h (.inl v)) w)
    · exact congrArg Additive.toMul (congrFun (congrFun h (.inr (.inl v))) w)
    · exact congrArg Additive.toMul (congrFun (congrFun h (.inr (.inr v))) w)
  · intro F
    refine ⟨(fun v w => (F (.inl v) w).toMul, fun v w => (F (.inr (.inl v)) w).toMul,
      fun v w => (F (.inr (.inr v)) w).toMul), funext fun i => ?_⟩
    rcases i with v | v | v <;> rfl

theorem sProj_eq_productToFamily (a : ↥(sIdelesSubmodule K L S)) (i : SIndex K S) :
    (sProj S i).hom a = productToFamily S (sIdelesToProduct _ (toSIdele S a)) i := by
  rcases i with v | v | v <;> rfl

theorem sProj_bijective :
    Function.Bijective fun (a : sIdeleRep K L S) (i : SIndex K S) => (sProj S i).hom a := by
  have e : (fun (a : ↥(sIdelesSubmodule K L S)) (i : SIndex K S) => (sProj S i).hom a) =
      productToFamily (L := L) S ∘ sIdelesToProduct _ ∘ toSIdele (L := L) S :=
    funext fun a => funext fun i => sProj_eq_productToFamily S a i
  have hb := (productToFamily_bijective (L := L) S).comp
    ((sIdelesEquivProduct _ (S.finite_toSet)).bijective.comp (toSIdele_bijective (L := L) S))
  rw [show ⇑(sIdelesEquivProduct (L := L) ((S : Set (HeightOneSpectrum (𝓞 K)))) S.finite_toSet) =
    sIdelesToProduct _ from rfl, ← e] at hb
  exact hb

noncomputable def integerInclRep (v : HeightOneSpectrum (𝓞 K)) :
    Rep.of (integerUnitsAboveRep L v) ⟶ Rep.of (finiteUnitsAboveRep L v) :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun z w => Additive.ofMul (integerUnitsAboveIncl v (fun w => (z w).toMul) w)
      map_zero' := by
        funext w
        change Additive.ofMul (integerUnitsAboveIncl v 1 w) = 0
        rw [map_one]
        rfl
      map_add' := fun y z => by
        funext w
        change Additive.ofMul (integerUnitsAboveIncl v
          ((fun w => (y w).toMul) * fun w => (z w).toMul) w) = _
        rw [map_mul]
        rfl },
    fun σ => LinearMap.ext fun z => by
      funext w
      change Additive.ofMul (integerUnitsAboveIncl v (σ • fun w => (z w).toMul) w) = _
      rw [integerUnitsAboveIncl_smul]
      rfl⟩

instance mono_integerInclRep (v : HeightOneSpectrum (𝓞 K)) : Mono (integerInclRep (L := L) v) := by
  rw [Rep.mono_iff_injective]
  intro y z h
  have h' : integerUnitsAboveIncl v (fun w => (y w).toMul) =
      integerUnitsAboveIncl v (fun w => (z w).toMul) :=
    funext fun w => congrArg Additive.toMul (congrFun h w)
  have := integerUnitsAboveIncl_injective v h'
  funext w
  exact congrArg Additive.ofMul (congrFun this w)

theorem integerEmbedAboveRep_eq (v : HeightOneSpectrum (𝓞 K)) :
    integerEmbedAboveRep (L := L) v = integerInclRep v ≫ finiteEmbedAboveRep v :=
  rfl

theorem sIntegerProj_comp_integerInclRep (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    sIntegerProj (L := L) S v ≫ integerInclRep v.1 =
      Rep.subtype _ _ _ ≫ finiteProjAboveRep v.1 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  funext w
  exact congrArg (fun f => Additive.ofMul (f w)) (integerUnitsAboveIncl_sIntegerProj S v a)

theorem sEmbInt_comp_subtype (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    sEmbInt (L := L) S v ≫ Rep.subtype _ _ _ = integerInclRep v.1 ≫ finiteEmbedAboveRep v.1 :=
  rfl

theorem eq_zero_of_comp_integerInclRep {v : HeightOneSpectrum (𝓞 K)} {X : Rep ℤ Gal(L/K)}
    (f : X ⟶ Rep.of (integerUnitsAboveRep L v)) (hf : f ≫ integerInclRep v = 0) : f = 0 := by
  rw [← cancel_mono (integerInclRep v), hf, Limits.zero_comp]

theorem sEmbInt_comp_sIntegerProj (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    sEmbInt (L := L) S v ≫ sIntegerProj S v = 𝟙 _ := by
  rw [← cancel_mono (integerInclRep v.1), Category.assoc, sIntegerProj_comp_integerInclRep,
    ← Category.assoc, sEmbInt_comp_subtype, Category.assoc,
    finiteEmbedAboveRep_comp_finiteProjAboveRep, Category.comp_id, Category.id_comp]

theorem sEmbInf_comp_sIntegerProj (v : InfinitePlace K)
    (v' : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) : sEmbInf (L := L) S v ≫ sIntegerProj S v' = 0 := by
  refine eq_zero_of_comp_integerInclRep _ ?_
  rw [Category.assoc, sIntegerProj_comp_integerInclRep, ← Category.assoc, sEmbInf_comp_subtype]
  exact infiniteEmbedAboveRep_comp_finiteProjAboveRep v v'.1

theorem sEmbFin_comp_sIntegerProj (v : (S : Set (HeightOneSpectrum (𝓞 K))))
    (v' : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) : sEmbFin (L := L) S v ≫ sIntegerProj S v' = 0 := by
  refine eq_zero_of_comp_integerInclRep _ ?_
  rw [Category.assoc, sIntegerProj_comp_integerInclRep, ← Category.assoc, sEmbFin_comp_subtype]
  exact finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne fun (e : v'.1 = v.1) => v'.2 (e ▸ v.2)

theorem sEmbInt_comp_sIntegerProj_of_ne {v v' : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ}
    (h : v ≠ v') : sEmbInt (L := L) S v ≫ sIntegerProj S v' = 0 := by
  refine eq_zero_of_comp_integerInclRep _ ?_
  rw [Category.assoc, sIntegerProj_comp_integerInclRep, ← Category.assoc, sEmbInt_comp_subtype,
    Category.assoc, finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne
      (fun e => h (Subtype.ext e.symm)), Limits.comp_zero]

theorem sEmbInt_comp_infinite (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) (v' : InfinitePlace K) :
    sEmbInt (L := L) S v ≫ Rep.subtype _ _ _ ≫ infiniteProjAboveRep v' = 0 := by
  rw [← Category.assoc, sEmbInt_comp_subtype, Category.assoc,
    finiteEmbedAboveRep_comp_infiniteProjAboveRep, Limits.comp_zero]

theorem sEmbInt_comp_finite (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)
    (v' : (S : Set (HeightOneSpectrum (𝓞 K)))) :
    sEmbInt (L := L) S v ≫ Rep.subtype _ _ _ ≫ finiteProjAboveRep v'.1 = 0 := by
  rw [← Category.assoc, sEmbInt_comp_subtype, Category.assoc,
    finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne (fun (e : v'.1 = v.1) => v.2 (e ▸ v'.2)),
    Limits.comp_zero]

theorem sEmb_comp_sProj (i : SIndex K S) : sEmb (L := L) S i ≫ sProj S i = 𝟙 _ := by
  rcases i with v | v | v
  · exact infiniteEmbedAboveRep_comp_infiniteProjAboveRep v
  · exact finiteEmbedAboveRep_comp_finiteProjAboveRep v.1
  · exact sEmbInt_comp_sIntegerProj S v

theorem sEmb_comp_sProj_of_ne (i j : SIndex K S) (h : i ≠ j) :
    sEmb (L := L) S i ≫ sProj S j = 0 := by
  rcases i with v | v | v <;> rcases j with v' | v' | v'
  · exact infiniteEmbedAboveRep_comp_infiniteProjAboveRep_of_ne fun e => h (by rw [e])
  · exact infiniteEmbedAboveRep_comp_finiteProjAboveRep v v'.1
  · exact sEmbInf_comp_sIntegerProj S v v'
  · exact finiteEmbedAboveRep_comp_infiniteProjAboveRep v' v.1
  · exact finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne fun e => h (by rw [Subtype.ext e])
  · exact sEmbFin_comp_sIntegerProj S v v'
  · exact sEmbInt_comp_infinite S v v'
  · exact sEmbInt_comp_finite S v v'
  · exact sEmbInt_comp_sIntegerProj_of_ne S fun e => h (by rw [e])

end GroundTheory.ProfCoh
