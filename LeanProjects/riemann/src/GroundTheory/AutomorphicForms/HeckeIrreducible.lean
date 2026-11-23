import Mathlib
import GroundTheory.AutomorphicForms.HeckeAlgebraLevel

noncomputable section

universe u

namespace GroundTheory.Automorphic

open Set Filter Topology MeasureTheory
open scoped Pointwise

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

namespace HeckeAlgebra

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [μ.IsHaarMeasure] in

theorem heckeAct_mul [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] (a b : HeckeAlgebra μ)
    {v : V} (hv : v ∈ smoothVectors ρ) :
    heckeAct μ ρ (a * b : HeckeAlgebra μ) v = heckeAct μ ρ a (heckeAct μ ρ b v) := by
  rw [coe_mul]
  exact heckeAct_groupConv a.mem b.mem hv

theorem leftReg_mul (g : G) (a b : HeckeAlgebra μ) : leftReg μ g (a * b) = leftReg μ g a * b := by
  rw [← heckeAct_leftReg, heckeAct_ltrans g a.mem (isSmooth_leftReg b), ← heckeAct_leftReg]
  rfl

theorem heckeAct_mem_subrep (X : Subrepresentation ρ) {f : G → ℂ}
    (hf : f ∈ locallyConstantCompactSupport G ℂ ℂ) {x : V} (hx : x ∈ smoothVectors ρ)
    (hX : x ∈ X) : heckeAct μ ρ f x ∈ X :=
  heckeAct_mem_of_forall (X := X.toSubmodule)
    (range_finite_of_mem_locallyConstantCompactSupport (smul_orbit_mem hf hx))
    fun g => X.toSubmodule.smul_mem _ (X.apply_mem_toSubmodule g hX)

theorem heckeAct_corner {v : V} (hv : v ∈ fixedVectors ρ K) (f : HeckeAlgebra μ) :
    heckeAct μ ρ (HeckeAlgebraLevel.corner hKc hKo f : HeckeAlgebra μ) v =
      heckeAct μ ρ (idem μ hKc hKo * f : HeckeAlgebra μ) v := by
  rw [HeckeAlgebraLevel.val_corner, heckeAct_mul _ _ (smooth_of_mem_fixedVectors hKo hv),
    heckeAct_idem_of_mem (μ := μ) hKc hKo hv]

theorem heckeAct_idem_apply (g : G) {v : V} (hv : v ∈ fixedVectors ρ K) :
    heckeAct μ ρ (idem μ hKc hKo) (ρ g v) =
      heckeAct μ ρ (idem μ hKc hKo * leftReg μ g (idem μ hKc hKo) : HeckeAlgebra μ) v := by
  have hs := smooth_of_mem_fixedVectors hKo hv
  rw [heckeAct_mul _ _ hs]
  conv_lhs => rw [← heckeAct_idem_of_mem (μ := μ) hKc hKo hv]
  rw [heckeAct_ltrans g (idem μ hKc hKo).mem hs]
  rfl

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G]
  [BorelSpace G] [IsTopologicalGroup G] in

theorem mem_span_orbit [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) (w : V) :
    w ∈ Submodule.span ℂ (range fun g => ρ g v) := by
  set S := Submodule.span ℂ (range fun g => ρ g v)
  have hS : ∀ g, ∀ ⦃x⦄, x ∈ S → ρ g x ∈ S := by
    intro g x hx
    have : S ≤ S.comap (ρ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp [Module.End.mul_apply]⟩)
    exact this hx
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨S, hS⟩ : Subrepresentation ρ) with h | h
  · exfalso
    apply hv
    have : v ∈ (⟨S, hS⟩ : Subrepresentation ρ) := Submodule.subset_span ⟨1, by simp⟩
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · have : w ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← h] at this
    exact this

end General

section Simple

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

theorem isSimpleModule_fixedVectors (hρ : IsSmooth ρ) [ρ.IsIrreducible]
    (hK : fixedVectors ρ K ≠ ⊥) :
    IsSimpleModule (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K) := by
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨?_, fun x hx y => ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
    exact ⟨⟨⟨v, hv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  · have hx0 : (x : V) ≠ 0 := fun h => hx (Subtype.ext h)
    let M : HeckeAlgebra μ →ₗ[ℂ] V :=
      { toFun := fun f => heckeAct μ ρ (idem μ hKc hKo * f : HeckeAlgebra μ) x
        map_add' := fun a b => by
          rw [mul_add, coe_add, heckeAct_add_left (mem _) (mem _) (hρ _)]
        map_smul' := fun c a => by
          simp only [RingHom.id_apply]
          rw [mul_smul_comm, coe_smul, heckeAct_smul_left c (mem _) (hρ _)] }
    let L : V →ₗ[ℂ] V := heckeRep (μ := μ) hρ (idem μ hKc hKo)
    have hspan : Submodule.span ℂ (range fun g => ρ g x) ≤ (LinearMap.range M).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact ⟨leftReg μ g (idem μ hKc hKo), (heckeAct_idem_apply hKc hKo g x.2).symm⟩
    obtain ⟨f, hf⟩ := hspan (mem_span_orbit hx0 (y : V))
    refine ⟨HeckeAlgebraLevel.corner hKc hKo f, Subtype.ext ?_⟩
    rw [LinearMap.toSpanSingleton_apply, HeckeAlgebraLevel.coe_smul_fixedVectors,
      heckeAct_corner hKc hKo x.2]
    refine hf.trans ?_
    exact heckeAct_idem_of_mem (μ := μ) hKc hKo y.2

def fixedMapLevel {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (T : Representation.IntertwiningMap ρ σ) :
    fixedVectors ρ K →ₗ[HeckeAlgebraLevel μ K hKc hKo] fixedVectors σ K where
  toFun v := ⟨T v, map_mem_fixedVectors ρ T v.2⟩
  map_add' v w := Subtype.ext (map_add T _ _)
  map_smul' h v := Subtype.ext (by
    simp only [RingHom.id_apply, HeckeAlgebraLevel.coe_smul_fixedVectors]
    exact map_heckeAct T (h : HeckeAlgebra μ).mem (smooth_of_mem_fixedVectors hKo v.2))

def fixedVectorsEquiv {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (T : ρ.Equiv σ) :
    fixedVectors ρ K ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] fixedVectors σ K :=
  LinearEquiv.ofBijective (fixedMapLevel hKc hKo T.toIntertwiningMap) (by
    refine ⟨fun v w h => Subtype.ext (T.toLinearEquiv.injective (congrArg Subtype.val h)), ?_⟩
    intro w
    set v := T.toLinearEquiv.symm (w : W)
    have hTv : T.toLinearEquiv v = w := T.toLinearEquiv.apply_symm_apply _
    have hv : v ∈ fixedVectors ρ K := fun k hk => T.toLinearEquiv.injective (by
      rw [Representation.Equiv.toLinearEquiv_apply, T.toIntertwiningMap.isIntertwining,
        ← Representation.Equiv.toLinearEquiv_apply, hTv, w.2 k hk])
    exact ⟨⟨v, hv⟩, Subtype.ext hTv⟩)

end Simple

section Construction

namespace HeckeAlgebraLevel

theorem smul_mem_ideal (I : Submodule (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo))
    (c : ℂ) {h : HeckeAlgebraLevel μ K hKc hKo} (hh : h ∈ I) : c • h ∈ I := by
  have : c • h = (c • (1 : HeckeAlgebraLevel μ K hKc hKo)) * h := by
    apply ext hKc hKo
    rw [val_smul, val_mul, val_smul, val_one, smul_mul_assoc,
      ((mem_biInvariant_iff_idem hKc hKo).1 (val_mem hKc hKo h)).1]
  rw [this]
  exact I.smul_mem _ hh

def cornerₗ : HeckeAlgebra μ →ₗ[ℂ] HeckeAlgebraLevel μ K hKc hKo where
  toFun := corner hKc hKo
  map_add' a b := ext hKc hKo (by simp only [val_corner, val_add, mul_add, add_mul])
  map_smul' c a := ext hKc hKo (by
    simp only [val_corner, val_smul, RingHom.id_apply, mul_smul_comm, smul_mul_assoc])

theorem val_cornerₗ (f : HeckeAlgebra μ) :
    ((cornerₗ hKc hKo f : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) =
      idem μ hKc hKo * f * idem μ hKc hKo := rfl

theorem cornerₗ_val (h : HeckeAlgebraLevel μ K hKc hKo) : cornerₗ hKc hKo (h : HeckeAlgebra μ) = h := by
  apply ext hKc hKo
  obtain ⟨h1, h2⟩ := (mem_biInvariant_iff_idem hKc hKo).1 (val_mem hKc hKo h)
  rw [val_cornerₗ, h1, h2]

theorem cornerₗ_mul_idem (f : HeckeAlgebra μ) :
    cornerₗ hKc hKo (f * idem μ hKc hKo) = cornerₗ hKc hKo f := by
  apply ext hKc hKo
  simp only [val_cornerₗ, mul_assoc, (isIdempotentElem_idem hKc hKo).eq]

theorem cornerₗ_idem_mul (f : HeckeAlgebra μ) :
    cornerₗ hKc hKo (idem μ hKc hKo * f) = cornerₗ hKc hKo f := by
  apply ext hKc hKo
  have he : ∀ x : HeckeAlgebra μ, idem μ hKc hKo * (idem μ hKc hKo * x) = idem μ hKc hKo * x :=
    fun x => by rw [← mul_assoc, (isIdempotentElem_idem hKc hKo).eq]
  simp only [val_cornerₗ, mul_assoc, he]

end HeckeAlgebraLevel

open HeckeAlgebraLevel

variable (I : Submodule (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo))

def heckeKernel : Submodule ℂ (HeckeAlgebra μ) where
  carrier := {φ | ∀ g, cornerₗ hKc hKo (leftReg μ g φ) ∈ I}
  add_mem' {a b} ha hb g := by
    rw [map_add, map_add]
    exact I.add_mem (ha g) (hb g)
  zero_mem' g := by
    rw [map_zero, map_zero]
    exact I.zero_mem
  smul_mem' c φ hφ g := by
    rw [map_smul, map_smul]
    exact smul_mem_ideal hKc hKo I c (hφ g)

theorem heckeKernel_le_comap (g : G) :
    heckeKernel hKc hKo I ≤ (heckeKernel hKc hKo I).comap (leftReg μ g) := by
  intro φ hφ g'
  rw [← Module.End.mul_apply, ← map_mul]
  exact hφ (g' * g)

def quotRep : Representation ℂ G (HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) :=
  (leftReg μ).quotient _ (heckeKernel_le_comap hKc hKo I)

theorem quotRep_mkQ (g : G) (φ : HeckeAlgebra μ) :
    quotRep hKc hKo I g ((heckeKernel hKc hKo I).mkQ φ) =
      (heckeKernel hKc hKo I).mkQ (leftReg μ g φ) := rfl

def quotMap : Representation.IntertwiningMap (leftReg μ) (quotRep hKc hKo I) where
  toLinearMap := (heckeKernel hKc hKo I).mkQ
  isIntertwining' g := LinearMap.ext fun φ => (quotRep_mkQ hKc hKo I g φ).symm

theorem isSmooth_quotRep : IsSmooth (quotRep hKc hKo I) := by
  intro y
  obtain ⟨φ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective y
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf (leftReg μ) φ) (fun g hg => ?_)
    (isSmooth_leftReg φ)
  rw [mem_stabilizerOf, quotRep_mkQ, mem_stabilizerOf.1 hg]

theorem heckeAct_quotRep (f φ : HeckeAlgebra μ) :
    heckeAct μ (quotRep hKc hKo I) f ((heckeKernel hKc hKo I).mkQ φ) =
      (heckeKernel hKc hKo I).mkQ (f * φ) := by
  have := map_heckeAct (μ := μ) (quotMap hKc hKo I) f.mem (isSmooth_leftReg φ)
  rw [heckeAct_leftReg] at this
  exact this.symm

theorem mkQ_mul_idem (φ : HeckeAlgebra μ) :
    (heckeKernel hKc hKo I).mkQ (φ * idem μ hKc hKo) = (heckeKernel hKc hKo I).mkQ φ := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  intro g
  rw [map_sub, leftReg_mul, map_sub, cornerₗ_mul_idem, sub_self]
  exact I.zero_mem

def toFixedQuot :
    HeckeAlgebraLevel μ K hKc hKo →ₗ[HeckeAlgebraLevel μ K hKc hKo] fixedVectors (quotRep hKc hKo I) K where
  toFun h := ⟨(heckeKernel hKc hKo I).mkQ (h : HeckeAlgebra μ), fun k hk => by
    rw [quotRep_mkQ, mem_fixedVectors_leftReg.2 (fun k' hk' x => apply_mul_left hKc hKo h hk' x) k hk]⟩
  map_add' a b := Subtype.ext (by simp only [val_add, map_add, Submodule.coe_add])
  map_smul' a h := Subtype.ext (by
    simp only [RingHom.id_apply, coe_smul_fixedVectors]
    rw [heckeAct_quotRep]
    rfl)

theorem toFixedQuot_apply (h : HeckeAlgebraLevel μ K hKc hKo) :
    ((toFixedQuot hKc hKo I h : fixedVectors (quotRep hKc hKo I) K) :
      HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) = (heckeKernel hKc hKo I).mkQ (h : HeckeAlgebra μ) := rfl

theorem ker_toFixedQuot : LinearMap.ker (toFixedQuot hKc hKo I) = I := by
  ext h
  rw [LinearMap.mem_ker]
  constructor
  · intro h0
    have hmem : (h : HeckeAlgebra μ) ∈ heckeKernel hKc hKo I := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← toFixedQuot_apply, h0]
      rfl
    have := hmem 1
    rwa [map_one, Module.End.one_apply, cornerₗ_val] at this
  · intro hI
    apply Subtype.ext
    rw [toFixedQuot_apply, Submodule.mkQ_apply, ZeroMemClass.coe_zero,
      Submodule.Quotient.mk_eq_zero]
    intro g
    obtain ⟨h1, h2⟩ := (mem_biInvariant_iff_idem hKc hKo).1 (val_mem hKc hKo h)
    have e1 : leftReg μ g (h : HeckeAlgebra μ) = leftReg μ g (idem μ hKc hKo) * h := by
      rw [← leftReg_mul, h1]
    have : cornerₗ hKc hKo (leftReg μ g (h : HeckeAlgebra μ)) =
        cornerₗ hKc hKo (leftReg μ g (idem μ hKc hKo)) * h := by
      apply HeckeAlgebraLevel.ext hKc hKo
      rw [val_mul, val_cornerₗ, val_cornerₗ, e1]
      simp only [mul_assoc, h1, h2]
    rw [this]
    exact I.smul_mem _ hI

theorem toFixedQuot_surjective : Function.Surjective (toFixedQuot hKc hKo I) := by
  intro y
  obtain ⟨φ, hφ⟩ := (heckeKernel hKc hKo I).mkQ_surjective (y : HeckeAlgebra μ ⧸ _)
  refine ⟨cornerₗ hKc hKo φ, Subtype.ext ?_⟩
  rw [toFixedQuot_apply, val_cornerₗ, mkQ_mul_idem, ← heckeAct_quotRep, hφ]
  exact heckeAct_idem_of_mem (μ := μ) hKc hKo y.2

def fixedQuotEquiv :
    (HeckeAlgebraLevel μ K hKc hKo ⧸ I) ≃ₗ[HeckeAlgebraLevel μ K hKc hKo]
      fixedVectors (quotRep hKc hKo I) K :=
  (Submodule.quotEquivOfEq I _ (ker_toFixedQuot hKc hKo I).symm).trans
    ((toFixedQuot hKc hKo I).quotKerEquivOfSurjective (toFixedQuot_surjective hKc hKo I))

theorem isIrreducible_quotRep (hI : IsCoatom I) : (quotRep hKc hKo I).IsIrreducible := by
  have hne : (toFixedQuot hKc hKo I 1 : HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) ≠ 0 := by
    intro h0
    apply hI.1
    rw [Ideal.eq_top_iff_one, ← ker_toFixedQuot hKc hKo I, LinearMap.mem_ker]
    exact Subtype.ext h0
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun X => ?_ }
  · have : (toFixedQuot hKc hKo I 1 : HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) ∈
        (⊤ : Subrepresentation (quotRep hKc hKo I)) := Submodule.mem_top
    rw [← h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · by_cases hX : ∃ y ∈ X, y ∈ fixedVectors (quotRep hKc hKo I) K ∧ y ≠ 0
    · right
      obtain ⟨y, hyX, hyK, hy0⟩ := hX
      obtain ⟨h₀, hh₀⟩ := toFixedQuot_surjective hKc hKo I ⟨y, hyK⟩
      let I' : Submodule (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) :=
        { carrier := {h | (toFixedQuot hKc hKo I h : HeckeAlgebra μ ⧸ heckeKernel hKc hKo I) ∈ X}
          add_mem' := fun {a b} ha hb => by
            simp only [mem_setOf_eq, map_add, Submodule.coe_add]
            exact X.toSubmodule.add_mem ha hb
          zero_mem' := by
            simp only [mem_setOf_eq, map_zero, ZeroMemClass.coe_zero]
            exact X.toSubmodule.zero_mem
          smul_mem' := fun a h hh => by
            simp only [mem_setOf_eq, map_smul, coe_smul_fixedVectors]
            exact heckeAct_mem_subrep X (a : HeckeAlgebra μ).mem (isSmooth_quotRep hKc hKo I _) hh }
      have hII' : I < I' := by
        refine lt_of_le_of_ne (fun h hh => ?_) fun heq => ?_
        · show _ ∈ X
          have : toFixedQuot hKc hKo I h = 0 := by rwa [← LinearMap.mem_ker, ker_toFixedQuot]
          rw [this]
          exact X.toSubmodule.zero_mem
        · have : h₀ ∈ I' := show _ ∈ X by rw [hh₀]; exact hyX
          rw [← heq, ← ker_toFixedQuot hKc hKo I, LinearMap.mem_ker, hh₀] at this
          exact hy0 (congrArg Subtype.val this)
      have h1 : (1 : HeckeAlgebraLevel μ K hKc hKo) ∈ I' := by
        rw [hI.2 I' hII']
        trivial
      rw [eq_top_iff]
      intro z _
      obtain ⟨φ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective z
      rw [← mkQ_mul_idem hKc hKo I φ, ← heckeAct_quotRep]
      exact heckeAct_mem_subrep X φ.mem (isSmooth_quotRep hKc hKo I _) h1
    · left
      push_neg at hX
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨φ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective z
      show _ ∈ (⊥ : Submodule ℂ _)
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      intro g
      have hmem : heckeAct μ (quotRep hKc hKo I) (idem μ hKc hKo)
          (quotRep hKc hKo I g ((heckeKernel hKc hKo I).mkQ φ)) = 0 :=
        hX _ (heckeAct_mem_subrep X (idem μ hKc hKo).mem (isSmooth_quotRep hKc hKo I _)
          (X.apply_mem_toSubmodule g hz))
          (heckeAct_idem_mem hKc hKo (isSmooth_quotRep hKc hKo I _))
      rw [quotRep_mkQ, heckeAct_quotRep, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
      have := hmem 1
      rwa [map_one, Module.End.one_apply, cornerₗ_idem_mul] at this

end Construction

section Classification

open HeckeAlgebraLevel

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

def orbitMap (v : V) (hv : v ∈ smoothVectors ρ) : HeckeAlgebra μ →ₗ[ℂ] V where
  toFun f := heckeAct μ ρ f v
  map_add' a b := by
    rw [coe_add]
    exact heckeAct_add_left a.mem b.mem hv
  map_smul' c a := by
    rw [coe_smul]
    exact heckeAct_smul_left c a.mem hv

theorem nonempty_equiv_quotRep (I : Submodule (HeckeAlgebraLevel μ K hKc hKo)
    (HeckeAlgebraLevel μ K hKc hKo)) (hρ : IsSmooth ρ) [ρ.IsIrreducible] {v₀ : V}
    (hv₀ : v₀ ∈ fixedVectors ρ K) (h0 : v₀ ≠ 0)
    (hI : ∀ h : HeckeAlgebraLevel μ K hKc hKo, h ∈ I ↔ heckeAct μ ρ (h : HeckeAlgebra μ) v₀ = 0) :
    Nonempty ((quotRep hKc hKo I).Equiv ρ) := by
  let Φ := orbitMap (μ := μ) v₀ (hρ v₀)
  have hΦ : ∀ f, Φ f = heckeAct μ ρ f v₀ := fun _ => rfl
  have crit : ∀ x : V, (∀ g, heckeAct μ ρ (idem μ hKc hKo) (ρ g x) = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hle : Submodule.span ℂ (range fun g => ρ g x) ≤
        LinearMap.ker (heckeRep (μ := μ) hρ (idem μ hKc hKo)) :=
      Submodule.span_le.2 (by
        rintro _ ⟨g, rfl⟩
        exact hx g)
    have := hle (mem_span_orbit hx0 v₀)
    rw [LinearMap.mem_ker, heckeRep_apply, heckeAct_idem_of_mem (μ := μ) hKc hKo hv₀] at this
    exact h0 this
  have key : ∀ φ g, heckeAct μ ρ (idem μ hKc hKo) (ρ g (Φ φ)) =
      heckeAct μ ρ (cornerₗ hKc hKo (leftReg μ g φ) : HeckeAlgebra μ) v₀ := by
    intro φ g
    rw [hΦ, heckeAct_ltrans g φ.mem (hρ v₀)]
    change heckeAct μ ρ (idem μ hKc hKo) (heckeAct μ ρ (leftReg μ g φ : HeckeAlgebra μ) v₀) = _
    rw [← heckeAct_mul _ _ (hρ v₀)]
    exact (heckeAct_corner hKc hKo hv₀ _).symm
  have hker : ∀ φ, Φ φ = 0 ↔ φ ∈ heckeKernel hKc hKo I := by
    intro φ
    constructor
    · intro h g
      rw [hI, ← key, h, map_zero]
      exact heckeAct_zero_right (idem μ hKc hKo).mem
    · intro h
      refine crit _ fun g => ?_
      rw [key, ← hI]
      exact h g
  have hint : ∀ g φ, Φ (leftReg μ g φ) = ρ g (Φ φ) := fun g φ =>
    (heckeAct_ltrans g φ.mem (hρ v₀)).symm
  have hsurj : Function.Surjective Φ := by
    intro w
    have hle : Submodule.span ℂ (range fun g => ρ g v₀) ≤ LinearMap.range Φ :=
      Submodule.span_le.2 (by
        rintro _ ⟨g, rfl⟩
        exact ⟨leftReg μ g (idem μ hKc hKo), by
          rw [hint, hΦ, heckeAct_idem_of_mem (μ := μ) hKc hKo hv₀]⟩)
    exact hle (mem_span_orbit h0 w)
  let T : HeckeAlgebra μ ⧸ heckeKernel hKc hKo I →ₗ[ℂ] V :=
    (heckeKernel hKc hKo I).liftQ Φ (fun φ hφ => (hker φ).2 hφ)
  let Tint : Representation.IntertwiningMap (quotRep hKc hKo I) ρ :=
    { toLinearMap := T
      isIntertwining' := fun g => (heckeKernel hKc hKo I).linearMap_qext
        (LinearMap.ext fun φ => hint g φ) }
  refine ⟨Tint.ofBijective ⟨fun y z hyz => ?_, fun w => ?_⟩⟩
  · obtain ⟨φ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective y
    obtain ⟨ψ, rfl⟩ := (heckeKernel hKc hKo I).mkQ_surjective z
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hker, map_sub,
      sub_eq_zero]
    exact hyz
  · obtain ⟨φ, rfl⟩ := hsurj w
    exact ⟨(heckeKernel hKc hKo I).mkQ φ, rfl⟩

theorem exists_irreducible_fixedVectors_equiv (M : Type*) [AddCommGroup M]
    [Module (HeckeAlgebraLevel μ K hKc hKo) M] [IsSimpleModule (HeckeAlgebraLevel μ K hKc hKo) M] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ G V),
      IsSmooth ρ ∧ ρ.IsIrreducible ∧
        Nonempty (fixedVectors ρ K ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] M) := by
  have hs := (isSimpleModule_iff_toSpanSingleton_surjective (R := HeckeAlgebraLevel μ K hKc hKo)
    (M := M)).1 inferInstance
  haveI := hs.1
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  set I := LinearMap.ker (LinearMap.toSpanSingleton (HeckeAlgebraLevel μ K hKc hKo) M m)
  let eM : (HeckeAlgebraLevel μ K hKc hKo ⧸ I) ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] M :=
    LinearMap.quotKerEquivOfSurjective _ (hs.2 m hm)
  have hI : IsCoatom I := isSimpleModule_iff_isCoatom.1 (IsSimpleModule.congr eM)
  exact ⟨_, _, _, quotRep hKc hKo I, isSmooth_quotRep hKc hKo I, isIrreducible_quotRep hKc hKo I hI,
    ⟨(fixedQuotEquiv hKc hKo I).symm.trans eM⟩⟩

theorem nonempty_equiv_of_fixedVectors_equiv {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (hρ : IsSmooth ρ) (hσ : IsSmooth σ) [ρ.IsIrreducible]
    [σ.IsIrreducible] (hK : fixedVectors ρ K ≠ ⊥)
    (e : fixedVectors ρ K ≃ₗ[HeckeAlgebraLevel μ K hKc hKo] fixedVectors σ K) :
    Nonempty (ρ.Equiv σ) := by
  obtain ⟨v₀, hv₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  set I := LinearMap.ker (LinearMap.toSpanSingleton (HeckeAlgebraLevel μ K hKc hKo)
    (fixedVectors ρ K) ⟨v₀, hv₀⟩)
  have hIρ : ∀ h : HeckeAlgebraLevel μ K hKc hKo, h ∈ I ↔
      heckeAct μ ρ (h : HeckeAlgebra μ) v₀ = 0 := by
    intro h
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Subtype.ext_iff]
    rfl
  have hIσ : ∀ h : HeckeAlgebraLevel μ K hKc hKo, h ∈ I ↔
      heckeAct μ σ (h : HeckeAlgebra μ) (e ⟨v₀, hv₀⟩ : W) = 0 := by
    intro h
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← e.map_eq_zero_iff, e.map_smul,
      Subtype.ext_iff]
    rfl
  have hw0 : (e ⟨v₀, hv₀⟩ : W) ≠ 0 := fun h =>
    h0 (congrArg Subtype.val (e.map_eq_zero_iff.1 (Subtype.ext h)))
  obtain ⟨A⟩ := nonempty_equiv_quotRep hKc hKo I hρ hv₀ h0 hIρ
  obtain ⟨B⟩ := nonempty_equiv_quotRep hKc hKo I hσ (e ⟨v₀, hv₀⟩).2 hw0 hIσ
  exact ⟨A.symm.trans B⟩

end Classification

end HeckeAlgebra

end GroundTheory.Automorphic
