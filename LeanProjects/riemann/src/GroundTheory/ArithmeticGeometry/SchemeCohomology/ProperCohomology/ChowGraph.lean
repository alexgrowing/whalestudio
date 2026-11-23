import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SchemeImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

noncomputable section

namespace ChowGraph

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (s : X ⟶ Spec (.of A))
  {k : ℕ} (n : Fin (k + 1) → ℕ) (U : Fin (k + 1) → X.Opens)
  (c : ∀ i, (U i).toScheme ⟶ (ProjSpace.stdOpen A (n i) 0).toScheme)
  (hc : ∀ i, c i ≫ (ProjSpace.stdOpen A (n i) 0).ι ≫ ProjSpace.toSpecBase A (n i) = (U i).ι ≫ s)

abbrev W : X.Opens := ⨅ i, U i

def gP : (W U).toScheme ⟶ ProjSpace.MP A k n :=
  ProjSpace.lift k n ((W U).ι ≫ s)
    (fun i => X.homOfLE (iInf_le U i) ≫ c i ≫ (ProjSpace.stdOpen A (n i) 0).ι) (fun i => by
      rw [Category.assoc, Category.assoc, hc i, ← Category.assoc, Scheme.homOfLE_ι])

@[reassoc (attr := simp)]
lemma gP_mpStr : gP s n U c hc ≫ ProjSpace.mpStr A k n = (W U).ι ≫ s :=
  ProjSpace.lift_mpStr _ _ _ _ _

@[reassoc (attr := simp)]
lemma gP_pr (i : Fin (k + 1)) : gP s n U c hc ≫ ProjSpace.pr A k n i =
    X.homOfLE (iInf_le U i) ≫ c i ≫ (ProjSpace.stdOpen A (n i) 0).ι :=
  ProjSpace.lift_pr _ _ _ _ _ i

abbrev G : Scheme.{u} := pullback s (ProjSpace.mpStr A k n)

def g : (W U).toScheme ⟶ G s n :=
  pullback.lift (W U).ι (gP s n U c hc) (gP_mpStr s n U c hc).symm

@[reassoc (attr := simp)]
lemma g_fst : g s n U c hc ≫ pullback.fst _ _ = (W U).ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma g_snd : g s n U c hc ≫ pullback.snd _ _ = gP s n U c hc := pullback.lift_snd _ _ _

lemma isIso_morphismRestrict_of_eq_ι {T : Scheme.{u}} (V : T.Opens) (h : V.toScheme ⟶ T)
    (hh : h = V.ι) : IsIso (h ∣_ V) := by
  subst hh
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  refine ⟨⟨x, by simp⟩, ?_⟩
  exact Subtype.ext ((morphismRestrict_base_coe _ _ _).trans rfl)

variable [IsProper (ProjSpace.mpStr A k n)]

omit [IsProper (ProjSpace.mpStr A k n)] in

lemma isIso_g_restrict_comp : IsIso ((g s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ W U)) ≫
      (pullback.fst s (ProjSpace.mpStr A k n) ∣_ W U)) := by
  rw [← morphismRestrict_comp]
  exact isIso_morphismRestrict_of_eq_ι _ _ (g_fst s n U c hc)

instance isClosedImmersion_g_restrict :
    IsClosedImmersion (g s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ W U)) := by
  have h1 : IsIso ((g s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ W U)) ≫
      (pullback.fst s (ProjSpace.mpStr A k n) ∣_ W U)) := by
    rw [← morphismRestrict_comp]
    exact isIso_morphismRestrict_of_eq_ι _ _ (g_fst s n U c hc)
  exact IsClosedImmersion.of_comp _ (pullback.fst s (ProjSpace.mpStr A k n) ∣_ W U)

variable [QuasiCompact (g s n U c hc)]

abbrev X' : Scheme.{u} := (g s n U c hc).image

abbrev ι' : X' s n U c hc ⟶ G s n := (g s n U c hc).imageι

abbrev π : X' s n U c hc ⟶ X := ι' s n U c hc ≫ pullback.fst _ _

abbrev q : X' s n U c hc ⟶ ProjSpace.MP A k n := ι' s n U c hc ≫ pullback.snd _ _

theorem isIso_π_restrict : IsIso (π s n U c hc ∣_ W U) := by
  have h1 := isIso_g_restrict_comp s n U c hc
  rw [π, morphismRestrict_comp, ← SchemeImage.imageRestrictLift_fac, Category.assoc]
  exact IsIso.comp_isIso' (SchemeImage.isIso_imageRestrictLift _ _) h1

abbrev V (i : Fin (k + 1)) : (ProjSpace.MP A k n).Opens :=
  ProjSpace.pr A k n i ⁻¹ᵁ ProjSpace.stdOpen A (n i) 0

abbrev αU (i : Fin (k + 1)) : (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i).toScheme ⟶
    projectiveSpace A (n i) :=
  (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i).ι ≫ pullback.snd _ _ ≫ ProjSpace.pr A k n i

abbrev βU (i : Fin (k + 1)) : (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i).toScheme ⟶
    projectiveSpace A (n i) :=
  (pullback.fst s (ProjSpace.mpStr A k n) ∣_ U i) ≫ c i ≫ (ProjSpace.stdOpen A (n i) 0).ι

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] in
include hc in
lemma αU_βU_over (i : Fin (k + 1)) :
    αU s n U i ≫ ProjSpace.toSpecBase A (n i) = βU s n U c i ≫ ProjSpace.toSpecBase A (n i) := by
  rw [αU, βU, Category.assoc, Category.assoc, ProjSpace.pr_toSpecBase, Category.assoc,
    Category.assoc, hc i, morphismRestrict_ι_assoc, ← pullback.condition]

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] in

lemma g_restrict_αU (i : Fin (k + 1)) :
    (g s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)) ≫ αU s n U i =
      (g s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)) ≫ βU s n U c i := by
  have hinc : (g s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)) ≫
      (pullback.fst s (ProjSpace.mpStr A k n) ∣_ U i) =
      (g s n U c hc ⁻¹ᵁ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)).ι ≫
        X.homOfLE (iInf_le U i) := by
    rw [← cancel_mono (U i).ι, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      g_fst, Category.assoc, Scheme.homOfLE_ι]
  rw [αU, βU, morphismRestrict_ι_assoc, reassoc_of% hinc, g_snd_assoc, gP_pr]

omit [IsProper (ProjSpace.mpStr A k n)] in

theorem q_mem_V (i : Fin (k + 1)) (y : X' s n U c hc) (hy : π s n U c hc y ∈ U i) :
    q s n U c hc y ∈ V n i := by
  obtain ⟨κ, hκ⟩ := SchemeImage.exists_lift_imageι_morphismRestrict (g s n U c hc)
    (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)
    (eqLocusι (ProjSpace.toSpecBase A (n i)) (αU s n U i) (βU s n U c i)
      (αU_βU_over s n U c hc i))
    (eqLocusLift _ _ _ _ (g s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i))
      (g_restrict_αU s n U c hc i)) (eqLocusLift_ι _ _ _ _ _ _)
  have hE : (ι' s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)) ≫ αU s n U i =
      (ι' s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)) ≫ βU s n U c i := by
    rw [← hκ, Category.assoc, Category.assoc, eqLocusι_comp_eq]
  have hy' : y ∈ ι' s n U c hc ⁻¹ᵁ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i) := hy
  have hE' : (ι' s n U c hc ⁻¹ᵁ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)).ι ≫
      q s n U c hc ≫ ProjSpace.pr A k n i =
      ((ι' s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)) ≫
        (pullback.fst s (ProjSpace.mpStr A k n) ∣_ U i) ≫ c i) ≫ (ProjSpace.stdOpen A (n i) 0).ι := by
    have := hE
    simp only [αU, βU, morphismRestrict_ι_assoc] at this
    simpa only [q, Category.assoc] using this
  have h2 : (⟨y, hy'⟩ : (ι' s n U c hc ⁻¹ᵁ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)).toScheme) ∈
      ((ι' s n U c hc ⁻¹ᵁ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)).ι ≫
        q s n U c hc ≫ ProjSpace.pr A k n i) ⁻¹ᵁ ProjSpace.stdOpen A (n i) 0 := by
    rw [hE']
    exact Subtype.prop (((ι' s n U c hc ∣_ (pullback.fst s (ProjSpace.mpStr A k n) ⁻¹ᵁ U i)) ≫
      (pullback.fst s (ProjSpace.mpStr A k n) ∣_ U i) ≫ c i).base ⟨y, hy'⟩)
  exact h2

section OverV

variable (i : Fin (k + 1))

abbrev ρ : (V (A := A) n i).toScheme ⟶ (ProjSpace.stdOpen A (n i) 0).toScheme :=
  ProjSpace.pr A k n i ∣_ ProjSpace.stdOpen A (n i) 0

abbrev F : Scheme.{u} := pullback (c i) (ρ (A := A) n i)

abbrev O : (G s n).Opens := pullback.snd s (ProjSpace.mpStr A k n) ⁻¹ᵁ V (A := A) n i

abbrev τ : (O s n i).toScheme ⟶ (V (A := A) n i).toScheme := pullback.snd s (ProjSpace.mpStr A k n) ∣_ V (A := A) n i

abbrev E : Scheme.{u} := pullback (pullback.snd (c i) (ρ (A := A) n i)) (τ s n i)

abbrev eX : E s n U c i ⟶ X := pullback.fst _ _ ≫ pullback.fst _ _ ≫ (U i).ι

abbrev eX' : E s n U c i ⟶ X := pullback.snd _ _ ≫ (O s n i).ι ≫ pullback.fst _ _

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] in
include hc in
lemma eX_eX'_over : eX s n U c i ≫ s = eX' s n U c i ≫ s := by
  have h1 : pullback.fst (c i) (ρ (A := A) n i) ≫ c i ≫ (ProjSpace.stdOpen A (n i) 0).ι =
      pullback.snd (c i) (ρ (A := A) n i) ≫ (V (A := A) n i).ι ≫ ProjSpace.pr A k n i := by
    rw [← morphismRestrict_ι, ← Category.assoc, pullback.condition, Category.assoc]
  have h2 := congrArg (· ≫ ProjSpace.toSpecBase A (n i)) h1
  simp only [Category.assoc, hc i, ProjSpace.pr_toSpecBase] at h2
  simp only [eX, eX', Category.assoc, h2, pullback.condition]
  rw [pullback.condition_assoc, morphismRestrict_ι_assoc]

variable [IsSeparated s]

abbrev Q : Scheme.{u} := eqLocus s (eX s n U c i) (eX' s n U c i) (eX_eX'_over s n U c hc i)

abbrev Qo : Q s n U c hc i ⟶ (O s n i).toScheme := eqLocusι _ _ _ _ ≫ pullback.snd _ _

abbrev Qφ : Q s n U c hc i ⟶ F n U c i := eqLocusι _ _ _ _ ≫ pullback.fst _ _

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] [IsSeparated s] in
include hc in

lemma F_over : pullback.fst (c i) (ρ (A := A) n i) ≫ (U i).ι ≫ s =
    pullback.snd (c i) (ρ (A := A) n i) ≫ (V (A := A) n i).ι ≫ ProjSpace.mpStr A k n := by
  have h1 : pullback.fst (c i) (ρ (A := A) n i) ≫ c i ≫ (ProjSpace.stdOpen A (n i) 0).ι =
      pullback.snd (c i) (ρ (A := A) n i) ≫ (V (A := A) n i).ι ≫ ProjSpace.pr A k n i := by
    rw [← morphismRestrict_ι, ← Category.assoc, pullback.condition, Category.assoc]
  have h2 := congrArg (· ≫ ProjSpace.toSpecBase A (n i)) h1
  simpa only [Category.assoc, hc i, ProjSpace.pr_toSpecBase] using h2

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] [IsSeparated s] in

def gF : (g s n U c hc ⁻¹ᵁ O s n i).toScheme ⟶ F n U c i :=
  pullback.lift ((g s n U c hc ⁻¹ᵁ O s n i).ι ≫ X.homOfLE (iInf_le U i))
    ((g s n U c hc ∣_ O s n i) ≫ τ s n i) (by
      rw [← cancel_mono (ProjSpace.stdOpen A (n i) 0).ι]
      simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, g_snd_assoc, gP_pr])

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] [IsSeparated s] in

def gE : (g s n U c hc ⁻¹ᵁ O s n i).toScheme ⟶ E s n U c i :=
  pullback.lift (gF s n U c hc i) (g s n U c hc ∣_ O s n i) (pullback.lift_snd _ _ _)

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] in

def gQ : (g s n U c hc ⁻¹ᵁ O s n i).toScheme ⟶ Q s n U c hc i :=
  eqLocusLift _ _ _ _ (gE s n U c hc i) (by
    simp only [gE, gF, eX, eX', pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι_assoc, g_fst])

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] [IsSeparated s] in
@[reassoc]
lemma gQ_Qo : gQ s n U c hc i ≫ Qo s n U c hc i = g s n U c hc ∣_ O s n i := by
  simp only [gQ, Qo, eqLocusLift_ι_assoc, gE]
  exact pullback.lift_snd _ _ _

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] in

def σG : F n U c i ⟶ G s n :=
  pullback.lift (pullback.fst _ _ ≫ (U i).ι) (pullback.snd _ _ ≫ (V (A := A) n i).ι)
    (by simpa only [Category.assoc] using F_over s n U c hc i)

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] [IsSeparated s] in
lemma range_σG : Set.range (σG s n U c hc i).base ⊆ Set.range (O s n i).ι.base := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (pullback.snd s (ProjSpace.mpStr A k n)).base ((σG s n U c hc i).base x) ∈ V (A := A) n i
  have : σG s n U c hc i ≫ pullback.snd s (ProjSpace.mpStr A k n) =
      pullback.snd _ _ ≫ (V (A := A) n i).ι := pullback.lift_snd _ _ _
  have h2 : x ∈ (σG s n U c hc i ≫ pullback.snd s (ProjSpace.mpStr A k n)) ⁻¹ᵁ V (A := A) n i := by
    rw [this]
    exact Subtype.prop ((pullback.snd (c i) (ρ (A := A) n i)).base x)
  exact h2

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] in

def σO : F n U c i ⟶ (O s n i).toScheme :=
  IsOpenImmersion.lift (O s n i).ι (σG s n U c hc i) (range_σG s n U c hc i)

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] [IsSeparated s] in
@[reassoc (attr := simp)]
lemma σO_ι : σO s n U c hc i ≫ (O s n i).ι = σG s n U c hc i := IsOpenImmersion.lift_fac _ _ _

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] in

def σE : F n U c i ⟶ E s n U c i :=
  pullback.lift (𝟙 _) (σO s n U c hc i) (by
    rw [← cancel_mono (V (A := A) n i).ι]
    simp only [Category.assoc, Category.id_comp, τ, morphismRestrict_ι, σO_ι_assoc, σG]
    exact (pullback.lift_snd _ _ _).symm)

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] in

def σ : F n U c i ⟶ Q s n U c hc i :=
  eqLocusLift _ _ _ _ (σE s n U c hc i) (by
    simp only [σE, eX, eX', pullback.lift_fst_assoc, pullback.lift_snd_assoc, σO_ι_assoc, σG,
      Category.id_comp, pullback.lift_fst])

omit [IsProper (ProjSpace.mpStr A k n)] [QuasiCompact (g s n U c hc)] in

instance isIso_Qφ [IsClosedImmersion (c i)] : IsIso (Qφ s n U c hc i) := by
  refine ⟨⟨σ s n U c hc i, ?_, ?_⟩⟩
  · have hmono : Mono (Qo s n U c hc i) := by unfold Qo; infer_instance
    rw [← cancel_mono (Qo s n U c hc i), Category.id_comp]
    rw [← cancel_mono (O s n i).ι]
    apply pullback.hom_ext
    · simp only [Qφ, Qo, σ, Category.assoc, eqLocusLift_ι_assoc, σE, pullback.lift_snd_assoc,
        σO_ι_assoc, σG, pullback.lift_fst]
      exact eqLocusι_comp_eq _ _ _ _
    · simp only [Qφ, Qo, σ, Category.assoc, eqLocusLift_ι_assoc, σE, σO_ι_assoc, σG,
        pullback.lift_snd]
      rw [← morphismRestrict_ι, pullback.condition_assoc]
  · simp only [Qφ, σ, eqLocusLift_ι_assoc, σE, pullback.lift_fst]

omit [IsProper (ProjSpace.mpStr A k n)] in

theorem isClosedImmersion_q_restrict [IsClosedImmersion (c i)] :
    IsClosedImmersion (q s n U c hc ∣_ V (A := A) n i) := by
  have hQo : IsClosedImmersion (Qo s n U c hc i) := by unfold Qo; infer_instance
  obtain ⟨κ, hκ⟩ := SchemeImage.exists_lift_imageι_morphismRestrict (g s n U c hc) (O s n i)
    (Qo s n U c hc i) (gQ s n U c hc i) (gQ_Qo s n U c hc i)
  have hκc : IsClosedImmersion κ := by
    have : IsClosedImmersion (κ ≫ Qo s n U c hc i) := by rw [hκ]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion κ (Qo s n U c hc i)
  have e : q s n U c hc ∣_ V (A := A) n i =
      κ ≫ Qφ s n U c hc i ≫ pullback.snd (c i) (ρ (A := A) n i) := by
    change (ι' s n U c hc ≫ pullback.snd _ _) ∣_ V (A := A) n i = _
    rw [morphismRestrict_comp]
    change (ι' s n U c hc ∣_ O s n i) ≫ τ s n i = _
    rw [← hκ, Category.assoc]
    congr 1
    simp only [Qo, Qφ, Category.assoc]
    rw [pullback.condition]
  rw [e]
  have h1 : IsClosedImmersion (Qφ s n U c hc i) := inferInstance
  have h2 : IsClosedImmersion (Qφ s n U c hc i ≫ pullback.snd (c i) (ρ (A := A) n i)) :=
    inferInstance
  exact @IsClosedImmersion.comp _ _ _ κ _ hκc h2

end OverV

theorem isClosedImmersion_q [IsProper s] (hU : iSup U = ⊤) [∀ i, IsClosedImmersion (c i)] :
    IsClosedImmersion (q s n U c hc) := by
  have hp : IsProper (q s n U c hc ≫ ProjSpace.mpStr A k n) := by
    change IsProper ((ι' s n U c hc ≫ pullback.snd _ _) ≫ ProjSpace.mpStr A k n)
    rw [Category.assoc, ← pullback.condition]
    infer_instance
  have hq : IsProper (q s n U c hc) := IsProper.of_comp _ (ProjSpace.mpStr A k n)
  have hcl : IsClosed (Set.range (q s n U c hc).base) := (q s n U c hc).isClosedMap.isClosed_range
  let W' : Option (Fin (k + 1)) → (ProjSpace.MP A k n).Opens := fun o =>
    o.elim ⟨(Set.range (q s n U c hc).base)ᶜ, hcl.isOpen_compl⟩ (fun i => V (A := A) n i)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top W' ?_ ?_
  · refine top_le_iff.1 fun p _ => ?_
    by_cases hpr : p ∈ Set.range (q s n U c hc).base
    · obtain ⟨y, rfl⟩ := hpr
      have hy : π s n U c hc y ∈ (⊤ : X.Opens) := trivial
      rw [← hU] at hy
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
      exact Opens.mem_iSup.2 ⟨some i, q_mem_V s n U c hc i y hi⟩
    · exact Opens.mem_iSup.2 ⟨none, hpr⟩
  · rintro (_ | i)
    · have : IsEmpty (q s n U c hc ⁻¹ᵁ W' none).toScheme :=
        ⟨fun x => x.2 ⟨x.1, rfl⟩⟩
      infer_instance
    · exact isClosedImmersion_q_restrict s n U c hc i

end ChowGraph

end

end GroundTheory.Arith.SchemeCoh
