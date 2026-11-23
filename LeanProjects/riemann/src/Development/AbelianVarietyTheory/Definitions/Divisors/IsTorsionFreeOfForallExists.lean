import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res homOfLinear homOfLinear_app isoOfLinear toMod fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover germ_resM)
open GlobalTheory.QCoh (IsFiniteQC appLinear appLinear_apply stalkLinear freeModule)

namespace GlobalTheory.VB

variable {X Y : Scheme.{0}} {F G H : X.Modules} {U V W : X.Opens} {r s : ℕ}

structure IsCohSub (i : G ⟶ F) : Prop where

  mono : Mono i

  isFiniteQC : IsFiniteQC G

structure IsSubbundle (i : G ⟶ F) : Prop where

  mono : Mono i

  isVB_cokernel : ∃ s, IsVB (cokernel i) s

theorem isCohSub_id [h : IsFiniteQC F] : IsCohSub (𝟙 F) := ⟨inferInstance, h⟩

theorem isCohSub_of_isZero (h : IsZero G) (i : G ⟶ F) : IsCohSub i := ⟨h.mono i, .of_isZero h⟩

theorem IsCohSub.comp {i : G ⟶ F} (h : IsCohSub i) (j : F ⟶ H) [Mono j] : IsCohSub (i ≫ j) :=
  have := h.mono
  ⟨inferInstance, h.isFiniteQC⟩

theorem isSubbundle_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : IsVB S.X₃ s) : IsSubbundle S.f :=
  ⟨hS.mono_f, s, h.of_iso (hS.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _))⟩

theorem isSubbundle_of_isIso (i : G ⟶ F) [IsIso i] : IsSubbundle i :=
  ⟨inferInstance, 0, isVB_zero_iff.2 (isZero_cokernel_of_epi i)⟩

theorem isSubbundle_inl (h : IsVB G s) : IsSubbundle (biprod.inl : F ⟶ F ⊞ G) :=
  isSubbundle_of_shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact h

theorem exists_app_eq_of_epi (φ : F ⟶ G) [Epi φ] (s : Γ(G, V)) {x : X} (hx : x ∈ V) :
    ∃ (W : X.Opens) (h : W ≤ V), x ∈ W ∧ ∃ t, φ.app W t = resM G h s := by
  obtain ⟨t, ht⟩ := QCoh.stalkLinear_surjective φ x (G.presheaf.germ V x hx s)
  obtain ⟨T, hT, hxT, t, rfl⟩ := Twist.exists_germ_eq_of_mem hx t
  rw [QCoh.stalkLinear_germ, ← germ_resM hT hxT] at ht
  obtain ⟨T', hxT', i₁, i₂, e⟩ := G.presheaf.germ_eq x hxT hxT _ _ ht
  exact ⟨T', i₁.le.trans hT, hxT', resM F i₁.le t,
    (app_resM φ _ t).trans (e.trans (resM_resM hT i₂.le s))⟩

section Integral

variable [IsIntegral X]

theorem genericPoint_mem {x : X} (hx : x ∈ V) : genericPoint X ∈ V :=
  (genericPoint_specializes x).mem_open V.isOpen hx

variable (F) in

abbrev genStalk : Type := (F.presheaf.stalk (genericPoint X) :)

variable (F) in

def genRank : ℕ := Module.finrank X.functionField (genStalk F)

theorem genRank_congr (φ : F ≅ G) : genRank F = genRank G :=
  (QCoh.stalkLinearEquiv φ _).finrank_eq

theorem IsVB.genRank_eq (h : IsVB F r) : genRank F = r := h.finrank_stalk _

theorem genRank_eq_zero_iff [IsFiniteQC F] : genRank F = 0 ↔ genericPoint X ∉ QCoh.support F :=
  (Module.finrank_zero_iff (R := X.functionField)).trans QCoh.notMem_support_iff.symm

theorem genRank_eq_zero_of_isZero (h : IsZero F) : genRank F = 0 := (isVB_zero_iff.2 h).genRank_eq

theorem genRank_le_of_mono (i : G ⟶ F) [Mono i] [IsFiniteQC F] : genRank G ≤ genRank F :=
  LinearMap.finrank_le_finrank_of_injective (QCoh.stalkLinear_injective i _)

theorem genRank_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) [IsFiniteQC S.X₂] :
    genRank S.X₂ = genRank S.X₁ + genRank S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have e := (QCoh.exact_iff_stalkLinear S).1 hS.exact (genericPoint X)
  have h := LinearMap.finrank_range_add_finrank_ker (K := X.functionField)
    (stalkLinear S.g (genericPoint X))
  rw [LinearMap.range_eq_top.2 (QCoh.stalkLinear_surjective S.g _), finrank_top, e.linearMap_ker_eq,
    LinearMap.finrank_range_of_inj (QCoh.stalkLinear_injective S.f _)] at h
  exact h.symm.trans (add_comm _ _)

theorem genRank_cokernel (i : G ⟶ F) [Mono i] [h : IsFiniteQC F] :
    genRank F = genRank G + genRank (cokernel i) :=
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  have := @genRank_shortExact _ _ _ hS h
  this

def Sub.ofGeneric (N : Submodule X.functionField (genStalk F)) : Sub F where
  sec V :=
    { carrier := {s | ∀ h : genericPoint X ∈ V, F.presheaf.germ V _ h s ∈ N}
      add_mem' := fun hs ht h => by rw [map_add]; exact add_mem (hs h) (ht h)
      zero_mem' := fun h => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun a s hs h => by rw [QCoh.germ_smul]; exact N.smul_mem _ (hs h) }
  res_mem h s hs hx := by rw [germ_resM]; exact hs (h hx)
  mem_of_local H hx := by
    obtain ⟨W, h, hxW, hs⟩ := H _ hx
    have := hs hxW
    rwa [germ_resM] at this

theorem Sub.mem_ofGeneric {N : Submodule X.functionField (genStalk F)} {s : Γ(F, V)} :
    s ∈ (Sub.ofGeneric N).sec V ↔ ∀ h : genericPoint X ∈ V, F.presheaf.germ V _ h s ∈ N := Iff.rfl

instance Sub.isQuasicoherent_ofGeneric [F.IsQuasicoherent]
    (N : Submodule X.functionField (genStalk F)) : (Sub.ofGeneric N).toMod.IsQuasicoherent := by
  refine Sub.isQuasicoherent _ fun U _ f t ht => ⟨1, ?_⟩
  by_cases hf : f = 0
  · rw [hf, pow_one, zero_smul]; exact zero_mem _
  · obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 (mt (basicOpen_eq_bot_iff f).1 hf)
    refine Submodule.smul_mem _ _ fun h => ?_
    have := ht (genericPoint_mem hx)
    rwa [germ_resM] at this

theorem Sub.range_stalkLinear_ofGeneric (N : Submodule X.functionField (genStalk F)) :
    LinearMap.range (stalkLinear (Sub.ofGeneric N).incl (genericPoint X)) = N := by
  refine le_antisymm ?_ fun t ht => ?_
  · rintro _ ⟨t, rfl⟩
    obtain ⟨V, hV, s, rfl⟩ := (Sub.ofGeneric N).toMod.presheaf.exists_germ_eq t
    rw [QCoh.stalkLinear_germ]
    exact (Sub.ofGeneric N).incl_app_mem s hV
  · obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
    exact ⟨_, QCoh.stalkLinear_germ _ _ hV ((Sub.ofGeneric N).mkSec s fun _ => ht)⟩

variable (F) in

def IsTorsionFree : Prop :=
  ∀ (V : X.Opens) (h : genericPoint X ∈ V) (s : Γ(F, V)), F.presheaf.germ V _ h s = 0 → s = 0

theorem IsTorsionFree.of_mono (h : IsTorsionFree F) (i : G ⟶ F) [Mono i] : IsTorsionFree G :=
  fun V hV s hs => QCoh.injective_app_of_mono i V <| (h V hV _ (by
    rw [← QCoh.stalkLinear_germ, hs, map_zero])).trans (map_zero _).symm

theorem isTorsionFree_of_forall_exists
    (H : ∀ (V : X.Opens) (h : genericPoint X ∈ V) (s : Γ(F, V)), F.presheaf.germ V _ h s = 0 →
      ∀ x ∈ V, ∃ (W : X.Opens) (h' : W ≤ V), x ∈ W ∧ resM F h' s = 0) : IsTorsionFree F := by
  intro V hV s hs
  choose W hW hx h0 using fun x : V => H V hV s hs x x.2
  exact sec_ext_of_cover W hW (fun x hxV => Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩) fun x =>
    (h0 x).trans (map_zero _).symm

theorem IsVB.isTorsionFree (h : IsVB F r) : IsTorsionFree F := by
  refine isTorsionFree_of_forall_exists fun V hV s hs x hx => ?_
  obtain ⟨U, e, -, hxU, hle, he⟩ := h.exists_affine hx
  have hU := genericPoint_mem hxU
  refine ⟨U, hle, hxU, ?_⟩
  obtain ⟨a, ha⟩ := (he U le_rfl).2 (resM F hle s)
  have h0 : ∑ i, X.presheaf.germ U _ hU (a i) • he.stalkBasis _ hU i = 0 := by
    rw [← hs, ← germ_resM hle hU, ← ha]
    simp only [Fintype.linearCombination_apply, map_sum, QCoh.germ_smul, resM_self,
      IsFrame.stalkBasis_apply]
  have h1 : a = 0 := funext fun i => germ_injective_of_isIntegral X _ hU
    ((Fintype.linearIndependent_iff.1 (he.stalkBasis _ hU).linearIndependent _ h0 i).trans
      (map_zero _).symm)
  rw [← ha, h1, map_zero]

theorem IsTorsionFree.eq_zero_of_smul (h : IsTorsionFree F) {a : Γ(X, V)} (ha : a ≠ 0)
    {s : Γ(F, V)} (hs : a • s = 0) : s = 0 := by
  obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 (mt (basicOpen_eq_bot_iff a).1 ha)
  have hη := genericPoint_mem hx
  have hV := X.basicOpen_le a hη
  refine h V hV s (((X.mem_basicOpen a _ hV).1 hη).smul_eq_zero.1 ?_)
  rw [← QCoh.germ_smul, hs, map_zero]

theorem IsTorsionFree.isZero [IsFiniteQC F] (h : IsTorsionFree F) (h0 : genRank F = 0) :
    IsZero F := by
  have := QCoh.notMem_support_iff.1 (genRank_eq_zero_iff.1 h0)
  refine QCoh.support_eq_empty_iff.1 (Set.eq_empty_of_forall_notMem fun x =>
    QCoh.notMem_support_iff.2 (subsingleton_of_forall_eq 0 fun t => ?_))
  obtain ⟨V, hV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  rw [h V (genericPoint_mem hV) s (Subsingleton.elim _ _), map_zero]

def satSub (i : G ⟶ F) : Sub F := Sub.ofGeneric (LinearMap.range (stalkLinear i (genericPoint X)))

def sat (i : G ⟶ F) : X.Modules := (satSub i).toMod

def satι (i : G ⟶ F) : sat i ⟶ F := (satSub i).incl

instance mono_satι (i : G ⟶ F) : Mono (satι i) := (satSub i).mono_incl

def toSat (i : G ⟶ F) : G ⟶ sat i :=
  (satSub i).lift i fun _ s h => ⟨_, QCoh.stalkLinear_germ i _ h s⟩

@[reassoc (attr := simp)] theorem toSat_ι (i : G ⟶ F) : toSat i ≫ satι i = i := rfl

instance mono_toSat (i : G ⟶ F) [Mono i] : Mono (toSat i) := mono_of_mono_fac (toSat_ι i)

instance isQuasicoherent_sat (i : G ⟶ F) [F.IsQuasicoherent] : (sat i).IsQuasicoherent :=
  Sub.isQuasicoherent_ofGeneric _

instance isFiniteQC_sat [IsLocallyNoetherian X] (i : G ⟶ F) [IsFiniteQC F] : IsFiniteQC (sat i) :=
  .of_mono (satι i)

theorem range_stalkLinear_satι (i : G ⟶ F) :
    LinearMap.range (stalkLinear (satι i) (genericPoint X)) =
      LinearMap.range (stalkLinear i (genericPoint X)) := Sub.range_stalkLinear_ofGeneric _

theorem genRank_sat (i : G ⟶ F) [Mono i] : genRank (sat i) = genRank G := by
  rw [genRank, genRank, ← LinearMap.finrank_range_of_inj (QCoh.stalkLinear_injective i _),
    ← LinearMap.finrank_range_of_inj (QCoh.stalkLinear_injective (satι i) _),
    range_stalkLinear_satι]

theorem mem_satSub_iff (i : G ⟶ F) [F.IsQuasicoherent] [G.IsQuasicoherent] (hU : IsAffineOpen U)
    (hη : genericPoint X ∈ U) {s : Γ(F, U)} :
    s ∈ (satSub i).sec U ↔ ∃ a : Γ(X, U), a ≠ 0 ∧ ∃ t, i.app U t = a • s := by
  have : Nonempty U := ⟨⟨_, hη⟩⟩
  constructor
  · intro h
    obtain ⟨t, ht⟩ := h hη
    obtain ⟨T, hT, hxT, t, rfl⟩ := Twist.exists_germ_eq_of_mem hη t
    rw [QCoh.stalkLinear_germ, ← germ_resM hT hxT] at ht
    obtain ⟨T', hxT', i₁, i₂, e⟩ := F.presheaf.germ_eq _ hxT hxT _ _ ht
    obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le (V := T') ⟨_, hxT'⟩ hη
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at hxf
    obtain ⟨n, u, hu⟩ := QCoh.exists_pow_smul_eq_res G hU f (X.basicOpen_le f) rfl
      (resM G (hf.trans i₁.le) t)
    have e' : i.app _ (resM G (hf.trans i₁.le) t) = resM F (X.basicOpen_le f) s := by
      have := congrArg (resM F hf) (show resM F i₁.le _ = resM F i₂.le _ from e)
      rwa [resM_resM, resM_resM, resM_resM, ← app_resM] at this
    obtain ⟨m, hm⟩ := QCoh.exists_pow_smul_eq_zero F hU f (X.basicOpen_le f) rfl
      (i.app U u - f ^ n • s) (by
        rw [map_sub, ← QCoh.app_res, ← hu, Scheme.Modules.Hom.app_smul, e',
          Scheme.Modules.map_smul, map_pow]
        exact sub_self _)
    refine ⟨f ^ (m + n), pow_ne_zero _ hf0, f ^ m • u, ?_⟩
    rw [Scheme.Modules.Hom.app_smul, pow_add, mul_smul, ← sub_eq_zero, ← smul_sub, hm]
  · rintro ⟨a, ha, t, ht⟩ h
    obtain ⟨x, hx⟩ := (Opens.ne_bot_iff_nonempty _).1 (mt (basicOpen_eq_bot_iff a).1 ha)
    refine (Submodule.smul_mem_iff_of_isUnit _
      ((X.mem_basicOpen a _ h).1 (genericPoint_mem hx))).1 ?_
    rw [← QCoh.germ_smul, ← ht]
    exact ⟨_, QCoh.stalkLinear_germ i _ h t⟩

def IsSaturated (i : G ⟶ F) : Prop := IsTorsionFree (cokernel i)

theorem germ_cokernel_π_eq_zero_iff (i : G ⟶ F) (h : genericPoint X ∈ V) (s : Γ(F, V)) :
    (cokernel i).presheaf.germ V _ h ((cokernel.π i).app V s) = 0 ↔ s ∈ (satSub i).sec V := by
  rw [← QCoh.stalkLinear_germ]
  exact ((QCoh.exact_iff_stalkLinear _).1 (ShortComplex.exact_cokernel i) (genericPoint X) _).trans
    ⟨fun H _ => H, fun H => H h⟩

theorem isSaturated_satι (i : G ⟶ F) : IsSaturated (satι i) := by
  refine isTorsionFree_of_forall_exists fun V hV s hs x hx => ?_
  obtain ⟨W, h, hxW, t, ht⟩ := exists_app_eq_of_epi (cokernel.π (satι i)) s hx
  refine ⟨W, h, hxW, ht ▸ (satSub i).cokernel_π_app_eq_zero_iff.2 fun hW => ?_⟩
  rw [← range_stalkLinear_satι]
  refine (germ_cokernel_π_eq_zero_iff (satι i) hW t).1 ?_ hW
  rw [ht, germ_resM, hs]

theorem IsSubbundle.isSaturated {i : G ⟶ F} (h : IsSubbundle i) : IsSaturated i :=
  have ⟨_, hs⟩ := h.isVB_cokernel
  hs.isTorsionFree

theorem isSaturated_iff_isIso_toSat (i : G ⟶ F) [Mono i] : IsSaturated i ↔ IsIso (toSat i) := by
  refine ⟨fun h => ?_, fun h => IsTorsionFree.of_mono (G := cokernel (toSat i ≫ satι i))
    (isSaturated_satι i) (cokernelEpiComp (toSat i) (satι i)).hom⟩
  have : Epi (toSat i) := QCoh.epi_of_locally_app_surjective _ fun V x hx =>
    ⟨V, hx, le_rfl, fun s => by
      obtain ⟨t, ht⟩ := (QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_cokernel i) V _).1
        (h V (genericPoint_mem hx) _ ((germ_cokernel_π_eq_zero_iff i _ _).2
          ((satSub i).incl_app_mem s)))
      exact ⟨t, (satSub i).incl_app_injective V ht⟩⟩
  exact isIso_of_mono_of_epi _

theorem isIso_satι_of_genRank_eq (i : G ⟶ F) [Mono i] [IsFiniteQC F] (h : genRank G = genRank F) :
    IsIso (satι i) := by
  have e : LinearMap.range (stalkLinear i (genericPoint X)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (K := X.functionField)
      ((LinearMap.finrank_range_of_inj (QCoh.stalkLinear_injective i _)).trans h)
  exact Twist.isIso_of_bijective _ fun V => ⟨(satSub i).incl_app_injective V, fun s =>
    ⟨(satSub i).mkSec s fun _ => e.ge trivial, rfl⟩⟩

variable (F) in

def torsionSub : Sub F := Sub.ofGeneric ⊥

end Integral

section Curves

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]

structure IsProperCurve : Prop where

  isIntegral : IsIntegral C

  dim_eq : topologicalKrullDim C = 1

  isProper : IsProper (strHom k C)

structure IsProjCurve : Prop where

  isIntegral : IsIntegral C

  dim_eq : topologicalKrullDim C = 1

  isProjOver : IsProjOver (strHom k C)

structure IsSmoothProjCurve : Prop extends IsProjCurve k C where

  smooth : Smooth (strHom k C)

variable {k C}

theorem IsProjCurve.isProperCurve (h : IsProjCurve k C) : IsProperCurve k C :=
  ⟨h.isIntegral, h.dim_eq, (isProper_and_exists_isAmpleLB_of_isProjOver h.isProjOver).1⟩

theorem IsProperCurve.isNoetherian (h : IsProperCurve k C) : AlgebraicGeometry.IsNoetherian C :=
  have := h.isProper
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (strHom k C)
  isNoetherian_of_locallyOfFiniteType_field (strHom k C)

theorem IsProjCurve.isNoetherian (h : IsProjCurve k C) : AlgebraicGeometry.IsNoetherian C :=
  h.isProperCurve.isNoetherian

theorem IsProjCurve.finiteCoh (h : IsProjCurve k C) (F : C.Modules) [IsFiniteQC F] :
    FiniteCoh k F := finiteCoh_of_isProjOver (algebraMap_eq_strHom k C) F h.isProjOver

omit [Field k] [Algebra k Γ(C, ⊤)] in

theorem suppDim_le_zero [IsIntegral C] (hd : topologicalKrullDim C = 1) {F : C.Modules} [IsFiniteQC F]
    (h : genRank F = 0) : QCoh.suppDim F ≤ 0 := by
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint C, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set C) = 1 := by
    rw [← hd, ← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact ENat.WithBot.add_le_add_one_right_iff.1 (this.trans_eq (zero_add 1).symm)

end Curves

section Degree

variable (k : Type) [Field k] [Algebra k Γ(X, ⊤)]

def degOfRank (F : X.Modules) (r : ℕ) : ℤ := chi k F - r * chi k (structureModule X)

theorem degOfRank_congr (φ : F ≅ G) : degOfRank k F r = degOfRank k G r := by
  rw [degOfRank, degOfRank, chi_congr k φ]

variable {k} in

theorem degOfRank_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : FiniteCoh k S.X₁) (h₃ : FiniteCoh k S.X₃) :
    degOfRank k S.X₂ (r + s) = degOfRank k S.X₁ r + degOfRank k S.X₃ s := by
  simp only [degOfRank, chi_shortExact hS h₁ h₃]
  push_cast
  ring

variable [IsIntegral X]

def deg (F : X.Modules) : ℤ := degOfRank k F (genRank F)

theorem deg_def : deg k F = chi k F - genRank F * chi k (structureModule X) := rfl

theorem IsVB.deg_eq (h : IsVB F r) : deg k F = degOfRank k F r := by rw [deg, h.genRank_eq]

theorem deg_congr (φ : F ≅ G) : deg k F = deg k G := by
  rw [deg, deg, genRank_congr φ, degOfRank_congr k φ]

theorem deg_eq_zero_of_isZero (h : IsZero F) : deg k F = 0 := by
  rw [deg_def, genRank_eq_zero_of_isZero h, chi_eq_zero_of_isZero k h]; simp

@[simp] theorem deg_structureModule : deg k (structureModule X) = 0 := by
  rw [deg_def, (isVB_structureModule X).genRank_eq]; simp

variable {k}

theorem deg_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) [IsFiniteQC S.X₂]
    (h₁ : FiniteCoh k S.X₁) (h₃ : FiniteCoh k S.X₃) :
    deg k S.X₂ = deg k S.X₁ + deg k S.X₃ := by
  rw [deg, genRank_shortExact hS, degOfRank_shortExact hS h₁ h₃, deg, deg]

theorem deg_freeModule (h : FiniteCoh k (structureModule X)) (ι : Type) [Fintype ι] :
    deg k (freeModule X ι) = 0 := by
  have := Abelian.hasFiniteBiproducts (C := X.Modules)
  have e : freeModule X ι ≅ ∏ᶜ fun _ : ι => structureModule X :=
    (biproduct.isoCoproduct fun _ : ι => structureModule X).symm ≪≫ biproduct.isoProduct _
  rw [deg_def, (isVB_freeModule X ι).genRank_eq, chi_congr k e, chi_pi fun _ => h]
  simp

theorem IsFrame.deg_eq_zero (h : FiniteCoh k (structureModule X)) {ι : Type} [Fintype ι]
    {e : ι → Γ(F, ⊤)} (he : IsFrame e) : deg k F = 0 :=
  (deg_congr k (he.iso (isFrame_freeFrame X ι))).trans (deg_freeModule h ι)

theorem IsProperCurve.deg_eq_hdim (hC : IsProperCurve k X) [IsFiniteQC F] (h : genRank F = 0) :
    deg k F = hdim k F 0 := by
  have := hC.isNoetherian
  rw [deg_def, h, chi_eq_hdim_zero_of_suppDim_le_zero k (suppDim_le_zero hC.dim_eq h)]
  simp

namespace IsProjCurve

variable (hC : IsProjCurve k X)
include hC

theorem deg_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) [IsFiniteQC S.X₁]
    [IsFiniteQC S.X₂] [IsFiniteQC S.X₃] : deg k S.X₂ = deg k S.X₁ + deg k S.X₃ :=
  VB.deg_shortExact hS (hC.finiteCoh _) (hC.finiteCoh _)

theorem deg_cokernel (i : G ⟶ F) [Mono i] [IsFiniteQC G] [IsFiniteQC F] :
    deg k (cokernel i) = deg k F - deg k G :=
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  eq_sub_of_add_eq' (VB.deg_shortExact hS (hC.finiteCoh G) (hC.finiteCoh (cokernel i))).symm

theorem deg_le_of_genRank_eq (i : G ⟶ F) [Mono i] [IsFiniteQC G] [IsFiniteQC F]
    (h : genRank G = genRank F) : deg k G ≤ deg k F := by
  have h0 := genRank_cokernel i
  have h1 := hC.isProperCurve.deg_eq_hdim (F := cokernel i) (by omega)
  rw [hC.deg_cokernel] at h1
  omega

theorem deg_le_deg_sat (i : G ⟶ F) [Mono i] [IsFiniteQC G] [IsFiniteQC F] :
    deg k G ≤ deg k (sat i) :=
  have := hC.isNoetherian
  hC.deg_le_of_genRank_eq (toSat i) (genRank_sat i).symm

theorem deg_eq_sum_eigen {O ι : Type} [CommRing O] [Fintype ι] {σ : ι → (O →+* k)}
    (hσ : IsSplitBy σ) (ρ : O →+* End F) [IsFiniteQC F] :
    deg k F = ∑ j, deg k (eigen ρ (scal X (σ j))) ∧
      genRank F = ∑ j, genRank (eigen ρ (scal X (σ j))) := by
  classical
  have := Abelian.hasFiniteBiproducts (C := X.Modules)
  have := hσ.isFiniteQC_eigen ρ
  have hr : genRank F = ∑ j, genRank (eigen ρ (scal X (σ j))) := by
    have hl : ∀ {A B : X.Modules} (φ : ι → (A ⟶ B)), stalkLinear (∑ j, φ j) (genericPoint X) =
        ∑ j, stalkLinear (φ j) (genericPoint X) := fun φ =>
      map_sum (AddMonoidHom.mk' (fun φ => stalkLinear φ (genericPoint X))
        fun _ _ => QCoh.stalkLinear_add _ _ _) _ _
    let e : genStalk F ≃ₗ[X.functionField] ∀ j, genStalk (eigen ρ (scal X (σ j))) :=
      LinearEquiv.ofLinearMap (LinearMap.pi fun j => stalkLinear (hσ.proj ρ j) _)
        (∑ j, stalkLinear (eigenι _ _) _ ∘ₗ LinearMap.proj j)
        (by
          refine LinearMap.pi_ext' fun i => LinearMap.ext fun t => funext fun j => ?_
          simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, map_sum,
            LinearMap.proj_apply, LinearMap.id_apply, LinearMap.single_apply]
          rw [Finset.sum_eq_single j (fun i' _ h' => ?_) (by simp), ← LinearMap.comp_apply,
            ← QCoh.stalkLinear_comp, hσ.ι_proj, QCoh.stalkLinear_id, LinearMap.id_apply]
          rw [← LinearMap.comp_apply, ← QCoh.stalkLinear_comp, hσ.ι_proj_ne ρ h',
            QCoh.stalkLinear_zero, LinearMap.zero_apply])
        (by
          rw [← QCoh.stalkLinear_id, ← hσ.sum_proj_ι ρ, hl]
          refine LinearMap.ext fun t => ?_
          simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply,
            LinearMap.proj_apply, QCoh.stalkLinear_comp])
    rw [genRank, e.finrank_eq, Module.finrank_pi_fintype]
    rfl
  refine ⟨?_, hr⟩
  simp only [deg_def]
  rw [chi_congr k (hσ.decompose ρ ≪≫ biproduct.isoProduct _), chi_pi fun j => hC.finiteCoh _, hr,
    Finset.sum_sub_distrib, ← Finset.sum_mul, Nat.cast_sum]

end IsProjCurve

variable (k) in

def degLB (L : LB X) : ℤ := deg k (toMod L)

variable {L M N : LB X}

theorem degLB_eq (hL : L.IsLB) : degLB k L = chi k (toMod L) - chi k (structureModule X) := by
  rw [degLB, deg_def, (isVB_toMod hL).genRank_eq]; simp

theorem degLB_congr (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L M) : degLB k L = degLB k M :=
  (LB.nonempty_iso_of_lbIso hL hM h).elim (deg_congr k)

theorem IsVB.degLB_det_one (h : IsVB F 1) : degLB k (det F 1) = deg k F :=
  (deg_congr k h.isoDet).symm

theorem IsProjCurve.degLB_eq_interNum (hC : IsProjCurve k X) (hL : L.IsLB) :
    degLB k L = interNum k (structureModule X) ![L] := by
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hC.isProjOver
  have hd := CechPic.isLB_dual hL
  have e₁ := interNum_one_of_cls_eq_add (k := k) hA hC.dim_eq (LB.isLB_triv X) hd hL
    (CechPic.cls_dual_add hL).symm
  have e₂ : interNum k (structureModule X) ![LB.triv X] = 0 :=
    interNum_eq_zero_of_cls_eq_zero k _ (isLB_vecOne (LB.isLB_triv X)) 0 rfl
  have e₃ : interNum k (structureModule X) ![CechPic.dual L] =
      chi k (structureModule X) - chi k (twist (structureModule X) L) :=
    (interNum_cons_of_cls_eq_neg k _ (P := ![]) hd isEmptyElim hL
      (by rw [CechPic.cls_dual hL, neg_neg])).trans
      (congrArg₂ (· - ·) (interNum_of_isEmpty k _ _) (interNum_of_isEmpty k _ _))
  rw [degLB_eq hL, ← chi_congr k (Twist.unitTwistIso L)]
  change chi k (twist (structureModule X) L) - _ = _
  omega

theorem IsProjCurve.degLB_of_cls_eq_add (hC : IsProjCurve k X) (hN : N.IsLB) (hL : L.IsLB)
    (hM : M.IsLB) (e : CechPic.cls N hN = CechPic.cls L hL + CechPic.cls M hM) :
    degLB k N = degLB k L + degLB k M := by
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hC.isProjOver
  rw [hC.degLB_eq_interNum hN, hC.degLB_eq_interNum hL, hC.degLB_eq_interNum hM]
  exact interNum_one_of_cls_eq_add hA hC.dim_eq hN hL hM e

def IsProjCurve.degPic (hC : IsProjCurve k X) : CechPic.Pic X →+ ℤ :=
  AddMonoidHom.mk' (Quotient.lift (fun L => degLB k L.1) fun L M h => degLB_congr L.2 M.2 h)
    fun a b => by
      obtain ⟨L, hL, rfl⟩ := CechPic.cls_surj a
      obtain ⟨M, hM, rfl⟩ := CechPic.cls_surj b
      exact hC.degLB_of_cls_eq_add (CechPic.isLB_tens hL hM) hL hM rfl

@[simp] theorem IsProjCurve.degPic_cls (hC : IsProjCurve k X) (hL : L.IsLB) :
    hC.degPic (CechPic.cls L hL) = degLB k L := rfl

omit [IsIntegral X] in

theorem nonempty_pullback_toMod_iso (hL : L.IsLB) (f : Y ⟶ X) :
    Nonempty ((Scheme.Modules.pullback f).obj (toMod L) ≅ toMod (L.pull f)) := by
  have h := isVB_toMod hL
  have h₁ := (h.pullback f).isLB_det
  have h₂ := Semi.LB.isLB_pull hL f
  have h₃ := Semi.LB.isLB_pull h.isLB_det f
  have e : CechPic.cls _ h₁ = CechPic.cls _ h₂ := by
    rw [← (CechPic.cls_eq_iff h₃ h₁).2 (h.lbIso_det_pullback f), CechPic.cls_pull h.isLB_det,
      CechPic.cls_pull hL, (CechPic.cls_eq_iff hL h.isLB_det).2 (lbIso_det_toMod hL)]
  obtain ⟨φ⟩ := LB.nonempty_iso_of_lbIso h₁ h₂ ((CechPic.cls_eq_iff _ _).1 e)
  exact ⟨(h.pullback f).isoDet ≪≫ φ⟩

theorem IsProjCurve.deg_frobPull_of_rank_one (hC : IsProjCurve k X) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) (h : IsVB F 1) : deg k ((frobPull p hp).obj F) = p * deg k F := by
  obtain ⟨φ⟩ := nonempty_pullback_toMod_iso h.isLB_det (frob X p hp)
  rw [deg_congr k ((frobPull p hp).mapIso h.isoDet ≪≫ φ), ← h.degLB_det_one,
    ← hC.degPic_cls h.isLB_det, ← nsmul_eq_mul, ← map_nsmul,
    ← cls_pull_frob p hp h.isLB_det (Semi.LB.isLB_pull h.isLB_det _)]
  rfl

theorem IsProjCurve.deg_dual_of_rank_one (hC : IsProjCurve k X) (h : IsVB F 1) :
    deg k (dual F) = -deg k F := by
  rw [← h.degLB_det_one, ← h.dual.degLB_det_one, ← hC.degPic_cls h.isLB_det, ← map_neg,
    ← CechPic.cls_dual h.isLB_det (CechPic.isLB_dual h.isLB_det), hC.degPic_cls]
  exact (degLB_congr (CechPic.isLB_dual h.isLB_det) h.dual.isLB_det h.lbIso_det_dual).symm

variable (k) in

def subDegs (F : X.Modules) : Set ℤ :=
  {d | ∃ (G : X.Modules) (i : G ⟶ F), IsCohSub i ∧ deg k G = d}

variable (k) in

def IsMaxSubDeg (F : X.Modules) (P : ℤ) : Prop := IsGreatest (subDegs k F) P

theorem IsCohSub.deg_mem {i : G ⟶ F} (h : IsCohSub i) : deg k G ∈ subDegs k F := ⟨G, i, h, rfl⟩

variable (k) in
open ZeroObject in

theorem zero_mem_subDegs (F : X.Modules) : 0 ∈ subDegs k F :=
  ⟨0, 0, isCohSub_of_isZero (isZero_zero _) _, deg_eq_zero_of_isZero k (isZero_zero _)⟩

theorem subDegs_mono (j : F ⟶ H) [Mono j] : subDegs k F ⊆ subDegs k H :=
  fun _ ⟨G, i, h, e⟩ => ⟨G, i ≫ j, h.comp j, e⟩

theorem subDegs_congr (φ : F ≅ H) : subDegs k F = subDegs k H :=
  (subDegs_mono φ.hom).antisymm (subDegs_mono φ.inv)

namespace IsMaxSubDeg

variable {P Q : ℤ}

theorem exists_isCohSub (h : IsMaxSubDeg k F P) :
    ∃ (G : X.Modules) (i : G ⟶ F), IsCohSub i ∧ deg k G = P := h.1

theorem deg_le (h : IsMaxSubDeg k F P) (i : G ⟶ F) [Mono i] [hG : IsFiniteQC G] : deg k G ≤ P :=
  h.2 (IsCohSub.deg_mem (i := i) ⟨inferInstance, hG⟩)

theorem nonneg (h : IsMaxSubDeg k F P) : 0 ≤ P := h.2 (zero_mem_subDegs k F)

theorem unique (h : IsMaxSubDeg k F P) (h' : IsMaxSubDeg k F Q) : P = Q := IsGreatest.unique h h'

theorem of_iso (h : IsMaxSubDeg k F P) (φ : F ≅ H) : IsMaxSubDeg k H P := by
  rwa [IsMaxSubDeg, ← subDegs_congr φ]

end IsMaxSubDeg

theorem exists_isMaxSubDeg_iff : (∃ P, IsMaxSubDeg k F P) ↔ BddAbove (subDegs k F) :=
  ⟨fun ⟨_, h⟩ => h.bddAbove, fun ⟨b, hb⟩ =>
    Int.exists_greatest_of_bdd ⟨b, fun _ h => hb h⟩ ⟨0, zero_mem_subDegs k F⟩⟩

theorem IsProjCurve.isMaxSubDeg_of_rank_one (hC : IsProjCurve k X) (h : IsVB F 1) :
    IsMaxSubDeg k F (max (deg k F) 0) := by
  have := h.isFiniteQC
  constructor
  · rcases max_choice (deg k F) 0 with e | e <;> rw [e]
    exacts [isCohSub_id.deg_mem, zero_mem_subDegs k F]
  · rintro _ ⟨G, i, hi, rfl⟩
    have := hi.mono
    have := hi.isFiniteQC
    have hr := genRank_le_of_mono i
    rw [h.genRank_eq] at hr
    by_cases h0 : genRank G = 0
    · rw [deg_eq_zero_of_isZero k ((h.isTorsionFree.of_mono i).isZero h0)]
      exact le_max_right _ _
    · exact (hC.deg_le_of_genRank_eq i (by rw [h.genRank_eq]; omega)).trans (le_max_left _ _)

end Degree

section Line

open ProjSpace ProjCoh

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type) [Field k]

theorem isSmoothProjCurve_line : IsSmoothProjCurve k (PSpace k 1) := by
  have e := strHom_eq (algebraMap_top_eq k 1)
  refine ⟨⟨inferInstance, topologicalKrullDim_eq k 1, e ▸ isProjOver_str k 1⟩, e ▸ ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{0}) (Q := @RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0}) (chartCover k 1)
    fun (i : Fin (1 + 1)) => ?_
  change Smooth (chartι k 1 i ≫ _)
  rw [chartι_str]
  refine (HasRingHomProperty.Spec_iff (P := @Smooth)).2 ?_
  exact RingHom.smooth_algebraMap.2
    (⟨inferInstance, inferInstance⟩ : Algebra.Smooth k (MvPolynomial {j // j ≠ i} k))

theorem isVB_sheafO (n : ℤ) : IsVB (sheafO k 1 n) 1 :=
  (isVB_structureModule _).twist (On_isLB k 1 n)

theorem deg_sheafO (n : ℤ) : deg k (sheafO k 1 n) = n := by
  rw [deg_def, (isVB_sheafO k n).genRank_eq, chi_sheafO,
    chi_congr k (Twist.twistZZeroIso (structureModule _) (O1_isLB k 1)), chi_sheafO]
  simp

theorem degLB_On (n : ℤ) : degLB k (On k 1 n) = n :=
  (deg_congr k (sheafOIso k 1 n)).symm.trans (deg_sheafO k n)

example : deg k (dual (sheafO k 1 1)) = -1 := by
  rw [(isSmoothProjCurve_line k).toIsProjCurve.deg_dual_of_rank_one (isVB_sheafO k 1), deg_sheafO]

example [Fact (Nat.Prime 3)] [CharP k 3] :
    deg k ((frobPull 3 (natCast_eq_zero (PSpace k 1) 3 k)).obj (sheafO k 1 2)) = 6 := by
  rw [(isSmoothProjCurve_line k).toIsProjCurve.deg_frobPull_of_rank_one 3 _ (isVB_sheafO k 2),
    deg_sheafO]
  rfl

end Line

section Prod

variable (F G) in

def prodAct : ℤ × ℤ →+* End (F ⊞ G) where
  toFun a := biprod.map (a.1 • 𝟙 F) (a.2 • 𝟙 G)
  map_one' := by
    change _ = 𝟙 _
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  map_mul' a b := by
    change _ = biprod.map _ _ ≫ biprod.map _ _
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [smul_smul, mul_comm]
  map_zero' := by
    change _ = (0 : F ⊞ G ⟶ F ⊞ G)
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp
  map_add' a b := by
    change _ = (biprod.map _ _ + biprod.map _ _ : F ⊞ G ⟶ F ⊞ G)
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [add_smul]

end Prod

end GlobalTheory.VB
