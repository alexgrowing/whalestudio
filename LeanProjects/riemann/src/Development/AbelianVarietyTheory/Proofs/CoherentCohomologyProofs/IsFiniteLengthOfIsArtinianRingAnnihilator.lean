import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthRestrictScalarsEqSumInertiaDegOfSubset
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh

universe u v

namespace GlobalTheory

section Topology

variable {T : Type*} [TopologicalSpace T] [QuasiSober T] [NoetherianSpace T]

theorem exists_finite_specializes_of_isClosed {Z : Set T} (hZ : IsClosed Z) :
    ∃ S : Set T, S.Finite ∧ S ⊆ Z ∧ ∀ x ∈ Z, ∃ y ∈ S, y ⤳ x := by
  obtain ⟨C, hC, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  have := hC.to_subtype
  refine ⟨Set.range fun c : C => (hi c.1 c.2).genericPoint, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨c.1, c.2, ((hi c.1 c.2).isGenericPoint_genericPoint (hc c.1 c.2)).mem⟩
  · rintro x ⟨c, hc', hx⟩
    exact ⟨_, ⟨⟨c, hc'⟩, rfl⟩, ((hi c hc').isGenericPoint_genericPoint (hc c hc')).specializes hx⟩

theorem exists_cover_of_topologicalKrullDim_lt (P : Opens T → Prop)
    (hP : ∀ S : Set T, S.Finite → ∃ A, P A ∧ S ⊆ A) (n : ℕ) {Z : Set T} (hZ : IsClosed Z)
    (hn : topologicalKrullDim Z < n) :
    ∃ U : Fin n → Opens T, (∀ i, P (U i)) ∧ ∀ x ∈ Z, ∃ i, x ∈ U i := by
  induction n generalizing Z with
  | zero =>
    have h : IsEmpty Z := topologicalKrullDim_eq_bot_iff.1 (WithBot.lt_coe_bot.1 hn)
    exact ⟨Fin.elim0, fun i => i.elim0, fun x hx => h.elim ⟨x, hx⟩⟩
  | succ n ih =>
    obtain ⟨S, hS, hSZ, hgen⟩ := exists_finite_specializes_of_isClosed hZ
    obtain ⟨A, hA, hSA⟩ := hP S hS
    have hZ' : IsClosed (Z \ A) := hZ.sdiff A.2
    have h₁ : topologicalKrullDim (Z \ A :) + 1 ≤ topologicalKrullDim Z :=
      topologicalKrullDim_add_one_le hZ' hZ fun x hx =>
        have ⟨y, hy, hyx⟩ := hgen x hx.1
        ⟨y, hSZ hy, fun h => h.2 (hSA hy), hyx⟩
    have h₂ : topologicalKrullDim (Z \ A :) < n := by
      by_contra! h
      refine (h₁.trans_lt hn).not_ge ?_
      rw [Nat.cast_succ]
      exact add_le_add_left h 1
    obtain ⟨U, hU, hc⟩ := ih hZ' h₂
    refine ⟨Fin.cons A U, fun i => Fin.cases hA hU i, fun x hx => ?_⟩
    by_cases hxA : x ∈ A
    · exact ⟨0, hxA⟩
    · obtain ⟨i, hi⟩ := hc x ⟨hx, hxA⟩
      exact ⟨i.succ, hi⟩

end Topology

section Vanishing

variable {X : Scheme.{u}} {F : X.Modules}

theorem QCoh.subsingleton_sections_of_notMem_support {W : X.Opens}
    (h : ∀ x ∈ W, x ∉ support F) : Subsingleton Γ(F, W) :=
  subsingleton_of_forall_eq 0 fun s => section_eq_zero_of_germ s fun x hx =>
    (notMem_support_iff.1 (h x hx)).elim _ _

theorem cohOn.subsingleton_of_notMem_support {W : X.Opens} (h : ∀ x ∈ W, x ∉ support F) (n : ℕ) :
    Subsingleton (cohOn F W n) := by
  have hz : IsZero (F.restrict W.ι) := by
    rw [← support_eq_empty_iff, support_restrict]
    exact Set.eq_empty_iff_forall_notMem.2 fun y hy => h _ y.2 hy
  have := cohOn.subsingleton_of_isZero hz ⊤ n
  exact (cohOn.restrictEquiv ℤ (fun r => (map_intCast _ r).trans (eq_intCast _ r).symm) F
    W.ι_image_top n).toEquiv.subsingleton

theorem coh.subsingleton_of_support_subset {ι : Type} [Fintype ι] {U : ι → X.Opens}
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) [F.IsQuasicoherent]
    {Z : Set X} (hZ : IsClosed Z) (hF : support F ⊆ Z) (hc : ∀ x ∈ Z, ∃ i, x ∈ U i) {n : ℕ}
    (hn : Fintype.card ι ≤ n) : Subsingleton (coh F n) := by
  classical
  let W : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  let U' : Option ι → X.Opens := fun o => o.elim W U
  have hW (s : Finset (Option ι)) (hs : none ∈ s) : ∀ x ∈ cechOpen ⊤ U' s, x ∉ support F :=
    fun x hx h => (show cechOpen ⊤ U' s ≤ W from inf_le_right.trans (iInf₂_le none hs)) hx (hF h)
  have hcov : ⊤ ≤ ⨆ o, U' o := fun x _ => Opens.mem_iSup.2 <| by
    by_cases hx : x ∈ Z
    · obtain ⟨i, hi⟩ := hc x hx
      exact ⟨some i, hi⟩
    · exact ⟨none, hx⟩
  have ha : CechAcyclicMod ⊤ U' F := fun s hs q => by
    by_cases h : none ∈ s
    · exact cohOn.subsingleton_of_notMem_support (hW s h) _
    · refine cohOn.subsingleton_of_isAffineOpen F ?_ q.succ_pos
      obtain ⟨t, rfl⟩ : ∃ t : Finset ι, t.map Function.Embedding.some = s :=
        ⟨s.eraseNone, by rw [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem h]⟩
      rw [cechOpen_of_nonempty (fun _ => le_top) hs]
      rw [Finset.map_eq_image, Finset.iInf_finset_image]
      exact hU t (Finset.map_nonempty.1 hs)
  letI : LinearOrder (Option ι) := LinearOrder.lift' _ (Fintype.equivFin _).injective
  have h₀ : IsZero ((cech ℤ F ⊤ U').X n) := by
    rw [cech_X, ModuleCat.isZero_iff_subsingleton]
    refine @Pi.instSubsingleton _ _ fun s => ?_
    refine (sectionsOn.toΓ F _).toEquiv.subsingleton_congr.2
      (subsingleton_sections_of_notMem_support (hW s.1 ?_))
    by_contra h
    have := Finset.card_le_univ s.1.eraseNone
    rw [Finset.card_eraseNone_of_not_mem h, s.2] at this
    omega
  have h₁ : IsZero (cechH ℤ F ⊤ U' n) :=
    ((cech ℤ F ⊤ U').exactAt_iff_isZero_homology n).1 (ShortComplex.exact_of_isZero_X₂ _ h₀)
  have := ModuleCat.isZero_iff_subsingleton.1 h₁
  exact (cechHEquivCohOn ℤ hcov ha n).symm.toEquiv.subsingleton

end Vanishing

section Ample

variable {X : Scheme.{0}} {L : LB X}

theorem IsAmpleLB.exists_cover_of_dim_lt [NoetherianSpace X] (h : IsAmpleLB L) {Z : Set X}
    (hZ : IsClosed Z) {n : ℕ} (hn : topologicalKrullDim Z < n) :
    ∃ N, 1 ≤ N ∧ ∃ s : Fin n → (lbPow L N).Sec, (∀ i, IsAffineOpen (nonzeroLocus (s i))) ∧
      ∀ x ∈ Z, ∃ i, x ∈ nonzeroLocus (s i) := by
  obtain ⟨U, hU, hc⟩ := exists_cover_of_topologicalKrullDim_lt
    (fun A : X.Opens => ∃ m, 1 ≤ m ∧ ∃ s : (lbPow L m).Sec, nonzeroLocus s = A ∧ IsAffineOpen A)
    (fun S hS => by
      obtain ⟨m, hm, s, h₁, -, h₂⟩ := h.exists_affine_finite_subset hS (U := ⊤) (Set.subset_univ _)
      exact ⟨_, ⟨m, hm, s, rfl, h₂⟩, h₁⟩) n hZ hn
  choose m hm s hs ha using hU
  obtain ⟨N, hN, t, ht⟩ := exists_common_pow m hm s
  refine ⟨N, hN, t, fun i => ?_, fun x hx => ?_⟩ <;> simp only [ht, hs]
  exacts [ha i, hc x hx]

theorem isAffineOpen_finset_biInf_nonzeroLocus {ι : Type*} (hL : L.IsLB) {s : ι → L.Sec}
    (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i))) (t : Finset ι) (ht : t.Nonempty) :
    IsAffineOpen (⨅ i ∈ t, nonzeroLocus (s i)) := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton i => simpa using ha i
  | cons i t hi _ ih =>
    classical
    rw [Finset.cons_eq_insert, Finset.iInf_insert]
    exact isAffineOpen_nonzeroLocus_inf hL _ ih

theorem IsAmpleLB.subsingleton_coh_of_support_subset [NoetherianSpace X] (h : IsAmpleLB L)
    (F : X.Modules) [F.IsQuasicoherent] {Z : Set X} (hZ : IsClosed Z) (hF : support F ⊆ Z) {n : ℕ}
    (hn : topologicalKrullDim Z < n) : Subsingleton (coh F n) := by
  obtain ⟨N, -, s, ha, hc⟩ := h.exists_cover_of_dim_lt hZ hn
  exact coh.subsingleton_of_support_subset
    (isAffineOpen_finset_biInf_nonzeroLocus (isLB_lbPow h.isLB N) ha) hZ hF hc (Fintype.card_fin n).le

theorem IsAmpleLB.noetherianSpace [IsLocallyNoetherian X] (h : IsAmpleLB L) : NoetherianSpace X :=
  have := h.compactSpace
  have : AlgebraicGeometry.IsNoetherian X := {}
  inferInstance

theorem IsAmpleLB.subsingleton_coh_of_dim_lt [IsLocallyNoetherian X] (h : IsAmpleLB L)
    (F : X.Modules) [F.IsQuasicoherent] {n : ℕ} (hn : topologicalKrullDim X < n) :
    Subsingleton (coh F n) :=
  have := h.noetherianSpace
  h.subsingleton_coh_of_support_subset F isClosed_univ (Set.subset_univ _)
    ((topologicalKrullDim_subspace_le X _).trans_lt hn)

theorem IsAmpleLB.subsingleton_coh_of_suppDim_lt [IsLocallyNoetherian X] (h : IsAmpleLB L)
    (F : X.Modules) [IsFiniteQC F] {n : ℕ} (hn : suppDim F < n) : Subsingleton (coh F n) :=
  have := h.noetherianSpace
  h.subsingleton_coh_of_support_subset F (isClosed_support F) subset_rfl hn

theorem isNoetherian_of_isProjOver {R : Type} [CommRing R] [IsNoetherianRing R] {f : X ⟶ Sp R}
    (hf : IsProjOver f) : AlgebraicGeometry.IsNoetherian X :=
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  {}

theorem subsingleton_coh_of_isProjOver {R : Type} [CommRing R] [IsNoetherianRing R] {f : X ⟶ Sp R}
    (hf : IsProjOver f) (F : X.Modules) [IsFiniteQC F] {n : ℕ} (hn : suppDim F < n) :
    Subsingleton (coh F n) :=
  have := isNoetherian_of_isProjOver hf
  have ⟨_, h⟩ := exists_isAmpleLB_of_isProjOver hf
  h.subsingleton_coh_of_suppDim_lt F hn

end Ample

section Annihilator

theorem map_annihilator_of_isLocalizedModule {A B M N : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (T : Submonoid A) [IsLocalization T B] [AddCommGroup M] [Module A M]
    [Module.Finite A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (f : M →ₗ[A] N) [IsLocalizedModule T f] :
    (Module.annihilator A M).map (algebraMap A B) = Module.annihilator B N := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun a ha => Module.mem_annihilator.2 fun n => ?_)
    fun b hb => ?_
  · obtain ⟨⟨m, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective T f n
    rw [algebraMap_smul, Function.uncurry_apply_pair, ← IsLocalizedModule.mk'_smul,
      Module.mem_annihilator.1 ha, IsLocalizedModule.mk'_zero]
  · obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective T b
    obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := A) (M := M)
    have h (i : Fin n) : ∃ u : T, u • a • g i = 0 := (IsLocalizedModule.eq_zero_iff T f).1 <| by
      rw [map_smul, ← algebraMap_smul B, ← IsLocalization.mk'_spec' B a t, mul_smul,
        Module.mem_annihilator.1 hb, smul_zero]
    choose u hu using h
    refine (IsLocalization.mk'_mem_map_algebraMap_iff T B _ _ _).2 ⟨_, (∏ i, u i).2, ?_⟩
    rw [← Submodule.annihilator_top, ← hg, Submodule.mem_annihilator_span]
    rintro ⟨_, i, rfl⟩
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem u (Finset.mem_univ i)
    rw [hc, mul_comm (u i), Submonoid.coe_mul, mul_smul, mul_smul]
    exact (congrArg _ (hu i)).trans (smul_zero _)

theorem isFiniteLength_of_isArtinianRing_annihilator {A M : Type*} [CommRing A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [IsArtinianRing (A ⧸ Module.annihilator A M)] : IsFiniteLength A M := by
  have h : Module.IsTorsionBySet A M (Module.annihilator A M) := fun m a =>
    Module.mem_annihilator.1 a.2 m
  letI := h.module
  haveI : Module.Finite (A ⧸ Module.annihilator A M) M := .of_restrictScalars_finite A _ _
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance,
    isArtinian_of_surjective_algebraMap (R := A ⧸ Module.annihilator A M)
      Ideal.Quotient.mk_surjective⟩

theorem length_eq_mul_length_residueField (R : Type*) {S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing S] [AddCommGroup M] [Module S M] (h : IsFiniteLength S M)
    [iR : Module R M] [iT : IsScalarTower R S M] :
    Module.length R M = Module.length S M * Module.length R (IsLocalRing.ResidueField S) := by
  revert iR iT
  induction h with
  | of_subsingleton => intros; simp
  | @of_simple_quotient M _ _ N hs _ ih =>
    intro iR iT
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    obtain rfl := IsLocalRing.eq_maximalIdeal hm
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R)
      N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
      Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), Module.length_eq_one S (M ⧸ N), add_mul, one_mul, ih,
      (e.restrictScalars R).length_eq]
    rfl

section General

variable {X : Scheme.{u}} (F : X.Modules) [IsFiniteQC F]

def QCoh.annihilatorSheaf : X.IdealSheafData where
  ideal U := Module.annihilator Γ(X, U) Γ(F, U)
  map_ideal_basicOpen U f :=
    have := U.2.isLocalization_basicOpen f
    have := isLocalizedModule_resBasicOpen F U.2 f
    map_annihilator_of_isLocalizedModule (B := Γ(X, X.basicOpen f)) (N := Γ(F, X.basicOpen f))
      (.powers f) (resBasicOpen F f)

@[simp] theorem QCoh.annihilatorSheaf_ideal (U : X.affineOpens) :
    (annihilatorSheaf F).ideal U = Module.annihilator Γ(X, U) Γ(F, U) := rfl

theorem QCoh.coe_support_annihilatorSheaf :
    ((annihilatorSheaf F).support : Set X) = support F := by
  ext x
  obtain ⟨U, hU, hx⟩ := exists_affine_mem x
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hx]
  exact ⟨fun h => ((support_inter_eq_zeroLocus F hU).ge ⟨h, hx⟩).1,
    fun h => ((support_inter_eq_zeroLocus F hU).le ⟨h, hx⟩).1⟩

theorem QCoh.range_annihilatorSheaf_subschemeι :
    Set.range (annihilatorSheaf F).subschemeι = support F :=
  (annihilatorSheaf F).range_subschemeι.trans (coe_support_annihilatorSheaf F)

theorem QCoh.topologicalKrullDim_annihilatorSheaf_subscheme :
    topologicalKrullDim (annihilatorSheaf F).subscheme = suppDim F := by
  rw [suppDim, ← range_annihilatorSheaf_subschemeι]
  exact (annihilatorSheaf F).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph
    |>.topologicalKrullDim_eq

end General

variable {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F]

instance QCoh.isIso_unit_annihilatorSheaf :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (annihilatorSheaf F).subschemeι).unit.app F) := by
  refine (isIso_iff_forall_affine (M := F) (N := (Scheme.Modules.pushforward _).obj
    ((Scheme.Modules.pullback (annihilatorSheaf F).subschemeι).obj F)) _).2 fun U hU => ?_
  obtain ⟨h₁, h₂⟩ := surjective_and_ker_unit_subschemeι (annihilatorSheaf F) F ⟨U, hU⟩
  refine ⟨(LinearMap.ker_eq_bot (f := appLinear _ U)).1 (h₂.trans ?_), h₁⟩
  exact Submodule.le_annihilator_iff.1 Submodule.annihilator_top.ge

instance QCoh.isFiniteQC_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [IsFiniteQC F] :
    IsFiniteQC ((Scheme.Modules.pullback f).obj F) :=
  .of_forall_exists_affine fun y => by
    obtain ⟨U, V, hU, hV, hy, -, e⟩ := exists_affine_pair f y (W := ⊤) trivial
    have := finite_sections F hV
    exact ⟨U, hU, hy, finite_sections_pullback f F hU hV e⟩

abbrev QCoh.onAnnihilator : (annihilatorSheaf F).subscheme.Modules :=
  (Scheme.Modules.pullback (annihilatorSheaf F).subschemeι).obj F

def QCoh.isoPushforwardOnAnnihilator :
    F ≅ (Scheme.Modules.pushforward (annihilatorSheaf F).subschemeι).obj (onAnnihilator F) :=
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction (annihilatorSheaf F).subschemeι).unit.app F)

end Annihilator

section DimZero

section General

variable {X : Scheme.{u}} {F : X.Modules}

theorem QCoh.germ_support_bijective (hf : (support F).Finite)
    (hc : ∀ x ∈ support F, IsClosed ({x} : Set X)) :
    Function.Bijective fun (s : Γ(F, ⊤)) (x : support F) =>
      (F.presheaf.germ ⊤ x.1 (Opens.mem_top _) s : (F.presheaf.stalk x.1 :)) := by
  classical
  letI := hf.fintype
  refine ⟨fun s t e => sub_eq_zero.1 (section_eq_zero_of_germ _ fun x hx => ?_), fun t => ?_⟩
  · by_cases h : x ∈ support F
    · rw [map_sub, sub_eq_zero]
      exact congrFun e ⟨x, h⟩
    · exact (notMem_support_iff.1 h).elim _ _
  have key (x : support F) : ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ x.1 (Opens.mem_top _) s = t x ∧
      ∀ y : support F, y ≠ x → F.presheaf.germ ⊤ y.1 (Opens.mem_top _) s = 0 := by
    obtain ⟨V, hx, u, hu⟩ := F.presheaf.exists_germ_eq (t x)
    have hC : IsClosed (support F \ {x.1}) := by
      rw [← Set.biUnion_of_singleton (support F \ {x.1})]
      exact (hf.subset Set.diff_subset).isClosed_biUnion fun y hy => hc y hy.1
    let U : X.Opens := V ⊓ ⟨_, hC.isOpen_compl⟩
    let W : X.Opens := ⟨_, (hc x x.2).isOpen_compl⟩
    have hxU : x.1 ∈ U := ⟨hx, fun h => h.2 rfl⟩
    have : Subsingleton Γ(F, U ⊓ W) :=
      subsingleton_sections_of_notMem_support fun y hy h => hy.1.2 ⟨h, hy.2⟩
    obtain ⟨s, h₁, h₂⟩ := Qcqs.exists_section_glue₂ F (V₁ := U) (V₂ := W) (W := ⊤) le_top le_top
      (fun y _ => (eq_or_ne y x.1).elim (fun e => Or.inl (e ▸ hxU)) Or.inr)
      (F.presheaf.map (homOfLE inf_le_left).op u) 0 (Subsingleton.elim _ _)
    refine ⟨s, ?_, fun y hy => ?_⟩
    · rw [← F.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x.1 hxU, h₁,
        F.presheaf.germ_res_apply, hu]
    · rw [← F.presheaf.germ_res_apply (homOfLE (le_top : W ≤ ⊤)) y.1 fun e => hy (Subtype.ext e),
        h₂, map_zero]
  choose s h₁ h₂ using key
  refine ⟨∑ x, s x, funext fun y => ?_⟩
  beta_reduce
  rw [map_sum, Finset.sum_eq_single y (fun x _ hx => h₂ x y hx.symm) (by simp), h₁]

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]

abbrev residueFieldAlgebraOver (x : X) : Algebra R (X.residueField x) :=
  ((X.Γevaluation x).hom.comp (algebraMap R Γ(X, ⊤))).toAlgebra

variable [IsLocallyNoetherian X] [IsFiniteQC F]

theorem QCoh.isLocallyArtinian_annihilatorSheaf (h : suppDim F ≤ 0) :
    IsLocallyArtinian (annihilatorSheaf F).subscheme :=
  have := LocallyOfFiniteType.isLocallyNoetherian (annihilatorSheaf F).subschemeι
  .of_topologicalKrullDim_le_zero ((topologicalKrullDim_annihilatorSheaf_subscheme F).trans_le h)

theorem QCoh.isClosed_singleton_of_suppDim_le_zero (h : suppDim F ≤ 0) {x : X}
    (hx : x ∈ support F) : IsClosed ({x} : Set X) := by
  have := isLocallyArtinian_annihilatorSheaf h
  obtain ⟨z, rfl⟩ := (range_annihilatorSheaf_subschemeι F).ge hx
  simpa using (annihilatorSheaf F).subschemeι.isClosedEmbedding.isClosedMap _ (isClosed_discrete {z})

theorem QCoh.isArtinianScheme_annihilatorSheaf [CompactSpace X] (h : suppDim F ≤ 0) :
    IsArtinianScheme (annihilatorSheaf F).subscheme :=
  { toIsLocallyArtinian := isLocallyArtinian_annihilatorSheaf h
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (annihilatorSheaf F).subschemeι }

theorem QCoh.finite_support_of_suppDim_le_zero [CompactSpace X] (h : suppDim F ≤ 0) :
    (support F).Finite := by
  have := isArtinianScheme_annihilatorSheaf h
  rw [← range_annihilatorSheaf_subschemeι]
  exact Set.finite_range _

theorem QCoh.isFiniteLength_sections (h : suppDim F ≤ 0) {U : X.Opens} (hU : IsAffineOpen U) :
    IsFiniteLength Γ(X, U) Γ(F, U) := by
  have := isLocallyArtinian_annihilatorSheaf h
  have := finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let I := annihilatorSheaf F
  have : IsArtinianRing Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) :=
    IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hU.preimage I.subschemeι⟩
  have : IsArtinianRing (Γ(X, U) ⧸ Module.annihilator Γ(X, U) Γ(F, U)) :=
    ((Ideal.quotEquivOfEq (I.ker_subschemeι_app ⟨U, hU⟩).symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (I.subschemeι_app_surjective ⟨U, hU⟩))).symm.isArtinianRing
  exact isFiniteLength_of_isArtinianRing_annihilator

theorem QCoh.isFiniteLength_stalk (h : suppDim F ≤ 0) (x : X) :
    IsFiniteLength (X.presheaf.stalk x) (F.presheaf.stalk x :) := by
  obtain ⟨U, hU, hx⟩ := exists_affine_mem x
  obtain ⟨x, rfl⟩ : ∃ x' : U, x' = x := ⟨⟨x, hx⟩, rfl⟩
  have := hU.isLocalization_stalk x
  have := isLocalizedModule_germLinear F hU x
  have hl := isFiniteLength_sections h hU
  rw [← Module.length_ne_top_iff,
    length_eq_length_localizedModule (hU.primeIdealOf x).asIdeal.primeCompl _ (germLinear F x)]
  exact ne_top_of_le_ne_top (Module.length_ne_top_iff.2 hl)
    (length_localizedModule_atPrime_le _ hl)

theorem length_coh_zero_eq_sum [CompactSpace X] (h : suppDim F ≤ 0) :
    Module.length R (coh F 0) = ∑ x ∈ (finite_support_of_suppDim_le_zero h).toFinset,
      Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) *
        (letI := residueFieldAlgebraOver R x; Module.length R (X.residueField x)) := by
  have hf := finite_support_of_suppDim_le_zero h
  letI := hf.fintype
  letI (x : X) := baseModuleStalk F (algebraMap R Γ(X, ⊤)) x
  let l : sectionsOn F ⊤ →ₗ[R] ∀ x : support F, (F.presheaf.stalk x.1 :) :=
    { toFun := fun s x => F.presheaf.germ ⊤ x.1 (Opens.mem_top _) (sectionsOn.toΓ F ⊤ s)
      map_add' := fun s t => funext fun x => by rw [map_add, map_add]; rfl
      map_smul' := fun r s => funext fun x => by
        rw [sectionsOn.toΓ_smul, restrictGlobal_top, germ_smul]; rfl }
  have hl : Function.Bijective l := (germ_support_bijective hf fun x hx =>
    isClosed_singleton_of_suppDim_le_zero h hx).comp (sectionsOn.toΓ F ⊤).bijective
  rw [((cohOn.zeroEquiv R F ⊤).trans (LinearEquiv.ofBijective l hl)).length_eq,
    Module.length_pi_of_fintype, Finset.sum_subtype (p := (· ∈ support F)) _ fun _ => hf.mem_toFinset]
  refine Finset.sum_congr rfl fun x _ => ?_
  letI : Algebra R (X.presheaf.stalk x.1) :=
    ((X.presheaf.germ ⊤ x.1 trivial).hom.comp (algebraMap R Γ(X, ⊤))).toAlgebra
  haveI : IsScalarTower R (X.presheaf.stalk x.1) (F.presheaf.stalk x.1 :) :=
    .of_algebraMap_smul fun _ _ => rfl
  exact length_eq_mul_length_residueField R (isFiniteLength_stalk h x.1)

end General

variable {X : Scheme.{0}} {F : X.Modules} [AlgebraicGeometry.IsNoetherian X] [IsFiniteQC F]

theorem subsingleton_coh_of_suppDim_le_zero (h : suppDim F ≤ 0) {n : ℕ} (hn : 0 < n) :
    Subsingleton (coh F n) := by
  have := isArtinianScheme_annihilatorSheaf h
  have := cohOn.subsingleton_of_isAffineOpen (onAnnihilator F) (isAffineOpen_top _) hn
  exact ((cohOn.mapIso ℤ ⊤ n (isoPushforwardOnAnnihilator F)).trans
    (coh.pushforwardEquiv ℤ (fun r => (map_intCast _ r).trans (eq_intCast _ r).symm)
      (onAnnihilator F) n)).toEquiv.subsingleton

theorem exists_isGen_of_finite {Z : Scheme.{0}} [Finite Z] [IsAffine Z] {M : LB Z} (hM : M.IsLB) :
    ∃ t : M.Gen, t.IsGen := by
  obtain ⟨s, hs, -, -⟩ := exists_sec_finite_subset_of_isQuasiAffine hM Set.finite_univ (U := ⊤)
    (Set.subset_univ _)
  exact exists_isGen_of_nonzeroLocus_eq_top s (top_le_iff.1 hs)

theorem nonempty_twist_iso_of_suppDim_le_zero (h : suppDim F ≤ 0) {M : LB X} (hM : M.IsLB) :
    Nonempty (twist F M ≅ F) := by
  have := isArtinianScheme_annihilatorSheaf h
  have hM' := LB.isLB_pull hM (annihilatorSheaf F).subschemeι
  obtain ⟨t, ht⟩ := exists_isGen_of_finite hM'
  exact ⟨(twistFunctor M).mapIso (isoPushforwardOnAnnihilator F) ≪≫
    (Twist.projIso M _ (onAnnihilator F)).symm ≪≫
    (Scheme.Modules.pushforward _).mapIso (Twist.genIso _ hM' t ht).symm ≪≫
    (isoPushforwardOnAnnihilator F).symm⟩

end DimZero

section Field

variable {X : Scheme.{0}} {k : Type} [Field k] (f : X ⟶ Sp k)

theorem residueDegree_eq_finrank (x : X) :
    f.residueDegree x =
      letI := algebraΓOfHom f
      letI := residueFieldAlgebraOver k x
      Module.finrank k (X.residueField x) := by
  letI := algebraΓOfHom f
  letI := residueFieldAlgebraOver k x
  letI := (f.residueFieldMap x).hom.toAlgebra
  let φ : k →+* (Sp k).residueField (f x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Sp k).Γevaluation (f x)).hom
  have hφ : Function.Surjective φ := by
    have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    intro a
    obtain ⟨b, rfl⟩ := (Sp k).residue_surjective _ a
    obtain ⟨U, hU, c, rfl⟩ := (Sp k).presheaf.exists_germ_eq b
    obtain rfl : U = ⊤ := top_le_iff.1 fun y _ => Subsingleton.elim (f x) y ▸ hU
    obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2 c
    exact ⟨r, rfl⟩
  refine (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective φ ⟨φ.injective, hφ⟩)
    (RingEquiv.refl (X.residueField x)) (RingHom.ext fun r => ?_)).symm
  exact Scheme.Γevaluation_naturality_apply f x _

variable [LocallyOfFiniteType f] [CompactSpace X] {F : X.Modules} [IsFiniteQC F]

include f in

theorem isNoetherian_of_locallyOfFiniteType_field : AlgebraicGeometry.IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  {}

theorem isFinite_annihilatorSheaf (h : suppDim F ≤ 0) :
    IsFinite ((annihilatorSheaf F).subschemeι ≫ f) := by
  have := isNoetherian_of_locallyOfFiniteType_field f
  have := isArtinianScheme_annihilatorSheaf h
  have : LocallyQuasiFinite ((annihilatorSheaf F).subschemeι ≫ f) :=
    .of_finite_preimage_singleton _ fun _ => Set.toFinite _
  exact .of_locallyQuasiFinite _

theorem finiteCohTwists_of_suppDim_le_zero (h : suppDim F ≤ 0) :
    letI := algebraΓOfHom f
    FiniteCohTwists k F := by
  letI := algebraΓOfHom f
  have := isNoetherian_of_locallyOfFiniteType_field f
  have := isArtinianScheme_annihilatorSheaf h
  have := isFinite_annihilatorSheaf f h
  letI := algebraΓOfHom ((annihilatorSheaf F).subschemeι ≫ f)
  have : Module.Finite k Γ((annihilatorSheaf F).subscheme, ⊤) :=
    (((annihilatorSheaf F).subschemeι ≫ f).finite_appTop).comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  exact ((finiteCohTwists_of_isAffine_of_finite k (onAnnihilator F)).pushforward_of_isAffineHom
    (appTop_algebraΓOfHom _ f rfl)).of_iso (isoPushforwardOnAnnihilator F).symm

theorem finite_residueField_of_suppDim_le_zero (h : suppDim F ≤ 0) {x : X} (hx : x ∈ support F) :
    letI := algebraΓOfHom f
    letI := residueFieldAlgebraOver k x
    Module.Finite k (X.residueField x) := by
  letI := algebraΓOfHom f
  letI := residueFieldAlgebraOver k x
  have := isNoetherian_of_locallyOfFiniteType_field f
  have := (finiteCohTwists_of_suppDim_le_zero f h).finiteCoh.finite 0
  have h₀ : Module.length k (coh F 0) ≠ ⊤ := Module.length_ne_top
  rw [length_coh_zero_eq_sum k h] at h₀
  have h₁ := WithTop.sum_ne_top.1 h₀ x ((Set.Finite.mem_toFinset _).2 hx)
  have := mem_support_iff.1 hx
  have h₂ : Module.length k (X.residueField x) ≠ ⊤ := fun e =>
    h₁ (by rw [e]; exact ENat.mul_top Module.length_pos.ne')
  have := (isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h₂)).1
  infer_instance

theorem hdim_zero_eq_sum (h : suppDim F ≤ 0) {S : Finset X} (hS : support F ⊆ S) :
    letI := algebraΓOfHom f
    (hdim k F 0 : ℕ∞) = ∑ x ∈ S,
      Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) * f.residueDegree x := by
  letI := algebraΓOfHom f
  have := isNoetherian_of_locallyOfFiniteType_field f
  have := (finiteCohTwists_of_suppDim_le_zero f h).finiteCoh.finite 0
  rw [hdim_def, ← Module.length_eq_finrank, length_coh_zero_eq_sum k h,
    ← Finset.sum_subset ((finite_support_of_suppDim_le_zero h).toFinset_subset.2 hS)]
  · refine Finset.sum_congr rfl fun x hx => ?_
    letI := residueFieldAlgebraOver k x
    have := finite_residueField_of_suppDim_le_zero f h ((Set.Finite.mem_toFinset _).1 hx)
    rw [residueDegree_eq_finrank, Module.length_eq_finrank]
  · intro x _ hx
    have := notMem_support_iff.1 (mt (Set.Finite.mem_toFinset _).2 hx)
    rw [Module.length_eq_zero, zero_mul]

theorem hdim_zero_eq_sum_toNat (h : suppDim F ≤ 0) {S : Finset X} (hS : support F ⊆ S) :
    letI := algebraΓOfHom f
    hdim k F 0 = ∑ x ∈ S,
      (Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :)).toNat * f.residueDegree x := by
  have := isNoetherian_of_locallyOfFiniteType_field f
  refine Nat.cast_injective (R := ℕ∞) ((hdim_zero_eq_sum f h hS).trans ?_)
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Nat.cast_mul, ENat.coe_toNat (Module.length_ne_top_iff.2 (isFiniteLength_stalk h x))]

end Field

section Twists

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (k : Type v) [Field k]
  [Algebra k Γ(X, ⊤)] {F : X.Modules} [IsFiniteQC F] (h : suppDim F ≤ 0)

include h

theorem hdim_twist_of_suppDim_le_zero {M : LB X} (hM : M.IsLB) (n : ℕ) :
    hdim k (twist F M) n = hdim k F n :=
  (nonempty_twist_iso_of_suppDim_le_zero h hM).elim (hdim_congr k n)

theorem chi_twist_of_suppDim_le_zero {M : LB X} (hM : M.IsLB) : chi k (twist F M) = chi k F :=
  (nonempty_twist_iso_of_suppDim_le_zero h hM).elim (chi_congr k)

theorem chi_eq_hdim_zero_of_suppDim_le_zero : chi k F = hdim k F 0 :=
  chi_eq_hdim_zero k fun _ hn => subsingleton_coh_of_suppDim_le_zero h hn

end Twists

example (I : Ideal ℤ) [I.IsMaximal] (M : LB (Sp ℤ)) (hM : M.IsLB) :
    Nonempty (twist (tildeIntQuotient I) M ≅ tildeIntQuotient I) := by
  have : Module.Finite (CommRingCat.of ℤ) (ModuleCat.of ℤ (ℤ ⧸ I)) :=
    inferInstanceAs (Module.Finite ℤ (ℤ ⧸ I))
  have : IsFiniteQC (tildeIntQuotient I) := (isFiniteQC_tilde_iff _).2 this
  refine nonempty_twist_iso_of_suppDim_le_zero (le_of_eq ?_) hM
  rw [suppDim_tilde]
  refine (Module.supportDim_quotient_eq_ringKrullDim I).trans ?_
  letI := Ideal.Quotient.field I
  exact ringKrullDim_eq_zero_of_field _

end GlobalTheory
