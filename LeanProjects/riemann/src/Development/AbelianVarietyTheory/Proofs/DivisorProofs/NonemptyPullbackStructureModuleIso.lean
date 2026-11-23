import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLink
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackTwistedSectionIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportPullbackEqPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetDimDropClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleLengthDisjointSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatQuasicoherentLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatAffineAvoiding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMapClosedFibre

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.FieldProj

theorem chi_eq_length_sections {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (k : Type)
    [Field k] [Algebra k Γ(X, ⊤)] (F : X.Modules) [IsFiniteQC F] (h : suppDim F ≤ 0) :
    chi k F = (Module.length k (sectionsOn F ⊤)).toNat := by
  rw [chi_eq_hdim_zero k fun n hn => subsingleton_coh_of_suppDim_le_zero h hn, hdim_zero,
    Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

theorem dim_le_zero_of_finite_closed {T : Type} [TopologicalSpace T] {s : Set T} (hs : s.Finite)
    (hc : ∀ x ∈ s, IsClosed ({x} : Set T)) : topologicalKrullDim s ≤ 0 := by
  have : Finite s := hs.to_subtype
  have : T1Space s := ⟨fun x => by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] using
      (hc x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ s)))⟩
  exact topologicalKrullDim_zero_of_discreteTopology s

theorem eq_empty_of_dim_add_one_le_zero {T : Type} [TopologicalSpace T] {S : Set T}
    (h : topologicalKrullDim S + 1 ≤ ((0 : ℕ) : WithBot ℕ∞)) : S = ∅ := by
  by_contra hS
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hS
  have hne : topologicalKrullDim S ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 ⟨⟨x, hx⟩⟩)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
  rw [← ha] at h
  have h' : ((a + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
  rw [WithBot.coe_le_coe] at h'
  simp at h'

theorem closure_nonzeroLocus_eq_top {X : Scheme.{0}} [IsLocallyNoetherian X] {A : LB X}
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

theorem nonempty_pullback_structureModule_iso {X Y : Scheme.{0}} (f : X ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback f).obj (QCoh.structureModule Y) ≅ QCoh.structureModule X) :=
  haveI : (TopologicalSpace.Opens.map f.base).Final :=
    final_of_representablyFlat _
  haveI : IsIso (SheafOfModules.pullbackObjUnitToUnit.{0} f.toRingCatSheafHom) := inferInstance
  ⟨asIso (SheafOfModules.pullbackObjUnitToUnit.{0} f.toRingCatSheafHom)⟩

section Main

variable {k : Type} [Field k] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]
  (f : X ⟶ Y) (hf : ∀ r : k, f.appTop (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(X, ⊤) r)
  (V : Y.Opens) (n : ℕ) (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
  (hfree : letI := (f.app V).hom.toAlgebra
    Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
      Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n)

include hf hV hV' hfree

theorem chi_pullback_eq_mul [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (G : Y.Modules) [IsFiniteQC G] (hdim : suppDim G ≤ 0) (hsub : support G ⊆ (V : Set Y)) :
    chi k ((Scheme.Modules.pullback f).obj G) = n * chi k G := by
  have hfin : (support G).Finite := finite_support_of_suppDim_le_zero hdim
  have hcl : ∀ x ∈ support G, IsClosed ({x} : Set Y) := fun x hx =>
    isClosed_singleton_of_suppDim_le_zero hdim hx
  have hsupp' : support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G :=
    QCoh.support_pullback f G
  have hpts : ∀ y ∈ support ((Scheme.Modules.pullback f).obj G), IsClosed ({y} : Set X) := by
    intro y hy
    rw [hsupp'] at hy
    exact (fibre_finite_isClosed_of_affine_finite f V hV hV' hfree.2.1 _ (hsub hy) (hcl _ hy)).2 y rfl
  have hfin' : (support ((Scheme.Modules.pullback f).obj G)).Finite := by
    rw [hsupp']
    refine (Set.Finite.biUnion (t := fun x => f.base ⁻¹' {x}) hfin fun x hx =>
      (fibre_finite_isClosed_of_affine_finite f V hV hV' hfree.2.1 _ (hsub hx) (hcl _ hx)).1).subset
      fun y hy => ?_
    exact Set.mem_biUnion hy rfl
  have hdim' : suppDim ((Scheme.Modules.pullback f).obj G) ≤ 0 :=
    dim_le_zero_of_finite_closed hfin' hpts
  rw [chi_eq_length_sections k _ hdim, chi_eq_length_sections k _ hdim',
    length_sectionsOn_top_eq_sum_of_separating G k (fun _ : Unit => V)
      (fun x hx => Set.mem_iUnion.2 ⟨(), hsub hx⟩) (fun i j hij => absurd rfl hij),
    length_sectionsOn_top_eq_sum_of_separating _ k (fun _ : Unit => f ⁻¹ᵁ V) ?_
      (fun i j hij => absurd rfl hij)]
  · simp_rw [length_sectionsOn_pullback_of_free k f hf _ n hV hV' hfree G]
    rw [← Finset.mul_sum, ENat.toNat_mul]
    simp
  · intro y hy
    rw [hsupp'] at hy
    exact Set.mem_iUnion.2 ⟨(), hsub hy⟩

theorem diffVanish_chiPic_pullback_sub [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] {A : LB Y} (hA : IsAmpleLB A)
    (hX : ∀ (F : X.Modules) [IsFiniteQC F], FiniteCohTwists k F)
    (hY : ∀ (F : Y.Modules) [IsFiniteQC F], FiniteCohTwists k F) :
    ∀ (m : ℕ) (G : Y.Modules) [IsFiniteQC G], suppDim G ≤ m →
      topologicalKrullDim (support G ∩ (V : Set Y)ᶜ : Set Y) + 1 ≤ (m : WithBot ℕ∞) →
      DiffVanish m ((chiPic k ((Scheme.Modules.pullback f).obj G) ∘ pull f) -
        (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k G) := by
  intro m
  induction m with
  | zero =>
    intro G _ h0 hk
    have hGU : support G ⊆ (V : Set Y) := fun x hx => by
      by_contra h
      have := eq_empty_of_dim_add_one_le_zero hk
      exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hx, h⟩
    refine diffVanish_zero_iff.2 (funext fun c => ?_)
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    have hM' := Semi.LB.isLB_pull hM f
    have := isFiniteQC_twist (F := G) hM
    have e := Twist.pullbackIso G f hM
    have hb := chi_pullback_eq_mul f hf V n hV hV' hfree (twist G M) (by rwa [suppDim_twist hM])
      (by rwa [support_twist hM])
    simp only [Pi.sub_apply, Function.comp_apply, Pi.zero_apply, AddMonoidHom.coe_mulLeft]
    rw [← cls_pull hM f hM', chiPic_cls, chiPic_cls, ← chi_congr k e, hb, sub_self]
  | succ m ih =>
    intro G _ hk hUk
    set G' := (Scheme.Modules.pullback f).obj G
    have hZ : IsClosed (support G ∩ (V : Set Y)ᶜ) :=
      (isClosed_support (F := G)).inter V.isOpen.isClosed_compl
    obtain ⟨S₃, hS₃, hS₃'⟩ := exists_finite_topologicalKrullDim_inter_add_one_le _ hZ
    let S : Set Y := assPoints G ∪ f.base '' assPoints G' ∪ S₃
    have hS : S.Finite := ((finite_assPoints G).union ((finite_assPoints G').image _)).union hS₃
    refine diffVanish_of_generators (closure_nonzeroLocus_eq_top hA hS) fun g hg => ?_
    obtain ⟨N, hN, t, hSt, e⟩ := hg 0
    have hN' := Semi.LB.isLB_pull hN f
    haveI hmono : Mono (cutHom G hN t) :=
      (mono_cutHom_iff G hN t).2 fun x hx => hSt (Or.inl (Or.inl hx))
    haveI hmono' : Mono (cutHom G' hN' (secPull t f)) :=
      (mono_cutHom_iff G' hN' _).2 fun x hx => by
        rw [nonzeroLocus_secPull]
        exact hSt (Or.inl (Or.inr ⟨x, hx, rfl⟩))
    have h₁ := bwdDiff_chiPic_eq_chiPic_cut hN t (hY G)
    have h₂ := bwdDiff_chiPic_eq_chiPic_cut hN' (secPull t f) (hX G')
    obtain ⟨ec⟩ := cut_pullback_iso f G hN t hN'
    have key : bwdDiff (cls N hN) ((chiPic k G' ∘ pull f) -
        (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k G) =
        (chiPic k ((Scheme.Modules.pullback f).obj (cut G hN t)) ∘ pull f) -
          (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k (cut G hN t) := by
      funext c
      have a₁ := congrFun h₁ c
      have a₂ := congrFun h₂ (pull f c)
      rw [chiPic_congr k ec.symm] at a₂
      simp only [bwdDiff_apply] at a₁ a₂
      simp only [bwdDiff_apply, Pi.sub_apply, Function.comp_apply,
        AddMonoidHom.coe_mulLeft, map_sub, cls_pull hN f hN'] at a₂ ⊢
      rw [← a₁, ← a₂]
      ring
    rw [← Fin.cons_self_tail g, multiDiff_cons', e, key]
    refine ih (cut G hN t) (suppDim_cut_le G hN t hk) ?_ _
    have hdim := hS₃' (nonzeroLocus t : Set Y)ᶜ (nonzeroLocus t).isOpen.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.2 fun x hx => hSt (Or.inr hx))
    have hZk : topologicalKrullDim (support G ∩ (V : Set Y)ᶜ : Set Y) ≤ m :=
      ENat.WithBot.add_le_add_one_right_iff.1 (hUk.trans_eq (Nat.cast_succ m))
    refine le_trans ?_ (hdim.trans hZk)
    refine add_le_add_left (topologicalKrullDim_mono ?_) 1
    rw [support_cut]
    rintro x ⟨⟨hx, hx'⟩, hxU⟩
    exact ⟨⟨hx, hxU⟩, hx'⟩

end Main

theorem interNum_pull_eq_mul (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral Y]
    (sY : Y ⟶ Sp k) (f : X ⟶ Y) (hX : IsProjOver (f ≫ sY)) (hY : IsProjOver sY)
    (V : Y.Opens) (n : ℕ) (hgen : genericPoint Y ∈ V) (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra
      Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
        Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d) (L : Fin d → LB Y) (hL : ∀ i, (L i).IsLB) :
    letI := GlobalTheory.algebraΓOfHom (f ≫ sY); letI := GlobalTheory.algebraΓOfHom sY
    GlobalTheory.interNum k (GlobalTheory.QCoh.structureModule X) (fun i => (L i).pull f) =
      (n : ℤ) * GlobalTheory.interNum k (GlobalTheory.QCoh.structureModule Y) L := by
  letI := GlobalTheory.algebraΓOfHom (f ≫ sY)
  letI := GlobalTheory.algebraΓOfHom sY
  have := isNoetherian_of_isProjOver hX
  have := isNoetherian_of_isProjOver hY
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hY
  have hf : ∀ r : k, f.appTop (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(X, ⊤) r := fun _ => rfl
  have hVd : topologicalKrullDim ((V : Set Y)ᶜ : Set Y) + 1 ≤ (d : WithBot ℕ∞) := by
    refine (topologicalKrullDim_add_one_le V.isOpen.isClosed_compl isClosed_univ
      fun x _ => ⟨genericPoint Y, trivial, fun h => h hgen, genericPoint_specializes x⟩).trans ?_
    exact (topologicalKrullDim_subspace_le _ _).trans hd
  have hD := diffVanish_chiPic_pullback_sub f hf V n hV hV' hfree hA
    (fun F _ => finiteCohTwists_of_isProjOver (fun _ => rfl) F hX)
    (fun F _ => finiteCohTwists_of_isProjOver (fun _ => rfl) F hY) d (QCoh.structureModule Y)
    (suppDim_structureModule.trans_le hd)
    ((add_le_add_left (topologicalKrullDim_mono Set.inter_subset_right) 1).trans hVd)
  obtain ⟨e⟩ := nonempty_pullback_structureModule_iso f
  have h0 := congrFun (hD fun i => cls (L i) (hL i)) 0
  simp only [multiDiff_sub, multiDiff_map, multiDiff_comap, Pi.sub_apply, Pi.zero_apply,
    Function.comp_apply, chiPic_congr k e, map_zero] at h0
  rw [AddMonoidHom.coe_mulLeft, sub_eq_zero] at h0
  rw [interNum_eq_multiDiff k _ hL,
    interNum_eq_multiDiff k _ fun i => Semi.LB.isLB_pull (hL i) f]
  exact h0

end GlobalTheory.FieldProj
