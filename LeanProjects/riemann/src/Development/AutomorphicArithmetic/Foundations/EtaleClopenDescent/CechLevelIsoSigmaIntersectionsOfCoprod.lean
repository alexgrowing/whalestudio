import Mathlib
import Development.EtaleCohomology.EtaleSheaves.CechYoneda

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb.RestrictionCovers
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

private theorem mem_iInf_fin {T : Type*} [TopologicalSpace T] {m : ℕ}
    (U : Fin m → TopologicalSpace.Opens T) (x : T) : x ∈ ⨅ k, U k ↔ ∀ k, x ∈ U k := by
  refine ⟨fun h k => (iInf_le U k) h, fun h => ?_⟩
  rw [← Finset.inf_univ_eq_iInf, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
  simp [Finset.inf_eq_iInf, h]

section
variable {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) {n : ℕ}

abbrev P (n : ℕ) : Scheme.{0} :=
  widePullback O.toScheme (fun _ : Fin (n + 1) => ∐ fun j => (V j).toScheme) (fun _ => cov O V hV)

private theorem ι_cov (i : ι) : Sigma.ι (fun j => (V j).toScheme) i ≫ cov O V hV ≫ O.ι = (V i).ι := by
  simp [cov]

variable (W : (Fin (n + 1) → ι) → X.Opens) (hW : ∀ j x, x ∈ W j ↔ ∀ k, x ∈ V (j k))

include hW in
private theorem le_V (j) (k) : W j ≤ V (j k) := fun x hx => (hW j x).1 hx k

include hV hW in
private theorem le_O (j) : W j ≤ O := (le_V V W hW j 0).trans (hV _)

def cmp (j : Fin (n + 1) → ι) : (W j).toScheme ⟶ P O V hV n :=
  WidePullback.lift (X.homOfLE (le_O O V hV W hW j))
    (fun k => X.homOfLE (le_V V W hW j k) ≫ Sigma.ι (fun j => (V j).toScheme) (j k))
    (fun k => by
      rw [← cancel_mono O.ι]
      simp [cov])

theorem cmp_base (j) : cmp O V hV W hW j ≫ WidePullback.base _ = X.homOfLE (le_O O V hV W hW j) :=
  WidePullback.lift_base ..

theorem cmp_π (j) (k) : cmp O V hV W hW j ≫ WidePullback.π _ k =
    X.homOfLE (le_V V W hW j k) ≫ Sigma.ι (fun j => (V j).toScheme) (j k) :=
  WidePullback.lift_π ..

def PJ (j : Fin (n + 1) → ι) : (P O V hV n).Opens :=
  ⨅ k, (WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k) ⁻¹ᵁ
    (Sigma.ι (fun j => (V j).toScheme) (j k)).opensRange

theorem mem_PJ (j) (x : P O V hV n) : x ∈ PJ O V hV j ↔
    ∀ k, ∃ z, Sigma.ι (fun j => (V j).toScheme) (j k) z =
      WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k x := by
  rw [PJ, mem_iInf_fin]
  rfl

include hW in
private theorem hr (j) : Set.range ((PJ O V hV j).ι ≫
    WidePullback.base (fun _ : Fin (n + 1) => cov O V hV) ≫ O.ι) ⊆ Set.range (W j).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (hW j _).2 fun k => ?_
  obtain ⟨z, hz⟩ := (mem_PJ O V hV j _).1 y.2 k
  have e : (V (j k)).ι z = ((PJ O V hV j).ι ≫
      WidePullback.base (fun _ : Fin (n + 1) => cov O V hV) ≫ O.ι) y := by
    rw [← ι_cov O V hV (j k), Scheme.Hom.comp_apply, hz, ← WidePullback.π_arrow _ k]
    simp only [Scheme.Hom.comp_apply, Category.assoc]
    rfl
  rw [← e]
  exact (V (j k)).ι_apply z ▸ z.2

def rr (j : Fin (n + 1) → ι) : (PJ O V hV j).toScheme ⟶ (W j).toScheme :=
  IsOpenImmersion.lift (W j).ι _ (hr O V hV W hW j)

theorem rr_ι (j) : rr O V hV W hW j ≫ (W j).ι =
    (PJ O V hV j).ι ≫ WidePullback.base (fun _ : Fin (n + 1) => cov O V hV) ≫ O.ι :=
  IsOpenImmersion.lift_fac _ _ _

theorem rr_cmp (j) : rr O V hV W hW j ≫ cmp O V hV W hW j = (PJ O V hV j).ι := by
  apply WidePullback.hom_ext
  · intro k
    have hs : Set.range ((PJ O V hV j).ι ≫ WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k) ⊆
        Set.range (Sigma.ι (fun j => (V j).toScheme) (j k)) := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := (mem_PJ O V hV j _).1 y.2 k
      exact ⟨z, by rw [hz, Scheme.Hom.comp_apply]; rfl⟩
    rw [Category.assoc, cmp_π, ← IsOpenImmersion.lift_fac _ _ hs, ← Category.assoc]
    congr 1
    rw [← cancel_mono (V (j k)).ι, Category.assoc, Scheme.homOfLE_ι, rr_ι, ← ι_cov O V hV (j k),
      IsOpenImmersion.lift_fac_assoc, Category.assoc, WidePullback.π_arrow_assoc]
  · rw [Category.assoc, cmp_base, ← cancel_mono O.ι, Category.assoc, Scheme.homOfLE_ι, rr_ι,
      Category.assoc]

private theorem hr3 (j) : Set.range (cmp O V hV W hW j) ⊆ Set.range (PJ O V hV j).ι := by
  rintro _ ⟨w, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (mem_PJ O V hV j _).2 fun k => ⟨X.homOfLE (le_V V W hW j k) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← cmp_π O V hV W hW j k, Scheme.Hom.comp_apply]

def ss (j : Fin (n + 1) → ι) : (W j).toScheme ⟶ (PJ O V hV j).toScheme :=
  IsOpenImmersion.lift (PJ O V hV j).ι _ (hr3 O V hV W hW j)

theorem ss_ι (j) : ss O V hV W hW j ≫ (PJ O V hV j).ι = cmp O V hV W hW j :=
  IsOpenImmersion.lift_fac _ _ _

theorem ss_rr (j) : ss O V hV W hW j ≫ rr O V hV W hW j = 𝟙 _ := by
  rw [← cancel_mono (W j).ι, Category.assoc, rr_ι, ← Category.assoc, ss_ι, ← Category.assoc,
    cmp_base, Scheme.homOfLE_ι, Category.id_comp]

theorem rr_ss (j) : rr O V hV W hW j ≫ ss O V hV W hW j = 𝟙 _ := by
  rw [← cancel_mono (PJ O V hV j).ι, Category.assoc, ss_ι, rr_cmp, Category.id_comp]

instance cmp_open (j) : IsOpenImmersion (cmp O V hV W hW j) := by
  have : IsIso (ss O V hV W hW j) := ⟨rr O V hV W hW j, ss_rr .., rr_ss ..⟩
  rw [← ss_ι]
  infer_instance

private theorem cmp_disj : Pairwise (Function.onFun Disjoint
    (fun j => Set.range (cmp O V hV W hW j))) := by
  intro a b hab
  rw [Function.onFun, Set.disjoint_left]
  rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
    by_contra h
    push_neg at h
    exact hab (funext h)
  have e : Sigma.ι (fun j => (V j).toScheme) (b k) (X.homOfLE (le_V V W hW b k) v) =
      Sigma.ι (fun j => (V j).toScheme) (a k) (X.homOfLE (le_V V W hW a k) u) := by
    rw [← Scheme.Hom.comp_apply, ← cmp_π O V hV W hW b k, Scheme.Hom.comp_apply, hv,
      ← Scheme.Hom.comp_apply, cmp_π, Scheme.Hom.comp_apply]
  exact hk (congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp e)).symm

instance cmp_sigma_open : IsOpenImmersion (Sigma.desc (cmp O V hV W hW)) :=
  isOpenImmersion_sigmaDesc _ _ (cmp_disj O V hV W hW)

instance cmp_sigma_surj : Surjective (Sigma.desc (cmp O V hV W hW)) := by
  refine ⟨fun x => ?_⟩
  have hx : ∀ k, ∃ i, ∃ z, Sigma.ι (fun j => (V j).toScheme) i z =
      WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k x := by
    intro k
    obtain ⟨⟨i, z⟩, hz⟩ := (sigmaMk (fun j => (V j).toScheme)).surjective
      (WidePullback.π (fun _ : Fin (n + 1) => cov O V hV) k x)
    rw [sigmaMk_mk] at hz
    exact ⟨i, z, hz⟩
  choose j z hz using hx
  have hm : x ∈ PJ O V hV j := (mem_PJ O V hV j x).2 fun k => ⟨z k, hz k⟩
  let y : (PJ O V hV j).toScheme := ⟨x, hm⟩
  have key : (rr O V hV W hW j ≫ cmp O V hV W hW j) y = x := by
    rw [rr_cmp]
    exact (PJ O V hV j).ι_apply _
  refine ⟨(Sigma.ι (fun j => (W j).toScheme) j) (rr O V hV W hW j y), ?_⟩
  rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans key

instance cmp_sigma_iso : IsIso (Sigma.desc (cmp O V hV W hW)) :=
  (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, inferInstance⟩

end

end UpperTheory.Cb.RestrictionCovers

namespace UpperTheory.Cb.RestrictionCovers
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

theorem nat_sq {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens)
    (hV : ∀ j, V j ≤ O) (n : ℕ)
    (hW : ∀ (j : Fin (n + 1) → ι) x, x ∈ (⨅ k, V (j k)) ↔ ∀ k, x ∈ V (j k))
    (hW' : ∀ (j : Fin (n + 1) → ι) x, x ∈ g ⁻¹ᵁ (⨅ k, V (j k)) ↔ ∀ k, x ∈ g ⁻¹ᵁ V (j k)) :
    Limits.Sigma.desc (cmp (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)) _ hW') ≫
        wpMap (sqS g O V hV) n =
      Limits.Sigma.map (fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k))) ≫
        Limits.Sigma.desc (cmp O V hV _ hW) := by
  apply Sigma.hom_ext
  intro j
  simp only [Sigma.ι_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_desc]
  apply WidePullback.hom_ext
  · intro k
    simp only [wpMap, sqS, Category.assoc, WidePullback.lift_π, Arrow.homMk_left]
    rw [← Category.assoc, cmp_π, cmp_π, Category.assoc, Sigma.ι_map, ← Category.assoc,
      ← Category.assoc]
    congr 1
    rw [← cancel_mono (V (j k)).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.homOfLE_ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  · simp only [wpMap, sqS, Category.assoc, WidePullback.lift_base, Arrow.homMk_right]
    rw [← Category.assoc, cmp_base, cmp_base, ← cancel_mono O.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, Scheme.homOfLE_ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]

end UpperTheory.Cb.RestrictionCovers

open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev UpperTheory.Cb.RestrictionCovers in
theorem UpperTheory.Cb.cechLevel_iso_sigma_intersections_of_coprod :
    LateralTheory.E.t_E3Cut.Coprod → LateralTheory.E.CechSigma_xy1Pf_Lev.SchemeLevel := by
  intro _ Y X g O ι V hV n
  have hW : ∀ (j : Fin (n + 1) → ι) x, x ∈ (⨅ k, V (j k)) ↔ ∀ k, x ∈ V (j k) :=
    fun j x => mem_iInf_fin (fun k => V (j k)) x
  have hW' : ∀ (j : Fin (n + 1) → ι) x, x ∈ g ⁻¹ᵁ (⨅ k, V (j k)) ↔ ∀ k, x ∈ g ⁻¹ᵁ V (j k) :=
    fun j x => mem_iInf_fin (fun k => V (j k)) (g x)
  exact ⟨(Arrow.isoMk (asIso (Limits.Sigma.desc (cmp (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j)
    (fun j => pre_le g (hV j)) _ hW'))) (asIso (Limits.Sigma.desc (cmp O V hV _ hW)))
    (nat_sq g O V hV n hW hW')).symm⟩
