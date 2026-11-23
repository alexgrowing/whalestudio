import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocusCodimBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatCoverExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackTwistedSectionIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackVerticalDivisorIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportPullbackEqPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetDimDropClosedStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Twist

namespace GlobalTheory.VertDegProj

theorem exists_goodOpen {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B B' : Vert.Model O) (f : Vert.Model.Hom B' B) (hB : GlobalTheory.IsNormalScheme B.X) (hf : f.relDim = 0) :
    ∃ (U : B.X.Opens) (n : ℕ), 0 < n ∧ f.fibreDeg 1 = n ∧
      topologicalKrullDim ((U : Set B.X)ᶜ : Set B.X) + 1 ≤ (B.relDim : WithBot ℕ∞) ∧
      ∀ x ∈ U, ∃ V : B.X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧
        (letI := (f.f.app V).hom.toAlgebra
         Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧
          Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = n) :=
  GlobalTheory.T.finite_flat_locus_codim_bound O B B' f hB hf

theorem chiLen_pullback_of_suppDim_le_zero {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (B B' : Vert.Model O) (f : Vert.Model.Hom B' B) (U : B.X.Opens) (n : ℕ)
    (hU : ∀ x ∈ U, ∃ V : B.X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧
        (letI := (f.f.app V).hom.toAlgebra
         Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧
          Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = n))
    (G : B.X.Modules) [IsFiniteQC G] (hG : B.IsVertical G) (h0 : suppDim G ≤ 0)
    (hGU : support G ⊆ (U : Set B.X)) :
    chiLen O ((Scheme.Modules.pullback f.f).obj G) = n * chiLen O G :=
  GlobalTheory.T.finite_flat_cover_extension O B B' f U n hU G hG h0 hGU

theorem nonempty_pullback_cut_iso {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent]
    {L : LB X} (hL : L.IsLB) (s : L.Sec) (hL' : (L.pull f).IsLB) :
    Nonempty ((Scheme.Modules.pullback f).obj (cut G hL s) ≅
      cut ((Scheme.Modules.pullback f).obj G) hL' (secPull s f)) :=
  GlobalTheory.T.pullback_twisted_section_iso f G hL s hL'

theorem nonempty_pullback_twist_iso {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules)
    {M : LB X} (hM : M.IsLB) :
    Nonempty ((Scheme.Modules.pullback f).obj (twist G M) ≅
      twist ((Scheme.Modules.pullback f).obj G) (M.pull f)) := ⟨pullbackIso G f hM⟩

theorem nonempty_pullback_divMod_iso {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B B' : Vert.Model O) (f : Vert.Model.Hom B' B) (I : B.effVert) :
    Nonempty ((Scheme.Modules.pullback f.f).obj (divMod I.1) ≅
      divMod (Vert.Model.effPull f.comp_str I).1) :=
  GlobalTheory.T.pullback_vertical_divisor_iso O B B' f I

theorem support_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [IsFiniteQC G] :
    support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G :=
  GlobalTheory.T.support_pullback_eq_preimage f G

theorem exists_finite_dim_inter_add_one_le {T : Type} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] [QuasiSober T] (Z : Set T) (hZ : IsClosed Z) :
    ∃ S : Set T, S.Finite ∧ ∀ C : Set T, IsClosed C → Disjoint S C →
      topologicalKrullDim (Z ∩ C : Set T) + 1 ≤ topologicalKrullDim Z :=
  GlobalTheory.T.exists_finite_set_dim_drop_closed Z hZ

end GlobalTheory.VertDegProj

namespace GlobalTheory.VertDegProj

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

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

abbrev cmpFn (B B' : Vert.Model O) (f : Vert.Model.Hom B' B) (n : ℕ) (G : B.X.Modules) :
    Pic B.X → ℤ :=
  (chiLenPic O ((Scheme.Modules.pullback f.f).obj G) ∘ pull f.f) -
    (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiLenPic O G

theorem isVertical_pullback (B B' : Vert.Model O) (f : Vert.Model.Hom B' B) (G : B.X.Modules)
    [IsFiniteQC G] (hG : B.IsVertical G) : B'.IsVertical ((Scheme.Modules.pullback f.f).obj G) :=
  fun x hx hx' => by
    rw [support_pullback] at hx
    exact hG _ hx ((Vert.Model.preimage_gen f.comp_str).ge hx')

theorem eq_empty_of_dim_add_one_le_zero {T : Type} [TopologicalSpace T] {S : Set T}
    (h : topologicalKrullDim S + 1 ≤ ((0 : ℕ) : WithBot ℕ∞)) : S = ∅ := by
  by_contra hS
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hS
  have : Nonempty S := ⟨⟨x, hx⟩⟩
  have hne : topologicalKrullDim S ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 ⟨⟨x, hx⟩⟩)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
  rw [← ha] at h
  have h' : ((a + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
  rw [WithBot.coe_le_coe] at h'
  simp at h'

theorem diffVanish_cmpFn (B B' : Vert.Model O) (f : Vert.Model.Hom B' B) (U : B.X.Opens) (n : ℕ)
    (hU : ∀ x ∈ U, ∃ V : B.X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧
        (letI := (f.f.app V).hom.toAlgebra
         Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧
          Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = n)) :
    ∀ (k : ℕ) (G : B.X.Modules) [IsFiniteQC G], B.IsVertical G → suppDim G ≤ k →
      topologicalKrullDim (support G ∩ (U : Set B.X)ᶜ : Set B.X) + 1 ≤ (k : WithBot ℕ∞) →
      DiffVanish k (cmpFn B B' f n G) := by
  obtain ⟨A, hA⟩ := B.exists_isAmpleLB
  have := hA.noetherianSpace
  intro k
  induction k with
  | zero =>
    intro G _ hG h0 hk
    have hGU : support G ⊆ (U : Set B.X) := fun x hx => by
      by_contra h
      have := eq_empty_of_dim_add_one_le_zero hk
      exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hx, h⟩
    refine diffVanish_zero_iff.2 (funext fun c => ?_)
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    have hM' := Semi.LB.isLB_pull hM f.f
    have := isFiniteQC_twist (F := G) hM
    obtain ⟨e⟩ := nonempty_pullback_twist_iso f.f G hM
    have hb := chiLen_pullback_of_suppDim_le_zero B B' f U n hU (twist G M)
      (fun x hx => hG x (by rwa [support_twist hM] at hx)) (by rwa [suppDim_twist hM])
      (by rwa [support_twist hM])
    simp only [cmpFn, Pi.sub_apply, Function.comp_apply, Pi.zero_apply, AddMonoidHom.coe_mulLeft]
    rw [← cls_pull hM f.f hM', chiLenPic_cls, chiLenPic_cls, ← chiLen_congr O e, hb, sub_self]
  | succ k ih =>
    intro G _ hG hk hUk
    set G' := (Scheme.Modules.pullback f.f).obj G
    have hZ : IsClosed (support G ∩ (U : Set B.X)ᶜ) :=
      (isClosed_support (F := G)).inter U.isOpen.isClosed_compl
    obtain ⟨S₃, hS₃, hS₃'⟩ := exists_finite_dim_inter_add_one_le _ hZ
    let S : Set B.X := assPoints G ∪ f.f.base '' assPoints G' ∪ S₃
    have hS : S.Finite := ((finite_assPoints G).union ((finite_assPoints G').image _)).union hS₃
    refine diffVanish_of_generators (closure_nonzeroLocus_eq_top hA hS) fun g hg => ?_
    obtain ⟨N, hN, t, hSt, e⟩ := hg 0
    have hN' := Semi.LB.isLB_pull hN f.f
    haveI hmono : Mono (cutHom G hN t) :=
      (mono_cutHom_iff G hN t).2 fun x hx => hSt (Or.inl (Or.inl hx))
    haveI hmono' : Mono (cutHom G' hN' (secPull t f.f)) :=
      (mono_cutHom_iff G' hN' _).2 fun x hx => by
        rw [nonzeroLocus_secPull]
        exact hSt (Or.inl (Or.inr ⟨x, hx, rfl⟩))
    have hG'v := isVertical_pullback B B' f G hG
    obtain ⟨-, h₁⟩ := bwdDiff_chiLenPic (R := O) hN t hG.finiteLenTwists
    obtain ⟨-, h₂⟩ := bwdDiff_chiLenPic (R := O) hN' (secPull t f.f) hG'v.finiteLenTwists
    obtain ⟨ec⟩ := nonempty_pullback_cut_iso f.f G hN t hN'
    have key : bwdDiff (cls N hN) (cmpFn B B' f n G) = cmpFn B B' f n (cut G hN t) := by
      funext c
      have a₁ := congrFun h₁ c
      have a₂ := congrFun h₂ (pull f.f c)
      rw [chiLenPic_congr O ec.symm] at a₂
      simp only [bwdDiff_apply] at a₁ a₂
      simp only [cmpFn, bwdDiff_apply, Pi.sub_apply, Function.comp_apply,
        AddMonoidHom.coe_mulLeft, map_sub, cls_pull hN f.f hN'] at a₂ ⊢
      rw [← a₁, ← a₂]
      ring
    rw [← Fin.cons_self_tail g, multiDiff_cons', e, key]
    have hsub : support (cut G hN t) ⊆ support G := by
      rw [support_cut]; exact Set.diff_subset
    refine ih (cut G hN t) (fun x hx => hG x (hsub hx)) (suppDim_cut_le G hN t hk) ?_ _
    have hdim := hS₃' (nonzeroLocus t : Set B.X)ᶜ (nonzeroLocus t).isOpen.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.2 fun x hx => hSt (Or.inr hx))
    have hZk : topologicalKrullDim (support G ∩ (U : Set B.X)ᶜ : Set B.X) ≤ k :=
      ENat.WithBot.add_le_add_one_right_iff.1 (hUk.trans_eq (Nat.cast_succ k))
    refine le_trans ?_ (hdim.trans hZk)
    refine add_le_add_left (topologicalKrullDim_mono ?_) 1
    rw [support_cut]
    rintro x ⟨⟨hx, hx'⟩, hxU⟩
    exact ⟨⟨hx, hxU⟩, hx'⟩

theorem vDeg_effPull (B B' : Vert.Model O) (f : Vert.Model.Hom B' B) (U : B.X.Opens) (n : ℕ)
    (hU : ∀ x ∈ U, ∃ V : B.X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧ IsAffineOpen (f.f ⁻¹ᵁ V) ∧
        (letI := (f.f.app V).hom.toAlgebra
         Module.Free Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧ Module.Finite Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) ∧
          Module.finrank Γ(B.X, V) Γ(B'.X, f.f ⁻¹ᵁ V) = n))
    (hUd : topologicalKrullDim ((U : Set B.X)ᶜ : Set B.X) + 1 ≤ (B.relDim : WithBot ℕ∞))
    (hrd : B'.relDim = B.relDim) (I : B.effVert) (Q : PicSym B.X) :
    B'.vDeg (Vert.Model.ofEff (Vert.Model.effPull f.comp_str I)) (picSymPull f.f Q) =
      n * B.vDeg (Vert.Model.ofEff I) Q := by
  have hv := Vert.Model.isVertical_divMod I
  have hv' := Vert.Model.isVertical_divMod (Vert.Model.effPull f.comp_str I)
  obtain ⟨e⟩ := nonempty_pullback_divMod_iso B B' f I
  have hsupp : suppDim (divMod I.1) ≤ B.relDim :=
    (topologicalKrullDim_mono hv).trans B.dim_special_le
  have hD := diffVanish_cmpFn B B' f U n hU B.relDim (divMod I.1) hv hsupp
    ((add_le_add_left (topologicalKrullDim_mono Set.inter_subset_right) 1).trans hUd)
  rw [Vert.Model.vDeg_ofEff, Vert.Model.vDeg_ofEff, Vert.Model.effDeg, Vert.Model.effDeg,
    Vert.Model.IsVertical.deg, Vert.Model.IsVertical.deg, ← picForm_comap]
  rw [← smul_eq_mul, ← LinearMap.smul_apply]
  refine LinearMap.congr_fun (picSym_linearMap_ext fun m g => ?_) Q
  rw [picForm_prod, LinearMap.smul_apply, picForm_prod, hrd, smul_eq_mul]
  split_ifs with hm
  · rw [Fintype.card_fin] at hm
    subst hm
    have h0 := congrFun (hD g) 0
    simp only [cmpFn, multiDiff_sub, multiDiff_map, Pi.sub_apply, Pi.zero_apply,
      Function.comp_apply, chiLenPic_congr O e] at h0
    rw [AddMonoidHom.coe_mulLeft, sub_eq_zero] at h0
    rw [h0]
    push_cast
    ring
  · simp

theorem capDeg_vp_vPullQ : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O),
    GlobalTheory.IsNormalScheme B.X → ∀ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B),
    f.relDim = 0 → 0 < f.fibreDeg 1 ∧ ∀ (d : B.VDivQ) (Q : PicSym B.X),
      B'.capDeg_vp p (GlobalTheory.Vert.Model.vPullQ f.comp_str d) (picSymPull f.f Q) =
        f.fibreDeg 1 * B.capDeg_vp p d Q := by
  intro O _ _ _ p _ _ _ B hB B' f hf
  obtain ⟨U, n, hn, hfd, hUd, hU⟩ := exists_goodOpen B B' f hB hf
  have hrd : B'.relDim = B.relDim := by
    have := f.relDim_add
    omega
  refine ⟨by rw [hfd]; exact_mod_cast hn, fun d Q => ?_⟩
  have hZ : ∀ D : B.VDivZ, B'.vDeg (Vert.Model.vPull f.comp_str D) (picSymPull f.f Q) =
      n * B.vDeg D Q := by
    intro D
    obtain ⟨I, J, rfl⟩ := Vert.Model.exists_eq_ofEff_sub D
    rw [map_sub, map_sub, map_sub, Vert.Model.vPull_ofEff, Vert.Model.vPull_ofEff,
      LinearMap.sub_apply, LinearMap.sub_apply, vDeg_effPull B B' f U n hU hUd hrd,
      vDeg_effPull B B' f U n hU hUd hrd, mul_sub]
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul a D =>
    have e : (a ⊗ₜ[ℤ] D : B.VDivQ) = a • Vert.Model.toQ D := by
      change a ⊗ₜ[ℤ] D = a • ((1 : ℚ) ⊗ₜ[ℤ] D)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simp only [e, map_smul, LinearMap.smul_apply, Vert.Model.vPullQ_toQ]
    rw [Vert.Model.capDeg_vp_toQ, Vert.Model.capDeg_vp_toQ, hZ, hfd]
    simp only [smul_eq_mul]
    ring
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb, mul_add]

end GlobalTheory.VertDegProj
