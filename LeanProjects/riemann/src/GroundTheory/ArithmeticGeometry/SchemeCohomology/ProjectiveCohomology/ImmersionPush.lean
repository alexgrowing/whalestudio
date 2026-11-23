import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Generation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory

universe u

noncomputable section

variable {X Y : Scheme.{u}}

lemma app_resO (i : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (r : Γ(Y, U)) :
    i.app V (resO h r) = resO ((Opens.map i.base).monotone h) (i.app U r) := by
  have := i.naturality (homOfLE h).op
  exact congrArg (fun φ => φ.hom r) this

variable (i : X ⟶ Y)

lemma resF_pushforward (F : X.Modules) {U V : Y.Opens} (h : V ≤ U)
    (m : Γ((Scheme.Modules.pushforward i).obj F, U)) :
    resF ((Scheme.Modules.pushforward i).obj F) h m =
      resF F ((Opens.map i.base).monotone h) m := rfl

lemma smul_pushforward (F : X.Modules) {U : Y.Opens} (r : Γ(Y, U))
    (m : Γ((Scheme.Modules.pushforward i).obj F, U)) :
    r • m = (i.app U r • (show Γ(F, i ⁻¹ᵁ U) from m) : Γ(F, i ⁻¹ᵁ U)) := rfl

theorem isQuasicoherent_pushforward_of_isAffineHom [IsAffineHom i] (F : X.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pushforward i).obj F).IsQuasicoherent := by
  refine isQuasicoherent_of_affineCover _ (fun V : Y.affineOpens => (V : Y.Opens))
    (fun V => V.2) (iSup_affineOpens_eq_top Y) ?_ ?_
  · intro V f
    have hV' : IsAffineOpen (i ⁻¹ᵁ (V : Y.Opens)) := V.2.preimage i
    have hb : i ⁻¹ᵁ Y.basicOpen f = X.basicOpen (i.app V f) := Scheme.preimage_basicOpen i f
    show ∀ m : Γ(F, i ⁻¹ᵁ Y.basicOpen f), ∃ (e : ℕ) (m' : Γ(F, i ⁻¹ᵁ (V : Y.Opens))),
      resF F ((Opens.map i.base).monotone (Y.basicOpen_le f)) m' =
        i.app (Y.basicOpen f) (resO (Y.basicOpen_le f) f ^ e) • m
    intro m
    obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F hV' (i.app V f) (resF F hb.ge m)
    refine ⟨e, m', ?_⟩
    have h2 := congrArg (resF F hb.le) hm'
    rw [resF_resF, resF_smul, resF_resF, resF_self, map_pow, resO_resO] at h2
    rw [h2, map_pow, app_resO]
  · intro V f
    have hV' : IsAffineOpen (i ⁻¹ᵁ (V : Y.Opens)) := V.2.preimage i
    have hb : i ⁻¹ᵁ Y.basicOpen f = X.basicOpen (i.app V f) := Scheme.preimage_basicOpen i f
    show ∀ m : Γ(F, i ⁻¹ᵁ (V : Y.Opens)),
      resF F ((Opens.map i.base).monotone (Y.basicOpen_le f)) m = 0 →
        ∃ e : ℕ, i.app V (f ^ e) • m = 0
    intro m hm
    obtain ⟨e, he⟩ := qcoh_exists_pow_smul_eq_zero F hV' (i.app V f) m (by
      have h2 := congrArg (resF F hb.ge) hm
      rw [resF_resF, map_zero] at h2
      exact h2)
    exact ⟨e, by rw [map_pow]; exact he⟩

theorem isCoherent_pushforward_of_isClosedImmersion [IsClosedImmersion i] {F : X.Modules}
    (hF : IsCoherent F) : IsCoherent ((Scheme.Modules.pushforward i).obj F) := by
  have := hF.1
  have := isQuasicoherent_pushforward_of_isAffineHom i F
  refine isCoherent_of_affineCover _ (fun V : Y.affineOpens => (V : Y.Opens)) (fun V => V.2)
    (iSup_affineOpens_eq_top Y) (fun V => ?_)
  have hfin := hF.2 _ (V.2.preimage i)
  obtain ⟨S, hS⟩ := hfin.fg_top
  have hsurj := Scheme.Hom.app_surjective i V V.2
  let S' : Finset Γ((Scheme.Modules.pushforward i).obj F, V) := S
  refine ⟨⟨S', ?_⟩⟩
  have key : ∀ x : Γ(F, i ⁻¹ᵁ (V : Y.Opens)),
      x ∈ Submodule.span Γ(X, i ⁻¹ᵁ (V : Y.Opens)) (S : Set Γ(F, i ⁻¹ᵁ (V : Y.Opens))) →
      (show Γ((Scheme.Modules.pushforward i).obj F, V) from x) ∈
        Submodule.span Γ(Y, V) (S' : Set Γ((Scheme.Modules.pushforward i).obj F, V)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      obtain ⟨c', rfl⟩ := hsurj c
      exact Submodule.smul_mem _ c' hx
  rw [eq_top_iff]
  intro m _
  exact key m (by rw [hS]; exact Submodule.mem_top)

section Span

abbrev freeM (Y : Scheme.{u}) (κ : Type u) : Y.Modules := SheafOfModules.free κ

attribute [local instance] Abelian.hasFiniteBiproducts

variable {Y : Scheme.{u}}

lemma sum_val_app' {M N : SheafOfModules.{u} Y.ringCatSheaf} {κ : Type*} (s : Finset κ)
    (f : κ → (M ⟶ N)) (W : Y.Opens) (x : M.val.obj (op W)) :
    (∑ k ∈ s, f k).val.app (op W) x = ∑ k ∈ s, (f k).val.app (op W) x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

lemma free_section_eq_sum {κ : Type u} [Fintype κ] (W : Y.Opens)
    (z : (SheafOfModules.free (R := Y.ringCatSheaf) κ).val.obj (op W)) :
    ∃ c : κ → Γ(Y, W), z = ∑ k, (SheafOfModules.ιFree (R := Y.ringCatSheaf) k).val.app (op W)
      (c k) := by
  let b := Bicone.ofColimitCocone (colimit.isColimit
    (Discrete.functor fun _ : κ => SheafOfModules.unit Y.ringCatSheaf))
  have hb : b.IsBilimit := biconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _)
  have h := congrArg (fun φ => φ.val.app (op W) z) (IsBilimit.total hb)
  have h2 := sum_val_app' Finset.univ (fun j => b.π j ≫ b.ι j) W z
  exact ⟨fun k => (b.π k).val.app (op W) z, h.symm.trans h2⟩

lemma sections_val_eq_resF (F : Y.Modules) (s : F.sections) (W : Y.Opens) :
    (show Γ(F, W) from s.val (op W)) = resF F (le_top : W ≤ ⊤) (show Γ(F, ⊤) from s.val (op ⊤)) :=
  (s.property (homOfLE (le_top : W ≤ ⊤)).op).symm

theorem span_eq_top_of_generatingSections (G : Y.Modules) [G.IsQuasicoherent]
    (σ : G.GeneratingSections) [σ.IsFiniteType] {V : Y.Opens} (hV : IsAffineOpen V) :
    Submodule.span Γ(Y, V) (Set.range fun k => resF G (le_top : V ≤ ⊤)
      (show Γ(G, ⊤) from (σ.s k).val (op ⊤))) = ⊤ := by
  classical
  have : Finite σ.I := (inferInstance : σ.IsFiniteType).finite
  have := Fintype.ofFinite σ.I
  set N := Submodule.span Γ(Y, V) (Set.range fun k => resF G (le_top : V ≤ ⊤)
      (show Γ(G, ⊤) from (σ.s k).val (op ⊤))) with hN
  let π : freeM Y σ.I ⟶ G := G.freeHomEquiv.symm σ.s
  have hπ : Epi π := ⟨fun g h e => σ.epi.left_cancellation g h e⟩
  have hab : Epi (modulesAbMap π) := epi_modulesAbMap π
  have hls := (Sheaf.isLocallySurjective_iff_epi' (φ := modulesAbMap π)).2 hab
  have hloc : ∀ g : Γ(G, V), ∀ y ∈ V, ∃ f : Γ(Y, V), y ∈ Y.basicOpen f ∧
      ∃ a : ℕ, f ^ a • g ∈ N := by
    intro g y hy
    have hmem := Presheaf.IsLocallySurjective.imageSieve_mem (self := hls) (U := V) g
    rw [Opens.mem_grothendieckTopology] at hmem
    obtain ⟨W, iW, ⟨z, hz⟩, hyW⟩ := hmem y hy
    obtain ⟨f, hfW, hyf⟩ := hV.exists_basicOpen_le (V := W) ⟨y, hyW⟩ hy
    have hDV : Y.basicOpen f ≤ V := Y.basicOpen_le f
    set x : σ.I → Γ(G, ⊤) := fun k => (show Γ(G, ⊤) from (σ.s k).val (op ⊤)) with hx
    obtain ⟨c, hc⟩ := free_section_eq_sum (Y := Y) (Y.basicOpen f)
      (resF (freeM Y σ.I) hfW (show Γ(freeM Y σ.I, W) from z))

    have hg : resF G hDV g = ∑ k, c k • resF G (le_top : Y.basicOpen f ≤ ⊤) (x k) := by
      have h1 : resF G hfW (π.app W z) = π.app (Y.basicOpen f) (resF (freeM Y σ.I) hfW z) :=
        (NatTrans.naturality_apply (modulesAbMap π).hom (homOfLE hfW).op z).symm
      have h2 : π.app W z = resF G iW.le g := hz
      rw [h2, resF_resF, hc] at h1
      rw [h1]
      change (π.val.app (op (Y.basicOpen f))) (∑ k, (SheafOfModules.ιFree k).val.app
        (op (Y.basicOpen f)) (c k)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [freeHomEquiv_symm_app_ιFree, sections_val_eq_resF]

    let _ : Algebra Γ(Y, V) Γ(Y, Y.basicOpen f) := (resO hDV).toAlgebra
    have := hV.isLocalization_basicOpen f
    choose n b hb using fun k => IsLocalization.Away.surj f (c k)
    let a := ∑ k, n k
    have hna : ∀ k, n k ≤ a := fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
    let b' : σ.I → Γ(Y, V) := fun k => b k * f ^ (a - n k)
    have hb' : ∀ k, resO hDV (b' k) = resO hDV f ^ a * c k := by
      intro k
      have := hb k
      change c k * resO hDV f ^ n k = resO hDV (b k) at this
      simp only [b', map_mul, map_pow, ← this]
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (hna k), mul_comm]
    let δ : Γ(G, V) := f ^ a • g - ∑ k, b' k • resF G (le_top : V ≤ ⊤) (x k)
    have hδ : resF G hDV δ = 0 := by
      simp only [δ, map_sub, map_sum, resF_smul, resF_resF, hg, Finset.smul_sum, smul_smul,
        map_pow, hb']
      rw [sub_self]
    obtain ⟨e, he⟩ := qcoh_exists_pow_smul_eq_zero G hV f δ hδ
    refine ⟨f, hyf, e + a, ?_⟩
    have : f ^ (e + a) • g = ∑ k, (f ^ e * b' k) • resF G (le_top : V ≤ ⊤) (x k) := by
      simp only [δ, smul_sub, Finset.smul_sum, smul_smul] at he
      rw [pow_add]
      exact sub_eq_zero.1 he
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  rw [eq_top_iff]
  intro g _
  have hT : Ideal.span {f : Γ(Y, V) | ∃ a : ℕ, f ^ a • g ∈ N} = ⊤ := by
    rw [← hV.iSup_basicOpen_eq_self_iff]
    apply le_antisymm (iSup_le fun f => Y.basicOpen_le _)
    intro y hy
    obtain ⟨f, hyf, a, ha⟩ := hloc g y hy
    exact Opens.mem_iSup.2 ⟨⟨f, a, ha⟩, hyf⟩
  have hrad : Ideal.span {f : Γ(Y, V) | ∃ a : ℕ, f ^ a • g ∈ N} ≤ (N.colon {g}).radical :=
    Ideal.span_le.2 fun f ⟨a, ha⟩ => ⟨a, Submodule.mem_colon_singleton.2 ha⟩
  have hI : N.colon {g} = ⊤ := Ideal.radical_eq_top.1 (eq_top_iff.2 (hT ▸ hrad))
  have h1 : (1 : Γ(Y, V)) ∈ N.colon {g} := hI ▸ Submodule.mem_top
  simpa using Submodule.mem_colon_singleton.1 h1

theorem exists_generatingSections_of_pushforward_of_isAffineHom {X : Scheme.{u}} (i : X ⟶ Y)
    [IsAffineHom i] (M : X.Modules) [M.IsQuasicoherent]
    (h : ∃ σ : ((Scheme.Modules.pushforward i).obj M).GeneratingSections, σ.IsFiniteType) :
    ∃ σ : M.GeneratingSections, σ.IsFiniteType := by
  obtain ⟨σ, hσ⟩ := h
  have : Finite σ.I := hσ.finite
  have := isQuasicoherent_pushforward_of_isAffineHom i M
  refine exists_generatingSections M (fun U : Y.affineOpens => i ⁻¹ᵁ (U : Y.Opens))
    (fun U => U.2.preimage i) ?_ (κ := σ.I)
    (fun k => (show Γ(M, ⊤) from (σ.s k).val (op ⊤))) (fun U => ?_)
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
    rfl
  · have hY := span_eq_top_of_generatingSections _ σ U.2
    rw [eq_top_iff]
    intro m _
    have key : ∀ z : Γ((Scheme.Modules.pushforward i).obj M, U), z ∈ Submodule.span Γ(Y, U)
        (Set.range fun k => resF ((Scheme.Modules.pushforward i).obj M) (le_top : (U : Y.Opens) ≤ ⊤)
          (show Γ((Scheme.Modules.pushforward i).obj M, ⊤) from (σ.s k).val (op ⊤))) →
        (show Γ(M, i ⁻¹ᵁ (U : Y.Opens)) from z) ∈ Submodule.span Γ(X, i ⁻¹ᵁ (U : Y.Opens))
          (Set.range fun k => resF M (le_top : i ⁻¹ᵁ (U : Y.Opens) ≤ ⊤)
            (show Γ(M, ⊤) from (σ.s k).val (op ⊤))) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul c x _ hx => exact Submodule.smul_mem _ (i.app U c) hx
    exact key m (by rw [hY]; exact Submodule.mem_top)

end Span

end

end GroundTheory.Arith.SchemeCoh
