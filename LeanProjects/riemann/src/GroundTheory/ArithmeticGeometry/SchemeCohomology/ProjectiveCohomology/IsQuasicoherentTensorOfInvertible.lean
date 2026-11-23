import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory

universe u

noncomputable section

variable {X : Scheme.{u}}

def tensorBasisMap (M L : X.Modules) {U : X.Opens} (s : ((preMod X).obj L).obj (op U))
    {V : X.Opens} (h : V ≤ U) : Γ(M, V) →+ Γ(M ⊗ L, V) where
  toFun m := (tensorToSheaf M L).app (op V)
    ((show ((preMod X).obj M).obj (op V) from m) ⊗ₜ resM ((preMod X).obj L) h s :
      ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V))
  map_zero' := by
    change (tensorToSheaf M L).app (op V) ((0 : ((preMod X).obj M).obj (op V)) ⊗ₜ
      resM ((preMod X).obj L) h s : ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V)) = 0
    rw [TensorProduct.zero_tmul]
    exact map_zero _
  map_add' m m' := by
    change (tensorToSheaf M L).app (op V) (((show ((preMod X).obj M).obj (op V) from m) +
      (show ((preMod X).obj M).obj (op V) from m')) ⊗ₜ resM ((preMod X).obj L) h s :
        ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V)) = _
    rw [TensorProduct.add_tmul]
    exact map_add _ _ _

variable {M M' L : X.Modules} {U V : X.Opens} {s : ((preMod X).obj L).obj (op U)}

lemma tensorBasisMap_apply (h : V ≤ U) (m : Γ(M, V)) :
    tensorBasisMap M L s h m = (tensorToSheaf M L).app (op V)
      ((show ((preMod X).obj M).obj (op V) from m) ⊗ₜ resM ((preMod X).obj L) h s :
        ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V)) := rfl

lemma resF_resF_of_le (F : X.Modules) {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (m : Γ(F, U)) :
    resF F i (resF F h m) = resF F (i.trans h) m := by
  change (F.presheaf.map (homOfLE h).op ≫ F.presheaf.map (homOfLE i).op) m = _
  rw [← Functor.map_comp]
  rfl

lemma tmul_basis_bijective {P Q : PMod X} {s : Q.obj (op U)} (hs : IsBasisOn Q U s)
    (h : V ≤ U) :
    Function.Bijective (fun m : P.obj (op V) => (m ⊗ₜ resM Q h s : (P ⊗ Q).obj (op V))) := by
  let eQ := LinearEquiv.ofBijective (LinearMap.toSpanSingleton (ringOn X V) _ (resM Q h s))
    (hs V h)
  let E := (TensorProduct.rid (ringOn X V) (P.obj (op V))).symm ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl _ _) eQ
  have hE : (fun m : P.obj (op V) => (m ⊗ₜ resM Q h s : (P ⊗ Q).obj (op V))) = E := by
    funext m
    change m ⊗ₜ resM Q h s = m ⊗ₜ ((1 : ringOn X V) • resM Q h s)
    rw [one_smul]
  rw [hE]
  exact E.bijective

lemma tensorBasisMap_smul (h : V ≤ U) (r : Γ(X, V)) (m : Γ(M, V)) :
    tensorBasisMap M L s h (r • m) = r • tensorBasisMap M L s h m := by
  rw [tensorBasisMap_apply, tensorBasisMap_apply]
  have e : ((show ((preMod X).obj M).obj (op V) from r • m) ⊗ₜ resM ((preMod X).obj L) h s :
      ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V)) =
      (show ringOn X V from r) • ((show ((preMod X).obj M).obj (op V) from m) ⊗ₜ
        resM ((preMod X).obj L) h s : ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V)) := by
    rw [TensorProduct.smul_tmul']
    rfl
  rw [e]
  exact app_smul _ _ _

lemma tensorBasisMap_res (h : V ≤ U) {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, V)) :
    resF (M ⊗ L) hWV (tensorBasisMap M L s h m) =
      tensorBasisMap M L s (hWV.trans h) (resF M hWV m) := by
  rw [tensorBasisMap_apply, tensorBasisMap_apply]
  have := (app_resM (tensorToSheaf M L) hWV
    ((show ((preMod X).obj M).obj (op V) from m) ⊗ₜ resM ((preMod X).obj L) h s :
      ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V))).symm
  refine this.trans ?_
  congr 1
  change resM _ hWV m ⊗ₜ resM _ hWV (resM _ h s) = _
  rw [resM_resM]
  rfl

lemma tensorBasisMap_change {U' : X.Opens} (s' : ((preMod X).obj L).obj (op U')) (h : V ≤ U)
    (h' : V ≤ U') (c : ringOn X V) (hc : resM ((preMod X).obj L) h' s' = c • resM ((preMod X).obj L) h s)
    (m : Γ(M, V)) : tensorBasisMap M L s' h' m = tensorBasisMap M L s h ((show Γ(X, V) from c) • m) := by
  rw [tensorBasisMap_apply, tensorBasisMap_apply, hc]
  congr 1
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rfl

theorem tensorBasisMap_bijective (hs : IsBasisOn ((preMod X).obj L) U s) (h : V ≤ U) :
    Function.Bijective (tensorBasisMap M L s h) := by
  obtain ⟨hinj, hsurj⟩ := (ModulesTensor.W_toPresheaf_iff (tensorToSheaf M L)).1
    (W_tensorToSheaf M L)
  have inj : ∀ (W : X.Opens) (hW : W ≤ U) (m : Γ(M, W)), tensorBasisMap M L s hW m = 0 → m = 0 := by
    intro W hW m hm
    have hz := hinj (op W) _ hm
    apply sheaf_eq_of_locally ⟨M.presheaf, M.isSheaf⟩ (V := W) m 0
    intro x hx
    obtain ⟨W', f, hf, hxW'⟩ := hz x hx
    refine ⟨W', f.le, hxW', ?_⟩
    have hf' : ((show ((preMod X).obj M).obj (op W') from resF M f.le m) ⊗ₜ
        resM ((preMod X).obj L) (f.le.trans hW) s :
          ((preMod X).obj M ⊗ (preMod X).obj L).obj (op W')) = 0 := by
      rw [← resM_resM _ hW f.le]
      exact hf
    have := (tmul_basis_bijective (P := (preMod X).obj M) hs (f.le.trans hW)).1
      (a₁ := resF M f.le m) (a₂ := 0) (by
        simp only
        rw [TensorProduct.zero_tmul]
        exact hf')
    change resF M f.le m = resF M f.le 0
    exact this.trans (map_zero _).symm
  constructor
  · rw [injective_iff_map_eq_zero]
    exact inj V h
  · intro y
    have hσ := hsurj (op V) y
    choose W f hf hxW using hσ
    choose p hp using hf
    have hWU : ∀ x hx, W x hx ≤ U := fun x hx => (f x hx).le.trans h
    choose m hm using fun x hx =>
      (tmul_basis_bijective (P := (preMod X).obj M) hs (hWU x hx)).2 (p x hx)
    have key : ∀ x hx, tensorBasisMap M L s (hWU x hx) (show Γ(M, W x hx) from m x hx) =
        resF (M ⊗ L) (f x hx).le y := by
      intro x hx
      rw [tensorBasisMap_apply]
      have e : ((show ((preMod X).obj M).obj (op (W x hx)) from m x hx) ⊗ₜ
          resM ((preMod X).obj L) (hWU x hx) s :
            ((preMod X).obj M ⊗ (preMod X).obj L).obj (op (W x hx))) = p x hx := hm x hx
      rw [e]
      exact hp x hx
    obtain ⟨g, hg⟩ := sheaf_exists_glue ⟨M.presheaf, M.isSheaf⟩ (V := V) (ι := {x : X // x ∈ V})
      (fun a => W a.1 a.2) (fun a => (f a.1 a.2).le) (fun x hx => ⟨⟨x, hx⟩, hxW x hx⟩)
      (fun a => m a.1 a.2) (by
        intro a b
        have hab : W a.1 a.2 ⊓ W b.1 b.2 ≤ U := inf_le_left.trans (hWU _ _)
        change resF M inf_le_left (m a.1 a.2) = resF M inf_le_right (m b.1 b.2)
        rw [← sub_eq_zero]
        apply inj _ hab
        rw [map_sub, sub_eq_zero]
        have ea := tensorBasisMap_res (M := M) (s := s) (hWU a.1 a.2)
          (inf_le_left : W a.1 a.2 ⊓ W b.1 b.2 ≤ W a.1 a.2) (m a.1 a.2)
        have eb := tensorBasisMap_res (M := M) (s := s) (hWU b.1 b.2)
          (inf_le_right : W a.1 a.2 ⊓ W b.1 b.2 ≤ W b.1 b.2) (m b.1 b.2)
        rw [← ea, ← eb, key, key, resF_resF_of_le, resF_resF_of_le])
    refine ⟨g, ?_⟩
    apply sheaf_eq_of_locally ⟨(M ⊗ L).presheaf, (M ⊗ L).isSheaf⟩ (V := V)
    intro x hx
    refine ⟨W x hx, (f x hx).le, hxW x hx, ?_⟩
    change resF (M ⊗ L) (f x hx).le (tensorBasisMap M L s h g) = resF (M ⊗ L) (f x hx).le y
    rw [tensorBasisMap_res, ← key x hx]
    congr 1
    exact hg ⟨x, hx⟩

section General

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G) [IsIso adj.counit]

abbrev counitTensor (a b : D) : F.obj (G.obj a ⊗ G.obj b) ⟶ a ⊗ b :=
  ((Functor.Monoidal.μIso F (G.obj a) (G.obj b)).symm ≪≫
    (asIso (adj.counit.app a) ⊗ᵢ asIso (adj.counit.app b))).hom

end General

def tensorDualIso (hL : IsInvertibleSheaf L) : L ⊗ dualSheaf L ≅ 𝟙_ X.Modules :=
  β_ L (dualSheaf L) ≪≫ @asIso _ _ _ _ (dualEval L) (isIso_dualEval hL)

def dualTensorIso (hL : IsInvertibleSheaf L) : dualSheaf L ⊗ L ≅ 𝟙_ X.Modules :=
  @asIso _ _ _ _ (dualEval L) (isIso_dualEval hL)

def tensorEquivOfInvertible (hL : IsInvertibleSheaf L) : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight (dualSheaf L))
    (NatIso.ofComponents (fun M => (ρ_ M).symm ≪≫ whiskerLeftIso M (tensorDualIso hL).symm ≪≫
      (α_ M L (dualSheaf L)).symm) (by
        intro M N f
        simp
        rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
          associator_inv_naturality_left]))
    (NatIso.ofComponents (fun M => α_ M (dualSheaf L) L ≪≫ whiskerLeftIso M (dualTensorIso hL) ≪≫
      ρ_ M) (by
        intro M N f
        simp
        rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]))

lemma tensorEquivOfInvertible_functor (hL : IsInvertibleSheaf L) :
    (tensorEquivOfInvertible hL).functor = tensorRight L := rfl

theorem shortExact_tensorEquiv (hL : IsInvertibleSheaf L) {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (tensorEquivOfInvertible hL).functor).ShortExact :=
  hS.map_of_exact _

lemma exists_affineCover_basis (hL : IsInvertibleSheaf L) :
    ∃ (V : X → X.Opens) (s : ∀ x, ((preMod X).obj L).obj (op (V x))),
      (∀ x, IsAffineOpen (V x)) ∧ (∀ x, x ∈ V x) ∧
        ∀ x, IsBasisOn ((preMod X).obj L) (V x) (s x) := by
  have key : ∀ x : X, ∃ (W : X.Opens) (t : ((preMod X).obj L).obj (op W)),
      IsAffineOpen W ∧ x ∈ W ∧ IsBasisOn ((preMod X).obj L) W t := by
    intro x
    obtain ⟨U, hxU, t, ht⟩ := hL x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (U : Set X) from hxU) U.2
    exact ⟨W, resM _ hWU t, hW, hxW, ht.restrict hWU⟩
  choose V s hV hx hs using key
  exact ⟨V, s, hV, hx, hs⟩

lemma iSup_eq_top_of_self_mem {V : X → X.Opens} (hx : ∀ x, x ∈ V x) : iSup V = ⊤ :=
  eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩

theorem isQuasicoherent_tensor_of_invertible (M : X.Modules) [M.IsQuasicoherent]
    (hL : IsInvertibleSheaf L) : (M ⊗ L).IsQuasicoherent := by
  obtain ⟨V, s, hV, hx, hs⟩ := exists_affineCover_basis hL
  refine isQuasicoherent_of_affineCover (M ⊗ L) V hV (iSup_eq_top_of_self_mem hx) ?_ ?_
  · intro i f m
    obtain ⟨n, rfl⟩ := (tensorBasisMap_bijective (M := M) (hs i) (X.basicOpen_le f)).2 m
    obtain ⟨e, n', hn'⟩ := qcoh_exists_res_eq M (hV i) f n
    refine ⟨e, tensorBasisMap M L (s i) le_rfl n', ?_⟩
    rw [tensorBasisMap_res, hn', tensorBasisMap_smul]
  · intro i f m hm
    obtain ⟨n, rfl⟩ := (tensorBasisMap_bijective (M := M) (hs i) (le_refl (V i))).2 m
    rw [tensorBasisMap_res] at hm
    have hn : resF M (X.basicOpen_le f) n = 0 :=
      (injective_iff_map_eq_zero _).1 (tensorBasisMap_bijective (M := M) (hs i) _).1 _ hm
    obtain ⟨e, he⟩ := qcoh_exists_pow_smul_eq_zero M (hV i) f n hn
    exact ⟨e, by rw [← tensorBasisMap_smul, he, map_zero]⟩

theorem isCoherent_tensor_of_invertible {M : X.Modules} (hM : IsCoherent M)
    (hL : IsInvertibleSheaf L) : IsCoherent (M ⊗ L) := by
  have := hM.1
  have := isQuasicoherent_tensor_of_invertible M hL
  obtain ⟨V, s, hV, hx, hs⟩ := exists_affineCover_basis hL
  refine isCoherent_of_affineCover (M ⊗ L) V hV (iSup_eq_top_of_self_mem hx) fun i => ?_
  have := hM.2 (V i) (hV i)
  let e : Γ(M, V i) →ₗ[Γ(X, V i)] Γ(M ⊗ L, V i) :=
    { toFun := tensorBasisMap M L (s i) le_rfl
      map_add' := map_add _
      map_smul' := tensorBasisMap_smul le_rfl }
  exact Module.Finite.of_surjective e (tensorBasisMap_bijective (hs i) le_rfl).2

end

end GroundTheory.Arith.SchemeCoh
