import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier
open GlobalTheory.TrueGeo.SmallSec (fnMap fnMap_fnOf)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)

namespace GlobalTheory.CorankOne

theorem fnMap_fnOf_appLE {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {U : X.Opens} {V : Y.Opens} (e : V ≤ j ⁻¹ᵁ U)
    (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ V) (s : Γ(X, U)) :
    fnMap j hη (fnOf U h s) = fnOf V h' ((j.appLE U V e).hom s) := by
  rw [fnMap_fnOf j hη h (e h'), ← fnOf_resG e h']
  rfl

theorem exists_modification_sections {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) {U : X.Opens} (hU : genericPoint X ∈ U) {N : ℕ} (r : Fin (N + 1) → Γ(X, U))
    (i₀ : Fin (N + 1)) (hr : r i₀ = 1) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y) (hη : ρ (genericPoint Y) = genericPoint X),
      IsArithVar (ρ ≫ p) D ∧ ρ.residueDegree (genericPoint Y) ≠ 0 ∧
      ∀ y : Y, ∃ i, fnOf U hU (r i) ≠ 0 ∧ ∀ j, ∃ g, RegAt y g ∧
        g * fnMap ρ (specializes_of_eq hη) (fnOf U hU (r i)) = fnMap ρ (specializes_of_eq hη) (fnOf U hU (r j)) := by
  have := h.isNoetherian
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  have hP : IsProjOver (PSpace.str k N) := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  have : IsProper (PSpace.str k N) := CommonModel.isProper_of_isProjOver hP
  have : IsDominant U.ι := ⟨(dense_iff_closure_eq.2 (genericPoint_spec X)).mono
    (Set.singleton_subset_iff.2 ⟨_, genericPoint_eq_of_isOpenImmersion U.ι⟩)⟩
  have w := (ProjSpace.ofCoords_str p U i₀ r).symm
  obtain ⟨Y, ρ, q, c, _, _, _, _, hc₁, hc₂, hproj⟩ : ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (q : Y ⟶ PSpace k N)
      (c : U.toScheme ⟶ Y) (_ : IsIntegral Y) (_ : IsOpenImmersion c) (_ : IsProper ρ) (_ : Surjective ρ),
      c ≫ ρ = U.ι ∧ c ≫ q = ProjSpace.ofCoords p U i₀ r ∧ IsProjOver (ρ ≫ p) := by
    refine ⟨graphClosure p _ U.ι _ w, graphClosure.fst _ _ _ _ _, graphClosure.snd _ _ _ _ _,
      graphClosure.incl _ _ _ _ _, inferInstance, inferInstance, inferInstance, inferInstance,
      graphClosure.incl_fst _ _ _ _ _, graphClosure.incl_snd _ _ _ _ _, ?_⟩
    obtain ⟨M, j, _, hj⟩ := ProjSpace.isProjOver_pullback h.isProjOver hP
    exact ⟨M, graphClosure.ι _ _ _ _ w ≫ j, inferInstance, by
      rw [Category.assoc, hj, ← graphClosure.ι_fst, Category.assoc]⟩
  have hcη : c (genericPoint U) = genericPoint Y := genericPoint_eq_of_isOpenImmersion c
  have hη : ρ (genericPoint Y) = genericPoint X := by
    rw [← hcη, ← Scheme.Hom.comp_apply, hc₁]
    exact genericPoint_eq_of_isOpenImmersion U.ι
  have hdeg : ρ.residueDegree (genericPoint Y) ≠ 0 := by
    have e := CurveDegreesCompare.residueDegree_comp c ρ (genericPoint U)
    rw [hc₁, CurveDegreesCompare.residueDegree_of_isOpenImmersion, hcη] at e
    exact left_ne_zero_of_mul_eq_one e.symm
  have hch : CharZero Γ(Y, ⊤) := by
    have := h.charZero
    refine charZero_of_injective_ringHom (f := (ρ.appLE ⊤ ⊤ le_rfl).hom) fun a b e => ?_
    apply fnOf_injective ⊤ trivial
    apply (fnMap ρ (specializes_of_eq hη)).injective
    rw [fnMap_fnOf_appLE ρ _ (U := ⊤) (V := ⊤) le_rfl trivial trivial,
      fnMap_fnOf_appLE ρ _ (U := ⊤) (V := ⊤) le_rfl trivial trivial, e]
  refine ⟨Y, ρ, inferInstance, hη, ⟨h.1, h.2, inferInstance, hproj, (flat_int_iff_charZero _).2 hch,
    le_antisymm ((ProperCover.dim_le_of_residueDegree_pos ρ hη (Nat.pos_of_ne_zero hdeg)).trans h.dim_eq.le)
      (h.dim_eq.ge.trans (PosBaseChange.dim_le_of_isClosedMap ρ.isClosedMap ρ.surjective))⟩, hdeg, fun y => ?_⟩
  have h₁ : ⊤ ≤ (c ≫ q) ⁻¹ᵁ ProjSpace.chart k N i₀ := hc₂ ▸ ProjSpace.ofCoords_preimage_top p U i₀ r
  have hV : genericPoint Y ∈ q ⁻¹ᵁ ProjSpace.chart k N i₀ := hcη ▸ h₁ (Set.mem_univ (genericPoint U))
  have key (j) : fnOf _ hV (ProjSpace.pullRatio q _ i₀ le_rfl j) =
      fnMap ρ (specializes_of_eq hη) (fnOf U hU (r j)) := by
    have h₂ : ⊤ ≤ c ⁻¹ᵁ ρ ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, hc₁]; exact U.ι_preimage_self.ge
    have h₃ : ⊤ ≤ c ⁻¹ᵁ q ⁻¹ᵁ ProjSpace.chart k N i₀ := h₁
    have hU' : genericPoint Y ∈ ρ ⁻¹ᵁ U := show ρ _ ∈ U from hη ▸ hU
    apply (fnMap c (specializes_of_eq hcη)).injective
    rw [fnMap_fnOf_appLE ρ _ le_rfl hU hU',
      fnMap_fnOf_appLE c _ (V := ⊤) h₃ hV trivial,
      fnMap_fnOf_appLE c _ (V := ⊤) h₂ hU' trivial, ProjSpace.appLE_pullRatio, ProjSpace.appLE_appLE]
    congr 1
    have e₁ : c ≫ q = 𝟙 _ ≫ ProjSpace.ofCoords p U i₀ r := by rw [hc₂, Category.id_comp]
    have e₂ : c ≫ ρ = 𝟙 _ ≫ U.ι := by rw [hc₁, Category.id_comp]
    rw [ProjSpace.pullRatio_of_eq e₁ _ (e₁ ▸ h₁), ProjSpace.appLE_of_eq e₂ _ _ _ (e₂ ▸ h₂)]
    exact ProjSpace.pullRatio_comp_ofCoords p U i₀ hr _ _ _ _ j
  obtain ⟨a, ha⟩ := ProjSpace.exists_mem_chart k N (q y)
  have hy : y ∈ q ⁻¹ᵁ ProjSpace.chart k N a := ha
  have hW := memInf hV (gen_mem hy)
  have mul (i j l : Fin (N + 1)) (hi : _ ≤ q ⁻¹ᵁ ProjSpace.chart k N i) (hj : _ ≤ q ⁻¹ᵁ ProjSpace.chart k N j) :=
    congrArg (fnOf _ hW) (ProjSpace.pullRatio_mul_pullRatio (φ := q) (hi := hi) (hj := hj) (k := l))
  refine ⟨a, fun h0 => ?_, fun j => ⟨_, regAt_fnOf hy (gen_mem hy) (ProjSpace.pullRatio q _ a le_rfl j), ?_⟩⟩
  · have e := mul i₀ a i₀ inf_le_left inf_le_right
    rw [ProjSpace.pullRatio_self, map_one, map_mul, ← ProjSpace.resG_pullRatio (hi := le_rfl) inf_le_left,
      fnOf_resG, key, h0, map_zero, zero_mul] at e
    exact zero_ne_one e
  · have e := mul i₀ a j inf_le_left inf_le_right
    rw [map_mul, ← ProjSpace.resG_pullRatio (hi := le_rfl) inf_le_left,
      ← ProjSpace.resG_pullRatio (hi := le_rfl) inf_le_right,
      ← ProjSpace.resG_pullRatio (hi := le_rfl) inf_le_left, fnOf_resG, fnOf_resG, fnOf_resG, key, key] at e
    rw [mul_comm, e]

theorem exists_modification {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) {A ι : Type} [Finite A] [Finite ι] (w : A → ι → X.functionField)
    (hw : ∀ α, ∃ i, w α i ≠ 0) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (_ : IsIntegral Y) (hη : ρ (genericPoint Y) = genericPoint X),
      IsArithVar (ρ ≫ p) D ∧ ρ.residueDegree (genericPoint Y) ≠ 0 ∧
      ∀ (y : Y) (α : A), ∃ i, w α i ≠ 0 ∧ ∀ j, ∃ g, RegAt y g ∧
        g * fnMap ρ (specializes_of_eq hη) (w α i) = fnMap ρ (specializes_of_eq hη) (w α j) := by
  classical
  have := Fintype.ofFinite A
  choose σ₀ hσ₀ using hw
  have : Nonempty (A → ι) := ⟨σ₀⟩
  obtain ⟨N, ⟨ε⟩⟩ : ∃ N, Nonempty (Fin (N + 1) ≃ (A → ι)) := by
    obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := A → ι)).ne'
    exact ⟨N, ⟨(Finite.equivFinOfCardEq hN).symm⟩⟩
  let P : (A → ι) → X.functionField := fun σ => ∏ α, w α (σ α)
  have hP₀ : P σ₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun α _ => hσ₀ α
  obtain ⟨U, hU, hr⟩ := InvertIdeal.exists_common_open (x := genericPoint X)
    fun i => regAt_genericPoint (P (ε i) / P σ₀)
  choose r hr using hr
  obtain ⟨Y, ρ, _, hη, h₁, h₂, h₃⟩ := exists_modification_sections h hU r (ε.symm σ₀)
    (fnOf_injective U hU (by rw [map_one]; refine (hr _).trans ?_; rw [ε.apply_symm_apply, div_self hP₀]))
  refine ⟨Y, ρ, inferInstance, hη, h₁, h₂, fun y α => ?_⟩
  obtain ⟨a, ha, hb⟩ := h₃ y
  have hr' (i) : fnOf U hU (r i) = P (ε i) / P σ₀ := hr i
  rw [hr'] at ha
  have hPa : P (ε a) ≠ 0 := left_ne_zero_of_mul (div_eq_mul_inv (P (ε a)) _ ▸ ha)
  refine ⟨ε a α, Finset.prod_ne_zero_iff.1 hPa α (Finset.mem_univ _), fun j => ?_⟩
  obtain ⟨g, hg, e⟩ := hb (ε.symm (Function.update (ε a) α j))
  refine ⟨g, hg, ?_⟩
  have e₁ : P (ε a) = w α (ε a α) * ∏ β ∈ Finset.univ.erase α, w β (ε a β) :=
    (Finset.mul_prod_erase _ (fun β => w β (ε a β)) (Finset.mem_univ α)).symm
  have e₂ : P (Function.update (ε a) α j) = w α j * ∏ β ∈ Finset.univ.erase α, w β (ε a β) := by
    refine (Finset.mul_prod_erase _ (fun β => w β (Function.update (ε a) α j β)) (Finset.mem_univ α)).symm.trans ?_
    rw [Function.update_self]
    exact congrArg _ (Finset.prod_congr rfl fun β hβ => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hβ)])
  rw [e₁, mul_div_assoc] at ha
  rw [hr', hr', ε.apply_symm_apply, e₁, e₂, mul_div_assoc, mul_div_assoc, map_mul, map_mul, ← mul_assoc] at e
  exact mul_right_cancel₀ ((map_ne_zero _).2 (right_ne_zero_of_mul ha)) e

theorem isVB_cokernel_ofGeneric {Y : Scheme.{0}} [IsIntegral Y] {F : Y.Modules} [F.IsQuasicoherent] {ι : Type}
    [Fintype ι] (φ : genStalk F →ₗ[Y.functionField] Y.functionField)
    (H : ∀ y : Y, ∃ (U : Y.Opens) (hy : y ∈ U) (e : ι → Γ(F, U)) (i : ι), IsFrame e ∧
      φ (F.presheaf.germ U _ (gen_mem hy) (e i)) ≠ 0 ∧ ∀ j, ∃ g, RegAt y g ∧
        g * φ (F.presheaf.germ U _ (gen_mem hy) (e i)) = φ (F.presheaf.germ U _ (gen_mem hy) (e j))) :
    IsVB (cokernel (Sub.ofGeneric (LinearMap.ker φ)).incl) 1 := by
  intro y
  obtain ⟨U, hy, e, i, he, hi, hg⟩ := H y
  choose g hg hg' using hg
  obtain ⟨W, hW, c⟩ := InvertIdeal.exists_common_open hg
  choose c hc using c
  let N := Sub.ofGeneric (LinearMap.ker φ)
  let π := cokernel.π N.incl
  refine ⟨U ⊓ W, fun _ => π.app _ (resM F inf_le_left (e i)), ⟨hy, hW⟩,
    isFrame_of_forall_exists fun V hV x hx => ?_⟩
  obtain ⟨T, hT, hxT, hle⟩ := QCoh.exists_affine_mem_le x hx
  have hTU : T ≤ U := (hle.trans hV).trans inf_le_left
  have hTW : T ≤ W := (hle.trans hV).trans inf_le_right
  have lc (a : Fin 1 → Γ(Y, T)) : Fintype.linearCombination Γ(Y, T)
      (fun _ : Fin 1 => resM (cokernel N.incl) (hle.trans hV) (π.app _ (resM F inf_le_left (e i)))) a =
      π.app T (a 0 • resM F hTU (e i)) := by
    rw [Fintype.linearCombination_apply, Fin.sum_univ_one, ← app_resM, resM_resM, Scheme.Modules.Hom.app_smul]
  have val (a : Γ(Y, T)) (j : ι) : φ (F.presheaf.germ T _ (gen_mem hxT) (a • resM F hTU (e j))) =
      fnOf T (gen_mem hxT) a * φ (F.presheaf.germ U _ (gen_mem hy) (e j)) := by
    rw [QCoh.germ_smul, germ_resM]
    exact φ.map_smul _ _
  refine ⟨T, hle, hxT, (injective_iff_map_eq_zero _).2 fun a ha => ?_, fun s => ?_⟩
  · rw [lc, N.cokernel_π_app_eq_zero_iff] at ha
    have h0 := (val _ _).symm.trans (ha (gen_mem hxT))
    funext l
    obtain rfl : l = 0 := Subsingleton.elim _ _
    exact fnOf_injective T (gen_mem hxT) (((mul_eq_zero.1 h0).resolve_right hi).trans (map_zero _).symm)
  · obtain ⟨t, rfl⟩ := QCoh.surjective_app_of_epi π hT s
    obtain ⟨a, rfl⟩ := (he T hTU).2 t
    refine ⟨fun _ => ∑ j, a j * resG Y hTW (c j), ?_⟩
    rw [lc, ← sub_eq_zero, ← map_sub, N.cokernel_π_app_eq_zero_iff]
    intro hη
    rw [LinearMap.mem_ker, map_sub, map_sub, val, Fintype.linearCombination_apply, map_sum, map_sum, map_sum,
      Finset.sum_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [val, map_mul, fnOf_resG, hc, mul_assoc, hg']

theorem coord_pullback {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (ρ : Y ⟶ X)
    (hη : ρ (genericPoint Y) = genericPoint X) {E : X.Modules} [E.IsQuasicoherent] {ι : Type} [Fintype ι]
    {U : X.Opens} (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ ρ ⁻¹ᵁ U) {e : ι → Γ(E, U)} (he : IsFrame e)
    (i : ι) {V : X.Opens} (hV : genericPoint X ∈ V) (hV' : genericPoint Y ∈ ρ ⁻¹ᵁ V) (s : Γ(E, V)) :
    ((he.pullback ρ).stalkBasis _ hU').coord i (((Scheme.Modules.pullback ρ).obj E).presheaf.germ _ _ hV'
      (QCoh.pullbackSections ρ E (le_refl (ρ ⁻¹ᵁ V)) s)) =
      fnMap ρ (specializes_of_eq hη) ((he.stalkBasis _ hU).coord i (E.presheaf.germ V _ hV s)) := by
  classical
  have hT := memInf hU hV
  have hT' : genericPoint Y ∈ ρ ⁻¹ᵁ (U ⊓ V) := ⟨hU', hV'⟩
  obtain ⟨a, ha⟩ := (he (U ⊓ V) inf_le_left).2 (resM E inf_le_right s)
  rw [Fintype.linearCombination_apply] at ha
  have e₁ : E.presheaf.germ V _ hV s = ∑ j, X.presheaf.germ _ _ hT (a j) • he.stalkBasis _ hU j := by
    rw [← germ_resM (inf_le_right : U ⊓ V ≤ V) hT, ← ha]
    simp only [map_sum, QCoh.germ_smul, germ_resM, IsFrame.stalkBasis_apply]
  have pr {T : X.Opens} (h : U ⊓ V ≤ T) (t : Γ(E, T)) :
      QCoh.pullbackSections ρ E (le_refl (ρ ⁻¹ᵁ (U ⊓ V))) (resM E h t) =
        resM _ (ρ.preimage_mono h) (QCoh.pullbackSections ρ E (le_refl (ρ ⁻¹ᵁ T)) t) :=
    (QCoh.pullbackSections_res ρ E _ h t).trans (QCoh.res_pullbackSections ρ E _ _ t).symm
  have e₂ : ((Scheme.Modules.pullback ρ).obj E).presheaf.germ _ _ hV'
      (QCoh.pullbackSections ρ E (le_refl (ρ ⁻¹ᵁ V)) s) =
      ∑ j, Y.presheaf.germ _ _ hT' (ρ.appLE _ _ le_rfl (a j)) • (he.pullback ρ).stalkBasis _ hU' j := by
    rw [← germ_resM (ρ.preimage_mono (inf_le_right : U ⊓ V ≤ V)) hT', ← pr inf_le_right, ← ha, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [QCoh.pullbackSections_smul, QCoh.germ_smul, pr, germ_resM, IsFrame.stalkBasis_apply]
  rw [e₁, e₂, Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_sum_self,
    Module.Basis.repr_sum_self]
  exact (fnMap_fnOf_appLE ρ _ le_rfl hT hT' (a i)).symm

theorem exists_modification_subbundle {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    {E : X.Modules} {r : ℕ} (h : IsArithVar p D) (hE : IsVB E (r + 1)) :
    ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (K : Y.Modules) (i : K ⟶ (Scheme.Modules.pullback ρ).obj E),
      IsArithVar (ρ ≫ p) D ∧ (∀ [IsIntegral Y] [IsIntegral X], ρ (genericPoint Y) = genericPoint X ∧
        ρ.residueDegree (genericPoint Y) ≠ 0) ∧ IsSubbundle i ∧ IsVB K r := by
  have := h.isIntegral
  have := h.isNoetherian
  have := hE.isQuasicoherent
  choose U e hx he using id hE
  obtain ⟨T, hT⟩ := exists_finset_iSup_eq_top U hx
  let φ := ((he _).stalkBasis _ (hx (genericPoint X))).coord 0
  have hφ : φ ≠ 0 := fun h0 => by
    have := LinearMap.congr_fun h0 ((he _).stalkBasis _ (hx (genericPoint X)) 0)
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same] at this
    exact one_ne_zero this
  obtain ⟨Y, ρ, _, hη, h₁, h₂, h₃⟩ := exists_modification h
    (fun (α : T) j => φ (E.presheaf.germ _ _ (gen_mem (hx α)) (e α j))) fun α => by
      by_contra! H
      exact hφ (((he α).stalkBasis _ (gen_mem (hx α))).ext fun j => by
        rw [IsFrame.stalkBasis_apply]; exact H j)
  have hF := hE.pullback ρ
  have := hF.isQuasicoherent
  have hU' : genericPoint Y ∈ ρ ⁻¹ᵁ U (genericPoint X) := show ρ _ ∈ U _ from hη ▸ hx _
  let ψ := (((he _).pullback ρ).stalkBasis _ hU').coord 0
  have hQ := isVB_cokernel_ofGeneric (F := (Scheme.Modules.pullback ρ).obj E) ψ fun y => by
    obtain ⟨α, hα⟩ := Opens.mem_iSup.1 (hT.ge (Set.mem_univ (ρ y)))
    obtain ⟨i, hi, hj⟩ := h₃ y α
    have hy : y ∈ ρ ⁻¹ᵁ U α := hα
    have c (j) := coord_pullback ρ hη (hx _) hU' (he _) 0 (gen_mem (hx α)) (gen_mem hy) (e α j)
    refine ⟨_, hy, _, i, (he α).pullback ρ, fun h0 => hi ?_, fun j => ?_⟩
    · exact (map_eq_zero _).1 ((c i).symm.trans h0)
    · obtain ⟨g, hg, e⟩ := hj j
      exact ⟨g, hg, ((congrArg (g * ·) (c i)).trans e).trans (c j).symm⟩
  have hS : (ShortComplex.mk _ (cokernel.π (Sub.ofGeneric (LinearMap.ker ψ)).incl)
      (cokernel.condition _)).ShortExact := { exact := ShortComplex.exact_cokernel _ }
  exact ⟨Y, ρ, _, (Sub.ofGeneric (LinearMap.ker ψ)).incl, h₁, ⟨hη, h₂⟩, ⟨inferInstance, 1, hQ⟩,
    isVB_X₁_of_shortExact Y _ r 1 hS hF hQ⟩

theorem exists_modification_subbundle_surface : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (E : X.Modules) (r : ℕ), IsArithVar p 1 → IsVB E (r + 1) → ∃ (Y : Scheme.{0}) (ρ : Y ⟶ X) (K : Y.Modules)
      (i : K ⟶ (Scheme.Modules.pullback ρ).obj E), IsArithVar (ρ ≫ p) 1 ∧ (∀ [IsIntegral Y] [IsIntegral X],
        ρ (genericPoint Y) = genericPoint X ∧ ρ.residueDegree (genericPoint Y) ≠ 0) ∧ IsSubbundle i ∧ IsVB K r :=
  fun _ _ _ _ _ _ h hE => exists_modification_subbundle h hE

end GlobalTheory.CorankOne
