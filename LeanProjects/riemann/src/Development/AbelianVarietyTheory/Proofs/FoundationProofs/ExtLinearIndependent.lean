import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlaceExtensionValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoeffExtRationalFormsValuesField

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues (IsCoefExt RationalValues RationalValuesAt ValuesIn)
open GlobalTheory.Proof.PlaceExtensionValues

namespace GlobalTheory.RationalValuesObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' c'' : VV K' lam →ₛₗ[σ'] W}

theorem exists_basis_val (lam : I → DomWeight n) (ι : K →+* K') (j : VVIdx lam) :
    ∃ v : VV K lam, ((bVV K' lam j : VV K' lam) : Pol K' I n) = MvPolynomial.map ι (v : Pol K I n) := by
  obtain ⟨F, hF, hj⟩ := GlobalTheory.Proof.TensorMapDescent.bVVfun_desc ι lam j
  exact ⟨⟨F, hF⟩, (bVV_coe _ _ _).trans hj⟩

theorem ext_unique (h : IsCoefExt ι lam c₀ c') (h' : IsCoefExt ι lam c₀ c'') : c' = c'' := by
  refine (bVV K' lam).ext fun j => ?_
  obtain ⟨v, hv⟩ := exists_basis_val lam ι j
  rw [h v _ hv, h' v _ hv]

theorem apply_eq_sum [Fintype (VVIdx lam)] (c' : VV K' lam →ₛₗ[σ'] W) (v : VV K' lam) :
    c' v = ∑ j, σ' ((bVV K' lam).repr v j) • c' (bVV K' lam j) := by
  conv_lhs => rw [← (bVV K' lam).sum_repr v, map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smulₛₗ _ _ _

theorem ext_linearIndependent (h : IsCoefExt ι lam c₀ c') (hli : LinearIndependent ℂ fun j => c₀ (bVV K lam j)) :
    LinearIndependent ℂ fun j => c' (bVV K' lam j) := by
  classical
  rw [linearIndependent_iff_card_le_finrank_span] at hli ⊢
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun j => c' (bVV K' lam j))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  refine hli.trans (Submodule.finrank_mono (Submodule.span_le.2 ?_))
  rintro _ ⟨j, rfl⟩
  obtain ⟨v', hv'⟩ := exists_ext_val h (bVV K lam j)
  show c₀ (bVV K lam j) ∈ Submodule.span ℂ (Set.range fun j => c' (bVV K' lam j))
  rw [← hv', apply_eq_sum c' v']
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem ext_injective (h : IsCoefExt ι lam c₀ c') (hli : LinearIndependent ℂ fun j => c₀ (bVV K lam j)) :
    Function.Injective c' := by
  classical
  refine (injective_iff_map_eq_zero c').2 fun v hv => ?_
  rw [apply_eq_sum c' v] at hv
  have h1 := Fintype.linearIndependent_iff.1 (ext_linearIndependent h hli) _ hv
  exact (bVV K' lam).forall_coord_eq_zero_iff.1 fun j => (map_eq_zero σ').1 (h1 j)

end Coef

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem placeEx_of_pins (hL : R.toLevCh.Is A.μ0) (hG : R.IsGrp F) (hF : R.IsFam) (hM : R.IsModels) (i : Fin D.R.m)
    {K' : Type} [Field K'] {jL : D.what₂.LL →+* K'} {σ' : K' →+* ℂ} {c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W}
    (hp : CoefPins R i jL σ' c') (t : T) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i)) : PlaceEx R i t h c' := by
  obtain ⟨-, _, _, _, hT, hc⟩ := hp
  exact GlobalTheory.RationalValues.placeEx R i jL σ' t h c' hM.jV hT hc hL hG.chiW hF.pl_onto hF.muVal

theorem exists_coefPins (hF : R.fam_tie) (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    (hσ : σ'.comp jL = D.what₂.embLL) : ∃ c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefPins R i jL σ' c' := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := hF
  obtain ⟨c', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (FWT.lamV D i) (c0L i)
  exact ⟨c', hσ, gramR, c0R, c0L, hT, hc⟩

theorem existsUnique_c0BC (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    (hσ : σ'.comp jL = D.what₂.embLL) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) :
    ∃! c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefficientBaseChange R i jL σ' c₀ c' := by
  obtain ⟨c', hc⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R.cV i).W) jL σ' hσ (FWT.lamV D i) c₀
  exact ⟨c', hc, fun c'' hc'' => ext_unique ((isCoefExt_iff_c0BC R i jL c₀ c'').2 hc'') ((isCoefExt_iff_c0BC R i jL c₀ c').2 hc)⟩

theorem injective_of_pins (i : Fin D.R.m) {K' : Type} [Field K'] {jL : D.what₂.LL →+* K'} {σ' : K' →+* ℂ}
    {c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W} (hp : CoefPins R i jL σ' c') : Function.Injective c' := by
  obtain ⟨-, _, _, c0L, hT, hc⟩ := hp
  have hli : LinearIndependent ℂ fun j => (c0L i (bVV D.what₂.LL (FWT.lamV D i) j) : (R.cV i).W) := (hT.mapL i).2.1
  exact ext_injective (W := (R.cV i).W) (c₀ := c0L i) (lam := FWT.lamV D i) ((isCoefExt_iff_c0BC R i jL (c0L i) c').2 hc) hli

theorem place_unique (i : Fin D.R.m) {K' : Type} [Field K'] {jL : D.what₂.LL →+* K'} {σ' : K' →+* ℂ}
    {c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W} (hp : CoefPins R i jL σ' c') (t : T) {Cl : Type} (h : Cl → GA D (Vc D i))
    (y : (R.HV i t).H) {x x' : Cl → VsV D i K'} (hx : Place R i t h c' y x) (hx' : Place R i t h c' y x') : x = x' :=
  funext fun k => injective_of_pins R i hp ((hx k).symm.trans (hx' k))

end Row

theorem placeRow : PlaceRow :=
  fun _ _ _ _ _ _ _ _ _ _ _ R F hL hG hF hM i _ _ _ _ _ hp t _ _ h _ _ _ => placeEx_of_pins R F hL hG hF hM i hp t h

theorem rationalValues : RationalValues := rationalValues_iff.2 placeRow

theorem placeEx_on_objects :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
      R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels →
      ∀ (i : Fin D.R.m) (K' : Type) [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ), σ'.comp jL = D.what₂.embLL →
        (∃ c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefPins R i jL σ' c') ∧
        ∀ c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W, CoefPins R i jL σ' c' →
          ∀ (t : T) (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)),
            PlaceEx R i t h c' ∧ ∀ x₀ : A.fam.amb.FL i t, ∃! x, Place R i t h c' (jVx R i t x₀) x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hG hF hM i K' _ jL σ' hσ
  refine ⟨exists_coefPins R hF.tie i jL σ' hσ, fun c' hp t Cl _ h => ?_⟩
  have H := placeEx_of_pins R F hL hG hF hM i hp t h
  exact ⟨H, fun x₀ => (H x₀).imp fun x hx => ⟨hx, fun x' hx' => place_unique R i hp t h _ hx' hx⟩⟩

theorem placeEx_of_thPinsR {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F)
    (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ) {v₀ : (R.MW i (sg0 D A)).Vec}
    {c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} {M : ℕ} {Mh : Ideal (𝓞 D.host.E)} {lev : G → La →ₗ[𝓞 D.host.E] La}
    (hP : ThPinsR R i jL σ' v₀ c' ι M Mh lev) (t : T) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i)) : PlaceEx R i t h c' :=
  placeEx_of_pins R F hR.lev hR.grp hR.fam hR.models i (CoefPins.of_thPinsR R hP) t h

end GlobalTheory.RationalValuesObj

end
