import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize

open Module NumberField

noncomputable section

namespace Formalism.BasicNotions

theorem HLat.slopes_of_isom {K : Type} [Field K] [NumberField K] [StarRing K] (A B : HLat K)
    (ψ : A.V →ₗ[K] B.V) (hA : ∀ v, IsUnit (A.X v).det) (hB : ∀ v, IsUnit (B.X v).det)
    (hψ : Function.Injective ψ)
    (hn : ∀ v x, Formalism.HermitianLatticesTheory.normAt A.b A.X v x = Formalism.HermitianLatticesTheory.normAt B.b B.X v (ψ x))
    (hfg : A.L.FG) (hL : A.L.map (ψ.restrictScalars (𝓞 K)) = B.L) :
    A.mu = B.mu ∧ A.muMax = B.muMax ∧ A.muMin = B.muMin ∧ A.lcv = B.lcv ∧ A.rank = B.rank := by
  obtain ⟨h0, -, h1, h2, h3, -, -⟩ := Formalism.HN.lattice_rerealization K A.V A.ι B.V B.ι A.b A.X B.b B.X ψ hA hB hψ
    (fun v x => (hn v x).symm) A.L hfg
  rw [hL] at h0 h1 h2 h3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold HLat.mu Formalism.HN.muDef; rw [h1]
  · unfold HLat.muMax Formalism.HN.muMaxDef; rw [h2]
  · unfold HLat.muMin Formalism.HN.muMinDef; rw [h3]
  · unfold HLat.lcv; rw [h0]
  · unfold HLat.rank Formalism.HN.rkK
    have hs : Submodule.span K (B.L : Set B.V) = (Submodule.span K (A.L : Set A.V)).map ψ := by
      rw [← hL, Submodule.map_coe, ← Submodule.span_image]
      rfl
    rw [hs]
    exact (Submodule.equivMapOfInjective ψ hψ _).finrank_eq

namespace D7

variable (D : D7)

theorem MramL_map (u : D.what₂.Word) :
    (DV.MramL D u).map ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) = (D.fm u).ramL := by
  unfold DV.MramL MemberForms.ramL
  rw [Submodule.map_comap_eq, ← D.nuIn_range u, inf_comm]
  rfl

theorem ramL_fg (u : D.what₂.Word) : (D.fm u).ramL.FG := by
  have : Module.Finite (𝓞 D.what₂.LL) ((D.fm u).lat 0).L := Module.Finite.iff_fg.2 ((D.fm u).lat_good 0).2.1
  have : IsNoetherian (𝓞 D.what₂.LL) ((D.fm u).lat 0).L := inferInstance
  have h : (D.fm u).ramL ≤ ((D.fm u).lat 0).L := inf_le_left
  have := (IsNoetherian.noetherian ((D.fm u).ramL.comap ((D.fm u).lat 0).L.subtype)).map ((D.fm u).lat 0).L.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 h] at this

theorem MramL_fg (u : D.what₂.Word) : (DV.MramL D u).FG := by
  have h := D.ramL_fg u
  rw [← D.MramL_map u] at h
  exact Submodule.fg_of_fg_map_injective ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) (D.nuIn_inj u) h

theorem ram_slopes (u : D.what₂.Word) :
    ({ D.div.Nu u with L := DV.MramL D u } : HLat D.what₂.LL).mu = (D.fm u).ramLat.mu ∧
    ({ D.div.Nu u with L := DV.MramL D u } : HLat D.what₂.LL).muMax = (D.fm u).ramLat.muMax ∧
    ({ D.div.Nu u with L := DV.MramL D u } : HLat D.what₂.LL).muMin = (D.fm u).ramLat.muMin ∧
    ({ D.div.Nu u with L := DV.MramL D u } : HLat D.what₂.LL).lcv = (D.fm u).ramLat.lcv ∧
    ({ D.div.Nu u with L := DV.MramL D u } : HLat D.what₂.LL).rank = (D.fm u).ramLat.rank :=
  HLat.slopes_of_isom ({ D.div.Nu u with L := DV.MramL D u } : HLat D.what₂.LL) (D.fm u).ramLat (D.nuIn u)
    (D.div_good.2 u) ((D.fm u).lat_good 0).1 (D.nuIn_inj u) (D.nuIn_norm u) (D.MramL_fg u) (D.MramL_map u)

theorem RRV_finrank : finrank D.what₂.LL D.div.RR.V = D.what₂.Drows := by
  have h1 : finrank D.what₂.LL D.div.RR.V = Fintype.card D.div.RR.ι := finrank_eq_card_basis D.div.RR.b
  have h2 : finrank ℂ D.what₂.EE = Fintype.card D.div.RR.ι :=
    finrank_eq_card_basis (Basis.mk D.jEE_basis.1 (le_of_eq D.jEE_basis.2.symm))
  have h3 : finrank ℂ D.what₂.EE = D.what₂.Drows := by
    simpa using finrank_eq_card_basis D.what₂.onb.toBasis
  omega

variable {D} in

theorem RRFull.rank (h : D.RRFull) : D.div.Drows = D.what₂.Drows := by
  unfold DivData.Drows HLat.rank Formalism.HN.rkK
  rw [h.2, finrank_top]
  exact D.RRV_finrank

variable {D} in

theorem RRFull.D_eq (h : D.RRFull) : (D.div.RR.rank : ℝ) = (1 - D.div.delP) * (D.div.Dall : ℝ) := by
  have := h.rank
  unfold DivData.Drows at this
  rw [this, D.delP_eq, D.Dall_eq]
  exact D.what₂.D_eq

variable {D} in
theorem RRFull.good (h : D.RRFull) : D.div.RR.Good := ⟨D.div_good.1, h.1, h.2⟩

theorem RR_span_of_rank (h : D.div.Drows = D.what₂.Drows) :
    Submodule.span D.what₂.LL (D.div.RR.L : Set D.div.RR.V) = ⊤ := by
  have : Module.Finite D.what₂.LL D.div.RR.V := Module.Finite.of_basis D.div.RR.b
  apply Submodule.eq_top_of_finrank_eq
  rw [D.RRV_finrank]
  exact h

theorem NuV_finrank (u : D.what₂.Word) : finrank D.what₂.LL (D.div.Nu u).V = (D.mem u).A.du := by
  have h1 : finrank D.what₂.LL (D.div.Nu u).V = Fintype.card (D.div.Nu u).ι := finrank_eq_card_basis (D.div.Nu u).b
  have h2 : finrank ℂ (D.what₂.Mu u) = Fintype.card (D.div.Nu u).ι :=
    finrank_eq_card_basis (Basis.mk (D.jN_basis u).1 (le_of_eq (D.jN_basis u).2.symm))
  have h3 : finrank ℂ (D.what₂.Mu u) = (D.mem u).A.du := (D.eMu u).finrank_eq
  omega

variable {D} in

theorem NuFull.rank (h : D.NuFull) (u : D.what₂.Word) : D.div.d u = (D.mem u).A.du := by
  unfold DivData.d dU HLat.rank Formalism.HN.rkK
  rw [(h u).2, finrank_top]
  exact D.NuV_finrank u

variable {D} in
theorem NuFull.good (h : D.NuFull) (u : D.what₂.Word) : (D.div.Nu u).Good := ⟨D.div_good.2 u, (h u).1, (h u).2⟩

variable {D} in

theorem NuFull.R_eq (h : D.NuFull) : D.div.R = ∑ u, (D.mem u).A.du :=
  Finset.sum_congr rfl (fun u _ => h.rank u)

theorem Nu_span_of_rank (u : D.what₂.Word) (h : D.div.d u = (D.mem u).A.du) :
    Submodule.span D.what₂.LL ((D.div.Nu u).L : Set (D.div.Nu u).V) = ⊤ := by
  have : Module.Finite D.what₂.LL (D.div.Nu u).V := Module.Finite.of_basis (D.div.Nu u).b
  apply Submodule.eq_top_of_finrank_eq
  rw [D.NuV_finrank u]
  exact h

variable {D} in
theorem allGood (h1 : D.RRFull) (h2 : D.NuFull) : D.div.AllGood := ⟨h1.good, h2.good⟩

end D7

theorem normAt_sq_eq_majAt {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 = (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]

theorem normAt_nonneg {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) : 0 ≤ Formalism.HermitianLatticesTheory.normAt b X v x :=
  Real.sqrt_nonneg _

namespace D7

variable (D : D7)

theorem jN_norm (u : D.what₂.Word) (x : (D.div.Nu u).V) :
    Formalism.HermitianLatticesTheory.normAt (D.div.Nu u).b (D.div.Nu u).X (InfinitePlace.mk D.what₂.embLL) x = ‖D.jN u x‖ := by
  have h : Formalism.HermitianLatticesTheory.normAt (D.div.Nu u).b (D.div.Nu u).X (InfinitePlace.mk D.what₂.embLL) x ^ 2 =
      ‖D.jN u x‖ ^ 2 := by
    rw [D.nuIn_norm, normAt_sq_eq_majAt, (D.fm u).emb_norm, ← D.nuIn_jN]
    rw [← @inner_self_eq_norm_sq ℂ, D.eMu_isom]
    rfl
  exact (sq_eq_sq₀ (normAt_nonneg _ _ _ _) (norm_nonneg _)).1 h

theorem Drows_le_Dall (h : 0 < D.what₂.Dall) : D.what₂.Drows ≤ D.what₂.Dall := by
  have : Module.Finite ℂ D.s.HH := Module.finite_of_finrank_pos (by rw [D.s_HH]; exact h)
  have hli : LinearIndependent ℂ (D.sEE.toLinearMap.toAddMonoidHom ∘ D.what₂.onb) :=
    D.what₂.onb.orthonormal.linearIndependent.map_of_surjective_injectiveₛ (starRingEnd ℂ)
      D.sEE.toLinearMap.toAddMonoidHom (fun z => ⟨starRingEnd ℂ z, Complex.conj_conj z⟩) D.sEE.injective
      (fun r m => D.sEE.map_smulₛₗ r m)
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_fin, D.s_HH] at this

theorem delpNonneg (h : 0 < D.what₂.Dall) : Rows.DelpNonneg D.what₂ := by
  unfold Rows.DelpNonneg
  have h1 : (D.what₂.Drows : ℝ) ≤ (D.what₂.Dall : ℝ) := by exact_mod_cast D.Drows_le_Dall h
  have h2 : (0 : ℝ) < (D.what₂.Dall : ℝ) := by exact_mod_cast h
  rw [D.what₂.D_eq] at h1
  by_contra hc
  have hc' : D.what₂.delp < 0 := not_le.1 hc
  nlinarith

theorem delPNonneg (h : 0 < D.div.Dall) : D.div.DelPNonneg := by
  unfold DivData.DelPNonneg
  rw [D.delP_eq]
  exact D.delpNonneg (by rw [← D.Dall_eq]; exact h)

end D7

namespace FBC

open TensorProduct IsLocalRing

theorem length_tensor_loc {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime]
    (O : Type*) [CommRing O] [IsLocalRing O] [Algebra A O] [Algebra (Localization.AtPrime P) O]
    [IsScalarTower A (Localization.AtPrime P) O] [IsLocalHom (algebraMap (Localization.AtPrime P) O)]
    [Module.Flat (Localization.AtPrime P) O] (Q : Type*) [AddCommGroup Q] [Module A Q] :
    Module.length O (O ⊗[A] Q) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl Q) *
        Module.length O (O ⧸ (maximalIdeal (Localization.AtPrime P)).map (algebraMap (Localization.AtPrime P) O)) := by
  rw [← IsLocalRing.length_baseChange (Localization.AtPrime P) O (LocalizedModule P.primeCompl Q)]
  have e1 : (Localization.AtPrime P) ⊗[A] Q ≃ₗ[Localization.AtPrime P] LocalizedModule P.primeCompl Q :=
    (IsLocalizedModule.isBaseChange P.primeCompl (Localization.AtPrime P)
      (LocalizedModule.mkLinearMap P.primeCompl Q)).equiv
  have e2 : O ⊗[Localization.AtPrime P] ((Localization.AtPrime P) ⊗[A] Q) ≃ₗ[O] O ⊗[A] Q :=
    AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime P) O O Q
  have e3 : O ⊗[Localization.AtPrime P] ((Localization.AtPrime P) ⊗[A] Q) ≃ₗ[O]
      O ⊗[Localization.AtPrime P] (LocalizedModule P.primeCompl Q) := e1.baseChange _ O _ _
  exact (e2.symm.trans e3).length_eq

theorem range_liftBaseChange {A : Type*} [CommRing A] (O : Type*) [CommRing O] [Algebra A O]
    {X W : Type*} [AddCommGroup X] [Module A X] [AddCommGroup W] [Module A W] [Module O W]
    [IsScalarTower A O W] (l : X →ₗ[A] W) :
    LinearMap.range (l.liftBaseChange O) = Submodule.span O (Set.range l) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      rw [LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp⟩

theorem length_span_quot {A : Type*} [CommRing A] (O : Type*) [CommRing O] [Algebra A O]
    {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] [Module O W]
    [IsScalarTower A O W] (φ : V →ₗ[A] W) (N M : Submodule A V) (hNM : N ≤ M)
    (hinj : Function.Injective ((φ ∘ₗ M.subtype).liftBaseChange O)) :
    Module.length O (↥(Submodule.span O (φ '' (M : Set V))) ⧸
        (Submodule.span O (φ '' (N : Set V))).comap (Submodule.span O (φ '' (M : Set V))).subtype) =
      Module.length O (O ⊗[A] (↥M ⧸ N.comap M.subtype)) := by
  set PM := Submodule.span O (φ '' (M : Set V)) with hPM
  set PN := Submodule.span O (φ '' (N : Set V)) with hPN
  set Θ := (φ ∘ₗ M.subtype).liftBaseChange O with hΘ
  set N' := N.comap M.subtype with hN'
  have hr : LinearMap.range Θ = PM := by
    rw [hΘ, range_liftBaseChange, hPM]
    congr 1
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  have hle : PN ≤ PM := Submodule.span_mono (Set.image_mono hNM)
  let e : O ⊗[A] ↥M ≃ₗ[O] ↥PM := (LinearEquiv.ofInjective Θ hinj).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ t, ((e t : ↥PM) : W) = Θ t := fun t => rfl
  let q : O ⊗[A] ↥M →ₗ[O] O ⊗[A] (↥M ⧸ N') := N'.mkQ.baseChange O
  have hq : Function.Surjective q := LinearMap.baseChange_surjective O (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker q = LinearMap.range (N'.subtype.baseChange O) := by
    have hex : Function.Exact (N'.subtype.lTensor O) (N'.mkQ.lTensor O) :=
      lTensor_exact O (LinearMap.exact_subtype_mkQ N') (Submodule.mkQ_surjective _)
    ext t
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    exact hex t
  have hmap : (LinearMap.ker q).map (e : O ⊗[A] ↥M →ₗ[O] ↥PM) = PN.comap PM.subtype := by
    apply Submodule.map_injective_of_injective PM.injective_subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hle, ← Submodule.map_comp, hker, ← LinearMap.range_comp]
    have hc : (PM.subtype ∘ₗ (e : O ⊗[A] ↥M →ₗ[O] ↥PM)) ∘ₗ N'.subtype.baseChange O =
        (φ ∘ₗ M.subtype ∘ₗ N'.subtype).liftBaseChange O := by
      ext x
      simp [he, hΘ]
    rw [hc, range_liftBaseChange, hPN]
    congr 1
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨⟨x, hNM hx⟩, hx⟩, rfl⟩
  exact ((Submodule.Quotient.equiv _ _ e hmap).symm.trans (q.quotKerEquivOfSurjective hq)).length_eq

theorem injective_of_basis_li {F X Y ι : Type*} [Field F] [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (f : X →ₗ[F] Y) (b : Basis ι F X) (h : LinearIndependent F (f ∘ b)) : Function.Injective f := by
  have hf : ∀ x, f x = Finsupp.linearCombination F (f ∘ b) (b.repr x) := by
    intro x
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.apply_linearCombination]
  intro x y hxy
  rw [hf, hf] at hxy
  exact b.repr.injective (h hxy)

section Tower

variable {A K O Kf V W ι : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing O] [Algebra A O] [Field Kf] [Algebra O Kf] [Algebra K Kf]
    [Algebra A Kf] [IsScalarTower A O Kf] [IsScalarTower A K Kf]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] [Module K W] [IsScalarTower K Kf W]
    [Module A W] [IsScalarTower A O W] [IsScalarTower A K W] [IsScalarTower A Kf W]

theorem liftBaseChange_injective_top
    (hO : Function.Injective (algebraMap O Kf)) (φ : V →ₗ[K] W) (b : Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) :
    Function.Injective ((φ.restrictScalars A).liftBaseChange O) := by
  have : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  have : Module.Flat A V := Module.Flat.trans A K V
  have h2 : Function.Injective (((IsScalarTower.toAlgHom A O Kf).toLinearMap).rTensor V) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hO
  have : IsLocalizedModule (nonZeroDivisors A) (LinearMap.id : V →ₗ[A] V) :=
    isLocalizedModule_id (nonZeroDivisors A) V K
  let eV : K ⊗[A] V ≃ₗ[K] V :=
    (IsLocalizedModule.isBaseChange (nonZeroDivisors A) K (LinearMap.id : V →ₗ[A] V)).equiv
  let e : Kf ⊗[A] V ≃ₗ[Kf] Kf ⊗[K] V :=
    (AlgebraTensorModule.cancelBaseChange A K Kf Kf V).symm.trans (eV.baseChange K Kf _ _)
  have h4 : Function.Injective (φ.liftBaseChange Kf) := by
    apply injective_of_basis_li _ (b.baseChange Kf)
    convert hb using 1
    ext i
    simp
  have h3 : Function.Injective ((φ.restrictScalars A).liftBaseChange Kf) := by
    have : ((φ.restrictScalars A).liftBaseChange Kf) = (φ.liftBaseChange Kf) ∘ₗ (e : Kf ⊗[A] V →ₗ[Kf] Kf ⊗[K] V) := by
      ext x
      simp [e, eV, IsBaseChange.equiv_tmul]
    rw [this]
    exact h4.comp e.injective
  have hc : ∀ t, ((φ.restrictScalars A).liftBaseChange O) t =
      ((φ.restrictScalars A).liftBaseChange Kf) ((((IsScalarTower.toAlgHom A O Kf).toLinearMap).rTensor V) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  intro s t hst
  rw [hc, hc] at hst
  exact h2 (h3 hst)

theorem liftBaseChange_injective [Module.Flat A O]
    (hO : Function.Injective (algebraMap O Kf)) (φ : V →ₗ[K] W) (b : Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (M : Submodule A V) :
    Function.Injective (((φ.restrictScalars A) ∘ₗ M.subtype).liftBaseChange O) := by
  have h1 : Function.Injective (M.subtype.lTensor O) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ M.injective_subtype
  have hc : ∀ t, (((φ.restrictScalars A) ∘ₗ M.subtype).liftBaseChange O) t =
      ((φ.restrictScalars A).liftBaseChange O) ((M.subtype.lTensor O) t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  intro s t hst
  rw [hc, hc] at hst
  exact h1 (liftBaseChange_injective_top hO φ b hb hst)

omit [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K] [CommRing O] [Algebra A O] [Algebra O Kf] [Algebra A Kf]
  [IsScalarTower A O Kf] [IsScalarTower A K Kf] [Module A V] [IsScalarTower A K V] [Module O W] [IsScalarTower O Kf W]
  [Module A W] [IsScalarTower A O W] [IsScalarTower A K W] [IsScalarTower A Kf W] in

theorem li_tower {ι' : Type*} (φ : V →ₗ[K] W) (b : Basis ι K V) (hb : LinearIndependent Kf (φ ∘ b))
    (e : ι' → V) (he : LinearIndependent K e) : LinearIndependent Kf (φ ∘ e) := by
  have h4 : Function.Injective (φ.liftBaseChange Kf) := by
    apply injective_of_basis_li _ (b.baseChange Kf)
    convert hb using 1
    ext i
    simp
  let B := Basis.extend he.linearIndepOn_id
  have h1 : LinearIndependent Kf (fun i => (1 : Kf) ⊗ₜ[K] e i) := by
    have := (B.baseChange Kf).linearIndependent.comp
      (fun i => (⟨e i, he.linearIndepOn_id.subset_extend _ ⟨i, rfl⟩⟩ : he.linearIndepOn_id.extend (Set.subset_univ _)))
      (fun i j h => he.injective (congrArg Subtype.val h))
    convert this using 1
    ext i
    simp [B, Basis.baseChange_apply, Basis.extend_apply_self]
  have h2 := h1.map' (φ.liftBaseChange Kf) (LinearMap.ker_eq_bot.2 h4)
  have h3 : (φ ∘ e) = (φ.liftBaseChange Kf) ∘ (fun i => (1 : Kf) ⊗ₜ[K] e i) := by
    ext i
    simp
  rw [h3]
  exact h2

theorem span_inf_span_tower [Module.Flat A O]
    (hO : Function.Injective (algebraMap O Kf)) (φ : V →ₗ[K] W) (b : Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (L : Submodule A V) (U : Submodule K V) :
    Submodule.span O (φ '' (L : Set V)) ⊓ (Submodule.span Kf (φ '' (U : Set V))).restrictScalars O =
      Submodule.span O (φ '' ((L ⊓ U.restrictScalars A : Submodule A V) : Set V)) := by
  apply le_antisymm
  · rintro z ⟨hz1, hz2⟩
    set S := Submodule.span Kf (φ '' (U : Set V)) with hS
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
    let bU := Basis.ofVectorSpace K U
    let bC := Basis.ofVectorSpace K C
    have hsum : LinearIndependent K (Sum.elim (fun i => (bU i : V)) (fun i => (bC i : V))) := by
      apply LinearIndependent.sum_type
      · exact bU.linearIndependent.map' U.subtype U.ker_subtype
      · exact bC.linearIndependent.map' C.subtype C.ker_subtype
      · refine hC.disjoint.mono ?_ ?_
        · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (bU i).2
        · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (bC i).2
    have hsumKf := li_tower φ b hb _ hsum
    have hSle : S ≤ Submodule.span Kf (Set.range (fun i => φ (bU i : V))) := by
      rw [hS, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span K (Set.range (fun i => (bU i : V))) := by
        have h1 : (⟨x, hx⟩ : U) ∈ Submodule.span K (Set.range bU) := by rw [bU.span_eq]; trivial
        have h2 := Submodule.mem_map_of_mem (f := U.subtype) h1
        rw [Submodule.map_span, ← Set.range_comp] at h2
        exact h2
      have key : ∀ y ∈ Submodule.span K (Set.range (fun i => (bU i : V))),
          φ y ∈ Submodule.span Kf (Set.range (fun i => φ (bU i : V))) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
        | zero => simp
        | add y y' _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
        | smul k y _ h =>
          rw [map_smul, ← IsScalarTower.algebraMap_smul Kf k (φ y)]
          exact Submodule.smul_mem _ _ h
      exact key x hx'
    have hdisj : Disjoint (Submodule.span Kf (Set.range (fun i => φ (bC i : V)))) S := by
      have := hsumKf.disjoint_span_image (s := Set.range Sum.inr) (t := Set.range Sum.inl) (by
        rw [Set.disjoint_left]; rintro _ ⟨i, rfl⟩ ⟨j, hj⟩; cases hj)
      rw [← Set.range_comp, ← Set.range_comp] at this
      exact this.mono_right hSle
    let bq : Basis _ K (V ⧸ U) := bC.map (Submodule.quotientEquivOfIsCompl U C hC).symm
    let φq : V ⧸ U →ₗ[K] W ⧸ S := U.liftQ ((S.mkQ.restrictScalars K) ∘ₗ φ) (fun x hx => by
      rw [LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨x, hx, rfl⟩))
    have hbq : LinearIndependent Kf (φq ∘ bq) := by
      have h1 : LinearIndependent Kf (fun i => φ (bC i : V)) := hsumKf.comp Sum.inr Sum.inr_injective
      have h2 := h1.map (f := S.mkQ) (by rw [Submodule.ker_mkQ]; exact hdisj)
      have h3 : (φq ∘ bq) = S.mkQ ∘ fun i => φ (bC i : V) := by
        ext i
        simp [φq, bq]
      rw [h3]
      exact h2
    have hΞ := liftBaseChange_injective_top (A := A) hO φq bq hbq
    have hr := range_liftBaseChange O ((φ.restrictScalars A) ∘ₗ L.subtype)
    have hz1' : z ∈ LinearMap.range (((φ.restrictScalars A) ∘ₗ L.subtype).liftBaseChange O) := by
      have hset : Set.range ⇑((φ.restrictScalars A) ∘ₗ L.subtype) = φ '' (L : Set V) := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩; exact ⟨x.1, x.2, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
      rw [hr, hset]
      exact hz1
    obtain ⟨t, rfl⟩ := hz1'
    let f : ↥L →ₗ[A] V ⧸ U := (U.mkQ.restrictScalars A) ∘ₗ L.subtype
    have hcomm : ∀ t, ((φq.restrictScalars A).liftBaseChange O) (f.lTensor O t) =
        S.mkQ ((((φ.restrictScalars A) ∘ₗ L.subtype).liftBaseChange O) t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul c x => simp [f, φq]
      | add a b ha hb => simp only [map_add, ha, hb]
    have h0 : f.lTensor O t = 0 := by
      apply hΞ
      rw [hcomm, map_zero]
      exact (Submodule.Quotient.mk_eq_zero S).2 hz2
    obtain ⟨s, rfl⟩ := (Module.Flat.lTensor_exact O (LinearMap.exact_subtype_ker_map f) t).1 h0
    have hc2 : ∀ s, (((φ.restrictScalars A) ∘ₗ L.subtype).liftBaseChange O) ((LinearMap.ker f).subtype.lTensor O s) =
        (((φ.restrictScalars A) ∘ₗ L.subtype ∘ₗ (LinearMap.ker f).subtype).liftBaseChange O) s := by
      intro s
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul c x => simp
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [hc2]
    have hmem : (((φ.restrictScalars A) ∘ₗ L.subtype ∘ₗ (LinearMap.ker f).subtype).liftBaseChange O) s ∈
        LinearMap.range (((φ.restrictScalars A) ∘ₗ L.subtype ∘ₗ (LinearMap.ker f).subtype).liftBaseChange O) := ⟨s, rfl⟩
    rw [range_liftBaseChange] at hmem
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨x, rfl⟩
    refine ⟨x.1.1, ⟨x.1.2, ?_⟩, rfl⟩
    have := x.2
    rw [LinearMap.mem_ker] at this
    exact (Submodule.Quotient.mk_eq_zero U).1 this
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨x, hx1, rfl⟩, Submodule.subset_span ⟨x, hx2, rfl⟩⟩

end Tower

theorem length_flat_tower {A K O Kf V W ι : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (P : Ideal A) [P.IsPrime] [CommRing O] [IsLocalRing O] [Algebra A O]
    [Algebra (Localization.AtPrime P) O] [IsScalarTower A (Localization.AtPrime P) O]
    [IsLocalHom (algebraMap (Localization.AtPrime P) O)] [Module.Flat (Localization.AtPrime P) O]
    [Field Kf] [Algebra O Kf] [Algebra K Kf]
    [Algebra A Kf] [IsScalarTower A O Kf] [IsScalarTower A K Kf]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W] [Module K W] [IsScalarTower K Kf W]
    [Module A W] [IsScalarTower A O W] [IsScalarTower A K W] [IsScalarTower A Kf W]
    (hO : Function.Injective (algebraMap O Kf)) (φ : V →ₗ[K] W) (b : Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (N M : Submodule A V) (hNM : N ≤ M) :
    Module.length O (↥(Submodule.span O (φ '' (M : Set V))) ⧸
        (Submodule.span O (φ '' (N : Set V))).comap (Submodule.span O (φ '' (M : Set V))).subtype) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (↥M ⧸ N.comap M.subtype)) *
        Module.length O (O ⧸ (maximalIdeal (Localization.AtPrime P)).map (algebraMap (Localization.AtPrime P) O)) := by
  have : Module.Flat A O := Module.Flat.trans A (Localization.AtPrime P) O
  rw [← length_tensor_loc P O]
  exact length_span_quot O (φ.restrictScalars A) N M hNM (liftBaseChange_injective hO φ b hb M)

section Ext

open IsDedekindDomain

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]
  (σ : K →+* Kf) (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))

noncomputable def rangeEquiv (O Kf : Type*) [CommRing O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf] :
    O ≃+* (algebraMap O Kf).range :=
  RingEquiv.ofBijective (algebraMap O Kf).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O Kf (congrArg Subtype.val h), (algebraMap O Kf).rangeRestrict_surjective⟩

theorem rangeEquiv_symm_spec (y : (algebraMap O Kf).range) :
    algebraMap O Kf ((rangeEquiv O Kf).symm y) = y := by
  have := (rangeEquiv O Kf).apply_symm_apply y
  exact congrArg Subtype.val this

include hσ in
theorem mem_range_of_int (a : A) : σ (algebraMap A K a) ∈ (algebraMap O Kf).range :=
  (hσ _).1 (w.valuation_le_one a)

noncomputable def toO : A →+* O :=
  ((rangeEquiv O Kf).symm : (algebraMap O Kf).range →+* O).comp
    ((σ.comp (algebraMap A K)).codRestrict (algebraMap O Kf).range (mem_range_of_int w σ hσ))

theorem toO_spec (a : A) : algebraMap O Kf (toO w σ hσ a) = σ (algebraMap A K a) :=
  rangeEquiv_symm_spec _

theorem toO_injective : Function.Injective (toO w σ hσ) := by
  intro a b h
  have := congrArg (algebraMap O Kf) h
  rw [toO_spec, toO_spec] at this
  exact IsFractionRing.injective A K (σ.injective this)

include hσ in

theorem isUnit_of_val_one (x : K) (hx : w.valuation K x = 1) (c : O) (hc : algebraMap O Kf c = σ x) :
    IsUnit c := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨d, hd⟩ := (hσ x⁻¹).1 (by rw [map_inv₀, hx, inv_one])
  refine IsUnit.of_mul_eq_one d ?_
  apply IsFractionRing.injective O Kf
  rw [map_mul, hc, hd, map_one, ← map_mul, mul_inv_cancel₀ hx0, map_one]

theorem isUnit_toO_iff (a : A) : IsUnit (toO w σ hσ a) ↔ a ∉ w.asIdeal := by
  constructor
  · intro h ha
    have hlt : w.valuation K (algebraMap A K a) < 1 := (w.valuation_lt_one_iff_mem a).2 ha
    obtain ⟨d, hd⟩ := h.exists_right_inv
    have ha0 : algebraMap A K a ≠ 0 := by
      intro h0
      have := congrArg (algebraMap O Kf) hd
      rw [map_mul, toO_spec, h0, map_zero, zero_mul, map_one] at this
      exact zero_ne_one this
    have h1 : σ (algebraMap A K a)⁻¹ = algebraMap O Kf d := by
      have := congrArg (algebraMap O Kf) hd
      rw [map_mul, toO_spec, map_one] at this
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right this
    have h2 : w.valuation K (algebraMap A K a)⁻¹ ≤ 1 := (hσ _).2 ⟨d, h1.symm⟩
    rw [map_inv₀] at h2
    have h3 : (1 : WithZero (Multiplicative ℤ)) ≤ w.valuation K (algebraMap A K a) := by
      have hv0 : w.valuation K (algebraMap A K a) ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
      exact (inv_le_one₀ (zero_lt_iff.2 hv0)).1 h2
    exact absurd hlt (not_lt.2 h3)
  · intro ha
    exact isUnit_of_val_one w σ hσ _ ((HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 ha) _ (toO_spec w σ hσ a)

end Ext

section Ext2

open IsDedekindDomain IsDiscreteValuationRing

theorem length_quot_span_dvr {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (t : O) (ht : t ≠ 0) :
    Module.length O (O ⧸ Ideal.span {t}) = addVal O t := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ht hϖ
  rw [addVal_def' u hϖ n]
  have : Ideal.span {(u : O) * ϖ ^ n} = IsLocalRing.maximalIdeal O ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [this, length_quotient_pow_maximalIdeal]

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]
  (σ : K →+* Kf) (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))

theorem map_toO_eq (ϖ : A) (hϖ : w.intValuation ϖ = WithZero.exp (-1 : ℤ)) :
    w.asIdeal.map (toO w σ hσ) = Ideal.span {toO w σ hσ ϖ} := by
  have hϖK : w.valuation K (algebraMap A K ϖ) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hϖ]
  have hmem : ∀ a : A, a ∈ w.asIdeal ↔ w.intValuation a ≤ WithZero.exp (-1 : ℤ) := by
    intro a
    have := w.intValuation_le_pow_iff_mem a 1
    simpa using this.symm
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    have h1 : w.valuation K (algebraMap A K a / algebraMap A K ϖ) ≤ 1 := by
      rw [map_div₀, hϖK, HeightOneSpectrum.valuation_of_algebraMap]
      exact (div_le_one₀ (by simp [zero_lt_iff])).2 ((hmem a).1 ha)
    obtain ⟨s, hs⟩ := (hσ _).1 h1
    refine ⟨s, ?_⟩
    apply IsFractionRing.injective O Kf
    have hϖ0 : algebraMap A K ϖ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hϖK
      exact WithZero.exp_ne_zero hϖK.symm
    rw [map_mul, hs, toO_spec, toO_spec, ← map_mul, mul_div_cancel₀ _ hϖ0]
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ ((hmem ϖ).2 hϖ.le)

theorem addVal_toO (ϖ : A) (hϖ : w.intValuation ϖ = WithZero.exp (-1 : ℤ)) (x : A) (r : ℕ)
    (hx : w.valuation K (algebraMap A K x) = WithZero.exp (-(r : ℤ))) :
    addVal O (toO w σ hσ x) = r * addVal O (toO w σ hσ ϖ) := by
  have hϖK : w.valuation K (algebraMap A K ϖ) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hϖ]
  have hϖ0 : algebraMap A K ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖK
    exact WithZero.exp_ne_zero hϖK.symm
  have h1 : w.valuation K (algebraMap A K x / algebraMap A K ϖ ^ r) = 1 := by
    rw [map_div₀, map_pow, hϖK, hx, ← WithZero.exp_nsmul]
    have : (r • (-1 : ℤ)) = -(r : ℤ) := by simp
    rw [this]
    exact div_self WithZero.exp_ne_zero
  obtain ⟨s, hs⟩ := (hσ _).1 h1.le
  have hu : IsUnit s := isUnit_of_val_one w σ hσ _ h1 s hs
  have hmul : toO w σ hσ x = s * toO w σ hσ ϖ ^ r := by
    apply IsFractionRing.injective O Kf
    rw [map_mul, map_pow, hs, toO_spec, toO_spec, ← map_pow σ, ← map_mul σ, div_mul_cancel₀ _ (pow_ne_zero _ hϖ0)]
  rw [hmul, addVal_mul, addVal_pow, addVal_eq_zero_iff.2 hu, zero_add, nsmul_eq_mul]

end Ext2

section Ext3

open IsDedekindDomain IsDiscreteValuationRing

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]
  (σ : K →+* Kf) (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))

theorem flat_ext {V W ι : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (b : Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) :
    (∀ (N M : Submodule A V), N ≤ M → ∀ (x : A) (r : ℕ),
      w.valuation K (algebraMap A K x) = WithZero.exp (-(r : ℤ)) →
    Module.length O (↥(Submodule.span O (φ '' (M : Set V))) ⧸
        (Submodule.span O (φ '' (N : Set V))).comap (Submodule.span O (φ '' (M : Set V))).subtype) * r =
      (letI : w.asIdeal.IsPrime := w.isPrime
       Module.length (Localization.AtPrime w.asIdeal)
        (LocalizedModule w.asIdeal.primeCompl (↥M ⧸ N.comap M.subtype))) * addVal O (toO w σ hσ x)) ∧
    (∀ (L : Submodule A V) (U : Submodule K V),
      Submodule.span O (φ '' (L : Set V)) ⊓ (Submodule.span Kf (φ '' (U : Set V))).restrictScalars O =
        Submodule.span O (φ '' ((L ⊓ U.restrictScalars A : Submodule A V) : Set V))) := by
  let : w.asIdeal.IsPrime := w.isPrime
  let algKKf : Algebra K Kf := σ.toAlgebra
  let algAO : Algebra A O := (toO w σ hσ).toAlgebra
  let algAKf : Algebra A Kf := ((algebraMap O Kf).comp (toO w σ hσ)).toAlgebra
  have t1 : IsScalarTower A O Kf := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have t2 : IsScalarTower A K Kf := IsScalarTower.of_algebraMap_eq (fun a => toO_spec w σ hσ a)
  let modKW : Module K W := Module.compHom W σ
  have t3 : IsScalarTower K Kf W := ⟨fun k c z => by
    show (σ k * c) • z = σ k • c • z
    rw [mul_smul]⟩
  let modAW : Module A W := Module.compHom W (toO w σ hσ)
  have t4 : IsScalarTower A O W := ⟨fun a c z => by
    show (toO w σ hσ a * c) • z = toO w σ hσ a • c • z
    rw [mul_smul]⟩
  have t5 : IsScalarTower A K W := ⟨fun a k z => by
    show σ (a • k) • z = toO w σ hσ a • σ k • z
    rw [Algebra.smul_def, map_mul, mul_smul, ← toO_spec w σ hσ a, algebraMap_smul]⟩
  have t6 : IsScalarTower A Kf W := ⟨fun a c z => by
    show (algebraMap O Kf (toO w σ hσ a) * c) • z = toO w σ hσ a • c • z
    rw [mul_smul, algebraMap_smul]⟩
  let algLO : Algebra (Localization.AtPrime w.asIdeal) O :=
    (IsLocalization.lift (M := w.asIdeal.primeCompl) (g := toO w σ hσ)
      (fun y => (isUnit_toO_iff w σ hσ y).2 y.2)).toAlgebra
  have t7 : IsScalarTower A (Localization.AtPrime w.asIdeal) O :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsLocalization.lift_eq _ a).symm)
  have hmk : ∀ y : Localization.AtPrime w.asIdeal, ∃ (a : A) (s : w.asIdeal.primeCompl),
      y * algebraMap A _ (s : A) = algebraMap A _ a ∧
      algebraMap (Localization.AtPrime w.asIdeal) O y * toO w σ hσ s = toO w σ hσ a := by
    intro y
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj w.asIdeal.primeCompl y
    refine ⟨a, s, h, ?_⟩
    have := congrArg (algebraMap (Localization.AtPrime w.asIdeal) O) h
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this
  have t8 : IsLocalHom (algebraMap (Localization.AtPrime w.asIdeal) O) := ⟨fun y hy => by
    obtain ⟨a, s, h1, h2⟩ := hmk y
    have ha : IsUnit (toO w σ hσ a) := h2 ▸ hy.mul ((isUnit_toO_iff w σ hσ s).2 s.2)
    have ha' : a ∉ w.asIdeal := (isUnit_toO_iff w σ hσ a).1 ha
    have : IsUnit (algebraMap A (Localization.AtPrime w.asIdeal) a) :=
      IsLocalization.map_units _ (⟨a, ha'⟩ : w.asIdeal.primeCompl)
    rw [← h1] at this
    exact isUnit_of_mul_isUnit_left this⟩
  have : IsDiscreteValuationRing (Localization.AtPrime w.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A w.ne_bot _
  have t9 : Module.IsTorsionFree (Localization.AtPrime w.asIdeal) O :=
    Module.IsTorsionFree.of_smul_eq_zero (fun y c h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      refine h.imp_left (fun h0 => ?_)
      obtain ⟨a, s, h1, h2⟩ := hmk y
      rw [h0, zero_mul] at h2
      have ha : a = 0 := toO_injective w σ hσ (by rw [← h2, map_zero])
      rw [ha, map_zero] at h1
      exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units _ s)).1 h1)
  have t10 : Module.Flat (Localization.AtPrime w.asIdeal) O := inferInstance
  let φL : V →ₗ[K] W := { toFun := φ, map_add' := φ.map_add, map_smul' := fun a x => hφ a x }
  have t11 : Module.Flat A O := Module.Flat.trans A (Localization.AtPrime w.asIdeal) O
  refine ⟨?_, fun L U => span_inf_span_tower (IsFractionRing.injective O Kf) φL b hb L U⟩
  intro N M hNM x r hx
  have key := length_flat_tower w.asIdeal (IsFractionRing.injective O Kf) φL b hb N M hNM
  obtain ⟨ϖ, hϖ⟩ := w.intValuation_exists_uniformizer
  have hϖ0 : toO w σ hσ ϖ ≠ 0 := by
    intro h0
    have : ϖ = 0 := toO_injective w σ hσ (by rw [h0, map_zero])
    rw [this, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime w.asIdeal)).map
      (algebraMap (Localization.AtPrime w.asIdeal) O) = Ideal.span {toO w σ hσ ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal w.asIdeal (Localization.AtPrime w.asIdeal), Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact map_toO_eq w σ hσ ϖ hϖ
  rw [hmax, length_quot_span_dvr _ hϖ0] at key
  rw [addVal_toO w σ hσ ϖ hϖ x r hx]
  have key' : Module.length O (↥(Submodule.span O (φ '' (M : Set V))) ⧸
        (Submodule.span O (φ '' (N : Set V))).comap (Submodule.span O (φ '' (M : Set V))).subtype) = _ := key
  rw [key']
  ring

end Ext3

theorem li_of_basis_li {K Kf V W ι₀ ι : Type*} [Field K] [Field Kf] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module Kf W] (σ : K →+* Kf) (ψ : V →+ W) (hψ : ∀ (a : K) x, ψ (a • x) = σ a • ψ x) (b₀ : Basis ι₀ K V)
    (hb₀ : LinearIndependent Kf (ψ ∘ b₀)) (e : ι → V) (he : LinearIndependent K e) :
    LinearIndependent Kf (ψ ∘ e) := by
  let algKKf : Algebra K Kf := σ.toAlgebra
  let modKW : Module K W := Module.compHom W σ
  have t3 : IsScalarTower K Kf W := ⟨fun k c z => by
    show (σ k * c) • z = σ k • c • z
    rw [mul_smul]⟩
  let ψL : V →ₗ[K] W := { toFun := ψ, map_add' := ψ.map_add, map_smul' := fun a x => hψ a x }
  exact li_tower ψL b₀ hb₀ e he

section Ext4

open IsDedekindDomain IsDiscreteValuationRing

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]
  (σ : K →+* Kf) (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))

include hσ in

theorem span_image_le_of_loc {V W : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (T : Set V) (N : Submodule A V)
    (h : ∀ x ∈ T, ∃ s : A, s ∉ w.asIdeal ∧ s • x ∈ N) :
    Submodule.span O (φ '' T) ≤ Submodule.span O (φ '' (N : Set V)) := by
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hsx⟩ := h x hx
  obtain ⟨v, hv⟩ := (isUnit_toO_iff w σ hσ s).2 hs
  have h1 : φ (s • x) = (v : O) • φ x := by
    rw [← algebraMap_smul K s x, hφ, ← toO_spec w σ hσ s, algebraMap_smul, hv]
  have h2 : φ x = ((v⁻¹ : Oˣ) : O) • φ (s • x) := by
    rw [h1, smul_smul, Units.inv_mul, one_smul]
  rw [SetLike.mem_coe, h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsx, rfl⟩)

end Ext4

section Fin

open IsDedekindDomain IsDiscreteValuationRing

theorem length_ne_top_of_smul {O Q : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup Q]
    [Module O Q] [Module.Finite O Q] (t : O) (ht : t ≠ 0) (h : ∀ q : Q, t • q = 0) : Module.length O Q ≠ ⊤ := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := Q)
  let li : Fin n → (O ⧸ Ideal.span {t}) →ₗ[O] Q := fun i =>
    Submodule.liftQ (Ideal.span {t}) (LinearMap.toSpanSingleton O Q (s i)) (by
      rw [Ideal.span, Submodule.span_le]
      rintro _ rfl
      simp [h])
  let g : (Fin n → O ⧸ Ideal.span {t}) →ₗ[O] Q := LinearMap.lsum O (fun _ => O ⧸ Ideal.span {t}) O li
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    have h1 : g (Pi.single i (Submodule.Quotient.mk 1)) = li i (Submodule.Quotient.mk 1) := by
      simp only [g, LinearMap.lsum_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, map_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [h1]
    show Submodule.liftQ (Ideal.span {t}) (LinearMap.toSpanSingleton O Q (s i)) _ (Submodule.Quotient.mk 1) = s i
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  have hle := Module.length_le_of_surjective g hg
  have hfin : Module.length O (Fin n → O ⧸ Ideal.span {t}) ≠ ⊤ := by
    rw [Module.length_pi_of_fintype]
    simp only [length_quot_span_dvr t ht, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (fun h0 => ht (addVal_eq_top_iff.1 h0))
    rw [← hk]
    exact_mod_cast ENat.natCast_ne_top (n * k)
  exact ne_top_of_le_ne_top hfin hle

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]
  (σ : K →+* Kf) (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))

include hσ in

theorem fg_span_image {V W : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (N : Submodule A V) (hN : N.FG) :
    (Submodule.span O (φ '' (N : Set V))).FG := by
  obtain ⟨S, hS⟩ := hN
  have h : Submodule.span O (φ '' (N : Set V)) = Submodule.span O (φ '' (S : Set V)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, ← hS] at hx
      rw [SetLike.mem_coe]
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => simp
      | add y y' _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
      | smul a y _ h =>
        rw [← algebraMap_smul K a y, hφ, ← toO_spec w σ hσ a, algebraMap_smul]
        exact Submodule.smul_mem _ _ h
    · apply Submodule.span_mono
      apply Set.image_mono
      rw [← hS]
      exact Submodule.subset_span
  rw [h]
  exact Submodule.fg_span ((Finset.finite_toSet S).image _)

end Fin

section Same

open IsDedekindDomain IsDiscreteValuationRing

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]
  (σ : K →+* Kf) (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))

theorem addVal_toO_uniformizer (hsurj : ∀ c : O, ∃ x : K, σ x = algebraMap O Kf c) (ϖ : A)
    (hϖ : w.intValuation ϖ = WithZero.exp (-1 : ℤ)) : addVal O (toO w σ hσ ϖ) = 1 := by
  apply addVal_uniformizer
  rw [irreducible_iff_uniformizer]
  have hϖK : w.valuation K (algebraMap A K ϖ) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hϖ]
  have hϖ0 : algebraMap A K ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖK
    exact WithZero.exp_ne_zero hϖK.symm
  have hmemw : ϖ ∈ w.asIdeal := by
    rw [← w.intValuation_lt_one_iff_mem, hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  apply le_antisymm
  · intro c hc
    rw [Ideal.mem_span_singleton]
    obtain ⟨x, hx⟩ := hsurj c
    have hx1 : w.valuation K x ≤ 1 := (hσ x).2 ⟨c, hx.symm⟩
    have hx2 : w.valuation K x ≠ 1 := by
      intro h1
      exact (IsLocalRing.mem_maximalIdeal c).1 hc (isUnit_of_val_one w σ hσ x h1 c hx.symm)
    have hx3 : w.valuation K x ≤ WithZero.exp (-1 : ℤ) := by
      by_cases hx0 : x = 0
      · rw [hx0, map_zero]; exact zero_le
      · have hv : w.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
        have hlt := lt_of_le_of_ne hx1 hx2
        rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
        rw [← WithZero.exp_log hv, WithZero.exp_le_exp]
        omega
    have h1 : w.valuation K (x / algebraMap A K ϖ) ≤ 1 := by
      rw [map_div₀, hϖK]
      exact (div_le_one₀ (by simp [zero_lt_iff])).2 hx3
    obtain ⟨s, hs⟩ := (hσ _).1 h1
    refine ⟨s, ?_⟩
    apply IsFractionRing.injective O Kf
    rw [map_mul, hs, toO_spec, ← hx, ← map_mul σ, mul_div_cancel₀ _ hϖ0]
  · rw [Ideal.span_singleton_le_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_toO_iff]
    exact fun h => h hmemw

include hσ in

theorem length_valuationRing (hsurj : ∀ c : O, ∃ x : K, σ x = algebraMap O Kf c)
    {V W ι : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (b : Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (N M : Submodule A V) (hNM : N ≤ M) :
    Module.length O (↥(Submodule.span O (φ '' (M : Set V))) ⧸
        (Submodule.span O (φ '' (N : Set V))).comap (Submodule.span O (φ '' (M : Set V))).subtype) =
      (letI : w.asIdeal.IsPrime := w.isPrime
       Module.length (Localization.AtPrime w.asIdeal)
        (LocalizedModule w.asIdeal.primeCompl (↥M ⧸ N.comap M.subtype))) := by
  obtain ⟨ϖ, hϖ⟩ := w.intValuation_exists_uniformizer
  have h := (flat_ext w σ hσ φ hφ b hb).1 N M hNM ϖ 1 (by
    rw [HeightOneSpectrum.valuation_of_algebraMap, hϖ]; rfl)
  rw [addVal_toO_uniformizer w σ hσ hsurj ϖ hϖ] at h
  simpa using h

end Same

end FBC

namespace LatCmp

open Formalism.MainNotions.G IsDedekindDomain IsDiscreteValuationRing

variable {D : D7} (c : LatCmp D)

theorem embW_val (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (x : D.what₂.LL) :
    (D.plEq w).valuation D.what₂.LL x ≤ 1 ↔
      c.embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf) := by
  rw [← c.embW_int u w hg x]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [D.val_eq w x hx]
    have hv : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    unfold vAdd
    rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.log_exp]
    constructor
    · intro h; exact_mod_cast (neg_nonneg.2 h)
    · intro h; exact neg_nonneg.1 (by exact_mod_cast h)

def cmpN (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : (D.div.Nu u).V →+ (D.gat u w hg).Fn :=
  (c.cmp u w hg).comp (D.nuIn u).toAddMonoidHom

theorem cmpN_smul (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (a : D.what₂.LL) (x : (D.div.Nu u).V) :
    c.cmpN u w hg (a • x) = c.embW u w hg a • c.cmpN u w hg x := by
  show c.cmp u w hg (D.nuIn u (a • x)) = _
  rw [map_smul, c.cmp_smul]
  rfl

theorem cmpN_li (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    LinearIndependent (D.gat u w hg).Kf (c.cmpN u w hg ∘ (D.div.Nu u).b) :=
  FBC.li_of_basis_li (c.embW u w hg) (c.cmp u w hg) (c.cmp_smul u w hg) ((D.fm u).lat 0).b (c.cmp_li u w hg)
    (D.nuIn u ∘ (D.div.Nu u).b)
    ((D.div.Nu u).b.linearIndependent.map' (D.nuIn u) (LinearMap.ker_eq_bot.2 (D.nuIn_inj u)))

end LatCmp

namespace LatCmp

open Formalism.MainNotions.G IsDedekindDomain IsDiscreteValuationRing

variable {D : D7} (c : LatCmp D)

theorem M_inf_Vram (Y : LatInst D) (hv : c.VramDef Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf] :
    (D.gat u w hg).M ⊓ Y.Vram u w hg =
      Submodule.span (D.gat u w hg).O (c.cmpN u w hg '' (DV.MramL D u : Set (D.div.Nu u).V)) := by
  have h2 := (FBC.flat_ext (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (c.cmp u w hg) (c.cmp_smul u w hg)
    ((D.fm u).lat 0).b (c.cmp_li u w hg)).2 ((D.fm u).lat 0).L (D.fm u).ramSub
  have hV : Y.Vram u w hg = (Submodule.span (D.gat u w hg).Kf
      (c.cmp u w hg '' ((D.fm u).ramSub : Set ((D.fm u).lat 0).V))).restrictScalars (D.gat u w hg).O :=
    SetLike.coe_injective (hv u w hg)
  rw [← c.cmp_M u w hg, hV, h2]
  have h3 : (((D.fm u).lat 0).L ⊓ (D.fm u).ramSub.restrictScalars (𝓞 D.what₂.LL) :
      Submodule (𝓞 D.what₂.LL) ((D.fm u).lat 0).V) = (D.fm u).ramL := rfl
  rw [h3, ← D.MramL_map u, Submodule.map_coe, Set.image_image]
  rfl

def NPDesc {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
    NP X Y K u w hg ≤ Submodule.span (D.gat u w hg).O
      (c.cmp u w hg '' {y | y ∈ (D.fm u).ramSub ∧ c.cmp u w hg y ∈ NP X Y K u w hg})

theorem NP_eq_span {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (hNu : DV.NuDef D L)
    (hs : c.NuServedDef X Y K) (hd : c.NPDesc X Y K) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf]
    (hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅) :
    NP X Y K u w hg = Submodule.span (D.gat u w hg).O
      (c.cmpN u w hg '' ((L.NuLat u ⊓ DV.MramL D u : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Set (D.div.Nu u).V)) := by
  have hT : D.what₂.places.resChar w ≠ (D.mem u).A.T := by
    intro h
    exact hg.2.2.2.2.2 (h ▸ dvd_rfl)
  apply le_antisymm
  · refine (hd u w hg hVV).trans ?_
    have h1 : c.cmp u w hg '' {y | y ∈ (D.fm u).ramSub ∧ c.cmp u w hg y ∈ NP X Y K u w hg} =
        c.cmpN u w hg '' {x | InLoc (D.plEq w) (L.NuLat u) x} := by
      ext z
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        rw [← D.nuIn_range u] at hy1
        obtain ⟨x, rfl⟩ := hy1
        exact ⟨x, (hs u w hg hVV x).2 hy2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨D.nuIn u x, ⟨?_, (hs u w hg hVV x).1 hx⟩, rfl⟩
        rw [← D.nuIn_range u]
        exact ⟨x, rfl⟩
    rw [h1]
    apply FBC.span_image_le_of_loc (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (c.cmpN u w hg) (c.cmpN_smul u w hg)
    rintro x ⟨s, hs1, hs2⟩
    obtain ⟨s', hs1', hs2'⟩ := hNu.1 u w hT _ hs2
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hs2'
    refine ⟨s' * s, ?_, ?_, ?_⟩
    · exact fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hs1' hs1
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hs2
    · rw [mul_smul]; exact hs2'
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    exact (hs u w hg hVV x).1 ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩

end LatCmp

theorem FBC.length_congr {O W : Type*} [CommRing O] [AddCommGroup W] [Module O W] {P₁ P₁' P₂ P₂' : Submodule O W}
    (h₁ : P₁ = P₁') (h₂ : P₂ = P₂') :
    Module.length O (↥P₁ ⧸ P₂.comap P₁.subtype) = Module.length O (↥P₁' ⧸ P₂'.comap P₁'.subtype) := by
  subst h₁ h₂
  rfl

namespace D7

theorem val_resChar' (D : D7) (w : D.what₂.places.Pl) :
    (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) =
      WithZero.exp (-((D.what₂.places.ramIdx w : ℕ) : ℤ)) := by
  rw [map_natCast]
  have hp0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have h1 := D.val_eq w _ hp0
  rw [D.what₂.places.val_resChar w] at h1
  have h2 : ((D.what₂.places.ramIdx w : ℕ) : ℤ) = vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) :=
    WithTop.coe_injective h1
  have hv : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hp0
  rw [h2]
  unfold vAdd
  rw [neg_neg, WithZero.exp_log hv]

end D7

namespace LatCmp

open Formalism.MainNotions.G IsDedekindDomain IsDiscreteValuationRing

variable {D : D7} (c : LatCmp D)

theorem length_quotient_of_nonempty {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (hNu : DV.NuDef D L)
    (hv : c.VramDef Y) (hs : c.NuServedDef X Y K) (hd : c.NPDesc X Y K) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf]
    (hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅)
    (hfin : Module.length (D.gat u w hg).O (↥((D.gat u w hg).M ⊓ Y.Vram u w hg) ⧸
      (NP X Y K u w hg).comap ((D.gat u w hg).M ⊓ Y.Vram u w hg).subtype) ≠ ⊤) :
    ∃ l : ℕ, Module.length (D.gat u w hg).O (↥((D.gat u w hg).M ⊓ Y.Vram u w hg) ⧸
          (NP X Y K u w hg).comap ((D.gat u w hg).M ⊓ Y.Vram u w hg).subtype) = l ∧
      (l : ℝ) = (L.lenMN u w : ℝ) * vUnit (D.gat u w hg) := by
  have key := (FBC.flat_ext (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (c.cmpN u w hg) (c.cmpN_smul u w hg)
    (D.div.Nu u).b (c.cmpN_li u w hg)).1 (L.NuLat u ⊓ DV.MramL D u) (DV.MramL D u) inf_le_right
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (D.what₂.places.ramIdx w) (D.val_resChar' w)
  rw [← FBC.length_congr (c.M_inf_Vram Y hv u w hg) (c.NP_eq_span X Y K hNu hs hd u w hg hVV), map_natCast] at key
  have hcomap : (L.NuLat u ⊓ DV.MramL D u).comap (DV.MramL D u).subtype = (L.NuLat u).comap (DV.MramL D u).subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  rw [hcomap] at key
  have key' : _ = DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) * _ := key
  obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1 hfin
  have hp0 : ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ≠ 0 := by
    intro h0
    have h1 : FBC.toO (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) = 0 := by
      rw [map_natCast, h0]
    have h2 := FBC.toO_injective (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (h1.trans (map_zero _).symm)
    exact (D.what₂.places.resChar_prime w).ne_zero (by exact_mod_cast h2)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (fun h => hp0 (addVal_eq_top_iff.1 h))
  have hU : vUnit (D.gat u w hg) = (n : ℝ) := by
    unfold vUnit
    rw [← hn]
    simp
  have hram : 0 < D.what₂.places.ramIdx w := D.what₂.places.ramIdx_pos w
  refine ⟨l, hl.symm, ?_⟩
  rw [← hl, ← hn] at key'
  rw [hU]
  by_cases hn0 : n = 0
  · subst hn0
    have : (l : ℕ∞) * (D.what₂.places.ramIdx w : ℕ∞) = 0 := by rw [key']; simp
    have h2 : l * D.what₂.places.ramIdx w = 0 := by exact_mod_cast this
    have h3 : l = 0 := (Nat.mul_eq_zero.1 h2).resolve_right hram.ne'
    simp [h3]
  · have hlt : DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) ≠ ⊤ := by
      intro h
      rw [h, ENat.top_mul (by exact_mod_cast hn0)] at key'
      exact ENat.natCast_ne_top _ (by exact_mod_cast key')
    obtain ⟨l', hl'⟩ := ENat.ne_top_iff_exists.1 hlt
    have h1 := hNu.2.2 u w l' hl'.symm
    rw [← hl'] at key'
    have h2 : l * D.what₂.places.ramIdx w = l' * n := by exact_mod_cast key'
    have h3 : (l : ℝ) * (D.what₂.places.ramIdx w : ℝ) = (l' : ℝ) * (n : ℝ) := by exact_mod_cast h2
    rw [h1] at h3
    have hr : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by exact_mod_cast hram
    have h4 : ((l : ℝ) - (L.lenMN u w : ℝ) * (n : ℝ)) * (D.what₂.places.ramIdx w : ℝ) = 0 := by
      rw [sub_mul, h3]; ring
    rcases mul_eq_zero.1 h4 with h5 | h5
    · linarith
    · exact absurd h5 hr.ne'

end LatCmp

theorem DV.lenLoc_eq_zero {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) (h : DV.LocLe w 0 B A) :
    DV.lenLoc w A B = 0 := by
  unfold DV.lenLoc
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  intro m
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  obtain ⟨s, hs, hsx⟩ := h x.1 x.2
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hsx
  refine ⟨s, hs, ?_⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hsx

namespace LatCmp

open Formalism.MainNotions.G IsDedekindDomain IsDiscreteValuationRing

variable {D : D7}

theorem inf_le_localSubmodule_of_empty {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅) :
    (D.gat u w hg).M ⊓ Y.Vram u w hg ≤ NP X Y K u w hg := by
  rintro F ⟨hF1, hF2⟩
  unfold NP
  refine ⟨⟨?_, ?_⟩, hF2⟩
  · apply Submodule.subset_span
    refine ⟨∅, Finset.empty_subset _, F, hF1, ?_⟩
    simp [hVV, yProd]
  · refine ⟨F, hF1, ?_⟩
    simp [tauP, hVV]

theorem lenMN_unserved {L : SizeData₂ D} (hNu : DV.NuDef D L) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : DV.LocEq (D.plEq w) (L.NuLat u) (DV.MramL D u)) : L.lenMN u w = 0 := by
  have h1 := hNu.2.2 u w 0 (by rw [DV.lenLoc_eq_zero _ _ _ h.2]; rfl)
  have h2 : L.lenMN u w = 0 ∨ D.what₂.places.ramIdx w = 0 := by simpa using h1.symm
  exact h2.resolve_right (D.what₂.places.ramIdx_pos w).ne'

theorem sizeDataLat_of_fin (c : LatCmp D) {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (hNu : DV.NuDef D L)
    (hl : LatDefs D L X Y K c) (hun : NuUnserved X K) (hd : c.NPDesc X Y K)
    (hfr : ∀ u w hg, IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf)
    (hfin : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
      Module.length (D.gat u w hg).O (↥((D.gat u w hg).M ⊓ Y.Vram u w hg) ⧸
        (NP X Y K u w hg).comap ((D.gat u w hg).M ⊓ Y.Vram u w hg).subtype) ≠ ⊤)
    (w : D.what₂.places.Pl) : LatticeLengthsAtPlace X Y K w := by
  refine ⟨fun _ u hg => ?_, fun u hVV hT => lenMN_unserved hNu u w (hun u w hT hVV)⟩
  by_cases hVV : VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅
  · have hT : D.what₂.places.resChar w ≠ (D.mem u).A.T := fun h => hg.2.2.2.2.2 (h ▸ dvd_rfl)
    refine ⟨0, ?_, ?_⟩
    · rw [Submodule.comap_subtype_eq_top.2 (inf_le_localSubmodule_of_empty X Y K u w hg hVV)]
      simp
    · rw [lenMN_unserved hNu u w (hun u w hT hVV)]
      simp
  · have := hfr u w hg
    exact c.length_quotient_of_nonempty X Y K hNu hl.vram hl.served hd u w hg hVV (hfin u w hg hVV)

end LatCmp

namespace LatCmp

open Formalism.MainNotions.G IsDedekindDomain IsDiscreteValuationRing

variable {D : D7} (c : LatCmp D)

include c in
theorem resChar_ne_zero_O (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf] :
    ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ≠ 0 := by
  intro h0
  have h1 : FBC.toO (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) = 0 := by
    rw [map_natCast, h0]
  have h2 := FBC.toO_injective (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (h1.trans (map_zero _).symm)
  exact (D.what₂.places.resChar_prime w).ne_zero (by exact_mod_cast h2)

theorem length_quotient_ne_top₂ {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (hv : c.VramDef Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf] :
    Module.length (D.gat u w hg).O (↥((D.gat u w hg).M ⊓ Y.Vram u w hg) ⧸
      (NP X Y K u w hg).comap ((D.gat u w hg).M ⊓ Y.Vram u w hg).subtype) ≠ ⊤ := by
  have hfg : ((D.gat u w hg).M ⊓ Y.Vram u w hg).FG := by
    rw [c.M_inf_Vram Y hv u w hg]
    exact FBC.fg_span_image (D.plEq w) (c.embW u w hg) (c.embW_val u w hg) (c.cmpN u w hg) (c.cmpN_smul u w hg) _
      (D.MramL_fg u)
  have : Module.Finite (D.gat u w hg).O ↥((D.gat u w hg).M ⊓ Y.Vram u w hg) := Module.Finite.iff_fg.2 hfg
  set a : ℕ := ∑ t0 ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w),
    ⌈Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat with ha
  set b : ℕ := ⌈tauP X K (aL L) (bL L) (D.what₂.places.resChar w)⌉.toNat with hb
  apply FBC.length_ne_top_of_smul (((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ (b + a))
    (pow_ne_zero _ (c.resChar_ne_zero_O u w hg))
  intro q
  obtain ⟨⟨F, hF1, hF2⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ (b + a) • F ∈ NP X Y K u w hg
  unfold NP
  refine ⟨⟨?_, ?_⟩, Submodule.smul_mem _ _ hF2⟩
  · rw [pow_add, mul_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨∅, Finset.empty_subset _, F, hF1, ?_⟩
    simp [yProd, ha]
  · refine ⟨((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ a • F, Submodule.smul_mem _ _ hF1, ?_⟩
    rw [pow_add, mul_smul]
    rfl

omit c in

theorem frac_of_ties (hT : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf := by
  have h : 0 < Fintype.card D.what₂.Tau := by
    rw [D.what₂.card_Tau]
    unfold Ranks.f Ranks.n
    positivity
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 h
  exact ((D.gat u w hg).P.setting ((hT.gat_pos u w hg).symm τ).1).frac_O

theorem sizeDataLat_of_latDefs {L : SizeData₂ D} (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (hNu : DV.NuDef D L)
    (hl : LatDefs D L X Y K c) (hun : NuUnserved X K) (hd : c.NPDesc X Y K)
    (w : D.what₂.places.Pl) : LatticeLengthsAtPlace X Y K w :=
  c.sizeDataLat_of_fin X Y K hNu hl hun hd (frac_of_ties hT)
    (fun u w hg _ => haveI := frac_of_ties hT u w hg; c.length_quotient_ne_top₂ X Y K hl.vram u w hg) w

end LatCmp

theorem DV.lamPDef_of {D : D7} (h : DV.LamDef D) (hs : DV.LamScalar D) : Rows.LamPDef D.what₂ := by
  intro μ j h1 h2 π x hx
  obtain ⟨c, hc⟩ := hs μ j h1 h2 π
  by_cases h0 : D.what₂.isot j π = ⊥
  · rw [h0, Submodule.mem_bot] at hx
    simp [hx]
  · rw [h μ j h1 h2 π h0, DV.lamTr_of_scalar D μ j π c h0 hc]
    exact hc x hx

theorem DV.lamDef_of_lamPDef {D : D7} (h : Rows.LamPDef D.what₂) : DV.LamDef D :=
  fun μ j h1 h2 π h0 => (DV.lamTr_of_scalar D μ j π _ h0 (h μ j h1 h2 π)).symm

namespace D7

variable (D : D7)

theorem val_nonneg_iff (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [D.val_eq w x hx]
    have hv : (D.plEq w).valuation D.what₂.LL x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    unfold vAdd
    conv_rhs => rw [← WithZero.exp_log hv, ← WithZero.exp_zero, WithZero.exp_le_exp]
    constructor
    · intro h; exact neg_nonneg.1 (by exact_mod_cast h)
    · intro h; exact_mod_cast (neg_nonneg.2 h)

theorem inLoc_of_mem_locW (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (A : Submodule (𝓞 D.what₂.LL) V) (y : V)
    (hy : y ∈ locW D.what₂.places w A) : InLoc (D.plEq w) A y := by
  have h1 : (1 : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal :=
    fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  unfold locW at hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact ⟨1, h1, by rwa [one_smul]⟩
  | zero => exact ⟨1, h1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.smul_mem _ hsy
    · rw [mul_smul]; exact A.smul_mem _ htz
  | smul r y _ hy =>
    obtain ⟨s, hs, hsy⟩ := hy
    obtain ⟨n, d, hnd⟩ := (D.plEq w).exists_primeCompl_mul_eq_of_integer (r : D.what₂.LL)
      ((D.val_nonneg_iff w r).1 r.2)
    refine ⟨(d : 𝓞 D.what₂.LL) * s, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim d.2 hs, ?_⟩
    have : ((d : 𝓞 D.what₂.LL) * s) • (r • y) = n • (s • y) := by
      rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL ((d : 𝓞 D.what₂.LL) * s), ← algebraMap_smul D.what₂.LL n,
        ← algebraMap_smul D.what₂.LL s, smul_smul, smul_smul, map_mul, ← hnd]
      congr 1
      ring
    rw [this]
    exact A.smul_mem _ hsy

theorem mem_locW_of_inLoc (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (A : Submodule (𝓞 D.what₂.LL) V) (y : V)
    (hy : InLoc (D.plEq w) A y) : y ∈ locW D.what₂.places w A := by
  obtain ⟨s, hs, hsy⟩ := hy
  have hv : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s) = 1 :=
    ((D.plEq w).valuation_eq_one_iff_notMem).2 hs
  have hs0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have hinv : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ ∈ intW D.what₂.places w :=
    (D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one])
  have : y = (⟨_, hinv⟩ : intW D.what₂.places w) • (s • y) := by
    rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL s, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsy)

theorem mem_locW_iff (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (A : Submodule (𝓞 D.what₂.LL) V) (y : V) :
    y ∈ locW D.what₂.places w A ↔ InLoc (D.plEq w) A y :=
  ⟨D.inLoc_of_mem_locW w A y, D.mem_locW_of_inLoc w A y⟩

theorem locSpan (u : D.what₂.Word) (w : D.what₂.places.Pl) (y : ((D.fm u).lat 0).V) (hy : y ∈ (D.fm u).S 0 w) :
    InLoc (D.plEq w) ((D.fm u).lat 0).L y :=
  D.inLoc_of_mem_locW w _ y hy

end D7

theorem denseRange_embedding_of_isComplex {K : Type*} [Field K] (v : InfinitePlace K) (hv : v.IsComplex) :
    DenseRange v.embedding := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure v.embedding.fieldRange) with h | h
  · exfalso
    rw [InfinitePlace.isComplex_iff] at hv
    apply hv
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : v.embedding x ∈ v.embedding.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · rw [denseRange_iff_closure_range, ← RingHom.coe_fieldRange]
    have h1 : (v.embedding.fieldRange.topologicalClosure : Set ℂ) = closure (v.embedding.fieldRange : Set ℂ) := rfl
    rw [← h1, h]
    rfl

theorem opNormAt_sq_le {K : Type} [Field K] [NumberField K] [StarRing K]
    {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (hv : v.IsComplex)
    (φ : V →ₗ[K] W) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x : V, (Formalism.HermitianLatticesTheory.majAt b' X' v (φ x) (φ x)).re ≤ c * (Formalism.HermitianLatticesTheory.majAt b X v x x).re) :
    Formalism.HN.opNormAt b X b' X' v φ ^ 2 ≤ c := by
  set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v)) with hT

  let g : (ι → ℂ) → EuclideanSpace ℂ ι := fun z => WithLp.toLp 2 ((X v)⁻¹.mulVec z)
  have hgc : Continuous g := by
    apply (PiLp.continuous_toLp 2 _).comp
    exact Continuous.matrix_mulVec continuous_const continuous_id
  have hgs : Function.Surjective g := by
    intro ξ
    refine ⟨(X v).mulVec (WithLp.ofLp ξ), ?_⟩
    simp only [g, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v), Matrix.one_mulVec]
  have hd0 : DenseRange (Pi.map (fun _ : ι => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v hv)
  have hd : DenseRange (fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι)) := by
    have h1 : DenseRange (g ∘ Pi.map (fun _ : ι => (v.embedding : K → ℂ))) := hgs.denseRange.comp hd0 hgc
    have h2 : DenseRange ((g ∘ Pi.map (fun _ : ι => (v.embedding : K → ℂ))) ∘ (b.equivFun : V → ι → K)) := by
      rw [DenseRange, b.equivFun.surjective.range_comp]
      exact h1
    exact h2
  have hbound : ∀ ξ : EuclideanSpace ℂ ι, ‖T ξ‖ ≤ Real.sqrt c * ‖ξ‖ := by
    intro ξ
    induction ξ using hd.induction_on with
    | hp => exact isClosed_le (T.continuous.norm) (continuous_const.mul continuous_norm)
    | ih x =>
      have h1 : T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x)) = WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b' X' v (φ x)) := by
        rw [Formalism.HN.PlaceOperatorNorms.fcoord_map b X b' X' hX v φ x]
        rfl
      rw [h1, ← Formalism.HN.PlaceOperatorNorms.cnorm_eq, ← Formalism.HN.PlaceOperatorNorms.cnorm_eq]
      have h2 := h x
      rw [← normAt_sq_eq_majAt, ← normAt_sq_eq_majAt] at h2
      have h3 : Formalism.HermitianLatticesTheory.normAt b' X' v (φ x) ≤ Real.sqrt c * Formalism.HermitianLatticesTheory.normAt b X v x := by
        apply abs_le_of_sq_le_sq' _ (mul_nonneg (Real.sqrt_nonneg _) (normAt_nonneg _ _ _ _)) |>.2
        rw [mul_pow, Real.sq_sqrt hc]
        exact h2
      exact h3
  have hle : ‖T‖ ≤ Real.sqrt c := T.opNorm_le_bound (Real.sqrt_nonneg _) hbound
  calc Formalism.HN.opNormAt b X b' X' v φ ^ 2 = ‖T‖ ^ 2 := rfl
    _ ≤ Real.sqrt c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = c := Real.sq_sqrt hc

theorem hNeZero_of_hP_ne_zero (D : D7) (p : ℕ) (hp : p.Prime) (hc : Formalism.MainNotions.G.IsResidueClassZero D p)
    (h : Formalism.MainNotions.G.HEv D p) : HNeZero D.host p := by
  have hc' : primeClass D.host.toHostRaw p = PrimeClass.inertClass := hc
  have : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p D.host.condN := hp.coprime_iff_not_dvd.2 (not_dvd_conductor_of_inert hp hc')
  intro P _ _ σ hσ
  have hne : ∃ g, g ∈ Formalism.MainNotions.G.frobSet D p := ⟨_, P, inferInstance, inferInstance, σ, hσ, rfl⟩
  obtain ⟨P₀, hP₀, hL₀, σ₀, hσ₀, hg₀⟩ := Classical.epsilon_spec hne
  have e1 := (D.host.frob_iff p hcop P σ).1 hσ
  have e2 := (D.host.frob_iff p hcop P₀ σ₀).1 hσ₀
  have h2 : (D.host.galE σ).2 = D.R.iota (Formalism.MainNotions.G.hP D p) := by
    unfold Formalism.MainNotions.G.hP
    rw [Formalism.HC.Frame.iota_iotaInv, ← hg₀, e1, e2]
  rw [h2, Formalism.HC.Frame.orderOf_iota]
  exact h

private theorem hEv_of_large_order {D : D7} (L : SizeData₂ D) (p : ℕ)
    (hx : L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (Formalism.MainNotions.G.hP D p) : ℝ)) : Formalism.MainNotions.G.HEv D p := by
  by_contra hne
  have ho : Odd (addOrderOf (Formalism.MainNotions.G.hP D p)) := Nat.not_even_iff_odd.1 hne
  have hcop : Nat.Coprime (addOrderOf (Formalism.MainNotions.G.hP D p)) (2 ^ D.R.toFrame.e) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 ho)
  have h0 : D.R.toFrame.h (Formalism.MainNotions.G.hP D p) = 0 := AddMonoid.addOrderOf_eq_one_iff.1
    (Nat.eq_one_of_dvd_coprimes hcop (D.R.toFrame.addOrderOf_h_dvd _) (D.R.toFrame.addOrderOf_h_dvd_two_pow _))
  have hle : addOrderOf (Formalism.MainNotions.G.hP D p) ≤ D.R.toFrame.o := Nat.le_of_dvd D.R.toFrame.o_pos
    (addOrderOf_dvd_iff_nsmul_eq_zero.2 (D.R.toFrame.o_nsmul_of_h_eq_zero h0))
  have hle' : (addOrderOf (Formalism.MainNotions.G.hP D p) : ℝ) ≤ (D.R.o : ℝ) := by exact_mod_cast hle
  have hlt : L.sc.x ^ (L.sc.eps / 100) < L.sc.x ^ (L.sc.eps / 4) :=
    Real.rpow_lt_rpow_of_exponent_lt L.sc.one_lt_alt (by linarith [L.sc.eps_pos])
  linarith [L.o_tie]

theorem gIdx_of_cand {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (K : Formalism.MainNotions.G.Consts)
    (h3 : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) (u : D.what₂.Word) (p : ℕ) (hc : Formalism.MainNotions.G.Cand D L K p)
    (hpT : p ≠ (D.mem u).A.T) : GIdx D.host (D.mem u).A.T p := by
  obtain ⟨hp, _, hc0, hord, _⟩ := hc
  have hc0' : primeClass D.host.toHostRaw p = PrimeClass.inertClass := hc0
  obtain ⟨hs, -, -, hjne, -⟩ := (primeClass_eq_inert_iff D.host.toHostRaw).1 hc0'
  have hne2 : p ≠ 2 := by rintro rfl; exact hs D.host.two_mem_small
  refine ⟨hp, ?_, hc0, hNeZero_of_hP_ne_zero D p hp hc0 (hEv_of_large_order L p hord), fun h => ?_, ?_⟩
  · by_contra h
    have hp3 : p = 3 := by
      have h5 : p < 5 := not_le.1 h
      have h2 := hp.two_le
      interval_cases p
      · exact absurd rfl hne2
      · rfl
      · exact absurd hp (by norm_num)
    have hp4 : p ≤ D.host.splitBound := by
      rw [hp3]
      exact le_trans (Nat.le_floor (by exact_mod_cast h3)) L.split_tie
    exact hjne (D.host.split_small p hp hne2 hp4)
  · have := P.level_split p h
    rw [show D.host.cls p = PrimeClass.inertClass from hc0] at this
    cases this
  · exact fun h => hpT ((Nat.prime_dvd_prime_iff_eq hp (D.mem u).A.T_prime).1 h)

theorem InLoc.inf_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) (x : V) :
    InLoc w (A ⊓ B) x ↔ InLoc w A x ∧ InLoc w B x := by
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    exact ⟨⟨s, hs, h1⟩, ⟨s, hs, h2⟩⟩
  · rintro ⟨⟨s, hs, h1⟩, ⟨t, ht, h2⟩⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_, ?_⟩
    · rw [mul_comm, mul_smul]; exact A.smul_mem _ h1
    · rw [mul_smul]; exact B.smul_mem _ h2

theorem InLoc.map_iff {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module (𝓞 K) V]
    [AddCommGroup W] [Module (𝓞 K) W] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ψ : V →ₗ[𝓞 K] W)
    (hψ : Function.Injective ψ) (A : Submodule (𝓞 K) V) (x : V) :
    InLoc w (A.map ψ) (ψ x) ↔ InLoc w A x := by
  constructor
  · rintro ⟨s, hs, y, hy, h⟩
    rw [← map_smul] at h
    exact ⟨s, hs, hψ h ▸ hy⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, s • x, h, map_smul _ _ _⟩

namespace D7

open IsDedekindDomain

variable (D : D7)

theorem intW_eq (w : D.what₂.places.Pl) :
    intW D.what₂.places w = ((D.plEq w).valuation D.what₂.LL).valuationSubring.toSubring := by
  ext x
  exact D.val_nonneg_iff w x

theorem intW_dvr (w : D.what₂.places.Pl) : IsDiscreteValuationRing (intW D.what₂.places w) := by
  rw [D.intW_eq w, ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 D.what₂.LL) (D.plEq w).ne_bot
    (HeightOneSpectrum.valuationSubringAtPrime D.what₂.LL (D.plEq w))

theorem intW_frac (w : D.what₂.places.Pl) : IsFractionRing (intW D.what₂.places w) D.what₂.LL := by
  rw [D.intW_eq w]
  exact inferInstanceAs (IsFractionRing ((D.plEq w).valuation D.what₂.LL).valuationSubring D.what₂.LL)

theorem Sram_eq (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    LT.Sram D u w = locW D.what₂.places w (D.fm u).ramL := by
  ext y
  rw [D.mem_locW_iff]
  unfold LT.Sram MemberForms.S
  rw [Submodule.mem_inf, D.mem_locW_iff]
  constructor
  · rintro ⟨⟨s, hs, h1⟩, h2⟩
    refine ⟨s, hs, h1, ?_⟩
    have h3 : y ∈ (D.fm u).ramSub := h2
    show s • y ∈ (D.fm u).ramSub
    rw [← algebraMap_smul D.what₂.LL s y]
    exact Submodule.smul_mem _ _ h3
  · rintro ⟨s, hs, h1, h2⟩
    refine ⟨⟨s, hs, h1⟩, ?_⟩
    have h3 : s • y ∈ (D.fm u).ramSub := h2
    have hs0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by
      intro h0
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL) (h0.trans (map_zero _).symm)
      exact hs (this ▸ (D.plEq w).asIdeal.zero_mem)
    rw [← algebraMap_smul D.what₂.LL s y] at h3
    exact ((D.fm u).ramSub.smul_mem_iff hs0).1 h3

theorem lenLoc_atT {L : SizeData₂ D} (hAtT : NuAtTDef D L) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) :
    DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) =
      Module.length (LT.Ow D w) (↥(LT.Sram D u w) ⧸ (LT.Nlam D u w).comap (LT.Sram D u w).subtype) := by
  haveI := D.intW_dvr w
  haveI := D.intW_frac w
  have hσ : ∀ x : D.what₂.LL, (D.plEq w).valuation D.what₂.LL x ≤ 1 ↔
      (RingHom.id D.what₂.LL) x ∈ Set.range (algebraMap (intW D.what₂.places w) D.what₂.LL) := by
    intro x
    rw [← D.val_nonneg_iff w x]
    constructor
    · exact fun h => ⟨⟨x, h⟩, rfl⟩
    · rintro ⟨c, hc⟩
      have hc' : (c : D.what₂.LL) = x := hc
      rw [← hc']
      exact c.2
  have key := FBC.length_valuationRing (D.plEq w) (RingHom.id D.what₂.LL) hσ (fun c => ⟨c, rfl⟩)
    (D.nuIn u).toAddMonoidHom (fun a x => map_smul (D.nuIn u) a x) (D.div.Nu u).b
    ((D.div.Nu u).b.linearIndependent.map' (D.nuIn u) (LinearMap.ker_eq_bot.2 (D.nuIn_inj u)))
    (L.NuLat u ⊓ DV.MramL D u) (DV.MramL D u) inf_le_right
  have hcomap : (L.NuLat u ⊓ DV.MramL D u).comap (DV.MramL D u).subtype = (L.NuLat u).comap (DV.MramL D u).subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  rw [hcomap] at key
  have key' : _ = DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) := key
  rw [← key']
  have hA : Submodule.span (intW D.what₂.places w) ((D.nuIn u).toAddMonoidHom '' (DV.MramL D u : Set (D.div.Nu u).V)) =
      LT.Sram D u w := by
    rw [D.Sram_eq u w, ← D.MramL_map u]
    rfl
  have hB : Submodule.span (intW D.what₂.places w) ((D.nuIn u).toAddMonoidHom ''
      ((L.NuLat u ⊓ DV.MramL D u : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Set (D.div.Nu u).V)) =
      LT.Nlam D u w ⊓ LT.Sram D u w := by
    have h1 : Submodule.span (intW D.what₂.places w) ((D.nuIn u).toAddMonoidHom ''
        ((L.NuLat u ⊓ DV.MramL D u : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Set (D.div.Nu u).V)) =
        locW D.what₂.places w ((L.NuLat u ⊓ DV.MramL D u).map ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL))) := rfl
    rw [h1]
    ext y
    rw [D.mem_locW_iff, Submodule.mem_inf, D.Sram_eq u w, D.mem_locW_iff, ← D.MramL_map u]
    have hinj : Function.Injective ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) := D.nuIn_inj u
    have hrange : ∀ (A : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V),
        InLoc (D.plEq w) (A.map ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL))) y → ∃ x, D.nuIn u x = y := by
      rintro A ⟨s, hs, x, -, hx⟩
      have hs0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by
        intro h0
        have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL) (h0.trans (map_zero _).symm)
        exact hs (this ▸ (D.plEq w).asIdeal.zero_mem)
      refine ⟨(algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ • x, ?_⟩
      have hx' : D.nuIn u x = s • y := hx
      rw [map_smul, hx', ← algebraMap_smul D.what₂.LL s y, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    constructor
    · intro h
      obtain ⟨x, rfl⟩ := hrange _ h
      have h2 := (InLoc.map_iff (D.plEq w) _ hinj _ x).1 h
      rw [InLoc.inf_iff] at h2
      exact ⟨(hAtT u w hw x).1 h2.1, (InLoc.map_iff (D.plEq w) _ hinj _ x).2 h2.2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨x, rfl⟩ := hrange _ h2
      apply (InLoc.map_iff (D.plEq w) _ hinj _ x).2
      rw [InLoc.inf_iff]
      exact ⟨(hAtT u w hw x).2 h1, (InLoc.map_iff (D.plEq w) _ hinj _ x).1 h2⟩
  rw [FBC.length_congr hA hB, Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]

end D7

end Formalism.BasicNotions

end
