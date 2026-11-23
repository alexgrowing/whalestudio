import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UltrametricCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationMapMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain)
open GlobalTheory.ChainPts.PullHT (pullA)
open scoped TensorProduct
open GlobalTheory.ChainPts

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ChainPts.LatLie

open GlobalTheory.ChainPts.FrameNorm
open GlobalTheory.Twist (resM_resM resM_smul app_resM)
open GlobalTheory.VB (IsFrame)

theorem mono_comp_of_exact {C : Type*} [Category C] [Abelian C] {I P Q E E' : C} (ι : I ⟶ P) (f : P ⟶ Q) (g : P ⟶ E)
    (k : E' ⟶ P) (hk : k ≫ f = 0) (hι : ι ≫ g = 0) (ex : (ShortComplex.mk k f hk).Exact) [Mono ι] [Mono (k ≫ g)] :
    Mono (ι ≫ f) := by
  refine Preadditive.mono_of_cancel_zero _ fun {T} x hx => ?_
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at ex
  obtain ⟨T₁, q, hq, y, hy⟩ := ex (x ≫ ι) (by simpa using hx)
  dsimp at hy y
  have h0 : y = 0 := by
    rw [← cancel_mono (k ≫ g), ← Category.assoc, ← hy, Category.assoc, Category.assoc, hι, comp_zero, comp_zero, zero_comp]
  rw [← cancel_epi q, ← cancel_mono ι, Category.assoc, hy, h0, zero_comp, comp_zero, zero_comp]

theorem mono_pullback_map_of_isIso {X Y : Scheme.{0}} [IsIntegral Y] (w : Y ⟶ X) {E E' : X.Modules} {r : ℕ}
    (h : GlobalTheory.VB.IsVB E' r) (ψ : E' ⟶ E) (U : X.Opens) [IsIso ((Scheme.Modules.pullback U.ι).map ψ)] (y : Y) (hy : w y ∈ U) :
    Mono ((Scheme.Modules.pullback w).map ψ) := by
  let e : Scheme.Modules.pullback w ⋙ Scheme.Modules.pullback (w ⁻¹ᵁ U).ι ≅
      Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (w.resLE U (w ⁻¹ᵁ U) le_rfl) :=
    Scheme.Modules.pullbackComp _ w ≪≫ Scheme.Modules.pullbackCongr (w.resLE_comp_ι le_rfl).symm ≪≫
      (Scheme.Modules.pullbackComp _ _).symm
  haveI : IsIso ((Scheme.Modules.pullback (w ⁻¹ᵁ U).ι).map ((Scheme.Modules.pullback w).map ψ)) :=
    (NatIso.isIso_map_iff e ψ).2 (inferInstanceAs (IsIso ((Scheme.Modules.pullback (w.resLE U (w ⁻¹ᵁ U) le_rfl)).map
      ((Scheme.Modules.pullback U.ι).map ψ))))
  exact mono_of_isIso_pullback_ι (h.pullback w).isTorsionFree _ (w ⁻¹ᵁ U) (GlobalTheory.VB.genericPoint_mem hy)

theorem exact_map_pullback_of_pres {X Y : Scheme.{0}} (w : Y ⟶ X) {A L Q E E' : X.Modules} (a : A ⟶ L) (j : L ⟶ Q)
    (h : a ≫ j = 0) (ex : (ShortComplex.mk a j h).Exact) [L.IsQuasicoherent] [Q.IsQuasicoherent] {r : ℕ}
    (vb : GlobalTheory.VB.IsVB E r) (ψ : E' ⟶ E) (e : cokernel j ≅ cokernel ψ) [Mono ((Scheme.Modules.pullback w).map ψ)] :
    ((ShortComplex.mk a j h).map (Scheme.Modules.pullback w)).Exact := by
  let c : Q ⟶ cokernel ψ := cokernel.π j ≫ e.hom
  let d := cokernel.π ψ
  have hc : kernel.ι (cokernel.π j) ≫ c = 0 := by simp [c]
  let ι : kernel (cokernel.π j) ⟶ pullback c d := pullback.lift (kernel.ι _) 0 (by simp [hc])
  let k : E' ⟶ pullback c d := pullback.lift 0 ψ (by simp [d])
  have hι : ι ≫ pullback.snd c d = 0 := pullback.lift_snd _ _ _
  have hι' : ι ≫ pullback.fst c d = kernel.ι _ := pullback.lift_fst _ _ _
  have hk : k ≫ pullback.fst c d = 0 := pullback.lift_fst _ _ _
  have hk' : k ≫ pullback.snd c d = ψ := pullback.lift_snd _ _ _
  haveI : Mono ι := mono_of_mono_fac hι'
  have s₁ : (ShortComplex.mk ι _ hι).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ this (Abelian.epi_snd_of_isLimit _ _ (limit.isLimit _))
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    dsimp at x hx
    have h1 : (x ≫ pullback.fst c d) ≫ cokernel.π j = 0 := by
      rw [← cancel_mono e.hom, zero_comp, Category.assoc, Category.assoc]
      change x ≫ pullback.fst c d ≫ c = 0
      rw [pullback.condition, ← Category.assoc, hx, zero_comp]
    refine ⟨T, 𝟙 _, inferInstance, kernel.lift _ _ h1, pullback.hom_ext ?_ ?_⟩
    · dsimp; rw [Category.id_comp, Category.assoc, hι', kernel.lift_ι]
    · dsimp; rw [Category.id_comp, Category.assoc, hι, hx, comp_zero]
  have s₂ : (ShortComplex.mk k _ hk).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    dsimp at x hx
    have h1 : (x ≫ pullback.snd c d) ≫ cokernel.π ψ = 0 := by
      rw [Category.assoc]
      change x ≫ pullback.snd c d ≫ d = 0
      rw [← pullback.condition, ← Category.assoc, hx, zero_comp]
    obtain ⟨T₁, q, hq, y, hy⟩ := (ShortComplex.exact_iff_exact_up_to_refinements _).1 (ShortComplex.exact_cokernel ψ) _ h1
    dsimp at y hy
    refine ⟨T₁, q, hq, y, pullback.hom_ext ?_ ?_⟩
    · dsimp; rw [Category.assoc, Category.assoc, hx, hk, comp_zero, comp_zero]
    · dsimp; rw [Category.assoc, Category.assoc, hk', hy]
  haveI := GlobalTheory.FlagPull.isQuasicoherent_X₂ _ s₁ vb
  haveI : Mono ((Scheme.Modules.pullback w).map ι) := GlobalTheory.FlagPull.mono_pullback_map_f w _ s₁ vb
  haveI : Epi (ShortComplex.mk k _ hk).g := Abelian.epi_fst_of_isLimit _ _ (limit.isLimit _)
  haveI : Mono ((Scheme.Modules.pullback w).map k ≫ (Scheme.Modules.pullback w).map (pullback.snd c d)) := by
    rwa [← Functor.map_comp, hk']
  have m := mono_comp_of_exact ((Scheme.Modules.pullback w).map ι) _ ((Scheme.Modules.pullback w).map (pullback.snd c d))
    ((Scheme.Modules.pullback w).map k) _ (by rw [← Functor.map_comp, hι, Functor.map_zero]) (exact_map_pullback w s₂).1
  dsimp at m
  rw [← Functor.map_comp, hι'] at m
  have h' : a ≫ Abelian.factorThruImage j = 0 := by
    rw [← cancel_mono (Abelian.image.ι j), Category.assoc, Abelian.image.fac, h, zero_comp]
  let φ : ShortComplex.mk a _ h' ⟶ ShortComplex.mk a j h :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι j, comm₁₂ := by simp, comm₂₃ := by simp }
  haveI : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 A))
  haveI : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 L))
  haveI : Mono φ.τ₃ := inferInstanceAs (Mono (Abelian.image.ι j))
  have ex' := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 ex
  haveI : Epi (ShortComplex.mk a _ h').g := inferInstanceAs (Epi (Abelian.factorThruImage j))
  let φ' := (Scheme.Modules.pullback w).mapShortComplex.map φ
  haveI : Epi φ'.τ₁ := inferInstanceAs (Epi ((Scheme.Modules.pullback w).map (𝟙 A)))
  haveI : IsIso φ'.τ₂ := inferInstanceAs (IsIso ((Scheme.Modules.pullback w).map (𝟙 L)))
  haveI : Mono φ'.τ₃ := m
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ').1 (exact_map_pullback w ex').1

section Crd

variable {X : Scheme.{0}} {F G : X.Modules} {r : ℕ} {V V' T : X.Opens}

def crd {e : Fin r → Γ(F, V)} (he : IsFrame e) (t : Γ(F, T)) (l : Fin r) : Γ(X, V ⊓ T) :=
  (he.basis inf_le_left).repr (resM F inf_le_right t) l

theorem crd_app (φ : F ⟶ G) {e : Fin r → Γ(F, V)} (he : IsFrame e) (he' : IsFrame fun i => φ.app V (e i)) (t : Γ(F, T))
    (l : Fin r) : crd he' (φ.app T t) l = crd he t l := by
  unfold crd
  rw [← app_resM]
  conv_lhs => rw [← (he.basis inf_le_left).sum_repr (resM F inf_le_right t)]
  simp only [map_sum, Scheme.Modules.Hom.app_smul, IsFrame.basis_apply, app_resM]
  simp only [← he'.basis_apply (inf_le_left : V ⊓ T ≤ V)]
  rw [← map_sum, Module.Basis.repr_sum_self]

def valR {R : Type} [CommRing R] (w : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (w.appLE U ⊤ h).hom

theorem map_valR {R k : Type} [CommRing R] [Field k] (f : R →+* k) (w : Sp R ⟶ X) (U : X.Opens) (hw : ⊤ ≤ w ⁻¹ᵁ U)
    (a : Γ(X, U)) : f (valR w U hw a) = valF (spMap f ≫ w) U a := by
  have h' : ⊤ ≤ (spMap f ≫ w) ⁻¹ᵁ U := fun q _ => hw (Set.mem_univ (spMap f q))
  rw [valF, dif_pos h']
  have e : (spMap f ≫ w).appLE U ⊤ h' = w.appLE U ⊤ hw ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap f) w U ⊤ ⊤ hw le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  rw [e]
  exact (congrArg (fun q => q.hom ((w.appLE U ⊤ hw).hom a)) n).symm

variable {k : Type} [Field k] (x : Sp k ⟶ X)

theorem valF_crd_app (φ : F ⟶ G) {e : Fin r → Γ(F, V)} {e' : Fin r → Γ(G, V')} (he : IsFrame e) (he' : IsFrame e')
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (hV' : ⊤ ≤ x ⁻¹ᵁ V') (hT : ⊤ ≤ x ⁻¹ᵁ T) (t : Γ(F, T)) (m : Fin r) :
    valF x _ (crd he' (φ.app T t) m) = ∑ l, valF x _ (crd he' (φ.app V (e l)) m) * valF x _ (crd he t l) := by
  have hU : ⊤ ≤ x ⁻¹ᵁ (V ⊓ (V' ⊓ T)) := fun q hq => ⟨hV hq, hV' hq, hT hq⟩
  have h₀ : V ⊓ (V' ⊓ T) ≤ V' ⊓ T := inf_le_right
  have h₁ : V ⊓ (V' ⊓ T) ≤ V' ⊓ V := le_inf (h₀.trans inf_le_left) inf_le_left
  have h₂ : V ⊓ (V' ⊓ T) ≤ V ⊓ T := inf_le_inf_left _ inf_le_right
  simp only [← valHom_resG x h₀ hU, ← valHom_resG x h₁ hU, ← valHom_resG x h₂ hU, ← map_mul, ← map_sum]
  congr 1
  simp only [crd, ← IsFrame.repr_resM, resM_resM]
  rw [← app_resM]
  conv_lhs => rw [← (he.basis inf_le_left).sum_repr (resM F (h₀.trans inf_le_right) t)]
  simp only [map_sum, Scheme.Modules.Hom.app_smul, IsFrame.basis_apply, app_resM, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem valF_crd_smul (π : Γ(X, ⊤)) {e : Fin r → Γ(F, V)} (he : IsFrame e) (hV : ⊤ ≤ x ⁻¹ᵁ V) (hT : ⊤ ≤ x ⁻¹ᵁ T)
    (t : Γ(F, T)) (m : Fin r) : valF x _ (crd he ((smulHom F π).app T t) m) = valF x ⊤ π * valF x _ (crd he t m) := by
  have hU : ⊤ ≤ x ⁻¹ᵁ (V ⊓ T) := fun q hq => ⟨hV hq, hT hq⟩
  rw [← valHom_resG x (le_top : V ⊓ T ≤ ⊤) hU, valF_eq_valHom _ _ hU, valF_eq_valHom _ _ hU, ← map_mul]
  congr 1
  unfold crd
  rw [← app_resM, smulHom_app_apply, map_smul]
  rfl

theorem valF_crd_self {e : Fin r → Γ(F, V)} (he : IsFrame e) (hV : ⊤ ≤ x ⁻¹ᵁ V) (l m : Fin r) :
    valF x _ (crd he (e l) m) = if l = m then 1 else 0 := by
  have hU : ⊤ ≤ x ⁻¹ᵁ (V ⊓ V) := fun q hq => ⟨hV hq, hV hq⟩
  rw [valF_eq_valHom _ _ hU]
  unfold crd
  erw [← he.basis_apply inf_le_left, Module.Basis.repr_self_apply]
  split_ifs <;> simp

theorem mem_kerAt_iff {R : Type} [CommRing R] (w : Sp R ⟶ X) {Q : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (a : F ⟶ G) (j : G ⟶ Q)
    (ex : Function.Exact (((Scheme.Modules.pullback w).map a).app ⊤) (((Scheme.Modules.pullback w).map j).app ⊤))
    {e : Fin r → Γ(G, V)} {e' : Fin r → Γ(F, V')} (he : IsFrame e) (he' : IsFrame e') (hV : ⊤ ≤ w ⁻¹ᵁ V) (hV' : ⊤ ≤ w ⁻¹ᵁ V')
    (hU : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V')) (c : Fin r → R) :
    c ∈ kerAt w j hV e ↔ ∃ b : Fin r → R, ∀ l, c l = ∑ m, valR w _ hU (crd he (a.app V' (e' m)) l) * b m := by
  let g := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let β := (he.pullback w).basis hV
  let β' := (he'.pullback w).basis hV'
  have hβ : ∀ l, pullbackSections w G hV (e l) = β l := fun l => by
    rw [IsFrame.basis_apply]; exact (res_pullbackSections w G le_rfl hV (e l)).symm
  have hβ' : ∀ l, β' l = pullbackSections w F hV' (e' l) := fun l => by
    rw [IsFrame.basis_apply]; exact res_pullbackSections w F le_rfl hV' (e' l)
  have key : ∀ u l, g (β.repr (((Scheme.Modules.pullback w).map a).app ⊤ u) l) =
      ∑ m, valR w _ hU (crd he (a.app V' (e' m)) l) * g (β'.repr u m) := fun u l => by
    conv_lhs => rw [← β'.sum_repr u]
    simp only [map_sum, Scheme.Modules.Hom.app_smul, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      map_mul, hβ', pullback_map_app_pullbackSections]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm, ← pullbackSections_res w G hU inf_le_right]
    exact congrArg (fun z => g z * _) (he.pullback_basis_repr w inf_le_left hU _ l)
  have hc : ∀ (c : Fin r → R) l, g (β.repr (∑ l, g.symm (c l) • β l) l) = c l := fun c l => by
    rw [Module.Basis.repr_sum_self, RingEquiv.apply_symm_apply]
  change ((Scheme.Modules.pullback w).map j).app ⊤ (∑ l, g.symm (c l) • pullbackSections w G hV (e l)) = 0 ↔ _
  simp only [hβ]
  rw [ex]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨fun m => g (β'.repr u m), fun l => by rw [← key, hu, hc]⟩
  · rintro ⟨b, hb⟩
    refine ⟨∑ m, g.symm (b m) • β' m, β.repr.injective (Finsupp.ext fun l => g.injective ?_)⟩
    rw [hc, key, hb]
    simp only [Module.Basis.repr_sum_self, RingEquiv.apply_symm_apply]

end Crd

theorem isFrame_app_of_isIso {X : Scheme.{0}} {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens)
    (hf : IsIso ((Scheme.Modules.pullback U.ι).map φ)) {T : X.Opens} (hT : T ≤ U) {r : ℕ} {e : Fin r → Γ(F, T)}
    (he : IsFrame e) : IsFrame fun i => φ.app T (e i) := by
  have hr : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) φ).2 hf
  have hb : ∀ D ≤ T, Function.Bijective (φ.app D) := fun D hD => by
    have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ D) = D := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 (hD.trans hT)]
    rw [← e]
    exact ConcreteCategory.bijective_of_isIso (((Scheme.Modules.restrictFunctor U.ι).map φ).app (U.ι ⁻¹ᵁ D))
  exact he.map_of_linearEquiv (fun V h => LinearEquiv.ofBijective (appLinear φ V) (hb V h)) fun _ h i => app_resM φ h (e i)

theorem norm_iff_mem_kerAt {X : Scheme.{0}} {A L Q : X.Modules} [A.IsQuasicoherent] [L.IsQuasicoherent] (ψ : L ⟶ A)
    (a : A ⟶ L) (j : L ⟶ Q) (π : Γ(X, ⊤)) (h₁ : ψ ≫ a = smulHom L π) (h₂ : a ≫ ψ = smulHom A π) {C : Type}
    [NontriviallyNormedField C] [IsUltrametricDist C] (w : Sp ↥(intO C) ⟶ X)
    (ex : Function.Exact (((Scheme.Modules.pullback w).map a).app ⊤) (((Scheme.Modules.pullback w).map j).app ⊤))
    (hπ : valF (spMap (intO C).subtype ≫ w) ⊤ π ≠ 0) {r : ℕ} {V V' T : X.Opens} {e : Fin r → Γ(L, V)}
    {e' : Fin r → Γ(A, V')} (he : IsFrame e) (he' : IsFrame e') (hV : ⊤ ≤ w ⁻¹ᵁ V) (hV' : ⊤ ≤ w ⁻¹ᵁ V')
    (hT : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ T) (s : Fin r → Γ(L, T)) (cf : Fin r → C) :
    (∃ c ∈ kerAt w j hV e, ∀ l, (c l : C) = valF (spMap (intO C).subtype ≫ w) ⊤ π *
      ∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (crd he (s i) l)) ↔
    ∀ l, ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (crd he' (ψ.app T (s i)) l)‖ ≤ 1 := by
  have hU : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V') := fun q hq => ⟨hV hq, hV' hq⟩
  have hx : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ V := fun q _ => hV (Set.mem_univ (spMap (intO C).subtype q))
  have hx' : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ V' := fun q _ => hV' (Set.mem_univ (spMap (intO C).subtype q))
  have hval := fun l m => map_valR (intO C).subtype w _ hU (crd he (a.app V' (e' m)) l)
  simp only [mem_kerAt_iff w a j ex he he' hV hV' hU]
  generalize spMap (intO C).subtype ≫ w = x at hπ hT hx hx' hval ⊢
  have k₁ : ∀ l, valF x ⊤ π * ∑ i, cf i * valF x _ (crd he (s i) l) =
      ∑ m, valF x _ (crd he (a.app V' (e' m)) l) * ∑ i, cf i * valF x _ (crd he' (ψ.app T (s i)) m) := fun l => by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, ← valF_crd_smul x π he hx hT, ← h₁]
    change _ * valF x _ (crd he (a.app T (ψ.app T (s i))) l) = _
    rw [valF_crd_app x a he' he hx' hx hT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => mul_left_comm _ _ _
  have k₂ : ∀ (b : Fin r → C) n, ∑ l, valF x _ (crd he' (ψ.app V (e l)) n) *
      ∑ m, valF x _ (crd he (a.app V' (e' m)) l) * b m = valF x ⊤ π * b n := fun b n => by
    have : ∀ m, ∑ l, valF x _ (crd he' (ψ.app V (e l)) n) * valF x _ (crd he (a.app V' (e' m)) l) =
        valF x ⊤ π * if m = n then 1 else 0 := fun m => by
      rw [← valF_crd_app x ψ he he' hx hx' hx', ← valF_crd_self x he' hx', ← valF_crd_smul x π he' hx' hx', ← h₂]
      rfl
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, this]
    simp
  simp only [k₁]
  constructor
  · rintro ⟨c, ⟨b, hb⟩, hc⟩ n
    have : ∑ i, cf i * valF x _ (crd he' (ψ.app T (s i)) n) = (b n : C) := by
      refine mul_left_cancel₀ hπ ?_
      rw [← k₂ (fun m => ∑ i, cf i * valF x _ (crd he' (ψ.app T (s i)) m)), ← k₂ fun m => (b m : C)]
      refine Finset.sum_congr rfl fun l _ => congrArg _ ?_
      rw [← hc, hb]
      change (intO C).subtype _ = _
      simp only [map_sum, map_mul, hval]
      rfl
    rw [this]
    exact (b n).2
  · intro H
    refine ⟨_, ⟨fun m => ⟨_, H m⟩, fun _ => rfl⟩, fun l => ?_⟩
    change (intO C).subtype _ = _
    simp only [map_sum, map_mul, hval]
    rfl

theorem isEqLatPres_of_ptJ : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [CharP (ResidueField O) p] {B : GlobalTheory.Vert.Model O} (h : B.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (lw : EPres B (𝓞 E)) (wl : lw.E ⟶ lw.E') (π : Γ(B.X, ⊤)) (P₁ P₃ : Pres B) (j : lw.E'.V ⟶ P₁.mod) (hj : wl.hom ≫ j = 0) (s : ∀ a : Fin Z.m, Fin r → Γ(lw.E'.V, h ⁻¹ᵁ (Z.U a).1)) (hs : IsEqLat Z h x false lw.E' s), lw.r = r → IsRootOfP p π (p - 1) → lw.ψ ≫ wl = smulA _ π → Mono wl.hom → (ShortComplex.mk wl.hom j hj).Exact → Nonempty (cokernel j ≅ P₃.mod) → PtJ Z h x hs.2.2.1.frame π j → IsEqLatPres Z h x false lw := by
  intro E _ _ _ H Dw Xo p _ W Y i₀ Z O _ _ _ _ _ B h r x lw wl π P₁ P₃ j hj s hs hr hroot hψ hm ex ⟨eC⟩ hJ
  have hgen : ∀ a, h ⁻¹ᵁ (Z.U a).1 ≤ B.gen := fun a => by
    rw [B.gen_eq_basicOpen (natCast_ne_zero O p) (natCast_mem_maximalIdeal O p)]
    refine le_basicOpen_of_isUnit le_top ?_
    rw [show B.const (p : O) = (p : Γ(B.X, ⊤)) from map_natCast _ p, map_natCast, ← map_natCast ((h.app (Z.U a).1).hom.comp (Z.alg a))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)).map _
  have fr : ∀ a, IsFrame fun i => lw.ψ.hom.app _ (s a i) := fun a =>
    isFrame_app_of_isIso _ B.gen lw.iso (hgen a) (hs.2.2.1.frame a)
  refine ⟨hr, s, hs.2.2.1, ⟨fr, fun k _ w a a' φ φ' h1 h2 i => ?_, fun y w hw a φ hφ V' e' he' hV' cf v hv => ?_⟩, hs.2.2.2⟩
  · have := fun l => crd_app lw.ψ.hom (hs.2.2.1.frame a) (fr a) (s a' i) l
    change IsCombAtG _ _ _ (fun l => valF w _ (crd (fr a) (lw.ψ.hom.app _ (s a' i)) l)) _
    simp only [this]
    exact hs.2.2.1.glue k w a a' φ φ' h1 h2 i
  · obtain ⟨V, e, he, hV, hJ⟩ := hJ y w hw a φ hφ
    haveI := lw.vb.isQuasicoherent
    haveI := lw.vb'.isQuasicoherent
    haveI := P₁.vb.isQuasicoherent
    haveI := P₁.vb'.isQuasicoherent
    haveI : P₁.mod.IsQuasicoherent := inferInstanceAs (cokernel P₁.ψ).IsQuasicoherent
    haveI := P₃.iso
    have hT : ⊤ ≤ (spMap (intO ↥y.C.S).subtype ≫ w) ⁻¹ᵁ h ⁻¹ᵁ (Z.U a).1 := fun q _ => by
      have e : (spMap (intO ↥y.C.S).subtype ≫ w) ≫ h = spMap φ ≫ Z.chart a := by rw [hφ, Category.assoc, hw]; rfl
      change ((spMap (intO ↥y.C.S).subtype ≫ w) ≫ h) q ∈ (Z.U a).1
      rw [e]
      exact (Z.U a).2.opensRange_fromSpec.le ⟨_, rfl⟩
    haveI := mono_pullback_map_of_isIso w P₃.vb' P₃.ψ B.gen (spMap (intO ↥y.C.S).subtype (closedPoint _))
      (hgen a (hT (Set.mem_univ (closedPoint _))))
    have ex' := exact_map_pullback_of_pres w wl.hom j hj ex P₃.vb P₃.ψ eC
    haveI : ((ShortComplex.mk wl.hom j hj).map (Scheme.Modules.pullback w)).X₁.IsQuasicoherent :=
      isQuasicoherent_pullback w lw.E.V
    haveI : ((ShortComplex.mk wl.hom j hj).map (Scheme.Modules.pullback w)).X₂.IsQuasicoherent :=
      isQuasicoherent_pullback w lw.E'.V
    haveI : ((ShortComplex.mk wl.hom j hj).map (Scheme.Modules.pullback w)).X₃.IsQuasicoherent :=
      isQuasicoherent_pullback w P₁.mod
    have h₁ : lw.ψ.hom ≫ wl.hom = smulHom _ π := congrArg Action.Hom.hom hψ
    have h₂ : wl.hom ≫ lw.ψ.hom = smulHom _ π := by
      rw [← cancel_mono wl.hom, Category.assoc, h₁, smulHom_comp]
    have hπ : valF (spMap (intO ↥y.C.S).subtype ≫ w) ⊤ π ≠ 0 := fun h0 => by
      obtain ⟨u, hu⟩ := hroot
      rw [valF_eq_valHom _ _ le_top] at h0
      have := congrArg (valHom (spMap (intO ↥y.C.S).subtype ≫ w) ⊤ le_top) hu
      rw [map_pow, h0, zero_pow (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt), map_mul, map_natCast,
        ← map_natCast (φ.comp (Z.alg a))] at this
      exact mul_ne_zero (u.isUnit.map _).ne_zero
        ((map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) this.symm
    exact (hJ cf v hv).trans (norm_iff_mem_kerAt lw.ψ.hom wl.hom j π h₁ h₂ w (exact_app_of_exact ex' (isAffineOpen_top _)) hπ
      he he' hV hV' hT (s a) cf)

end GlobalTheory.ChainPts.LatLie

end
