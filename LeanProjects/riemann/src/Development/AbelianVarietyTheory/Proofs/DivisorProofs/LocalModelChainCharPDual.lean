import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UltrametricCoefficientBound
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationExtensionClosed
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

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ChainPts.KerOm

open GlobalTheory.VB (IsFrame IsVB)
open GlobalTheory.Twist (resM_resM app_resM resM_smul)
open GlobalTheory.ChainPts.FrameNorm (valHom valF_eq_valHom valHom_resG)

section Sheaf

variable {X : Scheme.{0}} {F' F Q : X.Modules} {r : ℕ}

theorem repr_app (ψ : F' ⟶ F) {U V : X.Opens} {s' : Fin r → Γ(F', U)} {s : Fin r → Γ(F, U)} (hs' : IsFrame s')
    (hs : IsFrame s) (e : ∀ i, ψ.app U (s' i) = s i) (h : V ≤ U) (u : Γ(F', V)) (i : Fin r) :
    (hs.basis h).repr (ψ.app V u) i = (hs'.basis h).repr u i := by
  have k : ψ.app V u = ∑ j, (hs'.basis h).repr u j • hs.basis h j := by
    conv_lhs => rw [← (hs'.basis h).sum_repr u]
    rw [← appLinear_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, appLinear_apply, IsFrame.basis_apply, IsFrame.basis_apply, app_resM, e]
  rw [k, Module.Basis.repr_sum_self]

def evAt {R : Type} [CommRing R] (w : Sp R ⟶ X) {V : X.Opens} (hV : ⊤ ≤ w ⁻¹ᵁ V) : Γ(X, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (w.appLE V ⊤ hV).hom

theorem inv_evAt {R : Type} [CommRing R] (w : Sp R ⟶ X) {V : X.Opens} (hV : ⊤ ≤ w ⁻¹ᵁ V) (a : Γ(X, V)) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (evAt w hV a) = (w.appLE V ⊤ hV).hom a :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply _

theorem coe_evAt (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (w : Sp ↥(intO C) ⟶ X) {U : X.Opens} (hw : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) :
    (evAt w hw a : C) = valF (spMap (intO C).subtype ≫ w) U a := by
  have h' : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ U := fun q _ => hw (Set.mem_univ (spMap (intO C).subtype q))
  rw [valF, dif_pos h']
  have e : (spMap (intO C).subtype ≫ w).appLE U ⊤ h' = w.appLE U ⊤ hw ≫ (spMap (intO C).subtype).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (intO C).subtype) w U ⊤ ⊤ hw le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (intO C).subtype)
  have n' := congrArg (fun q => q.hom ((w.appLE U ⊤ hw).hom a)) n
  rw [e]
  exact n'.symm

variable {R : Type} [CommRing R] (w : Sp R ⟶ X) (ψ : F' ⟶ F) {V V' : X.Opens} (hle : V' ≤ V)
  {e : Fin r → Γ(F, V)} (he : IsFrame e) (e' : Fin r → Γ(F', V'))

def mat (k l : Fin r) : Γ(X, V') := (he.basis hle).repr (ψ.app V' (e' l)) k

theorem app_eq_sum (l : Fin r) : ψ.app V' (e' l) = ∑ k, mat ψ hle he e' k l • resM F hle (e k) := by
  conv_lhs => rw [← (he.basis hle).sum_repr (ψ.app V' (e' l))]
  simp only [mat, IsFrame.basis_apply]

theorem pull_app (hV : ⊤ ≤ w ⁻¹ᵁ V) (hV' : ⊤ ≤ w ⁻¹ᵁ V') (l : Fin r) :
    ((Scheme.Modules.pullback w).map ψ).app ⊤ (pullbackSections w F' hV' (e' l)) =
      ∑ k, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (evAt w hV' (mat ψ hle he e' k l)) •
        pullbackSections w F hV (e k) := by
  rw [pullback_map_app_pullbackSections, app_eq_sum ψ hle he, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pullbackSections_smul, inv_evAt]
  congr 1
  exact pullbackSections_res w F hV' hle (e k)

theorem col_mem {ρ : F ⟶ Q} (h0 : ψ ≫ ρ = 0) (hV : ⊤ ≤ w ⁻¹ᵁ V) (hV' : ⊤ ≤ w ⁻¹ᵁ V') (l : Fin r) :
    (fun k => evAt w hV' (mat ψ hle he e' k l)) ∈ kerAt w ρ hV e := by
  change ((Scheme.Modules.pullback w).map ρ).app ⊤ _ = 0
  rw [← pull_app w ψ hle he e' hV hV' l, app_app, ← Functor.map_comp, h0, Functor.map_zero]
  rfl

theorem isFrame_pull {G : X.Modules} [G.IsQuasicoherent] {U : X.Opens} (hU : ⊤ ≤ w ⁻¹ᵁ U) {t : Fin r → Γ(G, U)}
    (ht : IsFrame t) : IsFrame fun i => pullbackSections w G hU (t i) := PullHT.isFrame_pullS w hU ht

theorem exists_of_mem [F.IsQuasicoherent] [F'.IsQuasicoherent] {ρ : F ⟶ Q} (h0 : ψ ≫ ρ = 0) [Epi ρ]
    (hex : (ShortComplex.mk ψ ρ h0).Exact) (he' : IsFrame e') (hV : ⊤ ≤ w ⁻¹ᵁ V) (hV' : ⊤ ≤ w ⁻¹ᵁ V')
    {c : Fin r → R} (hc : c ∈ kerAt w ρ hV e) :
    ∃ d : Fin r → R, ∀ k, c k = ∑ l, d l * evAt w hV' (mat ψ hle he e' k l) := by
  haveI : Q.IsQuasicoherent := by
    have i : cokernel ψ ≅ Q := (cokernelIsCokernel ψ).coconePointUniqueUpToIso hex.gIsCokernel
    exact isQuasicoherent_of_iso i
  have hx := hex.map_of_epi_of_preservesCokernel (Scheme.Modules.pullback w) (inferInstanceAs (Epi ρ)) inferInstance
  have hs := @exact_app_of_exact _ ⊤ _ hx (inferInstanceAs ((Scheme.Modules.pullback w).obj F').IsQuasicoherent)
    (inferInstanceAs ((Scheme.Modules.pullback w).obj F).IsQuasicoherent)
    (inferInstanceAs ((Scheme.Modules.pullback w).obj Q).IsQuasicoherent) (isAffineOpen_top _)
  obtain ⟨n, hn⟩ := (hs _).1 hc
  obtain ⟨a, rfl⟩ := (isFrame_pull w hV' he' ⊤ le_rfl).2 n
  let G := Scheme.ΓSpecIso (CommRingCat.of R)
  refine ⟨fun l => G.hom.hom (a l), fun k => ?_⟩
  have key : (fun k => G.inv.hom (c k)) = fun k => ∑ l, a l * G.inv.hom (evAt w hV' (mat ψ hle he e' k l)) := by
    apply (isFrame_pull w hV he ⊤ le_rfl).1
    simp only [Fintype.linearCombination_apply, GlobalTheory.Twist.resM_self] at hn ⊢
    refine Eq.trans hn.symm ?_
    change appLinear ((Scheme.Modules.pullback w).map ψ) ⊤ _ = _
    simp only [map_sum, map_smul, appLinear_apply, pull_app w ψ hle he e' hV hV', Finset.smul_sum, Finset.sum_smul,
      mul_smul]
    exact Finset.sum_comm
  have k2 := congrArg G.hom.hom (congrFun key k)
  simp only [map_sum, map_mul] at k2
  have t (y : R) : G.hom.hom (G.inv.hom y) = y := G.inv_hom_id_apply y
  simpa only [t] using k2

end Sheaf

section Norm

variable {X : Scheme.{0}} {F' F Q : X.Modules} {r : ℕ}

theorem valF_coef {k : Type} [Field k] (x : Sp k ⟶ X) (ψ : F' ⟶ F) {V V' U : X.Opens} (hle : V' ≤ V)
    {e : Fin r → Γ(F, V)} (he : IsFrame e) {e' : Fin r → Γ(F', V')} (he' : IsFrame e')
    {s' : Fin r → Γ(F', U)} {s : Fin r → Γ(F, U)} (hs' : IsFrame s') (hs : IsFrame s) (es : ∀ i, ψ.app U (s' i) = s i)
    (hx : ⊤ ≤ x ⁻¹ᵁ V') (l i : Fin r) :
    valF x _ (coef true he' hs' l i) = ∑ m, valF x V' (mat ψ hle he e' m l) * valF x _ (coef true he hs m i) := by
  by_cases hU : ⊤ ≤ x ⁻¹ᵁ (V' ⊓ U)
  · have h₁ : V' ⊓ U ≤ V ⊓ U := inf_le_inf_right _ hle
    rw [valF_eq_valHom x _ hU]
    simp only [← valHom_resG x (inf_le_left : V' ⊓ U ≤ V') hU, ← valHom_resG x h₁ hU, ← map_mul, ← map_sum]
    congr 1
    simp only [coef]
    rw [← repr_app ψ hs' hs es, app_resM, app_eq_sum ψ hle he]
    simp only [map_sum, resM_smul, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      ← IsFrame.repr_resM, resM_resM]
  · have hU' : ¬ ⊤ ≤ x ⁻¹ᵁ (V ⊓ U) := fun h => hU fun q hq => ⟨hx hq, (h hq).2⟩
    rw [valF, dif_neg hU]
    exact (Finset.sum_eq_zero fun m _ => by rw [valF.eq_1 x (V ⊓ U), dif_neg hU', mul_zero]).symm

theorem norm_iff [F.IsQuasicoherent] [F'.IsQuasicoherent] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (w : Sp ↥(intO C) ⟶ X) (ψ : F' ⟶ F) {ρ : F ⟶ Q} (h0 : ψ ≫ ρ = 0) [Epi ρ]
    (hex : (ShortComplex.mk ψ ρ h0).Exact) {V V' U : X.Opens} (hle : V' ≤ V)
    {e : Fin r → Γ(F, V)} (he : IsFrame e) {e' : Fin r → Γ(F', V')} (he' : IsFrame e')
    {s' : Fin r → Γ(F', U)} {s : Fin r → Γ(F, U)} (hs' : IsFrame s') (hs : IsFrame s) (es : ∀ i, ψ.app U (s' i) = s i)
    (hV : ⊤ ≤ w ⁻¹ᵁ V) (hV' : ⊤ ≤ w ⁻¹ᵁ V') (cf : Fin r → C) :
    (∀ c ∈ kerAt w ρ hV e,
        ‖∑ l, (c l : C) * ∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef true he hs l i)‖ ≤ 1) ↔
      ∀ l, ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef true he' hs' l i)‖ ≤ 1 := by
  have hx : ⊤ ≤ (spMap (intO C).subtype ≫ w) ⁻¹ᵁ V' := fun q _ => hV' (Set.mem_univ (spMap (intO C).subtype q))
  have key : ∀ l, ∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef true he' hs' l i) =
      ∑ m, (evAt w hV' (mat ψ hle he e' m l) : C) *
        ∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef true he hs m i) := fun l => by
    simp only [valF_coef _ ψ hle he he' hs' hs es hx, coe_evAt, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine ⟨fun H l => ?_, fun H c hc => ?_⟩
  · rw [key]
    exact H _ (col_mem w ψ hle he e' h0 hV hV' l)
  · obtain ⟨d, hd⟩ := exists_of_mem w ψ hle he e' h0 hex he' hV hV' hc
    have : ∑ l, (c l : C) * ∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef true he hs l i) =
        ∑ l, (d l : C) * ∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef true he' hs' l i) := by
      have hc' : ∀ k, (c k : C) = ∑ l, (d l : C) * (evAt w hV' (mat ψ hle he e' k l) : C) := fun k => by
        have := congrArg (intO C).subtype (hd k)
        rw [map_sum] at this
        simp only [map_mul] at this
        exact this
      simp only [key, hc', Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
    rw [this]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (d l).2 (norm_nonneg _) (H l)

theorem coef_app (ψ : F' ⟶ F) {V U : X.Opens} {e' : Fin r → Γ(F', V)} {e : Fin r → Γ(F, V)} (he' : IsFrame e')
    (he : IsFrame e) {s' : Fin r → Γ(F', U)} {s : Fin r → Γ(F, U)} (hs' : IsFrame s') (hs : IsFrame s)
    (ee : ∀ i, ψ.app V (e' i) = e i) (es : ∀ i, ψ.app U (s' i) = s i) (l i : Fin r) :
    coef true he' hs' l i = coef true he hs l i := by
  simp only [coef]
  rw [← repr_app ψ hs' hs es, app_resM, ee]

theorem isFrame_of_app (ψ : F' ⟶ F) {U : X.Opens} {s' : Fin r → Γ(F', U)} {s : Fin r → Γ(F, U)} (hs : IsFrame s)
    (hb : ∀ V ≤ U, Function.Bijective (ψ.app V)) (es : ∀ i, ψ.app U (s' i) = s i) : IsFrame s' :=
  hs.map_of_linearEquiv (fun V hV => (LinearEquiv.ofBijective (appLinear ψ V) (hb V hV)).symm) fun V hV i => by
    rw [LinearEquiv.symm_apply_eq]
    exact ((app_resM ψ hV (s' i)).trans (congrArg _ (es i))).symm

end Norm

theorem bijective_app {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}
    {F' F : B.X.Modules} (ψ : F' ⟶ F) [IsIso (B.genRes.map ψ)] {V : B.X.Opens} (hV : V ≤ B.gen) :
    Function.Bijective (ψ.app V) := by
  let j := B.gen.ι
  have hR : IsIso ((Scheme.Modules.restrictFunctor j).map ψ) := by
    let e := Scheme.Modules.restrictFunctorIsoPullback j
    have h : (Scheme.Modules.restrictFunctor j).map ψ = e.hom.app _ ≫ B.genRes.map ψ ≫ e.inv.app _ := by
      rw [← e.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [h]; infer_instance
  obtain ⟨U, rfl⟩ : ∃ U : B.gen.toScheme.Opens, V = j ''ᵁ U := ⟨j ⁻¹ᵁ V, by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hV]⟩
  exact ConcreteCategory.bijective_of_isIso (((Scheme.Modules.restrictFunctor j).map ψ).app U)

theorem isEqLatPres_of_ptR : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (Z : GlobalTheory.LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [CharP (ResidueField O) p] {B : GlobalTheory.Vert.Model O} (h : B.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (oo : EPres B (𝓞 E)) (Q : B.X.Modules) (ρ : oo.E.V ⟶ Q) (hρ : oo.ψ.hom ≫ ρ = 0) (s : ∀ a : Fin Z.m, Fin r → Γ(oo.E.V, h ⁻¹ᵁ (Z.U a).1)) (hs : IsEqLat Z h x true oo.E s), oo.r = r → Epi ρ → (ShortComplex.mk oo.ψ.hom ρ hρ).Exact → PtR Z h x hs.2.2.1.frame ρ → IsEqLatPres Z h x true oo := by
  intro E _ _ _ H Dw Xo p _ W Y i₀ Z O _ _ _ _ _ B h r x oo Q ρ hρ s hs hr _ hex hR
  have hgen : ∀ a, h ⁻¹ᵁ (Z.U a).1 ≤ B.gen := fun a => by
    rw [B.gen_eq_basicOpen (GlobalTheory.Vert.natCast_ne_zero O p) (GlobalTheory.Vert.natCast_mem_maximalIdeal O p)]
    refine le_basicOpen_of_isUnit le_top ?_
    have hp : IsUnit (p : Z.i.c.F) := (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero).isUnit
    have := (hp.map (Z.alg a)).map (h.app (Z.U a).1).hom
    simp only [map_natCast] at this ⊢
    exact this
  haveI := oo.iso
  have hb : ∀ a (V : B.X.Opens), V ≤ h ⁻¹ᵁ (Z.U a).1 → Function.Bijective (oo.ψ.hom.app V) :=
    fun a V hV => bijective_app oo.ψ.hom (hV.trans (hgen a))
  choose s' es using fun a i => (hb a _ le_rfl).2 (s a i)
  have vb' : IsVB oo.E'.V r := hr ▸ oo.vb'
  haveI := vb'.isQuasicoherent
  haveI := hs.2.1.isQuasicoherent
  have fr : ∀ a, IsFrame (s' a) := fun a => isFrame_of_app oo.ψ.hom (hs.2.2.1.frame a) (hb a) (es a)
  refine ⟨hr, s', ⟨fr, ?_, ?_⟩, ?_, fun a i c => ?_⟩
  · intro k _ w a a' φ φ' h1 h2 j
    have e : ∀ i, coef true (fr a) (fr a') i j = coef true (hs.2.2.1.frame a) (hs.2.2.1.frame a') i j := fun i =>
      coef_app oo.ψ.hom _ _ _ _ (es a) (es a') i j
    simp only [e]
    exact hs.2.2.1.glue k w a a' φ φ' h1 h2 j
  · intro y w hw a φ hφ V₁ e₁ he₁ hV₁ cf v hv
    obtain ⟨V, e, he, hV, hK⟩ := hR y w hw a φ hφ
    have hle : V ⊓ V₁ ≤ V := inf_le_left
    have hV' : ⊤ ≤ w ⁻¹ᵁ (V ⊓ V₁) := fun q hq => ⟨hV hq, hV₁ hq⟩
    rw [hK cf v hv, norm_iff _ w oo.ψ.hom hρ hex hle he (he₁.res inf_le_right) (fr a) (hs.2.2.1.frame a) (es a) hV hV' cf]
    exact FrameNorm.norm_le_one_iff true _ he₁ (fr a) _ w hV' hV₁ cf
  · simp only [es]
    exact hs.2.2.1
  · apply (hb a _ le_rfl).1
    have hc : (oo.E'.ρ c : oo.E'.V ⟶ oo.E'.V) ≫ oo.ψ.hom = oo.ψ.hom ≫ (oo.E.ρ c : oo.E.V ⟶ oo.E.V) := oo.ψ.comm c
    rw [app_app, hc, ← app_app, es, hs.2.2.2, ← appLinear_apply, map_smul, appLinear_apply, es]

end GlobalTheory.ChainPts.KerOm

end
