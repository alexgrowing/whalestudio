import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharHomAdditiveShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardTwistHomDualIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistHomModuleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardHomAdjunctionIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenRankPushforwardAmpleTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointPreimageGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRankPushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurfaceAlterationEffectiveCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubbundleKernelOfLocallyPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImagePrincipalOfEffCartier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNotMemSupportCokernelOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberEqGenericRankMulProjCurve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RRTorsion

def defect (k : Type) [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] (E : X.Modules) (r : ℕ)
    (G : X.Modules) : ℤ :=
  chi k (homMod (dual E) G) + chi k (homMod E G) - 2 * (r : ℤ) * chi k G

section General

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]

omit [Field k] [Algebra k Γ(X, ⊤)] in

theorem isZero_homMod {E G : X.Modules} (h : IsZero E ∨ IsZero G) : IsZero (homMod E G) := by
  rw [IsZero.iff_id_eq_zero]
  ext V ψ : 3
  refine VB.hom_ext fun W hW s => ?_
  change homApp ψ hW s = 0
  rcases h with h | h
  · have e : s = 0 := by
      have : (𝟙 E : E ⟶ E).app W s = (0 : E ⟶ E).app W s := by rw [h.eq_of_src (𝟙 E) 0]
      exact this
    rw [e, map_zero]
  · have : (𝟙 G : G ⟶ G).app W (homApp ψ hW s) = (0 : G ⟶ G).app W (homApp ψ hW s) := by
      rw [h.eq_of_src (𝟙 G) 0]
    exact this

theorem defect_of_isZero (E : X.Modules) (r : ℕ) {G : X.Modules} (h : IsZero G) :
    defect k E r G = 0 := by
  rw [defect, chi_eq_zero_of_isZero k (isZero_homMod (.inr h)),
    chi_eq_zero_of_isZero k (isZero_homMod (.inr h)), chi_eq_zero_of_isZero k h]
  simp

theorem defect_rank_zero {E : X.Modules} (hE : IsVB E 0) (G : X.Modules) : defect k E 0 G = 0 := by
  rw [defect, chi_eq_zero_of_isZero k (isZero_homMod (.inl (isVB_zero_iff.1 hE.dual))),
    chi_eq_zero_of_isZero k (isZero_homMod (.inl (isVB_zero_iff.1 hE)))]
  simp

theorem defect_shortExact (hp : IsProjOver (strHom k X)) {E : X.Modules} {r : ℕ} (hE : IsVB E r)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (h₁ : QCoh.IsFiniteQC S.X₁)
    (h₂ : QCoh.IsFiniteQC S.X₂) (h₃ : QCoh.IsFiniteQC S.X₃) :
    defect k E r S.X₂ = defect k E r S.X₁ + defect k E r S.X₃ := by
  have hfc : ∀ (G : X.Modules), QCoh.IsFiniteQC G → FiniteCoh k G := fun G _ =>
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k X) G hp
  have H : ∀ W : X.Modules, IsVB W r →
      chi k (homMod W S.X₂) = chi k (homMod W S.X₁) + chi k (homMod W S.X₃) := fun W hW =>
    HomExact.chi_shortExact_mk k (HomExact.shortExact_homMod hW S hS)
      (hfc _ (PtNorm.isFiniteQC_homMod hW)) (hfc _ (PtNorm.isFiniteQC_homMod hW))
  simp only [defect, H _ hE, H _ hE.dual, chi_shortExact hS (hfc _ h₁) (hfc _ h₃)]
  ring

theorem defect_pushforward {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] (g : Y ⟶ X) [IsClosedImmersion g]
    (hg : ∀ a : k, g.appTop (algebraMap k Γ(X, ⊤) a) = algebraMap k Γ(Y, ⊤) a) {E : X.Modules} {r : ℕ}
    (hE : IsVB E r) (G : Y.Modules) :
    defect k E r ((Scheme.Modules.pushforward g).obj G) =
      defect k ((Scheme.Modules.pullback g).obj E) r G := by
  have hθ : IsIso (DualPull.theta g E) := DualPull.isIso_theta g hE
  rw [defect, defect, ← chi_congr k (HomPull.pushHomIso g (dual E) G),
    ← chi_congr k (HomPull.pushHomIso g E G), chi_pushforward_of_isClosedImmersion hg,
    chi_pushforward_of_isClosedImmersion hg, chi_pushforward_of_isClosedImmersion hg,
    chi_congr k (ProjFml.homIsoLeft (@asIso _ _ _ _ (DualPull.theta g E) hθ) G)]

theorem defect_twist {E : X.Modules} {r : ℕ} (hE : IsVB E r) (M : LB X) :
    defect k E r (twist (structureModule X) M) =
      chi k (twist E M) + chi k (twist (dual E) M) - 2 * (r : ℤ) * chi k (twist (structureModule X) M) := by
  have := hE.isIso_toBidual_of_local_frames
  have e : chi k (twist E M) = chi k (twist (dual (dual E)) M) :=
    chi_congr k ((twistFunctor M).mapIso (@asIso _ _ _ _ (cartierDualToBidual E) this))
  rw [defect, ← chi_congr k (TwistHomMod.iso (dual E) (structureModule X) M),
    ← chi_congr k (TwistHomMod.iso E (structureModule X) M), e]
  rfl

theorem chi_twist_line (hp : IsProjOver (strHom k X)) (hd : topologicalKrullDim X ≤ 1) {N : X.Modules}
    (h : IsVB N 1) {M : LB X} (hM : M.IsLB) :
    chi k (twist N M) + chi k (twist (dual N) M) = 2 * chi k (twist (structureModule X) M) := by
  have := (isVB_structureModule X).isFiniteQC
  have hv : DiffVanish (1 + 1) (chiPic k (structureModule X)) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) _ hp
      (by rw [QCoh.suppDim_structureModule]; exact hd)
  set f := chiPic k (structureModule X) with hf
  set c := CechPic.cls _ h.isLB_det with hc
  set m := CechPic.cls M hM with hm
  have e : ∀ (W : X.Modules) (hW : IsVB W 1), chi k (twist W M) = f (CechPic.cls _ hW.isLB_det + m) :=
    fun W hW => by
      rw [hf, ← chiPic_twist, hm, chiPic_cls]
      exact chi_congr k ((twistFunctor M).mapIso (hW.isoDet ≪≫ (Twist.unitTwistIso _).symm))
  have e₂ : CechPic.cls _ h.dual.isLB_det = -c := by
    rw [← (CechPic.cls_eq_iff (CechPic.isLB_dual h.isLB_det) _).2 h.lbIso_det_dual,
      CechPic.cls_dual h.isLB_det]
  have e₅ := congrFun (hv.multiDiff_eq_zero (g := fun _ : Fin 2 => c) (by simp)) (c + m)
  rw [multiDiff_const] at e₅
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, bwdDiff_apply,
    Pi.zero_apply] at e₅
  rw [e N h, e _ h.dual, e₂, ← hc]
  change _ = 2 * f m
  rw [show c + m - c = m by abel, show m - c = -c + m by abel] at e₅
  linarith

theorem defect_eq_genRank_mul [IsIntegral X] (hp : IsProjOver (strHom k X)) {E : X.Modules} {r : ℕ}
    (hE : IsVB E r)
    (htor : ∀ G : X.Modules, QCoh.IsFiniteQC G → genRank G = 0 → defect k E r G = 0) (n : ℕ) :
    ∀ G : X.Modules, QCoh.IsFiniteQC G → genRank G = n →
      defect k E r G = n * defect k E r (structureModule X) := by
  have hO : QCoh.IsFiniteQC (structureModule X) := (isVB_structureModule X).isFiniteQC
  have hgO : genRank (structureModule X) = 1 := (isVB_structureModule X).genRank_eq
  obtain ⟨hprop, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (strHom k X)
  induction n with
  | zero =>
    intro G hG h0
    rw [htor G hG h0]; simp
  | succ n ih =>
    intro F hF hr
    obtain ⟨m, hg, s, hs⟩ := ((hA.eventually_isGloballyGenerated_twist F).and
      (hA.eventually_exists_mono_cutHom_pow (structureModule X))).exists
    have hN := isLB_lbPow hA.isLB m
    have hP := Twist.isLB_lbZPow hN (-1)
    have hFN : genRank (twist F (lbPow A m)) ≠ 0 := by rw [genRank_twist hN]; omega
    obtain ⟨t, ht⟩ := exists_germ_ne_zero hg hFN
    have hmt := mono_sectionHom t ht
    obtain ⟨e₁⟩ := nonempty_twist_twist_iso_of_cls_eq F hN hP (LB.isLB_triv X)
      (by rw [cls_lbZPow hN (-1) hP, cls_triv]; simp)
    obtain ⟨e₂⟩ := nonempty_twist_iso_of_cls_eq_zero F (LB.isLB_triv X) (cls_triv _)
    have hM : QCoh.IsFiniteQC (twistZ (structureModule X) (lbPow A m) (-1)) :=
      Twist.isFiniteQC_twist hP
    have hmg : Mono (Twist.map (lbZPow (lbPow A m) (-1)) (QCoh.sectionHom t)) :=
      (Twist.mono_map_iff hP _).2 hmt
    obtain ⟨M, f, g, hM, hf, hg, hM1⟩ : ∃ (M : X.Modules) (f : M ⟶ structureModule X) (g : M ⟶ F),
        QCoh.IsFiniteQC M ∧ Mono f ∧ Mono g ∧ genRank M = 1 :=
      ⟨_, cutHom (structureModule X) hN s,
        Twist.map (lbZPow (lbPow A m) (-1)) (QCoh.sectionHom t) ≫ e₁.hom ≫ e₂.hom, hM, hs,
        inferInstance, (genRank_twist hP).trans hgO⟩
    have hSf : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    have hSg : (ShortComplex.mk g (cokernel.π g) (cokernel.condition g)).ShortExact :=
      { exact := ShortComplex.exact_cokernel g }
    have hCf : QCoh.IsFiniteQC (cokernel f) := QCoh.IsFiniteQC.of_epi (cokernel.π f)
    have hCg : QCoh.IsFiniteQC (cokernel g) := QCoh.IsFiniteQC.of_epi (cokernel.π g)
    have rf := genRank_shortExact hSf
    have rg := genRank_shortExact hSg
    simp only at rf rg
    have e1 := defect_shortExact hp hE _ hSf hM hO hCf
    have e2 := defect_shortExact hp hE _ hSg hM hF hCg
    simp only at e1 e2
    rw [htor _ hCf (by omega)] at e1
    rw [e2, ih _ hCg (by omega), e1]
    push_cast; ring

theorem exists_hom_line [IsIntegral X] (hp : IsProjOver (strHom k X)) {E : X.Modules} {r : ℕ}
    (hE : IsVB E (r + 1)) : ∃ (L : X.Modules) (φ : E ⟶ L), IsVB L 1 ∧ φ ≠ 0 := by
  obtain ⟨A, hA⟩ := (isProper_and_exists_isAmpleLB_of_isProjOver hp).2
  have := hE.dual.isFiniteQC
  obtain ⟨n, m, ψ, hψ⟩ := (hA.eventually_exists_epi_sigma (dual E)).exists
  have hM : IsVB (toMod (lbZPow A (-n))) 1 := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  have hne : ¬ IsZero (dual E) := fun hz => by
    haveI : Nonempty X := IsIntegral.nonempty
    have := hE.dual.rank_unique (isVB_zero_iff.2 hz)
    omega
  obtain ⟨i, hi⟩ : ∃ i, Sigma.ι (fun _ : Fin m => toMod (lbZPow A (-n))) i ≫ ψ ≠ 0 := by
    by_contra! h
    have h0 : ψ = 0 := Sigma.hom_ext _ _ fun i => by simp [h i]
    subst h0
    exact hne (IsZero.of_epi_zero (∐ fun _ : Fin m => toMod (lbZPow A (-n))) (dual E))
  set χ := Sigma.ι (fun _ : Fin m => toMod (lbZPow A (-n))) i ≫ ψ with hχ
  refine ⟨dual (toMod (lbZPow A (-n))), cartierDualToBidual E ≫ dualMap χ, hM.dual, fun h0 => hi ?_⟩
  have := hE.isIso_toBidual_of_local_frames
  have := hE.dual.isIso_toBidual_of_local_frames
  have h1 : dualMap χ = 0 := by
    rw [← cancel_epi (cartierDualToBidual E), h0, comp_zero]
  have h2 : χ ≫ cartierDualToBidual (dual E) = 0 := by
    rw [toBidual_naturality_dualSheafTranspose, h1, dualMap_zero, comp_zero]
  rw [← cancel_mono (cartierDualToBidual (dual E)), h2, zero_comp]

theorem exists_model [IsIntegral X] (hp : IsProjOver (strHom k X)) (J : X.IdealSheafData)
    (hJ : genericPoint X ∉ J.support) :
    ∃ (Y : Scheme.{0}) (_ : Algebra k Γ(Y, ⊤)) (_ : IsIntegral Y) (ρ : Y ⟶ X),
      IsProjOver (strHom k Y) ∧ topologicalKrullDim Y = topologicalKrullDim X ∧
      ρ ≫ strHom k X = strHom k Y ∧
      (∀ F : Y.Modules, genRank ((Scheme.Modules.pushforward ρ).obj F) = genRank F) ∧
      ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) := by
  obtain ⟨Y, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup (strHom k X) hp J
  let V : X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ V) := hiso V fun _ hx => hx
  have : Nonempty V.toScheme := ⟨⟨genericPoint X, hJ⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : Nonempty (b ⁻¹ᵁ V).toScheme := ⟨inv (b ∣_ V) (Classical.arbitrary _)⟩
  have : IsIntegral (b ⁻¹ᵁ V).toScheme := isIntegral_of_isOpenImmersion (b ∣_ V)
  have hU : (J.comap b).support.compl = b ⁻¹ᵁ V := by
    ext y
    exact not_congr (ProjBlowup.mem_support_comap J b y)
  have hdom : IsSchemeTheoreticallyDominant (b ⁻¹ᵁ V).ι :=
    hU ▸ ProjBlowup.isSchemeTheoreticallyDominant_compl_of_effCartier Y _ hb.1
  have : IsNoetherian Y := isNoetherian_of_isProjOver hproj
  have : IsIntegral Y := by
    have : IsReduced Y := IsSchemeTheoreticallyDominant.isReduced (b ⁻¹ᵁ V).ι
    have h := ((IrreducibleSpace.isIrreducible_univ (b ⁻¹ᵁ V).toScheme).image _
      (b ⁻¹ᵁ V).ι.continuous.continuousOn).closure
    rw [Set.image_univ, (b ⁻¹ᵁ V).ι.denseRange.closure_range] at h
    have : IrreducibleSpace Y := (irreducibleSpace_def _).2 h
    exact isIntegral_of_irreducibleSpace_of_isReduced Y
  have hfac : (b ⁻¹ᵁ V).ι ≫ b = b ∣_ V ≫ V.ι := (morphismRestrict_ι b V).symm
  have hoi : IsOpenImmersion ((b ⁻¹ᵁ V).ι ≫ b) := by rw [hfac]; infer_instance
  have hg : (b ⁻¹ᵁ V).ι (genericPoint _) = genericPoint Y := genericPoint_eq_of_isOpenImmersion _
  have hgen : b (genericPoint Y) = genericPoint X := by
    rw [← hg, ← Scheme.Hom.comp_apply]
    exact genericPoint_eq_of_isOpenImmersion _
  letI : Algebra k Γ(Y, ⊤) := (b.appTop.hom.comp (algebraMap k Γ(X, ⊤))).toAlgebra
  have hstr : b ≫ strHom k X = strHom k Y := comp_strHom (g := b) fun _ => rfl
  have hprojY : IsProjOver (strHom k Y) := hstr ▸ hproj
  have hPX := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hPY := (isProper_and_exists_isAmpleLB_of_isProjOver hprojY).1
  have hdim : topologicalKrullDim Y = topologicalKrullDim X :=
    OpenDim.topologicalKrullDim_eq_of_isIso_restrict k X Y (strHom k X) (strHom k Y) b
      inferInstance inferInstance hstr V ⟨genericPoint X, hJ⟩ hbV
  have hst : IsIso (b.stalkMap (genericPoint Y)) := by
    have h1 : IsIso (((b ⁻¹ᵁ V).ι ≫ b).stalkMap (genericPoint _)) := inferInstance
    rw [Scheme.Hom.stalkMap_comp] at h1
    have h3 : IsIso (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint (b ⁻¹ᵁ V).toScheme)) := inferInstance
    have h2 : IsIso (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _))) :=
      @IsIso.of_isIso_comp_right _ _ _ _ _ (b.stalkMap ((b ⁻¹ᵁ V).ι (genericPoint _)))
        (((b ⁻¹ᵁ V).ι).stalkMap (genericPoint _)) h3 h1
    exact hg ▸ h2
  have : IsProper (b ≫ strHom k X) := hstr ▸ hPY
  have : IsProper b := .of_comp b (strHom k X)
  have hfib : ∀ x : Y, b x = genericPoint X → x = genericPoint Y := fun x hx => by
    have hxV : x ∈ b ⁻¹ᵁ V := show b x ∈ V from hx ▸ hJ
    have e : ((b ⁻¹ᵁ V).ι ≫ b) ⟨x, hxV⟩ = ((b ⁻¹ᵁ V).ι ≫ b) (genericPoint _) := by
      refine (Scheme.Hom.comp_apply _ _ _).trans (.trans ?_ (Scheme.Hom.comp_apply _ _ _).symm)
      rw [hg, hgen]
      exact hx
    rw [← hg, ← ((b ⁻¹ᵁ V).ι ≫ b).isOpenEmbedding.injective e]
    rfl
  have hnbhd : ∀ W : Y.Opens, genericPoint Y ∈ W →
      ∃ U : X.Opens, genericPoint X ∈ U ∧ b ⁻¹ᵁ U ≤ W := by
    intro W hW
    have hZ := b.isClosedMap _ W.isOpen.isClosed_compl
    refine ⟨⟨_, hZ.isOpen_compl⟩, ?_, ?_⟩
    · rintro ⟨x, hx, hxη⟩
      exact hx ((hfib x hxη) ▸ hW)
    · intro y hy
      by_contra hyV
      exact hy ⟨y, hyV, rfl⟩
  have hs : b (genericPoint Y) ⤳ genericPoint X := by rw [hgen]
  refine ⟨Y, _, ‹_›, b, hprojY, hdim, hstr, fun F => ?_, hb.1⟩
  rw [genRank_pushforward_of_generic X Y b hs hnbhd]
  refine (congrArg (· * genRank F) ?_).trans (one_mul _)
  have := PushGenRank.isIso_stalkSpecializes hs hgen
  letI := (X.presheaf.stalkSpecializes hs ≫ b.stalkMap (genericPoint Y)).hom.toAlgebra
  exact Module.finrank_of_bijective_algebraMap
    (ConcreteCategory.bijective_of_isIso (X.presheaf.stalkSpecializes hs ≫ b.stalkMap (genericPoint Y)))

theorem eventually_chi_pushforward {Y : Scheme.{0}} [Algebra k Γ(Y, ⊤)] (hX : IsProjOver (strHom k X))
    (hY : IsProjOver (strHom k Y)) (ρ : Y ⟶ X) (hρ : ρ ≫ strHom k X = strHom k Y) {L : LB Y}
    (hL : IsAmpleLB L) (H : Y.Modules) (hH : QCoh.IsFiniteQC H) :
    ∀ᶠ n in atTop, QCoh.IsFiniteQC ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) ∧
      chi k ((Scheme.Modules.pushforward ρ).obj (twist H (lbPow L n))) = chi k (twist H (lbPow L n)) := by
  have hPT := (isProper_and_exists_isAmpleLB_of_isProjOver hX).1
  have hPT' := (isProper_and_exists_isAmpleLB_of_isProjOver hY).1
  have : IsProper (ρ ≫ strHom k X) := hρ ▸ hPT'
  have : IsProper ρ := .of_comp ρ (strHom k X)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (strHom k X)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (strHom k X)
  have := isAffineHom_diagonal_of_isSeparated (strHom k X)
  have hπ : ∀ r : k, ρ.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r := fun r => by
    rw [algebraMap_eq_strHom k X, algebraMap_eq_strHom k Y, ← hρ, Scheme.Hom.comp_appTop]
    rfl
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have hV : ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin m), I.Nonempty → ∀ q, 0 < q →
      Subsingleton (cohOn (twist H (lbPow L n)) (ρ ⁻¹ᵁ (⨅ i ∈ I, D i)) q) :=
    eventually_all.2 fun I => eventually_all.2 fun hI =>
      GlobalTheory.ProperFinite.eventually_subsingleton_cohOn ρ hL H (hD' I hI)
  filter_upwards [hV] with n hn
  have := GlobalTheory.Twist.isFiniteQC_twist (F := H) (isLB_lbPow hL.isLB n)
  have hF := GlobalTheory.ProperFinite.isFiniteQC_pushforward ρ hL (twist H (lbPow L n))
  refine ⟨hF, chi_eq_of_linearEquiv k fun p => ?_⟩
  exact (GlobalTheory.ProperFinite.nonempty_coh_pushforward_equiv k ρ hπ _ hc hD' hn p).some

omit [Field k] [Algebra k Γ(X, ⊤)] in

def projIso {Y : Scheme.{0}} (ρ : Y ⟶ X) (W : X.Modules) (M : LB Y) :
    (Scheme.Modules.pushforward ρ).obj (twist (dual ((Scheme.Modules.pullback ρ).obj W)) M) ≅
      homMod W ((Scheme.Modules.pushforward ρ).obj (twist (structureModule Y) M)) :=
  (Scheme.Modules.pushforward ρ).mapIso
      (TwistHomMod.iso ((Scheme.Modules.pullback ρ).obj W) (structureModule Y) M) ≪≫
    HomPull.pushHomIso ρ W (twist (structureModule Y) M)

theorem chi_twist_shortExact_mk {F G H : X.Modules} {f : F ⟶ G} {g : G ⟶ H} {w : f ≫ g = 0}
    (hS : (ShortComplex.mk f g w).ShortExact) {M : LB X} (hM : M.IsLB)
    (h₁ : FiniteCoh k (twist F M)) (h₃ : FiniteCoh k (twist H M)) :
    chi k (twist G M) = chi k (twist F M) + chi k (twist H M) := by
  have := chi_shortExact (k := k) (Twist.shortExact_map hM hS) h₁ h₃
  exact this

theorem defect_extension (hp : IsProjOver (strHom k X)) (hd : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) {r : ℕ} (h₁ : IsVB S.X₁ r)
    (h₂ : IsVB S.X₂ (r + 1)) (h₃ : IsVB S.X₃ 1) {M : LB X} (hM : M.IsLB) :
    defect k S.X₂ (r + 1) (twist (structureModule X) M) =
      defect k S.X₁ r (twist (structureModule X) M) := by
  have hfc : ∀ {G : X.Modules} {s : ℕ}, IsVB G s → FiniteCoh k (twist G M) := fun {G s} h =>
    have := (h.twist hM).isFiniteQC
    finiteCoh_of_isProjOver (algebraMap_eq_strHom k X) _ hp
  have e₁ := chi_twist_shortExact_mk (k := k) (f := S.f) (g := S.g) (w := S.zero) hS hM (hfc h₁)
    (hfc h₃)
  have e₂ := chi_twist_shortExact_mk (k := k) (DualExact.shortExact_dual X S 1 hS h₃) hM
    (hfc h₃.dual) (hfc h₁.dual)
  have e₃ := chi_twist_line hp hd h₃ hM
  rw [defect_twist h₂, defect_twist h₁, e₁, e₂]
  push_cast
  linarith

end General

variable (k : Type) [Field k]

def Holds (r : ℕ) : Prop :=
  ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ E : X.Modules, IsVB E r →
    ∀ F : X.Modules, QCoh.IsFiniteQC F → QCoh.suppDim F ≤ 1 → defect k E r F = 0

variable {k}

theorem exists_defect_eq_zero {r : ℕ} (ih : Holds k r) {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    [IsIntegral X] (hp : IsProjOver (strHom k X)) (hd : topologicalKrullDim X ≤ 1) {E : X.Modules}
    (hE : IsVB E (r + 1)) :
    ∃ G : X.Modules, QCoh.IsFiniteQC G ∧ genRank G = 1 ∧ defect k E (r + 1) G = 0 := by
  obtain ⟨L, φ, hL, hφ⟩ := exists_hom_line hp hE
  have := hE.isFiniteQC
  have := hL.isFiniteQC
  obtain ⟨Y, _, _, ρ, hY, hdim, hc, hrk, hC⟩ := exists_model hp (QCoh.annihilatorSheaf (cokernel φ))
    fun h => VB.genericPoint_notMem_support_cokernel_of_ne_zero X E L φ hL hφ
      ((QCoh.coe_support_annihilatorSheaf _).le h)
  have hdY : topologicalKrullDim Y ≤ 1 := hdim ▸ hd
  obtain ⟨hsub, hK⟩ := VB.isSubbundle_kernel_of_locally_principal Y _ _
    ((Scheme.Modules.pullback ρ).map φ) r (hE.pullback ρ) (hL.pullback ρ)
    (VB.exists_image_principal_of_effCartier X Y ρ E L φ _ hE hL hC)
  let S : ShortComplex Y.Modules :=
    ShortComplex.mk _ _ (cokernel.condition (kernel.ι ((Scheme.Modules.pullback ρ).map φ)))
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  obtain ⟨s, h₃⟩ := hsub.isVB_cokernel
  have h₁ : IsVB S.X₁ r := hK
  have h₂ : IsVB S.X₂ (r + 1) := hE.pullback ρ
  have h₃' : IsVB S.X₃ s := h₃
  have hs : s = 1 := by
    have := h₂.isFiniteQC
    have g := genRank_shortExact hS
    rw [h₁.genRank_eq, h₂.genRank_eq, h₃'.genRank_eq] at g
    omega
  subst hs
  obtain ⟨A, hA⟩ := (isProper_and_exists_isAmpleLB_of_isProjOver hY).2
  have hE' := hE.pullback ρ
  have hD' := hE.dual.pullback ρ
  obtain ⟨n, ⟨f₀, c₀⟩, ⟨-, c₁⟩, -, c₂⟩ :=
    ((eventually_chi_pushforward hp hY ρ hc hA _ (isVB_structureModule Y).isFiniteQC).and
      ((eventually_chi_pushforward hp hY ρ hc hA _ hE'.dual.isFiniteQC).and
        (eventually_chi_pushforward hp hY ρ hc hA _ hD'.dual.isFiniteQC))).exists
  have hM := isLB_lbPow hA.isLB n
  have hO := (isVB_structureModule Y).twist hM
  refine ⟨_, f₀, (hrk _).trans hO.genRank_eq, ?_⟩
  have e := (defect_extension hY hdY S hS h₁ h₂ h₃' hM).trans
    (ih Y hY _ h₁ _ hO.isFiniteQC ((QCoh.suppDim_le _).trans hdY))
  have hθ : IsIso (DualPull.theta ρ E) := DualPull.isIso_theta ρ hE
  have t : ∀ W : Y.Modules, chi k (twist (dual W) (lbPow A n)) =
      chi k (homMod W (twist (structureModule Y) (lbPow A n))) := fun W =>
    chi_congr k (TwistHomMod.iso W (structureModule Y) (lbPow A n))
  rw [defect, ← chi_congr k (projIso ρ (dual E) _), ← chi_congr k (projIso ρ E _), c₀, c₁, c₂, t, t,
    chi_congr k (ProjFml.homIsoLeft (@asIso _ _ _ _ (DualPull.theta ρ E) hθ) _)]
  exact e

theorem Holds.succ {r : ℕ} (ih : Holds k r) : Holds k (r + 1) := by
  intro X _ hp E hE F hF
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  obtain ⟨A, hA⟩ := (isProper_and_exists_isAmpleLB_of_isProjOver hp).2
  refine QCoh.devissage X (fun G => QCoh.IsFiniteQC G → QCoh.suppDim G ≤ 1 → defect k E (r + 1) G = 0)
    (fun G h _ _ => defect_of_isZero E _ h) (fun S hS h₁ h₃ p₁ p₃ h₂ h => ?_) ?_ F hF hF
  · rw [QCoh.suppDim_eq_max_of_shortExact hS, max_le_iff] at h
    rw [defect_shortExact hp hE S hS h₁ h₂ h₃, p₁ h₁ h.1, p₃ h₃ h.2, add_zero]
  intro Z hZ hsmall G hG _ hdim
  haveI := isIntegral_red hZ
  have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  have hcoh : ∀ H : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Modules, QCoh.IsFiniteQC H →
      QCoh.IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj H) := fun H _ =>
    ProperFinite.isFiniteQC_pushforward (redι Z) hAV H
  have hsub := support_pushforward_subset_image_of_isClosedImmersion (redι Z)
  have hsubZ := fun H => (hsub H).trans ((Set.image_subset_range _ _).trans (range_redι Z).le)
  rcases (hsubZ G).eq_or_ssubset with he | hlt
  swap
  · exact hsmall _ (hcoh G hG) hlt (hcoh G hG) hdim
  have hdZ : topologicalKrullDim (Z : Set X) ≤ 1 := by
    rw [← he]; exact hdim
  letI := algebraΓAlong k (redι Z)
  have hg := appTop_algebraMap_along k (redι Z)
  have hpZ : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom hg]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hE' := hE.pullback (redι Z)
  have key := defect_eq_genRank_mul hpZ hE' fun H hH h0 => by
    rw [← defect_pushforward (redι Z) hg hE]
    refine hsmall _ (hcoh H hH) ⟨hsubZ H, fun hle => genRank_eq_zero_iff.1 h0 ?_⟩
      (hcoh H hH) ((QCoh.topologicalKrullDim_mono (hsubZ H)).trans hdZ)
    obtain ⟨y, hy, hyη⟩ := hsub H (hle ((range_redι Z).le ⟨genericPoint _, rfl⟩))
    rwa [(redι Z).isClosedEmbedding.injective hyη] at hy
  obtain ⟨G₀, hG₀, hr₀, h₀⟩ :=
    exists_defect_eq_zero ih hpZ ((topologicalKrullDim_red Z).trans_le hdZ) hE'
  have e := key 1 G₀ hG₀ hr₀
  rw [h₀, Nat.cast_one, one_mul] at e
  rw [defect_pushforward (redι Z) hg hE, key _ G hG rfl, ← e, mul_zero]

variable (k) in

theorem intersectionNumber_baseChange (r : ℕ) : Holds k r := by
  induction r with
  | zero => exact fun X _ _ E hE F _ _ => defect_rank_zero hE F
  | succ r ih => exact ih.succ

theorem chi_homMod_add_of_genRank_eq_zero : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E r → ∀ (F : T.Modules), QCoh.IsFiniteQC F → genRank F = 0 → chi k (homMod (dual E) F) + chi k (homMod E F) = 2 * (r : ℤ) * chi k F := by
  intro k _ T _ _ hT E r hE F hF h
  refine sub_eq_zero.1 (intersectionNumber_baseChange k r T hT.isProjOver E hE F hF ?_)
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint T, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set T) = 2 := by
    rw [← hT.dim_eq, ← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact ENat.WithBot.add_le_add_one_right_iff.1 (this.trans_eq one_add_one_eq_two.symm)

end GlobalTheory.RRTorsion

end

theorem _root_.GlobalTheory.T.euler_char_dual_torsion_formula : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E r → ∀ (F : T.Modules), QCoh.IsFiniteQC F → genRank F = 0 → chi k (homMod (dual E) F) + chi k (homMod E F) = 2 * (r : ℤ) * chi k F :=
  GlobalTheory.RRTorsion.chi_homMod_add_of_genRank_eq_zero
