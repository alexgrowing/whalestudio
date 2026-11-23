import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationExtensionClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingChainExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingChainMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SystemCoverOfChainsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsNormalModelVectorBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelLettersPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelFramesBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechainPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelKernelVectorBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelVectorBundleOfPresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelChainCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalModelChainCharPDualStatement

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

namespace GlobalTheory.ChainPts.Cover

section Build

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime] [CharZero O]
  [CharP (ResidueField O) p] {B : Vert.Model O} {Λ : Type} [CommRing Λ]

omit [CharP (ResidueField O) p] in

theorem isIso_genRes_smulHom (E : B.X.Modules) {π : Γ(B.X, ⊤)} (h : IsRootOfP p π (p - 1)) :
    IsIso (B.genRes.map (smulHom E π)) := by
  rw [VB.pullback_map_smulHom]
  have hp : IsUnit ((Scheme.Hom.appTop B.gen.ι).hom (B.const (p : O))) :=
    RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x _ => (Scheme.mem_basicOpen_top _ _ x).1
      ((Scheme.preimage_basicOpen_top B.gen.ι _).le (B.gen_le_basicOpen (natCast_ne_zero O p) x.2))
  obtain ⟨u, hu⟩ := h
  have hc : B.const (p : O) = (p : Γ(B.X, ⊤)) := map_natCast _ p
  rw [hc] at hp
  have hpow : IsUnit (((Scheme.Hom.appTop B.gen.ι).hom π) ^ (p - 1)) := by
    rw [← map_pow, hu, map_mul]
    exact (u.isUnit.map _).mul hp
  have hπ := (isUnit_pow_iff (Nat.sub_ne_zero_of_lt (Fact.out : p.Prime).one_lt)).1 hpow
  exact (isUnit_iff_isIso _).1 (hπ.map (smulEnd _))

def kerV {M N : AM B Λ} (f : M ⟶ N) : (kernel f).V ≅ kernel f.hom :=
  PreservesKernel.iso (Action.forget B.X.Modules Λ) f

theorem mono_ι {M N : AM B Λ} (f : M ⟶ N) : Mono (kernel.ι f).hom :=
  inferInstanceAs (Mono ((Action.forget B.X.Modules Λ).map (kernel.ι f)))

theorem exact_ι {M N : AM B Λ} (f : M ⟶ N) (h : (kernel.ι f).hom ≫ f.hom = 0) :
    (ShortComplex.mk (kernel.ι f).hom f.hom h).Exact :=
  (ShortComplex.exact_kernel f).map (Action.forget B.X.Modules Λ)

theorem ι_comp {M N : AM B Λ} (f : M ⟶ N) : (kernel.ι f).hom ≫ f.hom = 0 :=
  congrArg Action.Hom.hom (kernel.condition f)

theorem isAdd_kernel {M N : AM B Λ} (f : M ⟶ N) (h : IsAdd M) : IsAdd (kernel f) := fun a b => by
  haveI := mono_ι f
  have k : ∀ c, ((kernel f).ρ c : (kernel f).V ⟶ (kernel f).V) ≫ (kernel.ι f).hom =
      (kernel.ι f).hom ≫ (M.ρ c : M.V ⟶ M.V) := fun c => (kernel.ι f).comm c
  rw [← cancel_mono (kernel.ι f).hom, Preadditive.add_comp, k, k, k, h, Preadditive.comp_add]

variable {o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} (P : PreChain p o Lie Om π)

theorem epi_ρ : Epi P.ρ.hom :=
  haveI := P.ρ_epi
  inferInstanceAs (Epi ((Action.forget B.X.Modules Λ).map P.ρ))

theorem isQuasicoherent_coker {r : ℕ} (vb : GlobalTheory.VB.IsVB Lie.V r) : (cokernel P.j).V.IsQuasicoherent := by
  haveI := vb.isQuasicoherent
  haveI := (P.q 0).vb.isQuasicoherent
  haveI := (P.q 0).vb'.isQuasicoherent
  haveI : (P.q 0).mod.V.IsQuasicoherent := isQuasicoherent_of_iso (Examples₂.cokV (P.q 0).ψ).symm
  exact isQuasicoherent_of_iso (Examples₂.cokV P.j).symm

theorem isZero_coker : IsZero (B.genRes.obj (cokernel P.j).V) := by
  have h := GlobalTheory.FrobFilt.ExtPres.isZero_genRes (P.q 0).toPres (M := (P.q 0).mod.V) (Examples₂.cokV (P.q 0).ψ)
  haveI : Epi (cokernel.π P.j).hom := inferInstanceAs (Epi ((Action.forget B.X.Modules Λ).map (cokernel.π P.j)))
  exact IsZero.of_epi (B.genRes.map (cokernel.π P.j).hom) h

def ooOf {r : ℕ} (add : IsAdd Om) (vb : GlobalTheory.VB.IsVB Om.V r) (vbK : GlobalTheory.VB.IsVB (kernel P.ρ.hom) r) : EPres B Λ where
  r := r
  E := Om
  E' := kernel P.ρ
  add := add
  add' := isAdd_kernel _ add
  vb := vb
  vb' := vbK.of_iso (kerV _).symm
  ψ := kernel.ι P.ρ
  iso := by
    haveI := (vbK.of_iso (kerV P.ρ).symm).isQuasicoherent
    haveI := vb.isQuasicoherent
    haveI := mono_ι P.ρ
    haveI := epi_ρ P
    have hm : Mono (B.genRes.map (kernel.ι P.ρ).hom) := mono_pullback_map _ _
    have e' : cokernel (kernel.ι P.ρ).hom ≅ (cokernel P.j).V := IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (exact_ι P.ρ (ι_comp _)).gIsCokernel
    have hz : IsZero (cokernel (B.genRes.map (kernel.ι P.ρ).hom)) :=
      ((isZero_coker P).of_iso (B.genRes.mapIso e')).of_iso (PreservesCokernel.iso B.genRes (kernel.ι P.ρ).hom).symm
    have he : Epi (B.genRes.map (kernel.ι P.ρ).hom) := Preadditive.epi_of_isZero_cokernel _ hz
    exact isIso_of_mono_of_epi _

def ooIso : cokernel (kernel.ι P.ρ) ≅ cokernel P.j :=
  haveI := P.ρ_epi
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (ShortComplex.exact_kernel P.ρ).gIsCokernel

def qIso : (P.q 0).mod.V ≅ (P.q 0).toPres.mod := Examples₂.cokV (P.q 0).ψ

def jP : Lie.V ⟶ (P.q 0).toPres.mod := P.j.hom ≫ (qIso P).hom

def cokJP {r : ℕ} (add : IsAdd Om) (vb : GlobalTheory.VB.IsVB Om.V r) (vbK : GlobalTheory.VB.IsVB (kernel P.ρ.hom) r) :
    cokernel (jP P) ≅ (ooOf P add vb vbK).toPres.mod :=
  cokernelCompIsIso P.j.hom (qIso P).hom ≪≫ (Examples₂.cokV P.j).symm ≪≫
    (Action.forget B.X.Modules Λ).mapIso (ooIso P).symm ≪≫ Examples₂.cokV (kernel.ι P.ρ)

def lwOf {r : ℕ} (add : IsAdd Lie) (vb : GlobalTheory.VB.IsVB Lie.V r) (vbN : GlobalTheory.VB.IsVB (kernel P.j.hom) r) : EPres B Λ where
  r := r
  E := kernel P.j
  E' := Lie
  add := isAdd_kernel _ add
  add' := add
  vb := vbN.of_iso (kerV _).symm
  vb' := vb
  ψ := kernel.lift P.j (smulA Lie π) P.j_kill
  iso := by
    haveI := (vbN.of_iso (kerV P.j).symm).isQuasicoherent
    haveI := vb.isQuasicoherent
    haveI := mono_ι P.j
    have hm : Mono (B.genRes.map (kernel.ι P.j).hom) := mono_pullback_map _ _
    have hc : (kernel.lift P.j (smulA Lie π) P.j_kill).hom ≫ (kernel.ι P.j).hom = smulHom Lie.V π :=
      congrArg Action.Hom.hom (kernel.lift_ι P.j _ P.j_kill)
    have h2 := isIso_genRes_smulHom Lie.V P.π_root
    rw [← hc, Functor.map_comp] at h2
    haveI : Epi (B.genRes.map (kernel.ι P.j).hom) := epi_of_epi (B.genRes.map (kernel.lift P.j (smulA Lie π) P.j_kill).hom) _
    haveI : IsIso (B.genRes.map (kernel.ι P.j).hom) := isIso_of_mono_of_epi _
    exact IsIso.of_isIso_comp_right _ (B.genRes.map (kernel.ι P.j).hom)

def chainOf {r : ℕ} (addL : IsAdd Lie) (vbL : GlobalTheory.VB.IsVB Lie.V r) (vbN : GlobalTheory.VB.IsVB (kernel P.j.hom) r)
    (addO : IsAdd Om) (vbO : GlobalTheory.VB.IsVB Om.V r) (vbK : GlobalTheory.VB.IsVB (kernel P.ρ.hom) r) : EqChain p B Λ o :=
  { P with
    π := π
    lw := lwOf P addL vbL vbN
    wl := kernel.ι P.j
    lw_wl := kernel.lift_ι P.j _ P.j_kill
    oo := ooOf P addO vbO vbK
    c3 := ⟨ShortComplex.mk (Abelian.image.ι P.j) (cokernel.π P.j) (kernel.condition _),
      { exact := ShortComplex.exact_kernel _ }, ⟨(Abelian.coimageIsoImage P.j).symm⟩, ⟨Iso.refl _⟩, ⟨(ooIso P).symm⟩⟩ }

end Build

theorem kerAt_comp {X : Scheme.{0}} {R : Type} [CommRing R] (w : Sp R ⟶ X) {F Q Q' : X.Modules} (u : F ⟶ Q) (e : Q ≅ Q')
    {V : X.Opens} (hV : ⊤ ≤ w ⁻¹ᵁ V) {r : ℕ} (s : Fin r → Γ(F, V)) : kerAt w (u ≫ e.hom) hV s = kerAt w u hV s := by
  ext c
  haveI : Mono ((Scheme.Modules.pullback w).map e.hom) := inferInstance
  simp only [kerAt, Set.mem_setOf_eq, Functor.map_comp]
  exact map_eq_zero_iff (((Scheme.Modules.pullback w).map e.hom).app ⊤).hom
    (app_injective_of_mono ((Scheme.Modules.pullback w).map e.hom) ⊤)

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} [Fact p.Prime] {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [CharP (ResidueField O) p] {B : Vert.Model O} {h : B.X ⟶ Z.X} {r o : ℕ} {x x' : Fin r → Letter Dw}
  {Lie Om : AM B (𝓞 E)} {sL : ∀ a : Fin Z.m, Fin r → Γ(Lie.V, h ⁻¹ᵁ (Z.U a).1)}
  {sO : ∀ a : Fin Z.m, Fin r → Γ(Om.V, h ⁻¹ᵁ (Z.U a).1)} {π : Γ(B.X, ⊤)}

omit [Fact p.Prime] in

theorem ptJ_comp {X : Scheme.{0}} {k : X ⟶ Z.X} {F Q Q' : X.Modules} {s : ∀ a : Fin Z.m, Fin r → Γ(F, k ⁻¹ᵁ (Z.U a).1)}
    (hs : ∀ a, GlobalTheory.VB.IsFrame (s a)) {t : Γ(X, ⊤)} (u : F ⟶ Q) (e : Q ≅ Q') (hJ : PtJ Z k x hs t u) :
    PtJ Z k x hs t (u ≫ e.hom) := by
  intro y w hw a φ hφ
  obtain ⟨V, s, hs, hV, k⟩ := hJ y w hw a φ hφ
  exact ⟨V, s, hs, hV, by rw [kerAt_comp]; exact k⟩

theorem exists_chain (hL : IsEqLat Z h x false Lie sL) (hO : IsEqLat Z h x' true Om sO) (P : PreChain p o Lie Om π)
    (hJ : PtJ Z h x hL.2.2.1.frame π P.j.hom) (hR : PtR Z h x' hO.2.2.1.frame P.ρ.hom)
    (vbK : GlobalTheory.VB.IsVB (kernel P.ρ.hom) r) :
    ∃ Q : EqChain p B (𝓞 E) o, IsEqLatPres Z h x false Q.lw ∧ IsEqLatPres Z h x' true Q.oo := by
  have eC := cokJP P hO.1 hO.2.1 vbK
  have vbN : GlobalTheory.VB.IsVB (kernel P.j.hom) r :=
    (GlobalTheory.T.kernel_vector_bundle_of_presentation _ B _ _ _ _ (jP P) hL.2.1 ⟨eC⟩).of_iso (kernelCompMono P.j.hom (qIso P).hom)
  have h0 : (kernel.ι P.j).hom ≫ jP P = 0 := by rw [jP, ← Category.assoc, ι_comp, zero_comp]
  refine ⟨chainOf P hL.1 hL.2.1 vbN hO.1 hO.2.1 vbK,
    GlobalTheory.T.local_model_chain_char_p Z _ _ (lwOf P hL.1 hL.2.1 vbN) (kernel.ι P.j) _ _ _ (jP P) h0 _ hL rfl P.π_root
      (kernel.lift_ι P.j _ P.j_kill) (mono_ι _) ?_ ⟨eC⟩ ?_,
    GlobalTheory.T.local_model_chain_char_p_dual Z _ _ (ooOf P hO.1 hO.2.1 vbK) _ P.ρ.hom (ι_comp _) _ hO rfl (epi_ρ P) (exact_ι _ _) hR⟩
  · exact ShortComplex.exact_of_iso (S₁ := ShortComplex.mk _ _ (ι_comp P.j))
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (qIso P) (by simp [lwOf]) (by simp [jP, lwOf])) (exact_ι _ _)
  · exact ptJ_comp _ _ (qIso P) hJ

theorem exists_cover_chain (hB : GlobalTheory.IsNormalScheme B.X) (hL : IsEqLat Z h x false Lie sL) (hO : IsEqLat Z h x' true Om sO)
    (P : PreChain p o Lie Om π) (hJ : PtJ Z h x hL.2.2.1.frame π P.j.hom) (hR : PtR Z h x' hO.2.2.1.frame P.ρ.hom) :
    ∃ (B' : Vert.Model O) (g : Vert.Model.Hom B' B) (Q : EqChain p B' (𝓞 E) o), GlobalTheory.IsNormalScheme B'.X ∧ g.relDim = 0 ∧
      IsEqLatPres Z (g.f ≫ h) x false Q.lw ∧ IsEqLatPres Z (g.f ≫ h) x' true Q.oo := by
  obtain ⟨B', g, hB', hg, hK⟩ := GlobalTheory.T.exists_model_kernel_vector_bundle _ p B _ _ _ P.ρ.hom hB hO.2.1 (isQuasicoherent_coker P hL.2.1) (epi_ρ P)
    (isZero_coker P)
  obtain ⟨P', e, e', he, he'⟩ := GlobalTheory.T.prechain_pullback _ p B B' g _ o _ _ _ P
  have hL' := hL.pull g.f
  have hO' := hO.pull g.f
  have hJ' := (GlobalTheory.T.local_model_frames_base_change Z g.f h x Lie.V _ sL hL.2.2.1.frame hL'.2.2.1.frame P.j.hom _ P'.j.hom e hL.2.1 he).1 _ hJ
  have hR' := (GlobalTheory.T.local_model_frames_base_change Z g.f h x' Om.V _ sO hO.2.2.1.frame hO'.2.2.1.frame P.ρ.hom _ P'.ρ.hom e' hO.2.1 he').2 hR
  have vbK : GlobalTheory.VB.IsVB (kernel P'.ρ.hom) r :=
    (hK.of_iso (kernelIsoOfEq he'.symm)).of_iso (kernelCompMono P'.ρ.hom e'.hom)
  obtain ⟨Q, hQ⟩ := exists_chain hL' hO' P' hJ' hR' vbK
  exact ⟨B', g, Q, hB', hg, hQ⟩

theorem exists_cover_of_sys (hB : GlobalTheory.IsNormalScheme B.X) (hL : IsEqLat Z h x false Lie sL) (hO : IsEqLat Z h x' true Om sO)
    {γ : ℕ → Γ(B.X, ⊤)} {n : ℕ} {M : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ} (C : ChainsBp p n o Lie Om π γ)
    (hπ : IsRootOfP p π (p - 1)) (hγ : ∀ k ≤ o, IsRootOfP p (γ k) (p ^ (k + 1))) (hsys : IsSys C M)
    (hpt : SysPt Z h x x' hL.2.2.1.frame hO.2.2.1.frame C) :
    ∃ (B' : Vert.Model O) (g : Vert.Model.Hom B' B) (Q : EqChain p B' (𝓞 E) o), GlobalTheory.IsNormalScheme B'.X ∧ g.relDim = 0 ∧
      IsEqLatPres Z (g.f ≫ h) x false Q.lw ∧ IsEqLatPres Z (g.f ≫ h) x' true Q.oo := by
  obtain ⟨B₃, g₃, P, hB₃, hg₃, hker⟩ := GlobalTheory.T.chains_normal_model_vector_bundle _ p B _ n o _ _ Lie Om π γ M C hB hL.1 hO.1 hL.2.1 hO.2.1 hπ hγ hsys
  have hL₃ := hL.pull g₃.f
  have hO₃ := hO.pull g₃.f
  obtain ⟨hJ₃, hR₃⟩ := GlobalTheory.T.local_model_letters_pullback Z h x x' Lie Om sL _ sO _ n o π γ C _ g₃.f _ _ P.j.hom P.ρ.hom hL₃.2.2.1.frame
    hO₃.2.2.1.frame hL.2.1 hO.2.1 hpt hker
  obtain ⟨B₄, g₄, Q, hB₄, hg₄, hQ⟩ := exists_cover_chain hB₃ hL₃ hO₃ P hJ₃ hR₃
  refine ⟨B₄, g₄.comp g₃, Q, hB₄, ?_, ?_⟩
  · unfold Vert.Model.Hom.relDim at *
    omega
  · rwa [← Category.assoc] at hQ

end Lat

theorem chainCoverSt : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd →
    GlobalTheory.GroupBplus.GroupAllSt → GlobalTheory.ChainPts.ChainCoverSt := by
  intro h1 h2 h3 h4 D O hO p _ W hW jc hj z
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c (Fact.out : p.Prime) hW
  intro c o B₁ f₁ hB₁ hf₁
  obtain ⟨B₂, g₂, hB₂, hg₂, hζ⟩ := GlobalTheory.T.exists_normal_model_roots_of_unity _ p B₁ hB₁ (o + 2)
  have hf₂ : (g₂.comp f₁).relDim = 0 := by
    unfold Vert.Model.Hom.relDim at *
    omega
  obtain ⟨Lie, Om, sL, sO, hL, hOm, π, γ, n, M, C, hπ, hγ, hsys, hpt⟩ :=
    GlobalTheory.T.system_cover_of_chains h1 h2 h3 h4 GlobalTheory.T.RingChainExists GlobalTheory.T.RingChainMap D O hO p W hW jc hj z c o B₂ (g₂.comp f₁) hB₂ hf₂ hζ
  obtain ⟨B₃, g₃, Q, hB₃, hg₃, hQ⟩ := exists_cover_of_sys hB₂ hL hOm C hπ hγ hsys hpt
  refine ⟨B₃, g₃.comp g₂, Q, hB₃, ?_, ?_⟩
  · unfold Vert.Model.Hom.relDim at *
    omega
  · have hh : ((g₃.comp g₂).comp f₁).f ≫ (nmodel z.Z).compι c = g₃.f ≫ (g₂.comp f₁).f ≫ (nmodel z.Z).compι c := by
      simp only [Vert.Model.Hom.comp, Category.assoc]
    rw [hh]
    exact hQ

end GlobalTheory.ChainPts.Cover

end
