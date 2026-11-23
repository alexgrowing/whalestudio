import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobCokernelSmulHomPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationExtensionClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOfProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLengthOneChainIdentityEmbedding

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TopologicalSpace
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.ChainPts

noncomputable section

namespace GlobalTheory.LocFreeQuot

section General

variable {X Y Z T : Scheme.{0}}

abbrev quot (r : ℕ) (a : Γ(X, ⊤)) : X.Modules := cokernel (smulHom (freeModule X (Fin r)) a)

theorem smulHom_quot (r : ℕ) (a : Γ(X, ⊤)) : smulHom (quot r a) a = 0 :=
  (cancel_epi (cokernel.π _)).1 (by rw [comp_zero, ← smulHom_comp, cokernel.condition])

theorem nonempty_pullback_quot (f : Y ⟶ X) (r : ℕ) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤)) (hb : f.appTop a = b) :
    Nonempty ((Scheme.Modules.pullback f).obj (quot r a) ≅ quot r b) := by
  have e : (Scheme.Modules.pullback f).obj (freeModule X (Fin r)) ≅ freeModule Y (Fin r) :=
    ((VB.isFrame_freeFrame X (Fin r)).pullback f).iso (VB.isFrame_freeFrame Y (Fin r))
  subst hb
  exact ⟨PreservesCokernel.iso (Scheme.Modules.pullback f) _ ≪≫
    cokernel.mapIso _ _ e e (by rw [VB.pullback_map_smulHom]; exact smulHom_comp e.hom _)⟩

theorem nonempty_pullback_of_range (j : Y ⟶ X) [IsOpenImmersion j] (f : T ⟶ X) (h : Set.range f ⊆ Set.range j)
    {G G' : X.Modules} (e : (Scheme.Modules.pullback j).obj G ≅ (Scheme.Modules.pullback j).obj G') :
    Nonempty ((Scheme.Modules.pullback f).obj G ≅ (Scheme.Modules.pullback f).obj G') := by
  rw [← IsOpenImmersion.lift_fac j f h]
  exact ⟨((Scheme.Modules.pullbackComp _ j).app G).symm ≪≫ (Scheme.Modules.pullback _).mapIso e ≪≫
    (Scheme.Modules.pullbackComp _ j).app G'⟩

theorem isIso_restrict_pushforward_unit (i : Z ⟶ X) (j : Y ⟶ Z) [IsOpenImmersion j] (U : X.Opens)
    (h : i ⁻¹ᵁ U ≤ j.opensRange) (G : Z.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward i).map
      ((Scheme.Modules.restrictAdjunction j).unit.app G))) := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.2 fun V => ?_
  change IsIso (G.presheaf.map (homOfLE (j.image_preimage_le (i ⁻¹ᵁ (U.ι ''ᵁ V)))).op)
  have hV : j ''ᵁ (j ⁻¹ᵁ (i ⁻¹ᵁ (U.ι ''ᵁ V))) = i ⁻¹ᵁ (U.ι ''ᵁ V) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.2 ((i.preimage_mono (U.ι_image_le V)).trans h)
  have : homOfLE (j.image_preimage_le (i ⁻¹ᵁ (U.ι ''ᵁ V))) = eqToHom hV := rfl
  rw [this]
  infer_instance

theorem nonempty_pullback_pushforward (i : Z ⟶ X) (j : Y ⟶ Z) [IsOpenImmersion j] (U : X.Opens)
    (h : i ⁻¹ᵁ U ≤ j.opensRange) {G G' : Z.Modules}
    (e : (Scheme.Modules.pullback j).obj G ≅ (Scheme.Modules.pullback j).obj G') :
    Nonempty ((Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward i).obj G) ≅
      (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward i).obj G')) := by
  have h₁ := isIso_restrict_pushforward_unit i j U h G
  have h₂ := isIso_restrict_pushforward_unit i j U h G'
  have e' : G.restrict j ≅ G'.restrict j := (Scheme.Modules.restrictFunctorIsoPullback j).app G ≪≫ e ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback j).app G').symm
  exact ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm ≪≫ @asIso _ _ _ _ _ h₁ ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso ((Scheme.Modules.pushforward i).mapIso
      ((Scheme.Modules.pushforward j).mapIso e')) ≪≫ (@asIso _ _ _ _ _ h₂).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _⟩

abbrev idl (a : Γ(X, ⊤)) : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})

theorem nonempty_iso_pushforward (a : Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] (hF : smulHom F a = 0) :
    Nonempty (F ≅ (Scheme.Modules.pushforward (idl a).subschemeι).obj
      ((Scheme.Modules.pullback (idl a).subschemeι).obj F)) := by
  refine ⟨@asIso _ _ _ _ ((Scheme.Modules.pullbackPushforwardAdjunction (idl a).subschemeι).unit.app F) ?_⟩
  refine (QCoh.isIso_iff_forall_affine (M := F) (N := (Scheme.Modules.pushforward (idl a).subschemeι).obj
    ((Scheme.Modules.pullback (idl a).subschemeι).obj F)) _).2 fun U hU => ?_
  obtain ⟨h₁, h₂⟩ := surjective_and_ker_unit_subschemeι (idl a) F ⟨U, hU⟩
  refine ⟨(LinearMap.ker_eq_bot (f := QCoh.appLinear _ U)).1 (h₂.trans ?_), h₁⟩
  refine Submodule.le_annihilator_iff.1 (le_trans ?_ Submodule.annihilator_top.ge)
  simp only [idl, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton,
    Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  rw [Module.mem_annihilator]
  intro m
  have := congrArg (fun φ => φ.app U m) hF
  simpa using this

theorem appTop_idl (a : Γ(X, ⊤)) : (idl a).subschemeι.appTop a = 0 := by
  set I := idl a
  refine I.subscheme.sheaf.eq_of_locally_eq' (fun U : X.affineOpens => I.subschemeι ⁻¹ᵁ U.1) ⊤
    (fun _ => homOfLE le_top) ?_ _ 0 fun U => ?_
  · intro z _
    have hz : I.subschemeι z ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := Opens.mem_iSup.1 hz
    exact Opens.mem_iSup.2 ⟨U, hU⟩
  · have h0 : (I.subschemeι.app U.1).hom ((X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom a) = 0 := by
      rw [← RingHom.mem_ker, I.ker_subschemeι_app U]
      simp only [I, idl, Scheme.IdealSheafData.ofIdealTop_ideal]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self a)
    change (I.subscheme.presheaf.map _).hom _ = (I.subscheme.presheaf.map _).hom 0
    rw [map_zero, ← h0]
    exact (congrArg (fun φ => φ.hom a) (I.subschemeι.naturality (homOfLE (le_top : U.1 ≤ ⊤)).op)).symm

theorem eq_zero_of_locally {F G : X.Modules} (φ : F ⟶ G)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (Scheme.Modules.pullback U.ι).map φ = 0) : φ = 0 := by
  choose U hx hU using h
  have hR (x : X) : (Scheme.Modules.restrictFunctor (U x).ι).map φ = 0 := by
    let e := Scheme.Modules.restrictFunctorIsoPullback (U x).ι
    rw [← cancel_mono (e.hom.app G), e.hom.naturality, hU, comp_zero, zero_comp]
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext s
  refine Twist.sec_ext_of_cover (fun x : W => (U x).ι ''ᵁ ((U x).ι ⁻¹ᵁ W))
    (fun x => Scheme.Hom.image_preimage_le _ _) (fun x hW => Opens.mem_iSup.2 ⟨⟨x, hW⟩, ?_⟩) fun x => ?_
  · rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact ⟨hx x, hW⟩
  · rw [← Twist.app_resM, ← Twist.app_resM]
    exact congrArg (fun ψ => ψ.app ((U x).ι ⁻¹ᵁ W) (Twist.resM F (Scheme.Hom.image_preimage_le _ _) s)) (hR x)

variable {g : Γ(X, ⊤)} {F : X.Modules}

theorem smulHom_eq_zero (h : LocFreeMod g F) : smulHom F g = 0 := by
  refine eq_zero_of_locally _ fun x => ?_
  obtain ⟨U, r, hx, ⟨e⟩⟩ := h x
  refine ⟨U, hx, ?_⟩
  rw [VB.pullback_map_smulHom, ← cancel_mono e.hom, smulHom_comp, ← VB.pullback_map_smulHom, smulHom_quot,
    Functor.map_zero, comp_zero, zero_comp]

theorem isFiniteQC (h : LocFreeMod g F) : IsFiniteQC F := by
  choose U r hx e using h
  refine IsFiniteQC.of_restrict (fun x => (U x).ι) (fun x => ⟨x, by simpa using hx x⟩) fun x => ?_
  exact IsFiniteQC.of_iso ((Scheme.Modules.restrictFunctorIsoPullback (U x).ι).app F ≪≫ (e x).some).symm

theorem of_iso (h : LocFreeMod g F) {F' : X.Modules} (e : F ≅ F') : LocFreeMod g F' := fun x =>
  have ⟨U, r, hx, ⟨e'⟩⟩ := h x
  ⟨U, r, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ e'⟩⟩

theorem exists_frame_of_retract {G : X.Modules} (i : G ⟶ F) (q : F ⟶ G) (hiq : i ≫ q = 𝟙 G) {r : ℕ}
    (hF : VB.IsVB F r) (x : X) : ∃ (V : X.Opens) (n : ℕ) (e : Fin n → Γ(G, V)), x ∈ V ∧ VB.IsFrame e := by
  have := hF.isQuasicoherent
  have hs : ∑ _ : Unit, i ≫ q = 𝟙 G := by simpa using hiq
  have : G.IsQuasicoherent :=
    QCoh.isQuasicoherent_of_sum_eq_id (A := fun _ : Unit => F) (fun _ => i) (fun _ => q) hs
  obtain ⟨U, e, hU, hx, -, he⟩ := hF.exists_affine (V := ⊤) (x := x) trivial
  have := Module.Free.of_basis (he.basis le_rfl)
  have := Module.Finite.of_basis (he.basis le_rfl)
  have hc : QCoh.appLinear q U ∘ₗ QCoh.appLinear i U = LinearMap.id := LinearMap.ext fun s => by
    simpa using QCoh.sum_app_app (A := fun _ : Unit => F) (fun _ => i) (fun _ => q) hs s
  have : Module.Projective Γ(X, U) Γ(G, U) := .of_split _ _ hc
  have : Module.Finite Γ(X, U) Γ(G, U) :=
    .of_surjective (QCoh.appLinear q U) fun s => ⟨_, LinearMap.congr_fun hc s⟩
  exact VB.Summand.exists_frame_of_projective (G := G) hU ⟨x, hx⟩

theorem of_retract (h : LocFreeMod g F) {F₁ : X.Modules} (i : F₁ ⟶ F) (q : F ⟶ F₁) (hiq : i ≫ q = 𝟙 F₁) :
    LocFreeMod g F₁ := by
  have := (isFiniteQC h).isQuasicoherent
  have hs : ∑ _ : Unit, i ≫ q = 𝟙 F₁ := by simpa using hiq
  have : F₁.IsQuasicoherent := isQuasicoherent_of_sum_eq_id (A := fun _ : Unit => F) (fun _ => i) (fun _ => q) hs
  have hk : smulHom F₁ g = 0 := by
    rw [← Category.comp_id (smulHom F₁ g), ← hiq, ← Category.assoc, smulHom_comp, smulHom_eq_zero h, comp_zero,
      zero_comp]
  obtain ⟨e₁⟩ := nonempty_iso_pushforward g F₁ hk
  let ι := (idl g).subschemeι

  have key (x : X) (U : X.Opens) (r : ℕ) (hx : x ∈ U) (T : Scheme.{0}) (j : T ⟶ (idl g).subscheme)
      [IsOpenImmersion j] (hj : ι ⁻¹ᵁ U ≤ j.opensRange)
      (e : (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).obj F₁) ≅
        (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).obj (quot r g))) :
      ∃ (U : X.Opens) (r : ℕ), x ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj F₁ ≅
        (Scheme.Modules.pullback U.ι).obj (quot r g)) := by
    obtain ⟨e₂⟩ := nonempty_iso_pushforward g (quot r g) (smulHom_quot r g)
    obtain ⟨e₃⟩ := nonempty_pullback_pushforward ι j U hj e
    exact ⟨U, r, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e₁ ≪≫ e₃ ≪≫
      ((Scheme.Modules.pullback U.ι).mapIso e₂).symm⟩⟩
  have hfree {T : Scheme.{0}} (j : T ⟶ (idl g).subscheme) (r : ℕ) :
      Nonempty ((Scheme.Modules.pullback (j ≫ ι)).obj (quot r g) ≅ freeModule T (Fin r)) := by
    obtain ⟨e⟩ := nonempty_pullback_quot (j ≫ ι) r g 0 (by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_idl, map_zero])
    exact ⟨e ≪≫ cokernelIsoOfEq (smulHom_zero _) ≪≫ cokernelZeroIsoTarget⟩
  intro x
  by_cases hx : x ∈ Set.range ι
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨U, r, hU, ⟨e⟩⟩ := h (ι z)
    let j := (ι ⁻¹ᵁ U).ι
    obtain ⟨e₂⟩ := nonempty_pullback_of_range U.ι (j ≫ ι) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2) e
    obtain ⟨e₃⟩ := hfree j r
    have hV := (VB.isVB_freeModule_fin _ r).of_iso (e₂ ≪≫ e₃).symm
    obtain ⟨V, n, s, hzV, hs⟩ := exists_frame_of_retract ((Scheme.Modules.pullback (j ≫ ι)).map i)
      ((Scheme.Modules.pullback (j ≫ ι)).map q) (by rw [← Functor.map_comp, hiq, CategoryTheory.Functor.map_id])
      hV ⟨z, hU⟩
    have e₄ := hs.restrictIso ((VB.isFrame_freeFrame _ (Fin n)).res le_top) V.ι V.opensRange_ι.le
    obtain ⟨e₅⟩ := hfree j n
    obtain ⟨W, hW, hWe⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.1 (V.ι ≫ j).opensRange.isOpen
    refine key _ ⟨W, hW⟩ n ?_ _ (V.ι ≫ j) hWe.le ?_
    · have : z ∈ ι ⁻¹' W := by
        rw [hWe]
        exact ⟨⟨⟨z, hU⟩, hzV⟩, rfl⟩
      exact this
    · have c (G : X.Modules) : (Scheme.Modules.pullback (V.ι ≫ j)).obj ((Scheme.Modules.pullback ι).obj G) ≅
          ((Scheme.Modules.pullback (j ≫ ι)).obj G).restrict V.ι :=
        ((Scheme.Modules.pullbackComp V.ι j).app _).symm ≪≫
          (Scheme.Modules.pullback V.ι).mapIso ((Scheme.Modules.pullbackComp j ι).app G) ≪≫
          ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm
      exact c F₁ ≪≫ e₄ ≪≫ (Scheme.Modules.restrictFunctor V.ι).mapIso e₅.symm ≪≫ (c _).symm
  · have hz (G : (⊥ : (idl g).subscheme.Opens).toScheme.Modules) : IsZero G :=
      support_eq_empty_iff.1 (Set.eq_empty_of_forall_notMem fun y _ => y.2)
    refine key x ⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩ 0 hx _
      (⊥ : (idl g).subscheme.Opens).ι (fun y hy => (hy ⟨y, rfl⟩).elim) ((hz _).iso (hz _))

end General

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
  {B : GlobalTheory.Vert.Model O} {g : Γ(B.X, ⊤)} {F : B.X.Modules}

theorem of_isFrob (h : LocFreeMod g F) {c : Γ(B.X, ⊤)} (hc : g ^ p * c = (p : Γ(B.X, ⊤))) {F' : B.X.Modules}
    (hF : IsFrob p F F') : LocFreeMod (g ^ p) F' := by
  obtain ⟨hp, ⟨e'⟩⟩ := hF
  intro x
  obtain ⟨U, r, hx, ⟨e⟩⟩ := h x
  refine ⟨U, r, hx, ?_⟩
  let ι := (fibI p B).subschemeι
  let φ := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out hp ≫ ι
  let j := (ι ⁻¹ᵁ U).ι
  have hCp : smulHom (quot r (g ^ p)) (p : Γ(B.X, ⊤)) = 0 := by
    rw [← hc, smulHom_mul, smulHom_quot, comp_zero]
  have hI := FrobQuot.isIso_unit_fibI p B (quot r (g ^ p)) hCp
  obtain ⟨e₁⟩ := nonempty_pullback_quot φ r g ((ι.appTop g) ^ p) (FrobQuot.appTop_absFrob_comp p B hp g)
  obtain ⟨e₂⟩ := nonempty_pullback_quot ι r (g ^ p) ((ι.appTop g) ^ p) (map_pow _ _ _)
  obtain ⟨e₃⟩ := nonempty_pullback_of_range U.ι (j ≫ φ) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact y.2) e
  obtain ⟨e₄⟩ := nonempty_pullback_pushforward ι j U (ι ⁻¹ᵁ U).opensRange_ι.ge
    ((Scheme.Modules.pullbackComp j φ).app F ≪≫ e₃ ≪≫ ((Scheme.Modules.pullbackComp j φ).app _).symm ≪≫
      (Scheme.Modules.pullback j).mapIso (e₁ ≪≫ e₂.symm))
  exact ⟨(Scheme.Modules.pullback U.ι).mapIso e' ≪≫ e₄ ≪≫
    ((Scheme.Modules.pullback U.ι).mapIso (@asIso _ _ _ _ _ hI)).symm⟩

theorem exists_pres (h : LocFreeMod g F) {c : Γ(B.X, ⊤)} {a : O} (ha : a ≠ 0) (hc : g * c = B.const a) :
    ∃ P : Pres B, Nonempty (P.mod ≅ F) := by
  have := isFiniteQC h
  obtain ⟨L, hL⟩ := B.exists_isAmpleLB
  obtain ⟨k, E, φ, hE, hφ⟩ := FrobFilt.ExtPres.exists_epi_of_isAmpleLB hL F
  have := hE.isFiniteQC
  have hmono (r : ℕ) : Mono (smulHom (freeModule B.X (Fin r)) g) := by
    have : Mono (smulHom (freeModule B.X (Fin r)) (B.const a)) :=
      FrobFilt.ExtPres.mono_ψ ⟨r, _, _, VB.isVB_freeModule_fin _ r, VB.isVB_freeModule_fin _ r, _,
        Vert.Model.isIso_genRes_map_smulHom _ ha⟩
    rw [← hc, mul_comm, smulHom_mul] at this
    exact mono_of_mono _ (smulHom _ c)
  have hK : VB.IsVB (kernel φ) k := by
    intro x
    obtain ⟨U, r, hx, ⟨e⟩⟩ := h x
    have := hmono r
    let R := Scheme.Modules.pullback U.ι
    have : Mono (R.map (smulHom (freeModule B.X (Fin r)) g)) := mono_pullback_map _ _
    let e' : R.obj F ≅ cokernel (R.map (smulHom (freeModule B.X (Fin r)) g)) := e ≪≫ PreservesCokernel.iso R _
    have h₁ := FrobFilt.ExtPres.isVB_kernel _ (R.map φ ≫ e'.hom) (hE.pullback U.ι)
      ((VB.isVB_freeModule_fin _ r).pullback U.ι) ((VB.isVB_freeModule_fin _ r).pullback U.ι)
    let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
    have : Epi S.g := hφ
    have hS := (exact_map_pullback U.ι (ShortComplex.exact_kernel φ)).1
    have : Mono (S.map R).f := mono_pullback_map _ (kernel.ι φ)
    have e₁ : kernel (R.map φ) ≅ R.obj (kernel φ) :=
      IsLimit.conePointUniqueUpToIso (limit.isLimit _) hS.fIsKernel
    have h₂ := h₁.of_iso (kernelCompMono (R.map φ) e'.hom ≪≫ e₁ ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm)
    obtain ⟨V, s, hV, hs⟩ := h₂ ⟨x, hx⟩
    exact ⟨U.ι ''ᵁ V, s, ⟨⟨x, hx⟩, hV, rfl⟩, (VB.isFrame_restrict_iff U.ι s).1 hs⟩
  have e' : cokernel (kernel.ι φ) ≅ F := IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel φ))
  have hz : IsZero (B.genRes.obj F) := by
    have := Vert.Model.isIso_genRes_map_smulHom F ha
    rw [← hc, smulHom_mul, smulHom_eq_zero h, comp_zero, Functor.map_zero] at this
    exact IsZero.of_mono_zero _ (B.genRes.obj F)
  have hm : Mono (B.genRes.map (kernel.ι φ)) := mono_pullback_map _ _
  have he : Epi (B.genRes.map (kernel.ι φ)) := Preadditive.epi_of_isZero_cokernel _
    ((hz.of_iso (B.genRes.mapIso e')).of_iso (PreservesCokernel.iso B.genRes (kernel.ι φ)).symm)
  exact ⟨⟨k, E, kernel φ, hE, hK, kernel.ι φ, isIso_of_mono_of_epi _⟩, ⟨e'⟩⟩

end Model

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (g : Γ(B.X, ⊤)) (F : B.X.Modules), LocFreeMod g F → ((∃ c : Γ(B.X, ⊤), g * c = (p : Γ(B.X, ⊤))) → Kills g F ∧ ∃ P : Pres B, Nonempty (P.mod ≅ F)) ∧ ((∃ c : Γ(B.X, ⊤), g ^ p * c = (p : Γ(B.X, ⊤))) → ∀ F' : B.X.Modules, IsFrob p F F' → LocFreeMod (g ^ p) F') ∧ ((∃ c : Γ(B.X, ⊤), g * c = (p : Γ(B.X, ⊤))) → ∀ (F₁ : B.X.Modules) (i : F₁ ⟶ F) (q : F ⟶ F₁), i ≫ q = 𝟙 F₁ → LocFreeMod g F₁) := by
  intro O _ _ _ p _ _ _ B g F h
  refine ⟨fun ⟨c, hc⟩ => ⟨smulHom_eq_zero h, ?_⟩, fun ⟨c, hc⟩ F' hF => of_isFrob p h hc hF,
    fun _ F₁ i q hiq => of_retract h i q hiq⟩
  exact exists_pres h (a := (p : O)) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    (hc.trans (map_natCast _ _).symm)

end GlobalTheory.LocFreeQuot
