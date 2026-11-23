import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSubschemeCounitIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CkPresentationInvariant

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.ChainPts

namespace GlobalTheory.ChainPts.PrePull

local notation "pb" => Scheme.Modules.pullback

theorem mono_pullback_of_resolution {X Y : Scheme.{0}} (f : Y ⟶ X) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] {K A : X.Modules} (ι : K ⟶ A) (q : A ⟶ S.X₃) (w : ι ≫ q = 0)
    (hT : (ShortComplex.mk ι q w).ShortExact) {r : ℕ} (hA : VB.IsVB A r) [Mono ((pb f).map ι)] :
    Mono ((pb f).map S.f) := by
  obtain ⟨h₁, h₂⟩ := PresMod.shortExact_pullback S.g q S.f ι S.zero w hS hT
  have := FlagPull.isQuasicoherent_X₂ _ h₂ hA
  have hm := FlagPull.mono_pullback_map_f f _ h₂ hA
  have := h₁.epi_g
  have hex := (QCoh.exact_map_pullback f h₁.exact).1
  dsimp only at hm
  refine Preadditive.mono_of_cancel_zero _ fun {W} z hz => ?_
  obtain ⟨W', u, hu, e, he⟩ := hex.exact_up_to_refinements
    (z ≫ (pb f).map (pullback.lift S.f 0 (by simp) : S.X₁ ⟶ pullback S.g q)) (by
      change (z ≫ _) ≫ (pb f).map (pullback.fst S.g q) = 0
      rw [Category.assoc, ← Functor.map_comp, pullback.lift_fst, hz])
  change u ≫ z ≫ _ = e ≫ (pb f).map (pullback.lift 0 ι _) at he
  have he0 : e = 0 := by
    have h := he =≫ (pb f).map (pullback.snd S.g q)
    simp only [Category.assoc, ← Functor.map_comp, pullback.lift_snd, Functor.map_zero, comp_zero] at h
    exact zero_of_comp_mono _ h.symm
  subst he0
  exact zero_of_comp_mono _ (zero_of_epi_comp u (he.trans zero_comp))

theorem locFreeMod_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) {a : Γ(X, ⊤)} {F : X.Modules} (h : LocFreeMod a F) :
    LocFreeMod (f.appTop a) ((pb f).obj F) := fun y => by
  obtain ⟨U, r, hx, ⟨e⟩⟩ := h (f y)
  obtain ⟨e₁⟩ := LocFreeQuot.nonempty_pullback_quot f r a _ rfl
  obtain ⟨e₂⟩ := LocFreeQuot.nonempty_pullback_of_range U.ι ((f ⁻¹ᵁ U).ι ≫ f) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact y.2) e
  exact ⟨f ⁻¹ᵁ U, r, hx, ⟨(Scheme.Modules.pullbackComp _ f).app F ≪≫ e₂ ≪≫
    ((Scheme.Modules.pullbackComp _ f).app _).symm ≪≫ (pb _).mapIso e₁⟩⟩

def bcMap {C D C' D' : Type 1} [Category.{0} C] [Category.{0} D] [Category.{0} C'] [Category.{0} D']
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj' : L' ⊣ R') {G : C ⥤ C'} {G₀ : D ⥤ D'}
    (c : G ⋙ L' ≅ L ⋙ G₀) {P : C ⥤ D} {P' : C' ⥤ D'} (b : P ⋙ G₀ ≅ G ⋙ P') : (P ⋙ R) ⋙ G ⟶ G ⋙ (P' ⋙ R') where
  app M := adj'.unit.app (G.obj (R.obj (P.obj M))) ≫
    R'.map (c.hom.app (R.obj (P.obj M)) ≫ G₀.map (adj.counit.app (P.obj M)) ≫ b.hom.app M)
  naturality M N f := by
    have h₁ := adj'.unit.naturality (G.map (R.map (P.map f)))
    have h₂ := c.hom.naturality (R.map (P.map f))
    have h₃ := adj.counit.naturality (P.map f)
    have h₄ := b.hom.naturality f
    dsimp at h₁ h₂ h₃ h₄ ⊢
    rw [reassoc_of% h₁, Category.assoc, ← R'.map_comp, ← R'.map_comp, reassoc_of% h₂, ← G₀.map_comp_assoc, h₃,
      G₀.map_comp_assoc, h₄]
    simp only [Category.assoc]

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
  {B B' : Vert.Model O} (g : Vert.Model.Hom B' B) {Λ : Type} [CommRing Λ]

theorem qc_frobA (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) (M : AM B Λ) [M.V.IsQuasicoherent] :
    (frobA p h M).V.IsQuasicoherent :=
  inferInstanceAs ((Scheme.Modules.pushforward (fibI p B).subschemeι).obj
    ((pb (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h ≫ (fibI p B).subschemeι)).obj M.V)).IsQuasicoherent

theorem pull_frobA (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) (h' : (p : Γ((fibI p B').subscheme, ⊤)) = 0)
    (M : AM B Λ) [M.V.IsQuasicoherent] :
    Nonempty ((pullA g.f).obj (frobA p h M) ≅ frobA p h' ((pullA g.f).obj M)) := by
  obtain ⟨f₀, hf₀⟩ := PullFrob.exists_fib_lift p g
  let i := (fibI p B).subschemeι
  let i' := (fibI p B').subschemeι
  let Fr := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h
  let Fr' := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h'
  have hsq : f₀ ≫ Fr ≫ i = (Fr' ≫ i') ≫ g.f := by
    rw [← Category.assoc, ← GlobalTheory.SS.FrobField.absFrob_nat f₀ p 1 Fact.out h' h, Category.assoc, hf₀,
      Category.assoc]
  let σ : frobFun p h ⋙ pb g.f ⟶ pb g.f ⋙ frobFun p h' :=
    bcMap (Scheme.Modules.pullbackPushforwardAdjunction i) (Scheme.Modules.pullbackPushforwardAdjunction i')
      (G₀ := pb f₀) (Scheme.Modules.pullbackComp i' g.f ≪≫ Scheme.Modules.pullbackCongr hf₀.symm ≪≫
        (Scheme.Modules.pullbackComp f₀ i).symm)
      (Scheme.Modules.pullbackComp f₀ (Fr ≫ i) ≪≫ Scheme.Modules.pullbackCongr hsq ≪≫
        (Scheme.Modules.pullbackComp (Fr' ≫ i') g.f).symm)
  let G := (pb (Fr ≫ i)).obj M.V
  have hk : smulHom ((pb g.f).obj ((Scheme.Modules.pushforward i).obj G)) (p : Γ(B'.X, ⊤)) = 0 := by
    have := VB.pullback_map_smulHom (F := (Scheme.Modules.pushforward i).obj G) g.f (p : Γ(B.X, ⊤))
    rw [map_natCast] at this
    rw [← this, smulHom_pushforward, map_natCast, h, smulHom_zero, Functor.map_zero, Functor.map_zero]
  have h₁ := FrobQuot.isIso_unit_fibI p B' _ hk
  have h₂ := ClosedCounit.isIso_counit_subschemeι (fibI p B) G
  have : IsIso (σ.app M.V) := by
    change IsIso (_ ≫ (Scheme.Modules.pushforward i').map (_ ≫ (pb f₀).map _ ≫ _))
    infer_instance
  exact ⟨Action.mkIso (asIso (σ.app M.V)) fun a => σ.naturality (M.ρ a : M.V ⟶ M.V)⟩

theorem pull_frobA_iter (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) (h' : (p : Γ((fibI p B').subscheme, ⊤)) = 0)
    (M : AM B Λ) [hM : M.V.IsQuasicoherent] (M' : AM B' Λ) (e : M' ≅ (pullA g.f).obj M) (k : ℕ) :
    ((frobA p h)^[k] M).V.IsQuasicoherent ∧
      Nonempty ((frobA p h')^[k] M' ≅ (pullA g.f).obj ((frobA p h)^[k] M)) := by
  induction k with
  | zero => exact ⟨hM, ⟨e⟩⟩
  | succ k ih =>
    obtain ⟨_, ⟨e₁⟩⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨e₂⟩ := pull_frobA p g h h' ((frobA p h)^[k] M)
    exact ⟨qc_frobA p h _, ⟨((frobFun p h').mapAction Λ).mapIso e₁ ≪≫ e₂.symm⟩⟩

theorem pullA_smulA (M : AM B Λ) (a : Γ(B.X, ⊤)) :
    (pullA g.f).map (smulA M a) = smulA ((pullA g.f).obj M) (g.f.appTop a) :=
  Action.Hom.ext (VB.pullback_map_smulHom g.f a)

def modIso (P : EPres B Λ) : (PullHT.EPres.pull g P).mod ≅ (pullA g.f).obj P.mod :=
  (PreservesCokernel.iso (pullA g.f) P.ψ).symm

theorem qc_mod (P : EPres B Λ) : P.mod.V.IsQuasicoherent := by
  have := P.vb.isQuasicoherent
  have := P.vb'.isQuasicoherent
  exact (SheafOfModules.isQuasicoherent _).prop_of_iso (Examples₂.cokV P.ψ).symm
    (inferInstanceAs (cokernel P.ψ.hom).IsQuasicoherent)

theorem isExtA_pull {P₁ P₂ P₃ : EPres B Λ} (h : IsExtA P₁.mod P₂.mod P₃.mod) :
    IsExtA (PullHT.EPres.pull g P₁).mod (PullHT.EPres.pull g P₂).mod (PullHT.EPres.pull g P₃).mod := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := h
  have := hS.epi_g
  have hS' : (S.map (Action.forget _ Λ)).ShortExact := hS.map_of_exact _
  have : (S.map (Action.forget _ Λ)).X₁.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent _).prop_of_iso ((Action.forget _ Λ).mapIso e₁).symm (qc_mod P₁)
  have : Mono P₃.ψ.hom := FrobFilt.ExtPres.mono_ψ P₃.toPres
  have : Mono ((pb g.f).map P₃.ψ.hom) := FrobFilt.ExtPres.mono_ψ (PullHT.EPres.pull g P₃).toPres
  let e : cokernel P₃.ψ.hom ≅ (S.map (Action.forget _ Λ)).X₃ := ((Action.forget _ Λ).mapIso e₃ ≪≫ Examples₂.cokV P₃.ψ).symm
  have hT : (ShortComplex.mk P₃.ψ.hom (cokernel.π _ ≫ e.hom) (by simp)).ShortExact :=
    ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk P₃.ψ.hom (cokernel.π _) (by simp))
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simp))
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  have hm := mono_pullback_of_resolution g.f _ hS' _ _ _ hT P₃.vb
  refine ⟨S.map (pullA g.f), ?_, ⟨(pullA g.f).mapIso e₁ ≪≫ (modIso g P₁).symm⟩,
    ⟨(pullA g.f).mapIso e₂ ≪≫ (modIso g P₂).symm⟩, ⟨(pullA g.f).mapIso e₃ ≪≫ (modIso g P₃).symm⟩⟩
  exact ShortComplex.ShortExact.mk' (hS.exact.map_of_epi_of_preservesCokernel _ inferInstance inferInstance)
    ((Action.forget _ Λ).mono_of_mono_map hm) (inferInstanceAs (Epi ((pullA g.f).map S.g)))

theorem isRootOfP_pull {a : Γ(B.X, ⊤)} {n : ℕ} (h : IsRootOfP p a n) : IsRootOfP p (g.f.appTop a) n := by
  obtain ⟨u, hu⟩ := h
  exact ⟨Units.map g.f.appTop.hom.toMonoidHom u, by
    rw [← map_pow]
    simp [hu, map_mul, map_natCast]⟩

theorem preChain_pull : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B B' : GlobalTheory.Vert.Model O) (g : GlobalTheory.Vert.Model.Hom B' B) (Λ : Type) [CommRing Λ] (o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (P : PreChain p o Lie Om π), ∃ (P' : PreChain p o ((pullA g.f).obj Lie) ((pullA g.f).obj Om) (g.f.appTop π)) (e : (P'.q 0).mod.V ≅ (Scheme.Modules.pullback g.f).obj (P.q 0).mod.V) (e' : (cokernel P'.j).V ≅ (Scheme.Modules.pullback g.f).obj (cokernel P.j).V), P'.j.hom ≫ e.hom = (Scheme.Modules.pullback g.f).map P.j.hom ∧ P'.ρ.hom ≫ e'.hom = (Scheme.Modules.pullback g.f).map P.ρ.hom := by
  intro O _ _ _ p _ _ _ B B' g Λ _ o Lie Om π P
  have h' := FrobQuot.natCast_eq_zero_fibI p B'
  let j' := (pullA g.f).map P.j ≫ (modIso g (P.q 0)).inv
  let c : cokernel j' ≅ (pullA g.f).obj (cokernel P.j) :=
    cokernelCompIsIso _ _ ≪≫ (PreservesCokernel.iso (pullA g.f) P.j).symm
  have := P.ρ_epi
  refine ⟨{
    g := g.f.appTop P.g
    γ := fun n => g.f.appTop (P.γ n)
    π_root := isRootOfP_pull p g P.π_root
    g_root := isRootOfP_pull p g P.g_root
    γ_root := fun n h => isRootOfP_pull p g (P.γ_root n h)
    hp := h'
    q := fun n => PullHT.EPres.pull g (P.q n)
    l := fun n => PullHT.EPres.pull g (P.l n)
    step := fun n h => isExtA_pull g (P.step n h)
    l_free := fun n h => LocFreeQuot.of_iso (locFreeMod_pullback g.f (P.l_free n h))
      ((Action.forget _ Λ).mapIso (modIso g (P.l n))).symm
    l_last := fun n h => ?_
    q_kill := fun n h => ?_
    q_frob := fun n h => ?_
    j := j'
    j_kill := by rw [← pullA_smulA, ← Category.assoc, ← Functor.map_comp, P.j_kill, Functor.map_zero, zero_comp]
    ρ := (pullA g.f).map P.ρ ≫ c.inv
    ρ_epi := epi_comp _ _ }, (Action.forget _ Λ).mapIso (modIso g (P.q 0)), (Action.forget _ Λ).mapIso c, ?_, ?_⟩
  · have := qc_mod (P.l n)
    obtain ⟨e₁⟩ := (pull_frobA_iter p g P.hp h' _ _ (modIso g (P.l n)) (n + 1)).2
    obtain ⟨e₂⟩ := P.l_last n h
    exact ⟨e₁ ≪≫ (pullA g.f).mapIso e₂ ≪≫ PreservesCokernel.iso (pullA g.f) _ ≪≫
      cokernelIsoOfEq (by rw [pullA_smulA, map_natCast])⟩
  · have k := P.q_kill n h
    let e := (Action.forget _ Λ).mapIso (modIso g (P.q (n + 1)))
    unfold Kills at k ⊢
    refine zero_of_comp_mono e.hom ?_
    erw [smulHom_comp e.hom, ← VB.pullback_map_smulHom, k, Functor.map_zero, comp_zero]
  · have := qc_mod (P.q (n + 1))
    obtain ⟨e₁⟩ := (pull_frobA_iter p g P.hp h' _ _ (modIso g (P.q (n + 1))) 1).2
    obtain ⟨e₂⟩ := P.q_frob n h
    exact ⟨modIso g _ ≪≫ (pullA g.f).mapIso e₂ ≪≫ e₁.symm⟩
  · exact congrArg Action.Hom.hom (show j' ≫ (modIso g (P.q 0)).hom = (pullA g.f).map P.j by simp [j'])
  · exact congrArg Action.Hom.hom (show ((pullA g.f).map P.ρ ≫ c.inv) ≫ c.hom = (pullA g.f).map P.ρ by simp)

end GlobalTheory.ChainPts.PrePull

end
