import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeClosureStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreRefineLineBundlesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRankStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeDedekindTwistStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateOmegaCoherentStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionWeilPullbackStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelCommonRefinementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalSchemeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundleStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TopHodge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Lin

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem pull_map (L : Lat ξ E) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (φ : E →ₗ[Ω] E') :
    (L.map φ).pull ξ' g (AddMonoidHom.id E') = (L.pull ξ' g (AddMonoidHom.id E)).map φ := by
  funext p
  show Submodule.span _ _ = Submodule.map _ (Submodule.span _ _)
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨h, e, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, ⟨h, u, hu, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨h, e, he, hu⟩, rfl⟩
    exact ⟨h, φ e, ⟨e, he, rfl⟩, congrArg φ hu⟩

theorem span_of_isVBOn {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {V : Submodule Ω E} (h : L.IsVBOn T r V)
    {p : Cpt ξ} (hp : p ∈ T) : Submodule.span Ω (L p : Set E) = V := by
  obtain ⟨U, hU, b, hb, H⟩ := h p hp
  rw [(H p hp hU).2, Submodule.span_span_of_tower, hb]

theorem span_map_top (L : Lat ξ E) (φ : E →ₗ[Ω] E') (hφ : Function.Surjective φ) (p : Cpt ξ)
    (h : Submodule.span Ω (L p : Set E) = ⊤) : Submodule.span Ω ((L.map φ) p : Set E') = ⊤ := by
  have : ((L.map φ) p : Set E') = φ '' (L p : Set E) := rfl
  rw [this, ← Submodule.map_span, h, Submodule.map_top, LinearMap.range_eq_top.2 hφ]

theorem isVBOn_mono {L : Lat ξ E} {r : ℕ} {V : Submodule Ω E} (h : L.IsVB r V) (T : Set (Cpt ξ)) :
    L.IsVBOn T r V := fun p _ => by
  obtain ⟨U, hU, b, hb, H⟩ := h p trivial
  exact ⟨U, hU, b, hb, fun q _ hq => H q trivial hq⟩

theorem eigSp_indep {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E) {I : Type} (σ : I → (O →+* Ω))
    (hσ : Function.Injective σ) : iSupIndep fun s => eigSp ρ (σ s) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : O => ρ a)
    (fun a b φ => Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.all b a).map ρ) φ)
  have h2 := h.comp (f := fun s => (σ s : O → Ω)) (fun s t hst => hσ (DFunLike.coe_injective hst))
  refine h2.mono fun s => ?_
  refine iInf_mono fun a v hv => ?_
  refine Module.End.eigenspace_le_maxGenEigenspace ?_
  rw [Module.End.mem_eigenspace_iff]
  simpa [sub_eq_zero] using hv

theorem frame_dualRestrict (L : Lat ξ E) (p : Cpt ξ) {I : Type} (V : I → Submodule Ω E) (hV : iSupIndep V)
    (htop : Submodule.span Ω (L p : Set E) = ⊤) (hL : L p = ⨆ s, (L.inter (V s)) p) (s : I) {r : ℕ} (b : Fin r → E)
    (hb : Submodule.span Ω (Set.range b) = V s) (hf : (L.inter (V s)).IsFrameAt b p) :
    ∃ (r : ℕ) (g : Fin r → Module.Dual Ω (V s)), (L.dual.map (V s).dualRestrict).IsFrameAt g p := by
  classical
  have hc : IsCompl (V s) (⨆ t ≠ s, V t) := by
    refine ⟨hV s, codisjoint_iff.2 (top_le_iff.1 ?_)⟩
    rw [← htop, Submodule.span_le, hL]
    intro e he
    refine Submodule.iSup_induction (motive := fun e => e ∈ V s ⊔ ⨆ t ≠ s, V t) _ he (fun t e he => ?_) (zero_mem _)
      (fun _ _ => add_mem)
    by_cases h : t = s
    · subst h; exact Submodule.mem_sup_left he.2
    · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem t (Submodule.mem_iSup_of_mem h he.2))
  let π := Submodule.linearProjOfIsCompl _ _ hc
  have hπ : ∀ e ∈ L p, (π e : E) ∈ L p := by
    intro e he
    rw [hL] at he
    refine Submodule.iSup_induction (motive := fun e => (π e : E) ∈ L p) _ he (fun t e he => ?_) (by simp)
      (fun _ _ h1 h2 => by simpa using add_mem h1 h2)
    by_cases h : t = s
    · subst h
      have : π e = ⟨e, he.2⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨e, he.2⟩
      rw [this]; exact he.1
    · have : π e = 0 := Submodule.linearProjOfIsCompl_apply_right' hc
        (Submodule.mem_iSup_of_mem t (Submodule.mem_iSup_of_mem h he.2))
      rw [this]; exact zero_mem _
  have hbm : ∀ i, b i ∈ V s := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hbL : ∀ i, b i ∈ L p := fun i => by
    have : b i ∈ (L.inter (V s)) p := by rw [hf.2]; exact Submodule.subset_span ⟨i, rfl⟩
    exact this.1
  let B : Module.Basis (Fin r) Ω (V s) := (Module.Basis.span hf.1).map (LinearEquiv.ofEq _ _ hb)
  have hB : ∀ i, (B i : E) = b i := fun i => by simp [B]
  have hco : ∀ (v : V s), (v : E) ∈ L p → ∀ i, B.coord i v ∈ regAt ξ p := by
    intro v hv i
    have h1 : (v : E) ∈ (L.inter (V s)) p := ⟨hv, v.2⟩
    rw [hf.2, Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hcv⟩ := h1
    have : v = ∑ j, (c j : Ω) • B j := Subtype.ext (by rw [← hcv]; simp [hB]; rfl)
    rw [this]
    simp [Finsupp.single_apply]
  refine ⟨r, fun i => B.coord i, ?_, le_antisymm ?_ ?_⟩
  · simpa [Module.Basis.coe_dualBasis] using B.dualBasis.linearIndependent
  · rintro _ ⟨w, hw, rfl⟩
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => ⟨w (b i), hw _ (hbL i)⟩, B.ext fun j => ?_⟩
    simp [Finsupp.single_apply, hB, Subring.smul_def]
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨B.coord i ∘ₗ π, fun e he => hco _ (hπ e he) i, ?_⟩
    ext v
    exact congrArg (B.coord i) (Submodule.linearProjOfIsCompl_apply_left hc v)

end Lin

section Sch

variable {X : Scheme.{0}} {Ω K : Type} [Field Ω] [Field K]

theorem exists_factor (ξ₀ : Spec (CommRingCat.of K) ⟶ X) (h₀ : IsCptGen ξ₀) (z : Spec (CommRingCat.of Ω) ⟶ X)
    (h : z (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ ξ₀ (IsLocalRing.closedPoint (CommRingCat.of K))) : ∃ i : K →+* Ω, z = Spec.map (CommRingCat.ofHom i) ≫ ξ₀ := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
  refine ⟨(inv (Scheme.stalkClosedPointTo ξ₀) ≫ X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo z).hom, ?_⟩
  have e₀ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀
  have e₁ : Spec.map (inv (Scheme.stalkClosedPointTo ξ₀)) ≫ ξ₀ = X.fromSpecStalk _ :=
    (congrArg (Spec.map (inv (Scheme.stalkClosedPointTo ξ₀)) ≫ ·) e₀.symm).trans (by
      rw [← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id, Category.id_comp])
  have e₂ := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) h
  refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm.trans ?_
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
  exact congrArg (Spec.map (Scheme.stalkClosedPointTo z) ≫ ·) (e₂.symm.trans
    (congrArg (Spec.map (X.presheaf.stalkSpecializes h) ≫ ·) e₁.symm))

theorem dualMap_id (R : Type) [CommRing R] : dualMap (RingHom.id R) = RingHom.id _ := by
  ext a <;> simp [dualMap]

theorem lat_stable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
    (M : LieModel G ξ E) (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E) (h : M.IsDiffOf a A) (p : Cpt ξ) :
    ∀ e ∈ M.lat p, A e ∈ M.lat p := by
  have : M.lat p ≤ (M.lat p).comap (A.restrictScalars (regAt ξ p)) := by
    refine Submodule.span_le.2 ?_
    rintro e ⟨v, hv, he⟩
    refine Submodule.subset_span ⟨v ≫ a, ?_, ?_⟩
    · unfold IsTanAt at hv ⊢
      rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]
    · show (M.pt (A e)).left = _
      rw [h e, Over.comp_left, he, Over.comp_left]
      exact Category.assoc _ _ _
  exact fun e he => this he

end Sch

section Common

theorem common₂ (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x)
    (B₁ : Type) [Finite B₁] (E₁ : Type) [AddCommGroup E₁] [Module Ω E₁] [FiniteDimensional Ω E₁]
    (L₁ : B₁ → Lat M.ξ E₁) (B₂ : Type) [Finite B₂] (E₂ : B₂ → Type) [∀ b, AddCommGroup (E₂ b)]
    [∀ b, Module Ω (E₂ b)] [∀ b, FiniteDimensional Ω (E₂ b)] (L₂ : ∀ b, Lat M.ξ (E₂ b))
    (h₁ : ∀ b, (L₁ b).IsCohOn Set.univ) (h₂ : ∀ b, (L₂ b).IsCohOn Set.univ)
    (s₁ : ∀ b p, Submodule.span Ω (L₁ b p : Set E₁) = ⊤) (s₂ : ∀ b p, Submodule.span Ω (L₂ b p : Set (E₂ b)) = ⊤) :
    ∃ (κ' : Type) (_ : Finite κ') (y : κ' → Ω) (M' : PModel ℤ y) (f : M'.X ⟶ M.X),
      GlobalTheory.CompanionTheory.Ar.Dominates M'.ξ M.ξ f (RingHom.id Ω) ∧ Flat.NormalCpt M'.ξ ∧ (∀ p' : Cpt M'.ξ, ∃ l, InChart M'.ξ x l p') ∧
      (∀ b, ((L₁ b).pull M'.ξ f (AddMonoidHom.id E₁)).IsVB (Module.finrank Ω E₁) ⊤) ∧
      (∀ b, ((L₂ b).pull M'.ξ f (AddMonoidHom.id (E₂ b))).IsVB (Module.finrank Ω (E₂ b)) ⊤) ∧
      ∀ p : Cpt M.ξ, (∀ b, ∃ (r : ℕ) (g : Fin r → E₁), (L₁ b).IsFrameAt g p) →
        (∀ b, ∃ (r : ℕ) (g : Fin r → E₂ b), (L₂ b).IsFrameAt g p) → NormAt M'.ξ f (RingHom.id Ω) p := by
  let F : B₁ ⊕ B₂ → Type := fun b => match b with
    | .inl _ => E₁
    | .inr b => E₂ b
  letI iA : ∀ b, AddCommGroup (F b) := fun b => match b with
    | .inl _ => inferInstanceAs (AddCommGroup E₁)
    | .inr b => inferInstanceAs (AddCommGroup (E₂ b))
  letI iM : ∀ b, Module Ω (F b) := fun b => match b with
    | .inl _ => inferInstanceAs (Module Ω E₁)
    | .inr b => inferInstanceAs (Module Ω (E₂ b))
  let L : ∀ b, Lat M.ξ (F b) := fun b => match b with
    | .inl b => L₁ b
    | .inr b => L₂ b
  haveI iF : ∀ b, FiniteDimensional Ω (⊤ : Submodule Ω (F b)) := fun b => match b with
    | .inl _ => inferInstanceAs (FiniteDimensional Ω (⊤ : Submodule Ω E₁))
    | .inr b => inferInstanceAs (FiniteDimensional Ω (⊤ : Submodule Ω (E₂ b)))
  obtain ⟨c₀, hc₀⟩ := M.tie.cover ⟨genPt M.ξ, specializes_rfl⟩
  obtain ⟨κ', hκ', y, M', f, hd, hn, hch, hvb, hnorm⟩ := GlobalTheory.T.flag_model_common_refinement ℤ Ω κ x M Unit (fun _ => κ) (fun _ => x)
    (B₁ ⊕ B₂) F L (fun _ => ⊤) (fun _ => ⟨c₀, hc₀.1⟩)
    (fun b => match b with
      | .inl b => h₁ b
      | .inr b => h₂ b)
    (fun b => match b with
      | .inl b => s₁ b
      | .inr b => s₂ b)
  refine ⟨κ', hκ', y, M', f, hd, hn, hch (), fun b => ?_, fun b => ?_, fun p g₁ g₂ => hnorm p (fun _ => M.tie.cover p)
    fun b => match b with
      | .inl b => g₁ b
      | .inr b => g₂ b⟩
  · rw [← finrank_top Ω E₁]; exact hvb (.inl b)
  · rw [← finrank_top Ω (E₂ b)]; exact hvb (.inr b)

end Common

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}

theorem tors_weil (hW : Out.WeilSt) {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} {f : X ⟶ Y.X}
    {y₀ : Sp Ω ⟶ Xo.XF c} {t : SAB H X} (m : SABMap t Y.t f) (h : ξ ≫ f = y₀ ≫ Y.j) {n : ℕ} (hn : 1 ≤ n)
    (hT : FullTorsion Y.t.G (y₀ ≫ Y.j) n) (hζ : ∃ ζ : Ω, IsPrimitiveRoot ζ n) :
    FullTorsion t.G ξ n ∧ ∃ e, GenWeil t.G t.PP.L ξ n e := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_generic_weil_pairing hW E H D l _ _ _ _ _ Y.oF Y.t Y.j Y.m Ω y₀ n hn hT hζ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.full_torsion_weil_pullback Y.X X Ω Ω (y₀ ≫ Y.j) ξ f (RingHom.id Ω)
    (by unfold GlobalTheory.CompanionTheory.Ar.Dominates; rw [h]; simp) Y.t.G t.G m.φ m.cart Y.t.PP.L t.PP.L Y.t.PP.isLB t.PP.isLB
    (m.lin.imp fun _ h => h.1) n hT
  obtain ⟨e', he', -⟩ := h2 e he
  exact ⟨h1, e', he'⟩

theorem exists_cst {Ω : Type} [Field Ω] (y₀ : Sp Ω ⟶ Xo.XF c) :
    ∃ cst : c.F →+* Ω, y₀ ≫ Y.j ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
  refine ⟨(Spec.preimage (y₀ ≫ pullback.snd _ _)).hom, ?_⟩
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc]
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem frame_om {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Sp Ω ⟶ X} (hg : IsCptGen ξ)
    (hN : Flat.NormalCpt ξ) (t : SAB H X) {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li)
    (ρ : 𝓞 E →+* Module.End Ω Li) (hρ : M.IsActOf t.act.act ρ) (cst : c.F →+* Ω) (q : Cpt ξ) (hq : q ∈ genFib ξ)
    (s : CMType H ⊕ CMType H) : ∃ (r : ℕ) (g : Fin r → Module.Dual Ω (eigSp ρ (cst.comp (labelEmb c s)))),
      (M.omLat.map (eigSp ρ (cst.comp (labelEmb c s))).dualRestrict).IsFrameAt g q := by
  classical
  obtain ⟨hinj, hcard⟩ := GlobalTheory.T.label_embedding_injective E H l c
  have hσ : Function.Injective fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s) := fun s s' h =>
    hinj (RingHom.ext fun a => cst.injective (RingHom.congr_fun h a))
  have hlat := (GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ t.G Li M hg t.semi.smooth).1
  obtain ⟨hvb, hsup⟩ := GlobalTheory.T.lattice_eigen_vector_bundle X Ω ξ Li E ρ M.lat {q} _ (CMType H ⊕ CMType H) _ hg hσ
    (by rw [← hcard, Nat.card_eq_fintype_card]) (isVBOn_mono hlat _)
    (fun p _ a => by haveI := t.act.hom a; exact lat_stable M _ _ (hρ a) p)
    (fun p _ s a => hN p _ ((((RingOfIntegers.isIntegral a).map_of_comp_eq (RingHom.id ℤ) (cst.comp (labelEmb c s))
      (Subsingleton.elim _ _))).tower_top))
    (by
      rintro p rfl
      have h := hq _ (Int.natAbs_pos.2 (NumberField.discr_ne_zero E))
      rcases Int.natAbs_eq (NumberField.discr E) with e | e
      · rw [e]; simpa using h
      · rw [e]
        refine ⟨by simpa using h.1, by simpa using h.2.1, ?_⟩
        simpa using h.2.2)
  obtain ⟨U, hU, b, hb, hf⟩ := hvb s q rfl
  exact frame_dualRestrict M.lat q _ (eigSp_indep ρ _ hσ) (span_of_isVBOn hlat trivial) (hsup q rfl) s b hb
    (hf q rfl hU)

end Main

theorem exists_hodgeCpt_htFree : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (R : ℕ → ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (M₁ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (f₁ : M₁.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c), Flat.NormalCpt M₁.ξ → M₁.ξ ≫ f₁ = y₀ ≫ Y.j → f₁ (GlobalTheory.CompanionTheory.Ar.genPt M₁.ξ) ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, 4 ≤ R p) → (∀ p ∈ S, FullTorsion Y.t.G (M₁.ξ ≫ f₁) (p ^ R p)) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ R p)) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐 : HodgeCpt Y S y') (g : 𝔐.X ⟶ M₁.X), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ M₁.ξ g (RingHom.id Ω) ∧ 𝔐.f = g ≫ f₁ ∧ 𝔐.R = R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ ∀ q ∈ genFib M₁.ξ, IsoAt 𝔐.ξ g (RingHom.id Ω) q := by
  intro hW E _ _ _ H D l Xo c Y S R Ω _ _ K _ J _ y M₁ f₁ y₀ hN₁ hy₀ hgen hS hdisc hR hT hζ
  have hpos : ∀ p ∈ S, 1 ≤ p ^ R p := fun p hp => Nat.one_le_pow _ _ (hS p hp).pos
  rw [hy₀] at hT
  obtain ⟨cst, hcst⟩ := exists_cst (Y := Y) y₀
  obtain ⟨t₁, ⟨m₁⟩⟩ : ∃ t₁ : SAB H M₁.X, Nonempty (SABMap t₁ Y.t f₁) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.proved_CubePullSt f₁ Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨Li, _, _, ⟨N₁⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t₁.G Ω M₁.ξ
  obtain ⟨ρ, hρ₁, -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ t₁.G Ω M₁.ξ Li N₁ (𝓞 E) t₁.act.act t₁.act.hom
    t₁.act.one t₁.act.mul t₁.act.add
  have hcst₁ : M₁.ξ ≫ f₁ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [← Category.assoc, hy₀, Category.assoc, hcst]
  obtain ⟨hfd, hrk⟩ := GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y _ Ω M₁.ξ f₁ y₀ t₁ m₁ Li N₁ ρ cst hy₀ hcst₁ hρ₁
  haveI : IsNoetherian M₁.X := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω M₁.ξ ℤ _ _ M₁.tie).2 M₁.all).1
  have hom₁ := (GlobalTheory.T.lie_omega_lattice_vector_bundle _ Ω M₁.ξ t₁.G Li N₁ M₁.tie.gen t₁.semi.smooth).2
  have htw₁ := fun p hp => tors_weil hW m₁ hy₀ (hpos p hp) (hT p hp) (hζ p hp)
  have hcoh : ∀ p ∈ S, (N₁.htOm t₁.PP.L (p ^ R p)).IsCohOn Set.univ ∧
      ∀ q, ∀ u ∈ N₁.omLat q, (p ^ R p) • u ∈ N₁.htOm t₁.PP.L (p ^ R p) q := fun p hp => by
    obtain ⟨h1, e, he⟩ := htw₁ p hp
    obtain ⟨h2, h3⟩ := GlobalTheory.T.hodge_tate_omega_coherent _ Ω M₁.ξ M₁.tie.gen hN₁ t₁.G t₁.semi t₁.PP.L _ (hpos p hp) h1 e he Li N₁
    exact ⟨h2, fun q => (h3 q).1⟩
  have hspan : ∀ p ∈ S, ∀ q, Submodule.span Ω (N₁.htOm t₁.PP.L (p ^ R p) q : Set (Module.Dual Ω Li)) = ⊤ := by
    intro p hp q
    rw [eq_top_iff, ← span_of_isVBOn hom₁ (p := q) trivial, Submodule.span_le]
    intro u hu
    have h0 : ((p ^ R p : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 (hpos p hp))
    have := Submodule.smul_mem _ ((p ^ R p : ℕ) : Ω)⁻¹ (Submodule.subset_span (R := Ω) ((hcoh p hp).2 q u hu))
    rwa [← Nat.cast_smul_eq_nsmul Ω, inv_smul_smul₀ h0] at this
  have heq : ∀ p ∈ S, ∀ q ∈ genFib M₁.ξ, N₁.htOm t₁.PP.L (p ^ R p) q = N₁.omLat q := by
    intro p hp q hq
    refine le_antisymm (N₁.htOm_le _ _ q) fun u hu => ?_
    have h0 := hq _ (hpos p hp)
    have := Submodule.smul_mem _ (⟨_, h0.2.2⟩ : regAt M₁.ξ q) ((hcoh p hp).2 q u hu)
    rwa [← Nat.cast_smul_eq_nsmul Ω, Subring.smul_def, inv_smul_smul₀ h0.1] at this
  obtain ⟨κ', _, x', M', g, hdom, hN', hch, hvb₁, hvb₂, hnorm⟩ := common₂ Ω _ _ M₁ S (Module.Dual Ω Li)
    (fun p => N₁.htOm t₁.PP.L (p.1 ^ R p.1)) (S × (CMType H ⊕ CMType H))
    (fun b => Module.Dual Ω (eigSp ρ (cst.comp (labelEmb c b.2))))
    (fun b => (N₁.htOm t₁.PP.L (b.1.1 ^ R b.1.1)).map (eigSp ρ (cst.comp (labelEmb c b.2))).dualRestrict)
    (fun p => (hcoh p.1 p.2).1)
    (fun b => (GlobalTheory.T.coherent_lattice_closure _ Ω M₁.ξ _ _ _ (N₁.htOm t₁.PP.L (b.1.1 ^ R b.1.1)) _).2.1 _ (hcoh b.1.1 b.1.2).1)
    (fun p => hspan p.1 p.2)
    (fun b q => span_map_top _ _ Subspace.dualRestrict_surjective q (hspan b.1.1 b.1.2 q))
  have hg : M'.ξ ≫ g = M₁.ξ := by
    have := hdom
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this
    simpa using this
  obtain ⟨t', ⟨m'⟩⟩ : ∃ t' : SAB H M'.X, Nonempty (SABMap t' t₁ g) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.proved_CubePullSt g t₁
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m'
  obtain ⟨N', hN⟩ : ∃ N' : LieModel t'.G M'.ξ Li, ∀ e, (N'.pt e).left ≫ m'.φ = (N₁.pt e).left := by
    have key : ∀ (z : Sp Ω ⟶ M₁.X), M'.ξ ≫ g = z → ∀ N : LieModel t₁.G z Li,
        ∃ N' : LieModel t'.G M'.ξ Li, ∀ e, (N'.pt e).left ≫ m'.φ = (N.pt e).left := by
      rintro z rfl
      exact (LiePull.lieModel_pullback _ _ t₁.G t'.G g m'.φ m'.cart Ω M'.ξ Li).1
    exact key _ hg N₁
  have hρ' : N'.IsActOf t'.act.act ρ := by
    intro a e
    refine Over.OverMorphism.ext (m'.cart.1.hom_ext ?_ ?_)
    · rw [Over.comp_left, Category.assoc, m'.act, ← Category.assoc, hN, hN, hρ₁ a e, Over.comp_left]
    · rw [Over.w, Over.w]
  have hy' : M'.ξ ≫ g ≫ f₁ = y₀ ≫ Y.j := by rw [← Category.assoc, hg, hy₀]
  have hcst' : M'.ξ ≫ (g ≫ f₁) ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [← Category.assoc, hy', Category.assoc, hcst]
  haveI : IsNoetherian M'.X := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω M'.ξ ℤ _ _ M'.tie).2 M'.all).1
  have htw' := fun p hp => tors_weil hW m hy' (hpos p hp) (hT p hp) (hζ p hp)
  have hpull : ∀ p ∈ S, N'.htOm t'.PP.L (p ^ R p) =
      (N₁.htOm t₁.PP.L (p ^ R p)).pull M'.ξ g (AddMonoidHom.id _) := fun p hp => by
    obtain ⟨h1, e, he⟩ := htw₁ p hp
    obtain ⟨-, e', he'⟩ := htw' p hp
    exact (GlobalTheory.T.hodge_tate_weil_pullback _ Ω M₁.ξ M₁.tie.gen hN₁ t₁.G t₁.semi t₁.PP.L _ (hpos p hp) h1 e he Li N₁ M'.X Ω M'.ξ
      M'.tie.gen hN' g (RingHom.id Ω) hdom t'.G m'.φ m'.cart t'.PP.L e' he' Li N' (AddMonoidHom.id _)
      (AddMonoidHom.id _) (fun v => by
        rw [dualMap_id]
        exact (hN v).trans ((congrArg (· ≫ (N₁.pt v).left) (Spec.map_id _)).trans (Category.id_comp _)).symm) (fun _ _ => rfl)).1
  have hf₁ : ∀ p ∈ S, (N'.htOm t'.PP.L (p ^ R p)).IsVB (Module.finrank Ω Li) ⊤ := fun p hp => by
    rw [hpull p hp, ← Subspace.dual_finrank_eq]
    exact hvb₁ ⟨p, hp⟩
  have hf₂ : ∀ p ∈ S, ∀ s, ((N'.htOm t'.PP.L (p ^ R p)).map
      (eigSp ρ (cst.comp (labelEmb c s))).dualRestrict).IsVB (labelRk D s) ⊤ := fun p hp s => by
    rw [hpull p hp, ← pull_map, ← hrk s, ← Subspace.dual_finrank_eq]
    exact hvb₂ (⟨p, hp⟩, s)
  have hvb := GlobalTheory.T.eigen_lattice_dedekind_twist hW E H D l Xo c Y M'.X Ω M'.ξ (g ≫ f₁) y₀ t' m Li N' ρ cst S R hy' hcst' hρ' M'.tie.gen hN'
    hS hdisc (fun p hp => (htw' p hp).1) hζ hf₂
  obtain ⟨K', _, J', _, y', bk, bx, -, hbk, hbx, htie, -⟩ := GlobalTheory.T.segre_refine_line_bundles ℤ Ω κ' x' M' K J y Empty
    (fun a => a.elim) hch (fun a => a.elim)
  obtain ⟨Ω₀, _, _, n, x₀, z₀, htie₀, -, hz₀⟩ := GlobalTheory.T.generic_point_normal_coords E H D l Xo c Y _ hgen
  obtain ⟨fn, hfn⟩ := exists_factor (z₀ ≫ Y.j) htie₀.gen (M'.ξ ≫ g ≫ f₁) (by
    show genPt (M'.ξ ≫ g ≫ f₁) ⤳ genPt (z₀ ≫ Y.j)
    rw [hz₀, ← Category.assoc, hg]
    exact specializes_rfl)
  let 𝔐 : HodgeCpt Y S y' :=
    { X := M'.X, ξ := M'.ξ, all := M'.all, tie := htie
      normal := ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω M'.ξ M'.tie.gen M'.all).2).1 hN'
      f := g ≫ f₁, Ω₀ := Ω₀, ξ₀ := z₀ ≫ Y.j, gen₀ := htie₀.gen, cst := cst, cst_over := hcst', fn := fn
      fn_over := hfn, t := t', m := m, Li := Li, M := N', ρ := ρ, act := hρ', S_prime := hS, R := R, R_ge := hR
      tors := fun p hp => (htw' p hp).1, vb := hvb }
  refine ⟨K', inferInstance, J', inferInstance, y', bk, bx, 𝔐, g, hbk, hbx, hdom, rfl, rfl,
    fun p hp => ⟨isVBOn_mono (hf₁ p hp) _, fun s => isVBOn_mono (hf₂ p hp s) _⟩, fun q hq => ?_⟩
  refine GlobalTheory.T.normal_iso_of_integrally_closed _ Ω M₁.ξ _ M'.ξ g q (hnorm q (fun p => ?_) fun b => ?_) (hN₁ q)
  · obtain ⟨U, hU, b, -, hb⟩ := hom₁ q trivial
    exact ⟨_, b, (hb q trivial hU).1, (heq p.1 p.2 q hq).trans (hb q trivial hU).2⟩
  · obtain ⟨r, w, hw⟩ := frame_om M₁.tie.gen hN₁ t₁ N₁ ρ hρ₁ cst q hq b.2
    refine ⟨r, w, hw.1, Eq.trans ?_ hw.2⟩
    show Submodule.map _ _ = Submodule.map _ _
    rw [heq b.1.1 b.1.2 q hq]

end GlobalTheory.CompanionTheory.Ar.TopHodge
