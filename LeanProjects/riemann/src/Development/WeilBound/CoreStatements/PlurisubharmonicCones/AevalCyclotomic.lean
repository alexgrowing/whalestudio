import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLatticeEigenCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalFractionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderAction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SandwichPointOverFieldExtStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.GhModelGeo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace LevelTowerAlt.LocalPrimeBound

section Lin

variable {F V O : Type} [Field F] [AddCommGroup V] [Module F V] [CommRing O]

theorem mem_eigSp {ρ : O →+* Module.End F V} {σ : O →+* F} {x : V} : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem eigSp_indep (ρ : O →+* Module.End F V) {I : Type} (σ : I → (O →+* F))
    (hσ : Function.Injective σ) : iSupIndep fun s => eigSp ρ (σ s) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : O => ρ a)
    (fun a b φ => Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.all b a).map ρ) φ)
  have h2 := h.comp (f := fun s => (σ s : O → F)) (fun s t hst => hσ (DFunLike.coe_injective hst))
  refine h2.mono fun s => ?_
  refine iInf_mono fun a v hv => ?_
  refine Module.End.eigenspace_le_maxGenEigenspace ?_
  rw [Module.End.mem_eigenspace_iff]
  simpa [sub_eq_zero] using hv

theorem mem_of_indep {R : Type} [CommRing R] [Module R V] [Algebra R F] [IsScalarTower R F V] {I : Type}
    (W : I → Submodule F V) (hW : iSupIndep W) (N : I → Submodule R V)
    (hN : ∀ s, N s ≤ (W s).restrictScalars R) (s : I) {x : V} (hx : x ∈ ⨆ t, N t) (hs : x ∈ W s) : x ∈ N s := by
  rw [iSup_split_single N s] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  have h1 : (⨆ t, ⨆ (_ : t ≠ s), N t) ≤ (⨆ t, ⨆ (_ : t ≠ s), W t).restrictScalars R :=
    iSup₂_le fun t ht y hy => (le_iSup₂_of_le (f := fun t (_ : t ≠ s) => W t) t ht le_rfl) (hN t hy)
  have h2 : b ∈ W s := by simpa using (W s).sub_mem hs (hN s ha)
  have h3 : b = 0 := (Submodule.disjoint_def.1 (hW s)) b h2 (h1 hb)
  simpa [h3] using ha

end Lin

section Pt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {R : Type} [CommRing R] [IsLocalRing R]

theorem exists_value (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem value_aeval (hg : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R} (hv : ValAt ξ z a r)
    (f : Polynomial ℤ) (hf : Polynomial.aeval a f = 0) : Polynomial.aeval r f = 0 := by
  obtain ⟨h, s, hs, rfl⟩ := hv
  let φ : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  have e1 := Polynomial.aeval_algHom_apply (genMap ξ ⟨centre z, h⟩).toIntAlgHom s f
  have e2 := Polynomial.aeval_algHom_apply φ.toIntAlgHom s f
  have h0 : Polynomial.aeval s f = 0 := by
    apply hg.inj ⟨centre z, h⟩
    rw [map_zero]
    have : (genMap ξ ⟨centre z, h⟩).toIntAlgHom s = a := hs
    rw [this, hf] at e1
    exact e1.symm
  rw [h0] at e2
  exact e2.trans (map_zero φ.toIntAlgHom)

theorem aeval_cyclotomic {S : Type} [CommRing S] (n : ℕ) (x : S) :
    Polynomial.aeval x (Polynomial.cyclotomic n ℤ) = (Polynomial.cyclotomic n S).eval x := by
  rw [← Polynomial.map_cyclotomic n (algebraMap ℤ S), Polynomial.eval_map_algebraMap]

theorem value_cp (hg : IsCptGen ξ) {F : Type} [Field F] [CharZero F] {z : Spec (CommRingCat.of F) ⟶ X} {p : ℕ}
    (hp : p.Prime) {κ : Ω} {r : F} (hκ : HT.IsCp p κ) (hv : ValAt ξ z κ r) :
    (p = 2 → r = 4) ∧ (p ≠ 2 → IsPrimitiveRoot (r + 1) p) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [HT.IsCp, if_pos h] at hκ
    have h3 := value_aeval hg hv (Polynomial.X - Polynomial.C 4) (by
      simp only [map_sub, Polynomial.aeval_X, hκ, map_ofNat, sub_self])
    simp only [map_sub, Polynomial.aeval_X, map_ofNat] at h3
    exact sub_eq_zero.1 h3
  · rw [HT.IsCp, if_neg h] at hκ
    obtain ⟨ζ, hζ, rfl⟩ := hκ
    have hp0 : NeZero (p : F) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
    have h3 := value_aeval hg hv ((Polynomial.cyclotomic p ℤ).comp (Polynomial.X + 1)) (by
      rw [Polynomial.aeval_comp]
      simp only [map_add, Polynomial.aeval_X, map_one, sub_add_cancel]
      rw [aeval_cyclotomic]
      exact hζ.isRoot_cyclotomic hp.pos)
    rw [Polynomial.aeval_comp] at h3
    simp only [map_add, Polynomial.aeval_X, map_one] at h3
    rw [aeval_cyclotomic] at h3
    exact Polynomial.isRoot_cyclotomic_iff.1 h3

variable {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
  (z : Spec (CommRingCat.of R) ⟶ X) {C : Type} [Field C] [Algebra R C] {EC : Type} [AddCommGroup EC] [Module C EC]
  (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC)

theorem val_exists (h : genPt ξ ⤳ centre z)
    (h' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) {e : Li}
    (he : e ∈ M.lat ⟨centre z, h⟩) :
    ∃ x, M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt x) := by
  obtain ⟨u, hu⟩ := (M.exists_valAt_iff z e).2 ⟨h, he⟩
  have ht := hu.isTanAt
  obtain ⟨_, v, hv, hu⟩ := hu
  have h1 := LieFib.valAt_base M z h h' v hv (LieCarrier.epsHom (algebraMap R C) z _ rfl ≫ u) u rfl hu
  obtain ⟨x, hx⟩ := MC.onto _ h1.isTanAt
  exact ⟨x, hx ▸ h1⟩

end Pt

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  (𝔐 : HodgeCpt Y S y) {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ 𝔐.X)

omit [∀ k, Fintype (J k)] in
theorem emb_value (s : CMType H ⊕ CMType H) (a : 𝓞 E) : ∃ r, ValAt 𝔐.ξ z (𝔐.emb s a) r := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* R, spMap ρ = z ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hint : IsIntegral ℤ (labelEmb c s a) :=
    (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
  have hm : algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = labelEmb c s a :=
    IsIntegralClosure.algebraMap_mk' _ _ hint
  have h := LabPt.valAt_of_const 𝔐.ξ (𝔐.f ≫ Y.s) 𝔐.cst_over z ρ hρ.symm (𝔐.all _)
    (IsIntegralClosure.mk' (𝓞 c.F) _ hint)
  have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb s a := by
    show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
    rw [hm]
  rw [he] at h
  exact ⟨_, h⟩

variable {C : Type} [Field C] [CharZero C] [Algebra R C] {EC : Type} [AddCommGroup EC] [Module C EC] [Module R EC]
  [IsScalarTower R C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC)
  (ρC : 𝓞 E →+* Module.End C EC) (hact : MC.IsActOf 𝔐.t.act.act ρC)

include hact in
omit [∀ k, Fintype (J k)] [CharZero C] [Module R EC] [IsScalarTower R C EC] in
theorem val_mem_eig {s : CMType H ⊕ CMType H} {σ : 𝓞 E →+* R} (hσ : ∀ a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ a))
    {e : 𝔐.Li} {x : EC} (he : e ∈ 𝔐.Vgen s)
    (hx : 𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt x)) :
    x ∈ eigSp ρC ((algebraMap R C).comp σ) := by
  refine mem_eigSp.2 fun a => ?_
  haveI := 𝔐.t.act.hom a
  have h1 := PositivityTheory.HtPt.Gh.valAt_act 𝔐.M MC _ _ _ (𝔐.act a) (hact a) hx
  have h2 := PtHt.FinFrame.val_smul (LieTangent.valAt_base 𝔐.tie.gen (algebraMap R C) (hσ a)) hx
  rw [mem_eigSp.1 he a] at h1
  exact MC.inj (h1.unique 𝔐.tie.gen h2)

include hact in

theorem off_S (σ : CMType H ⊕ CMType H → (𝓞 E →+* R)) (hσ : ∀ s a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ s a))
    (hinj : Function.Injective fun s => (algebraMap R C).comp (σ s)) (hS : ∀ p ∈ S, IsUnit (p : R))
    (hd : IsUnit (((discr E).natAbs : ℕ) : R)) (s : CMType H ⊕ CMType H) :
    𝔐.M.fibAt (𝔐.V s) z MC =
      𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap R C).comp (σ s))).restrictScalars R := by
  classical
  have hξ := 𝔐.tie.gen
  have h : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have h' : genPt 𝔐.ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) := 𝔐.all _
  have hV : 𝔐.V s ⟨centre z, h⟩ = 𝔐.dR s ⟨centre z, h⟩ :=
    Lat.patch_of_not _ _ _ fun p hp hf => hf ((PositivityTheory.HtPt.Gh.unitAt_centre_iff hξ z h p).2 (hS p hp))
  have hfib : 𝔐.M.fibAt (𝔐.V s) z MC = 𝔐.M.fibAt (𝔐.dR s) z MC := by
    unfold LieModel.fibAt
    congr 1
    ext x
    exact ⟨fun ⟨h1, e, h2, h3⟩ => ⟨h1, e, hV ▸ h2, h3⟩, fun ⟨h1, e, h2, h3⟩ => ⟨h1, e, hV.symm ▸ h2, h3⟩⟩
  have hle : ∀ t, 𝔐.M.fibAt (𝔐.dR t) z MC ≤ (eigSp ρC ((algebraMap R C).comp (σ t))).restrictScalars R := fun t =>
    Submodule.span_le.2 fun x ⟨_, e, h2, h3⟩ => val_mem_eig 𝔐 z MC ρC hact (hσ t) h2.2 h3
  rw [hfib]
  refine le_antisymm (le_inf (Submodule.span_mono fun x ⟨h1, e, h2, h3⟩ => ⟨h1, e, h2.1, h3⟩) (hle s)) ?_
  rintro x ⟨hx1, hx2⟩
  refine mem_of_indep _ (eigSp_indep ρC _ hinj) _ hle s ?_ hx2
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨hli, hcard⟩ := GlobalTheory.T.label_embedding_injective E H l c
  have hσ' : Function.Injective 𝔐.emb := fun s s' h =>
    hli (RingHom.ext fun a => 𝔐.cst.injective (RingHom.congr_fun h a))
  have hlat := (GlobalTheory.T.lie_omega_lattice_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.t.G 𝔐.Li 𝔐.M hξ 𝔐.t.semi.smooth).1
  obtain ⟨-, hsup⟩ := GlobalTheory.T.lattice_eigen_vector_bundle 𝔐.X Ω 𝔐.ξ 𝔐.Li E 𝔐.ρ 𝔐.M.lat {⟨centre z, h⟩} _ (CMType H ⊕ CMType H) 𝔐.emb hξ hσ'
    (by rw [← hcard, Nat.card_eq_fintype_card])
    (fun p _ => by
      obtain ⟨U, hU, b, hb, H⟩ := hlat p trivial
      exact ⟨U, hU, b, hb, fun q _ hq => H q trivial hq⟩)
    (fun p _ a => LieStable.lat_stable _ _ _ _ _ 𝔐.M _ 𝔐.t.act 𝔐.ρ 𝔐.act p a)
    (by
      rintro p rfl s a
      obtain ⟨_, t, ht, -⟩ := hσ s a
      exact ⟨t, ht⟩)
    (by
      rintro p rfl
      have h := (PositivityTheory.HtPt.Gh.unitAt_centre_iff hξ z h _).2 hd
      rcases Int.natAbs_eq (NumberField.discr E) with e | e
      · rw [e]; simpa using h
      · rw [e]
        refine ⟨by simpa using h.1, by simpa using h.2.1, ?_⟩
        simpa using h.2.2)
  have hs1 := hsup _ rfl
  refine (Submodule.span_le.2 ?_ : 𝔐.M.fibAt 𝔐.M.lat z MC ≤ _) hx1
  rintro w ⟨_, e, he, hw⟩
  have key : ∀ e ∈ ⨆ s, (𝔐.M.lat.inter (eigSp 𝔐.ρ (𝔐.emb s))) ⟨centre z, h⟩, ∃ x ∈ ⨆ t, 𝔐.M.fibAt (𝔐.dR t) z MC,
      𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt x) := by
    intro e he
    induction he using Submodule.iSup_induction' with
    | mem t e he =>
      obtain ⟨x, hx⟩ := val_exists 𝔐.M z MC h h' he.1
      exact ⟨x, Submodule.mem_iSup_of_mem t (Submodule.subset_span ⟨h, e, he, hx⟩), hx⟩
    | zero => exact ⟨0, zero_mem _, by rw [MC.pt_zero]; exact 𝔐.M.valAt_zero h'⟩
    | add a b _ _ ha hb =>
      obtain ⟨x, hx, ha⟩ := ha
      obtain ⟨x', hx', hb⟩ := hb
      exact ⟨x + x', add_mem hx hx', PtHt.FinFrame.val_add ha hb⟩
  obtain ⟨x', h1, h2⟩ := key e (hs1 ▸ he)
  rwa [MC.inj (hw.unique hξ h2)]

include hact in

theorem on_S {p : ℕ} (hpS : p ∈ S) (κ : Ω) (hfree : HT.HTFree 𝔐 p) (hsand : HT.Sandwich 𝔐 p κ)
    (v : Valuation C NNReal) (hv : v.Integers R) (hvp : v (p : C) < 1) (s : CMType H ⊕ CMType H)
    (σ : 𝓞 E →+* R) (hσ : ∀ a, ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) (κz : R) (hκ : ValAt 𝔐.ξ z κ κz) :
    𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R ≤ 𝔐.M.fibAt (𝔐.V s) z MC ∧
    ∀ w ∈ 𝔐.M.fibAt (𝔐.V s) z MC, ∀ d ∈ differentIdeal ℤ (𝓞 E), κz • σ d • w ∈
      𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (eigSp ρC ((algebraMap R C).comp σ)).restrictScalars R := by
  have hξ := 𝔐.tie.gen
  have hp : p.Prime := 𝔐.S_prime p hpS
  haveI : Fact p.Prime := ⟨hp⟩
  have h : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.sandwich_point_over_field_ext E H D l Xo c _ _ Y S Ω K J y 𝔐 p hpS κ hfree hsand C v R hv hvp z EC MC ρC s σ κz
    hact hσ hκ
  have hpu : ¬ IsUnit (p : R) := fun hu => by
    have := hv.one_of_isUnit hu
    rw [map_natCast] at this
    exact hvp.ne this
  have hq : InFibre 𝔐.ξ p ⟨centre z, h⟩ := fun hu => hpu ((PositivityTheory.HtPt.Gh.unitAt_centre_iff hξ z h p).1 hu)
  have hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' ⟨centre z, h⟩ → p' = p := by
    intro p' hp' hf
    by_contra hne
    have hc : IsCoprime (p' : R) (p : R) :=
      Nat.Coprime.cast ((Nat.coprime_primes (𝔐.S_prime p' hp') hp).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h1 | h1
    · exact hf ((PositivityTheory.HtPt.Gh.unitAt_centre_iff hξ z h p').2 (isUnit_of_mul_isUnit_right h1))
    · exact hpu (isUnit_of_mul_isUnit_right h1)
  have hV : 𝔐.V s ⟨centre z, h⟩ = 𝔐.HT p s ⟨centre z, h⟩ := Lat.patch_of_unique _ _ _ hpS hq hu
  have hreg : ∀ a, 𝔐.emb s a ∈ regAt 𝔐.ξ ⟨centre z, h⟩ := fun a => by
    obtain ⟨_, t, ht, -⟩ := hσ a
    exact ⟨t, ht⟩
  have hA : ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) ⟨centre z, h⟩, e ∈ 𝔐.V s ⟨centre z, h⟩ := by
    intro e he
    rw [hV]
    cases s with
    | inr τ => exact he
    | inl τ =>
      exact Submodule.subset_span ⟨𝔐.M.mem_eigSp_of_mem_htDual _ _ _ _ he, fun d _ =>
        Submodule.smul_mem _ (⟨_, hreg d⟩ : regAt 𝔐.ξ ⟨centre z, h⟩) he⟩
  have hB : ∀ d ∈ differentIdeal ℤ (𝓞 E), ∀ e ∈ 𝔐.V s ⟨centre z, h⟩,
      𝔐.emb s d • e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) ⟨centre z, h⟩ := by
    intro d hd e he
    rw [hV] at he
    cases s with
    | inr τ => exact Submodule.smul_mem _ (⟨_, hreg d⟩ : regAt 𝔐.ξ ⟨centre z, h⟩) he
    | inl τ =>
      induction he using Submodule.span_induction with
      | mem x hx => exact hx.2 d hd
      | zero => rw [smul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
      | smul a x _ hx =>
        have e1 : 𝔐.emb (.inl τ) d • a • x = a • 𝔐.emb (.inl τ) d • x := smul_comm (𝔐.emb (.inl τ) d) (a : Ω) x
        rw [e1]
        exact Submodule.smul_mem _ a hx
  refine ⟨h1.trans (Submodule.span_mono fun x ⟨h1, e, h2, h3⟩ => ⟨h1, e, hA e h2, h3⟩), fun w hw d hd => h2 _ ?_⟩
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨_, e, h2, h3⟩ := hx
    refine Submodule.subset_span ⟨h, _, hB d hd e h2, ?_⟩
    have := PtHt.FinFrame.val_smul (LieTangent.valAt_base hξ (algebraMap R C) (hσ d)) h3
    rwa [algebraMap_smul] at this
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

end Model

end LevelTowerAlt.LocalPrimeBound
