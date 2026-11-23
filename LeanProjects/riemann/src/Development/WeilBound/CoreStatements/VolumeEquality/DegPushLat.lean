import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparison
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstantsCompatibleGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstantsGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDominantHodgeStatement

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat.CptStalk

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {Ω₀ : Type} [Field Ω₀] {ξ₀ : Sp Ω₀ ⟶ Y.X} {Li₀ : Type}
  [AddCommGroup Li₀] [Module Ω₀ Li₀] (M₀ : LieModel Y.t.G ξ₀ Li₀) (ρ₀ : 𝓞 E →+* Module.End Ω₀ Li₀) (cst₀ : c.F →+* Ω₀)
  (b : ∀ s, Fin (labelRk D s) → Li₀)

def coordSet (s : CMType H ⊕ CMType H) (y₀ : Y.X) : Set (Fin (labelRk D s) → Ω₀) :=
  {a | ∃ h : genPt ξ₀ ⤳ y₀, ∑ m, a m • b s m ∈ M₀.eigLat ρ₀ (cst₀.comp (labelEmb c s)) ⟨y₀, h⟩}

variable {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

omit [∀ k, Fintype (J k)] in
theorem cst_eq (𝔐 : HodgeCpt Y S y) (ψ : Ω₀ →+* Ω) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ ξ₀ 𝔐.f ψ)
    (hs : ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F))) : ψ.comp cst₀ = 𝔐.cst := by
  have h1 := 𝔐.cst_over
  rw [← Category.assoc, hd, Category.assoc, hs] at h1
  have h2 : 𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) = (ψ.comp cst₀).comp (algebraMap (𝓞 c.F) c.F) := by
    have h3 := h1.symm
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h3
    have h4 := Spec.map_injective h3
    have h5 := congrArg CommRingCat.Hom.hom h4
    simpa using h5
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  exact (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2).symm

theorem lat_core (𝔐 : HodgeCpt Y S y) (ψ : Ω₀ →+* Ω) (j : Li₀ →+ 𝔐.Li) (hg : IsCptGen ξ₀)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ ξ₀ 𝔐.f ψ) (hs : ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)))
    (hact : M₀.IsActOf Y.t.act.act ρ₀)
    (hj : ∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap ψ) ≫ (M₀.pt e).left)
    (hb : ∀ s, LinearIndependent Ω₀ (b s) ∧ Submodule.span Ω₀ (Set.range (b s)) = eigSp ρ₀ (cst₀.comp (labelEmb c s))) :
    (∀ s, LinearIndependent Ω (fun m => j (b s m)) ∧ Submodule.span Ω (Set.range fun m => j (b s m)) = 𝔐.Vgen s) ∧
      ∀ q : Cpt 𝔐.ξ, (∀ p : ℕ, p.Prime → ¬ InFibre 𝔐.ξ p q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q)
        {w | ∃ a ∈ coordSet M₀ ρ₀ cst₀ b s (𝔐.f q.1), w = ∑ m, ψ (a m) • j (b s m)} := by
  have hcst : ψ.comp cst₀ = 𝔐.cst := cst_eq (cst₀ := cst₀) 𝔐 ψ hd hs
  haveI : CharZero Ω₀ := (RingHom.charZero_iff cst₀.injective).mp inferInstance
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).mp inferInstance
  have hsemi : ∀ (a : Ω₀) (e : Li₀), j (a • e) = ψ a • j e := LiePull.semilin 𝔐.m.cart hj
  refine ⟨fun s => ?_, fun q hq s => ?_⟩
  · have hsm : Smooth Y.t.G.hom := Y.t.semi.smooth
    have hsm' : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
    obtain ⟨hext, htop, -⟩ := LiePull.main _ _ _ _ ξ₀ 𝔐.ξ 𝔐.f ψ Y.t.G 𝔐.t.G 𝔐.m.φ _ _ M₀ 𝔐.M j hg
      𝔐.tie.gen hd 𝔐.m.cart hsm hj
    have hli : LinearIndependent Ω (fun m => j (b s m)) := hext.2 _ (b s) (hb s).1
    refine ⟨hli, ?_⟩
    have hle : Submodule.span Ω (Set.range fun m => j (b s m)) ≤ 𝔐.Vgen s := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      have hm : b s m ∈ eigSp ρ₀ (cst₀.comp (labelEmb c s)) := (hb s).2 ▸ Submodule.subset_span ⟨m, rfl⟩
      have h1 := map_mem_eigSp 𝔐.m hact 𝔐.act hj hsemi _ hm
      rw [← RingHom.comp_assoc, hcst] at h1
      exact h1
    haveI : Module.Finite Ω₀ Li₀ := (LieProj.lie_finite_projective_baseChange _ _ _ _ _ M₀).1
    haveI : Module.Finite Ω 𝔐.Li := (LieProj.lie_finite_projective_baseChange _ _ _ _ _ 𝔐.M).1
    letI : Algebra Ω₀ Ω := ψ.toAlgebra
    have hsemi' : ∀ (a : Ω₀) (e : Li₀), j (a • e) = (algebraMap Ω₀ Ω) a • j e := hsemi
    let B := Module.finBasis Ω₀ Li₀
    have hBspan : Submodule.span Ω (Set.range fun k => j (B k)) = ⊤ := by
      rw [eq_top_iff, ← htop, Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      rw [← B.sum_repr e, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [hsemi]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have hfr := EigRank.finrank_eigSp_baseChange Ω₀ Ω (𝓞 E) Li₀ 𝔐.Li _ B j hsemi'
      (hext.2 _ B B.linearIndependent) hBspan ρ₀ 𝔐.ρ
      (fun a e => (map_act 𝔐.m hact 𝔐.act hj a e).symm) (cst₀.comp (labelEmb c s))
    have h0 : Module.finrank Ω₀ (eigSp ρ₀ (cst₀.comp (labelEmb c s))) = labelRk D s := by
      rw [← (hb s).2, finrank_span_eq_card (hb s).1, Fintype.card_fin]
    have h2 : (algebraMap Ω₀ Ω).comp (cst₀.comp (labelEmb c s)) = 𝔐.cst.comp (labelEmb c s) := by
      rw [RingHom.algebraMap_toAlgebra, ← RingHom.comp_assoc, hcst]
    rw [h2, h0] at hfr
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_span_eq_card hli, Fintype.card_fin, hfr]
    rfl
  · have hnot : ¬ ∃ p ∈ S, InFibre 𝔐.ξ p q := fun ⟨p, hp, hf⟩ => hq p (𝔐.S_prime p hp) hf
    have hV : 𝔐.V s q = 𝔐.M.eigLat 𝔐.ρ ((ψ.comp cst₀).comp (labelEmb c s)) q := by
      simp only [HodgeCpt.V, Lat.patch, if_neg hnot, HodgeCpt.dR, HodgeCpt.emb, hcst]
    rw [hV, eigLat_eq_pull c 𝔐.m cst₀ hg 𝔐.tie.gen hd hact 𝔐.act (isIntegrallyClosed_regAt Y.normal hg)
      (isIntegrallyClosed_regAt 𝔐.normal 𝔐.tie.gen) hj s q hq]
    simp only [Lat.pull]
    congr 1
    ext w
    simp only [Set.mem_setOf_eq, coordSet]
    constructor
    · rintro ⟨h, e, he, rfl⟩
      have he' : e ∈ eigSp ρ₀ (cst₀.comp (labelEmb c s)) := by
        simp only [LieModel.eigLat, Lat.inter] at he
        exact (Submodule.mem_inf.1 he).2
      rw [← (hb s).2, Submodule.mem_span_range_iff_exists_fun] at he'
      obtain ⟨a, rfl⟩ := he'
      refine ⟨a, ⟨h, he⟩, ?_⟩
      simp only [map_sum, hsemi]
    · rintro ⟨a, ⟨h, ha⟩, rfl⟩
      refine ⟨h, _, ha, ?_⟩
      simp only [map_sum, hsemi]

end

private theorem coordLat_lemma {S : Scheme} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V)
    {O : Type} [CommRing O] (act : OAct O G) : ∃ ρ : O →+* Module.End R V, M.IsActOf act.act ρ := by
  have htan : ∀ (a : O) (e : V), IsTanAt G x (M.pt e ≫ act.act a) := by
    intro a e
    haveI := act.hom a
    have h1 := M.tan e
    simp only [IsTanAt] at h1 ⊢
    rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left, MonObj.one_comp]
  choose F hF using fun a e => M.onto _ (htan a e)
  have hadd : ∀ a e e', F a (e + e') = F a e + F a e' := by
    intro a e e'
    haveI := act.hom a
    apply M.inj
    rw [hF, M.add, M.add, hF, hF, MonObj.mul_comp]
  have hsmul : ∀ a (r : R) e, F a (r • e) = r • F a e := by
    intro a r e
    apply M.inj
    apply Over.OverMorphism.ext
    simp only [hF, Over.comp_left, M.smul, Category.assoc]
  let L : O → Module.End R V := fun a =>
    { toFun := F a, map_add' := hadd a, map_smul' := hsmul a }
  have hL : ∀ a e, M.pt (L a e) = M.pt e ≫ act.act a := hF
  have hone : L 1 = 1 := by
    ext e
    apply M.inj
    rw [hL, act.one, Category.comp_id]
    rfl
  have hmul : ∀ a b, L (a * b) = L a * L b := by
    intro a b
    ext e
    apply M.inj
    rw [Module.End.mul_apply, hL, hL, hL, show a * b = b * a from mul_comm a b, act.mul, Category.assoc]
  have haddL : ∀ a b, L (a + b) = L a + L b := by
    intro a b
    ext e
    apply M.inj
    rw [LinearMap.add_apply, M.add, hL, hL, hL, act.add, MonObj.comp_mul]
  have hzero : L 0 = 0 := by
    have h := haddL 0 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  exact ⟨{ toFun := L, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := haddL },
    fun a e => hL a e⟩

private theorem coordLat_lemma_2 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme}
    {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f) {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    {ξ₀ : Sp Ω₀ ⟶ X} {ξ : Sp Ω ⟶ X'} {ψ : Ω₀ →+* Ω} {V V' : Type} [AddCommGroup V] [Module Ω₀ V]
    [AddCommGroup V'] [Module Ω V'] (M₀ : LieModel t.G ξ₀ V) (M : LieModel t'.G ξ V')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f ψ) :
    ∃ j : V →+ V', ∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap ψ) ≫ (M₀.pt e).left := by
  obtain ⟨Mp, hMp⟩ := (LiePull.lieModel_pullback _ _ _ _ f m.φ m.cart Ω ξ V').2 M
  have key : ∀ x₂ : Sp Ω ⟶ X, ξ ≫ f = x₂ →
      ∃ Mq : LieModel t.G x₂ V', ∀ e, (Mq.pt e).left = (Mp.pt e).left := by
    rintro x₂ rfl
    exact ⟨Mp, fun _ => rfl⟩
  obtain ⟨Mq, hMq⟩ := key (spMap ψ ≫ ξ₀) hd
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts X t.G Ω₀ Ω ψ ξ₀ V V' M₀ Mq
  refine ⟨j.toAddMonoidHom, fun e => ?_⟩
  have h1 := hj e
  simp only [LieModel.Lifts, Category.comp_id] at h1
  change (M.pt (j e)).left ≫ m.φ = _
  rw [hMp, ← hMq, h1]

theorem coordLat : CoordLat := by
  intro E _ _ _ H D l Xo c Y S' Ω' _ K' _ J' _ y' 𝔐' Fl b hb
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  haveI : CharZero 𝔐'.Ω₀ := (RingHom.charZero_iff 𝔐'.fn.injective).mpr
    ((RingHom.charZero_iff 𝔐'.cst.injective).mp inferInstance)
  obtain ⟨ρ₀, hact⟩ := coordLat_lemma Fl.M₀ Y.t.act
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := IsFractionRing.injective _ _
  obtain ⟨r, hr⟩ : ∃ r : 𝓞 c.F →+* 𝔐'.Ω₀, 𝔐'.ξ₀ ≫ Y.s = spMap r :=
    ⟨(Spec.preimage (𝔐'.ξ₀ ≫ Y.s)).hom, by simp [spMap, Spec.map_preimage]⟩
  have hfr : 𝔐'.fn.comp r = 𝔐'.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have h1 := 𝔐'.cst_over
    rw [← Category.assoc, 𝔐'.fn_over, Category.assoc, hr] at h1
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    simpa using h2
  have hrinj : Function.Injective r := by
    have h1 : Function.Injective (𝔐'.fn.comp r) := by
      rw [hfr]
      exact 𝔐'.cst.injective.comp hβ
    exact Function.Injective.of_comp h1
  let cst₀ : c.F →+* 𝔐'.Ω₀ := IsFractionRing.lift hrinj
  have hcst₀ : cst₀.comp (algebraMap (𝓞 c.F) c.F) = r :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap hrinj x
  have hs : 𝔐'.ξ₀ ≫ Y.s = spMap (cst₀.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [hcst₀]
    exact hr
  have hcst' : 𝔐'.fn.comp cst₀ = 𝔐'.cst := cst_eq (cst₀ := cst₀) 𝔐' 𝔐'.fn 𝔐'.fn_over hs
  have hsemi : ∀ (a : 𝔐'.Ω₀) (e : Fl.Li₀), Fl.j (a • e) = 𝔐'.fn a • Fl.j e :=
    LiePull.semilin 𝔐'.m.cart Fl.j_pt
  obtain ⟨hext, -, -⟩ := LiePull.main _ _ _ _ 𝔐'.ξ₀ 𝔐'.ξ 𝔐'.f 𝔐'.fn Y.t.G 𝔐'.t.G 𝔐'.m.φ _ _ Fl.M₀ 𝔐'.M
    Fl.j 𝔐'.gen₀ 𝔐'.tie.gen 𝔐'.fn_over 𝔐'.m.cart Y.t.semi.smooth Fl.j_pt
  have hjinj : ∀ x, Fl.j x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have h1 := hext.2 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)
    exact (linearIndependent_unique_iff.1 h1) hx
  have hV0 : ∀ s, Fl.V₀ s = eigSp ρ₀ (cst₀.comp (labelEmb c s)) := by
    intro s
    ext e
    rw [Fl.V₀_mem]
    simp only [HodgeCpt.Vgen, HodgeCpt.emb, eigSp, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, RingHom.coe_comp, Function.comp_apply]
    refine forall_congr' fun a => ?_
    have h1 : Fl.j (ρ₀ a e - cst₀ (labelEmb c s a) • e) =
        𝔐'.ρ a (Fl.j e) - 𝔐'.cst (labelEmb c s a) • Fl.j e := by
      rw [map_sub, hsemi, map_act 𝔐'.m hact 𝔐'.act Fl.j_pt, ← RingHom.comp_apply 𝔐'.fn cst₀, hcst']
    constructor
    · intro h
      exact hjinj _ (h1.trans h)
    · intro h
      rw [← h1, h, map_zero]
  have hb₀ : ∀ s, LinearIndependent 𝔐'.Ω₀ (b s) ∧
      Submodule.span 𝔐'.Ω₀ (Set.range (b s)) = eigSp ρ₀ (cst₀.comp (labelEmb c s)) :=
    fun s => ⟨(hb s).1, (hb s).2.trans (hV0 s)⟩
  have hmain := lat_core (M₀ := Fl.M₀) (ρ₀ := ρ₀) (cst₀ := cst₀) (b := b) 𝔐' 𝔐'.fn Fl.j 𝔐'.gen₀
    𝔐'.fn_over hs hact Fl.j_pt hb₀
  refine ⟨fun s y₀ => coordSet Fl.M₀ ρ₀ cst₀ b s y₀, hmain.2, hmain.1, ?_⟩
  intro S Ω _ K _ J _ y 𝔐 ψ hd
  obtain ⟨j, hj⟩ := coordLat_lemma_2 𝔐.m Fl.M₀ 𝔐.M hd
  exact ⟨fun s m => j (b s m), lat_core (M₀ := Fl.M₀) (ρ₀ := ρ₀) (cst₀ := cst₀) (b := b) 𝔐 ψ j 𝔐'.gen₀
    hd hs hact hj hb₀⟩

end SheetDecomposition
