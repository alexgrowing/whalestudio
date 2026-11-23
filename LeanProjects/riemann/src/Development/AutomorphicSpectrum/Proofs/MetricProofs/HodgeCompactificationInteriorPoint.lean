import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarised
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptAwayFromPrimes

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
open scoped ComplexOrder
open Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramFrame

theorem generates_of_mono {O F : Type} [CommRing O] [Field F] (β : O →+* F) (h : Mono (spMap β)) (x : F) :
    ∃ p q : O, β q ≠ 0 ∧ x * β q = β p := by
  have h₁ : Mono (CommRingCat.ofHom β).op := Scheme.Spec.mono_of_mono_map h
  have h₂ : Epi (CommRingCat.ofHom β) := inferInstanceAs (Epi (CommRingCat.ofHom β).op.unop)
  let K := Subfield.closure (Set.range β)
  have h₃ : Epi (CommRingCat.ofHom (algebraMap K F)) :=
    epi_of_epi_fac (f := CommRingCat.ofHom (β.codRestrict K fun a => Subfield.subset_closure ⟨a, rfl⟩))
      (h := CommRingCat.ofHom β) rfl
  have h₄ := (Algebra.isEpi_iff_forall_one_tmul_eq K F).1 (CommRingCat.epi_iff_epi.1 h₃) x
  have hx : x ∈ K := by
    by_contra hx
    have hx' : x ∉ Submodule.span K {(1 : F)} := fun hm => by
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hm
      exact hx (by rw [← ha, Algebra.smul_def, _root_.mul_one]; exact a.2)
    obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx' inferInstance
    have f₁ : f 1 = 0 := (Submodule.mem_bot K).1
      (hf' ▸ Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _))
    have := congrArg (fun z => TensorProduct.rid K F (LinearMap.lTensor F f z)) h₄
    simp [f₁, hf] at this
  obtain ⟨y, hy, z, hz, e⟩ := Subfield.mem_closure_iff.1 hx
  have r : Subring.closure (Set.range β) = β.range := Subring.closure_eq β.range
  rw [r] at hy hz
  obtain ⟨p, rfl⟩ := hy
  obtain ⟨q, rfl⟩ := hz
  by_cases hq : β q = 0
  · exact ⟨0, 1, by simp, by simp [← e, hq]⟩
  · exact ⟨p, q, hq, by rw [← e, div_mul_cancel₀ _ hq]⟩

theorem exists_comp_eq_of_mono {O F : Type} [CommRing O] [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (β : O →+* F)
    (hm : Mono (spMap β)) (g : O →+* ℂ) (hk : ∀ a, β a = 0 → g a = 0) : ∃ g' : F →+* ℂ, g'.comp β = g := by
  have hgen := generates_of_mono β hm
  let R := O ⧸ RingHom.ker β
  let i : R →+* F := RingHom.kerLift β
  have hi : Function.Injective i := RingHom.kerLift_injective β
  let gb : R →+* ℂ := Ideal.Quotient.lift (RingHom.ker β) g fun a ha => hk a ha
  haveI : IsDomain R := hi.isDomain i
  letI : Algebra R F := i.toAlgebra
  have hinj : Function.Injective gb := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hZ : IsAlgebraic ℤ (algebraMap R F x) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have hxa : IsAlgebraic ℤ x := (isAlgebraic_algebraMap_iff hi).1 hZ
    refine Ideal.comap_ne_bot_of_algebraic_mem hx0 hx hxa ?_
    have e : Ideal.comap (algebraMap ℤ R) (RingHom.ker gb) = RingHom.ker (gb.comp (algebraMap ℤ R)) :=
      RingHom.comap_ker _ _
    rw [e, (RingHom.injective_iff_ker_eq_bot _).1]
    have e2 : gb.comp (algebraMap ℤ R) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [e2]
    exact Int.cast_injective
  haveI : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).2 hi
  haveI : IsFractionRing R F := IsFractionRing.of_field R F fun x => by
    obtain ⟨p, q, hq, hx⟩ := hgen x
    refine ⟨Ideal.Quotient.mk _ p, Ideal.Quotient.mk _ q, ?_⟩
    show x = β p / β q
    rw [eq_div_iff hq, hx]
  refine ⟨IsFractionRing.lift hinj, ?_⟩
  ext a
  have : (IsFractionRing.lift hinj : F →+* ℂ) (algebraMap R F (Ideal.Quotient.mk _ a)) = gb (Ideal.Quotient.mk _ a) :=
    IsFractionRing.lift_algebraMap hinj _
  exact this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem exists_spMap_of_point (𝔐 : HodgeCpt Y S y) (hm : Mono (spMap β)) (z : Sp ℂ ⟶ 𝔐.X) :
    ∃ g' : c.F →+* ℂ, (z ≫ 𝔐.f) ≫ Y.s = spMap g' ≫ spMap β := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  let g : O →+* ℂ := (Spec.preimage ((z ≫ 𝔐.f) ≫ Y.s)).hom
  have hs : (z ≫ 𝔐.f) ≫ Y.s = spMap g := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage ((z ≫ 𝔐.f) ≫ Y.s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hsp : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have h2 := hsp.map (𝔐.f ≫ Y.s).continuous
  have hk : ∀ a, β a = 0 → g a = 0 := by
    intro a ha
    have e1 : (𝔐.f ≫ Y.s) (genPt 𝔐.ξ) = spMap (𝔐.cst.comp β) (IsLocalRing.closedPoint Ω) :=
      (Scheme.Hom.comp_apply 𝔐.ξ (𝔐.f ≫ Y.s) _).symm.trans
        (congrArg (fun m : Sp Ω ⟶ Sp O => m (IsLocalRing.closedPoint Ω)) 𝔐.cst_over)
    have e2 : (𝔐.f ≫ Y.s) (centre z) = spMap g (IsLocalRing.closedPoint ℂ) :=
      (Scheme.Hom.comp_apply z (𝔐.f ≫ Y.s) _).symm.trans
        (congrArg (fun m : Sp ℂ ⟶ Sp O => m (IsLocalRing.closedPoint ℂ)) ((Category.assoc _ _ _).symm.trans hs))
    rw [e1, e2] at h2
    have hle : PrimeSpectrum.comap (𝔐.cst.comp β) (IsLocalRing.closedPoint Ω) ≤
        PrimeSpectrum.comap g (IsLocalRing.closedPoint ℂ) := (PrimeSpectrum.le_iff_specializes _ _).2 h2
    have hmem : a ∈ (PrimeSpectrum.comap (𝔐.cst.comp β) (IsLocalRing.closedPoint Ω)).asIdeal := by
      simp [ha]
    have h3 : g a ∈ IsLocalRing.maximalIdeal ℂ := hle hmem
    rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h3
  obtain ⟨g', hg'⟩ := exists_comp_eq_of_mono β hm g hk
  refine ⟨g', ?_⟩
  rw [hs, ← hg']
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem polarisedAt_of_interior_mono (𝔐 : HodgeCpt Y S y) (hm : Mono (spMap β)) (z : Sp ℂ ⟶ 𝔐.X) (hz : 𝔐.Interior z) :
    HodgeMetric.PolarisedAt 𝔐.t z := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hsub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have h₁ : (z ≫ 𝔐.f) p ∈ abLocus Y.t.G := by
    have := (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 (z p)).2 hz
    simpa using this
  obtain ⟨g', hg'⟩ := exists_spMap_of_point 𝔐 hm z
  let w : Sp ℂ ⟶ pullback Y.s (spMap β) := pullback.lift (z ≫ 𝔐.f) (spMap g') hg'
  have hw : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _
  have h₂ : w p ∈ Set.range Y.jQ := by
    rw [← Y.ab_gen]
    show (pullback.fst Y.s _) (w p) ∈ abLocus Y.t.G
    have : (pullback.fst Y.s (spMap β)) (w p) = (z ≫ 𝔐.f) p := by
      rw [← hw]; simp
    rw [this]; exact h₁
  have h₃ : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q p]
  haveI := Y.jQ_open
  let v : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w h₃
  have hv : v ≫ Y.jQ ≫ pullback.fst _ _ = z ≫ 𝔐.f := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hw]
  obtain ⟨t', ⟨m₁⟩⟩ := exists_sab z 𝔐.t
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ 𝔐.m m₁
  have cancel : ∀ (q : Sp ℂ ⟶ Y.X) (_ : q = v ≫ Y.jQ ≫ pullback.fst _ _) (_ : SABMap t' Y.t q),
      Nonempty (SABMap t' Y.oF.t v) := by
    intro q hq n; subst hq
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ hv.symm n
  obtain ⟨w₂, g₂, -⟩ := m₃.lin
  obtain ⟨am, -⟩ := amplePt _ _ v _ _ m₃.φ m₃.cart _ _ Y.oF.t.PP.isLB t'.PP.isLB ⟨w₂, g₂⟩ Y.oF.ample Y.oF.ktriv
  exact ⟨t', m₁, MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 Y.oF.proper, am⟩

theorem lattices_off_fibres (𝔐 : HodgeCpt Y S y) (q : Cpt 𝔐.ξ) (hq : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) :
    iSupIndep 𝔐.Vgen ∧ (∀ s, 𝔐.V s q = 𝔐.dR s q) ∧ 𝔐.M.lat q = ⨆ s, 𝔐.dR s q := by
  classical
  have hcst : Function.Injective 𝔐.cst := 𝔐.cst.injective
  haveI hchar : CharZero Ω := charZero_of_injective_ringHom hcst
  have hinj : Function.Injective 𝔐.emb := by
    intro s s' h
    refine HodgeBasic.labelEmb_injective c (RingHom.ext fun a => hcst ?_)
    exact congrArg (fun m : 𝓞 E →+* Ω => m a) h
  letI : Fintype (CMType H) := Fintype.ofFinite _
  have hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
    rw [Fintype.card_of_bijective (HodgeBasic.labelHom_bijective H), Embeddings.card]
  have hint := GlobalTheory.T.eigenspace_decomposition_internal Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hcard
  have htop := hint.submodule_iSup_eq_top
  have hreg : ∀ s a, 𝔐.emb s a ∈ regAt 𝔐.ξ q := fun s a =>
    HodgeBasic.mem_regAt_of_isIntegral 𝔐.tie.gen 𝔐.all 𝔐.normal q
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom)
  have hnat := HodgeChar0.unitAt_natCast (q := q) hq
  have hV : ∀ s, 𝔐.V s q = 𝔐.dR s q := fun s =>
    Lat.patch_of_not S _ _ fun p hp => hq p (𝔐.S_prime p hp)
  have hintg : ∀ (s : CMType H ⊕ CMType H) a, _root_.IsIntegral ℤ (𝔐.emb s a) := fun s a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb s).toIntAlgHom
  have hsep : ∀ s t, s ≠ t → ∃ a, 𝔐.emb s a ≠ 𝔐.emb t a ∧ (𝔐.emb s a - 𝔐.emb t a)⁻¹ ∈ regAt 𝔐.ξ q := by
    intro s t hst
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 (fun e => hst (hinj e))
    exact ⟨a, ha, HodgeChar0.inv_mem_regAt hnat (sub_mem (hreg s a) (hreg t a)) ((hintg s a).sub (hintg t a))⟩
  refine ⟨hint.submodule_iSupIndep, hV, le_antisymm (fun e he => ?_) (iSup_le fun s => inf_le_left)⟩
  have he' : e ∈ ⨆ s, 𝔐.Vgen s := by rw [show (⨆ s, 𝔐.Vgen s) = ⊤ from htop]; trivial
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 he'
  rw [Finsupp.sum_fintype _ _ fun _ => rfl] at he ⊢
  have h1 := HodgeChar0.mem_of_sum_mem (𝔐.M.lat q) 𝔐.ρ 𝔐.emb
    (fun a e he => HodgeChar0.lat_stable 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act q a he) hreg hsep Finset.univ f
    (fun s _ => hf s) he
  exact Submodule.sum_mem _ fun s _ =>
    Submodule.mem_iSup_of_mem s ⟨h1 s (Finset.mem_univ s), hf s⟩

theorem exists_gramAt_posDef_of_frame (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (hgen : genPt 𝔐.ξ ⤳ centre z)
    (hpol : HodgeMetric.PolarisedAt 𝔐.t z) (s : CMType H ⊕ CMType H) {N : ℕ} (b : Fin N → 𝔐.Li)
    (hfr : (𝔐.V s).IsFrameAt b ⟨centre z, hgen⟩) :
    ∃ Γ : Matrix (Fin N) (Fin N) ℂ, 𝔐.M.GramAt 𝔐.t.PP.L z b Γ ∧ Γ.PosDef := by
  haveI hchar : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  obtain ⟨hind, hV, hlat⟩ := lattices_off_fibres 𝔐 ⟨centre z, hgen⟩
    fun r hr => GramEx.not_inFibre_centre hgen hr
  have hmem : ∀ k, b k ∈ 𝔐.V s ⟨centre z, hgen⟩ := fun k => by
    rw [hfr.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hmemd : ∀ k, b k ∈ 𝔐.dR s ⟨centre z, hgen⟩ := fun k => hV s ▸ hmem k
  let bb : Fin N → ↥(𝔐.Vgen s ⊔ 𝔐.Vgen s) := fun k => ⟨b k, Submodule.mem_sup_left (hmemd k).2⟩
  have hfr' : (Lat.comap (fun p => 𝔐.V s p ⊔ 𝔐.V s p) (𝔐.Vgen s ⊔ 𝔐.Vgen s).subtype).IsFrameAt bb
      ⟨centre z, hgen⟩ := by
    refine ⟨LinearIndependent.of_comp (𝔐.Vgen s ⊔ 𝔐.Vgen s).subtype hfr.1, le_antisymm (fun x hx => ?_) ?_⟩
    · have hx' : (x : 𝔐.Li) ∈ 𝔐.V s ⟨centre z, hgen⟩ := by
        have h0 : (x : 𝔐.Li) ∈ 𝔐.V s ⟨centre z, hgen⟩ ⊔ 𝔐.V s ⟨centre z, hgen⟩ := hx
        rwa [sup_idem] at h0
      rw [hfr.2] at hx'
      obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx'
      have e : x = ∑ k, c' k • bb k := Subtype.ext (by
        rw [← hc', Submodule.coe_sum]
        rfl)
      rw [e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      exact Submodule.mem_sup_left (hmem k)
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨f, hHI, hh, hp⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z Vz MR hpol
  obtain ⟨π, hπ, hreg⟩ := GramEx.exists_dual_sum 𝔐 hind ⟨centre z, hgen⟩ hV hlat s s bb hfr'
  have hval : ∀ k, ∃ x : Vz, 𝔐.M.ValAt z (b k) (MR.pt x) := fun k => by
    obtain ⟨w, hw⟩ := (𝔐.M.exists_valAt_iff z _).2 ⟨hgen, (hmemd k).1⟩
    obtain ⟨x, rfl⟩ := MR.onto w hw.isTanAt
    exact ⟨x, hw⟩
  choose x hx using hval
  have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (x k) = if j = k then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := GlobalTheory.T.lattice_regular_at_local_point 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M ℂ z hgen Vz MR (π j) hξ (hreg j)
    refine ⟨g, fun k => hg _ _ _ (hx k) ?_⟩
    rw [show π j (b k) = if j = k then 1 else 0 from hπ j k]
    split_ifs
    · exact CxVal.one hgen
    · exact ⟨hgen, 0, map_zero _, map_zero _⟩
  choose g hg using hg
  exact ⟨Matrix.of fun p q => f (x p) (x q), ⟨fun k => MR.pt (x k), hx, fun p q => (hHI _ _ _).2 rfl⟩,
    GramEx.posDef_of_dual f hh hp x g hg⟩

theorem main : ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (Fl : A.Flag), Mono (spMap β) → ∀ (z : Sp ℂ ⟶ A.X), A.Interior z → ∀ s, ∃ (h : genPt A.ξ ⤳ centre z) (b : Fin (labelRk D s) → A.Li) (Γ : Matrix (Fin (labelRk D s)) (Fin (labelRk D s)) ℂ), (∀ k, flagStep Ω b k = flagStep Ω (Fl.b s) k) ∧ (A.V s).IsFrameAt b ⟨centre z, h⟩ ∧ A.M.GramAt A.t.PP.L z b Γ ∧ Γ.PosDef := by
  intro _ E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y A Fl hm z hz s
  have hgen : genPt A.ξ ⤳ centre z := A.all _
  obtain ⟨U, hU, b, hb, hfr⟩ := Fl.sub s ⟨centre z, hgen⟩ (Set.mem_univ _)
  have hfz := hfr ⟨centre z, hgen⟩ (Set.mem_univ _) hU
  obtain ⟨Γ, hΓ, hP⟩ := exists_gramAt_posDef_of_frame A z hgen (polarisedAt_of_interior_mono A hm z hz) s b hfz
  exact ⟨hgen, b, Γ, hb, hfz, hΓ, hP⟩

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramFrame
