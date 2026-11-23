import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsOfGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelCommonRefinementStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsReindexedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRankStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoherentLatticeClosureStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.EigBase

section Lin

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {Li : Type} [AddCommGroup Li]
  [Module Ω Li]

theorem exists_proj {I : Type} (V : I → Submodule Ω Li) (hV : iSupIndep V) (htop : ⨆ s, V s = ⊤) :
    ∃ π : I → (Li →ₗ[Ω] Li), (∀ s, ∀ v ∈ V s, π s v = v) ∧ (∀ s s', s ≠ s' → ∀ v ∈ V s', π s v = 0) ∧
      ∀ s, LinearMap.range (π s) = V s := by
  classical
  have hc : ∀ s, IsCompl (V s) (⨆ j, ⨆ _ : j ≠ s, V j) := fun s => by
    refine ⟨hV s, ?_⟩
    rw [codisjoint_iff, eq_top_iff, ← htop]
    refine iSup_le fun j => ?_
    by_cases h : j = s
    · subst h
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j h le_rfl)
  refine ⟨fun s => (V s).subtype ∘ₗ (V s).projectionOnto _ (hc s), fun s v hv => ?_, fun s s' h v hv => ?_,
    fun s => ?_⟩
  · simp [Submodule.projectionOnto_apply_left (hc s) ⟨v, hv⟩]
  · have h1 : v ∈ ⨆ j, ⨆ _ : j ≠ s, V j := le_iSup₂_of_le (f := fun j (_ : j ≠ s) => V j) s' (Ne.symm h) le_rfl hv
    simp [Submodule.projectionOnto_apply_of_mem_right (hc s) h1]
  · rw [LinearMap.range_comp, Submodule.range_projectionOnto, Submodule.map_top, Submodule.range_subtype]

theorem map_proj_eq {L : Lat ξ Li} {I : Type} {V : I → Submodule Ω Li} {π : I → (Li →ₗ[Ω] Li)}
    (h1 : ∀ s, ∀ v ∈ V s, π s v = v) (h2 : ∀ s s', s ≠ s' → ∀ v ∈ V s', π s v = 0) {p : Cpt ξ}
    (hL : L p = ⨆ s, L.inter (V s) p) (s : I) : L.map (π s) p = L.inter (V s) p := by
  apply le_antisymm
  · refine Submodule.map_le_iff_le_comap.2 (hL.le.trans (iSup_le fun s' v hv => ?_))
    show π s v ∈ L.inter (V s) p
    by_cases h : s = s'
    · subst h
      rw [h1 s v hv.2]
      exact hv
    · rw [h2 s s' h v hv.2]
      exact zero_mem _
  · intro v hv
    exact ⟨v, hv.1, h1 s v hv.2⟩

theorem span_map_eq_range {L : Lat ξ Li} {p : Cpt ξ} (hp : Submodule.span Ω (L p : Set Li) = ⊤) (π : Li →ₗ[Ω] Li) :
    Submodule.span Ω (L.map π p : Set Li) = LinearMap.range π := by
  have e : (L.map π p : Set Li) = π '' (L p : Set Li) := by
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, rfl⟩
  rw [e, Submodule.span_image, hp, Submodule.map_top]

theorem mem_pull_iff {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {g : X' ⟶ X} (L : Lat ξ Li) (q : Cpt ξ')
    (h : genPt ξ ⤳ g q.1) (hr : regAt ξ' q = regAt ξ ⟨g q.1, h⟩) (e : Li) :
    e ∈ L.pull ξ' g (AddMonoidHom.id Li) q ↔ e ∈ L ⟨g q.1, h⟩ := by
  constructor
  · intro he
    induction he using Submodule.span_induction with
    | mem e he =>
      obtain ⟨_, e', he', rfl⟩ := he
      exact he'
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      have hc : (c : Ω) ∈ regAt ξ ⟨g q.1, h⟩ := hr ▸ c.2
      exact (L ⟨g q.1, h⟩).smul_mem ⟨c, hc⟩ hx
  · intro he
    exact Submodule.subset_span ⟨h, e, he, rfl⟩

end Lin

section Ideal

variable {K K' : Type} [Fintype K] [Fintype K'] {J : K → Type} {J' : K' → Type} [∀ k, Fintype (J k)]
  [∀ k, Fintype (J' k)]

theorem mem_mcPts_rename (v : (Σ k, J k) → Σ k, J' k) (bd : Ideal (MRing J)) (w : (Σ k, J' k) → ℂ)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (hw' : ∀ k, ∃ i, w (v ⟨k, i⟩) ≠ 0) :
    w ∈ mcPts (bd.map (MvPolynomial.rename v)) ↔ (fun p => w (v p)) ∈ mcPts bd := by
  have e : ∀ f : MRing J, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ)
      (MvPolynomial.rename v f)) =
      MvPolynomial.eval (fun p => w (v p)) (MvPolynomial.map (Int.castRingHom ℂ) f) := by
    intro f
    rw [MvPolynomial.map_rename, MvPolynomial.eval_rename]
    rfl
  constructor
  · intro h
    exact ⟨hw', fun f hf => by
      rw [← e]
      exact h.2 _ (Ideal.mem_map_of_mem _ hf)⟩
  · intro h
    refine ⟨hw, fun f hf => ?_⟩
    let φ : MRing J' →+* ℂ := (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ))
    have hle : bd.map (MvPolynomial.rename v) ≤ RingHom.ker φ :=
      Ideal.map_le_iff_le_comap.2 fun g hg => by
        show φ (MvPolynomial.rename v g) = 0
        show MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.rename v g)) = 0
        rw [e]
        exact h.2 g hg
    exact hle hf

end Ideal

theorem inter_isVBOn_char0 {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hg : IsCptGen ξ) (cst : c.F →+* Ω) {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li)
    (ρ : 𝓞 E →+* Module.End Ω Li) (hact : M.IsActOf t.act.act ρ)
    (hint : ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q))
    (s : CMType H ⊕ CMType H) :
    (M.lat.inter (eigSp ρ (cst.comp (labelEmb c s)))).IsVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q}
      (Module.finrank Ω (eigSp ρ (cst.comp (labelEmb c s)))) (eigSp ρ (cst.comp (labelEmb c s))) := by
  classical
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  have hl := GlobalTheory.T.label_embedding_injective E H l c
  have hinj : Function.Injective fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s) := by
    intro s s' h
    exact hl.1 (RingHom.ext fun a => cst.injective (congrArg (fun φ : 𝓞 E →+* Ω => φ a) h))
  have hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card]; exact hl.2
  have hvb := (GlobalTheory.T.lie_omega_lattice_vector_bundle X Ω ξ t.G Li M hg t.semi.smooth).1
  have := (GlobalTheory.T.lattice_eigen_vector_bundle X Ω ξ Li E ρ M.lat {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (Module.finrank Ω Li) _
    (fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s)) hg hinj hcard ?_ ?_ ?_ ?_).1
  · exact this s
  · intro p _
    exact hvb p trivial |>.imp fun U h => ⟨h.1, h.2.imp fun b hb => ⟨hb.1, fun q _ hq => hb.2 q trivial hq⟩⟩
  · intro p _ a e he
    haveI := t.act.hom
    exact SatModel.lat_stable M t.act.act ρ hact p a e he
  · intro p hp s a
    have hf := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg p).2.1
    have := hint p hp
    have hi : IsIntegral ℤ (cst (labelEmb c s a)) :=
      (RingOfIntegers.isIntegral a).map (cst.comp (labelEmb c s)).toIntAlgHom
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hi.tower_top (A := regAt ξ p))
    exact hz ▸ z.2
  · intro p hp
    refine SatModel.unitAt_int hp ?_
    exact_mod_cast NumberField.discr_ne_zero E

theorem exists_cst {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {Ω : Type} [Field Ω]
    (y₀ : Sp Ω ⟶ Xo.XF c) :
    ∃ cst : c.F →+* Ω, y₀ ≫ Y.j ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
  refine ⟨(Spec.preimage (y₀ ≫ pullback.snd _ _)).hom, ?_⟩
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc]
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem isIntegrallyClosed_of_snc {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    [CharZero Ω] {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {y : (Σ k, J k) → Ω} {e : ℕ}
    {bd : Ideal (MRing J)} (htie : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)
    (hsnc : Cmp.IsSncModel y e bd) (q : Cpt ξ) (hq : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) :
    IsIntegrallyClosed (regAt ξ q) := by
  classical
  have hg := htie.gen
  obtain ⟨hloc, hfr, -⟩ := regAt_isLocalRing_isFractionRing_stalk X Ω ξ hg q
  obtain ⟨c, hc0, hc⟩ := htie.cover q
  have hck : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc0) k (Finset.mem_univ k)
  let r : (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩
  have hseg : ∀ c' : (k : K) → J k, (∏ k, y ⟨k, c' k⟩) / (∏ k, y ⟨k, c k⟩) = ∏ k, r ⟨k, c' k⟩ := fun c' =>
    (Finset.prod_div_distrib _ _).symm
  have hr : ∀ p, r p ∈ regAt ξ q := by
    rintro ⟨k, i⟩
    have h := hc (Function.update c k i)
    have e : ∏ k', r ⟨k', Function.update c k i k'⟩ = r ⟨k, i⟩ := by
      rw [Finset.prod_eq_single k]
      · simp
      · intro b _ hb
        rw [Function.update_of_ne hb]
        exact div_self (hck b)
      · simp
    rw [← e, ← hseg]
    exact h
  have hQ : ∀ a : ℚ, algebraMap ℚ Ω a ∈ regAt ξ q := by
    intro a
    have hd : ((a.den : ℤ) : Ω) ≠ 0 := by exact_mod_cast a.den_nz
    have hu := SatModel.unitAt_int hq hd
    have e : algebraMap ℚ Ω a = (a.num : Ω) * ((a.den : ℤ) : Ω)⁻¹ := by
      rw [eq_ratCast, Rat.cast_def]
      simp [div_eq_mul_inv]
    rw [e]
    exact mul_mem (intCast_mem _ _) hu.2.2
  let A : Subalgebra ℚ Ω :=
    { carrier := regAt ξ q
      mul_mem' := fun ha hb => mul_mem ha hb
      one_mem' := one_mem _
      add_mem' := fun ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      algebraMap_mem' := hQ }
  have hR : Algebra.adjoin ℚ (Set.range r) ≤ A := Algebra.adjoin_le (by rintro _ ⟨p, rfl⟩; exact hr p)
  obtain ⟨m, f, a, hf, ha, hs1, hsm⟩ := hsnc c hck
  let f' : Fin m → regAt ξ q := fun l => ⟨f l, hR (hf l)⟩
  let a' : Fin m → regAt ξ q := fun l => ⟨a l, hR (ha l)⟩
  have hsum' : ∑ l, a' l * f' l = 1 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    exact hs1
  obtain ⟨l, hl⟩ : ∃ l, IsUnit (f' l) := by
    by_contra hcon
    push_neg at hcon
    have h1 : (1 : regAt ξ q) ∈ IsLocalRing.maximalIdeal (regAt ξ q) := by
      rw [← hsum']
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon l))
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  obtain ⟨u, hu⟩ := hl.exists_right_inv
  have hu' : f l * (u : Ω) = 1 := congrArg Subtype.val hu
  have hfl0 : f l ≠ 0 := left_ne_zero_of_mul_eq_one hu'
  have hfinv : (f l)⁻¹ ∈ regAt ξ q := by
    rw [← eq_inv_of_mul_eq_one_right hu']
    exact u.2
  let S : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range r))
  obtain ⟨hsmooth, -⟩ := hsm l hfl0 S rfl
  haveI := hsmooth
  haveI : IsIntegrallyClosed S := GlobalTheory.isIntegrallyClosed_of_smooth ℚ S
  have hSle : S ≤ A := Algebra.adjoin_le (by
    rintro _ (rfl | ⟨p, rfl⟩)
    · exact hfinv
    · exact hr p)
  have hZ : ∀ s ∈ Algebra.adjoin ℤ (Set.range fun c' : (k : K) → J k =>
      (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩), s ∈ S := by
    have h : Algebra.adjoin ℤ (Set.range fun c' : (k : K) → J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) ≤
        S.restrictScalars ℤ := Algebra.adjoin_le (by
      rintro _ ⟨c', rfl⟩
      show _ ∈ S
      simp only [hseg]
      exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨_, rfl⟩))
    exact fun s hs => h hs
  let φ : S →+* regAt ξ q :=
    { toFun := fun s => ⟨s.1, hSle s.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra S (regAt ξ q) := φ.toAlgebra
  let P : Ideal S := (IsLocalRing.maximalIdeal (regAt ξ q)).comap (algebraMap S (regAt ξ q))
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : ∀ s : S, s ∉ P ↔ IsUnit (algebraMap S (regAt ξ q) s) := fun s => IsLocalRing.notMem_maximalIdeal
  haveI : IsLocalization.AtPrime (regAt ξ q) P :=
    { map_units := fun s => (hP s).1 s.2
      surj := fun z => by
        obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ htie c q ⟨hc0, hc⟩ z.1).1 z.2
        have hsu' : IsUnit (algebraMap S (regAt ξ q) ⟨s, hZ s hs⟩) := by
          refine IsUnit.of_mul_eq_one (⟨s⁻¹, hsu.2.2⟩ : regAt ξ q) (Subtype.ext ?_)
          exact mul_inv_cancel₀ hsu.1
        refine ⟨(⟨s * z.1, hZ _ hsa⟩, ⟨⟨s, hZ s hs⟩, (hP _).2 hsu'⟩), Subtype.ext ?_⟩
        exact mul_comm _ _
      exists_of_eq := fun {a b} h => ⟨1, by
        have : a = b := Subtype.ext (show (a : Ω) = b from congrArg (Subtype.val : regAt ξ q → Ω) h)
        rw [this]⟩ }
  exact (GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth ℚ P (regAt ξ q)).2

end GlobalTheory.CompanionTheory.Ar.EigBase

namespace GlobalTheory.CompanionTheory.Ar

open EigBase in

theorem exists_eigBase : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] [CharZero Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω₀) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω₀) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) (_ : AddCommGroup Li) (_ : Module Ω₀ Li) (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω₀ Li) (L : CMType H ⊕ CMType H → Lat ξ Li) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ ξ ≫ f = ξ₀ ∧ ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) ∧ M.IsActOf t.act.act ρ ∧ (∀ s, (L s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s)))) ∧ (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) ∧ Cmp.IsSncModel y D.dim bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  classical
  intro hRes E _ _ _ H D l Xo c Y Ω₀ _ _ ξ₀ hgen
  obtain ⟨K₀, _, J₀, _, y₀, X₀, ξ, f₀, bd₀, -, hall, htie, hξ, hsnc, hbd⟩ :=
    GlobalTheory.T.exists_coords_of_generic_point hRes E H D l Xo c Y Ω₀ ξ₀ hgen
  have hg : IsCptGen ξ := htie.gen
  obtain ⟨yp, hyp⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω₀ ξ₀ (GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y Ω₀ ξ₀ hgen)
  obtain ⟨cst, hcst⟩ := exists_cst Y yp
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H X₀, Nonempty (SABMap t Y.t f₀) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.proved_CubePullSt f₀ Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨Li, _, _, ⟨M⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ t.G Ω₀ ξ
  obtain ⟨ρ, hact, -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ t.G Ω₀ ξ Li M (𝓞 E) t.act.act t.act.hom
    t.act.one t.act.mul t.act.add
  have hcst₁ : ξ ≫ f₀ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [← Category.assoc, hξ, hyp, Category.assoc, hcst]
  obtain ⟨hfd, hrk⟩ := GlobalTheory.T.eigen_lattice_constant_rank E H D l Xo c Y X₀ Ω₀ ξ f₀ yp t m Li M ρ cst (hξ.trans hyp) hcst₁ hact
  have hint : ∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q) :=
    fun q hq => isIntegrallyClosed_of_snc htie hsnc q hq
  have hvb := (GlobalTheory.T.lie_omega_lattice_vector_bundle X₀ Ω₀ ξ t.G Li M hg t.semi.smooth).1
  let V : CMType H ⊕ CMType H → Submodule Ω₀ Li := fun s => eigSp ρ (cst.comp (labelEmb c s))
  obtain ⟨hind, hsum⟩ := SatModel.lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact hint
  have hspanTop : ∀ p, Submodule.span Ω₀ (M.lat p : Set Li) = ⊤ := by
    intro p
    obtain ⟨U, hU, b, hb, hf⟩ := hvb p trivial
    rw [(hf p trivial hU).2, Submodule.span_span_of_tower, hb]
  have hgp : Flat.ZLat.gp ξ ∈ {q : Cpt ξ | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} := by
    intro r hr hn
    exact hn (Flat.ZLat.unitAt_gp hg (Nat.cast_ne_zero.2 hr.ne_zero))
  have htop : ⨆ s, V s = ⊤ := by
    rw [eq_top_iff, ← hspanTop (Flat.ZLat.gp ξ), Submodule.span_le]
    intro e he
    have he' : e ∈ M.lat (Flat.ZLat.gp ξ) := he
    rw [hsum _ hgp] at he'
    have hle : (⨆ s, M.lat.inter (V s) (Flat.ZLat.gp ξ)) ≤
        (⨆ s, V s).restrictScalars (regAt ξ (Flat.ZLat.gp ξ)) :=
      iSup_le fun s v hv => (le_iSup V s) hv.2
    exact hle he'
  obtain ⟨π, hπ₁, hπ₂, hπ₃⟩ := exists_proj V hind htop
  let L : CMType H ⊕ CMType H → Lat ξ Li := fun s => M.lat.map (π s)
  have hcoh : ∀ s, (L s).IsCohOn Set.univ := fun s =>
    (GlobalTheory.T.coherent_lattice_closure X₀ Ω₀ ξ Li Li M.lat M.lat Set.univ).2.1 (π s)
      ((GlobalTheory.T.coherent_lattice_closure X₀ Ω₀ ξ Li Li M.lat M.lat Set.univ).1 _ _ hvb)
  have hspan : ∀ s p, Submodule.span Ω₀ (L s p : Set Li) = V s := fun s p => by
    rw [span_map_eq_range (hspanTop p), hπ₃]
  have hLeq : ∀ s (p : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → L s p = M.lat.inter (V s) p :=
    fun s p hp => map_proj_eq hπ₁ hπ₂ (hsum p hp) s

  let x : ((k : K₀) → J₀ k) → Ω₀ := fun c' => ∏ k, y₀ ⟨k, c' k⟩
  have hover : ξ ≫ (specZIsTerminal.from X₀) = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω₀)) :=
    specZIsTerminal.hom_ext _ _
  have hw : ∃ l, x l ≠ 0 := by
    obtain ⟨l, hl⟩ := htie.cover (Flat.ZLat.gp ξ)
    exact ⟨l, hl.1⟩
  obtain ⟨κ', _, y0, M', g, hd, hN, hch, hflat, hnorm⟩ := GlobalTheory.T.flag_model_common_refinement ℤ Ω₀ ((k : K₀) → J₀ k) x
    (PModel.mk X₀ ξ (specZIsTerminal.from X₀) hover hall htie) Unit (fun _ => (k : K₀) → J₀ k) (fun _ => x)
    (CMType H ⊕ CMType H) (fun _ => Li) L V (fun _ => hw) hcoh hspan
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates M'.ξ ξ g (RingHom.id Ω₀) := hd
  have hξ' : M'.ξ ≫ g = ξ := by
    have : M'.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω₀)) ≫ ξ := hd'
    rw [this]
    simp
  have hg' : IsCptGen M'.ξ := M'.tie.gen
  obtain ⟨K₁, _, J₁, _, y₁, bk, bx, -, hbk, hy₁, tie₁, -⟩ := GlobalTheory.T.segre_refine_line_bundles ℤ Ω₀ κ' y0 M' K₀ J₀ y₀ Empty Empty.elim
    (hch ()) (fun a => a.elim)
  obtain ⟨t', ⟨m₁⟩⟩ : ∃ t' : SAB H M'.X, Nonempty (SABMap t' t g) := by
    obtain ⟨_, _, _, _, _, m₁, -⟩ := sabPull Out.proved_CubePullSt g t
    exact ⟨_, ⟨m₁⟩⟩
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H Y.X X₀ M'.X Y.t t t' f₀ g m m₁
  obtain ⟨Ml, hMl, hlat, hactl⟩ := SatModel.exists_lieModel_pull t t' g m₁ M'.ξ M ρ hg hg' hd' hact
  have hnormAt : ∀ p : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → NormAt M'.ξ g (RingHom.id Ω₀) p := by
    intro p hp
    refine hnorm p (fun _ => htie.cover p) fun s => ?_
    obtain ⟨U, hU, b, -, hf⟩ := inter_isVBOn_char0 c t ξ hg cst M ρ hact hint s p hp
    refine ⟨_, b, (hf p hp hU).1, ?_⟩
    rw [hLeq s p hp]
    exact (hf p hp hU).2
  have hdown : ∀ (q : Cpt M'.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre M'.ξ r q) → ∀ h : genPt ξ ⤳ g q.1,
      ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨g q.1, h⟩ := by
    intro q hq h r hr hn
    obtain ⟨h', -, h2⟩ := RegAtDom.regAt_dominates X₀ Ω₀ ξ M'.X Ω₀ M'.ξ g (RingHom.id Ω₀) hd' q
    exact hn (h2 hg' _ (natCast_mem _ r) (not_not.1 (hq r hr)))
  have hreg : ∀ q' : Cpt M'.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre M'.ξ r q') → ∀ h : genPt ξ ⤳ g q'.1,
      regAt M'.ξ q' = regAt ξ ⟨g q'.1, h⟩ := fun q hq h =>
    (SatModel.normAt_id_elim hg (hint _ (hdown q hq h)) (hnormAt _ (hdown q hq h))).1 q rfl
  have huniq : ∀ q₁ q₂ : Cpt M'.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre M'.ξ r q₁) → g q₁.1 = g q₂.1 → q₁ = q₂ := by
    intro q₁ q₂ hq e
    obtain ⟨h, -⟩ := RegAtDom.regAt_dominates X₀ Ω₀ ξ M'.X Ω₀ M'.ξ g (RingHom.id Ω₀) hd' q₁
    exact (SatModel.normAt_id_elim hg (hint _ (hdown q₁ hq h)) (hnormAt _ (hdown q₁ hq h))).2 q₁ q₂ rfl e.symm
  let v : (Σ k, J₀ k) → Σ k, J₁ k := fun p => ⟨bk p.1, bx p.1 p.2⟩
  refine ⟨K₁, inferInstance, J₁, inferInstance, y₁, M'.X, M'.ξ, g ≫ f₀, cst, t', n, Li, inferInstance, inferInstance,
    Ml, ρ, fun s => (L s).pull M'.ξ g (AddMonoidHom.id Li), bd₀.map (MvPolynomial.rename v), M'.all, tie₁, ?_, ?_, hactl,
    ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hξ', hξ]
  · have e : M'.ξ ≫ (g ≫ f₀) ≫ Y.s = (M'.ξ ≫ g) ≫ f₀ ≫ Y.s := by simp only [Category.assoc]
    rw [e, hξ']
    exact hcst₁
  · intro s
    have h := hflat s
    rw [hrk s] at h
    exact h
  · intro s q hq
    obtain ⟨h, -⟩ := RegAtDom.regAt_dominates X₀ Ω₀ ξ M'.X Ω₀ M'.ξ g (RingHom.id Ω₀) hd' q
    have hr := hreg q hq h
    have hp := hdown q hq h
    ext e
    show e ∈ (L s).pull M'.ξ g (AddMonoidHom.id Li) q ↔ e ∈ Ml.lat q ∧ e ∈ eigSp ρ (cst.comp (labelEmb c s))
    rw [hlat, mem_pull_iff _ q h hr, mem_pull_iff _ q h hr, hLeq s _ hp]
    exact Iff.rfl
  · exact GlobalTheory.T.snc_model_reindexed_coords X₀ M'.X Ω₀ ξ M'.ξ g K₀ J₀ y₀ K₁ J₁ y₁ bk bx D.dim bd₀ hall M'.all htie tie₁ hξ' hy₁ hreg huniq hsnc
  · intro z w hw
    have hw₁ := GlobalTheory.T.complex_coords_reindexed X₀ M'.X Ω₀ ξ M'.ξ g K₀ J₀ y₀ K₁ J₁ y₁ bk bx z w hall M'.all hg' hξ' hy₁ hreg hw
    have hne : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hw.1 k).imp fun _ h => h.ne_zero
    have hne' : ∀ k, ∃ i, w (v ⟨k, i⟩) ≠ 0 := fun k => (hw₁.1 k).imp fun _ h => h.ne_zero
    rw [mem_mcPts_rename v bd₀ w hne hne']
    refine (show (fun p => w (v p)) ∈ mcPts bd₀ ↔ _ from hbd (z ≫ g) _ hw₁).trans ?_
    have hc : f₀ (centre (z ≫ g)) = (g ≫ f₀) (centre z) := rfl
    rw [hc]

end GlobalTheory.CompanionTheory.Ar
