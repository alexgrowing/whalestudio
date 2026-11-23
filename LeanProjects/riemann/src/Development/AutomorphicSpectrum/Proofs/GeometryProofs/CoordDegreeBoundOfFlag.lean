import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedSandwichDegreeBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsIndepOfSat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.Pick

theorem exists_indep_of_sat {R E : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [AddCommGroup E] [Module R E]
    [Module.Finite R E] [Module.IsTorsionFree R E] (T : Set E) (F : Submodule R E)
    (hF : ∀ x, x ∈ F ↔ ∃ a : R, a ≠ 0 ∧ a • x ∈ Submodule.span R T) :
    ∃ f : Fin (Module.finrank R F) → E, (∀ j, f j ∈ T) ∧ LinearIndependent R f :=
  _root_.UpperTheory.Reformulated.B.Ud9.exists_indep_of_sat T F hF

def valMap {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ X) : X.presheaf.stalk (centre z) →+* R :=
  (Scheme.stalkClosedPointTo z).hom

theorem isLocalHom_valMap {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (z : Sp R ⟶ X) :
    IsLocalHom (valMap z) :=
  inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)

theorem inv_nat_reg {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {L : Type} [Field L] [CharZero L]
    (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {m : ℕ} (hm : 0 < m) :
    (m : Ω) ≠ 0 ∧ (m : Ω)⁻¹ ∈ regAt ξ ⟨centre z, h⟩ := by
  have hu : IsUnit ((m : X.presheaf.stalk (centre z))) := by
    have hv : IsUnit (valMap z (m : X.presheaf.stalk (centre z))) := by
      rw [map_natCast]; exact (Nat.cast_ne_zero.2 hm.ne').isUnit
    haveI := isLocalHom_valMap z
    exact isUnit_of_map_unit (valMap z) _ hv
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have h1 : (m : Ω) * genMap ξ ⟨centre z, h⟩ g = 1 := by
    have := congrArg (genMap ξ ⟨centre z, h⟩) hg
    rwa [map_mul, map_natCast, map_one] at this
  have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨h0, ⟨g, eq_inv_of_mul_eq_one_right h1⟩⟩

theorem reg_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Sp R ⟶ X} {a : Ω} {r : R} (h : ValAt ξ z a r) (h' : genPt ξ ⤳ centre z) : a ∈ regAt ξ ⟨centre z, h'⟩ := by
  obtain ⟨_, s, hs, -⟩ := h
  exact ⟨s, hs⟩

theorem exists_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Sp R ⟶ X} {a : Ω} {h : genPt ξ ⤳ centre z} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

theorem valAt_zero_factor {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {L : Type} [Field L] [CharZero L]
    (hg : IsCptGen ξ) (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {m : ℕ} (hm : 0 < m) {a κ : Ω}
    (ha : a ∈ regAt ξ ⟨centre z, h⟩) (hκ : κ ∈ regAt ξ ⟨centre z, h⟩) (hκi : κ⁻¹ ∈ regAt ξ ⟨centre z, h⟩) (hκ0 : κ ≠ 0)
    (hv : ValAt ξ z ((m : Ω) * a * κ) 0) : ValAt ξ z a 0 := by
  obtain ⟨ga, hga⟩ : ∃ g : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ g = a := ha
  obtain ⟨gk, hgk⟩ : ∃ g : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ g = κ := hκ
  obtain ⟨gi, hgi⟩ : ∃ g : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ g = κ⁻¹ := hκi
  obtain ⟨_, gt, hgt, hgt0⟩ := hv
  replace hgt0 : valMap z gt = 0 := hgt0
  have e1 : gt = (m : X.presheaf.stalk (centre z)) * ga * gk := by
    apply hg.inj ⟨centre z, h⟩
    rw [hgt, map_mul, map_mul, map_natCast, hga, hgk]
  have e2 : gk * gi = 1 := by
    apply hg.inj ⟨centre z, h⟩
    rw [map_mul, map_one, hgk, hgi, mul_inv_cancel₀ hκ0]
  have e3 : valMap z gk * valMap z gi = 1 := by rw [← map_mul, e2, map_one]
  have e4 : valMap z gk ≠ 0 := left_ne_zero_of_mul_eq_one e3
  have e5 : valMap z ga = 0 := by
    rw [e1, map_mul, map_mul, map_natCast] at hgt0
    have hm' : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    simpa [hm', e4] using hgt0
  exact ⟨h, ga, hga, e5⟩

theorem lie_val_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (hg : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X} {e : Li} {v v' : epsAt z ⟶ G}
    (h : M.ValAt z e v) (h' : M.ValAt z e v') : v = v' := by
  obtain ⟨h₁, u, hu, hv⟩ := h
  obtain ⟨h₂, u', hu', hv'⟩ := h'
  have : u = u' := (lieLat_carrier X G Ω ξ Li M ⟨centre z, h₁⟩).2 hg inferInstance e u u' hu hu'
  subst this
  apply Over.OverMorphism.ext
  rw [hv, hv']

theorem mem_lat_of_val {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X} {e : Li} {v : epsAt z ⟶ G}
    (h : M.ValAt z e v) (h' : genPt ξ ⤳ centre z) : e ∈ M.lat ⟨centre z, h'⟩ := by
  obtain ⟨_, u, hu, -⟩ := h
  exact Submodule.subset_span ⟨u, hu⟩

theorem inChart_of_coords {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} [Fintype K] {J : K → Type}
    {y : (Σ k, J k) → Ω} {L : Type} [Field L] {z : Sp L ⟶ X} {w : (Σ k, J k) → L} (hw : CoordsAt ξ y z w)
    (h : genPt ξ ⤳ centre z) (c₀ : (k : K) → J k) (hc₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ ⟨centre z, h⟩ := by
  have hy : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (hc₀ k).isUnit).1
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (hw.2 k (c₀ k) (hc₀ k).isUnit).2 (c' k)
  exact reg_of_valAt hr h

theorem exists_cls {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : Fin r)
    {e : E} (he : e ∈ flagStep Ω b₀ (i + 1)) : ∃ t : Ω, IsCls b₀ i e t := by
  rw [Flag.step_succ] at he
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 he
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨t, by simpa [IsCls] using hy⟩

theorem sub_coord_mem {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b : Fin r → E)
    (π : Fin r → Module.Dual Ω E) (hπ : ∀ j l, π j (b l) = if j = l then 1 else 0) (i : Fin r)
    {e : E} (he : e ∈ flagStep Ω b (i + 1)) : e - π i e • b i ∈ flagStep Ω b i := by
  rw [Flag.step_succ] at he
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 he
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have hker : flagStep Ω b i ≤ LinearMap.ker (π i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hne : i ≠ k := by
      rintro rfl
      simp at hk
    simp [hπ, hne]
  have h0 : π i y = 0 := hker hy
  have : y + t • b i - π i (y + t • b i) • b i = y := by
    simp [h0, hπ]
  rwa [this]

theorem pick : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F : SatFlag B r), (∀ j : Fin (r + 1), IsSubFibre M (flagStep Ω b₀ j.val) z MB (F.F j)) →
      ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∃ (f : Fin i → B.carrier) (ef : Fin i → Li) (s : B.carrier) (e : Li) (t : Ω) (u : L)
        (vf : Fin i → (epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G)) (ve : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
        (∀ j, f j ∈ F.F i.castSucc) ∧ LinearIndependent (𝓞 L) f ∧ s ∈ F.F i.succ ∧ s ∉ F.F i.castSucc ∧
        (∀ j, ef j ∈ flagStep Ω b₀ i) ∧ e ∈ flagStep Ω b₀ (i + 1) ∧
        (∀ j, M.ValAt _ (ef j) (vf j) ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) (f j) (vf j)) ∧
        M.ValAt _ e ve ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) s ve ∧
        IsCls b₀ i e t ∧ ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u ∧ u ≠ 0 := by
  intro X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i a e₀ hc hall htie hm hind hsw hdeg L _ _ w z hw B MB F hsub c₀ hc₀
  have hg : IsCptGen ξ := htie.gen
  have hsub₀ : IsSubFibre M (flagStep Ω b₀ i) z MB (F.F i.castSucc) := by simpa using hsub i.castSucc
  have hsub₁ : IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB (F.F i.succ) := by simpa using hsub i.succ
  set zL := spMap (algebraMap (𝓞 L) L) ≫ z with hzL

  obtain ⟨f₀, hfT, hfi⟩ := exists_indep_of_sat _ (F.F i.castSucc) hsub₀
  have hrk : Module.finrank (𝓞 L) (F.F i.castSucc) = i := (F.rank i.castSucc).trans (by simp)
  have hrk₁ : Module.finrank (𝓞 L) (F.F i.succ) = i + 1 := (F.rank i.succ).trans (by simp)
  let f : Fin i → B.carrier := fun j => f₀ (Fin.cast hrk.symm j)
  have hfi' : LinearIndependent (𝓞 L) f := hfi.comp _ (Fin.cast_injective _)
  choose ef hef vf hv hl using fun j : Fin i => hfT (Fin.cast hrk.symm j)
  have hfF : ∀ j, f j ∈ F.F i.castSucc := fun j =>
    (hsub₀ _).2 ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span (hfT _)⟩

  obtain ⟨s, ⟨e, he, ve, hve, hsv⟩, hs0⟩ : ∃ s, (∃ e ∈ flagStep Ω b₀ (i + 1), ∃ v : epsAt zL ⟶ G,
      M.ValAt zL e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) s v) ∧ s ∉ F.F i.castSucc := by
    by_contra hno
    push_neg at hno
    have hle : F.F i.succ ≤ F.F i.castSucc := by
      intro x hx
      obtain ⟨c, hc₁, hcx⟩ := (hsub₁ x).1 hx
      have hsp := Submodule.span_le.2 (fun t ht => hno t ht) hcx
      exact F.sat _ c x hc₁ hsp
    have heq : F.F i.succ = F.F i.castSucc := le_antisymm hle (F.mono Fin.castSucc_lt_succ.le)
    rw [heq, hrk] at hrk₁
    omega
  have hs1 : s ∈ F.F i.succ := (hsub₁ s).2 ⟨1, one_ne_zero, by
    rw [one_smul]; exact Submodule.subset_span ⟨e, he, ve, hve, hsv⟩⟩

  have h : genPt ξ ⤳ centre zL := hall _
  obtain ⟨b, π, κ, hb, hfr, hmb, hπb, hπm, hκ0, hκ, hκi, hcl⟩ := cls_frame X Ω ξ K J y G Li M V r b₀ m i a e₀ hind hsw hdeg
    ⟨centre zL, h⟩ c₀ (inChart_of_coords hw h c₀ hc₀)
  obtain ⟨t, ht⟩ := exists_cls b₀ i he
  have hm0 := inv_nat_reg (ξ := ξ) zL h hm
  have he_lat := mem_lat_of_val M hve h
  have hAr : π i e ∈ regAt ξ ⟨centre zL, h⟩ := by
    have := mul_mem hm0.2 (hπm i e he_lat)
    rwa [inv_mul_cancel_left₀ hm0.1] at this
  have hα : (m : Ω)⁻¹ * π i e ∈ regAt ξ ⟨centre zL, h⟩ := mul_mem hm0.2 hAr
  have htg : t / gen y a e₀ c₀ = (m : Ω) * ((m : Ω)⁻¹ * π i e) * κ := by
    rw [hcl e t he ht, mul_inv_cancel_left₀ hm0.1]
  have hreg : t / gen y a e₀ c₀ ∈ regAt ξ ⟨centre zL, h⟩ := by
    rw [hcl e t he ht]; exact mul_mem hAr hκ
  obtain ⟨u, hu⟩ := exists_valAt hreg
  refine ⟨f, fun j => ef j, s, e, t, u, fun j => vf j, ve, hfF, hfi', hs1, hs0, hef, he,
    fun j => ⟨hv j, hl j⟩, hve, hsv, ht, hu, ?_⟩

  rintro rfl
  have hv0 : ValAt ξ zL ((m : Ω)⁻¹ * π i e) 0 :=
    valAt_zero_factor hg zL h hm hα hκ hκi hκ0 (htg ▸ hu)
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G L zL
  obtain ⟨ev, hev, hevs, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M L zL h ER MR hg inferInstance
  let ar : regAt ξ ⟨centre zL, h⟩ := ⟨_, hα⟩
  let xb : M.lat ⟨centre zL, h⟩ := ⟨_, hmb i⟩
  let xe : M.lat ⟨centre zL, h⟩ := ⟨e, he_lat⟩
  have h1 : ev (ar • xb) = 0 := by rw [hevs ar 0 xb hv0, zero_smul]
  have h2 : ((xe - ar • xb : M.lat ⟨centre zL, h⟩) : Li) = e - π i e • b i := by
    show e - ((m : Ω)⁻¹ * π i e) • (m : Ω) • b i = _
    have hmm : ((m : Ω)⁻¹ * π i e) * (m : Ω) = π i e := by
      have := hm0.1
      field_simp
    rw [smul_smul, hmm]
  have hval : M.ValAt zL e (MR.pt (ev xe)) := (hev e _).2 ⟨he_lat, rfl⟩
  have hveq : ve = MR.pt (ev xe) := lie_val_unique M hg hve hval
  have hval' : M.ValAt zL (e - π i e • b i) ve := by
    rw [hveq]
    refine (hev _ _).2 ⟨h2 ▸ (xe - ar • xb).2, ?_⟩
    have : (⟨e - π i e • b i, h2 ▸ (xe - ar • xb).2⟩ : M.lat ⟨centre zL, h⟩) = xe - ar • xb := Subtype.ext h2.symm
    rw [this, map_sub, h1, sub_zero]
  have hmem : e - π i e • b i ∈ flagStep Ω b₀ i := by
    rw [← hb i]
    exact sub_coord_mem b π hπb i (by rw [hb]; exact he)
  exact hs0 ((hsub₀ s).2 ⟨1, one_ne_zero, by
    rw [one_smul]; exact Submodule.subset_span ⟨_, hmem, ve, hval', hsv⟩⟩)

end GlobalTheory.CompanionTheory.Ar.RootHt.Pick
