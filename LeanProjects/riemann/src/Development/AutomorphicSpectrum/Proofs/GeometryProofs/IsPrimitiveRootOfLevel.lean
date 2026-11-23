import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGoodReductionDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBasesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelCoverStHoldsStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeExists

theorem coordTie_reindex {o : Type} [CommRing o] {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra o Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' → κ)
    (he : Function.Surjective e) (x' : κ' → Ω) (hx : ∀ c, x' c = x (e c)) : CoordTie o ξ x' := by
  obtain rfl : x' = fun c => x (e c) := funext hx
  have hc : ∀ c p, InChart ξ (fun c => x (e c)) c p ↔ InChart ξ x (e c) p := fun c p =>
    and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (e c) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    obtain ⟨c, rfl⟩ := he c
    exact ⟨c, (hc c p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have : (Set.range fun j => x (e j) / x (e c)) = Set.range fun j => x j / x (e c) :=
      he.range_comp fun j => x j / x (e c)
    simpa only [hc, this] using h.ring (e c) h0 a

theorem exists_lift_torsion {S S' Z : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (b : Z ⟶ S') (a : Z ⟶ S) (hab : a = b ≫ f) (n : ℕ)
    (g : Over.mk a ⟶ G) (hg : g ^ n = 1) : ∃ g' : Over.mk b ⟶ G', g'.left ≫ φ = g.left ∧ g' ^ n = 1 := by
  subst hab
  let P : (Over.mk b ⟶ G') → (Over.mk (b ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this])
  have hP : ∀ x, (P x).left = x.left ≫ φ := fun _ => rfl
  let Φ : (Over.mk b ⟶ G') →* (Over.mk (b ≫ f) ⟶ G) := MonoidHom.mk' P fun x y =>
    Over.OverMorphism.ext ((hP _).trans (h.2 (Over.mk b) x y (P x) (P y) rfl rfl).symm)
  have hinj : Function.Injective Φ := fun x y hxy => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg CommaMorphism.left hxy) ((Over.w x).trans (Over.w y).symm))
  let g' : Over.mk b ⟶ G' := Over.homMk (h.1.lift g.left b (Over.w g)) (h.1.lift_snd _ _ _)
  have hg' : g'.left ≫ φ = g.left := h.1.lift_fst _ _ _
  refine ⟨g', hg', hinj ?_⟩
  have : Φ g' = g := Over.OverMorphism.ext hg'
  rw [map_pow, this, hg, map_one]

theorem fullTorsion_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ S'}
    {N n : ℕ} (hn : n ∣ N) (ht : FullTorsion G' ξ N) : FullTorsion G (ξ ≫ f) n := by
  intro k _ i g hg
  obtain ⟨g', e, hg'⟩ := exists_lift_torsion h (spMap i ≫ ξ) _ (Category.assoc _ _ _).symm n g hg
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, hx⟩ := ht k i g' (by rw [pow_mul, hg', one_pow])
  refine ⟨Over.homMk (x.left ≫ φ) ?_, ?_⟩
  · have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this]
  · rw [← e, hx]
    exact Category.assoc _ _ _

theorem finite_of_dominates {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y} (hξ : IsCptGen ξ) (f : X ⟶ Y) [IsFinite f] {i : Ω₀ →+* Ω}
    (h : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) : i.Finite := by
  have h1 : LocallyQuasiFinite (Spec.map (Scheme.stalkClosedPointTo ξ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).2
      (.of_finite (RingHom.Finite.of_surjective _ hξ.bij.2))
  have h2 : LocallyQuasiFinite ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    infer_instance
  have h3 : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) := by
    rw [← h]
    infer_instance
  have h4 : i.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite) (φ := CommRingCat.ofHom i)).1
      (LocallyQuasiFinite.of_comp _ ξ₀)
  algebraize [i]
  exact .of_quasiFinite

theorem genPt_of_dominates {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y} {f : X ⟶ Y} {i : Ω₀ →+* Ω}
    (h : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) : f (GlobalTheory.CompanionTheory.Ar.genPt ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ := by
  refine (Scheme.Hom.comp_apply ξ f _).symm.trans ?_
  rw [show ξ ≫ f = _ from h]
  exact (Scheme.Hom.comp_apply _ ξ₀ _).trans
    (congrArg ξ₀ (Subsingleton.elim (α := PrimeSpectrum Ω₀) _ _))

theorem isPrimitiveRoot_of_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {X : Scheme.{0}} {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} (hN : 0 < N) {z : Ωˣ}
    {ev : D.La → (Over.mk ξ ⟶ t.G)} (h : XR.IsFullLevelAt D t ξ N z ev) : IsPrimitiveRoot (z : Ω) N := by
  obtain ⟨I, hI, -⟩ := h (AlgebraicClosure Ω) (algebraMap Ω _)
  refine IsPrimitiveRoot.of_map_of_injective (f := algebraMap Ω (AlgebraicClosure Ω)) ?_ (RingHom.injective _)
  rw [← hI]
  exact IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim N hN)

theorem exists_hodgeCpt_flag : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (R : ℕ → ℕ) (e₀ : Y.X), e₀ ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, 4 ≤ R p) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), 𝔐.f (GlobalTheory.CompanionTheory.Ar.genPt 𝔐.ξ) = e₀ ∧ 𝔐.R = R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ Fl.RootLines xdeg e ∧ ∀ s, (𝔐.dR s).IsFlagVBOn Set.univ (Fl.b s) := by
  intro hW E _ _ _ H D l Xo c Y S R e₀ he hS hd hR
  have hN : 0 < ∏ p ∈ S, p ^ R p := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  obtain ⟨Ω, _, _, n, x, M, f, y₀, t, m, z, ev, hnorm, hfin, hf, hy, hlev, htor, -⟩ :=
    GlobalTheory.T.LevelCoverSt_holds E H D l Xo c Y e₀ he _ hN
  have hz := isPrimitiveRoot_of_level hN hlev
  have hζ : ∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ R p) := fun p hp => by
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun p => p ^ R p) hp
    exact ⟨_, hz.pow hN (hm.trans (mul_comm _ _))⟩
  let M₁ : PModel ℤ (fun c' : (k : Unit) → Fin n => ∏ k, (fun q : Σ _ : Unit, Fin n => x q.2) ⟨k, c' k⟩) :=
    ⟨M.X, M.ξ, M.s, M.hover, M.all,
      coordTie_reindex M.tie (fun c' => c' ()) (fun a => ⟨fun _ => a, rfl⟩) _ fun c' => by simp⟩
  obtain ⟨K₁, _, J₁, _, y₁, -, -, A, g₁, -, -, hg₁, hAf, hAR, hA, -⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l Xo c Y S R Ω Unit (fun _ => Fin n) (fun q => x q.2) M₁ f y₀ hnorm hy (hf ▸ he) hS hd hR
      (fun p hp => fullTorsion_push m.cart (Finset.dvd_prod_of_mem (fun p => p ^ R p) hp) htor) hζ
  have hg₁' : A.ξ ≫ g₁ = M.ξ := by
    rw [hg₁]
    simp [M₁]
  have hAy : A.ξ ≫ A.f = y₀ ≫ Y.j := by rw [hAf, ← Category.assoc, hg₁', hy]
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates M.ξ A.ξ₀ f A.fn := by
    have := A.fn_over
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at this ⊢
    rw [← this, hAy, hy]
  have hcov : A.IsCover (letI := A.fn.toAlgebra; Module.finrank A.Ω₀ Ω) := by
    refine ⟨?_, rfl⟩
    let := A.fn.toAlgebra
    have : Module.Finite A.Ω₀ Ω := finite_of_dominates M.tie.gen f hdom
    exact Module.finrank_pos
  obtain ⟨Ω', _, _, i, K₂, _, J₂, _, y₂, B, g₂, b, Li₀, a₀, m₀, M₀, j, V₀, hg₂, hBf, hBR, hB, hb, hj, hV, hgen⟩ :=
    GlobalTheory.T.hodge_cpt_good_reduction_degree hW E H D l Xo c Y S Ω K₁ J₁ y₁ A y₀ _ hAy hd hA (by rw [hAR]; exact hζ) hcov
  have hBy : B.ξ ≫ B.f = (spMap i ≫ y₀) ≫ Y.j := by
    rw [hBf, ← Category.assoc, hg₂, Category.assoc, hAy, Category.assoc]
  obtain ⟨K₃, _, J₃, _, y₃, -, -, C, g₃, Fl, xdeg, e, -, -, hg₃, hCf, hCR, -, hC, -, -, hroot, hdR, -⟩ :=
    GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω' K₂ J₂ y₂ B (spMap i ≫ y₀) b Li₀ a₀ m₀ M₀ j V₀ _ hBy hd hB
      (fun p hp => by
        obtain ⟨ζ, hζ'⟩ := hζ p hp
        exact ⟨i ζ, by rw [hBR, hAR]; exact hζ'.map_of_injective i.injective⟩) hb hj hV hgen
  refine ⟨Ω', inferInstance, inferInstance, K₃, inferInstance, J₃, inferInstance, y₃, C, Fl, xdeg, e, ?_,
    by rw [hCR, hBR, hAR], hC, hroot, hdR⟩
  rw [hCf, Scheme.Hom.comp_apply, genPt_of_dominates hg₃, hBf, Scheme.Hom.comp_apply, genPt_of_dominates hg₂, hAf,
    Scheme.Hom.comp_apply, genPt_of_dominates hg₁]
  exact hf

end GlobalTheory.CompanionTheory.Ar.HodgeExists
