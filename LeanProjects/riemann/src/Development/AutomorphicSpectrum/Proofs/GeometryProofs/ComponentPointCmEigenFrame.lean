import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelEigenvectorsActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep.ValExists

section Linear
variable {Ω F V ER : Type} [Field Ω] [Field F] [AddCommGroup V] [Module Ω V] [AddCommGroup ER] [Module F ER]
  {A : Subring Ω} {L : Submodule A V}

theorem mem_span_of_val (Q : Set L) (e : L) (h : (e : V) ∈ Submodule.span A (Subtype.val '' Q)) :
    e ∈ Submodule.span A Q := by
  have h1 : Submodule.span A (Subtype.val '' Q) = (Submodule.span A Q).map L.subtype := by
    rw [Submodule.map_span]; rfl
  rw [h1] at h
  obtain ⟨e', he', h2⟩ := h
  have : e' = e := Subtype.ext h2
  exact this ▸ he'

theorem ev_mem_span (ev : L →+ ER) (hev : ∀ a : A, ∃ r : F, ∀ e : L, ev (a • e) = r • ev e) (Q : Set L) (e : L)
    (h : e ∈ Submodule.span A Q) : ev e ∈ Submodule.span F (ev '' Q) := by
  induction h using Submodule.span_induction with
  | mem e he => exact Submodule.subset_span ⟨e, he, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul a e _ he =>
    obtain ⟨r, hr⟩ := hev a
    rw [hr]
    exact Submodule.smul_mem _ _ he

theorem span_ev_le (ev : L →+ ER) (hev : ∀ a : A, ∃ r : F, ∀ e : L, ev (a • e) = r • ev e) (Q Q' : Set L)
    (h : Submodule.span A (Subtype.val '' Q) ≤ Submodule.span A (Subtype.val '' Q')) :
    Submodule.span F (ev '' Q) ≤ Submodule.span F (ev '' Q') := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨e, he, rfl⟩
  exact ev_mem_span ev hev Q' e (mem_span_of_val Q' e (h (Submodule.subset_span ⟨e, he, rfl⟩)))

theorem frame_values {O I : Type} (ev : L →+ ER) (hev : ∀ a : A, ∃ r : F, ∀ e : L, ev (a • e) = r • ev e)
    (hspan : Submodule.span F (Set.range ev) = ⊤) {g : ℕ} (hER : Module.finrank F ER = g)
    (c : Fin g → L) (hcli : LinearIndependent Ω fun i => (c i : V))
    (hcL : ∀ e : L, e ∈ Submodule.span A (Set.range c))
    (S : I → Finset (Fin g)) (hcov : ∀ i, ∃ s, i ∈ S s)
    (T : O → (ER →ₗ[F] ER)) (χ : I → O → F)
    (hT : ∀ s, ∀ i ∈ S s, ∀ a, T a (ev (c i)) = χ s a • ev (c i))
    (hχ : ∀ s t, s ≠ t → ∃ a, χ s a ≠ χ t a) (s₀ : I) {n : ℕ} (b : Fin n → L)
    (hbli : LinearIndependent Ω fun i => (b i : V))
    (hbs : Submodule.span A (Set.range fun i => (b i : V)) =
      Submodule.span A ((fun i => (c i : V)) '' (S s₀ : Set (Fin g)))) :
    LinearIndependent F (fun i => ev (b i)) ∧
      ∀ w, (∀ a, T a w = χ s₀ a • w) → w ∈ Submodule.span F (Set.range fun i => ev (b i)) := by
  classical
  let f : Fin g → ER := fun i => ev (c i)
  have hfspan : ⊤ ≤ Submodule.span F (Set.range f) := by
    rw [← hspan]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨e, rfl⟩
    have := ev_mem_span ev hev _ e (hcL e)
    rwa [← Set.range_comp] at this
  have hcard : Fintype.card (Fin g) = Module.finrank F ER := by simp [hER]
  haveI : Module.Finite F ER := ⟨⟨Finset.univ.image f, by
    rw [eq_top_iff]; simpa using hfspan⟩⟩
  have hfli : LinearIndependent F f := linearIndependent_of_top_le_span_of_card_eq_finrank hfspan hcard

  have himg : (fun i => (c i : V)) '' (S s₀ : Set (Fin g)) = Subtype.val '' (c '' (S s₀ : Set (Fin g))) := by
    rw [Set.image_image]
  have hrng : (Set.range fun i => (b i : V)) = Subtype.val '' Set.range b := by
    rw [← Set.range_comp]; rfl
  have hF : Submodule.span F (Set.range fun i => ev (b i)) = Submodule.span F (f '' (S s₀ : Set (Fin g))) := by
    have e1 : (Set.range fun i => ev (b i)) = ev '' Set.range b := by
      rw [← Set.range_comp]; rfl
    have e2 : f '' (S s₀ : Set (Fin g)) = ev '' (c '' (S s₀ : Set (Fin g))) := by
      rw [Set.image_image]
    rw [e1, e2]
    refine le_antisymm (span_ev_le ev hev _ _ ?_) (span_ev_le ev hev _ _ ?_)
    · rw [← himg, ← hrng, hbs]
    · rw [← himg, ← hrng, hbs]

  have hΩ : Submodule.span Ω (Set.range fun i => (b i : V)) =
      Submodule.span Ω ((fun i => (c i : V)) '' (S s₀ : Set (Fin g))) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · intro v hv
      have h1 : v ∈ Submodule.span A ((fun i => (c i : V)) '' (S s₀ : Set (Fin g))) := by
        rw [← hbs]; exact Submodule.subset_span hv
      exact Submodule.span_le_restrictScalars A Ω _ h1
    · intro v hv
      have h1 : v ∈ Submodule.span A (Set.range fun i => (b i : V)) := by
        rw [hbs]; exact Submodule.subset_span hv
      exact Submodule.span_le_restrictScalars A Ω _ h1
  have hsub : ∀ {K W : Type} [Field K] [AddCommGroup W] [Module K W] (u : Fin g → W), LinearIndependent K u →
      Module.finrank K (Submodule.span K (u '' (S s₀ : Set (Fin g)))) = (S s₀).card := by
    intro K W _ _ _ u hu
    have h1 : LinearIndependent K (fun i : (S s₀ : Set (Fin g)) => u i) := hu.comp _ Subtype.val_injective
    have h2 := finrank_span_eq_card h1
    rw [← Set.image_eq_range] at h2
    simpa using h2
  have hcardn : n = (S s₀).card := by
    have h1 := finrank_span_eq_card hbli
    rw [hΩ, hsub _ hcli] at h1
    simpa using h1.symm
  refine ⟨?_, fun w hw => ?_⟩
  · rw [linearIndependent_iff_card_eq_finrank_span]
    show _ = Module.finrank F (Submodule.span F (Set.range fun i => ev (b i)))
    rw [hF, hsub f hfli]
    simp [hcardn]
  · rw [hF]
    let B : Module.Basis (Fin g) F ER := Module.Basis.mk hfli hfspan
    have hB : ∀ i, B i = f i := fun i => by simp [B]
    choose t ht using hcov
    let d : Fin g → F := fun i => B.repr w i
    have hw' : w = ∑ i, d i • f i := by
      conv_lhs => rw [← B.sum_repr w]
      exact Finset.sum_congr rfl fun i _ => by rw [hB]
    have hz : ∀ i, d i ≠ 0 → i ∈ S s₀ := by
      intro i hi
      by_contra hn
      have hne : t i ≠ s₀ := fun h => hn (h ▸ ht i)
      obtain ⟨a, ha⟩ := hχ _ _ hne
      have e1 : T a w = ∑ j, (d j * χ (t j) a) • B j := by
        conv_lhs => rw [hw', map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, hB]
        show d j • T a (ev (c j)) = _
        rw [hT _ j (ht j), smul_smul]
      have e2 : T a w = ∑ j, (χ s₀ a * d j) • B j := by
        rw [hw a]
        conv_lhs => rw [hw', Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, hB]
      have e3 := congrArg (fun q => B.repr q i) (e1.symm.trans e2)
      simp only [Module.Basis.repr_sum_self] at e3
      have e4 : d i * (χ (t i) a - χ s₀ a) = 0 := by
        rw [mul_sub, e3, mul_comm]; ring
      exact (mul_eq_zero.1 e4).elim hi (fun h => ha (sub_eq_zero.1 h))
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : d i = 0
    · rw [hi, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hz i hi, rfl⟩)
end Linear

section Geo

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.Flat.EigVb

theorem finrank_lie_eq {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Ω F : Type} [Field Ω]
    [Field F] (ξ : Sp Ω ⟶ X) (z : Sp F ⟶ X) (h : genPt ξ ⤳ centre z) {V ER : Type} [AddCommGroup V] [Module Ω V]
    [AddCommGroup ER] [Module F ER] (M : LieModel G ξ V) (MR : LieModel G z ER) :
    Module.finrank F ER = Module.finrank Ω V := by
  obtain ⟨R, _, x, hx, F', _, _, MC, n, bas, hp⟩ := LieVB.exists_chart G (centre z)
  obtain ⟨a, ha⟩ := LieVB.exists_lift x z hp
  have hgen : genPt ξ ∈ x.opensRange := h.mem_open x.opensRange.isOpen hp
  obtain ⟨φ, hφ⟩ := LieVB.exists_lift x ξ hgen
  obtain ⟨_, B, -, -⟩ := LieVB.basis_tr a x z ha MC MR bas
  obtain ⟨_, B', -, -⟩ := LieVB.basis_tr φ x ξ hφ MC M bas
  rw [Module.finrank_eq_card_basis B, Module.finrank_eq_card_basis B']

theorem valAt_act {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (f : G ⟶ G) [IsMonHom f] (A : V →ₗ[Ω] V)
    (hA : M.IsDiffOf f A) {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X} {e : V} {w : epsAt z ⟶ G}
    (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  rw [LieModel.valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  exact ⟨h1, v ≫ f, extends_act M f A hA _ hv, Category.assoc _ _ _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}

theorem mem_genFib (Z : CptOver Y U) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) : (⟨_, h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib :=
  ⟨Y.jQ (y (IsLocalRing.closedPoint F)), ((Scheme.Hom.comp_apply y (Y.jQ ≫ pullback.fst _ _) _).trans
      (Scheme.Hom.comp_apply Y.jQ (pullback.fst _ _) _)).symm⟩

theorem pt_over {F : Type} [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c)
    (hy : y ≫ pullback.snd _ _ = spMap βF) : (y ≫ Y.j) ≫ Y.s = spMap (βF.comp β) := by
  have h1 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  rw [Category.assoc, h1, ← Category.assoc, hy]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem val_inc (Z : CptOver Y U) (hβ : Function.Injective β)
    (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) {F : Type} [Field F] (βF : c.F →+* F)
    (y : Sp F ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap βF)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (t : c.F) :
    ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (Z.inc t) (βF t) := by
  let p : Cpt (Z.ξ₀ ≫ Y.j) := ⟨_, h⟩
  obtain ⟨s, hs⟩ := inc_mem_regAt Z hβ hfr p (mem_genFib Z y h) t
  refine ⟨h, s, hs, ?_⟩
  let tt : Spec (Y.X.presheaf.stalk p.1) ⟶ Spec (CommRingCat.of O) := Y.X.fromSpecStalk p.1 ≫ Y.s
  let θ : O →+* Y.X.presheaf.stalk p.1 := (Spec.preimage tt).hom
  have ht : Spec.map (CommRingCat.ofHom θ) = tt := by
    simp only [θ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hg : (genMap (Z.ξ₀ ≫ Y.j) p).comp θ = Z.inc.comp β := by
    refine LieVB.spec_cancel (𝟙 _) ?_
    rw [Category.comp_id, Category.comp_id, ← LieVB.spec_comp', ht]
    refine Eq.trans ?_ (gen_over Z)
    show _ ≫ Y.X.fromSpecStalk p.1 ≫ Y.s = _
    rw [← Category.assoc, LieCarrier.genMap_fromSpecStalk p]
  let vz : Y.X.presheaf.stalk p.1 →+* F := (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom
  have hv : vz.comp θ = βF.comp β := by
    refine LieVB.spec_cancel (𝟙 _) ?_
    rw [Category.comp_id, Category.comp_id, ← LieVB.spec_comp', ht]
    refine Eq.trans ?_ (pt_over (Y := Y) βF y hy)
    have e : Spec.map (CommRingCat.ofHom vz) ≫ Y.X.fromSpecStalk p.1 = y ≫ Y.j := spec_centre (y ≫ Y.j)
    show _ ≫ Y.X.fromSpecStalk p.1 ≫ Y.s = _
    rw [← Category.assoc, e]
  obtain ⟨a, b, hb, hx⟩ := hfr t
  have h1 : genMap (Z.ξ₀ ≫ Y.j) p (θ b) = Z.inc (β b) := congrArg (fun f : O →+* Z.Ω => f b) hg
  have h2 : genMap (Z.ξ₀ ≫ Y.j) p (θ a) = Z.inc (β a) := congrArg (fun f : O →+* Z.Ω => f a) hg
  have h3 : s * θ b = θ a := Z.gen.inj p (by rw [map_mul, hs, h1, h2, ← map_mul, hx])
  have v1 : vz (θ b) = βF (β b) := congrArg (fun f : O →+* F => f b) hv
  have v2 : vz (θ a) = βF (β a) := congrArg (fun f : O →+* F => f a) hv
  have h4 := congrArg vz h3
  rw [map_mul, v1, v2, ← hx, map_mul] at h4
  exact mul_right_cancel₀ ((map_ne_zero βF).2 hb) h4

theorem lat_eq_iSup (Z : CptOver Y U) (hβ : Function.Injective β)
    (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (x : Cpt (Z.ξ₀ ≫ Y.j)) (hx : x ∈ Z.genFib) :
    Z.M.lat x = ⨆ s : E →+* ℂ, Z.eig s x := by
  classical
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  let σ : (E →+* ℂ) → (𝓞 E →+* Z.Ω) := fun s => Z.inc.comp (tauIn c s)
  let φ : (E →+* ℂ) → (E →+* Z.Ω) := fun s => Z.inc.comp (Formalism.L2.Pj.embF c s)
  have hφ : Function.Injective φ := by
    intro s t h
    ext x
    have h1 := congrArg (fun m : E →+* Z.Ω => m x) h
    have h2 := Z.inc.injective h1
    exact congrArg (fun z : c.F => (z : ℂ)) h2
  have hσ : Function.Injective σ := by
    intro s t h
    refine hφ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_)
    exact h
  have hcard : Fintype.card (E →+* ℂ) = Module.finrank ℚ E := Embeddings.card E ℂ
  have hVB : Z.M.lat.IsVBOn Z.genFib (Module.finrank Z.Ω Z.V) ⊤ := fun p _ => by
    obtain ⟨W, h, b, hb, hf⟩ := lat_isVB_of_smooth Y.t.semi.smooth Z.M p (Set.mem_univ _)
    exact ⟨W, h, b, hb, fun q _ hq => hf q (Set.mem_univ _) hq⟩
  have hst : ∀ p ∈ Z.genFib, ∀ a, ∀ e ∈ Z.M.lat p, Z.ρ a e ∈ Z.M.lat p := fun p _ a e he => by
    haveI := Y.t.act.hom a
    exact lat_stable Z.M _ (Z.ρ a) (Z.act a) p he
  have hreg : ∀ p ∈ Z.genFib, ∀ s a, σ s a ∈ regAt (Z.ξ₀ ≫ Y.j) p :=
    fun p hp s a => inc_mem_regAt Z hβ hfr p hp (tauIn c s a)
  have hdisc : ∀ p ∈ Z.genFib, unitAt (Z.ξ₀ ≫ Y.j) p ((discr E : ℤ) : Z.Ω) := by
    intro p hp
    have hmem := inc_mem_regAt Z hβ hfr p hp
    have e : ((discr E : ℤ) : Z.Ω) = Z.inc ((discr E : ℤ) : c.F) := by simp
    have h0 : ((discr E : ℤ) : c.F) ≠ 0 := Int.cast_ne_zero.2 (discr_ne_zero E)
    refine ⟨by rw [e]; exact (map_ne_zero _).2 h0, by rw [e]; exact hmem _, ?_⟩
    rw [e, ← map_inv₀]
    exact hmem _
  exact (EigSplit.isVBOn_eigSp Y.X Z.Ω (Z.ξ₀ ≫ Y.j) Z.V E Z.ρ Z.M.lat Z.genFib _ (E →+* ℂ) σ Z.gen hσ
    hcard hVB hst hreg hdisc).2 x hx

theorem exists_ne_tauIn {F : Type} [Field F] (βF : c.F →+* F) (s t : E →+* ℂ) (h : s ≠ t) :
    ∃ a : 𝓞 E, βF (tauIn c s a) ≠ βF (tauIn c t a) := by
  by_contra hn
  push_neg at hn
  refine h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) ?_)
  ext a
  exact congrArg (fun z : c.F => (z : ℂ)) (βF.injective (hn a))

end Geo
end GlobalTheory.CompanionTheory.Ar.Flat.Rep.ValExists

namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

open GlobalTheory.CompanionTheory.Ar.Flat.Rep.ValExists GlobalTheory.CompanionTheory.Ar.Flat.EigVb

theorem valFam_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → ∀ (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c), y ≫ pullback.snd _ _ = spMap βF → Set.range y ⊆ U → ∀ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (σ : E →+* ℂ) (n : ℕ) (b : Fin n → Z.V), (Z.eig σ).IsFrameAt b ⟨_, h⟩ → ∃ v : Vecs y n, IsValFam Z y b v ∧ IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c σ)) v := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ hβ hτ F _ βF y hy _ h σ n b hb
  classical
  obtain ⟨hinj, -, hfr⟩ := id hβ
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  let ξ := Z.ξ₀ ≫ Y.j
  let z := y ≫ Y.j
  let x : Cpt ξ := ⟨_, h⟩
  have hx : x ∈ Z.genFib := mem_genFib Z y h
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨g, cc, ⟨hcli, hcL⟩, hS⟩ := h3 x hx
  choose S hS using hS
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists Y.X Y.t.G F z
  obtain ⟨ρF, hρF, -⟩ := lieModel_exists_unique_act _ Y.t.G F z ER MR (𝓞 E) Y.t.act.act Y.t.act.hom Y.t.act.one
    Y.t.act.mul Y.t.act.add
  obtain ⟨ev, hev1, hev2, hev3⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring Y.X Y.t.G Z.Ω ξ Z.V Z.M F z h ER MR Z.gen inferInstance
  have hval : ∀ e : Z.M.lat x, Z.M.ValAt z e (MR.pt (ev e)) := fun e => (hev1 e _).2 ⟨e.2, rfl⟩
  have hEig : ∀ (s : E →+* ℂ) (e : Z.M.lat x), (e : Z.V) ∈ Z.eig s x → ∀ a : 𝓞 E,
      ρF a (ev e) = βF (tauIn c s a) • ev e := by
    intro s e he a
    haveI := Y.t.act.hom a
    have hmem : (e : Z.V) ∈ eigSp Z.ρ (Z.inc.comp (tauIn c s)) := he.2
    have hρ : Z.ρ a e = Z.inc (tauIn c s a) • (e : Z.V) := by
      simpa [eigSp, Submodule.mem_iInf, sub_eq_zero] using (Submodule.mem_iInf _).1 hmem a
    have v2 := valAt_act Z.M (Y.t.act.act a) (Z.ρ a) (Z.act a) (hval e)
    rw [← hρF a (ev e)] at v2
    obtain ⟨he', h2⟩ := (hev1 _ _).1 v2
    have hreg : Z.inc (tauIn c s a) ∈ regAt ξ x := inc_mem_regAt Z hinj hfr x hx _
    have h4 : (⟨Z.ρ a e, he'⟩ : Z.M.lat x) = (⟨_, hreg⟩ : regAt ξ x) • e := Subtype.ext hρ
    rw [← h2, h4]
    exact hev2 ⟨_, hreg⟩ _ e (val_inc Z hinj hfr βF y hy h _)
  have hmemL : ∀ i, cc i ∈ Z.M.lat x := fun i => by
    rw [hcL]; exact Submodule.subset_span ⟨i, rfl⟩
  let cL : Fin g → Z.M.lat x := fun i => ⟨cc i, hmemL i⟩
  have hcov : ∀ i, ∃ s, i ∈ S s := by
    intro i
    have h1 : cc i ∈ ⨆ s : E →+* ℂ, Z.eig s x := by
      rw [← lat_eq_iSup Z hinj hfr x hx]; exact hmemL i
    simp_rw [hS] at h1
    rw [Submodule.iSup_span, ← Set.image_iUnion] at h1
    have h2 := Submodule.span_le_restrictScalars (regAt ξ x) Z.Ω _ h1
    by_contra hn
    push_neg at hn
    refine hcli.notMem_span_image (s := ⋃ s, (S s : Set (Fin g))) (x := i) ?_ h2
    simpa using hn
  have hfin : Module.finrank F ER = g := by
    rw [finrank_lie_eq Y.t.G ξ z h Z.M MR]
    obtain ⟨W, hW, b₀, hb₀, hf⟩ := lat_isVB_of_smooth Y.t.semi.smooth Z.M x (Set.mem_univ _)
    have hL := (hf x (Set.mem_univ _) hW).2
    have htop : Submodule.span Z.Ω (Set.range cc) = ⊤ := by
      rw [eq_top_iff, ← hb₀, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h1 : b₀ j ∈ Z.M.lat x := by
        rw [hL]; exact Submodule.subset_span ⟨j, rfl⟩
      rw [hcL] at h1
      exact Submodule.span_le_restrictScalars (regAt ξ x) Z.Ω _ h1
    have h2 := finrank_span_eq_card hcli
    rw [htop, finrank_top] at h2
    simpa using h2
  have hbmem : ∀ i, b i ∈ Z.eig σ x := fun i => by
    rw [hb.2]; exact Submodule.subset_span ⟨i, rfl⟩
  let bL : Fin n → Z.M.lat x := fun i => ⟨b i, (hbmem i).1⟩
  have hcE : ∀ s, ∀ i ∈ S s, cc i ∈ Z.eig s x := fun s i hi => by
    rw [hS s]; exact Submodule.subset_span ⟨i, hi, rfl⟩
  have hcLs : ∀ e : Z.M.lat x, e ∈ Submodule.span (regAt ξ x) (Set.range cL) := by
    intro e
    refine mem_span_of_val _ e ?_
    have h1 : Subtype.val '' Set.range cL = Set.range cc := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← hcL]
    exact e.2
  obtain ⟨li, sp⟩ := frame_values (A := regAt ξ x) (L := Z.M.lat x) ev
    (fun a => by
      obtain ⟨s, hs⟩ := a.2
      exact ⟨_, fun e => hev2 a _ e ⟨h, s, hs, rfl⟩⟩) hev3 hfin cL hcli hcLs S hcov
    (fun a => (ρF a : ER →ₗ[F] ER)) (fun s a => βF (tauIn c s a))
    (fun s i hi a => hEig s (cL i) (hcE s i hi) a)
    (fun s t hst => exists_ne_tauIn βF s t hst) σ bL hb.1 (hb.2.symm.trans (hS σ))
  have hmemE : ∀ u, u ∈ eigSp ρF (βF.comp (tauIn c σ)) ↔ ∀ a, ρF a u = βF (tauIn c σ a) • u := by
    intro u
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  have final : IsEigFrame Y.t.act z (βF.comp (tauIn c σ)) (fun k => MR.pt (ev (bL k))) := by
    refine (((GlobalTheory.T.lie_model_eigenvectors_action Y.X F Y.t.G z ER MR).2 (𝓞 E) Y.t.act ρF _ hρF).2 n _).2 ⟨li, le_antisymm ?_ ?_⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      exact (hmemE _).2 (hEig σ (bL k) (hbmem k))
    · intro w hw
      exact sp w ((hmemE w).1 hw)
  choose v hv using fun k => exists_sameVec_left Y y (MR.pt (ev (bL k)))
  exact ⟨v, fun k => ⟨_, hval (bL k), hv k⟩, isEigFrame_of_sameVec Y y _ v _ hv final⟩

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
