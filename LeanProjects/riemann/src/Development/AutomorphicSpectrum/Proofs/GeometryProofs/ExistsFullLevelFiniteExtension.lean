import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquivStatement

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR.LevelPt

theorem exists_finite_subfield {F k : Type} [Field F] [Field k] [Algebra F k] [Algebra.IsAlgebraic F k]
    {X : Scheme.{0}} (s : X ⟶ Sp F) [LocallyOfFiniteType s] (p : Sp k ⟶ X)
    (hp : p ≫ s = spMap (algebraMap F k)) :
    ∃ K : IntermediateField F k, FiniteDimensional F K ∧ ∃ q : Sp K ⟶ X, spMap (algebraMap K k) ≫ q = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint k))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(X, U) ⟶ CommRingCat.of k, Spec.map f ≫ hU.fromSpec = p := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum k) y (IsLocalRing.closedPoint k)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of F ⟶ Γ(X, U), Spec.map g = hU.fromSpec ≫ s :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap F k) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf]
      exact hp)
  have hV : ∀ r : F, f.hom (g.hom r) = algebraMap F k r := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra F Γ(X, U) := g.hom.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType F Γ(X, U) from hft).out
  let S : Set k := (t.image f.hom : Finset k)
  let K := IntermediateField.adjoin F S
  refine ⟨K, IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin F (t : Set Γ(X, U)) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin F S (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(X, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Spec.map f' ≫ hU.fromSpec, ?_⟩
  change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
  rw [← hf, ← Spec.map_comp_assoc]
  rfl

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem epi_spMap {K k : Type} [Field K] [Field k] (f : K →+* k) : Epi (spMap f) := by
  have h1 : Flat (spMap f) := by
    let _ := f.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (show (algebraMap K k).Flat from
      RingHom.flat_algebraMap_iff.2 inferInstance)
  have h2 : Surjective (spMap f) :=
    ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_reps (M : Type) [AddCommGroup M] [Module.Finite ℤ M] (N : ℕ) (hN : 0 < N) :
    ∃ (T : Type) (_ : Finite T) (r : M → T) (u : T → M), ∀ a, ∃ b, a = u (r a) + N • b := by
  let S : Submodule ℤ M := LinearMap.range ((N : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))
  have hfin : Finite (M ⧸ S) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro x
    obtain ⟨a, rfl⟩ := S.mkQ_surjective x
    refine ⟨⟨(N : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN.ne')⟩, ?_⟩
    show (N : ℤ) • S.mkQ a = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero S).2 ⟨a, by simp⟩
  refine ⟨M ⧸ S, hfin, S.mkQ, fun t => Function.surjInv S.mkQ_surjective t, fun a => ?_⟩
  have h : S.mkQ (Function.surjInv S.mkQ_surjective (S.mkQ a)) = S.mkQ a :=
    Function.surjInv_eq _ _
  obtain ⟨b, hb⟩ := (Submodule.Quotient.eq S).1 h.symm
  refine ⟨b, ?_⟩
  have hb' : (N : ℤ) • b = a - Function.surjInv S.mkQ_surjective (S.mkQ a) := by simpa using hb
  have : N • b = (N : ℤ) • b := by simp
  rw [this, hb']
  abel

theorem exists_extend {L K C : Type} [Field L] [Field K] [Algebra L K] [Algebra.IsAlgebraic L K] [Field C] [IsAlgClosed C]
    (f : L →+* C) : ∃ g : K →+* C, ∀ x, g (algebraMap L K x) = f x := by
  letI := f.toAlgebra
  exact ⟨(IsAlgClosed.lift : K →ₐ[L] C), fun x => (IsAlgClosed.lift : K →ₐ[L] C).commutes x⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem finite_La (D : Datum H) : Module.Finite ℤ D.La :=
  haveI := D.fin
  Module.Finite.trans (𝓞 E) D.La

theorem exists_of_tateIso {D : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) {K L : Type} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsAlgClosed L] [CharZero L] (y : Sp K ⟶ Xo.XF c) (N : ℕ) (hN : 1 ≤ N)
    (I : TateIsoAt D Y.oF.t (spMap (algebraMap K L) ≫ y)) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (z : Ωˣ)
      (ev : D.La → (Over.mk (spMap (algebraMap K Ω) ≫ y ≫ Y.j) ⟶ Y.t.G)),
      FiniteDimensional K Ω ∧ IsFullLevelAt D Y.t (spMap (algebraMap K Ω) ≫ y ≫ Y.j) N z ev := by
  classical
  have hN0 : 0 < N := hN
  haveI := Y.oF.proper

  let q : pullback Y.oF.t.G.hom y ⟶ Sp K := pullback.snd _ _
  have hw : ∀ a, (I.ev N a).left ≫ Y.oF.t.G.hom = spMap (algebraMap K L) ≫ y := fun a =>
    Over.w (I.ev N a)
  let g : D.La → (Sp L ⟶ pullback Y.oF.t.G.hom y) := fun a =>
    pullback.lift (I.ev N a).left (spMap (algebraMap K L)) (hw a)
  have hg : ∀ a, g a ≫ q = spMap (algebraMap K L) := fun a => pullback.lift_snd _ _ _
  have hgf : ∀ a, g a ≫ pullback.fst _ _ = (I.ev N a).left := fun a => pullback.lift_fst _ _ _
  haveI := finite_La D
  obtain ⟨T, _, r, u, hru⟩ := exists_reps D.La N hN0
  choose F hF e he using fun τ : T => exists_finite_subfield q (g (u τ)) (hg _)

  let Fz : IntermediateField K L := IntermediateField.adjoin K {((I.ζ N : Lˣ) : L)}
  haveI : FiniteDimensional K Fz := IntermediateField.finiteDimensional_adjoin fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : ∀ τ, FiniteDimensional K (F τ) := hF
  let Ω : IntermediateField K L := Fz ⊔ ⨆ τ, F τ
  have hΩfin : FiniteDimensional K Ω := by
    haveI : FiniteDimensional K (⨆ τ, F τ : IntermediateField K L) :=
      IntermediateField.finiteDimensional_iSup_of_finite
    exact IntermediateField.finiteDimensional_sup _ _
  have hFΩ : ∀ τ, F τ ≤ Ω := fun τ => (le_iSup F τ).trans le_sup_right
  have hz : ((I.ζ N : Lˣ) : L) ∈ Ω :=
    (le_sup_left : Fz ≤ Ω) (IntermediateField.subset_adjoin K _ rfl)
  let z : (↥Ω)ˣ := Units.mk0 ⟨_, hz⟩ (fun h => (I.ζ N).ne_zero (congrArg Subtype.val h))
  let eΩ : T → (Sp Ω ⟶ pullback Y.oF.t.G.hom y) := fun τ =>
    spMap (IntermediateField.inclusion (hFΩ τ)).toRingHom ≫ e τ
  have heΩ : ∀ τ, spMap (algebraMap Ω L) ≫ eΩ τ = g (u τ) := fun τ => by
    rw [← he τ]
    simp only [eΩ]
    rw [← Category.assoc, spMap_comp_spMap]
    rfl
  haveI := epi_spMap (algebraMap Ω L)
  have hover : ∀ τ, eΩ τ ≫ q = spMap (algebraMap K Ω) := fun τ => by
    rw [← cancel_epi (spMap (algebraMap Ω L)), ← Category.assoc, heΩ, hg, spMap_comp_spMap]
    rfl
  have hpull : ∀ τ, eΩ τ ≫ pullback.fst _ _ ≫ Y.oF.t.G.hom = spMap (algebraMap K Ω) ≫ y := fun τ => by
    calc eΩ τ ≫ pullback.fst _ _ ≫ Y.oF.t.G.hom = eΩ τ ≫ q ≫ y := congrArg (eΩ τ ≫ ·) pullback.condition
      _ = (eΩ τ ≫ q) ≫ y := (Category.assoc _ _ _).symm
      _ = _ := congrArg (· ≫ y) (hover τ)

  have hφ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
  have hevw : ∀ τ, (eΩ τ ≫ pullback.fst _ _ ≫ Y.m.φ) ≫ Y.t.G.hom = spMap (algebraMap K Ω) ≫ y ≫ Y.j := fun τ => by
    have h := congrArg (· ≫ Y.j) (hpull τ)
    simp only [Category.assoc] at h ⊢
    rw [hφ]
    exact h
  let ev : D.La → (Over.mk (spMap (algebraMap K Ω) ≫ y ≫ Y.j) ⟶ Y.t.G) := fun a =>
    Over.homMk (eΩ (r a) ≫ pullback.fst _ _ ≫ Y.m.φ) (hevw (r a))
  refine ⟨Ω, inferInstance, inferInstance, z, ev, hΩfin, ?_⟩
  intro k _ _ i

  haveI : Algebra.IsAlgebraic Ω L := Algebra.IsAlgebraic.tower_top (K := K) Ω
  obtain ⟨i', hi'⟩ : ∃ i' : L →+* k, ∀ x : Ω, i' (algebraMap Ω L x) = i x := exists_extend i
  have hcomp : i'.comp (algebraMap Ω L) = i := RingHom.ext hi'
  have hprop : IsProper (pullback.snd Y.oF.t.G.hom (spMap (algebraMap K L) ≫ y)) := inferInstance
  obtain ⟨I', hI'⟩ := GlobalTheory.T.tate_iso_base_change E H D (Xo.XF c) Y.oF.t L k i' _ hprop I
  have hx : spMap i ≫ spMap (algebraMap K Ω) ≫ y ≫ Y.j =
      (spMap i' ≫ spMap (algebraMap K L) ≫ y) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    have h1 : spMap i ≫ spMap (algebraMap K Ω) = spMap i' ≫ spMap (algebraMap K L) := by
      rw [spMap_comp_spMap, spMap_comp_spMap, ← hcomp]
      rfl
    rw [← Category.assoc, h1]
    simp only [Category.assoc]
    rfl
  obtain ⟨I'', hζ, hev⟩ := (GlobalTheory.T.tate_iso_pullback_equiv E H D Y.X (Xo.XF c) Y.t Y.oF.t _ Y.m k _ _ hx).2 I'
  refine ⟨I'', ?_, fun a => ?_⟩
  · rw [← hζ]
    rw [(hI' N hN0).1]
    exact hi' z
  · obtain ⟨b, hb⟩ := hru a
    have hev1 : I.ev N a = I.ev N (u (r a)) := by
      have : I.ev N (N • b) = 1 := (I.ker N hN0 _).2 ⟨b, rfl⟩
      conv_lhs => rw [hb]
      rw [I.add, this, _root_.mul_one]
    have h2 : (I.ev N a).left = spMap (algebraMap Ω L) ≫ eΩ (r a) ≫ pullback.fst _ _ := by
      rw [← Category.assoc, heΩ, hgf, hev1]
    rw [← hev, (hI' N hN0).2 a, h2]
    show _ = spMap i ≫ eΩ (r a) ≫ pullback.fst _ _ ≫ Y.m.φ
    simp only [Category.assoc]
    rw [← Category.assoc (spMap i'), spMap_comp_spMap, hcomp]

end GlobalTheory.CompanionTheory.Ar.XR.LevelPt

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem exists_fullLevel_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (N : ℕ), 1 ≤ N → ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra K Ω) (z : Ωˣ) (ev : D.La → (Over.mk (spMap (algebraMap K Ω) ≫ y ≫ Y.j) ⟶ Y.t.G)), FiniteDimensional K Ω ∧ IsFullLevelAt D Y.t (spMap (algebraMap K Ω) ≫ y ≫ Y.j) N z ev := by
  intro E _ _ _ H D l Xo c O _ β Y K _ y N hN

  haveI hK : CharZero K := by
    let f : c.F →+* K := (Spec.preimage (y ≫ pullback.snd _ _)).hom
    exact charZero_of_injective_ringHom f.injective
  haveI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let xb : Sp (AlgebraicClosure K) ⟶ Xo.XF c := spMap (algebraMap K (AlgebraicClosure K)) ≫ y
  let f : CommRingCat.of (KA l) ⟶ CommRingCat.of (AlgebraicClosure K) :=
    Spec.preimage (xb ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have hf : xb ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap f.hom :=
    (Spec.map_preimage _).symm
  obtain ⟨-, I, -⟩ := Y.oF.geom (AlgebraicClosure K) xb f.hom hf
  exact LevelPt.exists_of_tateIso Y y N hN I

end GlobalTheory.CompanionTheory.Ar.XR
