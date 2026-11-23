import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.LocM GlobalTheory.LocM.Cht

noncomputable section

namespace GlobalTheory.LocM.Cht

theorem isFractionRing_ball (C : Type) [NormedField C] [IsUltrametricDist C] : IsFractionRing (intO C) C := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  by_cases h : ‖z‖ ≤ 1
  · exact ⟨⟨z, h⟩, 1, by rw [map_one, div_one]; rfl⟩
  · exact ⟨1, ⟨z⁻¹, show ‖z⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ (le_of_not_ge h)⟩,
      by rw [map_one, one_div]; exact (inv_inv z).symm⟩

section Ext

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}

theorem exists_pt_of_range (i : Idx H p) (k : Type) [Field k] (x : Sp k ⟶ (Y i).X)
    (hx : Set.range x ⊆ Set.range (Y i).j) :
    ∃ (f : i.c.F →+* k) (y : Sp k ⟶ (Xo i.l).XF i.c), y ≫ pullback.snd _ _ = spMap f ∧ y ≫ (Y i).j = x := by
  have := (Y i).jQ_open
  let g : i.c.V W →+* k := (Spec.preimage (x ≫ (Y i).s)).hom
  have hg : spMap g = x ≫ (Y i).s := Spec.map_preimage _
  have hinj : Function.Injective g := by
    obtain ⟨q⟩ : Nonempty (Sp k) := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨y₀, hy₀⟩ := hx ⟨q, rfl⟩
    have e1 : (spMap g) q = (pullback.snd _ _ ≫ spMap (i.c.V W).subtype) y₀ := by
      rw [hg, ← Model.j_s, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy₀]
    rw [Scheme.Hom.comp_apply] at e1
    obtain ⟨r, hr⟩ : ∃ r : PrimeSpectrum i.c.F, (spMap g) q = (spMap (i.c.V W).subtype) r := ⟨_, e1⟩
    have e2 := congrArg PrimeSpectrum.asIdeal hr
    change Ideal.comap g q.asIdeal = Ideal.comap (i.c.V W).subtype r.asIdeal at e2
    rw [@Ideal.eq_bot_of_prime _ _ _ q.2, Ideal.eq_bot_of_prime (K := i.c.F) r.asIdeal,
      Ideal.comap_bot_of_injective _ (i.c.V W).subtype_injective] at e2
    exact (RingHom.injective_iff_ker_eq_bot g).2 e2
  let f : i.c.F →+* k := IsFractionRing.lift hinj
  have hf : f.comp (i.c.V W).subtype = g := RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  have hpre : IsPreimmersion (spMap (i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (R := i.c.V W) (S := i.c.F) (nonZeroDivisors _)
  let q : Sp k ⟶ pullback (Y i).s (spMap (i.c.V W).subtype) :=
    pullback.lift x (spMap f) (by rw [← hg, ← hf, spMap_comp])
  have hq : q ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hr : Set.range q ⊆ Set.range (Y i).jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := hx ⟨z, rfl⟩
    refine ⟨y, (pullback.fst (Y i).s (spMap (i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq]
    exact hy
  refine ⟨f, IsOpenImmersion.lift _ q hr, ?_, ?_⟩
  · rw [← (Y i).jQ_over, IsOpenImmersion.lift_fac_assoc]
    exact pullback.lift_snd _ _ _
  · rw [Model.j, IsOpenImmersion.lift_fac_assoc, hq]

theorem exists_ptAt {i₀ : Idx H p} (Z : Mdl Y i₀) (C : SCF p) (z : Sp ↥(intO ↥C.S) ⟶ Z.X)
    (hz : Set.range (spMap (intO ↥C.S).subtype ≫ z) ⊆ Z.opn) : ∃ y : PtAt Z C, y.z = z := by
  let alg : Z.i.c.V W →+* ↥(intO ↥C.S) := (Spec.preimage (z ≫ Z.s)).hom
  have halg : spMap alg = z ≫ Z.s := Spec.map_preimage _
  obtain ⟨f, y, hy₁, hy₂⟩ := exists_pt_of_range (Y := Y) Z.i ↥C.S (spMap (intO ↥C.S).subtype ≫ z ≫ Z.π) (by
    rintro _ ⟨q, rfl⟩
    have := hz ⟨q, rfl⟩
    rw [← Category.assoc]
    exact this)
  have hs : z ≫ Z.π ≫ (Y Z.i).s = spMap alg := by rw [halg, Z.π_s]
  have compat : (intO ↥C.S).subtype.comp alg = f.comp (Z.i.c.V W).subtype := by
    have h : spMap ((intO ↥C.S).subtype.comp alg) = spMap (f.comp (Z.i.c.V W).subtype) := by
      rw [spMap_comp, spMap_comp, ← hs, ← hy₁, Category.assoc, ← Model.j_s, ← Category.assoc y, hy₂]
      simp only [Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  exact ⟨⟨⟨alg, f, compat, y, hy₁, z ≫ Z.π, hs, by rw [hy₂]⟩, z, rfl⟩, rfl⟩

theorem exists_ptAt_gen {i₀ : Idx H p} (Z : Mdl Y i₀) (C : SCF p) (w : Sp ↥C.S ⟶ Z.X)
    (alg : Z.i.c.V W →+* ↥(intO ↥C.S)) (hw : Set.range w ⊆ Z.opn)
    (hws : w ≫ Z.s = spMap ((intO ↥C.S).subtype.comp alg)) : ∃ y : PtAt Z C, y.gen = w := by
  have : IsProper Z.s := projProper _ _ Z.s ⟨Z.n, Z.I.subschemeι, inferInstance, rfl⟩
  have := isFractionRing_ball ↥C.S
  have hE : ValuativeCriterion.Existence Z.s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed Z.s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact : MorphismProperty Scheme) Z.s).1
  let S : ValuativeCommSq Z.s :=
    { R := ↥(intO ↥C.S)
      K := ↥C.S
      i₁ := w
      i₂ := spMap alg
      commSq := ⟨by rw [hws, spMap_comp]; rfl⟩ }
  obtain ⟨⟨l⟩⟩ := hE S
  have hl : spMap (intO ↥C.S).subtype ≫ l.l = w := l.fac_left
  obtain ⟨y, hy⟩ := exists_ptAt Z C l.l (by rw [hl]; exact hw)
  exact ⟨y, by rw [PtAt.gen, hy, hl]⟩

theorem extendSt : ExtendSt := by
  intro E _ _ _ H Dw Xo p W Y i₀
  exact ⟨fun i k _ x hx => exists_pt_of_range i k x hx, fun Z C z hz => exists_ptAt Z C z hz,
    fun Z C w alg hw hws => exists_ptAt_gen Z C w alg hw hws⟩

end Ext

end GlobalTheory.LocM.Cht
