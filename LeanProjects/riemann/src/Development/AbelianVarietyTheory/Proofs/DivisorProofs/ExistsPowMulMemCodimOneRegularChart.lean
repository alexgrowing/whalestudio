import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem gp_comp {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (h : X ⟶ Sp R) :
    gp X ≫ h = spMap (cst h) := by
  apply ext_of_isAffine
  rw [gp, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  ext a
  have e : CommRingCat.ofHom (cst h) =
      (Scheme.ΓSpecIso _).inv ≫ h.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := rfl
  simp [e]

theorem exists_pow_mul_mem {O K : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (hd : ringKrullDim O ≤ 1) {a : O} (ha : a ∈ maximalIdeal O) (v : K) :
    ∃ N : ℕ, ∃ c : O, algebraMap O K a ^ N * v = algebraMap O K c := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := O) v
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  haveI : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hrad : a ∈ (Ideal.span {y}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hJp⟩
    have hne : J ≠ ⊥ := fun h => hy0 (by
      have := hJ (Ideal.mem_span_singleton_self y); rw [h] at this; exact (Submodule.mem_bot _).1 this)
    have : J.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot J hne
    rw [IsLocalRing.eq_maximalIdeal this]; exact ha
  obtain ⟨N, hN⟩ := hrad
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hN
  refine ⟨N, c * x, ?_⟩
  have hy' : algebraMap O K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  rw [← map_pow, ← hc, map_mul, map_mul]
  field_simp

theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {z : X} {g : X.functionField} (h : RegAt z g) (n : ℕ) :
    RegAt z (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one z).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem eq_of_specializes {X : Scheme.{0}} [IsIntegral X] {z w : X} (hd : ringKrullDim (X.presheaf.stalk z) ≤ 1)
    (hwz : w ⤳ z) (hw : w ≠ genericPoint X) : w = z := by
  by_contra hne
  have hw' : w ∈ Set.range (X.fromSpecStalk z) := by rw [Scheme.range_fromSpecStalk]; exact hwz
  obtain ⟨p, rfl⟩ := hw'
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec X).specializes trivial
  obtain ⟨q, hq⟩ := hη
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := Ring.krullDimLE_iff.2 (by exact_mod_cast hd)
  have hp : p.asIdeal = ⊥ := by
    by_contra h
    haveI := p.isPrime
    have hm := Ideal.isMaximal_of_isPrime_of_ne_bot p.asIdeal h
    have : p = closedPoint _ := PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
    apply hne; rw [this, Scheme.fromSpecStalk_closedPoint]
  have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
    show p.asIdeal ≤ q.asIdeal; rw [hp]; exact bot_le)
  have h1 : X.fromSpecStalk z p ⤳ genericPoint X := hq ▸ hpq.map (X.fromSpecStalk z).continuous
  have h2 : genericPoint X ⤳ X.fromSpecStalk z p := (genericPoint_spec X).specializes trivial
  exact hw (h1.antisymm h2).eq

theorem θ_comp_c₀ (σ : Setup) (x : Sp σ.R) :
    (σ.θ x).comp σ.c₀ = (cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl₁, hl₂⟩ := σ.hθ x
  have w := (σ.cart x).w
  simp only [Category.assoc] at w
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    calc spMap ((σ.θ x).comp σ.c₀) = spMap (σ.θ x) ≫ spMap σ.c₀ := by
          simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
      _ = l ≫ σ.φ x ≫ σ.A.hom ≫ awayMap σ.f := by
          rw [Setup.c₀, ← gp_comp, ← Category.assoc, ← hl₂]; simp only [Category.assoc]
      _ = l ≫ (σ.V x).ι ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [w]
      _ = gp _ ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) := by rw [← Category.assoc l, hl₁]
      _ = spMap ((cst (σ.C x).G.hom).comp (σ.ρ x)) := by
          rw [← Category.assoc, gp_comp]; simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have e' := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 e)
  simpa using e'

theorem zeroAt_cst {R : Type} [CommRing R] {Y : Scheme.{0}} [IsIntegral Y] (h : Y ⟶ Sp R) (r : R) (z : Y)
    (hz : r ∈ (h z).asIdeal) : ZeroAt z (cst h r) := by
  rw [zeroAt_iff]
  refine ⟨regAt_fnOf (U := ⊤) trivial trivial _, fun hu => ?_⟩
  have h1 := (unitAt_fnOf_iff (x := z) (U := ⊤) trivial (gen_mem (x := z) trivial) _).1 hu
  rw [RingHom.comp_apply, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  exact h1 hz

theorem exists_pow_mul_mem_codimOne_regular_chart : ∀ (σ : Setup) (x : Sp σ.R) (u : σ.A.left.functionField), ∃ m : ℕ, σ.c₀ σ.f ^ m * u ∈ σ.W x := by
  intro σ x u
  haveI := (σ.C x).semi
  haveI : Smooth (σ.C x).G.hom := IsSemiAbelian.smooth
  haveI : QuasiCompact (σ.C x).G.hom := IsSemiAbelian.quasiCompact
  haveI : IsLocallyNoetherian (σ.C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (σ.C x).G.hom
  haveI : CompactSpace (σ.C x).G.left := QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom
  haveI : IsNoetherian (σ.C x).G.left := {}
  haveI : TopologicalSpace.NoetherianSpace (σ.C x).G.left := IsNoetherian.noetherianSpace
  have hg : σ.θ x (σ.c₀ σ.f) = cst (σ.C x).G.hom (σ.ρ x σ.f) := RingHom.congr_fun (θ_comp_c₀ σ x) σ.f
  set g := cst (σ.C x).G.hom (σ.ρ x σ.f)
  set v := σ.θ x u
  let P : Set (σ.C x).G.left := {z | ¬ RegAt z v}
  have hP : IsClosed P := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hzU, a, ha⟩ := RegAt.exists_fnOf (not_not.1 hz)
    exact ⟨U, fun y hy => not_not.2 (ha ▸ regAt_fnOf hy _ a), U.isOpen, hzU⟩
  obtain ⟨S, hS, hirr, hPS⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_closeds_irreducible ⟨P, hP⟩
  let F : Set (σ.C x).G.left := ⋃ t ∈ S, {w | IsGenericPoint w (t : Set _)}
  have hF : F.Finite := hS.biUnion fun t _ => Set.Subsingleton.finite fun a ha b hb => ha.eq hb
  have hPt : ∀ t ∈ S, (t : Set (σ.C x).G.left) ⊆ P := fun t ht => by
    have : t ≤ sSup S := le_sSup ht
    rw [← hPS] at this
    exact this
  let C : TopologicalSpace.Closeds (σ.C x).G.left :=
    ⟨⋃ t ∈ S, (t : Set _), hS.isClosed_biUnion fun t _ => t.isClosed⟩
  have hPC : P ⊆ (C : Set _) := by
    have : sSup S ≤ C := sSup_le fun t ht y hy => Set.mem_iUnion₂.2 ⟨t, ht, hy⟩
    rw [← hPS] at this
    exact this
  have key : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → z ∈ P → z ∈ F := by
    intro z hz hzP
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 (hPC hzP)
    have hw : IsGenericPoint (hirr t ht).genericPoint (t : Set _) := by
      have := (hirr t ht).isGenericPoint_genericPoint_closure
      rwa [t.isClosed.closure_eq] at this
    have hwP : (hirr t ht).genericPoint ∈ P := hPt t ht hw.mem
    have hwη : (hirr t ht).genericPoint ≠ genericPoint _ := fun h => hwP (h ▸ regAt_genericPoint v)
    have := eq_of_specializes hz.1.le (hw.specializes hzt) hwη
    exact Set.mem_iUnion₂.2 ⟨t, ht, this ▸ hw⟩
  have hpt : ∀ z, Vert (σ.C x).G.hom (σ.ρ x σ.f) z → ∃ N : ℕ, RegAt z (g ^ N * v) := by
    intro z hz
    obtain ⟨a, ha, hag⟩ := zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2
    obtain ⟨N, c, hc⟩ := exists_pow_mul_mem hz.1.le ha v
    exact ⟨N, c, by rw [← hc, hag]⟩
  classical
  let N : (σ.C x).G.left → ℕ := fun z => if h : Vert (σ.C x).G.hom (σ.ρ x σ.f) z then Classical.choose (hpt z h) else 0
  refine ⟨hF.toFinset.sup N, fun z hz => ?_⟩
  have hgz : RegAt z g := (zeroAt_cst (σ.C x).G.hom (σ.ρ x σ.f) z hz.2).regAt
  rw [map_mul, map_pow, hg]
  by_cases hzP : z ∈ P
  · have hle : N z ≤ hF.toFinset.sup N := Finset.le_sup (hF.mem_toFinset.2 (key z hz hzP))
    have hN : RegAt z (g ^ N z * v) := by
      simp only [N, dif_pos hz]; exact Classical.choose_spec (hpt z hz)
    rw [← Nat.sub_add_cancel hle, pow_add, _root_.mul_assoc]
    exact (regAt_pow hgz _).mul hN
  · exact (regAt_pow hgz _).mul (not_not.1 hzP)

end GlobalTheory.Desc
