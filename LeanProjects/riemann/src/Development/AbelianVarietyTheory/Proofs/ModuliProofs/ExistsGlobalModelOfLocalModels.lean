import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMonoStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalModelAboveFiniteCoverStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescendsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCoverStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.GlobalModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isLocalization_away {S A : ℕ} (hS : 0 < S) (b : RZ H 1 A →+* RZ H S A)
    (hb : IsInc (RZ H 1 A).subtype (RZ H S A).subtype b) :
    @IsLocalization.Away (RZ H 1 A) _ (S : RZ H 1 A) (RZ H S A) _ b.toAlgebra := by
  letI := b.toAlgebra
  have hS' : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hS.ne'
  have hb' : ∀ x, ((b x : RZ H S A) : ℂ) = x := hb
  have key : ∀ z ∈ RZ H S A, ∃ (n : ℕ) (a : RZ H 1 A), z * (S : ℂ) ^ n = a := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, ⟨_, Subring.subset_closure (Or.inl rfl)⟩, by simp⟩
      · exact ⟨1, 1, by simp [hS']⟩
      · exact ⟨0, ⟨_, Subring.subset_closure (Or.inr (Or.inr rfl))⟩, by simp⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, c, hc⟩ := hy
      refine ⟨n + m, a * (S : RZ H 1 A) ^ m + c * (S : RZ H 1 A) ^ n, ?_⟩
      push_cast
      rw [← ha, ← hc]; ring
    | neg x _ hx =>
      obtain ⟨n, a, ha⟩ := hx
      exact ⟨n, -a, by push_cast; rw [← ha]; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, c, hc⟩ := hy
      exact ⟨n + m, a * c, by push_cast; rw [← ha, ← hc]; ring⟩
  refine IsLocalization.Away.mk _ ?_ (fun z => ?_) (fun x y h => ⟨0, ?_⟩)
  · refine IsUnit.of_mul_eq_one ⟨(S : ℂ)⁻¹, Subring.subset_closure (Or.inr (Or.inl rfl))⟩ (Subtype.ext ?_)
    simp [hS']
  · obtain ⟨n, a, ha⟩ := key z.1 z.2
    refine ⟨n, a, Subtype.ext ?_⟩
    rw [map_natCast]
    refine Eq.trans ?_ (ha.trans (hb' a).symm)
    push_cast
    rfl
  · have : x = y := Subtype.ext ((hb' x).symm.trans ((congrArg Subtype.val h).trans (hb' y)))
    rw [this]

theorem span_natCast_eq_top {R I : Type} [CommRing R] (a : I → ℕ) (h : ∀ p : ℕ, p.Prime → ∃ i, ¬ p ∣ a i) :
    Ideal.span (Set.range fun i => (a i : R)) = ⊤ := by
  set J := Ideal.span (Set.range fun i => (a i : R))
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (J.comap (Int.castRingHom R))).principal
  have hd : ∀ i, g ∣ (a i : ℤ) := fun i => by
    rw [← Ideal.mem_span_singleton]
    change _ ∈ Submodule.span ℤ {g}
    rw [← hg, Ideal.mem_comap, map_natCast]
    exact Ideal.subset_span ⟨i, rfl⟩
  have h1 : g.natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨i, hi⟩ := h p hp
    exact hi (hpg.trans (Int.natAbs_dvd_natAbs.mpr (hd i)))
  have hu : IsUnit g := Int.isUnit_iff_natAbs_eq.mpr h1
  have hm : g ∈ J.comap (Int.castRingHom R) := hg ▸ Submodule.mem_span_singleton_self g
  exact Ideal.eq_top_of_isUnit_mem _ hm (hu.map _)

theorem finite_parts (l : Level H) : Finite {l₀ : Level H // ∃ p : ℕ, p.Prime ∧ IsPrimeToPart l₀ l p} := by
  refine Finite.of_injective (fun x => (⟨x.1.M, ?_⟩ : Set.Iic l.M)) ?_
  · obtain ⟨p, -, -, h, -⟩ := x.2
    exact h ▸ Nat.div_le_self _ _
  · rintro ⟨⟨M, _, _, Mb, _, _, _, A, _⟩, p, _, h₁, _, h₃⟩ ⟨⟨M', _, _, Mb', _, _, _, A', _⟩, p', _, h₁', _, h₃'⟩ h
    obtain rfl : M = M' := congrArg Subtype.val h
    obtain rfl : A = A' := h₁.trans h₁'.symm
    obtain rfl : Mb = Mb' := h₃.trans h₃'.symm
    rfl

theorem exists_map_to_base {U U'' U₀ : Scheme.{0}} {F F'' F₀ O O'' O₀ R V : Type} [Field F] [Field F''] [Field F₀]
    [CommRing O] [CommRing O''] [CommRing O₀] [CommRing R] [CommRing V]
    {c : U ⟶ Sp F} {c'' : U'' ⟶ Sp F''} {c₀ : U₀ ⟶ Sp F₀} {t : SAB H U} {t'' : SAB H U''} {t₀ : SAB H U₀}
    {β : O →+* F} {β'' : O'' →+* F''} {β₀ : O₀ →+* F₀} {ω : R →+* F}
    {C' : Cpt c t β} {C'' : Cpt c'' t'' β''} {C₀ : Cpt c₀ t₀ β₀} {C₁ : Cpt c t ω}
    {b'' : O →+* O''} {r'' : U'' ⟶ U} {ν'' : SABMap t'' t r''} (A'' : C''.Above C' b'' r'' ν'')
    {b₀ : O₀ →+* R} {r : U ⟶ U₀} {ν : SABMap t t₀ r} (A₁ : C₁.Above C₀ b₀ r ν)
    (b₁ : O →+* R) [Mono (spMap b₁)] (hω : ω.comp b₁ = β)
    (f : pullback C'.s (spMap b₁) ⟶ C₁.X) (t₁ : SAB H (pullback C'.s (spMap b₁)))
    (m₁ : SABMap t₁ C'.t (pullback.fst _ _)) (m₂ : SABMap t₁ C₁.t f)
    (h₁ : ∀ g : U ⟶ pullback C'.s (spMap b₁), g ≫ pullback.fst _ _ = C'.j → g ≫ f = C₁.j)
    (h₂ : ∀ y : t.G.left ⟶ t₁.G.left, y ≫ m₁.φ = C'.m.φ → y ≫ m₂.φ = C₁.m.φ)
    (b : O'' →+* V) (e : R →+* V) (he : e.comp b₁ = b.comp b'') :
    ∃ (f' : pullback C''.s (spMap b) ⟶ C₀.X) (τ : SAB H (pullback C''.s (spMap b)))
      (n₁ : SABMap τ C''.t (pullback.fst _ _)) (n₂ : SABMap τ C₀.t f'),
      (∀ g : U'' ⟶ pullback C''.s (spMap b), g ≫ pullback.fst _ _ = C''.j → g ≫ f' = (r'' ≫ r) ≫ C₀.j) ∧
      ∀ y : t''.G.left ⟶ τ.G.left, y ≫ n₁.φ = C''.m.φ → y ≫ n₂.φ = (ν''.φ ≫ ν.φ) ≫ C₀.m.φ := by
  have w₀ : (pullback.fst C''.s (spMap b) ≫ A''.π) ≫ C'.s = (pullback.snd _ _ ≫ spMap e) ≫ spMap b₁ := by
    rw [Category.assoc, A''.π_over, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      ← spMap_comp, ← spMap_comp, he]
  let g₀ : pullback C''.s (spMap b) ⟶ pullback C'.s (spMap b₁) := pullback.lift _ _ w₀
  have hg₀ : g₀ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ A''.π := pullback.lift_fst _ _ _
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull (pullback.fst C''.s (spMap b)) C''.t
  obtain ⟨k₁, hk₁⟩ := LevelCover.sab_comp n₁ A''.mu rfl
  obtain ⟨k₂, hk₂⟩ := LevelCover.sab_cancel m₁ k₁ g₀ hg₀
  obtain ⟨k₃, hk₃⟩ := LevelCover.sab_comp m₂ A₁.mu rfl
  obtain ⟨n₂, hn₂⟩ := LevelCover.sab_comp k₂ k₃ rfl
  have w₁ : C'.j ≫ C'.s = (c ≫ spMap ω) ≫ spMap b₁ := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C'.jQ_over, Category.assoc, ← spMap_comp, hω]
  let g₁ : U ⟶ pullback C'.s (spMap b₁) := pullback.lift _ _ w₁
  have hg₁ : g₁ ≫ pullback.fst _ _ = C'.j := pullback.lift_fst _ _ _
  refine ⟨_, _, n₁, n₂, fun g hg => ?_, fun y hy => ?_⟩
  · have : g ≫ g₀ = r'' ≫ g₁ := by
      rw [← cancel_mono (pullback.fst C'.s (spMap b₁)), Category.assoc, hg₀, ← Category.assoc, hg, A''.j_comm,
        Category.assoc, hg₁]
    rw [← Category.assoc, this, Category.assoc, ← Category.assoc g₁, h₁ g₁ hg₁, A₁.j_comm, Category.assoc]
  · have p₁ : IsPullback m₁.φ t₁.G.hom C'.t.G.hom (pullback.fst C'.s (spMap b₁)) := m₁.cart.1
    have w₂ : C'.m.φ ≫ C'.t.G.hom = (t.G.hom ≫ g₁) ≫ pullback.fst C'.s (spMap b₁) := by
      rw [Category.assoc, hg₁]
      exact C'.m.cart.1.w
    have hy₁ : p₁.lift _ _ w₂ ≫ m₁.φ = C'.m.φ := p₁.lift_fst _ _ _
    have : Mono m₁.φ := (MorphismProperty.monomorphisms _).of_isPullback p₁.flip
      (inferInstanceAs (Mono (pullback.fst C'.s (spMap b₁))))
    have e₁ : y ≫ k₂.φ = ν''.φ ≫ p₁.lift _ _ w₂ := by
      rw [← cancel_mono m₁.φ, Category.assoc, hk₂, hk₁, ← Category.assoc, hy, A''.φ_comm, Category.assoc, hy₁]
    rw [hn₂, hk₃, ← Category.assoc, e₁, Category.assoc, ← Category.assoc _ m₂.φ, h₂ _ hy₁, A₁.φ_comm, Category.assoc]

theorem base_ring (l : Level H) (h : l.A = 1) {S : ℕ} (hS : 0 < S) :
    (∃ β : RZ H S 1 →+* KA l, IsInc (RZ H S 1).subtype (KA l).val.toRingHom β) ∧ Algebra.FiniteType ℤ (RZ H S 1) ∧
      ∀ β : RZ H S 1 →+* KA l, IsInc (RZ H S 1).subtype (KA l).val.toRingHom β → IsDedFrac β := by
  have := GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l S 0 hS (by simp [h])
  rwa [h] at this

theorem exists_global_model : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∀ S : System Xo, N6 S.Y := by
  intro hExt L₁ L₂ L₃ E _ _ _ H D Xo _ hN S l c hg hA
  let P := {l₀ : Level H // ∃ p : ℕ, p.Prime ∧ IsPrimeToPart l₀ l p}
  have : Finite P := finite_parts l
  have hP : ∀ x : P, x.1.A = 1 ∧ x.1.Dvd l := fun x => by
    obtain ⟨p, hp, h⟩ := x.2
    exact ⟨h.1, ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 l x.1 h).1⟩
  have hcop : ∀ (p : ℕ), p.Prime → ∀ l₀ : Level H, IsPrimeToPart l₀ l p → (S.n (S.ch p) * l₀.M).Coprime p :=
    fun p hp l₀ h => Nat.Coprime.mul_left ((Nat.coprime_primes (S.aux _).1 hp).mpr (S.ch_ne p))
      ((GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).2.1 l l₀ h).2.1
  have : Nonempty P := by
    obtain ⟨l₀, h⟩ := (GlobalTheory.T.primeToPart_level_exists_unique_mono E H 2 Nat.prime_two).1 l (hg 2 Nat.prime_two)
    exact ⟨⟨l₀, 2, Nat.prime_two, h⟩⟩
  let a : Bool × P → ℕ := fun i => S.n i.1 * i.2.1.M
  have ha : ∀ i, 0 < a i := fun i => Nat.mul_pos (S.aux _).1.pos (lt_of_lt_of_le (by norm_num) i.2.1.three_le)
  let B : ∀ i : Bool × P, BaseModel (S.T i.1) i.2.1 := fun i => S.B i.1 i.2.1 (hP i.2).1
  choose k r ν hr hk hlev hfin _ using fun x : P => GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN x.1 l (hP x).2
  have hnorm : Geo.Tor.IsNormalScheme (Xo l).X := by
    have := (Xo l).smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ (Xo l).s
      (SmoothOfRelativeDimension.smooth D.dim _)).2.1
  let ω : ∀ i : Bool × P, RZ H (a i) 1 →+* KA l := fun i => (k i.2).comp (B i).β
  have hω : ∀ i, IsInc (RZ H (a i) 1).subtype (KA l).val.toRingHom (ω i) := fun i x =>
    (hk i.2 _).trans ((B i).β_inc x)
  have hωd : ∀ i, IsDedFrac (ω i) := fun i => (base_ring l hA (ha i)).2.2 _ (hω i)
  choose C hC using fun i : Bool × P => GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ (B i).β _ _ _ (Xo l).s (Xo l).univ.t (ω i) (B i).C
    (RingHom.id _) (k i.2) (r i.2) (hr i.2) (ν i.2) ((base_ring i.2.1 (hP i.2).1 (ha i)).2.2 _ (B i).β_inc) (hωd i)
    rfl hnorm (hfin i.2)
  obtain ⟨⟨β₀, hβ₀⟩, hft, hd₀⟩ := base_ring l hA Nat.one_pos
  choose b₁ hb₁ using fun i : Bool × P => (GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H 1 (a i) 1 1 0 (ha i) Nat.one_pos (one_dvd _) dvd_rfl).1
  have hωb : ∀ i, (ω i).comp (b₁ i) = β₀ := fun i =>
    RingHom.ext fun x => Subtype.ext ((hω i _).trans ((hb₁ i x).trans (hβ₀ x).symm))
  obtain ⟨C', hC'⟩ := GlobalTheory.T.exists_model_dominating_models_on_open_cover hExt E H _ _ _ (Xo l).s (Xo l).univ.t β₀ (Bool × P) (fun i => RZ H (a i) 1)
    (fun i => (a i : RZ H 1 1)) b₁ ω C (hd₀ _ hβ₀) (fun i => ⟨hωd i, hωb i, isLocalization_away (ha i) _ (hb₁ i)⟩)
    (span_natCast_eq_top a fun p hp => by
      obtain ⟨l₀, h⟩ := (GlobalTheory.T.primeToPart_level_exists_unique_mono E H p hp).1 l (hg p hp)
      exact ⟨(S.ch p, ⟨l₀, p, hp, h⟩), (Nat.Prime.coprime_iff_not_dvd hp).mp (hcop p hp l₀ h).symm⟩)
    hft (Xo l).univ.proper
  obtain ⟨hdO, -, hbO, hV⟩ := GlobalTheory.T.coefficientField_integers_dedekind_fractionField E H l c
  obtain ⟨b₀, hb₀⟩ := hbO 1 (one_dvd _)
  have hb₀' : (algebraMap (𝓞 c.F) c.F).comp b₀ = (IntermediateField.inclusion c.le).toRingHom.comp β₀ :=
    RingHom.ext fun x => Subtype.ext ((hb₀ x).trans ((hβ₀ x).symm.trans
      (IntermediateField.coe_inclusion c.le (β₀ x)).symm))
  obtain ⟨oF, ⟨m0⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) (Xo l).X ((Xo l).XF c)
    (Xo l).s (pullback.fst _ _ ≫ (Xo l).s) (pullback.fst _ _) rfl rfl
    (by rw [LevelCover.spMap_id', Category.comp_id]) (Xo l).univ
  have hnormF : Geo.Tor.IsNormalScheme ((Xo l).XF c) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
      (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).2.1
  obtain ⟨C'', ⟨A''⟩⟩ := GlobalTheory.T.exists_normal_model_above_finite_cover E H _ _ _ _ _ β₀ ((Xo l).XF c) _ _ (pullback.snd _ _) oF.t
    (algebraMap (𝓞 c.F) c.F) C' b₀ (IntermediateField.inclusion c.le).toRingHom (pullback.fst _ _) pullback.condition
    m0.toSABMap (hd₀ _ hβ₀) hdO hb₀' hnormF (by rw [pullback.lift_fst_snd]; infer_instance)
  let Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F) :=
    ⟨C''.X, C''.s, C''.normal, C''.proj, C''.flat, C''.jQ, C''.jQ_over, C''.jQ_open, C''.jQ_dense, C''.t, oF, m0,
      C''.m, C''.ab_gen⟩
  refine ⟨Y, GlobalTheory.T.model_finite_over_moduliModel_descends E H D l (Xo l) c _ _ Y _ β₀ C' b₀ A'' (hd₀ _ hβ₀) hdO hb₀', fun p W hp hW b hb => ?_⟩
  obtain ⟨l₀, h, hR⟩ := S.raises p W hp hW ⟨l, c, hg p hp⟩
  let i : Bool × P := (S.ch p, ⟨l₀, p, hp, h⟩)
  obtain ⟨hdV, -, hbV⟩ := hV p W hp hW
  obtain ⟨e, he⟩ := hbV (a i) 1 (hcop p hp l₀ h) Nat.one_pos (hA ▸ c.le (baseKA l).ζ.2)
  obtain ⟨f, t₁, m₁, m₂, -, h₁, h₂⟩ := hC' i
  obtain ⟨A₁⟩ := hC i
  have := (((GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H 1 (a i) 1 1 0 (ha i) Nat.one_pos (one_dvd _) dvd_rfl).2 _ (hb₁ i)).2 rfl).1
  obtain ⟨f', τ, n₁, n₂, e₁, e₂⟩ := exists_map_to_base A'' A₁ (b₁ i) (hωb i) f t₁ m₁ m₂ h₁ h₂ b e
    (RingHom.ext fun x => Subtype.ext (Subtype.ext ((he _).trans ((hb₁ i x).trans ((hb₀ x).symm.trans
      (congrArg Subtype.val (hb _)).symm)))))
  obtain ⟨ν', hν'⟩ := LevelCover.sab_comp m0.toSABMap (ν i.2) rfl
  refine GlobalTheory.T.model_dominated_of_map_to_baseModel L₁ L₂ L₃ E H D Xo _ _ _ l₀ l (B i) c _ _ _ _ Y _ b f' τ n₁ n₂ _ ν'
    ((IntermediateField.inclusion c.le).toRingHom.comp (k i.2)) hdO hdV (RingHom.ext hb) hR ⟨fun x => ?_, fun x => ?_⟩
    (fun x => (IntermediateField.coe_inclusion c.le _).trans (hk i.2 x)) ?_ e₁ (hν' ▸ e₂)
  · rw [hν', ← Category.assoc, LevelCover.sec_pow m0.toSABMap _ _ (m0.eta x), Category.assoc, (hlev i.2).1,
      Category.assoc]
  · rw [hν', ← Category.assoc, LevelCover.sec_pow m0.toSABMap _ _ (m0.etaA x), Category.assoc, (hlev i.2).2,
      Category.assoc]
  · rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, spMap_comp]

end GlobalTheory.GlobalModel
