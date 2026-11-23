import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtaleAndSurjectiveOfDensePartMonoFiniteEtale

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.AbelianLocusCover

theorem densePart_of_isPullback {X U Y V : Scheme.{0}} {j : U ⟶ X} {p : Y ⟶ X} {j' : V ⟶ Y} {q : V ⟶ U}
    (h : IsPullback j' q p j) (hp : IsOpenMap p) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] :
    IsPreimmersion j' ∧ Flat j' ∧ IsDominant j' ∧ QuasiCompact j' := by
  refine ⟨MorphismProperty.of_isPullback (P := @IsPreimmersion) h.flip ‹_›,
    MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›, ?_,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h.flip ‹_›⟩
  have := isDominant_pullback_fst_of_isOpenMap j p hp
  rw [← h.isoPullback_hom_fst]
  infer_instance

theorem mono_of_points {X S₀ S Z : Scheme.{0}} (i : X ⟶ Z) (p : Z ⟶ S) (e : X ⟶ S₀) (j : S₀ ⟶ S) [Mono j] [Etale e]
    (w : i ≫ p = e ≫ j) (h : ∀ (k : Type) [Field k] (y y' : Sp k ⟶ X), y ≫ i = y' ≫ i → y = y') : Mono i := by
  let i₀ : X ⟶ pullback p j := pullback.lift i e w
  have h₁ : i₀ ≫ pullback.fst p j = i := pullback.lift_fst _ _ _
  have h₂ : i₀ ≫ pullback.snd p j = e := pullback.lift_snd _ _ _
  have : FormallyUnramified (i₀ ≫ pullback.snd p j) := by rw [h₂]; infer_instance
  have : LocallyOfFiniteType (i₀ ≫ pullback.snd p j) := by rw [h₂]; infer_instance
  have : FormallyUnramified i₀ := FormallyUnramified.of_comp i₀ (pullback.snd p j)
  have : LocallyOfFiniteType i₀ := locallyOfFiniteType_of_comp i₀ (pullback.snd p j)
  have hs : Surjective (pullback.diagonal i₀) :=
    ((tfae_universallyInjective i₀).out 1 3).1 fun (k : Type) [Field k] y y' (e' : y ≫ i₀ = y' ≫ i₀) =>
      h k y y' (by rw [← h₁, ← Category.assoc, e', Category.assoc])
  have : IsIso (pullback.diagonal i₀) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  have : Mono i₀ := (pullback.isIso_diagonal_iff i₀).1 this
  rw [← h₁]
  infer_instance

theorem isPullback_fraction {O O₁ F F₁ : Type} [CommRing O] [CommRing O₁] [Field F] [Field F₁]
    [Algebra O F] [IsFractionRing O F] [Algebra O₁ F₁] [IsFractionRing O₁ F₁] (b : O →+* O₁) (k : F →+* F₁)
    (h : (algebraMap O₁ F₁).comp b = k.comp (algebraMap O F))
    (hd : ∀ x : F₁, ∃ (y : O₁) (z : O), z ≠ 0 ∧ x * algebraMap O₁ F₁ (b z) = algebraMap O₁ F₁ y) :
    IsPullback (spMap (algebraMap O₁ F₁)) (spMap k) (spMap b) (spMap (algebraMap O F)) := by
  have : IsDomain O := (IsFractionRing.injective O F).isDomain _
  have h2 : IsLocalization ((nonZeroDivisors O).map b) F₁ := by
    refine ⟨⟨?_, fun x => ?_, fun {x y} hxy => ⟨1, by rw [IsFractionRing.injective O₁ F₁ hxy]⟩⟩⟩
    · rintro ⟨_, z, hz, rfl⟩
      refine IsUnit.mk0 _ ?_
      have e : algebraMap O₁ F₁ (b z) = k (algebraMap O F z) := congrArg (fun f => f z) h
      show algebraMap O₁ F₁ (b z) ≠ 0
      rw [e, map_ne_zero]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
    · obtain ⟨y, z, hz, e⟩ := hd x
      exact ⟨⟨y, ⟨b z, z, mem_nonZeroDivisors_of_ne_zero hz, rfl⟩⟩, e⟩
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization b k h.symm (nonZeroDivisors O))

theorem exists_torsion_cover {X S T : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (G' : Over T) [GrpObj G'] (f : S ⟶ X) (q : T ⟶ S) (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G (q ≫ f) φ)
    (hp : IsProper (pullback.snd G.hom f)) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (σ : La → (𝟙_ (Over T) ⟶ G'))
    (hσ : ∀ a c, σ (a + c) = σ a * σ c) (hσn : ∀ a, σ a ^ n = 1) :
    ∃ (Z : Scheme.{0}) (p : Z ⟶ S) (i : T ⟶ Z), IsFinite p ∧ Etale p ∧ i ≫ p = q ∧
      ∀ (W : Scheme.{0}) (y y' : W ⟶ T), y ≫ i = y' ≫ i → ∀ a, y ≫ (σ a).left ≫ φ = y' ≫ (σ a).left ≫ φ := by
  have hS := IsSemiAbelian.pullback f G hG
  have := hS.comm
  have hA : IsAbelianScheme ((Over.pullback f).obj G) := ⟨hS.comm, hS.smooth, hp, hS.geomConnected⟩
  obtain ⟨Z, et, h₁, h₂, -, -, hu⟩ := exists_finiteEtale_latticeTorsionHom S _ n La hA hn
  have g := isGrpPullback_pullback G f
  let φ' : G'.left ⟶ ((Over.pullback f).obj G).left := g.1.lift φ (G'.hom ≫ q) (by rw [h.1.w, Category.assoc])
  have e₁ : φ' ≫ pullback.fst G.hom f = φ := g.1.lift_fst _ _ _
  have g' : IsGrpPullback G' ((Over.pullback f).obj G) q φ' :=
    g.cancel (by rw [e₁]; exact h) (g.1.lift_snd _ _ _)
  obtain ⟨i, hi, -⟩ := hu _ (fun a => pushHom g' _ (σ a)) (fun a c => by rw [hσ, map_mul])
    (fun a => by rw [← map_pow, hσn, map_one])
  refine ⟨Z.left, Z.hom, i.left, h₁, h₂, (Over.w i).trans (Category.id_comp q), fun W y y' e a => ?_⟩
  have e₂ : i.left ≫ (et a).left = (σ a).left ≫ φ' := congrArg (fun z => z.left) (hi a)
  rw [← e₁, ← Category.assoc (σ a).left, ← e₂]
  simp only [← Category.assoc]
  rw [e]

theorem eq_of_pow_eq_of_coprime {M : Type} [Group M] {x y : M} {m n : ℕ} (h : m.Coprime n) (hm : x ^ m = y ^ m)
    (hn : x ^ n = y ^ n) : x = y := by
  have key : ∀ z : M, z = (z ^ m) ^ (m.gcdA n) * (z ^ n) ^ (m.gcdB n) := fun z => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← Nat.gcd_eq_gcd_ab, h.gcd_eq_one]
    simp
  rw [key x, hm, hn, ← key y]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem sec_of_coprime {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (x : 𝟙_ (Over S') ⟶ t'.G) (y : 𝟙_ (Over S) ⟶ t.G) {k k' : ℕ} (hk : k.Coprime k')
    (h : (x ^ k).left ≫ m.φ = f ≫ (y ^ k).left) (h' : (x ^ k').left ≫ m.φ = f ≫ (y ^ k').left) :
    x.left ≫ m.φ = f ≫ y.left := by
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
    Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e : pushHom m.cart _ (x ^ k) = preHom U (y ^ k) := Over.OverMorphism.ext h
  have e' : pushHom m.cart _ (x ^ k') = preHom U (y ^ k') := Over.OverMorphism.ext h'
  rw [map_pow, map_pow] at e e'
  exact congrArg (fun z => z.left) (eq_of_pow_eq_of_coprime hk e e')

theorem points_eq {l : Level H} (Xo : Moduli D l) (c : Coeff l)
    (o : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))
    (m0 : ObjMap o Xo.univ (pullback.fst _ _)) {X T : Scheme.{0}} [IsReduced T] {t : SAB H X} {f : Xo.XF c ⟶ X}
    (ν : SABMap o.t t f) (y y' : T ⟶ Xo.XF c) (e : y ≫ f = y' ≫ f)
    (e₂ : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _) {k k' : ℕ} (hk : k.Coprime k')
    (h₀ : ∀ a, y ≫ (o.eta a).left ≫ ν.φ = y' ≫ (o.eta a).left ≫ ν.φ)
    (h₁ : ∀ a, y ≫ (o.etaA a ^ k).left ≫ ν.φ = y' ≫ (o.etaA a ^ k).left ≫ ν.φ)
    (h₂ : ∀ a, y ≫ (o.etaA a ^ k').left ≫ ν.φ = y' ≫ (o.etaA a ^ k').left ≫ ν.φ) : y = y' := by
  obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ T _
    ((y ≫ pullback.fst _ _) ≫ Xo.s) y rfl rfl
    ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).symm.trans
      (congrArg (((y ≫ pullback.fst _ _) ≫ Xo.s) ≫ ·) (Spec.map_id _).symm))) o
  obtain ⟨n, hn⟩ := LevelCover.sab_comp m.toSABMap ν rfl
  obtain ⟨m', hm'⟩ := LevelCover.sab_cancel ν n y' e.symm
  have key : ∀ (x : 𝟙_ (Over T) ⟶ o'.t.G) (z : 𝟙_ (Over (Xo.XF c)) ⟶ o.t.G),
      x.left ≫ m.toSABMap.φ = y ≫ z.left → y ≫ z.left ≫ ν.φ = y' ≫ z.left ≫ ν.φ →
      x.left ≫ m'.φ = y' ≫ z.left := fun x z hx hz =>
    LevelCover.sec_cancel m' ν x z (by rw [hm', hn, ← Category.assoc, hx, Category.assoc, hz])
  have a₁ : ∀ a, (o'.eta a).left ≫ m'.φ = y' ≫ (o.eta a).left := fun a => key _ _ (m.eta a) (h₀ a)
  have a₂ : ∀ a, (o'.etaA a).left ≫ m'.φ = y' ≫ (o.etaA a).left := fun a =>
    sec_of_coprime m' _ _ hk (key _ _ (LevelCover.sec_pow m.toSABMap _ _ (m.etaA a) k) (h₁ a))
      (key _ _ (LevelCover.sec_pow m.toSABMap _ _ (m.etaA a) k') (h₂ a))
  have comp : ∀ (g : T ⟶ Xo.XF c), ObjMap o' o g → Nonempty (ObjMap o' Xo.univ (g ≫ pullback.fst _ _)) := by
    intro g u
    obtain ⟨v, hv⟩ := LevelCover.sab_comp u.toSABMap m0.toSABMap rfl
    refine ⟨⟨v, fun a => ?_, fun a => ?_⟩⟩
    · show _ ≫ v.φ = _
      rw [hv, ← Category.assoc, u.eta a, Category.assoc, m0.eta a, Category.assoc]
    · show _ ≫ v.φ = _
      rw [hv, ← Category.assoc, u.etaA a, Category.assoc, m0.etaA a, Category.assoc]
  refine pullback.hom_ext ?_ e₂
  refine (Xo.rep _ _ inferInstance o').unique ⟨rfl, comp y m⟩ ⟨?_, comp y' ⟨m', a₁, a₂⟩⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← e₂, Category.assoc]

theorem levelMap_etale (hL : Out.Laws) (hL₂ : Out.Laws2) (hL₃ : Out.Laws3) (Xo : ∀ l : Level H, Moduli D l)
    (hN : ToroidalLevelCompatibility (H := H) (D := D)) {l l₁ : Level H} (hd : l.Dvd l₁) (c : Coeff l) (c₁ : Coeff l₁) (hc : c.F ≤ c₁.F)
    (o : Obj D l (baseKA l)
      (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s))
    (m0 : ObjMap o (Xo l).univ (pullback.fst _ _))
    (o₁ : Obj D l₁ (baseKA l₁)
      (pullback.fst (Xo l₁).s (spMap (IntermediateField.inclusion c₁.le).toRingHom) ≫ (Xo l₁).s))
    (m₁ : ObjMap o₁ (Xo l₁).univ (pullback.fst _ _)) [IsReduced ((Xo l₁).XF c₁)]
    (r : (Xo l₁).XF c₁ ⟶ (Xo l).XF c) (ν : SABMap o₁.t o.t r) (hν : LevComp o₁ o r ν)
    (hr : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc).toRingHom) :
    Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) := by
  obtain ⟨k, r', ν', hr', hk, hν', -, het, hsur⟩ :=
    LevelMapField.exists_levelMap hL hL₂ hL₃ E H D Xo hN l l₁ c₁ o₁ m₁ hd
  have ek : k = (IntermediateField.inclusion hc).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom :=
    RingHom.ext fun x => Subtype.ext (hk x)
  subst ek
  obtain ⟨v, hv⟩ := LevelCover.sab_comp ν m0.toSABMap rfl
  have hr'' : (r ≫ pullback.fst _ _) ≫ (Xo l).s = r' ≫ (Xo l).s := by
    rw [hr', Category.assoc, pullback.condition, ← Category.assoc, hr, spMap_comp, Category.assoc]
  have e : r ≫ pullback.fst _ _ = r' :=
    (LevUniq.map_to_univ_unique hL hL₂ hL₃ E H D l l₁ (Xo l) _ _ _ _ o₁ _ _ v ν' inferInstance hr''
      ⟨fun a => by rw [hv, ← Category.assoc, hν.1 a, Category.assoc, m0.eta a, Category.assoc],
        fun a => by rw [hv, ← Category.assoc, hν.2 a, Category.assoc, m0.etaA a, Category.assoc]⟩ hν').1
  have P := (IsPullback.of_hasPullback (pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (spMap (IntermediateField.inclusion hc).toRingHom)).paste_horiz (IsPullback.of_hasPullback _ _)
  rw [← spMap_comp] at P
  have e' : pullback.lift r _ hr = pullback.lift r' _ hr' ≫ P.isoPullback.inv := by
    rw [Iso.eq_comp_inv]
    apply pullback.hom_ext
    · rw [Category.assoc, P.isoPullback_hom_fst, pullback.lift_fst, pullback.lift_fst_assoc, e]
    · rw [Category.assoc, P.isoPullback_hom_snd, pullback.lift_snd, pullback.lift_snd]
  rw [e']
  exact ⟨inferInstance, inferInstance⟩

theorem exists_densePart {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (hβ : IsDedFrac β) (U : Y.X.Opens) (hU : (U : Set Y.X) = abLocus Y.t.G) :
    IsLocallyNoetherian Y.X ∧ Mono (spMap β) ∧ Mono Y.j ∧ ∃ j : Xo.XF c ⟶ U.toScheme, j ≫ U.ι = Y.j ∧
      IsPreimmersion j ∧ Flat j ∧ IsDominant j ∧ QuasiCompact j := by
  obtain ⟨⟨_, _⟩, -, hf⟩ := hβ
  letI := β.toAlgebra
  obtain ⟨h₁, -, -, h₂, h₃, h₄, h₅⟩ :=
    genericPart_dense_proOpen O c.F Y.X _ Y.s Y.jQ Y.flat Y.proj Y.jQ_open Y.jQ_dense
  have h₂ : IsPreimmersion Y.j := h₂
  have h₃ : Flat Y.j := h₃
  have h₄ : IsDominant Y.j := h₄
  have h₅ : QuasiCompact Y.j := h₅
  have hb : IsPreimmersion (spMap β) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := c.F) (nonZeroDivisors O)
  have hr : Set.range Y.j ⊆ Set.range U.ι := by
    rintro _ ⟨p, rfl⟩
    have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι, hU]
    exact hz
  have e := IsOpenImmersion.lift_fac U.ι Y.j hr
  have P : IsPullback (IsOpenImmersion.lift U.ι Y.j hr) (𝟙 _) U.ι Y.j :=
    IsPullback.of_vert_isIso_mono ⟨e.trans (Category.id_comp _).symm⟩
  exact ⟨h₁, inferInstance, inferInstance, _, e, densePart_of_isPullback P U.ι.isOpenEmbedding.isOpenMap⟩

theorem abelianLocus_finite_etale : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β) (l₁ : Level H) (c₁ : Coeff l₁) (O₁ : Type) [CommRing O₁] (β₁ : O₁ →+* c₁.F) (Y₁ : Model (Xo l₁) c₁ β₁) (b : O →+* O₁) (π : Y₁.X ⟶ Y.X) (N : ℕ), IsDedFrac β → IsDedFrac β₁ → IsInc (c.F.val.toRingHom.comp β) (c₁.F.val.toRingHom.comp β₁) b → Etale (spMap b) → (∃ n e : ℕ, n.Prime ∧ IsUnit (n : O) ∧ N = n ^ e) → l₁.M = l.M → l₁.Mb = l.Mb → l₁.A = Nat.lcm l.A N → c.F ≤ c₁.F → (∀ x : c₁.F, ∃ (y : O₁) (z : O), z ≠ 0 ∧ x * β₁ (b z) = β₁ y) → AbOpen Y.t.G → IsTransition Y Y₁ b π → ∀ (U : Y.X.Opens) (U₁ : Y₁.X.Opens), (U : Set Y.X) = abLocus Y.t.G → (U₁ : Set Y₁.X) = abLocus Y₁.t.G → ∃ e : U₁.toScheme ⟶ pullback (U.ι ≫ Y.s) (spMap b), e ≫ pullback.fst _ _ ≫ U.ι = U₁.ι ≫ π ∧ e ≫ pullback.snd _ _ = U₁.ι ≫ Y₁.s ∧ IsFinite e ∧ Etale e ∧ Surjective e := by
  intro hL hL₂ hL₃ E _ _ _ H D Xo hN l c O _ β Y l₁ c₁ O₁ _ β₁ Y₁ b π N hβ hβ₁ hinc het ⟨n, ε, hn, hu, hNe⟩ hM hMb hA
    hc hden ⟨U', hU', hpr⟩ ⟨π', mu, r, hπ₁, hπ₂, hfin, hj, hl₁, hl₂⟩ U U₁ hU hU₁
  obtain rfl : U' = U := SetLike.coe_injective (hU'.trans hU.symm)
  obtain ⟨nY, mβ, mj, jU, ejU, _, _, _, _⟩ := exists_densePart Y hβ U' hU
  obtain ⟨nY₁, mβ₁, -, jU₁, ejU₁, p₁, p₂, p₃, p₄⟩ := exists_densePart Y₁ hβ₁ U₁ hU₁
  have hUU : π ⁻¹ᵁ U' = U₁ := by
    ext x
    rw [hU₁]
    refine Iff.trans ?_ (abLocus_pullback abLocusOne Y.t.semi mu.cart.1 x)
    rw [← hU]
    exact Iff.rfl
  subst hUU
  have := IsNormalScheme.of_pred Y.normal
  have := IsNormalScheme.of_pred Y₁.normal

  let inc : c.F →+* c₁.F := (IntermediateField.inclusion hc).toRingHom
  have hinc' : β₁.comp b = inc.comp β := RingHom.ext fun x => Subtype.ext (hinc x)
  have hinc'' : spMap β₁ ≫ spMap b = spMap inc ≫ spMap β := by rw [← spMap_comp, ← spMap_comp, hinc']
  have R : IsPullback (spMap β₁) (spMap inc) (spMap b) (spMap β) := by
    letI := β.toAlgebra
    letI := β₁.toAlgebra
    have := hβ.2.2
    have := hβ₁.2.2
    exact isPullback_fraction b inc hinc' hden
  have hs : π ≫ Y.s = Y₁.s ≫ spMap b := by
    rw [← hπ₁, ← hπ₂, Category.assoc, Category.assoc, pullback.condition]
  have hr : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap inc := by
    rw [← cancel_mono (spMap β), Category.assoc, ← Y.j_s, ← Category.assoc, ← hj, Category.assoc, hs,
      ← Category.assoc, Y₁.j_s, Category.assoc, Category.assoc, hinc'']

  have w : (π ∣_ U') ≫ U'.ι ≫ Y.s = ((π ⁻¹ᵁ U').ι ≫ Y₁.s) ≫ spMap b := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hs, Category.assoc]
  let e : (π ⁻¹ᵁ U').toScheme ⟶ pullback (U'.ι ≫ Y.s) (spMap b) := pullback.lift _ _ w
  have e₁ : e ≫ pullback.fst _ _ = π ∣_ U' := pullback.lift_fst _ _ _
  have e₂ : e ≫ pullback.snd _ _ = (π ⁻¹ᵁ U').ι ≫ Y₁.s := pullback.lift_snd _ _ _
  have hef : IsFinite e := by
    let κ : pullback (U'.ι ≫ Y.s) (spMap b) ⟶ pullback Y.s (spMap b) :=
      pullback.lift (pullback.fst _ _ ≫ U'.ι) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
    have k₁ : κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ U'.ι := pullback.lift_fst _ _ _
    have k₂ : κ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
    have Q : IsPullback (pullback.fst (U'.ι ≫ Y.s) (spMap b)) κ U'.ι (pullback.fst Y.s (spMap b)) :=
      IsPullback.of_bot (by rw [k₂]; exact IsPullback.of_hasPullback _ _) k₁.symm (IsPullback.of_hasPullback _ _)
    have Q' : IsPullback e (π ⁻¹ᵁ U').ι κ π' := by
      refine IsPullback.of_right (by rw [e₁, hπ₁]; exact isPullback_morphismRestrict π U') ?_ Q
      apply pullback.hom_ext
      · rw [Category.assoc, k₁, ← Category.assoc, e₁, Category.assoc, hπ₁, morphismRestrict_ι]
      · rw [Category.assoc, k₂, e₂, Category.assoc, hπ₂]
    exact MorphismProperty.of_isPullback Q'.flip hfin
  refine ⟨e, by rw [← Category.assoc, e₁, morphismRestrict_ι], e₂, hef, ?_⟩

  have hjs : jU ≫ U'.ι ≫ Y.s = pullback.snd _ _ ≫ spMap β := by rw [← Category.assoc, ejU, Y.j_s]
  let sF := pullback.snd (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let j : pullback sF (spMap inc) ⟶ pullback (U'.ι ≫ Y.s) (spMap b) :=
    pullback.lift (pullback.fst _ _ ≫ jU) (pullback.snd _ _ ≫ spMap β₁)
      (by rw [Category.assoc, hjs, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hinc''])
  have j₁ : j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ jU := pullback.lift_fst _ _ _
  have j₂ : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap β₁ := pullback.lift_snd _ _ _
  have J : IsPullback j (pullback.fst sF (spMap inc)) (pullback.fst (U'.ι ≫ Y.s) (spMap b)) jU :=
    IsPullback.of_right (by rw [j₂, hjs]; exact (IsPullback.of_hasPullback sF (spMap inc)).flip.paste_horiz R) j₁
      (IsPullback.of_hasPullback _ _).flip
  obtain ⟨q₁, q₂, q₃, q₄⟩ := densePart_of_isPullback J (pullback.fst (U'.ι ≫ Y.s) (spMap b)).isOpenMap
  have := isNormalScheme_of_smooth (pullback.fst (U'.ι ≫ Y.s) (spMap b))
  have : IsLocallyNoetherian (pullback (U'.ι ≫ Y.s) (spMap b)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (U'.ι ≫ Y.s) (spMap b))

  obtain ⟨mm, hmm⟩ := LevelCover.sab_comp Y₁.m mu hj
  obtain ⟨ν, hν⟩ := LevelCover.sab_cancel Y.m mm r rfl
  have lev : LevComp Y₁.oF Y.oF r ν :=
    ⟨fun a => LevelCover.sec_cancel ν Y.m _ _ (by rw [hν, hmm]; exact hl₁ a),
      fun a => LevelCover.sec_cancel ν Y.m _ _ (by rw [hν, hmm]; exact hl₂ a)⟩
  have : IsReduced ((Xo l₁).XF c₁) := by
    have := isIso_stalkMap_of_flat_of_surjectiveOnStalks jU₁
    have := IsNormalScheme.of_isIso_stalkMap jU₁
    exact IsNormalScheme.isReduced
  obtain ⟨t₁, t₂⟩ := levelMap_etale hL hL₂ hL₃ Xo hN ⟨by rw [hM], hMb.le, by rw [hA]; exact Nat.dvd_lcm_left _ _⟩
    c c₁ hc Y.oF Y.m0 Y₁.oF Y₁.m0 r ν lev hr
  let e₀ : (Xo l₁).XF c₁ ⟶ pullback sF (spMap inc) := pullback.lift r _ hr
  have f₁ : e₀ ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  have f₂ : e₀ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hsq : jU₁ ≫ e = e₀ ≫ j := by
    apply pullback.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, j₁, ← Category.assoc, f₁, ← cancel_mono U'.ι, Category.assoc,
        morphismRestrict_ι, ← Category.assoc, ejU₁, hj, Category.assoc, ejU]
    · rw [Category.assoc, e₂, Category.assoc, j₂, ← Category.assoc, ejU₁, Y₁.j_s, ← Category.assoc, f₂]

  obtain ⟨v, A', hA', hAv⟩ := Nat.exists_eq_pow_mul_and_not_dvd l₁.A_pos.ne' n hn.ne_one
  have hco : A'.Coprime (l₁.A / l.A) := by
    have hd : l₁.A / l.A ∣ n ^ ε := by
      rw [← hNe, hA]
      refine Nat.dvd_of_mul_dvd_mul_left l.A_pos ?_
      rw [Nat.mul_div_cancel' (Nat.dvd_lcm_left _ _)]
      exact Nat.lcm_dvd_mul _ _
    exact (((Nat.Prime.coprime_iff_not_dvd hn).2 hA').symm.pow_right ε).coprime_dvd_right hd
  have hpow : ∀ (k : ℕ) a, Y₁.oF.etaA (k • a) = Y₁.oF.etaA a ^ k := by
    intro k a
    induction k with
    | zero =>
      have h0 := Y₁.oF.etaA_ker 0
      rw [smul_zero] at h0
      rw [zero_smul, pow_zero, h0]
    | succ k ih => rw [succ_nsmul, Y₁.oF.etaA_add, ih, pow_succ]
  have := D.fin
  have := D.proj
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have hbase : (e₀ ≫ j) ≫ pullback.fst _ _ ≫ U'.ι = r ≫ Y.j := by
    rw [Category.assoc, ← Category.assoc j, j₁, Category.assoc, ejU, ← Category.assoc, f₁]
  have hprop : IsProper (pullback.snd Y.t.G.hom (pullback.fst (U'.ι ≫ Y.s) (spMap b) ≫ U'.ι)) := by
    have hp := (IsPullback.of_hasPullback (Y.t.G.hom ∣_ U') (pullback.fst (U'.ι ≫ Y.s) (spMap b))).paste_horiz
      (isPullback_morphismRestrict Y.t.G.hom U').flip
    rw [← hp.isoPullback_inv_snd]
    infer_instance
  have hunit : IsUnit ((n ^ v : ℕ) : Γ(pullback (U'.ι ≫ Y.s) (spMap b), ⊤)) := by
    have h := (hu.pow v).map ((pullback.snd (U'.ι ≫ Y.s) (spMap b) ≫ spMap b).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)
    rwa [← Nat.cast_pow, map_natCast] at h
  obtain ⟨Z, p, i, z₁, z₂, z₃, z₄⟩ := exists_torsion_cover Y.t.G Y.t.semi Y₁.oF.t.G
    (pullback.fst (U'.ι ≫ Y.s) (spMap b) ≫ U'.ι) (e₀ ≫ j) mm.φ (by rw [hbase]; exact mm.cart) hprop (n ^ v) hunit
    D.La (fun a => Y₁.oF.etaA (A' • a)) (fun a a' => by rw [smul_add, Y₁.oF.etaA_add])
    (fun a => by rw [← hpow, smul_smul, ← hAv, Y₁.oF.etaA_ker])
  have hi : Mono i := by
    refine mono_of_points i p e₀ j z₃ fun k _ y y' hy => ?_
    have h₀ : y ≫ e₀ = y' ≫ e₀ := by
      rw [← cancel_mono j, Category.assoc, Category.assoc, ← z₃, ← Category.assoc, hy, Category.assoc]
    have h₁ : y ≫ r = y' ≫ r := by rw [← f₁, ← Category.assoc, h₀, Category.assoc]
    refine points_eq (Xo l₁) c₁ Y₁.oF Y₁.m0 mm y y' (by rw [← Category.assoc, h₁, Category.assoc])
      (by rw [← f₂, ← Category.assoc, h₀, Category.assoc]) hco (fun a => ?_) (fun a => ?_) (fun a => ?_)
    · have h := hl₁ a
      rw [hM, Nat.div_self (lt_of_lt_of_le (by norm_num) l.three_le), pow_one] at h
      rw [hmm, h, ← Category.assoc, h₁, Category.assoc]
    · rw [← hpow]
      exact z₄ _ y y' hy a
    · rw [hmm, hl₂ a, ← Category.assoc, h₁, Category.assoc]
  exact GlobalTheory.etale_and_surjective_of_densePart_mono_finiteEtale _ _ _ _ Z j jU₁ e e₀ p i (IsNormalScheme.pred _) (IsNormalScheme.pred _) q₁ q₂ q₃ q₄
    p₁ p₂ p₃ p₄ hef hsq z₁ z₂ z₃ t₂ t₁ hi

end GlobalTheory.AbelianLocusCover
