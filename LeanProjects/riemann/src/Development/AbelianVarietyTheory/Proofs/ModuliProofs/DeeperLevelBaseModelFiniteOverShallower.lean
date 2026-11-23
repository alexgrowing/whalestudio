import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescOfIsFiniteOfDensePartStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleMapExtendingModelMapStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleSurjectiveLevelMapStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbedStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.BaseTransition

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem isProper_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem isReduced_of_normal {X : Scheme.{0}} (h : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

section

variable {U : Scheme.{0}} {F : Type} [Field F] {c : U ⟶ Sp F} {t : SAB H U} {O : Type} [CommRing O] {β : O →+* F}

theorem j_s (C : Cpt c t β) : C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

theorem dense_part (C : Cpt c t β) (h : IsDedFrac β) :
    IsLocallyNoetherian C.X ∧ IsPreimmersion C.j ∧ Flat C.j ∧ IsDominant C.j ∧ QuasiCompact C.j := by
  obtain ⟨⟨_, _⟩, _, h₃⟩ := h
  letI := β.toAlgebra
  obtain ⟨a, -, -, b⟩ := GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  exact ⟨a, b⟩

theorem isReduced_open (C : Cpt c t β) (h : IsDedFrac β) : IsReduced U := by
  obtain ⟨-, a, b, d, e⟩ := dense_part C h
  have hs := (GlobalTheory.densePart_basic _ _ C.j a b d e).2.1
  have : ∀ x : U, _root_.IsReduced (U.presheaf.stalk x) := fun x => by
    have := (C.normal (C.j x)).1
    have := hs x
    have e := (asIso (C.j.stalkMap x)).commRingCatIsoToRingEquiv
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  exact isReduced_of_isReduced_stalk U

theorem mono_spMap (h : IsDedFrac β) : Mono (spMap β) := by
  obtain ⟨-, -, h₃⟩ := h
  letI := β.toAlgebra
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O) (R := O) (S := F)
  infer_instance

end

theorem ded (l : Level H) (S e A : ℕ) (hA : l.A = A) (hS : 0 < S) (hd : A ∣ S ^ e) :
    Algebra.FiniteType ℤ (RZ H S A) ∧
      ∀ β : RZ H S A →+* KA l, IsInc (RZ H S A).subtype (KA l).val.toRingHom β → IsDedFrac β := by
  subst hA
  exact (GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding E H l S e hS hd).2

theorem finite_fibres_of_comp {X Y Z : Type} {f : X → Y} {g : Y → Z}
    (h : ∀ z, ((g ∘ f) ⁻¹' {z}).Finite) (y : Y) : (f ⁻¹' {y}).Finite :=
  (h (g y)).subset fun x hx => by simp_all

theorem finite_fibres_comp {X Y Z : Type} {f : X → Y} {g : Y → Z}
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hg : ∀ z, (g ⁻¹' {z}).Finite) (z : Z) : ((g ∘ f) ⁻¹' {z}).Finite := by
  rw [Set.preimage_comp]
  exact (hg z).preimage' fun y _ => hf y

theorem finite_fibres_of_surj {X Y Z : Type} {f : X → Y} {g : Y → Z} (hf : Function.Surjective f)
    (h : ∀ z, ((g ∘ f) ⁻¹' {z}).Finite) (z : Z) : (g ⁻¹' {z}).Finite :=
  ((h z).image f).subset fun y hy => by
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨x, hy, rfl⟩

theorem levComp_comp {D : Datum H} {l l' l'' : Level H} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    {b : Base l B} {b' : Base l' B'} {b'' : Base l'' B''} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'}
    {s'' : S'' ⟶ Sp B''} {o : Obj D l b s} {o' : Obj D l' b' s'} {o'' : Obj D l'' b'' s''} {r : S' ⟶ S}
    {r' : S'' ⟶ S'} {ν : SABMap o'.t o.t r} {ν' : SABMap o''.t o'.t r'} (hd : l.Dvd l') (hd' : l'.Dvd l'')
    (h : LevComp o' o r ν) (h' : LevComp o'' o' r' ν') :
    ∃ mu : SABMap o''.t o.t (r' ≫ r), LevComp o'' o (r' ≫ r) mu := by
  obtain ⟨mu, hmu⟩ := LevelCover.sab_comp ν' ν rfl
  have key : ∀ {a a' a'' : ℕ}, 0 < a' → a ∣ a' → a' ∣ a'' → a'' / a = a'' / a' * (a' / a) := by
    rintro a _ _ h0 ⟨u, rfl⟩ ⟨v, rfl⟩
    have ha : 0 < a := Nat.pos_of_mul_pos_right h0 |>.trans_le' le_rfl
    rw [Nat.mul_div_cancel_left _ h0, Nat.mul_div_cancel_left _ ha, Nat.mul_assoc, Nat.mul_div_cancel_left _ ha,
      Nat.mul_comm]
  refine ⟨mu, fun a => ?_, fun a => ?_⟩
  · rw [hmu, key (lt_of_lt_of_le (by norm_num) l'.three_le) hd.1 hd'.1, pow_mul, ← Category.assoc,
      LevelCover.sec_pow ν' _ _ (h'.1 a), Category.assoc, h.1, Category.assoc]
  · rw [hmu, key l'.A_pos hd.2.2 hd'.2.2, pow_mul, ← Category.assoc,
      LevelCover.sec_pow ν' _ _ (h'.2 a), Category.assoc, h.2, Category.assoc]

theorem fib_of_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {e : X ⟶ Z} (he : f ≫ g = e)
    (h : ∀ z, (e ⁻¹' {z}).Finite) (y : Y) : (f ⁻¹' {y}).Finite := by
  subst he
  refine finite_fibres_of_comp (f := f) (g := g) (fun z => (h z).subset fun x hx => ?_) y
  simpa using hx

theorem fib_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : ∀ y, (f ⁻¹' {y}).Finite)
    (hg : ∀ z, (g ⁻¹' {z}).Finite) (z : Z) : ((f ≫ g) ⁻¹' {z}).Finite := by
  refine (finite_fibres_comp (f := f) (g := g) hf hg z).subset fun x hx => ?_
  simpa using hx

theorem fib_of_surj {X Y Z : Scheme.{0}} (f : X ⟶ Y) [Surjective f] (g : Y ⟶ Z) {e : X ⟶ Z} (he : f ≫ g = e)
    (h : ∀ z, (e ⁻¹' {z}).Finite) (z : Z) : (g ⁻¹' {z}).Finite := by
  subst he
  refine finite_fibres_of_surj (f := f) (g := g) f.surjective (fun z => (h z).subset fun x hx => ?_) z
  simpa using hx

theorem isFinite_lift {X Y S S' : Scheme.{0}} (f : X ⟶ Y) (s' : X ⟶ S') (s : Y ⟶ S) (b : S' ⟶ S)
    (w : f ≫ s = s' ≫ b) [IsProper s] [IsProper s'] (h : ∀ y, (f ⁻¹' {y}).Finite) :
    IsFinite (pullback.lift f s' w) := by
  have e₁ : pullback.lift f s' w ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have e₂ : pullback.lift f s' w ≫ pullback.snd _ _ = s' := pullback.lift_snd _ _ _
  have : IsProper (pullback.lift f s' w ≫ pullback.snd _ _) := by rw [e₂]; infer_instance
  have : IsProper (pullback.lift f s' w) := IsProper.of_comp _ (pullback.snd s b)
  have : LocallyQuasiFinite (pullback.lift f s' w) := by
    exact .of_finite_preimage_singleton _ (fib_of_comp _ _ e₁ h)
  exact .of_isProper_of_locallyQuasiFinite _

theorem baseModel_above : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₀' : Level H) (B : BaseModel T l₀) (B' : BaseModel T l₀'), 0 < n → (∃ e, N ∣ n ^ e) → l₀.Dvd l₀' → ∃ (b : RZ H (n * l₀.M) 1 →+* RZ H (n * l₀'.M) 1) (r : (Xo l₀').X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₀').univ.t (Xo l₀).univ.t r), IsInc (RZ H (n * l₀.M) 1).subtype (RZ H (n * l₀'.M) 1).subtype b ∧ LevComp (Xo l₀').univ (Xo l₀).univ r ν ∧ Nonempty (B'.C.Above B.C b r ν) := by
  intro hR L₁ L₂ L₃ E _ _ _ H D Xo n N T hN l₀ l₀' B B' hn ⟨e, he⟩ hd
  have hM : 0 < l₀.M := lt_of_lt_of_le (by norm_num) l₀.three_le
  have hM' : 0 < l₀'.M := lt_of_lt_of_le (by norm_num) l₀'.three_le
  have hS : 0 < n * l₀.M := Nat.mul_pos hn hM
  have hS' : 0 < n * l₀'.M := Nat.mul_pos hn hM'
  have hN0 : 0 < N := B.A_eq ▸ B.l₁.A_pos
  have hSS : n * l₀.M ∣ n * l₀'.M := Nat.mul_dvd_mul_left n hd.1
  have he₀ : N ∣ (n * l₀.M) ^ e := he.trans (pow_dvd_pow_of_dvd (Dvd.intro _ rfl) e)
  have he₁ : N ∣ (n * l₀'.M) ^ e := he.trans (pow_dvd_pow_of_dvd (Dvd.intro _ rfl) e)
  obtain ⟨b, hb⟩ := (GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H _ _ 1 1 e hS' one_pos hSS dvd_rfl).1
  obtain ⟨b₁, hb₁⟩ := (GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H _ _ N N e hS' hN0 hSS dvd_rfl).1
  have hd₁ : B.l₁.Dvd B'.l₁ := ⟨by rw [B.M_eq, B'.M_eq]; exact hd.1, by rw [B.Mb_eq, B'.Mb_eq]; exact hd.2.1,
    by rw [B.A_eq, B'.A_eq]⟩
  have hdB : l₀.Dvd B.l₁ := ⟨by rw [B.M_eq], by rw [B.Mb_eq], by rw [B.A_one]; exact one_dvd _⟩
  have hdB' : l₀'.Dvd B'.l₁ := ⟨by rw [B'.M_eq], by rw [B'.Mb_eq], by rw [B'.A_one]; exact one_dvd _⟩
  obtain ⟨k, r, ν, hr, hk, hlev, -⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN l₀ l₀' hd
  obtain ⟨k₁, r₁, ν₁, hr₁, hk₁, hlev₁, -⟩ := GlobalTheory.T.exists_finite_etale_surjective_levelMap E H D Xo hN B.l₁ B'.l₁ hd₁
  have dO := (ded l₀ _ e 1 B.A_one hS (one_dvd _)).2 B.β B.β_inc
  obtain ⟨ft', dO'⟩ := ded l₀' _ e 1 B'.A_one hS' (one_dvd _)
  replace dO' := dO' B'.β B'.β_inc
  have dO₁' := (ded B'.l₁ _ e N B'.A_eq hS' he₁).2 B'.β₁ B'.β₁_inc
  obtain ⟨ln', pre', fl', dom', qc'⟩ := dense_part B'.C dO'
  obtain ⟨ln₁', pre₁', fl₁', dom₁', qc₁'⟩ := dense_part B'.C₁ dO₁'
  have pr := isProper_of_proj B.C.proj
  have pr' := isProper_of_proj B'.C.proj
  have pr₁' := isProper_of_proj B'.C₁.proj
  have red' := isReduced_of_normal B'.C.normal
  have red₁' := isReduced_of_normal B'.C₁.normal

  have q₁ : k₁.comp B.β₁ = B'.β₁.comp b₁ := RingHom.ext fun x => Subtype.ext <|
    ((hk₁ _).trans (B.β₁_inc x)).trans ((B'.β₁_inc _).trans (hb₁ x)).symm
  have q₂ : b₁.comp B.b' = B'.b' := RingHom.ext fun x => Subtype.ext <|
    ((hb₁ _).trans (B.b'_inc x)).trans (B'.b'_inc x).symm
  have q₃ : b₁.comp B.b = B'.b.comp b := RingHom.ext fun x => Subtype.ext <|
    ((hb₁ _).trans (B.b_inc x)).trans ((B'.b_inc _).trans (hb x)).symm
  have q₄ : k.comp B.β = B'.β.comp b := RingHom.ext fun x => Subtype.ext <|
    ((hk _).trans (B.β_inc x)).trans ((B'.β_inc _).trans (hb x)).symm

  have ha : r₁ ≫ T.a B.l₁ B.A_eq = T.a B'.l₁ B'.A_eq := by
    refine (T.compat B.l₁ B'.l₁ B.A_eq B'.A_eq r₁ ν₁ k₁ hk₁ hr₁ fun x => ?_).1
    have := hlev₁.2 x
    rwa [B.A_eq, B'.A_eq, Nat.div_self hN0, pow_one] at this
  have w : B'.q ≫ T.s = (B'.C₁.s ≫ spMap b₁) ≫ spMap B.b' := by
    rw [B'.q_over, Category.assoc, spMap_spMap, q₂]
  have hrs₁ : r₁ ≫ B.C₁.j ≫ B.C₁.s = B'.C₁.j ≫ B'.C₁.s ≫ spMap b₁ := by
    rw [j_s, ← Category.assoc, hr₁, ← Category.assoc B'.C₁.j, j_s, Category.assoc, Category.assoc, spMap_spMap,
      spMap_spMap, q₁]
  have hrs : r ≫ B.C.j ≫ B.C.s = B'.C.j ≫ B'.C.s ≫ spMap b := by
    rw [j_s, ← Category.assoc, hr, ← Category.assoc B'.C.j, j_s, Category.assoc, Category.assoc, spMap_spMap,
      spMap_spMap, q₄]
  have qf := B.q_fin
  obtain ⟨h, ⟨h₁, h₂⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart B'.C₁.X _ _ B.C₁.X B'.C₁.j B'.C₁.normal pre₁' fl₁'
    dom₁' qc₁' (pullback.lift B.q B.C₁.s B.q_over) (pullback.lift B'.q _ w) (r₁ ≫ B.C₁.j) inferInstance (by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, B.q_j, B'.q_j, ha]
      · simp only [Category.assoc, pullback.lift_snd, hrs₁])
  have hq : h ≫ B.q = B'.q := by
    have := congrArg (· ≫ pullback.fst _ _) h₂
    simpa only [Category.assoc, pullback.lift_fst] using this
  have hs : h ≫ B.C₁.s = B'.C₁.s ≫ spMap b₁ := by
    have := congrArg (· ≫ pullback.snd _ _) h₂
    simpa only [Category.assoc, pullback.lift_snd] using this
  have hf : (h ≫ B.above.π) ≫ B.C.s = B'.above.π ≫ B'.C.s ≫ spMap b := by
    rw [Category.assoc, B.above.π_over, ← Category.assoc, hs, ← Category.assoc, B'.above.π_over, Category.assoc,
      Category.assoc, spMap_spMap, spMap_spMap, q₃]

  have sq : r₁ ≫ B.r = B'.r ≫ r := by
    obtain ⟨m₁, hm₁⟩ := levComp_comp hdB hd₁ B.lev hlev₁
    obtain ⟨m₂, hm₂⟩ := levComp_comp hd hdB' hlev B'.lev
    refine (GlobalTheory.T.map_to_universalObject_unique L₁ L₂ L₃ E H D l₀ B'.l₁ (Xo l₀) _ _ _ _ (Xo B'.l₁).univ _ _ m₁ m₂
      (isReduced_open B'.C₁ dO₁') ?_ hm₁ hm₂).1
    have := mono_spMap dO
    rw [← cancel_mono (spMap B.β)]
    simp only [Category.assoc, ← j_s B.C]
    rw [hrs, ← Category.assoc B.r, ← B.above.j_comm, ← Category.assoc B'.r, ← B'.above.j_comm, Category.assoc,
      Category.assoc, ← hf, ← Category.assoc r₁, ← h₁]
    simp only [Category.assoc]

  have fin : ∀ {l : Level H} (B : BaseModel T l), IsFinite B.above.π := by
    intro l B
    have hS : 0 < n * l.M := Nat.mul_pos hn (lt_of_lt_of_le (by norm_num) l.three_le)
    have := (((GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H _ _ 1 N e hS hN0 dvd_rfl (one_dvd _)).2 B.b B.b_inc).1 rfl
      (he.trans (pow_dvd_pow_of_dvd (Dvd.intro _ rfl) e))).1
    have := B.above.fin
    rw [← pullback.lift_fst B.above.π B.C₁.s B.above.π_over]
    infer_instance
  have fπ := fin B
  have fπ' := fin B'
  have rs := B'.r_surj
  have sπ' : Surjective B'.above.π := by
    have : IsDominant (B'.C₁.j ≫ B'.above.π) := by rw [B'.above.j_comm]; infer_instance
    have : IsDominant B'.above.π := IsDominant.of_comp B'.C₁.j _
    exact surjective_of_isDominant_of_isClosed_range _ B'.above.π.isClosedMap.isClosed_range
  obtain ⟨f, hf₁, hf₂⟩ := GlobalTheory.T.exists_desc_of_dense_preimmersion _ _ _ _ _ _ B'.above.π B'.C₁.j B'.C.j B'.r (B'.C.s ≫ spMap b) B.C.s
    (h ≫ B.above.π) (r ≫ B.C.j) B'.C.normal red₁' fπ' sπ' rs dom₁' qc₁' pre' fl' dom' qc' inferInstance
    inferInstance B'.above.j_comm
    (by rw [← Category.assoc, h₁, Category.assoc, B.above.j_comm, ← Category.assoc, sq, Category.assoc]) hf
    (by rw [Category.assoc, hrs])
  have fo : f ≫ B.C.s = B'.C.s ≫ spMap b :=
    ext_of_isDominant B'.C.j (by rw [← Category.assoc, hf₁, Category.assoc, hrs])
  obtain ⟨mu, hmu⟩ := GlobalTheory.T.exists_semiAbelianTripleMap_extending_modelMap hR E H _ _ _ _ _ _ _ _ _ _ _ _ B.C B'.C r ν f dO' ft' (Xo l₀').univ.proper hf₁
  refine ⟨b, r, ν, hb, hlev, ⟨⟨f, fo, isFinite_lift _ _ _ _ fo ?_, mu, hf₁, hmu⟩⟩⟩
  have fq : ∀ z, (B'.q ⁻¹' {z}).Finite := by
    have := (((GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion E H n _ N N e hS' hN0 (Dvd.intro _ rfl) dvd_rfl).2 B'.b' B'.b'_inc).2 rfl).1
    have := B'.q_fin
    intro z
    rw [← pullback.lift_fst B'.q B'.C₁.s B'.q_over]
    exact Scheme.Hom.finite_preimage_singleton _ z
  exact fib_of_surj _ _ hf₂ (fib_comp _ _ (fib_of_comp _ _ hq fq) B.above.π.finite_preimage_singleton)

end GlobalTheory.BaseTransition
