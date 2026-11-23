import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.AlgStep

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CechPic
open scoped TensorProduct

namespace GlobalTheory.IntModel

theorem ringKrullDim_adjoin_le {R S : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S] (s : Finset S) :
    ringKrullDim (Algebra.adjoin R (s : Set S)) ≤ ringKrullDim R := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, Algebra.adjoin_empty]
    exact (ringKrullDim_eq_of_ringEquiv (Algebra.botEquivOfInjective
      (FaithfulSMul.algebraMap_injective R S)).toRingEquiv).le
  | insert a s _ ih =>
    refine le_trans ?_ ih
    set T := Algebra.adjoin R (s : Set S)
    set T' := Algebra.adjoin R ((insert a s : Finset S) : Set S)
    have hle : T ≤ T' := Algebra.adjoin_mono (by simp)
    have ha : a ∈ T' := Algebra.subset_adjoin (by simp)
    have : Algebra.FiniteType R T := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
    have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R T
    let f : T →+* T' := (Subalgebra.inclusion hle).toRingHom
    have hf : Function.Injective f := Subalgebra.inclusion_injective hle
    have hgen : Function.Surjective (Polynomial.eval₂RingHom f ⟨a, ha⟩) := by
      rintro ⟨y, hy⟩
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with rfl | hx
        · exact ⟨Polynomial.X, by simp⟩
        · exact ⟨Polynomial.C ⟨x, Algebra.subset_adjoin hx⟩, by simp [f]⟩
      | algebraMap r => exact ⟨Polynomial.C (algebraMap R T r), by simp [f]; rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨p, hp⟩ := hx
        obtain ⟨q, hq⟩ := hy
        exact ⟨p + q, by rw [map_add, hp, hq]; rfl⟩
      | mul x y _ _ hx hy =>
        obtain ⟨p, hp⟩ := hx
        obtain ⟨q, hq⟩ := hy
        exact ⟨p * q, by rw [map_mul, hp, hq]; rfl⟩
    obtain ⟨g, hg0, hg⟩ := Algebra.IsAlgebraic.isAlgebraic (R := R) a
    have hinj : Function.Injective (algebraMap R T) := fun x y h =>
      FaithfulSMul.algebraMap_injective R S (congrArg Subtype.val h)
    have halg : ∃ g : Polynomial T, g ≠ 0 ∧ Polynomial.eval₂ f ⟨a, ha⟩ g = 0 := by
      refine ⟨g.map (algebraMap R T), (Polynomial.map_ne_zero_iff hinj).2 hg0, Subtype.ext ?_⟩
      rw [Polynomial.eval₂_map]
      refine (Polynomial.hom_eval₂ g _ T'.val.toRingHom _).trans ?_
      exact hg
    refine (ringKrullDim_le_iff_height_le _).2 fun q hq => ?_
    have h := ReciprocityTheory.CA.height_le_height_comap_of_eval₂_surjective f hf _ hgen halg q
    exact le_trans (by exact_mod_cast h) (Ideal.height_le_ringKrullDim_of_ne_top (Ideal.comap_isPrime f q).ne_top)

theorem ringKrullDim_le_add {O A : Type} (K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [CommRing A]
    [IsDomain A] [Algebra O A] [FaithfulSMul O A] [Algebra.FiniteType O A] [Field K] [Algebra O K] [IsFractionRing O K] :
    ringKrullDim A ≤ ringKrullDim O + ringKrullDim (K ⊗[O] A) := by
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  rw [ringKrullDim_genericFibre_eq O K hd]
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis O A
  have hc : Cardinal.mk s = d := hs.cardinalMk_eq_trdeg.trans hd
  have : Finite s := Cardinal.lt_aleph0_iff_finite.1 (hc ▸ Cardinal.nat_lt_aleph0 d)
  let R := Algebra.adjoin O (Set.range ((↑) : s → A))
  have e : MvPolynomial s O ≃+* R := hs.1.aevalEquiv.toRingEquiv
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv _ e
  have : Algebra.IsAlgebraic R A := hs.isAlgebraic
  have : Algebra.FiniteType R A := .of_restrictScalars_finiteType O R A
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := A)
  have h := ringKrullDim_adjoin_le (R := R) t
  rw [ht, ringKrullDim_eq_of_ringEquiv Subalgebra.topEquiv.toRingEquiv, ← ringKrullDim_eq_of_ringEquiv e,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card, hc, Cardinal.toNat_natCast] at h
  exact h

theorem topologicalKrullDim_eq_succ {O K : Type} [CommRing O] [IsDedekindDomain O] (hO : ¬ IsField O) [Field K]
    [Algebra O K] [IsFractionRing O K] {X Y : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp O} [IsProper p] [Flat p]
    {j : Y ⟶ X} {q : Y ⟶ Sp K} (H : IsPullback j q p (spMap (algebraMap O K))) {d : ℕ}
    (hd : topologicalKrullDim Y = d) : topologicalKrullDim X = (d + 1 : ℕ) := by
  have hO1 : ringKrullDim O ≤ 1 := by exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 O)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨A, _, _, i, _, a, rfl, hi⟩ := exists_affine_chart_over p x
    obtain ⟨i₀, _, -⟩ := exists_affine_chart_of_isPullback H i hi
    refine ⟨Set.range i, i.isOpenEmbedding.isOpen_range, ⟨a, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding i.isOpenEmbedding.isEmbedding rfl]
    have : Nonempty (Spec (.of A)) := ⟨a⟩
    have : IsIntegral (Spec (.of A)) := isIntegral_of_isOpenImmersion i
    have : IsDomain A := (affine_isIntegral_iff (.of A)).1 this
    have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap O A))) := by rw [← hi]; infer_instance
    have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap O A))) := by rw [← hi]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
    rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hfl
    have : Algebra.FiniteType O A := RingHom.finiteType_algebraMap.mp hft
    have : Module.Flat O A := RingHom.flat_algebraMap_iff.mp hfl
    have : FaithfulSMul O A := inferInstance
    have h₁ : ringKrullDim (K ⊗[O] A) ≤ d :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).ge.trans
        (i₀.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans hd.le)
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).le.trans ((ringKrullDim_le_add (O := O) K).trans ?_)
    refine (add_le_add hO1 h₁).trans_eq ?_
    push_cast
    exact add_comm _ _
  · have := IsPreimmersion.of_isLocalization (R := O) (S := K) (nonZeroDivisors O)
    have : IsPreimmersion j := MorphismProperty.of_isPullback H.flip this
    have hj := j.isEmbedding
    have eX : topologicalKrullDim X = Order.krullDim X := Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    have eY : topologicalKrullDim Y = Order.krullDim Y := Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
    rw [eY] at hd
    rw [eX]
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hd.ge
    have hm : StrictMono (j : Y → X) := fun a b h =>
      ⟨hj.isInducing.specializes_iff.2 h.1, fun h' => h.2 (hj.isInducing.specializes_iff.1 h')⟩
    obtain ⟨m, hm0, hmp⟩ := Ring.not_isField_iff_exists_prime.1 hO
    have hp (y : Y) : (p (j y)).asIdeal = ⊥ := by
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
      change Ideal.comap (algebraMap O K) (q y).asIdeal = ⊥
      rw [(Ideal.eq_bot_or_top _).resolve_right (q y).2.ne_top]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
    have hs : p (j l.head) ⤳ (⟨m, hmp⟩ : PrimeSpectrum O) :=
      (PrimeSpectrum.le_iff_specializes _ _).1 ((hp _).le.trans bot_le)
    obtain ⟨x, hx, hxm⟩ := p.isClosedMap.specializingMap hs
    have hlt : x < (l.map _ hm).head := by
      refine ⟨hx, fun h' => hm0 ?_⟩
      have h₁ : p x ⤳ p (j l.head) := Specializes.map h' p.continuous
      rw [hxm] at h₁
      have h₂ : m ≤ (p (j l.head)).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
      exact le_bot_iff.1 (h₂.trans (hp _).le)
    refine Order.le_krullDim_iff.2 ⟨(l.map _ hm).cons x hlt, ?_⟩
    simp [hl]

theorem exists_flat_model {O K : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp K) (hq : IsProjOver q) {ι : Type} [Fintype ι]
    (P : ι → Scheme.{0}) (p : ∀ i, P i ⟶ Sp O) (f : ∀ i, Y ⟶ P i) (hp : ∀ i, IsProjOver (p i))
    (hf : ∀ i, f i ≫ p i = q ≫ spMap (algebraMap O K)) :
    ∃ (X : Scheme.{0}) (π : X ⟶ Sp O) (j : Y ⟶ X), IsIntegral X ∧ IsProjOver π ∧ Flat π ∧
      IsPullback j q π (spMap (algebraMap O K)) ∧ ∀ i, ∃ g : X ⟶ P i, j ≫ g = f i ∧ g ≫ p i = π := by
  obtain ⟨W₀, s₀, i₀, hs₀, H₀⟩ :=
    GlobalTheory.ProjClosure.exists_isProjOver_isPullback_of_isLocalization (nonZeroDivisors O) q hq
  obtain ⟨W, h, r, hW, hr, hg⟩ :=
    CommonModel.exists_common s₀ hs₀ i₀ P p f hp (fun i => (hf i).trans H₀.w.symm) Finset.univ
  have w : h ≫ r ≫ s₀ = q ≫ spMap (algebraMap O K) := by rw [← Category.assoc, hr, H₀.w]
  have hqp : IsProper q := CommonModel.isProper_of_isProjOver hq
  have hsp : IsProper (r ≫ s₀) := CommonModel.isProper_of_isProjOver hW
  have hb := IsPullback.of_hasPullback (r ≫ s₀) (spMap (algebraMap O K))
  let f' : Y ⟶ pullback (r ≫ s₀) (spMap (algebraMap O K)) := pullback.lift h q w
  have hf' : f' ≫ pullback.snd _ _ = q := pullback.lift_snd _ _ _
  let ρ : pullback (r ≫ s₀) (spMap (algebraMap O K)) ⟶ Y :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  have hρ : ρ ≫ q = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 Y := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ q) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ q
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : f' ≫ pullback.fst _ _ = h := pullback.lift_fst _ _ _
  have : IsAffineHom (pullback.fst (r ≫ s₀) (spMap (algebraMap O K))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : QuasiCompact h := by rw [← hh]; infer_instance
  have : Flat (spMap (algebraMap O K)) := flat_specMap_localization (nonZeroDivisors O) K
  have : Mono (spMap (algebraMap O K)) := mono_specMap_localization (nonZeroDivisors O) K
  have hpb := isPullback_toImage_of_isClosedImmersion h f' _ hh
  refine ⟨h.image, h.imageι ≫ r ≫ s₀, h.toImage, inferInstance,
    ProjSpace.isProjOver_comp_of_isClosedImmersion _ hW, flat_image_of_over_fractionField h (r ≫ s₀) q w.symm, ?_,
    fun i => ?_⟩
  · have := hpb.flip.paste_vert hb
    rwa [hf'] at this
  · obtain ⟨g, h₁, h₂⟩ := hg i (Finset.mem_univ i)
    exact ⟨h.imageι ≫ g, by rw [← Category.assoc, h.toImage_imageι, h₁], by rw [Category.assoc, h₂]⟩

theorem exists_presents {Z : Scheme.{0}} [IsIntegral Z] (Δ : CartierDiv Z) {L : LB Z} (hL : L.IsLB)
    (e : toPic Δ = cls L hL) : ∃ r : L.ι → Z.functionFieldˣ, Presents Δ L r := by
  obtain ⟨r, hr⟩ := exists_isRatSec hL
  have h := presents_divOfRatSec hL hr
  set E := divOfRatSec hL hr
  have h0 : toPic (Δ - E) = 0 := by rw [map_sub, e, h.toPic_eq, sub_self]
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (isLB_toLB (Δ - E))).1 h0
  let s : (toLB (Δ - E)).Sec := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  have P := presents_toLB (Δ - E)
  have hg (x : Z) : (Δ - E).GeneratesAt x (P.rat s) := by
    obtain ⟨i, hi⟩ := exists_chart P.isLB x
    exact ⟨_, P.isEqn i x hi, (P.rat_mul s i (gen_mem hi)).symm ▸ unitAt_fnOf hi _ (t.s i)⟩
  let g : Z.functionFieldˣ := (Units.mk0 _ (hg (genericPoint Z)).ne_zero)⁻¹
  have eg : Δ - E = CartierDiv.principal g := CartierDiv.ext_of_isEqn fun x =>
    ⟨g, CartierDiv.isEqn_iff_generatesAt_inv.2 (by simpa [g] using hg x), CartierDiv.isEqn_principal g x⟩
  have := h.add_principal g
  rw [← eg, add_sub_cancel] at this
  exact ⟨_, this⟩

theorem exists_flat_model_two {O K : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp K) (hq : IsProjOver q) {P P' : Scheme.{0}} {p : P ⟶ Sp O}
    {p' : P' ⟶ Sp O} {f : Y ⟶ P} {f' : Y ⟶ P'} (hp : IsProjOver p) (hp' : IsProjOver p')
    (hf : f ≫ p = q ≫ spMap (algebraMap O K)) (hf' : f' ≫ p' = q ≫ spMap (algebraMap O K)) :
    ∃ (X : Scheme.{0}) (π : X ⟶ Sp O) (j : Y ⟶ X), IsIntegral X ∧ IsProjOver π ∧ Flat π ∧
      IsPullback j q π (spMap (algebraMap O K)) ∧ (∃ g : X ⟶ P, j ≫ g = f ∧ g ≫ p = π) ∧
        ∃ g : X ⟶ P', j ≫ g = f' ∧ g ≫ p' = π := by
  obtain ⟨X, π, j, hX, hπ, hfl, H, hg⟩ := exists_flat_model (O := O) q hq (fun i : Bool => Bool.rec P P' i)
    (fun i => Bool.rec p p' i) (fun i => Bool.rec f f' i) (fun i => by cases i <;> assumption)
    (fun i => by cases i <;> assumption)
  exact ⟨X, π, j, hX, hπ, hfl, H, hg false, hg true⟩

theorem pull_cls_O1 {R : Type} [CommRing R] {X Y : Scheme.{0}} (j : Y ⟶ X) (c : Y ⟶ Sp R) {n : ℕ} {B : LB Y} (hB : B.IsLB)
    (s : Fin (n + 1) → B.Sec) (hs : ⨆ i, Out.nonzeroLocus (s i) = ⊤) (g : X ⟶ PSpace R n)
    (h₁ : j ≫ g = ProjSpace.toProj c s hs) (h : ((ProjSpace.O1 R n).pull g).IsLB) : pull j (cls _ h) = cls B hB := by
  have hO := ProjSpace.O1_isLB R n
  rw [cls_pull hO, ← pull_comp, h₁, ← cls_pull hO _ (LB.isLB_pull hO _)]
  exact (cls_eq_iff _ _).2 (ProjSpace.lbIso_pullback_O1_toProj c s hs)

theorem exists_model_pair {O K : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {Y : Scheme.{0}} [IsIntegral Y] (q : Y ⟶ Sp K) (hq : IsProjOver q) {A B : LB Y} (hA : IsGenerated A)
    (hB : IsGenerated B) :
    ∃ (X : Scheme.{0}) (π : X ⟶ Sp O) (j : Y ⟶ X), IsIntegral X ∧ IsProjOver π ∧ Flat π ∧
      IsPullback j q π (spMap (algebraMap O K)) ∧ ∃ La Lb : HermLB π,
        pull j (cls _ La.isLB) = cls _ hA.isLB ∧ pull j (cls _ Lb.isLB) = cls _ hB.isLB := by
  obtain ⟨a, sa, hsa⟩ := hA.exists_fin_succ
  obtain ⟨b, sb, hsb⟩ := hB.exists_fin_succ
  let c := q ≫ spMap (algebraMap O K)
  obtain ⟨X, π, j, hX, hπ, hfl, H, ⟨ga, ha₁, ha₂⟩, gb, hb₁, hb₂⟩ := exists_flat_model_two q hq
    ⟨a, 𝟙 _, inferInstance, Category.id_comp _⟩ ⟨b, 𝟙 _, inferInstance, Category.id_comp _⟩ (ProjSpace.toProj_str c sa hsa)
    (ProjSpace.toProj_str c sb hsb)
  have ea := pull_cls_O1 j c hA.isLB sa hsa ga ha₁ (LB.isLB_pull (ProjSpace.O1_isLB O a) ga)
  have eb := pull_cls_O1 j c hB.isLB sb hsb gb hb₁ (LB.isLB_pull (ProjSpace.O1_isLB O b) gb)
  obtain ⟨La, hLa⟩ : ∃ L : HermLB π, L.B = (ProjSpace.O1 O a).pull ga := ⟨(ProjSpace.hermitianTwistingSheaf O a).pull ga ha₂, rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ L : HermLB π, L.B = (ProjSpace.O1 O b).pull gb := ⟨(ProjSpace.hermitianTwistingSheaf O b).pull gb hb₂, rfl⟩
  refine ⟨X, π, j, hX, hπ, hfl, H, La, Lb, ?_, ?_⟩
  · rw [← ea]
    congr 2
  · rw [← eb]
    congr 2

theorem exists_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv), ∃ (M : TrueGeo.Model Y)
    (L : HermLB M.p) (r : (L.B.pull M.j).ι → Y.Fnˣ), Presents Δ (L.B.pull M.j) r := by
  intro F _ _ Y Δ
  obtain ⟨t, ht⟩ := (AmpleDominates.eventually_isGenerated Y.str Y.isAmple_projective_O_one (isLB_toLB Δ)).exists
  have hA : IsGenerated (lbPow Y.O1 t) := ((isGenerated_O1 F Y.N).pull Y.ι).pow t
  obtain ⟨X, π, j, hX, hπ, hfl, H, La, Lb, ea, eb⟩ := exists_model_pair (O := 𝓞 F) Y.str Y.isProjOver hA ht
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance
  have har : IsArithVar π Y.dim := ⟨inferInstance, inferInstance, hX, hπ, inferInstance,
    topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩
  refine ⟨⟨X, π, har, j, H⟩, La.tens Lb.dual, exists_presents Δ (LB.isLB_pull (La.tens Lb.dual).isLB j) ?_⟩
  have e : cls _ (La.tens Lb.dual).isLB = cls _ La.isLB - cls _ Lb.isLB :=
    (cls_tens La.isLB Lb.dual.isLB _).trans ((congrArg _ (cls_dual Lb.isLB _)).trans (sub_eq_add_neg _ _).symm)
  refine Eq.trans ?_ (cls_pull (La.tens Lb.dual).isLB j _).symm
  rw [e, map_sub, ea, eb, cls_div hA.isLB (isLB_toLB Δ), sub_sub_cancel, toPic_apply]

end GlobalTheory.IntModel
