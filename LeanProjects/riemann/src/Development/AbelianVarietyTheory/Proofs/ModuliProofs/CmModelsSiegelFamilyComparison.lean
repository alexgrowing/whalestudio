import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EtaleOfSemilocalDedekindOfBirational
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MonoOfUnramifiedOfPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsClosedImmersionRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusFiniteEtale
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteLiftRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelDataPullbackOfLevelMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.SiegelComparison

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull (hC : Out.CubePullSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull hC f t
  exact ⟨_, ⟨m⟩⟩

theorem exists_section {S S' : Scheme.{0}} {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f)
    (x : S' ⟶ t.G.left) (hx : x ≫ t.G.hom = f) : ∃ σ : 𝟙_ (Over S') ⟶ t'.G, σ.left ≫ m.φ = x :=
  ⟨Over.homMk (m.cart.1.lift x (𝟙 S') (hx.trans (Category.id_comp f).symm)) (m.cart.1.lift_snd _ _ _),
    m.cart.1.lift_fst _ _ _⟩

theorem exists_cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (g : S'' ⟶ S') (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, m'.φ ≫ m.φ = n.φ := by
  subst e
  obtain ⟨m', hm⟩ := sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n
  exact ⟨m', hm.symm⟩

theorem isAbelianScheme_of_proper {S : Scheme.{0}} (t : SAB H S) (h : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨t.comm, t.semi.smooth, h, t.semi.geomConnected⟩

theorem exists_square {S S' : Scheme.{0}} {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) :
    ∃ m₂ : (G2 t'.G).left ⟶ (G2 t.G).left, IsSquare m.φ m₂ ∧ ∀ (X : Scheme.{0}) (φ₂ : X ⟶ (G2 t'.G).left),
      LBIso ((abelian₂ t'.G t'.PP.L).pull φ₂) ((abelian₂ t.G t.PP.L).pull (φ₂ ≫ m₂)) := by
  have h := m.cart
  let U := lift (pushPt h.1.w (fst t'.G t'.G)) (pushPt h.1.w (snd t'.G t'.G))
  refine ⟨U.left, ⟨?_, ?_⟩, fun X φ₂ => ?_⟩
  · exact congrArg (fun z => z.left) (lift_fst (pushPt h.1.w (fst t'.G t'.G)) (pushPt h.1.w (snd t'.G t'.G)))
  · exact congrArg (fun z => z.left) (lift_snd (pushPt h.1.w (fst t'.G t'.G)) (pushPt h.1.w (snd t'.G t'.G)))
  · obtain ⟨w, hw, -⟩ := m.lin
    refine LBIso.chartPull (chartPullOut t'.PP.L _ _ φ₂ _ fun _ => rfl) (chartPullOut t.PP.L _ _ _ _ fun I => ?_)
      (iso_linComb ((isGen_iff w).1 hw) _ _)
    rw [Category.assoc, Category.assoc]
    congr 1
    refine psum_push h _ _ U (fun i => ?_) I.down
    fin_cases i <;> simp [U, x2]

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_genericPart (Y : Model Xo c β) (hβ : IsDedFrac β) (U : Y.X.Opens) (hU : (U : Set Y.X) = abLocus Y.t.G) :
    ∃ j : Xo.XF c ⟶ U.toScheme, j ≫ U.ι = Y.j ∧ IsPullback j (pullback.snd _ _) (U.ι ≫ Y.s) (spMap β) ∧
      IsLocallyNoetherian U.toScheme ∧ Geo.Tor.IsNormalScheme U.toScheme ∧ IsPreimmersion j ∧ Flat j ∧
      IsDominant j ∧ QuasiCompact j := by
  obtain ⟨⟨_, hD⟩, _, hF⟩ := hβ
  letI : Algebra O c.F := β.toAlgebra
  obtain ⟨hN, -, -, j₁, j₂, j₃, j₄⟩ := genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense
  replace j₁ : IsPreimmersion Y.j := j₁
  replace j₂ : Flat Y.j := j₂
  replace j₃ : IsDominant Y.j := j₃
  replace j₄ : QuasiCompact Y.j := j₄
  have hr : Set.range Y.j ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hU]
    have : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    exact this
  let j : Xo.XF c ⟶ U.toScheme := IsOpenImmersion.lift U.ι Y.j hr
  have hj : j ≫ U.ι = Y.j := IsOpenImmersion.lift_fac _ _ _
  have sq : IsPullback (𝟙 _) j Y.j U.ι := IsPullback.of_horiz_isIso_mono ⟨by simp [hj]⟩
  have := Y.jQ_open
  have pb : IsPullback j Y.jQ U.ι (pullback.fst Y.s (spMap β)) := by
    refine (IsOpenImmersion.isPullback j Y.jQ U.ι (pullback.fst Y.s (spMap β)) hj.symm ?_)
    ext x
    simp [hU, ← Y.ab_gen]
  refine ⟨j, hj, ?_, inferInstance, fun x => ?_, MorphismProperty.of_isPullback (P := @IsPreimmersion) sq j₁,
    MorphismProperty.of_isPullback (P := @Flat) sq j₂, ?_, MorphismProperty.of_isPullback (P := @QuasiCompact) sq j₄⟩
  · rw [← Y.jQ_over]
    exact pb.paste_vert (IsPullback.of_hasPullback _ _)
  · obtain ⟨_, _⟩ := Y.normal (U.ι x)
    let e := (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv
    exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩
  · constructor
    have hd := Dense.preimage j₃.denseRange U.ι.isOpenEmbedding.isOpenMap
    refine hd.mono ?_
    rintro y ⟨x, hx⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← hx, ← hj]; rfl

theorem map_nsmul_of_add {La A : Type} [AddCommGroup La] [Group A] (e : La → A) (he : ∀ a b, e (a + b) = e a * e b)
    (k : ℕ) (a : La) : e (k • a) = e a ^ k :=
  map_pow (MonoidHom.mk' (fun x : Multiplicative La => e x.toAdd) fun _ _ => he _ _) (Multiplicative.ofAdd a) k

theorem levels_pow {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (x y : D.La) : (o.eta x * o.etaA y) ^ (l.M * l.A) = 1 := by
  have h₁ : o.eta x ^ l.M = 1 := by
    rw [← map_nsmul_of_add _ o.eta_add, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    refine o.eta_ker _ (Submodule.smul_mem_smul ?_ trivial)
    have : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at this
    exact (Ideal.mul_le_inf (I := l.Mb) this).1
  have h₂ : o.etaA y ^ l.A = 1 := by rw [← map_nsmul_of_add _ o.etaA_add, o.etaA_ker]
  rw [mul_pow, pow_mul, h₁, one_pow, _root_.mul_comm l.M, pow_mul, h₂, one_pow, _root_.one_mul]

theorem exists_levelImage (L₁ : Out.Laws) (L₂ : Out.Laws2) (L₃ : Out.Laws3) [Module.Free ℤ D.La] [Module.Finite ℤ D.La]
    (Y : Model Xo c β) (hβ : IsDedFrac β) (U : Y.X.Opens) (hU : (U : Set Y.X) = abLocus Y.t.G)
    (hn : IsUnit ((l.M * l.A : ℕ) : O)) {T : Scheme.{0}} (sT : T ⟶ Sp O) [LocallyOfFiniteType sT] [QuasiCompact sT]
    (tT : SAB H T) (hT : IsProper tT.G.hom) (f : U.toScheme ⟶ T) [IsFinite f] (hf : f ≫ sT = U.ι ≫ Y.s)
    (tU : SAB H U.toScheme) (m₁ : SABMap tU Y.t U.ι) (m₂ : SABMap tU tT f) :
    ∃ (XX : Scheme.{0}) (u : U.toScheme ⟶ XX) (i : XX ⟶ T) (W : XX.Opens) (t : SAB H XX) (m : SABMap tU t u)
      (η' ηA' : D.La → (𝟙_ (Over XX) ⟶ t.G)),
      u ≫ i = f ∧ IsFinite u ∧ Surjective u ∧ Dense (W : Set XX) ∧ IsIso (u ∣_ W) ∧
      Dense ((u ⁻¹ᵁ W : U.toScheme.Opens) : Set U.toScheme) ∧
      IsAbelianScheme t.G ∧ IsReduced XX ∧ Flat (i ≫ sT) ∧ IsFinite i ∧ FormallyUnramified i ∧
      ∀ (a : D.La) (j' : Xo.XF c ⟶ U.toScheme) (g₁ : Xo.XF c ⟶ tU.G.left), j' ≫ U.ι = Y.j →
        (g₁ ≫ m₁.φ = (Y.oF.eta a).left ≫ Y.m.φ → g₁ ≫ m.φ = j' ≫ u ≫ (η' a).left) ∧
        (g₁ ≫ m₁.φ = (Y.oF.etaA a).left ≫ Y.m.φ → g₁ ≫ m.φ = j' ≫ u ≫ (ηA' a).left) := by
  obtain ⟨j, hj, pb, hN, hnorm, j₁, j₂, j₃, j₄⟩ := exists_genericPart Y hβ U hU
  obtain ⟨⟨_, hD⟩, _, hF⟩ := hβ
  letI : Algebra O c.F := β.toAlgebra
  have hn' : IsUnit ((l.M * l.A : ℕ) : Γ(T, ⊤)) := by
    simpa using hn.map (sT.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)
  obtain ⟨Z, et, z₁, z₂, -, -, hZ⟩ := exists_finiteEtale_latticeTorsionHom T tT.G (l.M * l.A) (D.La × D.La)
    (isAbelianScheme_of_proper tT hT) hn'
  obtain ⟨ν₀, hν₀⟩ := exists_cancel m₁ Y.m j hj
  obtain ⟨ν₁, hν₁⟩ := sabComp pullCubComp E H _ _ _ tT tU Y.oF.t f j m₂ ν₀
  obtain ⟨h, hh, -⟩ := hZ _ (fun x => pushHom ν₁.cart _ (Y.oF.eta x.1 * Y.oF.etaA x.2))
    (fun x y => by
      rw [← map_mul, Prod.fst_add, Prod.snd_add, Y.oF.eta_add, Y.oF.etaA_add, _root_.mul_mul_mul_comm])
    (fun x => by rw [← map_pow, levels_pow, map_one])
  have e₀ : Y.oF.eta 0 = 1 := Y.oF.eta_ker 0 (Submodule.zero_mem _)
  have e₀' : Y.oF.etaA 0 = 1 := by simpa using Y.oF.etaA_ker 0
  obtain ⟨k, hk⟩ : ∃ k : Xo.XF c ⟶ Z.left, k = h.left := ⟨_, rfl⟩
  have hw : k ≫ Z.hom = j ≫ f := by rw [hk]; exact (Over.w h).trans (Category.id_comp _)
  have k₁ : ∀ a, k ≫ (et (a, 0)).left = (Y.oF.eta a).left ≫ ν₁.φ := fun a => by
    have := congrArg (fun z => z.left) (hh (a, 0))
    rw [hk]
    simp only [e₀', _root_.mul_one] at this
    exact this
  have k₂ : ∀ a, k ≫ (et (0, a)).left = (Y.oF.etaA a).left ≫ ν₁.φ := fun a => by
    have := congrArg (fun z => z.left) (hh (0, a))
    rw [hk]
    simp only [e₀, _root_.one_mul] at this
    exact this
  obtain ⟨u₀, ⟨hu₁, hu₂⟩, -⟩ := existsUnique_lift_of_densePart _ _ _ _ j hnorm j₁ j₂ j₃ j₄ Z.hom f k inferInstance hw
  have hu₀ : IsFinite u₀ := by
    have : IsFinite (u₀ ≫ Z.hom) := by rw [hu₂]; infer_instance
    exact IsFinite.of_comp _ Z.hom
  have hs : u₀ ≫ Z.hom ≫ sT = U.ι ≫ Y.s := by rw [reassoc_of% hu₂, hf]

  let p : pullback (Z.hom ≫ sT) (spMap β) ⟶ Z.left := pullback.fst _ _
  let g : Xo.XF c ⟶ pullback (Z.hom ≫ sT) (spMap β) :=
    pullback.lift k (pullback.snd _ _) (by rw [← hu₁, Category.assoc, hs, pb.w])
  have hg₁ : g ≫ p = k := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have pb' : IsPullback j g u₀ p :=
    IsPullback.of_bot (by rw [hs, hg₂]; exact pb) (by rw [hu₁, hg₁]) (IsPullback.of_hasPullback _ _)
  obtain ⟨tF, ⟨mF⟩⟩ := exists_pull L₃.cubePull (p ≫ Z.hom) tT
  obtain ⟨νF, hνF⟩ := exists_cancel mF ν₁ g (by rw [reassoc_of% hg₁, hw])
  choose σ hσ using fun x => exists_section mF (p ≫ (et x).left) (by rw [Category.assoc, Over.w])
  have key : ∀ {X : Scheme.{0}} {q : X ⟶ Z.left} {t : SAB H X} (mX : SABMap t tT (q ≫ Z.hom)) (r : Xo.XF c ⟶ X)
      (y : Xo.XF c ⟶ t.G.left) (x : D.La × D.La) (τ : 𝟙_ (Over X) ⟶ t.G) (e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G),
      r ≫ q = k → τ.left ≫ mX.φ = q ≫ (et x).left → k ≫ (et x).left = e.left ≫ ν₁.φ →
      y ≫ mX.φ = e.left ≫ ν₁.φ → y ≫ t.G.hom = r → y = r ≫ τ.left := by
    intro X q t mX r y x τ e a₁ a₂ a₃ a₄ a₅
    apply mX.cart.1.hom_ext
    · rw [Category.assoc]
      erw [a₂]
      rw [reassoc_of% a₁, a₃, a₄]
    · rw [a₅, Category.assoc]
      erw [Over.w τ]
      exact (Category.comp_id _).symm
  have hsec : ∀ {X : Scheme.{0}} {t : SAB H X} {r : Xo.XF c ⟶ X} (ν : SABMap Y.oF.t t r)
      (e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), (e.left ≫ ν.φ) ≫ t.G.hom = r := by
    intro X t r ν e
    rw [Category.assoc, ν.cart.1.w, ← Category.assoc, Over.w e]
    exact Category.id_comp _
  have hcl : IsClosedImmersion g := moduli_isClosedImmersion L₁ L₂ L₃ E H D l Xo c Y.oF Y.m0 _ (pullback.snd _ _) tF g νF
    (fun a => σ (a, 0)) (fun a => σ (0, a)) hg₂
    (fun a => key mF g _ _ _ _ hg₁ (hσ _) (k₁ a) (by rw [← hνF]; exact Category.assoc _ _ _) (hsec νF _))
    (fun a => key mF g _ _ _ _ hg₁ (hσ _) (k₂ a) (by rw [← hνF]; exact Category.assoc _ _ _) (hsec νF _))
    (MorphismProperty.of_isPullback (P := @IsFinite) pb' hu₀)
  have hred : IsReduced U.toScheme := by
    have : ∀ x : U.toScheme, _root_.IsReduced (U.toScheme.presheaf.stalk x) := fun x => by
      obtain ⟨_, _⟩ := hnorm x
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have := Y.flat
  obtain ⟨XX, u, i, W, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉⟩ := FiniteImage.main O c.F _ _ u₀ (Z.hom ≫ sT) hu₀ hred
    (by rw [hs]; infer_instance) inferInstance inferInstance (by
      have e : pb'.isoPullback.inv ≫ g = pullback.snd u₀ p := pb'.isoPullback_inv_snd
      change IsClosedImmersion (pullback.snd u₀ p)
      rw [← e]; infer_instance)
  obtain ⟨t, ⟨mt⟩⟩ := exists_pull L₃.cubePull (i ≫ Z.hom) tT
  obtain ⟨m, hm⟩ := exists_cancel mt m₂ u (by rw [reassoc_of% a₁, hu₂])
  choose τ hτ using fun x => exists_section mt (i ≫ (et x).left) (by rw [Category.assoc, Over.w])
  refine ⟨XX, u, i ≫ Z.hom, W, t, m, fun a => τ (a, 0), fun a => τ (0, a), by rw [reassoc_of% a₁, hu₂], a₃, a₄, a₅,
    a₆, a₇, isAbelianScheme_of_proper t (MorphismProperty.of_isPullback (P := @IsProper) mt.cart.1 hT), a₈,
    by rw [Category.assoc]; exact a₉, inferInstance,
    MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance inferInstance, fun a j' g₁ hj' => ?_⟩
  obtain rfl : j' = j := by rw [← cancel_mono U.ι, hj, hj']
  have : Mono m₁.φ := MorphismProperty.of_isPullback (P := .monomorphisms _) m₁.cart.1.flip
    (inferInstanceAs (Mono U.ι))
  have fin : ∀ (x : D.La × D.La) (e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G), k ≫ (et x).left = e.left ≫ ν₁.φ →
      g₁ ≫ m₁.φ = e.left ≫ Y.m.φ → g₁ ≫ m.φ = j' ≫ u ≫ (τ x).left := by
    intro x e b₁ b₂
    have b₃ : g₁ = e.left ≫ ν₀.φ := by
      rw [← cancel_mono m₁.φ, b₂, ← hν₀]; exact (Category.assoc _ _ _).symm
    refine (key mt (j' ≫ u) _ x _ e (by rw [Category.assoc, a₁, hu₁]) (hτ x) b₁ ?_ ?_).trans (Category.assoc _ _ _)
    · rw [Category.assoc, hm, hν₁, b₃]; exact Category.assoc _ _ _
    · rw [Category.assoc, m.cart.1.w, ← Category.assoc, b₃]
      exact congrArg (· ≫ u) (hsec ν₀ e)
  exact ⟨fin _ _ (k₁ a), fin _ _ (k₂ a)⟩

theorem exists_int_mul_mem {F : Type} [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] (V : ValuationSubring F) (x : F) :
    ∃ (m : ℤ) (y : V), m ≠ 0 ∧ x * m = y := by
  obtain ⟨m, hm, h⟩ := exists_integral_multiples ℤ ℚ (L := F) {x}
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 (h x (Finset.mem_singleton_self x)).tower_top
  refine ⟨m, y, hm, ?_⟩
  rw [_root_.mul_comm, ← zsmul_eq_mul]
  exact hy.symm

theorem section_comp {S S' : Scheme.{0}} {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f)
    (e : 𝟙_ (Over S') ⟶ t'.G) : (e.left ≫ m.φ) ≫ t.G.hom = f := by
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w e]
  exact Category.id_comp _

theorem eq_comp_section {X S S' : Scheme.{0}} {f : S' ⟶ S} {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f)
    (r : X ⟶ S') (y : X ⟶ t'.G.left) (τ : 𝟙_ (Over S') ⟶ t'.G) (x : S' ⟶ t.G.left) (h₁ : τ.left ≫ m.φ = x)
    (h₂ : y ≫ m.φ = r ≫ x) (h₃ : y ≫ t'.G.hom = r) : y = r ≫ τ.left := by
  apply m.cart.1.hom_ext
  · exact h₂.trans ((congrArg (r ≫ ·) h₁.symm).trans (Category.assoc _ _ _).symm)
  · exact h₃.trans (((Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w τ))).trans (Category.comp_id _)).symm

theorem comp_section {X S : Scheme.{0}} {G : Over S} (r : X ⟶ S) (τ : 𝟙_ (Over S) ⟶ G) :
    (r ≫ τ.left) ≫ G.hom = r :=
  ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) (Over.w τ))).trans (Category.comp_id _)

theorem siegelCompare : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ p : ℕ, p.Prime → p ≠ n → n.Prime → (∃ e, N = n ^ e) → ∃ Ag : SiegelFamily (Module.finrank ℚ E / 2 * (D.p + D.q)) p N, ∀ (W : ValuationSubring ℂ) (l₀ : Level H) (B : BaseModel T l₀) (l l₁ : Level H) (c : Coeff l) (c₁ : Coeff l₁) (Y : Model (Xo l) c (c.V W).subtype) (Y₁ : Model (Xo l₁) c₁ (c₁.V W).subtype) (b : c.V W →+* c₁.V W) (z : ZP p N →+* c₁.V W) (π : Y₁.X ⟶ Y.X), (p : ℂ) ∈ W.nonunits → IsPrimeToPart l₀ l p → n.Coprime l.M → IsIncl b → (∀ x, (((z x : c₁.V W) : c₁.F) : ℂ) = (x : ℂ)) → l₁.M = l.M → l₁.Mb = l.Mb → l₁.A = Nat.lcm l.A N → c₁.F = c.F ⊔ IntermediateField.adjoin ℚ {zeta N} → Raises B Y → Raises B Y₁ → IsTransition Y Y₁ b π → SiegelCompare Y Y₁ b π Ag z := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N T hN₁ p hp hpn hn ⟨e, hN⟩
  obtain ⟨Ag, bas, hbas, hs⟩ := T.sieg p hp hpn
  refine ⟨Ag, fun W l₀ B l l₁ c c₁ Y Y₁ b z π hW hl₀ _ hb hz hM hMb hA hF hR hR₁ htr U U₁ hU hU₁ => ?_⟩
  have hnp : n.Coprime p := (Nat.coprime_primes hn hp).2 hpn.symm
  have hNp : N.Coprime p := hN ▸ hnp.pow_left e
  have hN0 : 0 < N := hN ▸ pow_pos hn.pos e
  obtain ⟨ded, unit, -⟩ := (CoeffRings.coeff_isDedFrac E H l c).2.2.2 p W hp hW
  obtain ⟨ded₁, unit₁, rz₁⟩ := (CoeffRings.coeff_isDedFrac E H l₁ c₁).2.2.2 p W hp hW
  refine ⟨?_, ?_⟩
  · have ab : AbOpen Y.t.G := by
      obtain ⟨_, r, ν, -, -, ⟨a⟩⟩ := hR
      exact (good_pullback L₃.gtBaseChange E H _ _ B.C.t Y.t a.π a.mu B.good).1
    refine AbelianLocusCover.abelianLocus_finite_etale L₁ L₂ L₃ E H D Xo hN₁ l c _ _ Y l₁ c₁ _ _ Y₁ b π N ded ded₁ hb
      (etale_coeff_adjoin_zeta E H l l₁ c c₁ p N W hp hW hNp hN0 hF b hb) ⟨n, e, hn, unit n hnp, hN⟩ hM hMb hA
      (hF ▸ le_sup_left) (fun x => ?_) ab htr U U₁ hU hU₁
    have := c₁.fin
    have := ded.2.1
    obtain ⟨m, y, hm, h⟩ := exists_int_mul_mem (c₁.V W) x
    exact ⟨y, m, Int.cast_ne_zero.2 hm, by rw [map_intCast, map_intCast]; exact h⟩
  obtain ⟨hd, hcop, -⟩ := (primeToPart_spec E H p hp).2.1 l l₀ hl₀
  obtain ⟨b', hb'⟩ := rz₁ n N hnp hN0
    (hF ▸ (le_sup_right : _ ≤ c.F ⊔ IntermediateField.adjoin ℚ {zeta N}) (IntermediateField.mem_adjoin_simple_self ℚ _))
  obtain ⟨f, hf, tU, m₁, m₂, hfin, hlev⟩ := AbelianLocusMap.exists_finite_map L₁ L₂ L₃ E H D Xo n N T hN₁ l₀ B l₁ c₁ _ _
    Y₁ b' U₁ hn.pos ⟨e, hN ▸ dvd_rfl⟩ ⟨hM ▸ hd.1, hMb ▸ hd.2.1, hA ▸ hd.2.2.trans (Nat.dvd_lcm_left _ _)⟩
    (hA ▸ Nat.dvd_lcm_right _ _) (by
      have := unit₁ (n * l₀.M) (Nat.Coprime.mul_left hnp hcop)
      rw [Nat.cast_mul] at this
      exact this) ded₁ hb' hR₁ hU₁
  obtain ⟨f', hf₁, hf₂, hfin⟩ : ∃ f' : U₁.toScheme ⟶ pullback T.sM (spMap b'),
      f' ≫ pullback.fst _ _ = f ∧ f' ≫ pullback.snd _ _ = U₁.ι ≫ Y₁.s ∧ IsFinite f' :=
    ⟨_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, hfin⟩
  obtain ⟨tT, ⟨mT⟩⟩ := exists_pull L₃.cubePull (pullback.fst T.sM (spMap b')) T.tM
  choose levT hlevT using fun x => exists_section mT _ (comp_section (pullback.fst T.sM (spMap b')) (T.lev x))
  choose lev' hlev' using fun x => exists_section m₂ _ (comp_section f (T.lev x))
  obtain ⟨ν', hν'⟩ := exists_cancel mT m₂ f' hf₁
  obtain ⟨w, hw, w₁, w₂⟩ := hs _ (c₁.F.val.toRingHom.comp (c₁.V W).subtype) z b'
    (Subtype.val_injective.comp Subtype.val_injective) hz hb' _ _ _ tT mT levT (IsPullback.of_hasPullback _ _) hlevT
  have hw' : w ≫ pullback.snd _ _ = pullback.snd T.sM (spMap b') := by
    obtain ⟨_, _, _, -, -, -, -, h, -⟩ := hw
    exact h
  have hd := GlobalTheory.SiegelDataPull.siegData_pull E H D _ _ _ _ f' tT tU ν' levT lev' _ p N Ag z bas w (fun x =>
    eq_comp_section mT f' _ _ _ (hlevT x)
      (((Category.assoc _ _ _).trans (congrArg ((lev' x).left ≫ ·) hν')).trans ((hlev' x).trans
        ((congrArg (· ≫ (T.lev x).left) hf₁.symm).trans (Category.assoc _ _ _))))
      (section_comp ν' _)) hw
  rw [hf₂, SiegData, Category.assoc U₁.ι] at hd
  obtain ⟨o, φ, φ₂, o₁, o₂, o₃, o₄, o₅, o₆⟩ := hd
  obtain ⟨q, q₁, q₂⟩ := exists_square m₁
  refine ⟨bas, f' ≫ w, o, φ ≫ m₁.φ, φ₂ ≫ q, hbas, (o₁.comp m₁.cart).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩,
    LBIso.trans o.isLB (pull_isLB (DVR.linComb_isLB _ tU.PP.isLB _ _) _) (pull_isLB (DVR.linComb_isLB _ Y₁.t.PP.isLB _ _) _)
      o₃ (q₂ _ φ₂), fun u j' hj' => ?_, o₅, o₆, inferInstance, fun hM' => ?_⟩
  · rw [Category.assoc, q₁.1, reassoc_of% o₂.1]
  · rw [Category.assoc, q₁.2, reassoc_of% o₂.2]
  · obtain ⟨ν₀, hν₀⟩ := exists_cancel m₁ Y₁.m j' hj'
    have a₁ : ((Y₁.oF.etaA (bas u) ^ (l₁.A / N)).left ≫ ν₀.φ) ≫ m₁.φ =
        (Y₁.oF.etaA (bas u) ^ (l₁.A / N)).left ≫ Y₁.m.φ :=
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hν₀)
    have a₂ := eq_comp_section m₂ j' _ _ _ (hlev' (bas u)) (hlev (bas u) j' _ hj' a₁) (section_comp ν₀ _)
    refine Eq.trans ?_ a₁
    rw [a₂, ← o₄]
    exact ((Category.assoc _ _ _).trans (congrArg (j' ≫ ·) (Category.assoc _ _ _))).symm
  · have : Module.Free ℤ D.La := Module.Free.of_equiv bas
    have : Module.Finite ℤ D.La := Module.Finite.equiv bas
    have := Ag.qc
    have : Smooth Ag.s := @SmoothOfRelativeDimension.smooth _ _ _ Ag.s Ag.smooth
    have : LocallyOfFiniteType (pullback.snd T.sM (spMap b')) := by rw [← hw']; infer_instance
    have : QuasiCompact (pullback.snd T.sM (spMap b')) := by rw [← hw']; infer_instance
    have hc : l.M'.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hM').symm
    have hc' : (l₁.M * l₁.A).Coprime p := by
      rw [hM, hA]
      exact Nat.Coprime.mul_left (hc.coprime_dvd_left (Nat.dvd_lcm_left _ _))
        ((Nat.Coprime.mul_left (hc.coprime_dvd_left (Nat.dvd_lcm_right _ _)) hNp).coprime_dvd_left
          (Nat.lcm_dvd_mul _ _))
    obtain ⟨XX, u, i, V, t, m, η', ηA', a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, b₁, b₂, b₃⟩ :=
      exists_levelImage L₁ L₂ L₃ Y₁ ded₁ U₁ hU₁ (unit₁ _ hc') (pullback.snd T.sM (spMap b')) tT
        (MorphismProperty.of_isPullback (P := @IsProper) mT.cart.1 T.MM_ab) f' hf₂ tU m₁ ν'
    exact ⟨XX, u, i ≫ w, V, t, tU, m₁, m, η', ηA', by rw [reassoc_of% a₁], a₂, a₃, a₄, a₅, a₆, a₇, a₈,
      by rw [Category.assoc, hw']; exact a₉, inferInstance,
      MorphismProperty.comp_mem @FormallyUnramified _ _ b₂ w₂, b₃⟩

end GlobalTheory.SiegelComparison
