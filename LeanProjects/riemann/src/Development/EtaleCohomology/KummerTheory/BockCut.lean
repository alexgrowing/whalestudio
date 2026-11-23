import Development.EtaleCohomology.KummerTheory.InjSlice
import Development.EtaleCohomology.TateTwists.PrimitiveRootsOfUnityBasicIdentities
import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally
import Development.EtaleCohomology.TateTwists.EtaleTateTwistSectionsLocallyGenerated
import Development.EtaleCohomology.TateTwists.EtaleSheafMonoEpiSectionCriteria
import Development.EtaleCohomology.TateTwists.EtaleSheafShortComplexExactIffLocallyLifts
import Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosure
import Development.EtaleCohomology.TateTwists.EtaleInjectiveResolutionBasicProperties
import Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomExtendsAlongQuasiIso
import Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapOnClasses
import Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapCompCompatible
import Development.EtaleCohomology.TateTwists.EtaleRootsOfUnityReductionMapGenerator
import Development.EtaleCohomology.TateTwists.EtaleRestrictScalarsResolutionCompatible

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.BockCut

abbrev TZ (q : ℕ) (i : ℤ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q i)

def genZ {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Sec (TZ q i) U := twGen i ζ

def IsRed (Q q : ℕ) (i : ℤ) (π : TZ Q i ⟶ TZ q i) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → Sec.map π (genZ i ζ) = genZ i ξ

def DerDict : Prop := ∀ (R : Type) [CommRing R] (K : Cx R),
  letI := HasDerivedCategory.standard (Shv R)
  ∃ e : ∀ (F : Shv R) (n : ℤ), HK R K F n ≃+ (DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor (Shv R) 0).obj F)⟦n⟧),
    ∀ {F G : Shv R} (φ : F ⟶ G) (n : ℤ) (x : HK R K F n),
      e G n (HK.post R K φ n x) = e F n x ≫ ((DerivedCategory.singleFunctor (Shv R) 0).map φ)⟦n⟧'

def NatLES : Prop := ∀ (R : Type) [CommRing R] (K : Cx R),
  ∃ d : ∀ (S : ShortComplex (Shv R)), S.ShortExact → ∀ n : ℤ, HK R K S.X₃ n →+ HK R K S.X₁ (n + 1),
    (∀ (S : ShortComplex (Shv R)) (hS : S.ShortExact) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (d S hS n) ∧
      Function.Exact (d S hS n) (HK.post R K S.f (n + 1))) ∧
    ∀ (S T : ShortComplex (Shv R)) (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℤ) (x : HK R K S.X₃ n),
      HK.post R K φ.τ₁ (n + 1) (d S hS n x) = d T hT n (HK.post R K φ.τ₃ n x)

def ZHom : Prop := ∀ (F G : Shv ℤ) (f : ∀ U : Scheme.{0}, Sec F U →+ Sec G U),
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec F U), Sec.res g (f U a) = f V (Sec.res g a)) →
  ∃ φ : F ⟶ G, ∀ (U : Scheme.{0}) (a : Sec F U), Sec.map φ a = f U a

def RedEx : Prop := ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ i : ℤ, ∃ π : TZ Q i ⟶ TZ q i, IsRed Q q i π

def TwExt : Prop := ∀ (Q : ℕ) [NeZero Q] (i : ℤ) (M : Shv ℤ) (φ ψ : TZ Q i ⟶ M),
  (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map φ (genZ i ζ) = Sec.map ψ (genZ i ζ)) → φ = ψ

def RedEpi : Prop := ∀ (l : ℕ) [Fact l.Prime] (c a : ℕ), a ≤ c → ∀ (i : ℤ) (π : TZ (l ^ c) i ⟶ TZ (l ^ a) i),
  IsRed (l ^ c) (l ^ a) i π → Epi π

def RedKer : Prop := ∀ (Q e q : ℕ) [NeZero Q], Q = e * q → ∀ (i : ℤ) (π : TZ Q i ⟶ TZ q i), IsRed Q q i π →
  ∀ (U : Scheme.{0}) (y : Sec (TZ Q i) U), (Sec.map π y = 0 ↔ e • y = 0) ∧
    (Sec.map π y = 0 → Loc U fun V g => ∃ x : Sec (TZ Q i) V, q • x = Sec.res g y)

def TwSES : Prop := ∀ (l : ℕ) [Fact l.Prime] (b a : ℕ) (i : ℤ) (π₁ : TZ (l ^ (b + a)) i ⟶ TZ (l ^ a) i)
  (π₂ : TZ (l ^ (b + a)) i ⟶ TZ (l ^ b) i), IsRed _ _ i π₁ → IsRed _ _ i π₂ →
  ∃ ι : TZ (l ^ a) i ⟶ TZ (l ^ (b + a)) i, π₁ ≫ ι = l ^ b • 𝟙 _ ∧ ∃ w : ι ≫ π₂ = 0, (ShortComplex.mk ι π₂ w).ShortExact

def RestrRes : Prop := ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
  ∃ (T : Cx R) (σ : SemiMap (res S F) T) (ε : sgl ((restr φ).obj F) ⟶ T), QuasiIso ε ∧
    (∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (σ.app U s)) ∧
    ∀ (U : Scheme.{0}) (a : Sec F U), Sec.map (ε.f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) =
      σ.app U 0 (Sec.map (resι S F) a)

def SemiUniq : Prop := ∀ (S : Type) [CommRing S] (F : Shv S) (G : Shv ℤ) (ρ ρ' : SemiMap (res S F) (res ℤ G)),
  (∀ (U : Scheme.{0}) (a : Sec F U), ρ.app U 0 (Sec.map (resι S F) a) = ρ'.app U 0 (Sec.map (resι S F) a)) →
  ∀ (E : Spc) (n : ℤ) (x : H S E F n), ρ.op.app E n x = ρ'.op.app E n x

def RedPost : Prop := ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (π : TZ Q i ⟶ TZ q i), IsRed Q q i π →
  ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i),
    restrH (Int.castRingHom (ZMod q)) E (tw q i) n (red Q q E n i x) =
      HK.post ℤ ((chains ℤ).obj E) π n (restrH (Int.castRingHom (ZMod Q)) E (tw Q i) n x)

theorem post_comp (hD : DerDict) {R : Type} [CommRing R] (K : Cx R) {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) (n : ℤ)
    (x : HK R K F n) : HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x) := by
  obtain ⟨e, he⟩ := hD R K
  apply (e M n).injective
  rw [he, he, he, Functor.map_comp, Functor.map_comp, Category.assoc]

theorem post_nsmul (hD : DerDict) {R : Type} [CommRing R] (K : Cx R) {F : Shv R} (c : ℕ) (n : ℤ)
    (x : HK R K F n) : HK.post R K (c • 𝟙 F) n x = c • x := by
  obtain ⟨e, he⟩ := hD R K
  let := HasDerivedCategory.standard (Shv R)
  apply (e F n).injective
  rw [he, Functor.map_nsmul, Functor.map_nsmul, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Preadditive.comp_nsmul, Category.comp_id, map_nsmul]

theorem red_comp (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) (hE : TwExt) {Q q r : ℕ} [NeZero Q] (h1 : q ∣ Q) (h2 : r ∣ q) {i : ℤ}
    {π₁ : TZ Q i ⟶ TZ q i} {π₂ : TZ q i ⟶ TZ r i} {π₃ : TZ Q i ⟶ TZ r i} (a : IsRed Q q i π₁) (b : IsRed q r i π₂)
    (c : IsRed Q r i π₃) : π₁ ≫ π₂ = π₃ := by
  have : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) h1⟩
  refine hE Q i _ _ _ fun U ζ => ?_
  obtain ⟨ξ, hξ⟩ := (hP Q Γ(U, ⊤)).2.2.2.2.2 q h1 ζ
  obtain ⟨η, hη⟩ := (hP q Γ(U, ⊤)).2.2.2.2.2 r h2 ξ
  have h : η.1 = ζ.1 ^ (Q / r) := by rw [hη, hξ, ← pow_mul, Nat.div_mul_div h1 h2]
  rw [c U ζ η h, ← b U ξ η hη, ← a U ζ ξ hξ]
  rfl

theorem exact_tr {A B C A' B' C' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup A']
    [AddCommGroup B'] [AddCommGroup C'] (ea : A ≃+ A') (eb : B ≃+ B') (ec : C ≃+ C') {f : A → B} {g : B → C}
    {f' : A' → B'} {g' : B' → C'} (hf : ∀ x, eb (f x) = f' (ea x)) (hg : ∀ x, ec (g x) = g' (eb x))
    (h : Function.Exact f' g') : Function.Exact f g := by
  intro y
  rw [← ec.map_eq_zero_iff, hg, h]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨ea.symm x, eb.injective (by rw [hf, ea.apply_symm_apply, hx])⟩
  · rintro ⟨x, rfl⟩
    exact ⟨ea x, (hf x).symm⟩

theorem goal_of (hD : DerDict) (hL : NatLES) (hX : RedEx) (hE : TwExt) (hEpi : RedEpi) (hS : TwSES) (hR : RedPost)
    (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) : LateralTheory.KummerTheory.Bock := by
  intro _ h8 _ _ l _ b E i _
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hnz : ∀ c : ℕ, NeZero (l ^ c) := fun c => ⟨pow_ne_zero _ hl⟩
  choose π hπ using fun (c a : ℕ) (h : a ≤ c) => hX (l ^ c) (l ^ a) (pow_dvd_pow l h) i
  have hc : ∀ (c a r : ℕ) (h1 : a ≤ c) (h2 : r ≤ a), π c a h1 ≫ π a r h2 = π c r (h2.trans h1) := fun c a r h1 h2 =>
    red_comp hP hE (pow_dvd_pow l h1) (pow_dvd_pow l h2) (hπ _ _ _) (hπ _ _ _) (hπ _ _ _)
  choose ι hι w hw using fun a : ℕ => hS l b a i (π (b + a) a (by omega)) (π (b + a) b (by omega)) (hπ _ _ _) (hπ _ _ _)
  have hsq : ∀ a : ℕ, π (a + 1) a (by omega) ≫ ι a = ι (a + 1) ≫ π (b + (a + 1)) (b + a) (by omega) := fun a => by
    have := hEpi l (b + (a + 1)) (a + 1) (by omega) i _ (hπ _ _ (Nat.le_add_left _ _))
    rw [← cancel_epi (π (b + (a + 1)) (a + 1) (Nat.le_add_left _ _)), ← Category.assoc, ← Category.assoc, hι, hc,
      ← hc (b + (a + 1)) (b + a) a (Nat.le_succ _) (Nat.le_add_left a b), Category.assoc, hι, Preadditive.comp_nsmul,
      Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]
  obtain ⟨d, hd, hnat⟩ := hL ℤ ((chains ℤ).obj E)
  let e : ∀ (c : ℕ) (n : ℤ), Ht (l ^ c) E n i ≃+ HK ℤ ((chains ℤ).obj E) (TZ (l ^ c) i) n := fun c n =>
    AddEquiv.ofBijective (restrH (Int.castRingHom (ZMod (l ^ c))) E (tw (l ^ c) i) n) (h8 ℤ _ _ E _ n)
  have he : ∀ (c a : ℕ) (h : a ≤ c) (n : ℤ) (x : Ht (l ^ c) E n i),
      e a n (red (l ^ c) (l ^ a) E n i x) = HK.post ℤ _ (π c a h) n (e c n x) := fun c a h n x =>
    hR _ _ (pow_dvd_pow l h) i _ (hπ c a h) E n x
  let u : ∀ (a : ℕ) (n : ℤ), Ht (l ^ a) E n i →+ Ht (l ^ (b + a)) E n i := fun a n =>
    ((e (b + a) n).symm.toAddMonoidHom.comp (HK.post ℤ _ (ι a) n)).comp (e a n).toAddMonoidHom
  let δ : ∀ (a : ℕ) (n : ℤ), Ht (l ^ b) E n i →+ Ht (l ^ a) E (n + 1) i := fun a n =>
    ((e a (n + 1)).symm.toAddMonoidHom.comp (d _ (hw a) n)).comp (e b n).toAddMonoidHom
  have hu : ∀ a n x, e (b + a) n (u a n x) = HK.post ℤ _ (ι a) n (e a n x) := fun a n x => (e (b + a) n).apply_symm_apply _
  have hδ : ∀ a n x, e a (n + 1) (δ a n x) = d _ (hw a) n (e b n x) := fun a n x => (e a (n + 1)).apply_symm_apply _
  refine ⟨u, δ, fun a n => ⟨?_, ?_, ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩⟩
  · exact exact_tr _ _ _ (hu a n) (he _ _ (by omega) n) (hd _ (hw a) n).1
  · exact exact_tr _ _ _ (he _ _ (by omega) n) (hδ a n) (hd _ (hw a) n).2.1
  · exact exact_tr _ _ _ (hδ a n) (hu a (n + 1)) (hd _ (hw a) n).2.2
  · apply (e (b + a) n).injective
    rw [hu, he _ _ (by omega), ← post_comp hD, hι, post_nsmul hD, map_nsmul]
  · apply (e a (n + 1)).injective
    let φ : ShortComplex.mk _ _ (w (a + 1)) ⟶ ShortComplex.mk _ _ (w a) :=
      { τ₁ := π (a + 1) a (by omega)
        τ₂ := π (b + (a + 1)) (b + a) (by omega)
        τ₃ := 𝟙 _
        comm₁₂ := hsq a
        comm₂₃ := (hc _ _ _ _ _).trans (Category.comp_id _).symm }
    have h1 := hnat _ _ (hw (a + 1)) (hw a) φ n (e b n x)
    have h2 := post_nsmul hD ((chains ℤ).obj E) 1 n (e b n x)
    rw [one_smul, one_smul] at h2
    rw [he _ _ (by omega), hδ, hδ]
    exact h1.trans (congrArg _ h2)
  · apply (e (b + a) n).injective
    rw [he _ _ (by omega), hu, hu, he _ _ (by omega), ← post_comp hD, ← post_comp hD, hsq]

end LateralTheory.KummerTheory.BockCut
