import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem existsUnique_pairing_eq_character {H M : Type} [CommGroup H] [CommMonoid M] (N : ℕ)
    [NeZero N] [HasEnoughRootsOfUnity M N] [hfin : Finite {x : H // x ^ N = 1}]
    (W : H → H → Mˣ → Prop)
    (hex : ∀ x y : H, x ^ N = 1 → y ^ N = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hskew : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x : H, x ^ N = 1 → (∀ y : H, y ^ N = 1 → W x y 1) → x = 1)
    (χ : {x : H // x ^ N = 1} → Mˣ)
    (hχ : ∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) :
    ∃! b : H, b ^ N = 1 ∧ ∀ x : {x : H // x ^ N = 1}, W x.1 b (χ x) := by
  classical
  let G : Subgroup H := (powMonoidHom N : H →* H).ker
  have hG : ∀ x : G, (x : H) ^ N = 1 := fun x => x.2
  haveI : Finite G := hfin
  choose e he huniq using fun x y : G => hex x y (hG x) (hG y)
  have hel : ∀ x x' y : G, e (x * x') y = e x y * e x' y := fun x x' y =>
    (huniq _ _ _ (hmul _ _ _ _ _ (he x y) (he x' y))).symm
  have hes : ∀ x y : G, e y x = (e x y)⁻¹ := fun x y =>
    (huniq _ _ _ (hskew _ _ _ (he x y))).symm
  have her : ∀ x y y' : G, e x (y * y') = e x y * e x y' := fun x y y' => by
    rw [hes (y * y') x, hel, hes y x, hes y' x, mul_inv]
  let Φ : G →* (G →* Mˣ) := MonoidHom.mk' (fun b => MonoidHom.mk' (fun x => e x b)
    (fun x x' => hel x x' b)) (fun b b' => MonoidHom.ext fun x => her x b b')
  have hΦ : ∀ b x, Φ b x = e x b := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    refine Subtype.ext (hnd b (hG b) fun y hy => ?_)
    have h1 : e ⟨y, hy⟩ b = 1 := by rw [← hΦ, hb]; rfl
    have h2 := he b ⟨y, hy⟩
    rwa [hes, h1, inv_one] at h2
  haveI : HasEnoughRootsOfUnity M (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd M (n := N)
      (Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hG g))
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G M
  haveI : Finite (G →* Mˣ) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  let χ' : G →* Mˣ := MonoidHom.mk' (fun x => χ ⟨x.1, hG x⟩)
    (fun x y => hχ ⟨x.1, hG x⟩ ⟨y.1, hG y⟩)
  obtain ⟨b, hb⟩ := hbij.2 χ'
  refine ⟨b, ⟨hG b, fun x => ?_⟩, ?_⟩
  · have h1 : e ⟨x.1, x.2⟩ b = χ x := by rw [← hΦ, hb]; rfl
    rw [← h1]
    exact he ⟨x.1, x.2⟩ b
  · rintro b' ⟨hb', h⟩
    have : (⟨b', hb'⟩ : G) = b := by
      apply hinj
      rw [hb]
      ext1 x
      rw [hΦ]
      exact (huniq x ⟨b', hb'⟩ _ (h ⟨x.1, hG x⟩)).symm
    exact congrArg Subtype.val this

theorem finite_torsion_of_isFinite_mul (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (N : ℕ) [IsFinite (mulA P.A N).left] :
    Finite {x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ N = 1} := by
  haveI := P.isAb.proper
  let p := IsLocalRing.closedPoint K
  let o : P.A.left := (1 : baseOver (Spec (CommRingCat.of K)) ⟶ P.A).left p
  have hfib := Scheme.Hom.finite_preimage_singleton (mulA P.A N).left o
  haveI := hfib.to_subtype
  refine Finite.of_injective (β := (mulA P.A N).left ⁻¹' {o}) (fun x => ⟨x.1.left p, ?_⟩) ?_
  · have h : x.1 ≫ mulA P.A N = 1 := by rw [mulA, MonObj.comp_pow, Category.comp_id, x.2]
    change (x.1 ≫ mulA P.A N).left p = o
    rw [h]
  · intro x y hxy
    refine Subtype.ext (Over.OverMorphism.ext ?_)
    exact ext_of_apply_closedPoint_eq P.A.hom (Over.w x.1) (Over.w y.1) (congrArg Subtype.val hxy)

theorem hasEnoughRootsOfUnity_globalSections (K : Type) [Field K] [IsAlgClosed K] (N : ℕ)
    (hN : (N : K) ≠ 0) :
    HasEnoughRootsOfUnity Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) N := by
  haveI : NeZero (N : K) := ⟨hN⟩
  haveI : NeZero N := .of_neZero_natCast K
  let e : K ≃+* Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  exact MulEquiv.hasEnoughRootsOfUnity (e.toMulEquiv.restrictRootsOfUnity N)

theorem charPair_of_weil :
    WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → WeilNondegSt → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → CharPairSt := by
  intro hW hskew hnd hM K _ _ P N hN χ hχ
  haveI : NeZero (N : K) := ⟨hN⟩
  haveI : NeZero N := .of_neZero_natCast K
  haveI := (hM _ P N (NeZero.one_le)).1
  haveI := finite_torsion_of_isFinite_mul K P N
  haveI := hasEnoughRootsOfUnity_globalSections K N hN
  obtain ⟨hex, hmul, -, -⟩ := hW _ P N (baseOver (Spec (CommRingCat.of K)))
  exact existsUnique_pairing_eq_character N (fun x y c => WeilIs P.A P.L N x y c) hex hmul
    (hskew _ P N _).2.1 (hnd K P N hN) χ hχ

end GlobalTheory
