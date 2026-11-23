import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowEqTorus
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionZerosTwistLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueDescendOfTorsionInvariant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusProdSec
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FewZeros

theorem card_mono {α : Type} {p q : α → Prop} (hq : Finite {x // q x}) (h : ∀ x, p x → q x) :
    Finite {x // p x} ∧ Nat.card {x // p x} ≤ Nat.card {x // q x} :=
  ⟨Finite.of_injective _ (Subtype.impEmbedding p q h).injective,
    Nat.card_le_card_of_injective _ (Subtype.impEmbedding p q h).injective⟩

theorem sec_eq_zero_of_dim_zero {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = 0)
    {M : LB (Out.baseOver (Sp K) ⊗ P.A).left} (s : M.Sec)
    (hs : ¬ ⊤ ≤ (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left ⁻¹ᵁ Out.nonzeroLocus s) (j : M.ι) :
    s.f j = 0 := by
  have := polAV_isIntegral_of_isAlgClosed K P
  have : Etale P.A.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 (hg ▸ P.smoothDim)
  let e : Sp K ⟶ P.A.left := (1 : Out.baseOver (Sp K) ⟶ P.A).left
  have := isOpenImmersion_of_section_of_etale P.A.hom e (Over.w _)
  have : IsDominant e := ⟨e.isOpenEmbedding.isOpen_range.dense ⟨_, (default : PrimeSpectrum K), rfl⟩⟩
  have : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  let z : Sp K ⟶ (Out.baseOver (Sp K) ⊗ P.A).left := (Out.ptSecT P.A (1 : Out.baseOver (Sp K) ⟶ P.A)).left
  have hz : z = e ≫ inv (snd (Out.baseOver (Sp K)) P.A).left := by
    rw [IsIso.eq_comp_inv]
    exact congrArg (·.left) (lift_snd (𝟙 _) (1 : Out.baseOver (Sp K) ⟶ P.A))
  have hd : IsDominant z := by rw [hz]; infer_instance
  have : IsReduced (Out.baseOver (Sp K) ⊗ P.A).left :=
    isReduced_of_isOpenImmersion (snd (Out.baseOver (Sp K)) P.A).left
  by_contra hne
  have hb : ((Out.baseOver (Sp K) ⊗ P.A).left.basicOpen (s.f j) : Set (Out.baseOver (Sp K) ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => hne ((basicOpen_eq_bot_iff _).1 (TopologicalSpace.Opens.ext h))
  obtain ⟨y, hy⟩ := hd.denseRange.exists_mem_open (TopologicalSpace.Opens.isOpen _) hb
  refine hs fun y' _ => ?_
  have : y' = y := Subsingleton.elim (α := PrimeSpectrum K) _ _
  subst this
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩

theorem finite_torsion_of_mulEquiv {G G' : Type} [Monoid G] [Monoid G'] (e : G ≃* G') (n : ℕ)
    (h : Finite {x : G // x ^ n = 1}) : Finite {x : G' // x ^ n = 1} :=
  Finite.of_equiv _ (e.toEquiv.subtypeEquiv (p := fun b => b ^ n = 1) (q := fun b => b ^ n = 1) fun b =>
    (by rw [← map_pow, e.map_eq_one_iff] : e b ^ n = 1 ↔ _).symm)

theorem exists_hom_of_extension {T G₀ B₀ G B : Type} [Group T] [CommGroup G₀] [Group B₀] [Group G] [Group B]
    (i : T →* G₀) (q : G₀ →* B₀) (eG : G₀ ≃* G) (eB : B₀ ≃* B) (n : ℕ) (hi : Function.Injective i)
    (hqi : ∀ t, q (i t) = 1) (hker : ∀ x, q x = 1 → ∃ t, i t = x) (hq : Function.Surjective q)
    (hT : ∀ t : T, ∃ s, s ^ n = t) (hT' : Finite {t : T // t ^ n = 1}) :
    ∃ p : G →* B, Function.Surjective p ∧ (∀ x, p x = 1 → ∃ y, p y = 1 ∧ y ^ n = x) ∧
      (Finite {b : B // b ^ n = 1} → Finite {x : G // x ^ n = 1}) ∧ ∀ x, p (eG x) = eB (q x) := by
  let p := (eB.toMonoidHom.comp q).comp eG.symm.toMonoidHom
  have hp : ∀ x, p (eG x) = eB (q x) := fun x => by simp [p]
  refine ⟨p, (eB.surjective.comp hq).comp eG.symm.surjective, fun x hx => ?_, fun hB => ?_, hp⟩
  · obtain ⟨x, rfl⟩ := eG.surjective x
    rw [hp, eB.map_eq_one_iff] at hx
    obtain ⟨t, rfl⟩ := hker x hx
    obtain ⟨s, rfl⟩ := hT t
    exact ⟨eG (i s), by rw [hp, hqi, map_one], by rw [map_pow, map_pow]⟩
  · exact finite_torsion_of_mulEquiv eG n (SemiAbTorsion.finite_pow_eq_one_of_extension i q hi hker n hT'
      (finite_torsion_of_mulEquiv eB.symm n hB))

theorem card_lt_of_quotient {G B : Type} [CommGroup G] [CommGroup B] (p : G →* B) (n m : ℕ)
    (hp : Function.Surjective p) (hk : ∀ x, p x = 1 → ∃ y, p y = 1 ∧ y ^ n = x)
    (hG : Finite {x : G // x ^ n = 1}) (Z : G → Prop) (Z' : B → Prop) (hZ : ∀ x, Z x → Z' (p x))
    (h : m * Nat.card {b : B // b ^ n = 1 ∧ Z' b} < Nat.card {b : B // b ^ n = 1}) :
    m * Nat.card {x : G // x ^ n = 1 ∧ Z x} < Nat.card {x : G // x ^ n = 1} := by
  have lift : ∀ b : B, b ^ n = 1 → ∃ x : G, x ^ n = 1 ∧ p x = b := fun b hb => by
    obtain ⟨x, rfl⟩ := hp b
    obtain ⟨y, hy, hyx⟩ := hk (x ^ n) (by rw [map_pow, hb])
    exact ⟨x * y⁻¹, by rw [mul_pow, inv_pow, hyx, mul_inv_cancel], by rw [map_mul, map_inv, hy, inv_one, _root_.mul_one]⟩
  choose s hs hps using lift
  let T := {t : G // t ^ n = 1 ∧ p t = 1}
  have key : ∀ W : B → Prop, Nat.card {x : G // x ^ n = 1 ∧ W (p x)} =
      Nat.card {b : B // b ^ n = 1 ∧ W b} * Nat.card T := fun W => by
    rw [← Nat.card_prod]
    refine (Nat.card_eq_of_bijective (fun a : {b : B // b ^ n = 1 ∧ W b} × T =>
      (⟨s a.1.1 a.1.2.1 * a.2.1, by rw [mul_pow, hs, a.2.2.1, _root_.mul_one], by
        rw [map_mul, hps, a.2.2.2, _root_.mul_one]; exact a.1.2.2⟩ : {x : G // x ^ n = 1 ∧ W (p x)})) ⟨?_, ?_⟩).symm
    · rintro ⟨⟨b, hb⟩, ⟨t, ht⟩⟩ ⟨⟨b', hb'⟩, ⟨t', ht'⟩⟩ e
      have e₁ : s b hb.1 * t = s b' hb'.1 * t' := congrArg Subtype.val e
      have e₂ := congrArg p e₁
      rw [map_mul, map_mul, hps, hps, ht.2, ht'.2, _root_.mul_one, _root_.mul_one] at e₂
      subst e₂
      obtain rfl := mul_left_cancel e₁
      rfl
    · rintro ⟨x, hx, hW⟩
      have hb : p x ^ n = 1 := by rw [← map_pow, hx, map_one]
      exact ⟨(⟨p x, hb, hW⟩, ⟨(s (p x) hb)⁻¹ * x, by rw [mul_pow, inv_pow, hs, hx, inv_one, _root_.mul_one], by
        rw [map_mul, map_inv, hps, inv_mul_cancel]⟩), Subtype.ext (mul_inv_cancel_left _ _)⟩
  have fin : ∀ W : G → Prop, Finite {x : G // x ^ n = 1 ∧ W x} := fun W =>
    (card_mono hG fun _ h => h.1).1
  have := fin fun t => p t = 1
  have : Nonempty T := ⟨⟨1, one_pow _, map_one _⟩⟩
  have hT : 0 < Nat.card T := Nat.card_pos
  have h₁ := key fun _ => True
  simp only [and_true] at h₁
  have h₂ : Nat.card {x : G // x ^ n = 1 ∧ Z x} ≤ Nat.card {x : G // x ^ n = 1 ∧ Z' (p x)} :=
    (card_mono (fin fun x => Z' (p x)) fun _ h => ⟨h.1, hZ _ h.2⟩).2
  rw [key] at h₂
  rw [h₁]
  calc _ ≤ m * Nat.card {b : B // b ^ n = 1 ∧ Z' b} * Nat.card T := by
        rw [_root_.mul_assoc]; exact Nat.mul_le_mul_left _ h₂
    _ < _ := Nat.mul_lt_mul_of_pos_right h hT

theorem exists_sec_prod {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (θ : L.Sec) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ (fun _ => 1) φ' ε') :
    ∃ s : (LB.LinComb L φ' ε').Sec, ∀ y, y ∈ Out.nonzeroLocus s ↔ ∀ i, φ i y ∈ Out.nonzeroLocus θ := by
  obtain ⟨s, hs⟩ := exists_sec hL h (BoxSection.prodSec L φ fun _ => θ)
  refine ⟨s, fun y => ?_⟩
  choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
  have hJ' : Good L y J := hJ
  have e : y ∈ Out.nonzeroLocus s ↔ y ∈ Out.nonzeroLocus (BoxSection.prodSec L φ fun _ => θ) :=
    (mem_nonzeroLocus_iff_pull s (𝟙 Y) y (hJ'.mem φ' (𝟙 Y))).trans ((congrArg IsUnit (hs _ (𝟙 Y) y J hJ')).to_iff.trans
      (mem_nonzeroLocus_iff_pull (BoxSection.prodSec L φ fun _ => θ) (𝟙 Y) y (hJ'.mem φ (𝟙 Y))).symm)
  refine e.trans ⟨fun h i => ?_, BoxSection.mem_nonzeroLocus_prodSec L φ _ y⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hy : y ∈ LB.wchart L φ l := Y.basicOpen_le _ hl
  have h₁ := (Scheme.mem_basicOpen _ _ y hy).1 hl
  erw [map_prod] at h₁
  have h₂ := (Scheme.mem_basicOpen _ _ y hy).2 (IsUnit.prod_univ_iff.1 h₁ i)
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨l i, ((Scheme.basicOpen_appLE (φ i) _ _ (LB.wchart_le L φ l i) _).le h₂).2⟩

theorem exists_sec_of_formEq_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (X ⟶ X)} {ε : K → ℤ} (h : FormEq φ ε (fun _ : PUnit => 𝟙 X) fun _ => 1) (t : (LB.LinComb L φ ε).Sec) :
    ∃ s : L.Sec, Out.nonzeroLocus s = Out.nonzeroLocus t := by
  obtain ⟨s, hs⟩ := exists_sec hL h t
  obtain ⟨s', hs'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hL (LB.isLB_linComb hL _ _) (lbIso_pull_id hL).symm s
  refine ⟨s', hs'.trans (TopologicalSpace.Opens.ext (Set.ext fun y => ?_))⟩
  choose J hJ using fun χ : X ⟶ X => exists_chart hL (χ y)
  have hJ' : Good L y J := hJ
  exact (mem_nonzeroLocus_iff_pull s (𝟙 X) y (hJ'.mem _ (𝟙 X))).trans ((congrArg IsUnit (hs _ (𝟙 X) y J hJ')).to_iff.trans
      (mem_nonzeroLocus_iff_pull t (𝟙 X) y (hJ'.mem φ (𝟙 X))).symm)

theorem card_lt_field (h : Out.Laws) (h₂ : Out.Laws2) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    (θ : P.L.Sec) (hθ : ∃ x, x ∈ Out.nonzeroLocus θ) {N n g m : ℕ} (hg : P.g ≤ g) (hN : 4 ≤ N) (hn : (n : K) ≠ 0)
    (hb : m * (N ^ g * g.factorial) < n ^ 2) (c : Out.baseOver (Sp K) ⟶ P.A) :
    m * Nat.card {b : Out.baseOver (Sp K) ⟶ P.A // b ^ n = 1 ∧ ¬ ⊤ ≤ (c * b).left ⁻¹ᵁ Out.nonzeroLocus θ} <
      Nat.card {b : Out.baseOver (Sp K) ⟶ P.A // b ^ n = 1} := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun e => hn (by rw [e, Nat.cast_zero])
  have hcard : Nat.card {b : Out.baseOver (Sp K) ⟶ P.A // b ^ n = 1} = n ^ (2 * P.g) :=
    (h.mulN (Sp K) P n hn1).2.2.2.2 K (𝟙 _) hn
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s : LB.Sec (Out.twistLB P.A P.L ((M + 1) * 1) c), ∀ y, y ∈ Out.nonzeroLocus s ↔
      ∀ i : Option (Fin M), (i.elim (Out.translPt P.A c).left fun _ => (snd (Out.baseOver (Sp K)) P.A).left) y ∈
        Out.nonzeroLocus θ :=
    exists_sec_prod P.isLB θ _ fun U _ f => by
      simp [Fintype.prod_option, Fin.prod_univ_two, _root_.mul_comm]
  have hint := polAV_isIntegral_of_isAlgClosed K P
  have i₁ : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  have hsurj : Function.Surjective (Out.translPt P.A c).left := fun x => by
    let b : P.A ⟶ Out.baseOver (Sp K) := Over.homMk P.A.hom (Category.comp_id _)
    have e : lift b ((b ≫ c)⁻¹ * 𝟙 P.A) ≫ Out.translPt P.A c = 𝟙 P.A := by
      rw [Out.translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, ← Hom.mul_def, mul_inv_cancel_left]
    exact ⟨(lift b ((b ≫ c)⁻¹ * 𝟙 P.A)).left x, congrArg (fun q : P.A ⟶ P.A => q.left x) e⟩
  have hs0 : ∃ j, s.f j ≠ 0 := by
    obtain ⟨x, hx⟩ := hθ
    have : IrreducibleSpace (Out.baseOver (Sp K) ⊗ P.A).left :=
      (snd (Out.baseOver (Sp K)) P.A).left.homeomorph.symm.surjective.irreducibleSpace
        (snd (Out.baseOver (Sp K)) P.A).left.homeomorph.symm.continuous
    obtain ⟨y₁, rfl⟩ := hsurj x
    obtain ⟨y₂, hy₂⟩ := (snd (Out.baseOver (Sp K)) P.A).left.homeomorph.surjective ((Out.translPt P.A c).left y₁)
    obtain ⟨y, hy, hy'⟩ := nonempty_preirreducible_inter
      ((Out.translPt P.A c).left ⁻¹ᵁ Out.nonzeroLocus θ).isOpen
      ((snd (Out.baseOver (Sp K)) P.A).left ⁻¹ᵁ Out.nonzeroLocus θ).isOpen ⟨y₁, hx⟩
      ⟨y₂, show (snd (Out.baseOver (Sp K)) P.A).left.homeomorph y₂ ∈ Out.nonzeroLocus θ from hy₂ ▸ hx⟩
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 ((hs y).2 fun i => by
      cases i
      exacts [hy, hy'])
    exact ⟨j, fun e => by rw [e, Scheme.basicOpen_zero] at hj; exact hj⟩
  have hz : ∀ b : Out.baseOver (Sp K) ⟶ P.A, ¬ ⊤ ≤ (c * b).left ⁻¹ᵁ Out.nonzeroLocus θ →
      ¬ ⊤ ≤ (Out.ptSecT P.A b).left ⁻¹ᵁ Out.nonzeroLocus s := fun b hb hh => hb fun z _ => by
    have e : Out.ptSecT P.A b ≫ Out.translPt P.A c = c * b := by
      rw [Out.ptSecT, Out.translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, Hom.mul_def]
    rw [← e]
    exact (hs _).1 (hh (Set.mem_univ z)) none
  rcases Nat.eq_zero_or_pos P.g with h0 | h0
  · rw [h0] at hcard
    have hsub := (Nat.card_eq_one_iff_unique.1 hcard).1
    have : IsEmpty {b : Out.baseOver (Sp K) ⟶ P.A // b ^ n = 1 ∧ ¬ ⊤ ≤ (c * b).left ⁻¹ᵁ Out.nonzeroLocus θ} := by
      refine ⟨fun ⟨b, hb₁, hb₂⟩ => ?_⟩
      obtain rfl : b = 1 := congrArg Subtype.val (hsub.elim ⟨b, hb₁⟩ ⟨1, one_pow _⟩)
      obtain ⟨j, hj⟩ := hs0
      exact hj (sec_eq_zero_of_dim_zero P h0 s (hz 1 hb₂) j)
    rw [Nat.card_of_isEmpty, hcard]
    simp
  have h₄ := card_torsion_zeros_twist_le h h₂ K P (M + 1) 1 n c h0 hN le_rfl hn s hs0
  have f₁ : Finite {b : Out.baseOver (Sp K) ⟶ P.A // b ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have h₅ : Nat.card {b : Out.baseOver (Sp K) ⟶ P.A // b ^ n = 1 ∧ ¬ ⊤ ≤ (c * b).left ⁻¹ᵁ Out.nonzeroLocus θ} ≤ _ :=
    (card_mono (card_mono f₁ fun _ h => h.1).1 fun _ h => ⟨h.1, hz _ h.2⟩).2.trans h₄
  have e : n ^ (2 * P.g) = n ^ 2 * n ^ (2 * P.g - 2) := by rw [← pow_add]; congr 1; omega
  have h₇ : (M + 1) ^ P.g * P.g.factorial ≤ (M + 1) ^ g * g.factorial :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hg) (Nat.factorial_le hg)
  rw [hcard, e]
  calc _ ≤ m * ((M + 1) ^ g * g.factorial) * n ^ (2 * P.g - 2) := by
        rw [_root_.mul_assoc]
        exact Nat.mul_le_mul_left _ (h₅.trans (Nat.mul_le_mul_right _ (by rwa [_root_.mul_one])))
    _ < _ := Nat.mul_lt_mul_of_pos_right hb (by positivity)

theorem card_lt_fibre (h : Out.Laws) (h₂ : Out.Laws2) {S : Scheme.{0}} (P : Out.PolAV S) {K : Type} [Field K]
    [IsAlgClosed K] (r : Sp K ⟶ S) (θ : P.L.Sec) (hθ : ∃ x ∈ Out.nonzeroLocus θ, P.A.hom x ∈ Set.range r)
    {N n g m : ℕ} (hg : P.g ≤ g) (hN : 4 ≤ N) (hn : (n : K) ≠ 0) (hb : m * (N ^ g * g.factorial) < n ^ 2)
    (c : Over.mk r ⟶ P.A) :
    m * Nat.card {b : Over.mk r ⟶ P.A // b ^ n = 1 ∧ ¬ ⊤ ≤ (c * b).left ⁻¹ᵁ Out.nonzeroLocus θ} <
      Nat.card {b : Over.mk r ⟶ P.A // b ^ n = 1} := by
  obtain ⟨P', π, hπ, hg', hmul, w, hw⟩ := h.polBaseChange S (Sp K) r P
  obtain ⟨s₀, hs₀⟩ : ∃ s : (P.L.pull π).Sec, ∀ y, y ∈ Out.nonzeroLocus s ↔ ∀ _ : PUnit, π y ∈ Out.nonzeroLocus θ :=
    exists_sec_prod P.isLB θ (fun _ : PUnit => π) fun _ _ _ => rfl
  obtain ⟨s, hs⟩ := exists_sec_nonzeroLocus_eq_of_lbIso P'.isLB (LB.isLB_linComb P.isLB _ _)
    (LBIso.symm ⟨w, hw⟩) s₀
  have hs' : Out.nonzeroLocus s = π ⁻¹ᵁ Out.nonzeroLocus θ :=
    hs.trans (TopologicalSpace.Opens.ext (Set.ext fun y => (hs₀ y).trans ⟨fun h => h ⟨⟩, fun h _ => h⟩))
  let φ : (Out.baseOver (Sp K) ⟶ P'.A) → (Over.mk r ⟶ P.A) := fun x => Over.homMk (x.left ≫ π) (by
    change (x.left ≫ π) ≫ P.A.hom = r
    rw [Category.assoc, hπ.w, ← Category.assoc, Over.w x]
    exact Category.id_comp _)
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y e => Over.OverMorphism.ext (hπ.hom_ext (congrArg (·.left) e)
      ((Over.w x).trans (Over.w y).symm)), fun x => ?_⟩
    exact ⟨Over.homMk (hπ.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp _).symm)) (hπ.lift_snd _ _ _),
      Over.OverMorphism.ext (hπ.lift_fst _ _ _)⟩
  have hmul' : ∀ x y, φ (x * y) = φ x * φ y := fun x y => by
    let u : Over.mk r ⟶ Over.mk ((Out.baseOver (Sp K)).hom ≫ r) := Over.homMk (𝟙 _) (by simp)
    have e : ∀ x, φ x = u ≫ Out.toBase hπ.w x := fun x => Over.OverMorphism.ext (Category.id_comp _).symm
    rw [e, e, e, hmul, MonObj.comp_mul]
  let ψ : (Out.baseOver (Sp K) ⟶ P'.A) ≃* (Over.mk r ⟶ P.A) := MulEquiv.ofBijective (MonoidHom.mk' φ hmul') hφ
  obtain ⟨c, rfl⟩ := ψ.surjective c
  have hp : ∀ b, ψ b ^ n = 1 ↔ b ^ n = 1 := fun b => by rw [← map_pow, ψ.map_eq_one_iff]
  have H := card_lt_field h h₂ P' s (by
    obtain ⟨x, hx, z, hz⟩ := hθ
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hπ x z hz.symm
    exact ⟨y, by rw [hs']; change π y ∈ Out.nonzeroLocus θ; rwa [show π y = x from hy]⟩) (hg'.trans_le hg) hN hn hb c
  rw [← Nat.card_congr (ψ.toEquiv.subtypeEquiv (p := fun b => b ^ n = 1) (q := fun b => b ^ n = 1)
    fun b => (hp b).symm), ← Nat.card_congr (ψ.toEquiv.subtypeEquiv
      (p := fun b => b ^ n = 1 ∧ ¬ ⊤ ≤ (c * b).left ⁻¹ᵁ Out.nonzeroLocus s)
      (q := fun b => b ^ n = 1 ∧ ¬ ⊤ ≤ (ψ c * b).left ⁻¹ᵁ Out.nonzeroLocus θ) fun b => ?_)]
  · exact H
  · refine and_congr (hp b).symm ?_
    rw [hs']
    change _ ↔ ¬ ⊤ ≤ (ψ c * ψ b).left ⁻¹ᵁ Out.nonzeroLocus θ
    rw [← map_mul]
    rfl

section Unif

open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G]

theorem dim_le (U : UnifPre (maximalIdeal V) D A G) : D.toPre.P.g ≤ A.g := by
  have := U.smooth
  obtain ⟨n, W, hW, dW⟩ := H1.exists_dim G.hom (eSec G (closedPoint V))
  have all : ∀ y : Sp V, eSec G y ∈ W := fun y =>
    (congrArg (fun U => y ∈ U) (Scheme.preimage_eq_top_of_closedPoint_mem (eSec G) hW)).mpr trivial
  have unit : ∀ {S' : Scheme.{0}} (b : S' ⟶ Sp V) (y : S'),
      pullback.fst G.hom b (eSec ((Over.pullback b).obj G) y) ∈ W := fun b y =>
    (congrArg (fun g => g y ∈ W) (cubeMapOf (isGrpPullback_pullback G b)).e_comm).mpr (all _)
  have g₁ : n = A.g := by
    have := A.smoothDim
    have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
    have d : SmoothOfRelativeDimension (0 + A.g) (pullback.snd G.hom (jK V)) := by
      rw [show pullback.snd G.hom (jK V) = U.gen.hom.left ≫ A.A.hom from (Over.w U.gen.hom).symm]
      infer_instance
    exact (H1.dim_base (IsPullback.of_hasPullback _ _) dW d _
      (unit (jK V) (default : PrimeSpectrum (FractionRing V)))).trans (zero_add _)
  let c := U.gt 0
  have := c.q_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  have dT := H1.torus_dim (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) D.toPre.X
  have : Smooth c.q.left := by
    have := dT.smooth
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback c.i c.q c.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact c.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  have : Nontrivial (V ⧸ maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [zero_add, pow_one]; exact (maximalIdeal.isMaximal V).ne_top)
  obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1)))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  obtain ⟨m, W₁, hW₁, d₁⟩ := H1.exists_dim c.q.left (eSec (thickObj V (maximalIdeal V) 0 G) y)
  have dB : SmoothOfRelativeDimension D.toPre.P.g (thickObj V (maximalIdeal V) 0 D.toPre.P.A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _)
      D.toPre.P.smoothDim
  have d₂ : SmoothOfRelativeDimension (m + D.toPre.P.g) (W₁.ι ≫ (thickObj V (maximalIdeal V) 0 G).hom) := by
    rw [← Over.w c.q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension n ((pullback.fst G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W).ι ≫
      (thickObj V (maximalIdeal V) 0 G).hom) := (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    ((isPullback_morphismRestrict _ W).paste_vert (IsPullback.of_hasPullback _ _)) dW
  have g₃ : n = m + D.toPre.P.g := by
    let W₂ := pullback.fst G.hom (thick V (maximalIdeal V) 0) ⁻¹ᵁ W
    have e₁ : SmoothOfRelativeDimension (0 + n) ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W₂ ⊓ W₁ ≤ W₂), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + (m + D.toPre.P.g))
        ((W₂ ⊓ W₁).ι ≫ (thickObj V (maximalIdeal V) 0 G).hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W₂ ⊓ W₁ ≤ W₁), Category.assoc]; infer_instance
    simpa using H1.dim_unique _ e₁ e₂ ⟨_, unit _ y, hW₁⟩
  omega

theorem exists_weight_zero [IsNoetherianRing V] (hG : GlobalFnsSt) (U : Unif (maximalIdeal V) D A G)
    (σ : H0 U.LG.L 1) : ∃ f : D.toPre.SecB 1 0, ∀ y : (thickObj V (maximalIdeal V) 0 G).left,
      fGl (maximalIdeal V) G 0 y ∈ nonzeroLocus σ ↔ pGl U.toUnifPre 0 y ∈ nonzeroLocus f := by
  have hp : pullback.fst G.hom (jK V) ≫ G.hom =
      pullback.snd G.hom (jK V) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := pullback.condition
  have hφ : ∀ k : Fin 1, (fun _ : Fin 1 => pullback.fst G.hom (jK V)) k =
      pullback.fst G.hom (jK V) ≫ (fun _ : Fin 1 => 𝟙 G.left) k := fun _ => (Category.comp_id _).symm
  let ρ := FieldBaseChange.pullOver U.LG.L (fun _ : Fin 1 => ((1 : ℕ) : ℤ)) hp hφ
  have hS := fun s₁ s₂ c => FieldBaseChange.secScal_iff hp hφ (ε := fun _ : Fin 1 => ((1 : ℕ) : ℤ)) U.LG.isLB s₁ s₂
    (pullback.snd G.hom (jK V) ≫ jK V) (algebraMap V (FractionRing V)) rfl c
  have one₁ : scal (pullback.snd G.hom (jK V) ≫ jK V) (1 : V) = 1 := by rw [scal, map_one, map_one]
  obtain ⟨Ψ, hΨ, -⟩ := (U.expand 1 le_rfl).1 (ρ σ)
  obtain ⟨f, hE, hg⟩ := IntegralExpansionLocal.main V _ le_rfl D A G U.toUnifPre 1 σ (ρ σ)
    (one₁ ▸ (hS _ _ 1).2 (by rw [map_one, one_smul])) Ψ hΨ
  have hf : ∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal V, ∃ g : D.toPre.SecB 1 α, SecIsMul D.toPre.P.A.hom a (f α) g :=
    fun α hα => by
      obtain ⟨a, ha, g, g', h₁, h₂⟩ := ThetaUnit.exists_integral_term hG D Ψ (f 0) (hg 0) α hα
      obtain rfl : g = f α := ConstFam.resF_injective D.toPre (FractionRing V) 1 α
        (((ThetaUnit.secScal_one_iff D.toPre Ψ α _).1 h₂).trans ((ThetaUnit.secScal_one_iff D.toPre Ψ α _).1 (hg α)).symm)
      exact ⟨a, ha, g', h₁⟩
  refine ⟨f 0, fun y => ?_⟩
  have hc' : pGl U.toUnifPre 0 ≫ D.toPre.P.A.hom =
      (thickObj V (maximalIdeal V) 0 G).hom ≫ spMap (Ideal.Quotient.mk (maximalIdeal V ^ (0 + 1))) :=
    Over.w (U.gt 0).pG
  obtain ⟨S, hS⟩ := expandsAt_val U.toUnifPre 0 1 σ f (hE 0)
  choose J hJ₀ using fun χ : (thickObj V (maximalIdeal V) 0 G).left ⟶ D.toPre.P.A.left =>
    exists_chart D.toPre.P.isLB (χ y)
  have hJ : Good D.toPre.P.L y J := hJ₀
  obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB (fGl (maximalIdeal V) G 0 y)
  obtain ⟨H₁, H₂⟩ := hS _ (𝟙 _) y J hJ
  have H := H₂ jL hL
  simp only [Category.id_comp] at H H₁
  rw [Finset.sum_eq_single 0 (fun α _ hα => by
    obtain ⟨a, ha, g, hg⟩ := hf α hα
    rw [IndivisibleSection.sval_of_secIsMul hg _ y hJ, hc', cst_comp, Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ha),
      GermDiv.cst_zero, zero_mul, zero_mul]) (fun h => by rw [H₁ 0 h, zero_mul])] at H
  have hm : fGl (maximalIdeal V) G 0 y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL) :=
    Set.mem_iInter.2 fun _ => hL
  refine (mem_nonzeroLocus_iff_pull σ _ y hm).trans (Iff.trans ?_
    (mem_nonzeroLocus_iff_pull (f 0) _ y (hJ.mem _ (pGl U.toUnifPre 0))).symm)
  have := congrArg IsUnit H
  rw [Units.isUnit_units_mul, Units.isUnit_mul_units] at this
  exact this.to_iff

theorem exists_points_hom (U : UnifPre (maximalIdeal V) D A G) {K : Type} [Field K] [IsAlgClosed K]
    (r : Sp K ⟶ Sp V) (hr : Set.range r = {closedPoint V}) {n : ℕ} (hn : 1 ≤ n) :
    ∃ p : (Over.mk r ⟶ G) →* (Over.mk r ⟶ D.toPre.P.A), Function.Surjective p ∧
      (∀ x, p x = 1 → ∃ y, p y = 1 ∧ y ^ n = x) ∧
      (Finite {b : Over.mk r ⟶ D.toPre.P.A // b ^ n = 1} → Finite {x : Over.mk r ⟶ G // x ^ n = 1}) ∧
      ∀ x, ∃ y : Sp K ⟶ (thickObj V (maximalIdeal V) 0 G).left,
        y ≫ fGl (maximalIdeal V) G 0 = x.left ∧ y ≫ pGl U 0 = (p x).left := by
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Sp K ⟶ Sp (V ⧸ maximalIdeal V ^ (0 + 1)), r₀ ≫ thick V (maximalIdeal V) 0 = r := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective r
    have h₁ : PrimeSpectrum.comap φ.hom ⟨⊥, Ideal.isPrime_bot⟩ = closedPoint V :=
      hr.le ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), rfl⟩
    have h₂ : ∀ a ∈ maximalIdeal V ^ (0 + 1), φ.hom a = 0 := fun a ha => by
      rw [zero_add, pow_one] at ha
      have : a ∈ (PrimeSpectrum.comap φ.hom ⟨⊥, Ideal.isPrime_bot⟩).asIdeal := by rw [h₁]; exact ha
      exact this
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ φ.hom h₂)), ?_⟩
    rw [← Spec.map_comp]
    rfl
  let c := U.gt 0
  have := c.q_hom
  have := c.i_hom
  have := c.q_surj
  have := U.smooth
  have hk := c.isKernel
  let T : Over (Sp (V ⧸ maximalIdeal V ^ (0 + 1))) := Over.mk r₀
  let eG := TorsionLift.ptsEquiv (thick V (maximalIdeal V) 0) G T r hr₀
  let eB := TorsionLift.ptsEquiv (thick V (maximalIdeal V) 0) D.toPre.P.A T r hr₀
  let q := IsMonHom.monoidHom c.q T
  let i := IsMonHom.monoidHom c.i T
  let e := splitTorusPointsEquiv _ D.toPre.X T
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  have hqi : ∀ t, q (i t) = 1 := fun t => by
    change (t ≫ c.i) ≫ c.q = 1
    rw [Category.assoc, hk.w, ← Category.assoc, comp_toUnit]
    rfl
  have hker : ∀ x, q x = 1 → ∃ t, i t = x := fun x hx =>
    ⟨hk.lift x (toUnit _) (by rw [show x ≫ c.q = 1 from hx, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hq : Function.Surjective q := fun b => by
    have : LocallyOfFiniteType (c.q.left ≫ (thickObj V (maximalIdeal V) 0 D.toPre.P.A).hom) := by
      rw [Over.w c.q]
      exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom (thick V (maximalIdeal V) 0)))
    have : LocallyOfFiniteType c.q.left :=
      locallyOfFiniteType_of_comp _ (thickObj V (maximalIdeal V) 0 D.toPre.P.A).hom
    obtain ⟨x, hx⟩ := GeomSurj.exists_lift_of_surjective c.q.left b.left
    exact ⟨Over.homMk x (by rw [← Over.w c.q, ← Category.assoc, ← hx]; exact Over.w b),
      Over.OverMorphism.ext hx.symm⟩
  have : IsDomain Γ(T.left, ⊤) := inferInstanceAs (IsDomain Γ(Sp K, ⊤))
  obtain ⟨p, h₁, h₂, h₃, h₄⟩ := exists_hom_of_extension i q eG eB n hi hqi hker hq (fun t => by
    obtain ⟨g, hg⟩ := TorsLift.exists_pow_eq_hom (M := Γ(T.left, ⊤)ˣ) n (TorsLift.exists_pow_eq_unit K n hn) (e t)
    exact ⟨e.symm g, by rw [← map_pow, hg, e.symm_apply_apply]⟩)
    (finite_torsion_of_mulEquiv e.symm n (SemiAbTorsion.finite_chars_pow_eq_one D.toPre.X Γ(T.left, ⊤) hn))
  refine ⟨p, h₁, h₂, h₃, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := eG.surjective x
  refine ⟨x.left, (TorsionLift.ptsEquiv_left _ _ _ _ _ x).symm, ?_⟩
  rw [h₄]
  exact (Category.assoc _ _ _).symm.trans (TorsionLift.ptsEquiv_left _ _ _ _ _ (q x)).symm

end Unif

theorem card_torsion_translate_zeros_lt :
    Out.Laws → Out.Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : Out.DegData V (IsLocalRing.maximalIdeal V)) (A : Out.PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Out.Unif (IsLocalRing.maximalIdeal V) D A G) (L : LB G.left) (θ : LB.Sec L), L.IsLB → LBIso L U.LG.L → (∃ x ∈ Out.nonzeroLocus θ, G.hom x = IsLocalRing.closedPoint V) → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : Sp K ⟶ Sp V) (N n : ℕ), Set.range r = {IsLocalRing.closedPoint V} → 4 ≤ N → (n : K) ≠ 0 → 6 * (N ^ A.g * A.g.factorial) < n ^ 2 → ∀ c : Over.mk r ⟶ G, 6 * Nat.card {h : Over.mk r ⟶ G // h ^ n = 1 ∧ ¬ ⊤ ≤ (c * h).left ⁻¹ᵁ Out.nonzeroLocus θ} < Nat.card {h : Over.mk r ⟶ G // h ^ n = 1} := by
  intro h h₂ V _ _ _ _ D A G _ _ U L θ hL hiso hθ K _ _ r N n hr hN hn hb c
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun e => hn (by rw [e, Nat.cast_zero])
  obtain ⟨θ', hθ'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso U.LG.isLB hL hiso.symm θ
  obtain ⟨σ, hσ⟩ : ∃ σ : Out.H0 U.LG.L 1, ∀ y, y ∈ Out.nonzeroLocus σ ↔
      ∀ _ : PUnit, (𝟙 G.left : G.left ⟶ G.left) y ∈ Out.nonzeroLocus θ' :=
    exists_sec_prod U.LG.isLB θ' (fun _ : PUnit => 𝟙 G.left) fun _ _ _ => by simp
  obtain ⟨f, hf⟩ := exists_weight_zero h.globalFns U σ
  obtain ⟨s, hs⟩ := exists_sec_of_formEq_id D.toPre.P.isLB (fun U _ k => by
    have e : toUnit D.toPre.P.A ≫ D.toPre.c 0 = 1 := cPoint_zero (D := D.toPre) _
    have e₁ : padd D.toPre.P.A (𝟙 D.toPre.P.A) 1 = 𝟙 D.toPre.P.A := _root_.mul_one (𝟙 D.toPre.P.A)
    have e₂ : toUnit D.toPre.P.A ≫ η[D.toPre.P.A] = 1 := rfl
    simp [Out.DegPre.famφB, Out.DegPre.famε, Fin.prod_univ_four, e, e₁, e₂]) f
  have key : ∀ y, DVR.fGl (IsLocalRing.maximalIdeal V) G 0 y ∈ Out.nonzeroLocus θ ↔
      DVR.pGl U.toUnifPre 0 y ∈ Out.nonzeroLocus s := fun y => by
    rw [hs, ← hf, hσ, ← hθ']
    exact ⟨fun h _ => h, fun h => h ⟨⟩⟩
  obtain ⟨p, hp, hk, hfin, hy⟩ := exists_points_hom U.toUnifPre r hr hn1
  have H := card_lt_fibre h h₂ D.toPre.P r s (by
    obtain ⟨x, hx, hx'⟩ := hθ
    obtain ⟨y, rfl⟩ := ThetaUnit.exists_thick_pt le_rfl 0 G x hx'
    have hc : DVR.pGl U.toUnifPre 0 ≫ D.toPre.P.A.hom = DVR.fGl (IsLocalRing.maximalIdeal V) G 0 ≫ G.hom :=
      (Over.w (U.gt 0).pG).trans (Over.w (Out.fstG _ 0 G)).symm
    refine ⟨_, (key y).1 hx, ?_⟩
    rw [hr]
    exact (congrArg (fun q => q y) hc).trans hx') (dim_le U.toUnifPre) hN hn hb (p c)
  refine card_lt_of_quotient p n 6 hp hk (hfin (Nat.finite_of_card_ne_zero (by omega))) _
    (fun b => ¬ ⊤ ≤ (p c * b).left ⁻¹ᵁ Out.nonzeroLocus s) (fun x hx hh => hx fun z _ => ?_) H
  obtain ⟨y, h₁, h₂⟩ := hy (c * x)
  rw [← map_mul, ← h₂] at hh
  rw [← h₁]
  exact (key (y z)).2 (hh (Set.mem_univ z))

end GlobalTheory.FewZeros
