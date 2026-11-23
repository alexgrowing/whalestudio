import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.CommensurableQuotient

theorem card_range_eq {R M Q : Type} [Ring R] [AddCommGroup M] [Module R M] [Group Q]
    (φ : Multiplicative M →* Q) (p : Submodule R M) (h : ∀ a, φ (Multiplicative.ofAdd a) = 1 ↔ a ∈ p) :
    Nat.card φ.range = Nat.card (M ⧸ p) := by
  have e : φ.ker = AddSubgroup.toSubgroup p.toAddSubgroup := Subgroup.ext fun a => h a.toAdd
  rw [← Subgroup.index_ker, e, AddSubgroup.index_toSubgroup]
  rfl

theorem exists_point_lift {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} (ψ : A ⟶ B) [IsFinite ψ.left]
    [Surjective ψ.left] (c : 𝟙_ (Over (Sp k)) ⟶ B) : ∃ d : 𝟙_ (Over (Sp k)) ⟶ A, d ≫ ψ = c := by
  obtain ⟨u, hu⟩ := H1.SectionDivision.exists_section (k := k) (pullback.snd ψ.left c.left)
  have hb : (u ≫ pullback.fst ψ.left c.left) ≫ ψ.left = c.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]; exact Category.id_comp _
  have hw : (u ≫ pullback.fst ψ.left c.left) ≫ A.hom = (𝟙_ (Over (Sp k))).hom := by
    rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w c
  exact ⟨Over.homMk _ hw, Over.OverMorphism.ext hb⟩

theorem smoothDim_of_etale {k : Type} [Field k] {A B : Over (Sp k)} (ψ : A ⟶ B) [Etale ψ.left] [Smooth B.hom]
    [GeometricallyConnected B.hom] (x : A.left) {g : ℕ} (hA : SmoothOfRelativeDimension g A.hom) :
    SmoothOfRelativeDimension g B.hom := by
  have : ConnectedSpace (Sp k) := inferInstanceAs (ConnectedSpace (PrimeSpectrum k))
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace B.hom B.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected B.hom (ψ.left x)
  have h : SmoothOfRelativeDimension (0 + d) (ψ.left ≫ B.hom) := inferInstance
  rw [Over.w ψ, zero_add] at h
  rwa [H1.dim_unique _ hA h x]

theorem isHolTo_smul_comp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ y) (c : ℂ) (φ : X ⟶ Y) :
    IsHolTo Set.univ (fun z => y (c • z) ≫ φ) := by
  intro U f
  obtain ⟨h₁, h₂⟩ := h (φ ⁻¹ᵁ U) ((φ.app U).hom f)
  have hc : Differentiable ℂ (fun z : V => c • z) := differentiable_id.const_smul c
  refine ⟨h₁.preimage hc.continuous, ?_⟩
  simp only [← valAt'_comp]
  exact h₂.comp hc.differentiableOn fun z hz => hz

theorem exists_weilIs (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type}
    [Field k] (t : SAB H (Sp k)) [IsProper t.G.hom] {g : ℕ} (hd : SmoothOfRelativeDimension g t.G.hom)
    (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L) (n : ℕ) {T : Over (Sp k)} (x y : T ⟶ t.G)
    (hx : x ^ n = 1) (hy : y ^ n = 1) : ∃ c, Out.WeilIs t.G t.PP.L n x y c := by
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let P : Out.PolAV (Sp k) :=
    { A := t.G, g := g, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ha, ktriv := hk
      isAb := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  exact ((hL.weil _ P n T).1 x y hx hy).exists

end GlobalTheory.CommensurableQuotient

namespace GlobalTheory

open CommensurableQuotient

theorem exists_uniformised_quotient_of_commensurable : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (N : ℕ) (j : D.La →ₗ[𝓞 E] D'.La) (j' : D'.La →ₗ[𝓞 E] D.La) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)), D'.p = D.p → D'.q = D.q → (0 < N ∧ (∀ a, j' (j a) = (N ^ 2) • a) ∧ (∀ a, j (j' a) = (N ^ 2) • a) ∧ (∀ a b, D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b) ∧ (∀ a b, D.EF (j' a) (j' b) = (N : ℤ) ^ 2 * D'.EF a b) ∧ Nat.card (D'.La ⧸ LinearMap.range j) = N ^ (2 * g)) → IsPeriod D ty P → IsPeriod D' ty P' → (∀ a, P' (j a) = (N : ℂ) • P a) → (∀ a, P (j' a) = (N : ℂ) • P' a) → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) → ∃ (t' : SAB H (Sp ℂ)) (e' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t'.G)), (IsProper t'.G.hom ∧ SmoothOfRelativeDimension g t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ DetCond D' t'.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ (∀ z, e' z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t'.act.act a) ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t'.G t'.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c)) := by
  intro hL hQ E _ _ _ H D D' g ty P P' N j j' t e hp hq ⟨hN, _, _, _, hE, hcard⟩ _ hP' hj hj'
    ⟨hpr, hsm, ham, hkt, hdet, hadd, hsurj, hker, hlin, hhol, hweil⟩
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e0 : e 0 = 1 := (hker 0).2 (zero_mem _)
  let eh : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ t.G) :=
    { toFun := fun z => e z.toAdd, map_one' := e0, map_mul' := fun z w => hadd _ _ }
  have epow : ∀ (n : ℕ) z, e z ^ n = e ((n : ℂ) • z) := fun n z => by
    rw [Nat.cast_smul_eq_nsmul]
    exact (map_pow eh (Multiplicative.ofAdd z) n).symm
  have esub : ∀ z w, e z = e w ↔ z - w ∈ P.range := fun z w => by
    rw [← hker, ← mul_inv_eq_one, ← div_eq_mul_inv]
    exact Eq.congr_left (map_div eh (Multiplicative.ofAdd z) (Multiplicative.ofAdd w)).symm
  let φ : Multiplicative D'.La →* (𝟙_ (Over (Sp ℂ)) ⟶ t.G) :=
    { toFun := fun a => e ((N : ℂ)⁻¹ • P' a.toAdd)
      map_one' := by rw [toAdd_one, map_zero, smul_zero, e0]
      map_mul' := fun a b => by rw [toAdd_mul, map_add, smul_add, hadd] }
  have hmem : ∀ x, x ∈ φ.range ↔ ∃ a, e ((N : ℂ)⁻¹ • P' a) = x := fun x => Iff.rfl
  have hrw : ∀ (k : ℕ) a, ((k * N ^ 2 : ℕ) : ℂ)⁻¹ • P (j' a) = (N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' a := fun k a => by
    rw [hj', smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  have hw : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L ((k * N ^ 2 : ℕ) : ℤ) (e ((N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' a))
        (e ((N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' b)) (unitOn c) := fun k a b c hk hc => by
    rw [← hrw, ← hrw]
    refine hweil (k * N ^ 2) (j' a) (j' b) c (by positivity) (hc.trans ?_)
    rw [hE]
    congr 1
    push_cast
    field_simp
  obtain ⟨t', ψ, hpr', ham', hkt', hψ, hfin, het, hsj, hkψ, hact, hiso⟩ :=
    hQ E H ℂ t g N φ.range hN hpr hsm ham hkt
      (by
        intro x hx c
        obtain ⟨a, rfl⟩ := (hmem x).1 hx
        refine (hmem _).2 ⟨c • a, ?_⟩
        rw [← hlin]
        congr 1
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, hP'.1]
        ring)
      (by
        intro x hx
        obtain ⟨a, rfl⟩ := (hmem x).1 hx
        rw [epow, hker]
        refine ⟨j' a, ?_⟩
        rw [hj', smul_smul]
        congr 1
        push_cast
        field_simp)
      (by
        intro x hx y hy
        obtain ⟨a, rfl⟩ := (hmem x).1 hx
        obtain ⟨b, rfl⟩ := (hmem y).1 hy
        have h := hw 1 a b 1 one_pos (by
          rw [Units.val_one, Nat.cast_one, div_one, ← Complex.exp_int_mul_two_pi_mul_I (-(D'.EF a b))]
          congr 1
          push_cast
          ring)
        rw [_root_.one_mul, Nat.cast_one, inv_one, one_smul, one_smul, show unitOn (1 : ℂˣ) = 1 from map_one _] at h
        exact h)
      (by
        rw [← hcard]
        refine card_range_eq φ _ fun a => (hker _).trans ⟨?_, ?_⟩
        · rintro ⟨b, hb⟩
          refine ⟨b, hP'.2.1 ?_⟩
          rw [hj, hb, smul_inv_smul₀ hN']
          rfl
        · rintro ⟨b, rfl⟩
          exact ⟨b, by rw [toAdd_ofAdd, hj, inv_smul_smul₀ hN']⟩)
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hB := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have := hB.smooth
  have := hB.geomConnected
  have hsm' : SmoothOfRelativeDimension g t'.G.hom :=
    smoothDim_of_etale ψ ((e 0).left (default : PrimeSpectrum ℂ)) hsm
  have hker' : ∀ z, e ((N : ℂ)⁻¹ • z) ≫ ψ = 1 ↔ z ∈ P'.range := fun z => by
    rw [hkψ, hmem]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := (esub _ _).1 ha
      refine ⟨a - j b, ?_⟩
      rw [map_sub, hj, hb, ← smul_sub, smul_inv_smul₀ hN', sub_sub_cancel]
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  refine ⟨t', fun z => e ((N : ℂ)⁻¹ • z) ≫ ψ, hpr', hsm', ham', hkt', fun τ => ?_, fun z w => ?_, fun y => ?_, hker',
    fun a z => ?_, isHolTo_smul_comp hhol _ ψ.left, fun k a b c hk hc => ?_⟩
  · rw [hp, hq, ← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ t.act t'.act hψ het hact,
      ← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ t.act t'.act hψ het hact]
    exact hdet τ
  · simp only [smul_add, hadd, MonObj.mul_comp]
  · obtain ⟨x, rfl⟩ := exists_point_lift ψ y
    obtain ⟨z, rfl⟩ := hsurj x
    exact ⟨(N : ℂ) • z, by simp only [inv_smul_smul₀ hN']⟩
  · beta_reduce
    rw [Category.assoc, ← hact, ← Category.assoc, ← hlin]
    congr 2
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have htor : ∀ a, (e ((N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' a) ≫ ψ) ^ k = 1 := fun a => by
      rw [← MonObj.pow_comp, epow, smul_comm (k : ℂ), smul_inv_smul₀ hk', hker']
      exact ⟨a, rfl⟩
    obtain ⟨c', hc'⟩ := exists_weilIs hL t' hsm' ham' hkt' k _ _ (htor a) (htor b)
    have h₁ := (weilIs_along_hom hL.globalFns _ _ _ ψ _ _ _ _ _ _ _ c' c' hA hB t.PP.isLB t'.PP.isLB hψ hiso hc').1
    have h₂ := hw k a b c hk hc
    rw [Nat.cast_mul] at h₂
    exact CommutatorPairing.weilIs_unique hL.globalFns hA t.PP.isLB h₁ h₂ ▸ hc'

end GlobalTheory
