import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def Isometric (L M : HermLB p) : Prop :=
  ∃ w : LB.Iso L.B M.B, w.IsGen ∧ ∀ (σ : k →+* ℂ) (a : M.B.ι) (b : L.B.ι) (y : CxPts p σ),
    y ∈ ptsIn p σ (M.B.U a) → y ∈ ptsIn p σ (L.B.U b) →
      (M.φ σ).φ a y = (L.φ σ).φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)
private theorem res_res_lemma {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a.val) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a.val
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
private theorem isGen_iso_self_of_isLB (B : LB X) (hB : B.IsLB) :
    (⟨fun c => B.g c.1 c.2⟩ : LB.Iso B B).IsGen := by
  obtain ⟨-, -, hc⟩ := hB
  rintro ⟨a, b⟩ ⟨a', b'⟩
  have e1 := congrArg (res (fun x hx => by simp only [Opens.mem_inf] at hx ⊢; tauto :
    (B.U a ⊓ B.U b) ⊓ (B.U a' ⊓ B.U b') ≤ _)) (hc a a' b')
  have e2 := congrArg (res (fun x hx => by simp only [Opens.mem_inf] at hx ⊢; tauto :
    (B.U a ⊓ B.U b) ⊓ (B.U a' ⊓ B.U b') ≤ _)) (hc a b b')
  simp only [map_mul, res_res_lemma] at e1 e2
  dsimp only [LB.div]
  refine (eq_mul_inv_of_mul_eq e2).trans ?_
  rw [← e1]
  exact mul_right_comm _ _ _
private theorem iso_phi_eq_add_log_normSq_transition {B : LB X} (hB : B.IsLB) (φ ψ : ∀ σ : k →+* ℂ, Weight p σ B)
    (h : ∀ σ a, ∀ y ∈ ptsIn p σ (B.U a), (ψ σ).φ a y = (φ σ).φ a y) (σ : k →+* ℂ) (a b : B.ι)
    (y : CxPts p σ) (ha : y ∈ ptsIn p σ (B.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (ψ σ).φ a y = (φ σ).φ b y + Real.log (‖ev p σ (B.U a ⊓ B.U b) (B.g a b).val y‖ ^ 2) := by
  rw [h σ a y ha, (φ σ).trans a b y ha hb]
  exact (sub_add_cancel _ _).symm

theorem isometric_of_eqOn {B : LB X} {hB : B.IsLB} {φ ψ : ∀ σ : k →+* ℂ, Weight p σ B} {h₁ h₂ h₃ h₄}
    (h : ∀ σ a, ∀ y ∈ ptsIn p σ (B.U a), (ψ σ).φ a y = (φ σ).φ a y) :
    Isometric (p := p) ⟨B, hB, φ, h₁, h₂⟩ ⟨B, hB, ψ, h₃, h₄⟩ :=
  ⟨⟨fun c => B.g c.1 c.2⟩, isGen_iso_self_of_isLB B hB, fun σ a b y ha hb => iso_phi_eq_add_log_normSq_transition hB φ ψ h σ a b y ha hb⟩

theorem Isometric.refl (L : HermLB p) : L.Isometric L := by
  obtain ⟨B, hB, φ, h₁, h₂⟩ := L
  exact isometric_of_eqOn fun _ _ _ _ => rfl

def raise (M : HermLB p) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) : HermLB p where
  B := M.B
  isLB := M.isLB
  φ σ := (M.φ σ).addFn (u σ)
  cInf σ := (M.cInf σ).addFn (hu σ)
  conj σ σ' c y y' h hy := congrArg₂ (· + ·) (M.conj σ σ' c y y' h hy)
    (hc σ σ' PUnit.unit y y' h mem_ptsIn_top)

theorem isometric_raise_triv (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) :
    (fnB u hu hc).Isometric ((triv p).raise u hu hc) :=
  isometric_of_eqOn fun σ _ y _ => zero_add (u σ y)
private theorem inv_eq_self_units_sections_spec_int_top (U : (Sp ℤ).Opens) (hU : U = ⊤) (u : Γ(Sp ℤ, U)ˣ) : u⁻¹ = u := by
  subst hU
  haveI := ArithBase.isArithVar_int.charZero
  obtain ⟨n, hn⟩ := ArithBase.surjective_intCast (𝟙 (Sp ℤ)) (u : Γ(Sp ℤ, ⊤))
  obtain ⟨m, hm⟩ := ArithBase.surjective_intCast (𝟙 (Sp ℤ)) ((u⁻¹ : Γ(Sp ℤ, ⊤)ˣ) : Γ(Sp ℤ, ⊤))
  simp only [Int.coe_castRingHom] at hn hm
  have h1 : n * m = 1 := by
    have e := u.mul_inv
    rw [← hn, ← hm] at e
    exact_mod_cast e
  ext
  rw [← hn, ← hm]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem eq_of_isometric_trivShift {s t : ℝ} (h : (ArithBase.trivShift s).Isometric (ArithBase.trivShift t)) : s = t := by
  obtain ⟨w, -, hw⟩ := h
  obtain ⟨y⟩ : Nonempty (CxPts (𝟙 (Sp ℤ)) (Int.castRingHom ℂ)) := ⟨⟨spMap (Int.castRingHom ℂ), by simp⟩⟩
  have hy : y ∈ ptsIn (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) ⊤ := mem_ptsIn_top
  have e : (0 : ℝ) + 2 * t = 0 + 2 * s +
      Real.log (‖ev (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) (⊤ ⊓ ⊤) (w.s (PUnit.unit, PUnit.unit)).val y‖ ^ 2) :=
    hw (Int.castRingHom ℂ) PUnit.unit PUnit.unit y hy hy
  have hne : ev (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) (⊤ ⊓ ⊤) (w.s (PUnit.unit, PUnit.unit)).val y ≠ 0 :=
    ev_iso_ne_zero w hy hy
  have hinv := ev_inv (mem_ptsIn_inf.2 ⟨hy, hy⟩ : y ∈ ptsIn (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) (⊤ ⊓ ⊤))
    (w.s (PUnit.unit, PUnit.unit))
  have hu := inv_eq_self_units_sections_spec_int_top _ (inf_idem _) (w.s (PUnit.unit, PUnit.unit))
  have hc := congrArg (fun v : Γ(Sp ℤ, ⊤ ⊓ ⊤)ˣ => ev (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) (⊤ ⊓ ⊤) v.val y) hu
  have key : ev (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) (⊤ ⊓ ⊤) (w.s (PUnit.unit, PUnit.unit)).val y =
      (ev (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) (⊤ ⊓ ⊤) (w.s (PUnit.unit, PUnit.unit)).val y)⁻¹ :=
    hc.symm.trans hinv
  set x := ev (𝟙 (Sp ℤ)) (Int.castRingHom ℂ) (⊤ ⊓ ⊤) (w.s (PUnit.unit, PUnit.unit)).val y
  have hxx : x * x = 1 := by
    have h2 : x * x⁻¹ = 1 := mul_inv_cancel₀ hne
    rwa [← key] at h2
  have hn : ‖x‖ * ‖x‖ = 1 := by rw [← norm_mul, hxx, norm_one]
  have hx : ‖x‖ = 1 := by
    rcases mul_self_eq_one_iff.mp hn with h | h
    · exact h
    · linarith [norm_nonneg x]
  rw [hx] at e
  simp at e
  linarith

end GlobalTheory.HermLB

namespace GlobalTheory.Published

def ArExists : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  (∀ L : HermLB p, ∃ h, L.IsArithHeight h) ∧
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), (∃ Φ, IsArFun L D Φ) ∧ ∃ Ψ, IsGeoFun L D Ψ

def ArChange : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
    IsArFun (fun o : Option ι => o.elim (fnB u hu hc) L) D Φ → ∀ n : ι → ℤ,
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u

def ArShift : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (L : HermLB p) (a t : ℝ), L.IsSelfInter a →
    (L.shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D)

def ArMix : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ),
  IsArithVar p D → ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
    IsArFun (fun o : Option ι => o.elim M L) D Φ → ∀ (n : ι → ℤ) (h : X → ℝ), (comb L n).IsArithHeight h →
    ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (comb L n).ArchIntegrable M D hr ∧
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
        ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - (comb L n).archInt M D hr

def ArProj : Prop := ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
  (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X →
    π.residueDegree (genericPoint Y) ≠ 0 →
    (∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a →
      (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * a)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun L D Φ →
      IsArFun (fun i => (L i).pull π hπ) D ((π.residueDegree (genericPoint Y) : ℝ) • Φ)

def ArIso : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  (∀ (L M : HermLB p) (h : X → ℝ), L.Isometric M → L.IsArithHeight h → M.IsArithHeight h) ∧
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun L D Φ →
    (∀ i, (L i).IsSelfInter (Φ (MvPolynomial.X i ^ (D + 1)))) ∧
    (∀ M : ι → HermLB p, (∀ i, (L i).Isometric (M i)) → IsArFun M D Φ) ∧
    ∀ (κ : Type) [Fintype κ] (M : κ → HermLB p) (A : κ → ι → ℤ), (∀ j, (comb L (A j)).Isometric (M j)) →
      IsArFun M D (Φ ∘ₗ (aeval fun j => lin fun i => (A j i : ℝ) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ).toLinearMap)

def ArMetric : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ)
    (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ')))
    (Φ Φ' : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o : Option ι => o.elim M L) D Φ →
    IsArFun (fun o : Option ι => o.elim (M.raise u hu hc) L) D Φ' → ∀ n : ι → ℤ,
      (∀ σ, ((comb L n).φ σ).ChernIntegrableOn D Set.univ (u σ)) ∧
      Φ' (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
        Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) + 1 / 2 * chInt (comb L n) D u

def ArCalc : Prop := ArExists ∧ ArChange ∧ ArShift ∧ ArMix ∧ ArProj ∧ ArIso ∧ ArMetric

theorem ArCalc.arExists (h : ArCalc) : ArExists := h.1

theorem ArCalc.arChange (h : ArCalc) : ArChange := h.2.1

theorem ArCalc.arShift (h : ArCalc) : ArShift := h.2.2.1

theorem ArCalc.arMix (h : ArCalc) : ArMix := h.2.2.2.1

theorem ArCalc.arProj (h : ArCalc) : ArProj := h.2.2.2.2.1

theorem ArCalc.arIso (h : ArCalc) : ArIso := h.2.2.2.2.2.1

section Consequences

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} {ι : Type} [Fintype ι]

theorem ArMix.vertical (H : ArMix) (HE : ArExists) [IsLocallyNoetherian X] (hX : IsArithVar p D) {M : HermLB p}
    {L : ι → HermLB p} {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ} (hΦ : IsArFun (fun o : Option ι => o.elim M L) D Φ)
    (n : ι → ℤ) {r : M.B.ι → X.functionFieldˣ} (hr : IsRatSec M.B r)
    (h1 : ∀ σ, ∀ y ∈ offSupp p σ (M.div hr), logNorm (M.φ σ) r y = 0) (l : ℕ) [Fact l.Prime] (d : X → ℤ)
    (hd : ∀ z, (M.div hr).mult z ≠ 0 → ∃ (Z : Scheme.{0}) (i : Z ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral Z)
      (_ : Algebra (ZMod l) Γ(Z, ⊤)), i (genericPoint Z) = z ∧ topologicalKrullDim Z = D ∧
        d z = topSelfIntersection (ZMod l) ((comb L n).B.pull i) D) :
    Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
      (∑ᶠ z, ((M.div hr).mult z * d z : ℝ)) * Real.log l := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨h, hh⟩ := (HE k X p D hX).1 (comb L n)
  obtain ⟨-, he⟩ := H k X p D hX ι M L Φ hΦ n h hh r hr
  have hA : (comb L n).archInt M D hr = 0 := by
    unfold HermLB.archInt
    refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
    simp only [Weight.chernInt]
    rw [MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (h1 σ),
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (h1 σ),
      sub_zero]
  rw [he, hA, sub_zero, finsum_mul]
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  obtain ⟨Z, i, hi, hZ, alg, rfl, hdim, hdz⟩ := hd z hz
  haveI := hi
  haveI := hZ
  letI := alg
  rw [hh.vertical Z i (ZMod l) D hdim, hdz, Nat.card_zmod]
  first
    | (push_cast; ring)
    | push_cast
    | ring

theorem ArMix.fnB (H : ArMix) (HE : ArExists) (hX : IsArithVar p D) {L : ι → HermLB p}
    {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} {hu : ∀ σ y, CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim (fnB u hu hc) L) D Φ) (n : ι → ℤ) :
    (∀ σ, ((comb L n).φ σ).ChernIntegrableOn D Set.univ (u σ)) ∧
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u := by
  haveI : IsLocallyNoetherian X := hX.isLocallyNoetherian
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  obtain ⟨h, hh⟩ := (HE k X p D hX).1 (comb L n)
  have hr1 : IsRatSec (LB.triv X) (fun _ => 1) := by
    intro i j hij
    change (1 : X.functionField) = fnOf _ hij ((1 : Γ(X, ⊤ ⊓ ⊤)ˣ) : Γ(X, ⊤ ⊓ ⊤)) * 1
    simp
  obtain ⟨hI, he⟩ := H k X p D hX ι (ArInt.fnB u hu hc) L Φ hΦ n h hh _ hr1
  have hE : ∀ x, ((ArInt.fnB u hu hc).div hr1).IsEqn x 1 := fun x =>
    (presents_divOfRatSec (LB.isLB_triv X) hr1).isEqn PUnit.unit x trivial
  have hmult : ∀ z, ((ArInt.fnB u hu hc).div hr1).mult z = 0 := fun z => by
    rw [(hE z).mult_eq]
    first
      | exact UnitAt.ord_eq_zero (unitAt_one z)
      | simpa using UnitAt.ord_eq_zero (unitAt_one z)
  have hoff : ∀ σ, offSupp p σ ((ArInt.fnB u hu hc).div hr1) = Set.univ := fun σ =>
    Set.eq_univ_of_forall fun y => mem_offSupp.2 fun hy => hy (hE _)
  have hlog : ∀ σ, logNorm ((ArInt.fnB u hu hc).φ σ) (fun _ : (LB.triv X).ι => 1) =
      fun y => (-1 / 2 : ℝ) * u σ y := by
    intro σ
    funext y
    have hv : ratVal (1 : X.functionField) y = 1 := by
      have e := ratVal_fnOf (mem_ptsIn_top : y ∈ ptsIn p σ ⊤) trivial (1 : Γ(X, ⊤))
      rwa [map_one, ev_one (mem_ptsIn_top : y ∈ ptsIn p σ ⊤)] at e
    simp only [logNorm, Units.val_one, hv, norm_one, Real.log_one, zero_sub]
    change -(u σ y / 2) = (-1 / 2 : ℝ) * u σ y
    ring
  refine ⟨fun σ => ?_, ?_⟩
  · have hi := hI σ
    rw [hoff σ, hlog σ] at hi
    exact ⟨(MeasureTheory.Integrable.const_mul hi.1 (-2)).congr
        (Filter.Eventually.of_forall fun y => by dsimp only; ring),
      (MeasureTheory.Integrable.const_mul hi.2 (-2)).congr
        (Filter.Eventually.of_forall fun y => by dsimp only; ring)⟩
  · rw [he]
    simp only [hmult, Int.cast_zero, zero_mul, finsum_zero, zero_sub]
    unfold HermLB.archInt chInt
    simp only [hoff, hlog, Weight.chernInt_const_mul]
    rw [← mul_finsum]
    ring

end Consequences

theorem arChange_of_arMix (HE : ArExists) (H : ArMix) : ArChange := by
  intro k _ X _ p D hX ι _ L u hu hc Φ hΦ n
  exact (ArMix.fnB H HE hX hΦ n).2

end GlobalTheory.Published
