import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubmatrixMulOfVanish
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsUnitField
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.AlternatingSumChooseMulSubPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulSectionsExactAlgClosedPolarisedAVStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.JacNeZeroIffSpanEqMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa.KoszulEx

section Alg

def Ex {K Ix : Type} [CommRing K] [Fintype Ix] (D : Matrix Ix Ix K) : Prop :=
  ∀ v, D.mulVec v = 0 → ∃ w, D.mulVec w = v

theorem Ex.descend {k Ω Ix : Type} [Field k] [Field Ω] [Fintype Ix] (f : k →+* Ω) (D : Matrix Ix Ix k)
    (h : Ex (D.map f)) : Ex D := by
  letI := f.toAlgebra
  obtain ⟨ρ, hρ⟩ := (Algebra.linearMap k Ω).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 f.injective)
  have hρ' : ∀ a, ρ (f a) = a := fun a => LinearMap.congr_fun hρ a
  intro v hv
  obtain ⟨w, hw⟩ := h (f ∘ v) (funext fun p => by
    rw [← RingHom.map_mulVec, hv]; simp)
  refine ⟨ρ ∘ w, funext fun p => ?_⟩
  have e := congrArg ρ (congrFun hw p)
  rw [Function.comp_apply, hρ'] at e
  rw [← e]
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, Function.comp_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact ((ρ.map_smul (D p q) (w q)).trans (smul_eq_mul _ _)).symm

theorem count_eq {g d : ℕ} {N : ℕ → ℕ}
    (e : {p : KIx g d N // Even (kdeg p)} ≃ {p : KIx g d N // ¬ Even (kdeg p)}) :
    (d : ℤ) = ∑ j ∈ Finset.range (g + 1), (-1 : ℤ) ^ j * (g.choose j : ℤ) * (N j : ℤ) := by
  have h : ∑ p : KIx g d N, (-1 : ℤ) ^ kdeg p = 0 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun p : KIx g d N => Even (kdeg p)),
      Finset.sum_congr rfl (fun (p : {p : KIx g d N // Even (kdeg p)}) _ => p.2.neg_one_pow),
      Finset.sum_congr rfl (fun (p : {p : KIx g d N // ¬ Even (kdeg p)}) _ =>
        (Nat.not_even_iff_odd.1 p.2).neg_one_pow)]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [Fintype.card_congr e]
    simp
  rw [Fintype.sum_sum_type, Fintype.sum_sigma] at h
  simp only [kdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, pow_zero] at h
  have h2 := Finset.sum_powerset_apply_card (fun j => N j • (-1 : ℤ) ^ (j + 1)) (x := (Finset.univ : Finset (Fin g)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h2
  rw [h2] at h
  rw [nsmul_eq_mul, _root_.mul_one] at h
  rw [eq_neg_of_add_eq_zero_right h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [nsmul_eq_mul]
  ring

variable {K : Type} [CommRing K] {g d : ℕ} {N : ℕ → ℕ}

def Resolves (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K) (ev : Matrix (Fin d) (Fin (N 0)) K) : Prop :=
  (∀ v : KIx g 0 N → K, (kosD m (fun _ => 0)).mulVec v = 0 →
    ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p)) ∧
  (∀ t, ∃ c, ev.mulVec c = t) ∧
  ∀ c, ev.mulVec c = 0 → ∃ w : Fin g → Fin (N 1) → K, c = ∑ i, (m i 0 1).mulVec (w i)

theorem mulVec_inl (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) K)
    (v : KIx g d N → K) (p) :
    (kosD m ev).mulVec v (.inl p) = ∑ q, kosD (d := 0) m (fun _ => 0) (.inl p) (.inl q) * v (.inl q) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero]

theorem mulVec_inr (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) K)
    (v : KIx g d N → K) (a) :
    (kosD m ev).mulVec v (.inr a) = (ev 0).mulVec (fun k => v (.inl ⟨∅, k⟩)) a := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    Fintype.sum_sigma]
  rw [Finset.sum_eq_single ∅ (fun J _ hJ => by simp [hJ]) (by simp)]
  simp only [if_true]
  rfl

theorem kosD_inl_empty (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) K)
    (p) (k) : kosD m ev (.inl p) (.inl ⟨∅, k⟩) = 0 := by
  simp only [kosD]
  exact Finset.sum_eq_zero fun i _ => if_neg fun h => Finset.insert_ne_empty _ _ h.2.symm

theorem kosD_single_ne (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) K)
    (p : Σ I : Finset (Fin g), Fin (N I.card)) (hp : p.1 ≠ ∅) (i) (k) : kosD m ev (.inl p) (.inl ⟨{i}, k⟩) = 0 := by
  simp only [kosD]
  refine Finset.sum_eq_zero fun i' _ => if_neg fun h => hp ?_
  have := congrArg Finset.card h.2
  rw [Finset.card_insert_of_notMem h.1, Finset.card_singleton] at this
  exact Finset.card_eq_zero.1 (by omega)

theorem kosD_single_empty (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) K) (k' : Fin (N 0)) (i) (k : Fin (N 1)) :
    kosD m ev (.inl ⟨∅, k'⟩) (.inl ⟨{i}, k⟩) = m i 0 1 k' k := by
  simp only [kosD]
  rw [Finset.sum_eq_single i (fun i' _ h => if_neg fun h' => h (by simpa using h'.2.symm)) (by simp),
    if_pos (by simp)]
  simp only [Finset.filter_empty, Finset.card_empty, pow_zero, _root_.one_mul]
  rfl

theorem Resolves.ex {m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K} {ev : ∀ j, Matrix (Fin d) (Fin (N j)) K}
    (h : Resolves m (ev 0)) (hD : kosD m ev * kosD m ev = 0) : Ex (kosD m ev) := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := h
  intro v hv
  obtain ⟨w₀, hw₀⟩ := h₁ (Sum.elim (fun q => v (.inl q)) Fin.elim0) (funext fun p => by
    rcases p with p | p
    · exact (mulVec_inl m _ _ p).trans ((mulVec_inl m ev v p).symm.trans (congrFun hv _))
    · exact p.elim0)
  obtain ⟨c, hc⟩ := h₂ (fun a => v (.inr a))
  obtain ⟨F, hF₀, hF⟩ : ∃ F : ∀ I : Finset (Fin g), Fin (N I.card) → K, F ∅ = c ∧
      ∀ I, I ≠ ∅ → F I = fun k => w₀ (.inl ⟨I, k⟩) :=
    ⟨Function.update (fun I k => w₀ (.inl ⟨I, k⟩)) ∅ c, Function.update_self .., fun I h => Function.update_of_ne h ..⟩
  let w₁ : KIx g d N → K := Sum.elim (fun q => F q.1 q.2) (fun _ => 0)
  have e₁ : ∀ p, (kosD m ev).mulVec w₁ (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w₀ (.inl p) := by
    intro p
    rw [mulVec_inl, mulVec_inl]
    refine Finset.sum_congr rfl fun ⟨I, k⟩ _ => ?_
    by_cases hI : I = ∅
    · subst hI
      rw [kosD_inl_empty, zero_mul, zero_mul]
    · simp only [w₁, Sum.elim_inl, hF I hI]
  have e₂ : ∀ a, (kosD m ev).mulVec w₁ (.inr a) = v (.inr a) := by
    intro a
    rw [mulVec_inr, ← congrFun hc a, ← hF₀]
    rfl
  have e₃ : (kosD m ev).mulVec (v - (kosD m ev).mulVec w₁) = 0 := by
    rw [Matrix.mulVec_sub, hv, Matrix.mulVec_mulVec, hD, Matrix.zero_mulVec, sub_zero]
  obtain ⟨w, hw⟩ := h₃ (fun k => (v - (kosD m ev).mulVec w₁) (.inl ⟨∅, k⟩))
    (funext fun a => (mulVec_inr m ev _ a).symm.trans (congrFun e₃ _))
  let w₂ : KIx g d N → K := ∑ i, ∑ k : Fin (N 1), w i k • Pi.single (.inl ⟨{i}, k⟩) 1
  have e₄ : ∀ p, (kosD m ev).mulVec w₂ p = ∑ i, ∑ k : Fin (N 1), kosD m ev p (.inl ⟨{i}, k⟩) * w i k := by
    intro p
    simp only [w₂, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_single_one, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.col_apply, _root_.mul_comm]
  refine ⟨w₁ + w₂, funext fun p => ?_⟩
  rw [Matrix.mulVec_add, Pi.add_apply, e₄]
  rcases p with ⟨I, k⟩ | a
  · by_cases hI : I = ∅
    · subst hI
      have := congrFun hw k
      rw [Pi.sub_apply, sub_eq_iff_eq_add'] at this
      rw [this]
      congr 1
      refine Eq.trans ?_ (Finset.sum_apply (k : Fin (N 0)) Finset.univ fun i => (m i 0 1).mulVec (w i)).symm
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k' _ =>
        congrArg (· * w i k') (kosD_single_empty m ev k i k')
    · rw [e₁, ← hw₀ ⟨I, k⟩ hI]
      refine add_eq_left.2 (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k' _ => ?_)
      exact (congrArg (· * w i k') (kosD_single_ne m ev ⟨I, k⟩ hI i k')).trans (zero_mul _)
  · rw [e₂]
    simp [kosD]

theorem Resolves.scale {m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K} {ev ev' : Matrix (Fin d) (Fin (N 0)) K}
    (h : Resolves m ev') (u : Fin d → Kˣ) (hu : ∀ a k, ev' a k * u a = ev a k) : Resolves m ev := by
  have e : ∀ c a, ev.mulVec c a = ev'.mulVec c a * u a := fun c a => by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, ← hu]
    exact Finset.sum_congr rfl fun k _ => by ring
  refine ⟨h.1, fun t => ?_, fun c hc => h.2.2 c (funext fun a => ?_)⟩
  · obtain ⟨c, hc⟩ := h.2.1 (fun a => t a * ((u a)⁻¹ : Kˣ))
    exact ⟨c, funext fun a => by rw [e, hc]; simp⟩
  · exact (u a).isUnit.mul_left_eq_zero.1 ((e c a).symm.trans (congrFun hc a))

theorem Resolves.cast {g' : ℕ} (hg : g' = g) (M : ℕ → ℕ)
    (m : Fin g → ∀ j j', Matrix (Fin (M j ^ g)) (Fin (M j' ^ g)) K) (ev : Matrix (Fin d) (Fin (M 0 ^ g)) K)
    (h : Resolves (N := fun j => M j ^ g')
      (fun i j j' k k' => m (i.cast hg) j j' (k.cast (congrArg (M j ^ ·) hg)) (k'.cast (congrArg (M j' ^ ·) hg)))
      (fun a k => ev a (k.cast (congrArg (M 0 ^ ·) hg)))) : Resolves (N := fun j => M j ^ g) m ev := by
  subst hg
  exact h

theorem kosD_map {K' : Type} [CommRing K'] (f : K →+* K') (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) K) :
    (kosD m ev).map f = kosD (fun i j j' => (m i j j').map f) (fun j => (ev j).map f) := by
  ext p q
  rcases p with p | p <;> rcases q with q | q <;> simp [kosD, apply_ite f]

end Alg

section Geo

def comb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {S : Type}
    [Fintype S] (a : S → R) (s : S → L.Sec) : L.Sec where
  f j := ∑ i, AbLaw.cst p (L.U j) (a i) * (s i).f j
  compat j k := by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, rs_cst, rs_cst, (s i).compat j k]
    ring

theorem gs_mem_iff {K : Type} [Field K] {X : Scheme.{0}} (z : Sp K ⟶ X) (U : X.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (p : Sp K)
    (a : Γ(X, U)) : gs (𝟙 X) (z p) U a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (z p)) ↔ valT z U a = 0 := by
  have hp : z p ∈ U := h (show p ∈ ⊤ from trivial)
  have e₁ : IsUnit (gs (𝟙 X) (z p) U a) ↔ z p ∈ X.basicOpen a := by
    rw [gs_eq (𝟙 X) (z p) U hp]
    exact (X.mem_basicOpen a (z p) hp).symm
  have e₂ : z p ∈ X.basicOpen a ↔ p ∈ (Sp K).basicOpen ((z.appLE U ⊤ h).hom a) := by
    have := Scheme.basicOpen_appLE z ⊤ U h a
    exact ⟨fun hy => this.ge ⟨trivial, hy⟩, fun hy => (this.le hy).2⟩
  have e₃ : (z.appLE U ⊤ h).hom a = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (valT z U a) := by
    rw [EtBaseChange.valT_eq z U h]
    exact ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply _).symm
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, e₁, e₂, e₃]
  by_cases h0 : valT z U a = 0
  · simp [h0]
  · simp only [h0, iff_false, not_not]
    rw [Scheme.basicOpen_of_isUnit _ ((IsUnit.mk0 _ h0).map _)]
    trivial

theorem gs_sub {X : Scheme.{0}} (y : X) (U : X.Opens) (h : y ∈ U) (a b : Γ(X, U)) :
    gs (𝟙 X) y U (a - b) = gs (𝟙 X) y U a - gs (𝟙 X) y U b := by
  simp only [gs_eq (𝟙 X) y U h, map_sub]

theorem isUnit_gs {X : Scheme.{0}} {L : LB X} (s : L.Sec) (y : X) (h : y ∈ Out.nonzeroLocus s) (i : L.ι)
    (hi : y ∈ L.U i) : IsUnit (gs (𝟙 X) y (L.U i) (s.f i)) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  have hk' : y ∈ L.U k := X.basicOpen_le _ hk
  have hm : (𝟙 X : X ⟶ X) y ∈ L.U i ⊓ L.U k := ⟨hi, hk'⟩
  have e := (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (s.compat i k)).trans
    ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))
  rw [e]
  refine (Units.isUnit _).mul ?_
  rw [gs_eq (𝟙 X) y _ hk']
  exact (X.mem_basicOpen _ _ hk').1 hk

variable {R : Type} [CommRing R]

theorem exists_cast (x : KeyIn R) {l l' : ℕ} (h : l = l') (s : RR x l) :
    ∃ s' : RR x l', ∀ i, (show Γ(x.P.A.left, x.P.L.U i) from s'.f i) = s.f i := by
  subst h
  exact ⟨s, fun _ => rfl⟩

theorem valT_coords (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) (f) (hc : Coords x b c f)
    (z : Pt x) (i : x.P.L.ι) (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U i) :
    valT (T := R) z.left (x.P.L.U i) (f i) = ∑ k, valT (T := R) z.left (x.P.L.U i) ((b k).f i) * c k := by
  refine (congrArg (valT (T := R) z.left (x.P.L.U i)) (hc i)).trans ((EtBaseChange.valT_eq (T := R) z.left _ h _).trans
    ((map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => (map_mul _ _ _).trans ((_root_.mul_comm _ _).trans ?_))))
  exact congrArg₂ (· * ·) (EtBaseChange.valT_eq (T := R) z.left _ h _).symm
    ((EtBaseChange.valT_eq (T := R) z.left _ h _).symm.trans (KoszulCx.valH_cst x z _ h _))

theorem coords_sum (x : KeyIn R) {l N : ℕ} {S : Type} [Fintype S] (b : Fin N → RR x l) (c : S → Fin N → R)
    (f : S → ∀ i, Γ(x.P.A.left, x.P.L.U i)) (hc : ∀ a, Coords x b (c a) (f a)) :
    Coords x b (∑ a, c a) (fun i => ∑ a, f a i) := by
  intro i
  refine (Finset.sum_congr rfl fun a _ => hc a i).trans (Finset.sum_comm.trans ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_apply, map_sum, Finset.sum_mul]

theorem resolves_field (hL : Out.Laws) (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l d : ℕ)
    (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (z : Fin d → Pt x)
    (ch : Fin d → x.P.L.ι) (hn : 1 ≤ n) (hl : x.P.g * n < l) (hb : ∀ j ≤ x.P.g, IsBasis x (b j)) (hz : EtZ x s z ch)
    (m) (hm : IsMul x l s b m) :
    Resolves (N := fun j => (l - j * n) ^ x.P.g) m
      (Matrix.of fun a k => valT (T := K) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) := by
  classical
  obtain ⟨hz₁, hz₂, hz₃, hz₄, hz₅⟩ := hz
  let p : Sp K := IsLocalRing.closedPoint K
  have hp : ∀ q : Sp K, q = p := fun q => Subsingleton.elim (α := PrimeSpectrum K) q p
  let y : Fin d → x.P.A.left := fun a => (z a).left p
  have hy : Function.Injective y := fun a a' e => by_contra fun h => hz₄ a a' h p e
  have hyU : ∀ a, y a ∈ x.P.L.U (ch a) := fun a => hz₁ a (show p ∈ ⊤ from trivial)
  have hzero : ∀ t, (∀ i, t ∉ Out.nonzeroLocus (s i)) → ∃ a, y a = t := fun t ht => by
    obtain ⟨a, q, hq⟩ := hz₅ t ht
    exact ⟨a, (congrArg (z a).left (hp q)).symm.trans hq⟩
  have hmax : ∀ a, Ideal.span (Set.range fun i => gs (𝟙 _) (y a) (x.P.L.U (ch a)) ((s i).f (ch a))) =
      IsLocalRing.maximalIdeal (x.P.A.left.presheaf.stalk (y a)) := fun a =>
    (GlobalTheory.KeyKa.jac_ne_zero_iff_span_eq_maximalIdeal K x n s (z a) (ch a) p (hz₁ a) (hz₂ a)).1 (hz₃ a).ne_zero
  have hzero' : ∀ a i, y a ∉ Out.nonzeroLocus (s i) := fun a i h => by
    refine (IsLocalRing.mem_maximalIdeal _).1 ((gs_mem_iff (K := K) (z a).left _ (hz₁ a) p _).2 (hz₂ a i)) ?_
    exact isUnit_gs (s i) (y a) h (ch a) (hyU a)
  choose c₀ hc₀ using fun t : x.P.A.left => exists_chart x.P.isLB t
  let c : x.P.A.left → x.P.L.ι := Function.extend y ch c₀
  have hc : ∀ a, c (y a) = ch a := fun a => hy.extend_apply _ _ a
  have hcU : ∀ t, t ∈ x.P.L.U (c t) := fun t => by
    by_cases h : ∃ a, y a = t
    · obtain ⟨a, rfl⟩ := h
      rw [hc]; exact hyU a
    · rw [show c t = c₀ t from Function.extend_apply' _ _ _ h]; exact hc₀ t
  have hfin : FinZ x s := (Set.finite_range y).subset fun t ht => hzero t ht
  obtain ⟨h₁, h₂, h₃⟩ := GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV hL K x n l s b m c hn hl hfin hb hm hcU
  have hl0 : l = l - 0 * n := by simp
  refine ⟨h₁, fun t => ?_, fun v hv => ?_⟩
  · obtain ⟨sg, hsg⟩ := h₂ fun q => gs (𝟙 _) q (x.P.L.U (c q)) (AbLaw.cst x.P.A.hom (x.P.L.U (c q)) (Function.extend y t 0 q))
    obtain ⟨sg', hsg'⟩ := exists_cast x hl0 sg
    obtain ⟨v, hv, -⟩ := hb 0 (Nat.zero_le _) sg'
    refine ⟨v, funext fun a => (valT_coords x (b 0) v _ hv (z a) (ch a) (hz₁ a)).symm.trans ?_⟩
    have e := hsg (y a) (hzero' a)
    rw [hc a, hmax a, hy.extend_apply] at e
    have e' := (gs_mem_iff (K := K) (z a).left _ (hz₁ a) p _).1 ((gs_sub (y a) _ (hyU a) _ _).symm ▸ e)
    replace e' := sub_eq_zero.1 ((map_sub _ _ _).symm.trans ((EtBaseChange.valT_eq (T := K) _ _ (hz₁ a) _).symm.trans e'))
    refine (congrArg (valT (T := K) (z a).left (x.P.L.U (ch a))) (hsg' (ch a))).trans ?_
    exact (EtBaseChange.valT_eq (T := K) _ _ (hz₁ a) _).trans (e'.trans
      ((EtBaseChange.valT_eq (T := K) _ _ (hz₁ a) _).symm.trans (KoszulCx.valH_cst x (z a) _ (hz₁ a) _)))
  · let sg' : RR x (l - 0 * n) := comb x.P.A.hom v (b 0)
    have hv' : Coords x (b 0) v sg'.f := fun _ => rfl
    obtain ⟨sg, hsg⟩ := exists_cast x hl0.symm sg'
    obtain ⟨ta, hta⟩ := h₃ sg fun t ht => by
      obtain ⟨a, rfl⟩ := hzero t ht
      rw [hc a, hmax a]
      refine (gs_mem_iff (K := K) (z a).left _ (hz₁ a) p _).2 ?_
      refine (congrArg (valT (T := K) (z a).left (x.P.L.U (ch a))) (hsg (ch a))).trans ?_
      exact (valT_coords x (b 0) v _ hv' (z a) (ch a) (hz₁ a)).trans (congrFun hv a)
    choose w hw using fun i : Fin x.P.g => (hb 1 i.pos (ta i)).exists
    refine ⟨w, (hb 0 (Nat.zero_le _) sg').unique hv' ?_⟩
    have e := coords_sum x (b 0) _ _ fun i : Fin x.P.g =>
      KoszulCx.coords_mul x (b 0) (b 1) (m i 0 1) _ _ _ (hm i 0 i.pos) (hw i)
    exact fun i => (hsg i).symm.trans ((hta i).trans (e i))

end Geo

section Main

theorem secVia_mul {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ w} {a b c : ℕ}
    (h : (c : ℤ) = a + b) {s : RR x a} {s' : RR x' a} {t : RR x b} {t' : RR x' b} (hs : SecVia x' x φ w s' s)
    (ht : SecVia x' x φ w t' t) :
    SecVia x' x φ w (l := c) (KoszulCx.mulSec x'.P.L h s' t') (KoszulCx.mulSec x.P.L h s t) := by
  intro j i hle
  obtain rfl : c = a + b := by exact_mod_cast h
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (hs j i hle) (ht j i hle)).trans ?_)
  exact (mul_mul_mul_comm _ _ _ _).trans (congrArg₂ (· * ·) (pow_add _ _ _).symm (map_mul _ _ _).symm)

theorem isBasis_cast {R : Type} [CommRing R] {x : KeyIn R} {l N N' : ℕ} (h : N' = N) {b : Fin N → RR x l}
    (hb : IsBasis x b) : IsBasis x (fun k => b (k.cast h)) := by
  subst h
  exact hb

theorem coords_cast {R : Type} [CommRing R] {x : KeyIn R} {l N N' : ℕ} (h : N' = N) {b : Fin N → RR x l} {c f}
    (hb : Coords x b c f) : Coords x (fun k => b (k.cast h)) (fun k => c (k.cast h)) f := by
  subst h
  exact hb

theorem resolves_map (hL : Out.Laws) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R)
    (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (z : Fin d → Pt x)
    (ch : Fin d → x.P.L.ι) (hn : 1 ≤ n) (hl : x.P.g * n < l) (hb : ∀ j ≤ x.P.g, IsBasis x (b j)) (hz : EtZ x s z ch)
    (m) (hm : IsMul x l s b m) (K : Type) [Field K] [IsAlgClosed K] (f : R →+* K) :
    Resolves (N := fun j => (l - j * n) ^ x.P.g) (fun i j j' => (m i j j').map f)
      ((Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))).map f) := by
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange R K x f
  obtain ⟨hv₁, hv₂⟩ := GlobalTheory.KeyVia.main R K x x' f
  obtain ⟨φ, w, hw⟩ := hv₁.1 hx'
  obtain ⟨hsec, -, hco⟩ := hv₂ φ w hw
  have hg : x'.P.g = x.P.g := hw.2.1
  choose pb hpb using fun l s => (hsec l s).exists
  have hN : ∀ j, (l - j * n) ^ x'.P.g = (l - j * n) ^ x.P.g := fun j => congrArg ((l - j * n) ^ ·) hg
  let s' : Fin x'.P.g → RR x' n := fun i => pb n (s (i.cast hg))
  let b' : ∀ j, Fin ((l - j * n) ^ x'.P.g) → RR x' (l - j * n) := fun j k => pb _ (b j (k.cast (hN j)))
  obtain ⟨z', ch', u, hz', -, hu⟩ := etZ_baseChange R K x x' f φ w n d hg s s' z ch hw (fun i => hpb _ _) hz
  have hb' : ∀ j ≤ x'.P.g, IsBasis x' (b' j) := fun j hj => by
    have hj' : j ≤ x.P.g := hg ▸ hj
    have h1 : 1 ≤ l - j * n := by
      have := Nat.mul_le_mul_right n hj'
      omega
    exact isBasis_cast (hN j) ((GlobalTheory.KeyBasis.main hL R x (l - j * n) h1).2 (b j) (hb j hj') K f x' φ w
      (fun k => pb _ (b j k)) hw fun k => hpb _ _)
  have hm' : IsMul x' l s' b' (fun i j j' k k' => f (m (i.cast hg) j j' (k.cast (hN j)) (k'.cast (hN j')))) := by
    intro i j hj k
    have hj' : j < x.P.g := hg ▸ hj
    exact coords_cast (hN j) (hco _ _ (b j) (fun k => pb _ (b j k)) _ _ _ (fun k => hpb _ _)
      (secVia_mul (KoszulCx.cast_step hl hj') (hpb _ (s (i.cast hg))) (hpb _ (b (j + 1) (k.cast (hN (j + 1))))))
      (hm (i.cast hg) j hj' (k.cast (hN (j + 1)))))
  have H := resolves_field hL K x' n l d s' b' z' ch' hn (hg.symm ▸ hl) hb' hz' _ hm'
  refine Resolves.cast hg (fun j => l - j * n) _ _ (H.scale (fun a => u a ^ (l - 0 * n)) fun a k => ?_)
  exact (congrArg (_ * ·) (Units.val_pow_eq_pow_val _ _)).trans (hu _ _ _ a (hpb _ _))

theorem exists_kosVal : Out.Laws → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → EtZ x s z ch → d = x.P.g.factorial * n ^ x.P.g ∧ ∃ t : Rˣ, KosVal x l s z ch b t := by
  intro hL R _ _ _ x n l d s b z ch hn hl hb hz
  obtain ⟨⟨m, hm⟩, hcx⟩ := KoszulCx.koszul_isCx R x n l d s b z ch hl hb
  have hD := hcx m hm hz.1 hz.2.1
  let k := IsLocalRing.ResidueField R
  let f : k →+* AlgebraicClosure k := algebraMap _ _
  have H := resolves_map hL R x n l d s b z ch hn hl hb hz m hm (AlgebraicClosure k) (f.comp (IsLocalRing.residue R))
  obtain ⟨t, ht⟩ := GlobalTheory.TorsExists.exists_torsSq R _ kdeg _ hD (Ex.descend f _ (by
    rw [Matrix.map_map, ← RingHom.coe_comp, kosD_map]
    refine Resolves.ex H ?_
    rw [← kosD_map, ← Matrix.map_mul, hD.2, Matrix.map_zero _ (map_zero _)]))
  obtain ⟨-, u, rfl⟩ := GlobalTheory.TorsionUnique.torsSq_unique R _ kdeg _ t t hD ht ht
  refine ⟨?_, u, m, hm, ht⟩
  obtain ⟨_, -, -, e, -⟩ := ht
  have e' := (count_eq (N := fun j => (l - j * n) ^ x.P.g) e).trans
    (GlobalTheory.alternating_sum_choose_mul_sub_pow x.P.g n l hl.le)
  exact_mod_cast e'

end Main

end GlobalTheory.KeyKa.KoszulEx
end
