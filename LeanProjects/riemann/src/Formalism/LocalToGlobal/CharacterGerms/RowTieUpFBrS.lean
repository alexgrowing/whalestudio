import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrR

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

def PlaceSt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R] [Algebra ℤ_[l] R],
    (l : R) ∈ maximalIdeal R → ¬ ((l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
    ∀ (d : ℕ) [NeZero d] (em : ZMod d → OE →+* R),
      (∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) →
      (∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) →
      (∃ ε : OE, (∃ y, ε * ε - ε = (l : OE) * y) ∧ (∀ a, em a ε - 1 ∈ maximalIdeal R) ∧
        ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) → PlaceIn l OE R d em

def EigFreeSt : Prop :=
  ∀ (C : Type) [Field C] (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], vm.Integers R →
    ∀ (n : ℕ) (ι : Type) (L : ι → Matrix (Fin n) (Fin n) R) (χ : ι → R),
      ∃ (s : ℕ) (W : Fin s → Fin n → R), (∀ i a, (L a).mulVec (W i) = χ a • W i) ∧
        ∀ v : Fin n → R, (∀ a, (L a).mulVec v = χ a • v) → ∃! c : Fin s → R, ∑ i, c i • W i = v

section Eig

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {R : Type} [CommRing R] [Algebra R C]

theorem linAct_toC {Y : FBChart C V OE dd} (actR : OE → Fin dd → PS R 1 dd)
    (hact : ∀ a i, Y.B.A.act a i = toC (actR a i)) (x : OE) (v : Fin dd → R) (i : Fin dd) :
    algebraMap R C ((linPart (actR x)).mulVec v i) = linAct (Y.B.A.act x) (fun j => algebraMap R C (v j)) i := by
  simp only [linAct, hact, toC, MvPowerSeries.coeff_map, linPart, Matrix.mulVec, dotProduct, Matrix.of_apply,
    map_sum, map_mul]

theorem eig_at {Y : FBChart C V OE dd} (p : PairData Y d I) (hinj : Function.Injective (algebraMap R C))
    (hsurj : ∀ x : C, V.Ge 0 x → ∃ r : R, algebraMap R C r = x) (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (actR : OE → Fin dd → PS R 1 dd) (hact : ∀ a i, Y.B.A.act a i = toC (actR a i))
    (τ : OE →+* R) (g : Fin 2) (a : ZMod d) (hτ : ∀ x, algebraMap R C (τ x) = p.em g a x) :
    ∃ (s : ℕ) (W : Fin s → Fin dd → R) (e : Fin s ≃ {x : I g // p.ty g x = a}), IsEigBasis actR τ W ∧
      ∀ c i, algebraMap R C (W c i) = p.u g (e c) i := by
  choose lift hlift using hsurj
  let S := {x : I g // p.ty g x = a}
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let W : Fin (Fintype.card S) → Fin dd → R := fun c i => lift (p.u g (e c) i) (p.u_int g (e c) i)
  have hu : ∀ c i, algebraMap R C (W c i) = p.u g (e c) i := fun c i => hlift _ _
  refine ⟨Fintype.card S, W, e, ?_, hu⟩
  unfold IsEigBasis
  refine ⟨fun c a' => ?_, fun v hv => ?_⟩
  · funext i
    apply hinj
    rw [linAct_toC actR hact a' (W c) i]
    have hW : (fun j => algebraMap R C (W c j)) = p.u g (e c) := funext (hu c)
    rw [hW, p.u_eig g (e c) a', (e c).2]
    simp [hτ, hu]
  · obtain ⟨vC, hvC⟩ : ∃ vC : Fin dd → C, ∀ j, vC j = algebraMap R C (v j) := ⟨_, fun _ => rfl⟩
    have heig : ∀ x, linAct (Y.B.A.act x) vC = p.em g a x • vC := by
      intro x
      funext i
      have h1 : vC = fun j => algebraMap R C (v j) := funext hvC
      rw [h1, ← linAct_toC actR hact x v i, hv x]
      simp [hτ]
    obtain ⟨b, hbsupp, hvb⟩ := p.u_full g a vC heig
    obtain ⟨w, hw1, hw2⟩ := p.u_sat g
    have hvb' : ∀ j, vC j = ∑ c, b c * p.u g c j := by
      intro j
      rw [hvb]
      simp [Finset.sum_apply]
    have hcoef : ∀ c', ∑ x, vC x * w x c' = b c' := by
      intro c'
      simp_rw [hvb', Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum, hw2]
      simp
    have hbint : ∀ c, V.Ge 0 (b c) := by
      intro c
      rw [← hcoef c]
      exact VF.Ge.sum (fun x _ => by rw [hvC x]; exact (hR (v x)).mul_int (hw1 x c))
    have hsum : ∀ F : I g → C, (∀ c, p.ty g c ≠ a → F c = 0) →
        ∑ c, F c = ∑ k : Fin (Fintype.card S), F (e k) := by
      intro F hF
      rw [← Fintype.sum_subtype_add_sum_subtype (fun c => p.ty g c = a) F]
      rw [Fintype.sum_eq_zero (fun x : {c // ¬ p.ty g c = a} => F x) (fun x => hF x x.2), add_zero]
      exact (Equiv.sum_comp e (fun x : S => F x)).symm
    refine ⟨fun k => lift (b (e k)) (hbint (e k)), ?_, ?_⟩
    · funext j
      apply hinj
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hlift, hu]
      rw [← hsum (fun c => b c * p.u g c j) (fun c hc => by rw [hbsupp c hc, zero_mul]), ← hvb', hvC]
    · intro c' hc'
      funext k
      apply hinj
      rw [hlift, ← hcoef (e k)]
      have h2 : ∀ j, vC j = ∑ m, algebraMap R C (c' m) * p.u g (e m) j := by
        intro j
        rw [hvC, ← hc']
        simp [Finset.sum_apply, map_sum, hu]
      simp_rw [h2, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [mul_assoc, ← Finset.mul_sum, hw2]
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single k]
      · simp
      · intro m _ hm
        have hne : (↑(e m) : I g) ≠ ↑(e k) := fun h => hm (e.injective (Subtype.ext h))
        simp [hne]
      · intro h
        exact absurd (Finset.mem_univ k) h

theorem eigIn_of_free (hFree : EigFreeSt) {Y : FBChart C V OE dd} (p : PairData Y d I) (vm : Valuation C NNReal)
    (hv : vm.Integers R) (hsurj : ∀ x : C, V.Ge 0 x → ∃ r : R, algebraMap R C r = x)
    (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (actR : OE → Fin dd → PS R 1 dd) (hact : ∀ a i, Y.B.A.act a i = toC (actR a i))
    (emR : Fin 2 → ZMod d → OE →+* R) (hem : ∀ g a x, algebraMap R C (emR g a x) = p.em g a x) :
    EigIn p R actR emR := by
  have hsep : ∀ g a g' a', emR g a = emR g' a' → g = g' ∧ a = a' := by
    intro g a g' a' h
    by_contra hne
    have hne' : (g, a) ≠ (g', a') := fun h' => hne (by simpa using h')
    obtain ⟨x, hx⟩ := p.em_sep (g, a) (g', a') hne'
    have h1 : p.em g a x = p.em g' a' x := by rw [← hem, ← hem, h]
    dsimp only at hx
    rw [h1, sub_self, AddValuation.map_zero] at hx
    simp at hx
  have key : ∀ τ : OE →+* R, ∃ (s : ℕ) (W : Fin s → Fin dd → R), IsEigBasis actR τ W ∧
      ∀ g a, emR g a = τ → ∃ e : Fin s ≃ {x : I g // p.ty g x = a},
        ∀ c i, algebraMap R C (W c i) = p.u g (e c) i := by
    intro τ
    by_cases h : ∃ g a, emR g a = τ
    · obtain ⟨g, a, rfl⟩ := h
      obtain ⟨s, W, e, hb, hu⟩ := eig_at p hv.hom_inj hsurj hR actR hact (emR g a) g a (hem g a)
      refine ⟨s, W, hb, fun g' a' h' => ?_⟩
      obtain ⟨rfl, rfl⟩ := hsep g' a' g a h'
      exact ⟨e, hu⟩
    · push_neg at h
      obtain ⟨s, W, h1, h2⟩ := hFree C vm R hv dd OE (fun x => linPart (actR x)) τ
      refine ⟨s, W, ?_, fun g a h' => absurd h' (h g a)⟩
      unfold IsEigBasis
      exact ⟨h1, h2⟩
  choose r W hW using key
  unfold EigIn
  exact ⟨r, W, fun τ => (hW τ).1, fun g a => (hW (emR g a)).2 g a rfl⟩

end Eig

end UpFBr

end Formalism.L2.FormalSeriesBounds
