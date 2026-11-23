import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CochainLim

universe v u w w'
variable {C : Type u} [Category.{v} C] [Preadditive C]

def pb {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z : Cochain B L n) : Cochain A L n :=
  (Cochain.ofHom f).comp z (zero_add n)

theorem pb_v {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z : Cochain B L n) (p q : ℤ)
    (h : p + n = q) : (pb f z).v p q h = f.f p ≫ z.v p q h := by
  simp [pb]

theorem pb_pb {A B D L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (g : B ⟶ D) (z : Cochain D L n) :
    pb f (pb g z) = pb (f ≫ g) z := by
  ext p q h; simp [pb_v]

theorem pb_add {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z z' : Cochain B L n) :
    pb f (z + z') = pb f z + pb f z' := by simp [pb]

theorem pb_sub {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z z' : Cochain B L n) :
    pb f (z - z') = pb f z - pb f z' := by simp [pb]

theorem pb_zero {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) :
    pb f (0 : Cochain B L n) = 0 := by simp [pb]

theorem δ_pb {A B L : CochainComplex C ℤ} {n : ℤ} (f : A ⟶ B) (z : Cochain B L n) (m : ℤ) :
    δ n m (pb f z) = pb f (δ n m z) := by simp [pb]

section Rel
variable {I : Type w} [Category.{w'} I] [IsCofiltered I] {K : I ⥤ CochainComplex C ℤ} (c : Cone K)
  (L : CochainComplex C ℤ)

def Q (n m a : ℤ) : Prop :=
  ∀ (i : I) (w : Cochain (K.obj i) L m) (z : Cochain c.pt L n), δ m (m + 1) w = 0 →
    δ n m z = pb (c.π.app i) w → (∀ p q (h : p + m = q), a < p → w.v p q h = 0) →
    (∀ p q (h : p + n = q), a < p → z.v p q h = 0) →
    ∃ (k : I) (f : k ⟶ i) (b : Cochain (K.obj k) L n) (y : Cochain c.pt L (n - 1)),
      δ n m b = pb (K.map f) w ∧ pb (c.π.app k) b = z + δ (n - 1) n y

theorem Q_base (hL : ∀ p : ℤ, p < 0 → IsZero (L.X p)) (n m a : ℤ) (ham : a + m < 0) (han : a + n < 0) :
    Q c L n m a := by
  intro i w z hw hz hw0 hz0
  have w0 : w = 0 := by
    ext p q h
    rw [Cochain.zero_v]
    by_cases hp : a < p
    · exact hw0 p q h hp
    · exact (hL q (by omega)).eq_of_tgt _ _
  have z0 : z = 0 := by
    ext p q h
    rw [Cochain.zero_v]
    by_cases hp : a < p
    · exact hz0 p q h hp
    · exact (hL q (by omega)).eq_of_tgt _ _
  exact ⟨i, 𝟙 i, 0, 0, by simp [w0, pb_zero], by simp [z0, pb_zero]⟩

end Rel

section Step
variable {I : Type w} [Category.{w'} I] [IsCofiltered I] {K : I ⥤ CochainComplex C ℤ} (c : Cone K)
  (L : CochainComplex C ℤ)

theorem Q_of_Q_sub_one
    (hA : ∀ (p s s' : ℤ), s' + 1 = s → ∀ t : c.pt.X p ⟶ L.X s', t ≫ L.d s' s = 0 →
      ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s') (y : c.pt.X p ⟶ L.X (s' - 1)),
        u ≫ L.d s' s = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s' - 1) s')
    (hB : ∀ (p s : ℤ) (i : I) (u : (K.obj i).X p ⟶ L.X s), u ≫ L.d s (s + 1) = 0 →
      (∃ y : c.pt.X p ⟶ L.X (s - 1), (c.π.app i).f p ≫ u = y ≫ L.d (s - 1) s) →
      ∃ (k : I) (f : k ⟶ i) (y : (K.obj k).X p ⟶ L.X (s - 1)), (K.map f).f p ≫ u = y ≫ L.d (s - 1) s)
    (n m : ℤ) (hnm : n + 1 = m) (p : ℤ) (ih : Q c L n m (p - 1)) : Q c L n m p := by
  intro i w z hw hz hw0 hz0
  obtain ⟨s, hs⟩ : ∃ s, p + m = s := ⟨_, rfl⟩
  have hwc : w.v p s hs ≫ L.d s (s + 1) = 0 := by
    have := Cochain.congr_v hw p (s + 1) (by omega)
    rw [δ_v m (m + 1) rfl w p (s + 1) (by omega) s (p + 1) (by omega) rfl, Cochain.zero_v,
      hw0 (p + 1) (s + 1) (by omega) (by omega), comp_zero, smul_zero, add_zero] at this
    exact this
  have hzw : (c.π.app i).f p ≫ w.v p s hs = z.v p (s - 1) (by omega) ≫ L.d (s - 1) s := by
    have := Cochain.congr_v hz p s hs
    rw [δ_v n m hnm z p s hs (s - 1) (p + 1) rfl rfl,
      hz0 (p + 1) s (by omega) (by omega), comp_zero, smul_zero, add_zero, pb_v] at this
    exact this.symm
  obtain ⟨k, f, y', hy'⟩ := hB p s i (w.v p s hs) hwc ⟨_, hzw⟩
  have hδσ := Cochain.δ_single y' n m hnm (p - 1) s (by omega) (by omega)
  set σ : Cochain (K.obj k) L n := Cochain.single y' n with hσ
  set w' := pb (K.map f) w - δ n m σ with hw'def
  set z' := z - pb (A := c.pt) (c.π.app k) σ with hz'def
  have hw' : δ m (m + 1) w' = 0 := by
    simp only [hw'def, δ_sub, δ_pb, hw, pb_zero, δ_δ, sub_zero]
  have hz' : δ n m z' = pb (c.π.app k) w' := by
    simp only [hz'def, hw'def, δ_sub, δ_pb, hz, pb_sub, pb_pb, c.w f]
  have hw'0 : ∀ p'' q (h : p'' + m = q), p - 1 < p'' → w'.v p'' q h = 0 := by
    intro p'' q h hp''
    by_cases hpp : p'' = p
    · subst hpp
      obtain rfl : q = s := by omega
      simp only [hw'def, hδσ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v, hy',
        Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p'' - 1 by omega), smul_zero,
        add_zero, sub_self]
    · simp only [hw'def, hδσ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v,
        hw0 p'' q h (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpp,
        Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p - 1 by omega), smul_zero, add_zero, comp_zero,
        sub_self]
  have hz'0 : ∀ p'' q (h : p'' + n = q), p < p'' → z'.v p'' q h = 0 := by
    intro p'' q h hp''
    simp only [hz'def, hσ, Cochain.sub_v, pb_v, hz0 p'' q h hp'',
      Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p by omega), comp_zero, sub_self]
  have hz'c : z'.v p (s - 1) (by omega) ≫ L.d (s - 1) s = 0 := by
    have := Cochain.congr_v hz' p s hs
    rw [δ_v n m hnm z' p s hs (s - 1) (p + 1) rfl rfl,
      hz'0 (p + 1) s (by omega) (by omega), comp_zero, smul_zero, add_zero, pb_v,
      hw'0 p s hs (by omega), comp_zero] at this
    exact this
  obtain ⟨j, u2, y2, hu2c, hu2⟩ := hA p s (s - 1) (by omega) _ hz'c
  let l := IsCofiltered.min j k
  let g : l ⟶ j := IsCofiltered.minToLeft j k
  let h : l ⟶ k := IsCofiltered.minToRight j k
  have hδv := Cochain.δ_single ((K.map g).f p ≫ u2) n m hnm (p - 1) s (by omega) (by omega)
  rw [Category.assoc, hu2c, comp_zero, Cochain.single_zero, zero_add] at hδv
  set v : Cochain (K.obj l) L n := Cochain.single ((K.map g).f p ≫ u2) n with hv
  have hδρ := Cochain.δ_single y2 (n - 1) n (by omega) (p - 1) (s - 1) (by omega) (by omega)
  set ρ : Cochain c.pt L (n - 1) := Cochain.single y2 (n - 1) with hρ
  set w'' := pb (K.map h) w' - δ n m v with hw''def
  set z'' := z' - pb (A := c.pt) (c.π.app l) v + δ (n - 1) n ρ with hz''def
  have hw'' : δ m (m + 1) w'' = 0 := by
    simp only [hw''def, δ_sub, δ_pb, hw', pb_zero, δ_δ, sub_zero]
  have hz'' : δ n m z'' = pb (c.π.app l) w'' := by
    simp only [hz''def, hw''def, δ_add, δ_sub, δ_pb, hz', δ_δ, add_zero, pb_sub, pb_pb, c.w h]
  have hw''0 : ∀ p'' q (hh : p'' + m = q), p - 1 < p'' → w''.v p'' q hh = 0 := by
    intro p'' q hh hp''
    simp only [hw''def, hδv, Cochain.sub_v, Cochain.units_smul_v, pb_v, hw'0 p'' q hh hp'',
      Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p - 1 by omega), smul_zero, comp_zero, sub_self]
  have hz''0 : ∀ p'' q (hh : p'' + n = q), p - 1 < p'' → z''.v p'' q hh = 0 := by
    intro p'' q hh hp''
    by_cases hpp : p'' = p
    · subst hpp
      obtain rfl : q = s - 1 := by omega
      simp only [hz''def, hv, hδρ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v,
        Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p'' - 1 by omega), smul_zero,
        add_zero]
      rw [← Category.assoc, ← HomologicalComplex.comp_f, c.w g, hu2]
      abel
    · simp only [hz''def, hv, hδρ, Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v, pb_v,
        hz'0 p'' q hh (by omega), Cochain.single_v_eq_zero _ _ _ _ _ hpp,
        Cochain.single_v_eq_zero _ _ _ _ _ (show p'' ≠ p - 1 by omega), smul_zero, add_zero, comp_zero,
        sub_self]
  obtain ⟨k', f', b'', y'', hb'', hby''⟩ := ih l w'' z'' hw'' hz'' hw''0 hz''0
  refine ⟨k', f' ≫ h ≫ f, b'' + pb (K.map f') v + pb (K.map (f' ≫ h)) σ, y'' + ρ, ?_, ?_⟩
  · simp only [δ_add, δ_pb, hb'', hw''def, hw'def, pb_sub, pb_pb, Functor.map_comp, Category.assoc]
    abel
  · simp only [pb_add, pb_pb, c.w, hby'', hz''def, hz'def, δ_add]
    abel

end Step

section Main
variable {I : Type w} [Category.{w'} I] [IsCofiltered I] {K : I ⥤ CochainComplex C ℤ} (c : Cone K)
  (L : CochainComplex C ℤ)

theorem relative
    (hK : ∀ i (p : ℤ), 0 < p → IsZero ((K.obj i).X p)) (hc : ∀ p : ℤ, 0 < p → IsZero (c.pt.X p))
    (hL : ∀ p : ℤ, p < 0 → IsZero (L.X p))
    (hA : ∀ (p s : ℤ) (t : c.pt.X p ⟶ L.X s), t ≫ L.d s (s + 1) = 0 →
      ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s) (y : c.pt.X p ⟶ L.X (s - 1)),
        u ≫ L.d s (s + 1) = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s - 1) s)
    (hB : ∀ (p s : ℤ) (i : I) (u : (K.obj i).X p ⟶ L.X s), u ≫ L.d s (s + 1) = 0 →
      (∃ y : c.pt.X p ⟶ L.X (s - 1), (c.π.app i).f p ≫ u = y ≫ L.d (s - 1) s) →
      ∃ (k : I) (f : k ⟶ i) (y : (K.obj k).X p ⟶ L.X (s - 1)), (K.map f).f p ≫ u = y ≫ L.d (s - 1) s)
    (n m : ℤ) (hnm : n + 1 = m) (i : I) (w : Cochain (K.obj i) L m) (z : Cochain c.pt L n)
    (hw : δ m (m + 1) w = 0) (hz : δ n m z = pb (c.π.app i) w) :
    ∃ (k : I) (f : k ⟶ i) (b : Cochain (K.obj k) L n) (y : Cochain c.pt L (n - 1)),
      δ n m b = pb (K.map f) w ∧ pb (c.π.app k) b = z + δ (n - 1) n y := by
  have hA' : ∀ (p s s' : ℤ), s' + 1 = s → ∀ t : c.pt.X p ⟶ L.X s', t ≫ L.d s' s = 0 →
      ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s') (y : c.pt.X p ⟶ L.X (s' - 1)),
        u ≫ L.d s' s = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s' - 1) s' := by
    intro p s s' h
    subst h
    exact hA p s'
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = -|m| - 2 := ⟨_, rfl⟩
  have hall : ∀ k : ℕ, Q c L n m (a + k) := by
    intro k
    induction k with
    | zero =>
      simpa using Q_base c L hL n m a (by linarith [le_abs_self m]) (by linarith [le_abs_self m])
    | succ k ih =>
      have := Q_of_Q_sub_one c L hA' hB n m hnm (a + (k + 1 : ℕ)) (by
        rw [show a + ((k + 1 : ℕ) : ℤ) - 1 = a + k by push_cast; ring]; exact ih)
      exact this
  have h0 := hall (-a).toNat
  rw [show a + ((-a).toNat : ℤ) = 0 by
    have : 0 ≤ -a := by rw [ha]; linarith [abs_nonneg m]
    omega] at h0
  exact h0 i w z hw hz (fun p q h hp => (hK i p hp).eq_of_src _ _) (fun p q h hp => (hc p hp).eq_of_src _ _)

end Main

end GlobalTheory.CochainLim

open GlobalTheory.CochainLim in

theorem GlobalTheory.EtC.cont_cx_of_degreewise : ∀ (R : Type) [CommRing R] (I : Type) [SmallCategory I] [IsCofiltered I] (K : I ⥤ Cx R) (c : Cone K) (L : Cx R), (∀ i (p : ℤ), 0 < p → IsZero ((K.obj i).X p)) → (∀ p : ℤ, 0 < p → IsZero (c.pt.X p)) → (∀ p : ℤ, p < 0 → IsZero (L.X p)) → (∀ p s : ℤ, (∀ t : c.pt.X p ⟶ L.X s, t ≫ L.d s (s + 1) = 0 → ∃ (i : I) (u : (K.obj i).X p ⟶ L.X s) (y : c.pt.X p ⟶ L.X (s - 1)), u ≫ L.d s (s + 1) = 0 ∧ (c.π.app i).f p ≫ u = t + y ≫ L.d (s - 1) s) ∧ ∀ (i : I) (u : (K.obj i).X p ⟶ L.X s), u ≫ L.d s (s + 1) = 0 → (∃ y : c.pt.X p ⟶ L.X (s - 1), (c.π.app i).f p ≫ u = y ≫ L.d (s - 1) s) → ∃ (k : I) (f : k ⟶ i) (y : (K.obj k).X p ⟶ L.X (s - 1)), (K.map f).f p ≫ u = y ≫ L.d (s - 1) s) → ∀ n : ℤ, (∀ x : CohomologyClass c.pt L n, ∃ (i : I) (y : CohomologyClass (K.obj i) L n), cpre (Cocycle.ofHom (c.π.app i)) L n n (zero_add n) y = x) ∧ ∀ (i : I) (y : CohomologyClass (K.obj i) L n), cpre (Cocycle.ofHom (c.π.app i)) L n n (zero_add n) y = 0 → ∃ (k : I) (f : k ⟶ i), cpre (Cocycle.ofHom (K.map f)) L n n (zero_add n) y = 0 := by
  intro R _ I _ _ K c L hK hc hL hAB n
  have rel := relative c L hK hc hL (fun p s => (hAB p s).1) (fun p s => (hAB p s).2)
  constructor
  · intro x
    obtain ⟨ζ, rfl⟩ := x.mk_surjective
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
    obtain ⟨k, f, b, y, hb, hby⟩ := rel n (n + 1) rfl i 0 ζ.1 (by simp)
      (by rw [Cocycle.δ_eq_zero, pb_zero])
    rw [pb_zero] at hb
    refine ⟨k, CohomologyClass.mk (Cocycle.mk b (n + 1) rfl hb), ?_⟩
    rw [cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨y, ?_⟩
    rw [Cocycle.coe_sub]
    change _ = pb (A := c.pt) (c.π.app k) b - ζ.1
    rw [hby]
    abel
  · intro i y hy
    obtain ⟨β, rfl⟩ := y.mk_surjective
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hy
    obtain ⟨γ, hγ⟩ := hy
    obtain ⟨k, f, b, y, hb, -⟩ := rel (n - 1) n (by omega) i β.1 γ (Cocycle.δ_eq_zero _ _) hγ
    refine ⟨k, f, ?_⟩
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨b, hb⟩

end
