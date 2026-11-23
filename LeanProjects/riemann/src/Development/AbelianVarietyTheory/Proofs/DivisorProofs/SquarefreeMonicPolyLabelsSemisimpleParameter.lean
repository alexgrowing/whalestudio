import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamExists

open GlobalTheory.GoodCharsCompare

variable {p : ℕ} [Fact p.Prime]

theorem thetaOf_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have hp : 0 < p ^ d - 1 := g_pow_sub_pos hd
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dif_pos h]
  have hfin : IsOfFinOrder (L.gen d) := by
    rw [← orderOf_pos_iff, L.gen_order d hd]; exact hp
  have h1 := hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  rw [L.gen_order d hd] at h1
  have h2 : L.teich x ^ (p ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [pow_eq_pow_mod _ h2, pow_eq_pow_mod n h2]
  exact congrArg _ h1.symm

theorem exists_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) (u : Tor p d) :
    ∃ n : ℕ, ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ n := by
  haveI : NeZero (p ^ d - 1) := ⟨(g_pow_sub_pos hd).ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
  exact ⟨n, hn.symm⟩

theorem exists_char (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1) :
    ∃ θ : Tor p d →* ℂˣ, LabelsChar L θ x := by
  let φ : Tor p d →* ℂ :=
    { toFun := fun u => GlobalTheory.GLq.thetaOf L d x ((u : (Fbar p)ˣ) : Fbar p)
      map_one' := by
        have := thetaOf_gen_pow L hd hx 0
        simpa using this
      map_mul' := by
        intro u v
        obtain ⟨n, hn⟩ := exists_gen_pow L hd u
        obtain ⟨m, hm⟩ := exists_gen_pow L hd v
        rw [Subgroup.coe_mul, Units.val_mul, hn, hm, ← pow_add, thetaOf_gen_pow L hd hx,
          thetaOf_gen_pow L hd hx, thetaOf_gen_pow L hd hx, pow_add] }
  exact ⟨φ.toHomUnits, hx, fun u => rfl⟩

theorem minpoly_eq_of_mem {y z : Fbar p} (h : z ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y)) :
    minpoly (ZMod p) z = minpoly (ZMod p) y :=
  (eq_minpoly (minpoly.monic (isInt y)) (minpoly.irreducible (isInt y)) h).symm

theorem self_mem (y : Fbar p) : y ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y) :=
  mem_roots_minpoly.2 ⟨0, by simp⟩

theorem exists_rootPoly (r : ℕ) (f : (ZMod p)[X]) (hm : f.Monic) (hr : f.natDegree = r) (h0 : f.coeff 0 ≠ 0)
    (hs : Squarefree f) : ∃ (b : Fin r → Fin r) (x : Cyc b → Fbar p), IsRootPoly x f := by
  classical
  have hf := hm.ne_zero
  have hnd := (squarefree_iff hf).1 hs
  have hz0 := (coeff_zero_iff hf).1 h0
  let S := (Formalism.CyclotomicNorms.rootsBar f).toFinset
  have hS : S.card = r := by rw [Multiset.toFinset_card_of_nodup hnd, card_rootsBar, hr]
  let e : Fin r ≃ S := (Finset.equivFinOfCardEq hS).symm
  let z : Fin r → Fbar p := fun i => (e i : Fbar p)
  have zinj : Function.Injective z := Subtype.val_injective.comp e.injective
  have zmem : ∀ i, z i ∈ Formalism.CyclotomicNorms.rootsBar f := fun i => Multiset.mem_toFinset.1 (e i).2
  have zsurj : ∀ w ∈ Formalism.CyclotomicNorms.rootsBar f, ∃ i, z i = w := fun w hw =>
    ⟨e.symm ⟨w, Multiset.mem_toFinset.2 hw⟩, by simp [z]⟩
  let m : Fin r → (ZMod p)[X] := fun i => minpoly (ZMod p) (z i)
  have hsub : ∀ i w, w ∈ Formalism.CyclotomicNorms.rootsBar (m i) → w ∈ Formalism.CyclotomicNorms.rootsBar f := by
    intro i w hw
    obtain ⟨k, rfl⟩ := mem_roots_minpoly.1 hw
    rw [mem_rootsBar hf]
    exact aeval_pow_g _ _ _ ((mem_rootsBar hf).1 (zmem i))
  have hb : ∃ b : Fin r → Fin r, (∀ i, m (b i) = m i) ∧ ∀ i j, m i = m j → b i = b j := by
    refine ⟨fun i => @Function.invFun _ _ ⟨i⟩ m (m i), fun i => @Function.invFun_eq _ _ ⟨i⟩ m _ ⟨i, rfl⟩, ?_⟩
    intro i j h
    simp only [h]
  obtain ⟨b, hb1, hb2⟩ := hb
  have hbc : ∀ c : Cyc b, ∀ i, b i = c.1 ↔ m i = m c.1 := by
    rintro ⟨c, j, rfl⟩ i
    exact ⟨fun h => by rw [← hb1 i]; exact congrArg m h, fun h => hb2 _ _ (h.trans (hb1 j))⟩
  have hlen : ∀ c : Cyc b, cycLen b c = dg (z c.1) := by
    intro c
    rw [dg, ← card_rootsBar, ← Multiset.toFinset_card_of_nodup (nodup_minpoly _), cycLen, Fintype.card_subtype]
    refine Finset.card_bij (fun i _ => z i) ?_ ?_ ?_
    · intro i hi
      have h1 : m i = m c.1 := (hbc c i).1 (Finset.mem_filter.1 hi).2
      rw [Multiset.mem_toFinset]
      exact (show minpoly (ZMod p) (z i) = minpoly (ZMod p) (z c.1) from h1) ▸ self_mem (z i)
    · intro i _ j _ h
      exact zinj h
    · intro w hw
      rw [Multiset.mem_toFinset] at hw
      obtain ⟨i, rfl⟩ := zsurj w (hsub _ w hw)
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hbc c i).2 (minpoly_eq_of_mem hw)⟩, rfl⟩
  refine ⟨b, fun c => z c.1, fun c => ?_, hm, ?_⟩
  · rw [hlen]
    exact pow_dg (fun h => hz0 (h ▸ zmem _))
  · rw [Multiset.Nodup.ext hnd (Finset.univ.nodup.map ?_)]
    · intro w
      rw [Multiset.mem_map]
      constructor
      · intro hw
        obtain ⟨i, rfl⟩ := zsurj w hw
        let c : Cyc b := ⟨b i, i, rfl⟩
        have h1 : z i ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) (z c.1)) :=
          (show minpoly (ZMod p) (z i) = minpoly (ZMod p) (z c.1) from (hb1 i).symm) ▸ self_mem (z i)
        rw [← Multiset.mem_toFinset, roots_minpoly] at h1
        obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 h1
        exact ⟨⟨c, ⟨k, by rw [hlen]; exact Finset.mem_range.1 hk⟩⟩, Finset.mem_univ_val _, hk'⟩
      · rintro ⟨y, -, rfl⟩
        exact hsub y.1.1 _ (mem_roots_minpoly.2 ⟨_, rfl⟩)
    · rintro ⟨c, i⟩ ⟨c', j⟩ h
      have h' : z c.1 ^ p ^ (i : ℕ) = z c'.1 ^ p ^ (j : ℕ) := h
      have e1 := minpoly_eq_of_mem (y := z c.1) (mem_roots_minpoly.2 ⟨i, rfl⟩)
      have e2 := minpoly_eq_of_mem (y := z c'.1) (mem_roots_minpoly.2 ⟨j, rfl⟩)
      have e3 : m c.1 = m c'.1 := e1.symm.trans (h' ▸ e2)
      have e4 : c = c' := Subtype.ext (((hbc c c.1).2 rfl).symm.trans ((hbc c' c.1).2 e3))
      subst e4
      have := (frobenius_orbit_degreeOverPrimeFieldFbar (z c.1)).2 i (hlen c ▸ i.2) j (hlen c ▸ j.2) h'
      rw [Fin.ext this]

theorem param_exists : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (f : (ZMod p)[X]),
    f.Monic → f.natDegree = r → f.coeff 0 ≠ 0 → Squarefree f →
    ∃ (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p), Labels L s x f := by
  intro p _ L r f hm hr h0 hs
  obtain ⟨b, x, hx⟩ := exists_rootPoly r f hm hr h0 hs
  choose θ hθ using fun c => exists_char L (cycLen_pos b c) (hx.1 c)
  exact ⟨⟨b, θ⟩, x, hθ, hx⟩

end GlobalTheory.ParamExists

end
