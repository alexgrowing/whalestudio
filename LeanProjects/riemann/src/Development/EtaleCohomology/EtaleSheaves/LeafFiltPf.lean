import Development.EtaleCohomology.EtaleSheaves.LeafSSCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafFiltPf

abbrev Sg {R : Type} [CommRing R] (X : Shv R) : Cx R := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj X

variable {R : Type} [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ)

theorem coe_sub' {K L : Cx R} {m : ℤ} (a b : Cocycle K L m) :
    ((a - b : Cocycle K L m) : Cochain K L m) = (a : Cochain K L m) - (b : Cochain K L m) := rfl

theorem coe_zero' {K L : Cx R} {m : ℤ} : ((0 : Cocycle K L m) : Cochain K L m) = 0 := rfl

theorem res_zero (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) := by
  have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 q (by omega)

def V (s : ℤ) (z : Cocycle K (res R F) n) : Prop := ∀ p q (h : p + n = q), s < p → z.1.v p q h = 0

def S (s : ℤ) : Set (HK R K F n) := {x | ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z}

theorem memS {s : ℤ} {x : HK R K F n} (h : x ∈ S K F n s) :
    ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z := h

theorem cocyc (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    z.1.v s d hd ≫ (res R F).d d (d + 1) = 0 := by
  have h0 := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) s (d + 1) (by omega)
  rw [δ_v n (n + 1) rfl _ s (d + 1) _ d (s + 1) (by omega) rfl, hz (s + 1) (d + 1) (by omega) (by omega)] at h0
  simpa using h0

def clsC (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    Cocycle (Sg (K.X s)) (res R F) d :=
  Cocycle.fromSingleMk (z.1.v s d hd) (zero_add d) (d + 1) rfl (cocyc K F n s d hd z hz)

theorem clsC_v (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    (clsC K F n s d hd z hz).1.v 0 d (zero_add d) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd :=
  Cochain.fromSingleMk_v _ _

theorem CB (X : Shv R) (d : ℤ) (c : Cocycle (Sg X) (res R F) d) (hc : CohomologyClass.mk c = 0) (e : ℤ)
    (he : e + 1 = d) : ∃ β : Cochain (Sg X) (res R F) e,
      β.v 0 e (zero_add e) ≫ (res R F).d e d = c.1.v 0 d (zero_add d) := by
  obtain ⟨m, hm, β, hβ⟩ := (CohomologyClass.mk_eq_zero_iff c).1 hc
  obtain rfl : e = m := by omega
  refine ⟨β, ?_⟩
  have := Cochain.congr_v hβ 0 d (zero_add d)
  rw [δ_v e d hm β 0 d _ e 1 (by omega) rfl] at this
  have hz1 : IsZero ((Sg X).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
  rw [hz1.eq_of_tgt ((Sg X).d 0 1) 0] at this
  simpa using this

theorem KL (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) (e : ℤ) (he : e + 1 = d)
    (β : Cochain (Sg (K.X s)) (res R F) e)
    (hβ : β.v 0 e (zero_add e) ≫ (res R F).d e d =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd) :
    ∃ w : Cocycle K (res R F) n, CohomologyClass.mk w = CohomologyClass.mk z ∧ V K F n (s - 1) w := by
  let g : K.X s ⟶ (res R F).X e :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).inv ≫ β.v 0 e (zero_add e)
  let hh : Cochain K (res R F) (n - 1) := Cochain.single g (n - 1)
  let D : Cocycle K (res R F) n := Cocycle.mk (δ (n - 1) n hh) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - D, ?_, ?_⟩
  · have hD : CohomologyClass.mk D = 0 := (CohomologyClass.mk_eq_zero_iff D).2 ⟨n - 1, by omega, hh, rfl⟩
    rw [CohomologyClass.mk_sub, hD, sub_zero]
  · intro p q hpq hp
    have hDv : D.1.v p q hpq = (δ (n - 1) n hh).v p q hpq := rfl
    simp only [coe_sub', Cochain.sub_v, hDv]
    rw [δ_v (n - 1) n (by omega) hh p q hpq (q - 1) (p + 1) rfl rfl]
    rcases lt_or_eq_of_le (show s ≤ p by omega) with h | h
    · rw [hz p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp
    · subst h
      obtain rfl : q = d := by omega
      obtain rfl : e = q - 1 := by omega
      rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp only [g, Category.assoc, hβ, Iso.inv_hom_id_assoc, comp_zero, smul_zero, add_zero, sub_self]

theorem step (s d : ℤ) (hd : s + n = d) [Finite (HK R (Sg (K.X s)) F d)] (hS : (S K F n (s - 1)).Finite) :
    (S K F n s).Finite := by
  classical
  let φ : HK R K F n → HK R (Sg (K.X s)) F d := fun x =>
    if h : x ∈ S K F n s then CohomologyClass.mk (clsC K F n s d hd (memS K F n h).choose (memS K F n h).choose_spec.2) else 0
  have key : ∀ x ∈ S K F n s, ∀ x' ∈ S K F n s, φ x = φ x' → x - x' ∈ S K F n (s - 1) := by
    intro x hx x' hx' he
    simp only [φ, dif_pos hx, dif_pos hx'] at he
    have hz := (memS K F n hx).choose_spec
    have hz' := (memS K F n hx').choose_spec
    have h0 : CohomologyClass.mk (clsC K F n s d hd (memS K F n hx).choose hz.2 -
        clsC K F n s d hd (memS K F n hx').choose hz'.2) = 0 := by
      rw [CohomologyClass.mk_sub, he, sub_self]
    obtain ⟨β, hβ⟩ := CB F (K.X s) d _ h0 (d - 1) (by omega)
    have hV : V K F n s ((memS K F n hx).choose - (memS K F n hx').choose) := by
      intro p q h hp
      simp [Cochain.sub_v, hz.2 p q h hp, hz'.2 p q h hp]
    obtain ⟨w, hw, hwV⟩ := KL K F n s d hd _ hV (d - 1) (by omega) β (by
      rw [hβ]
      simp only [coe_sub', Cochain.sub_v, clsC_v, Preadditive.comp_sub])
    exact ⟨w, by rw [hw, CohomologyClass.mk_sub, hz.1, hz'.1], hwV⟩
  let g : HK R (Sg (K.X s)) F d → HK R K F n := fun t =>
    if h : ∃ x ∈ S K F n s, φ x = t then h.choose else 0
  refine ((Set.finite_univ.prod hS).image (fun p => g p.1 + p.2)).subset ?_
  intro x hx
  have h : ∃ y ∈ S K F n s, φ y = φ x := ⟨x, hx, rfl⟩
  refine ⟨(φ x, x - g (φ x)), ⟨trivial, ?_⟩, ?_⟩
  · have hg : g (φ x) = h.choose := by simp only [g, dif_pos h]
    rw [hg]
    exact key x hx _ h.choose_spec.1 h.choose_spec.2.symm
  · simp

theorem base (s : ℤ) (hs : s + n < 0) : S K F n s ⊆ {0} := by
  rintro x ⟨z, rfl, hz⟩
  have : z = 0 := by
    refine Cocycle.ext (Cochain.ext _ _ (fun p q hpq => ?_))
    rw [coe_zero', Cochain.zero_v]
    rcases lt_or_ge s p with h | h
    · exact hz p q hpq h
    · exact (res_zero F q (by omega)).eq_of_tgt (z.1.v p q hpq) 0
  simp [this]

theorem LeafFilt_of : LateralTheory.E.LeafSSCut.LeafFilt := by
  intro _ R _ K _ F n hfin
  have ind : ∀ k : ℕ, ∀ r : ℕ, 1 ≤ r → n < r + k → (S K F n (-(r : ℤ))).Finite := by
    intro k
    induction k with
    | zero => intro r _ hr; exact (Set.finite_singleton 0).subset (base K F n _ (by push_cast at hr; omega))
    | succ k ih =>
      intro r hr1 hr
      by_cases hk : n < r + k
      · exact ih r hr1 hk
      · have : Finite (HK R (Sg (K.X (-(r : ℤ)))) F (n - r)) := hfin r (by omega) (by push_cast at hr; omega)
        have h2 := ih (r + 1) (by omega) (by push_cast at hr ⊢; omega)
        have e : (-((r + 1 : ℕ) : ℤ)) = -(r : ℤ) - 1 := by push_cast; ring
        rw [e] at h2
        exact step K F n (-(r : ℤ)) (n - r) (by omega) h2
  have hS := ind n.toNat 1 le_rfl (by omega)
  have e : (-((1 : ℕ) : ℤ)) = (0 : ℤ) - 1 := by norm_num
  rw [e] at hS
  have hsub : ((HK.pull R (LateralTheory.E.LeafSSCut.incl0 K) F n).ker : Set (HK R K F n)) ⊆ S K F n (0 - 1) := by
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    have hz : V K F n 0 z := fun p q hpq hp =>
      (CochainComplex.isZero_of_isStrictlyLE K 0 p hp).eq_of_src _ _
    have hc : CohomologyClass.mk (zcomp (Cocycle.ofHom (LateralTheory.E.LeafSSCut.incl0 K)) z (zero_add n)) = 0 := hx
    obtain ⟨β, hβ⟩ := CB F (K.X 0) n _ hc (n - 1) (by omega)
    obtain ⟨w, hw, hwV⟩ := KL K F n 0 n (zero_add n) z hz (n - 1) (by omega) β (by
      rw [hβ]
      change ((Cochain.ofHom (LateralTheory.E.LeafSSCut.incl0 K)).comp z.1 (zero_add n)).v 0 n (zero_add n) = _
      rw [Cochain.comp_v _ _ (zero_add n) 0 0 n (by omega) (by omega), Cochain.ofHom_v]
      simp [LateralTheory.E.LeafSSCut.incl0, HomologicalComplex.mkHomFromSingle_f])
    exact ⟨w, hw, hwV⟩
  exact (hS.subset hsub).to_subtype

end LateralTheory.E.LeafFiltPf
