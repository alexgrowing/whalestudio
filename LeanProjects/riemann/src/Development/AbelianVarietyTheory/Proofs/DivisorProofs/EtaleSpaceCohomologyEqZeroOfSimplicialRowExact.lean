import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyComplexOfSheafCocycleClassProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicProperti
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.RowVanish

open GlobalTheory.EtC.ClsBasic GlobalTheory.EtC.HCElements

variable {R : Type} [CommRing R] {F : Shv R}

theorem const_d (P : PSh) : ((chains R).obj (disc.obj P)).d (-(((0 : ℕ) + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) = 0 := by
  rw [chains_d (R := R) (disc.obj P) 0, Fin.sum_univ_two]
  have h0 : (disc.obj P).δ (0 : Fin 2) = 𝟙 _ := rfl
  have h1 : (disc.obj P).δ (1 : Fin 2) = 𝟙 _ := rfl
  simp [h0, h1]

def dcoc (P : PSh) (m : ℤ) (t : (free R).obj P ⟶ (res R F).X m) (ht : t ≫ (res R F).d m (m + 1) = 0) :
    Cocycle ((chains R).obj (disc.obj P)) (res R F) m :=
  Cocycle.mk (Cochain.single (p := -((0 : ℕ) : ℤ)) (q := m) ((chainsXIso R (disc.obj P) 0).hom ≫ t) m) (m + 1) rfl (by
    rw [Cochain.δ_single _ m (m + 1) rfl (-(((0 : ℕ) + 1 : ℕ) : ℤ)) (m + 1) (by simp) rfl, const_d]
    simp [ht])

def dcl (P : PSh) (m : ℤ) (t : (free R).obj P ⟶ (res R F).X m) (ht : t ≫ (res R F).d m (m + 1) = 0) :
    H R (disc.obj P) F m :=
  CohomologyClass.mk (dcoc P m t ht)

theorem dcl_add (P : PSh) (m : ℤ) (t t' : (free R).obj P ⟶ (res R F).X m) (ht ht') (h) :
    dcl P m t ht + dcl P m t' ht' = dcl P m (t + t') h := by
  rw [dcl, dcl, dcl, ← CohomologyClass.mk_add]
  congr 1
  refine Cocycle.ext ?_
  change Cochain.single _ m + Cochain.single _ m = Cochain.single _ m
  rw [← single_add', Preadditive.comp_add]

def closedSub (P : PSh) (m : ℤ) : AddSubgroup ((free R).obj P ⟶ (res R F).X m) :=
  (Preadditive.rightComp ((free R).obj P) ((res R F).d m (m + 1))).ker

def dclHom (P : PSh) (m : ℤ) : closedSub (F := F) P m →+ H R (disc.obj P) F m :=
  AddMonoidHom.mk' (fun t => dcl P m t.1 t.2) (fun t t' => (dcl_add P m t.1 t'.1 t.2 t'.2 (t + t').2).symm)

theorem dcl_sum_zsmul (P : PSh) (m : ℤ) {ι : Type} (S : Finset ι) (c : ι → ℤ) (t : ι → ((free R).obj P ⟶ (res R F).X m))
    (ht : ∀ i, t i ≫ (res R F).d m (m + 1) = 0) (h) :
    ∑ i ∈ S, c i • dcl P m (t i) (ht i) = dcl P m (∑ i ∈ S, c i • t i) h := by
  have hs : (∑ i ∈ S, c i • (⟨t i, ht i⟩ : closedSub (F := F) P m)) = ⟨∑ i ∈ S, c i • t i, h⟩ := by
    apply Subtype.ext
    rw [AddSubgroup.val_finset_sum]
    rfl
  have e : dclHom (F := F) P m (∑ i ∈ S, c i • (⟨t i, ht i⟩ : closedSub (F := F) P m)) =
      ∑ i ∈ S, c i • dcl P m (t i) (ht i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rfl
  rw [← e, hs]
  rfl

end GlobalTheory.EtC.RowVanish

namespace GlobalTheory.EtC.RowVanish

open GlobalTheory.EtC.ClsBasic GlobalTheory.EtC.HCElements

variable {R : Type} [CommRing R] {F : Shv R}

theorem pull_dcl {P P' : PSh} (f : P ⟶ P') (m : ℤ) (t : (free R).obj P' ⟶ (res R F).X m) (ht) (h) :
    pull R (disc.map f) F m (dcl P' m t ht) = dcl P m ((free R).map f ≫ t) h := by
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (disc.map f))) (dcoc P' m t ht) (zero_add m)) = _
  congr 1
  refine Cocycle.ext ?_
  change (Cochain.ofHom ((chains R).map (disc.map f))).comp (Cochain.single _ m) (zero_add m) = Cochain.single _ m
  rw [ofHom_comp_single, ← Category.assoc, chainsXIso_nat (disc.map f) 0, Category.assoc]
  rfl

theorem dcl_bd (P : PSh) (m : ℤ) (y : (free R).obj P ⟶ (res R F).X (m - 1)) (h) :
    dcl P m (y ≫ (res R F).d (m - 1) m) h = 0 := by
  rw [dcl, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)]
  refine ⟨Cochain.single (p := -((0 : ℕ) : ℤ)) (q := m - 1) ((chainsXIso R (disc.obj P) 0).hom ≫ y) (m - 1), ?_⟩
  change _ = Cochain.single _ m
  rw [Cochain.δ_single _ (m - 1) m (by omega) (-(((0 : ℕ) + 1 : ℕ) : ℤ)) m (by simp) (by omega), const_d]
  simp

theorem dcl_eq_zero (P : PSh) (m : ℤ) (t : (free R).obj P ⟶ (res R F).X m) (ht) (h0 : dcl P m t ht = 0) :
    ∃ u : (free R).obj P ⟶ (res R F).X (m - 1), t = u ≫ (res R F).d (m - 1) m := by
  rw [dcl, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)] at h0
  obtain ⟨β, hβ⟩ := h0
  have e := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) m (by simp)
  rw [δ_v (m - 1) m (by omega) β _ m _ (m - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl] at e
  have hz : ((chains R).obj (disc.obj P)).d (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) = 0 :=
    (chains_X_isZero R _ _ (by simp)).eq_of_tgt _ _
  rw [hz, zero_comp, smul_zero, add_zero] at e
  change _ = (Cochain.single _ m).v _ _ _ at e
  rw [Cochain.single_v] at e
  refine ⟨(chainsXIso R (disc.obj P) 0).inv ≫ β.v (-((0 : ℕ) : ℤ)) (m - 1) (by omega), ?_⟩
  rw [Category.assoc, e, Iso.inv_hom_id_assoc]

theorem rowD_dcl (E : Spc) (s : ℤ) (p : ℕ) (t : (free R).obj (E.obj (op ⦋p⦌)) ⟶ (res R F).X s) (ht) (h) :
    rowD R E F s p (dcl _ s t ht) =
      dcl _ s ((∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ t) h := by
  have hi : ∀ i : Fin (p + 2), ((free R).map (E.δ i) ≫ t) ≫ (res R F).d s (s + 1) = 0 := fun i => by
    rw [Category.assoc, ht, comp_zero]
  calc rowD R E F s p (dcl _ s t ht)
      = ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • dcl _ s ((free R).map (E.δ i) ≫ t) (hi i) := by
        simp only [rowD, AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pull_dcl]
    _ = dcl _ s (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • ((free R).map (E.δ i) ≫ t))
          (by simp [Preadditive.sum_comp, hi]) := dcl_sum_zsmul _ s _ _ _ hi _
    _ = _ := by
        congr 1
        simp [Preadditive.sum_comp]

theorem dcl_surj (P : PSh) (m : ℤ) (w : H R (disc.obj P) F m) :
    ∃ (s : (free R).obj P ⟶ (res R F).X m) (hs : s ≫ (res R F).d m (m + 1) = 0), w = dcl P m s hs := by
  obtain ⟨α, rfl, hα⟩ := GlobalTheory.EtC.discRep R P (res R F) m w
  have e := Cochain.congr_v (Cocycle.δ_eq_zero α (m + 1)) (-((0 : ℕ) : ℤ)) (m + 1) (by simp)
  rw [δ_v m (m + 1) rfl _ _ _ _ m (-((0 : ℕ) : ℤ) + 1) (by simp) rfl,
    (chains_X_isZero R _ (-((0 : ℕ) : ℤ) + 1) (by simp)).eq_of_tgt (((chains R).obj (disc.obj P)).d _ _) 0] at e
  simp only [zero_comp, smul_zero, add_zero, Cochain.zero_v] at e
  refine ⟨(chainsXIso R (disc.obj P) 0).inv ≫ α.1.v (-((0 : ℕ) : ℤ)) m (by simp), by rw [Category.assoc, e, comp_zero], ?_⟩
  congr 1
  refine Cocycle.ext (Cochain.ext _ _ fun p' q' hpq => ?_)
  change α.1.v p' q' hpq = (Cochain.single _ m).v p' q' hpq
  rcases lt_trichotomy p' (-((0 : ℕ) : ℤ)) with hp | hp | hp
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, p' = -(j : ℤ) := ⟨(-p').toNat, by omega⟩
    rw [hα j (by omega) q' hpq, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
  · subst hp
    obtain rfl : q' = m := by omega
    rw [Cochain.single_v, Iso.hom_inv_id_assoc]
  · exact (chains_X_isZero R _ p' (by omega)).eq_of_src _ _

end GlobalTheory.EtC.RowVanish

namespace GlobalTheory.EtC.RowVanish

open GlobalTheory.EtC.ClsBasic GlobalTheory.EtC.HCElements

variable {R : Type} [CommRing R] {F : Shv R}

theorem dcl_congr (P : PSh) (m : ℤ) {t t' : (free R).obj P ⟶ (res R F).X m} (e : t = t') (ht) (ht') :
    dcl P m t ht = dcl P m t' ht' := by
  subst e; rfl

theorem dcl_sub (P : PSh) (m : ℤ) (t t' : (free R).obj P ⟶ (res R F).X m) (ht ht') (h) :
    dcl P m (t - t') h = dcl P m t ht - dcl P m t' ht' := by
  refine eq_sub_of_add_eq ?_
  rw [dcl_add P m _ _ h ht' (by rw [sub_add_cancel]; exact ht)]
  exact dcl_congr P m (sub_add_cancel t t') _ _

theorem clear_step {K L : Cx R} {n : ℤ} (z : Cocycle K L n) (k : ℕ)
    (hv : ∀ p q (hpq : p + n = q), -(k : ℤ) < p → z.1.v p q hpq = 0) (γ : Cochain K L (n - 1))
    (h1 : ∀ p q (hpq : p + n = q), -(k : ℤ) < p → (δ (n - 1) n γ).v p q hpq = 0)
    (h2 : ∀ q (hpq : -(k : ℤ) + n = q), (δ (n - 1) n γ).v (-(k : ℤ)) q hpq = z.1.v (-(k : ℤ)) q hpq) :
    ∃ z' : Cocycle K L n, CohomologyClass.mk z' = CohomologyClass.mk z ∧
      ∀ p q (hpq : p + n = q), -((k + 1 : ℕ) : ℤ) < p → z'.1.v p q hpq = 0 := by
  let c : Cocycle K L n := Cocycle.mk (δ (n - 1) n γ) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨γ, rfl⟩
  · intro p q hpq hp
    rw [Cocycle.coe_sub, Cochain.sub_v]
    change z.1.v p q hpq - (δ (n - 1) n γ).v p q hpq = 0
    rcases lt_or_eq_of_le (show -(k : ℤ) ≤ p by omega) with h | h
    · rw [hv p q hpq h, h1 p q hpq h, sub_zero]
    · subst h
      rw [h2, sub_self]

end GlobalTheory.EtC.RowVanish

open GlobalTheory.EtC.RowVanish GlobalTheory.EtC.ClsBasic GlobalTheory.EtC.HCElements in

theorem GlobalTheory.EtC.vanish_of_rowExact : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (P : PSh) (g : disc.obj P ⟶ E),
    IsIso (g.app (op ⦋0⦌)) →
    ∀ (n : ℕ) (x : H R E F n), pull R g F n x = 0 →
    (∀ p : ℕ, p + 1 ≤ n → RowExact R E F ((n : ℤ) - ((p + 1 : ℕ) : ℤ)) p) → x = 0 := by
  intro R _ F E P g hg n x hx hrow
  obtain ⟨-, hneg, -, -, -, hpos⟩ := GlobalTheory.EtC.res_basic R F
  have key : ∀ k : ℕ, k ≤ n + 1 → ∃ z : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z = x ∧
      ∀ p q (hpq : p + (n : ℤ) = q), -(k : ℤ) < p → z.1.v p q hpq = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨z, rfl⟩ := x.mk_surjective
      exact ⟨z, rfl, fun p q hpq hp => (hpos E p (by omega)).eq_of_src _ _⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, hz, hv⟩ := ih (by omega)
      rcases k with _ | p
      · subst hz
        have hx' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map g)) z (zero_add _)) = 0 := hx
        rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ ((n : ℤ) - 1) (by omega)] at hx'
        obtain ⟨β, hβ⟩ := hx'
        have e := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) n (by simp)
        rw [δ_v ((n : ℤ) - 1) n (by omega) β _ n _ ((n : ℤ) - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl,
          (chains_X_isZero R _ (-((0 : ℕ) : ℤ) + 1) (by simp)).eq_of_tgt (((chains R).obj (disc.obj P)).d _ _) 0,
          zero_comp, smul_zero, add_zero] at e
        change _ = ((Cochain.ofHom ((chains R).map g)).comp z.1 (zero_add _)).v _ _ _ at e
        rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at e
        haveI : IsIso (((chains R).map g).f (-((0 : ℕ) : ℤ))) := by
          have h := chainsXIso_nat (R := R) g 0
          rw [← Iso.eq_comp_inv] at h
          rw [h]
          infer_instance
        let γ : Cochain ((chains R).obj E) (res R F) ((n : ℤ) - 1) :=
          Cochain.single (p := -((0 : ℕ) : ℤ)) (q := (n : ℤ) - 1)
            (inv (((chains R).map g).f (-((0 : ℕ) : ℤ))) ≫ β.v (-((0 : ℕ) : ℤ)) ((n : ℤ) - 1) (by omega)) ((n : ℤ) - 1)
        refine clear_step z 0 hv γ (fun p q hpq hp => (hpos E p (by omega)).eq_of_src _ _) (fun q hpq => ?_)
        obtain rfl : q = (n : ℤ) := by omega
        rw [δ_v ((n : ℤ) - 1) n (by omega) γ _ n hpq ((n : ℤ) - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl,
          (hpos E (-((0 : ℕ) : ℤ) + 1) (by simp)).eq_of_tgt (((chains R).obj E).d _ _) 0, zero_comp, smul_zero, add_zero,
          Cochain.single_v, Category.assoc, e, IsIso.inv_hom_id_assoc]
      · subst hz
        obtain ⟨S, hS⟩ : ∃ S : ℤ, S = (n : ℤ) - ((p + 1 : ℕ) : ℤ) := ⟨_, rfl⟩
        have hrowp := hrow p (by omega)
        rw [← hS] at hrowp
        let t : (free R).obj (E.obj (op ⦋p + 1⦌)) ⟶ (res R F).X S :=
          (chainsXIso R E (p + 1)).inv ≫ z.1.v (-((p + 1 : ℕ) : ℤ)) S (by omega)
        have ht : t ≫ (res R F).d S (S + 1) = 0 := by
          have e := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((p + 1 : ℕ) : ℤ)) (S + 1) (by omega)
          rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ S (-((p + 1 : ℕ) : ℤ) + 1) (by omega) rfl,
            hv (-((p + 1 : ℕ) : ℤ) + 1) _ _ (by omega), comp_zero, smul_zero, add_zero, Cochain.zero_v] at e
          simp only [t, Category.assoc, e, comp_zero]

        let D1 : (free R).obj (E.obj (op ⦋p + 1 + 1⦌)) ⟶ (free R).obj (E.obj (op ⦋p + 1⦌)) :=
          ∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)
        have hb : D1 ≫ t = ((-(((n : ℤ) + 1).negOnePow : ℤ)) • ((chainsXIso R E (p + 1 + 1)).inv ≫
            z.1.v (-((p + 1 + 1 : ℕ) : ℤ)) (S - 1) (by omega))) ≫ (res R F).d (S - 1) S := by
          have e := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((p + 1 + 1 : ℕ) : ℤ)) S (by omega)
          rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ (S - 1) (-((p + 1 : ℕ) : ℤ)) (by omega) (by omega),
            chains_d E (p + 1), Cochain.zero_v, Units.smul_def] at e
          have e2 := eq_neg_of_add_eq_zero_right e
          apply (cancel_epi (chainsXIso R E (p + 1 + 1)).hom).1
          have e3 := congrArg (fun f => (((n : ℤ) + 1).negOnePow : ℤ) • f) e2
          simp only [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul] at e3
          simp only [D1, t, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc, Iso.hom_inv_id_assoc,
            smul_neg, neg_smul, Preadditive.neg_comp, Preadditive.comp_neg] at e3 ⊢
          rw [← e3]
        have hD1 : (D1 ≫ t) ≫ (res R F).d S (S + 1) = 0 := by rw [Category.assoc, ht, comp_zero]
        have hc0 : rowD R E F S (p + 1) (dcl _ S t ht) = 0 := by
          rw [rowD_dcl E S (p + 1) t ht hD1]
          rw [dcl_congr _ S hb hD1 (by rw [← hb]; exact hD1)]
          exact dcl_bd _ S _ _
        obtain ⟨w, hw⟩ := hrowp _ hc0
        obtain ⟨s, hs, rfl⟩ := dcl_surj _ S w
        let D0 : (free R).obj (E.obj (op ⦋p + 1⦌)) ⟶ (free R).obj (E.obj (op ⦋p⦌)) :=
          ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)
        have hD0 : (D0 ≫ s) ≫ (res R F).d S (S + 1) = 0 := by rw [Category.assoc, hs, comp_zero]
        rw [rowD_dcl E S p s hs hD0] at hw
        have hdiff : dcl _ S (t - D0 ≫ s) (by rw [Preadditive.sub_comp, ht, hD0, sub_zero]) = 0 := by
          rw [dcl_sub _ S t (D0 ≫ s) ht hD0, ← hw, sub_self]
        obtain ⟨u, hu⟩ := dcl_eq_zero _ S _ _ hdiff
        let ε : ℤˣ := (n : ℤ).negOnePow
        let γ : Cochain ((chains R).obj E) (res R F) ((n : ℤ) - 1) :=
          Cochain.single (p := -((p + 1 : ℕ) : ℤ)) (q := S - 1) ((chainsXIso R E (p + 1)).hom ≫ u) ((n : ℤ) - 1) +
            ε • Cochain.single (p := -((p : ℕ) : ℤ)) (q := S) ((chainsXIso R E p).hom ≫ s) ((n : ℤ) - 1)
        have htz : z.1.v (-((p + 1 : ℕ) : ℤ)) S (by omega) =
            (chainsXIso R E (p + 1)).hom ≫ (u ≫ (res R F).d (S - 1) S + D0 ≫ s) := by
          rw [← hu, sub_add_cancel]
          simp only [t, Iso.hom_inv_id_assoc]
        refine clear_step z (p + 1) hv γ (fun p' q hpq hp' => ?_) (fun q hpq => ?_)
        · rcases eq_or_ne p' (-((p : ℕ) : ℤ)) with h | h
          · subst h
            obtain rfl : q = S + 1 := by omega
            rw [δ_v ((n : ℤ) - 1) n (by omega) γ _ _ hpq S (-((p : ℕ) : ℤ) + 1) (by omega) rfl]
            simp (disch := omega) only [γ, Cochain.add_v, Cochain.units_smul_v, Cochain.single_v_eq_zero,
              Cochain.single_v, smul_zero, add_zero, zero_add, comp_zero]
            rw [Units.smul_def, Preadditive.zsmul_comp, Category.assoc, hs, comp_zero, smul_zero]
          · rw [δ_v ((n : ℤ) - 1) n (by omega) γ _ _ hpq (q - 1) (p' + 1) (by omega) rfl]
            simp (disch := omega) only [γ, Cochain.add_v, Cochain.units_smul_v, Cochain.single_v_eq_zero,
              smul_zero, add_zero, zero_add, comp_zero, zero_comp]
        · have hq : S = q := by omega
          subst hq
          rw [δ_v ((n : ℤ) - 1) n (by omega) γ _ _ hpq (S - 1) (-((p : ℕ) : ℤ)) (by omega) (by omega), chains_d E p]
          simp (disch := omega) only [γ, Cochain.add_v, Cochain.units_smul_v, Cochain.single_v_eq_zero,
            Cochain.single_v, smul_zero, add_zero, zero_add]
          rw [htz, Units.smul_def, Units.smul_def, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul,
            Int.units_mul_self, Units.val_one, one_smul]
          simp only [D0, Category.assoc, Iso.inv_hom_id_assoc, Preadditive.comp_add]
  obtain ⟨z, hz, hv⟩ := key (n + 1) le_rfl
  have h0 : z = 0 := Cocycle.ext (Cochain.ext _ _ fun p q hpq => by
    by_cases hp : -((n + 1 : ℕ) : ℤ) < p
    · exact hv p q hpq hp
    · exact (hneg q (by omega)).eq_of_tgt _ _)
  rw [← hz, h0]
  rfl
