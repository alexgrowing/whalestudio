import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology

noncomputable section

namespace GlobalTheory.PlaceProducts

section Loc
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def locM (e : R) (M : Matrix n n R) : Matrix n n R := e • M + (1 - e) • (1 : Matrix n n R)

theorem locM_apply (e : R) (M : Matrix n n R) (i j : n) :
    locM e M i j = e * M i j + (1 - e) * (1 : Matrix n n R) i j := by
  simp [locM, Matrix.add_apply, Matrix.smul_apply]

theorem locM_one (e : R) : locM e (1 : Matrix n n R) = 1 := by
  rw [locM, ← add_smul, add_sub_cancel, one_smul]

theorem locM_zero (M : Matrix n n R) : locM 0 M = 1 := by simp [locM]

theorem locM_mul_orth {e f : R} (hef : e * f = 0) (M : Matrix n n R) :
    locM e M * locM f M = locM (e + f) M := by
  have h1 : e * (1 - f) = e := by rw [mul_sub, mul_one, hef, sub_zero]
  have h2 : (1 - e) * f = f := by linear_combination -hef
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination hef
  simp only [locM, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, hef, h1, h2, h3, zero_smul, zero_add]
  rw [add_smul]; abel

theorem locM_mul {e : R} (he : e * e = e) (M N : Matrix n n R) :
    locM e M * locM e N = locM e (M * N) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  simp only [locM, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem locM_sandwich {e : R} (he : e * e = e) (A B J : Matrix n n R) :
    locM e A * J * locM e B = e • (A * J * B) + (1 - e) • J := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  simp only [locM, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, mul_one, one_mul, he, h1, h2, h3,
    zero_smul, add_zero, zero_add]

theorem cT_locM (σ : R →+* R) {e : R} (hσ : σ e = e) (M : Matrix n n R) :
    Formalism.UG.cT σ (locM e M) = locM e (Formalism.UG.cT σ M) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, locM_apply, map_add, map_mul, map_sub, map_one, hσ]
  congr 2
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

end Loc

end GlobalTheory.PlaceProducts

namespace GlobalTheory.PlaceProducts

open Classical

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

theorem mt_mul (S : HSp D) (a b : GA D S) : mt S (a * b) = mt S a * mt S b := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]

def locG (S : HSp D) {e : AE D} (he : e * e = e) (hc : cA D e = e) (κ : GA D S) : GA D S :=
  ⟨⟨locM e (mt S κ), locM e (mt S κ⁻¹), by rw [locM_mul he, ← mt_mul, mul_inv_cancel, mt_one, locM_one],
      by rw [locM_mul he, ← mt_mul, inv_mul_cancel, mt_one, locM_one]⟩, by
    show Formalism.UG.cT (cA D) (locM e (mt S κ)) * JR (AF D.host.F) (HSpace.gram S) * locM e (mt S κ) =
      JR (AF D.host.F) (HSpace.gram S)
    have hκ : Formalism.UG.cT (cA D) (mt S κ) * JR (AF D.host.F) (HSpace.gram S) * mt S κ =
      JR (AF D.host.F) (HSpace.gram S) := κ.2
    rw [cT_locM _ hc, locM_sandwich he, hκ, ← add_smul, add_sub_cancel, one_smul]⟩

theorem mt_locG (S : HSp D) {e : AE D} (he : e * e = e) (hc : cA D e = e) (κ : GA D S) :
    mt S (locG S he hc κ) = locM e (mt S κ) := rfl

def pe (D : D7) (v : Pl D) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))

theorem pe_place (v : Pl D) : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
  ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩

theorem inf_pe (v : Pl D) : infPart D (pe D v) = 0 := (GlobalTheory.VacStabFixed.place_comp (pe_place v)).1

theorem comp_pe (v w : Pl D) : compAt D w (pe D v) = if w = v then 1 else 0 := by
  obtain ⟨-, h1, h0⟩ := GlobalTheory.VacStabFixed.place_comp (pe_place v)
  split_ifs with h
  · subst h; exact h1
  · exact h0 w h

theorem cA_pe (v : Pl D) : cA D (pe D v) = pe D v := by
  simp [pe, cA, sigR, Algebra.TensorProduct.algebraMap_apply]

theorem ext_AE {x y : AE D} (h1 : infPart D x = infPart D y) (h2 : ∀ w, compAt D w x = compAt D w y) : x = y :=
  GlobalTheory.VacStabFixed.parts_ext h1 (GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => h2 w)

theorem pe_idem (v : Pl D) : pe D v * pe D v = pe D v :=
  ext_AE (by simp [inf_pe]) fun w => by rw [map_mul, comp_pe]; split_ifs <;> simp

def peT (D : D7) (T : Finset (Pl D)) : AE D := ∑ v ∈ T, pe D v

theorem inf_peT (T : Finset (Pl D)) : infPart D (peT D T) = 0 := by
  rw [peT, map_sum]; exact Finset.sum_eq_zero fun v _ => inf_pe v

theorem comp_peT (T : Finset (Pl D)) (w : Pl D) : compAt D w (peT D T) = if w ∈ T then 1 else 0 := by
  simp [peT, map_sum, comp_pe]

theorem pe_mul_peT {v : Pl D} {T : Finset (Pl D)} (hv : v ∉ T) : pe D v * peT D T = 0 :=
  ext_AE (by simp [inf_pe]) fun w => by
    rw [map_mul, comp_pe, comp_peT, map_zero]
    split_ifs with h1 h2 <;> simp_all

theorem mem_idAt {P : Pl D → Prop} {x : AE D} :
    x ∈ idAt D P ↔ infPart D x = 0 ∧ ∀ w, ¬ P w → compAt D w x = 0 := by
  rw [idAt, Ideal.mem_inf, RingHom.mem_ker, Submodule.mem_iInf]
  simp only [RingHom.mem_ker, Subtype.forall]

theorem mem_grpAt {S : HSp D} {P : Pl D → Prop} {g : GA D S} :
    g ∈ grpAt S P ↔ ∀ i j, mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idAt D P := by
  rw [grpAt, congGrp, MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun g : GL (Fin S.rank) (AE D ⧸ idAt D P) => g.1 i j) h
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Units.val_one] at this
    have h2 : Ideal.Quotient.mk (idAt D P) (mt S g i j) =
        Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
      refine this.trans ?_
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    exact Ideal.Quotient.eq.1 h2
  · intro h
    apply Units.ext
    ext i j
    have h2 := Ideal.Quotient.eq.2 (h i j)
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Units.val_one]
    refine h2.trans ?_
    rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.PlaceProducts

namespace GlobalTheory.PlaceProducts

open Classical Matrix

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

theorem pe_mul_of_mem {v : Pl D} {x : AE D} (hx : x ∈ idAt D (· = v)) : pe D v * x = x := by
  obtain ⟨h1, h2⟩ := mem_idAt.1 hx
  refine ext_AE (by rw [map_mul, inf_pe, zero_mul, h1]) fun w => ?_
  rw [map_mul, comp_pe]
  split_ifs with h
  · rw [one_mul]
  · rw [zero_mul, h2 w h]

theorem pe_mul_mem (v : Pl D) (x : AE D) : pe D v * x ∈ idAt D (· = v) :=
  mem_idAt.2 ⟨by rw [map_mul, inf_pe, zero_mul], fun w hw => by rw [map_mul, comp_pe, if_neg hw, zero_mul]⟩

theorem idAt_mono {P : Pl D → Prop} {v : Pl D} (hv : P v) {x : AE D} (hx : x ∈ idAt D (· = v)) : x ∈ idAt D P := by
  obtain ⟨h1, h2⟩ := mem_idAt.1 hx
  exact mem_idAt.2 ⟨h1, fun w hw => h2 w fun h => hw (h ▸ hv)⟩

theorem pairA_mul (a b : Af D.host.F) :
    pairA D.host.F 0 a * pairA D.host.F 0 b = pairA D.host.F 0 (a * b) :=
  Prod.ext (mul_zero _) rfl

theorem latV_le (S : HSp D) (L : Lat S) {P : Pl D → Prop} {v : Pl D} (hv : P v) :
    latV S L (· = v) ≤ latV S L P := by
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun u hu => h0 u fun h => hu (h ▸ hv), a, ha, x, hx, rfl⟩

theorem pe_smul_latV (S : HSp D) (L : Lat S) (P : Pl D → Prop) (v : Pl D) {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : pe D v • y ∈ latV S L (· = v) := by
  let f : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := DistribMulAction.toAddMonoidHom _ (pe D v)
  have hle : latV S L P ≤ (latV S L (· = v)).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v 1 * α, fun u => ?_, fun u hu => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]
      by_cases h : u = v
      · subst h; rw [GlobalTheory.SplitIdem.evalV_singleV_same, one_mul]; exact hα u
      · rw [GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ h, zero_mul]; exact zero_mem _
    · rw [map_mul, GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hu, zero_mul]
    · funext i
      show pe D v * _ = _
      rw [pe, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [pairA_mul]
  exact hle hy

theorem latV_iff (S : HSp D) (L : Lat S) {P : Pl D → Prop} {v : Pl D} (hv : P v) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· = v)) : z ∈ latV S L P ↔ z ∈ latV S L (· = v) := by
  refine ⟨fun h => ?_, fun h => latV_le S L hv h⟩
  have he : pe D v • z = z := funext fun i => pe_mul_of_mem (hz i)
  rw [← he]; exact pe_smul_latV S L P v h

theorem mulVec_loc {S : HSp D} (K : Matrix (Fin S.rank) (Fin S.rank) (AE D)) {v : Pl D} {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· = v)) : locM (pe D v) K *ᵥ z = K *ᵥ z := by
  have he : pe D v • z = z := funext fun i => pe_mul_of_mem (hz i)
  rw [locM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_smul, he, sub_smul, one_smul, he, sub_self, add_zero]

theorem inK_locG (S : HSp D) (L : Lat S) {P : Pl D → Prop} {κ : GA D S} (hκ : InK S L P κ) {v : Pl D} (hv : P v) :
    InK S L (· = v) (locG S (pe_idem v) (cA_pe v) κ) := by
  refine ⟨mem_grpAt.2 fun i j => ?_, fun z hz => ?_⟩
  · rw [mt_locG, locM_apply]
    have : pe D v * mt S κ i j + (1 - pe D v) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j -
        (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j =
        pe D v * (mt S κ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by ring
    rw [this]; exact pe_mul_mem v _
  · rw [mt_locG, mulVec_loc _ hz]
    have he : pe D v • z = z := funext fun i => pe_mul_of_mem (hz i)
    have hz' : ∀ i, (mt S κ *ᵥ z) i ∈ idAt D (· = v) := fun i => by
      rw [← he, Matrix.mulVec_smul]; exact pe_mul_mem v _
    rw [← latV_iff S L hv hz, ← latV_iff S L hv hz']
    exact hκ.2 z fun i => idAt_mono hv (hz i)

theorem exists_list (S : HSp D) (L : Lat S) (P : Pl D → Prop) {κ : GA D S} (hκ : InK S L P κ)
    (T : Finset (Pl D)) (hT : ∀ v ∈ T, P v) :
    ∃ l : List (GA D S), (∀ y ∈ l, ∃ v, P v ∧ InK S L (· = v) y) ∧ mt S l.prod = locM (peT D T) (mt S κ) := by
  induction T using Finset.induction_on with
  | empty => exact ⟨[], by simp, by simp [peT, locM_zero, mt_one]⟩
  | insert v T hv ih =>
    obtain ⟨l, hl, hp⟩ := ih fun u hu => hT u (Finset.mem_insert_of_mem hu)
    have hPv := hT v (Finset.mem_insert_self v T)
    refine ⟨locG S (pe_idem v) (cA_pe v) κ :: l, fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨v, hPv, inK_locG S L hκ hPv⟩
      · exact hl y hy
    · rw [List.prod_cons, mt_mul, hp, mt_locG, locM_mul_orth (pe_mul_peT hv), peT, peT, Finset.sum_insert hv]

end GlobalTheory.PlaceProducts

namespace GlobalTheory.PlaceProducts

open Classical

set_option synthInstance.maxHeartbeats 400000

theorem hom_loc {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (e a b : A) :
    φ (e * a + (1 - e) * b) = φ e * φ a + (1 - φ e) * φ b := by
  simp only [map_add, map_mul, map_sub, map_one]

theorem hom_loc_one {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {e : A} (he : φ e = 1) (a b : A) :
    φ (e * a + (1 - e) * b) = φ a := by
  rw [hom_loc, he, sub_self, zero_mul, add_zero, one_mul]

theorem hom_loc_zero {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {e : A} (he : φ e = 0) (a b : A) :
    φ (e * a + (1 - e) * b) = φ b := by
  rw [hom_loc, he, zero_mul, zero_add, sub_zero, one_mul]

set_option maxHeartbeats 1000000 in

theorem finite_place_products : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (κ : GA D S), IsSelfDualC S L →
    InK S L P κ → ∀ Fs : Finset (Pl D), ∃ l : List (GA D S), (∀ y ∈ l, ∃ v, P v ∧ InK S L (· = v) y) ∧
      (∀ i j, infPart D (Formalism.L2.Theta.mt S l.prod i j) = infPart D (Formalism.L2.Theta.mt S κ i j)) ∧
      (∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S l.prod i j) =
        GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j)) ∧
      ∀ w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S l.prod i j) =
        GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
  intro D S L P κ _ hκ Fs
  obtain ⟨l, hl, hp⟩ := exists_list S L P hκ (Fs.filter P) fun v hv => (Finset.mem_filter.1 hv).2
  have hK := mem_grpAt.1 hκ.1
  refine ⟨l, hl, fun i j => ?_, fun w hw i j => ?_, fun w hw i j => ?_⟩
  · rw [hp, locM_apply, hom_loc_zero (infPart D) (inf_peT _)]
    have := (mem_idAt.1 (hK i j)).1
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  · rw [hp, locM_apply]
    by_cases hPw : P w
    · have hc : compAt D w (peT D (Fs.filter P)) = 1 := by
        rw [comp_peT, if_pos (Finset.mem_filter.2 ⟨hw, hPw⟩)]
      exact hom_loc_one (compAt D w) hc _ _
    · have hc : compAt D w (peT D (Fs.filter P)) = 0 := by
        rw [comp_peT, if_neg fun h => hPw (Finset.mem_filter.1 h).2]
      have := (mem_idAt.1 (hK i j)).2 w hPw
      rw [map_sub, sub_eq_zero] at this
      rw [hom_loc_zero (compAt D w) hc]
      exact this.symm
  · have e1 : mt S l.prod i j = peT D (Fs.filter P) * mt S κ i j +
        (1 - peT D (Fs.filter P)) * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j := by rw [hp, locM_apply]
    refine (congrArg (compAt D w) e1).trans (hom_loc_zero (compAt D w) ?_ _ _)
    rw [comp_peT, if_neg fun h => hw (Finset.mem_filter.1 h).1]

end GlobalTheory.PlaceProducts

end
