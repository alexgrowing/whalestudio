import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ChernSpec

open GlobalTheory.EtC.ClsSpec

set_option backward.isDefEq.respectTransparency false

theorem sec_neg {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) {U : Scheme.{0}}
    (a b : Sec ((res R F).X s) U) : a = b := by
  have hZ : IsZero ((res R F).X s) :=
    CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 s hs
  have h := hZ.eq_of_src (𝟙 _) 0
  have ha : Sec.map (𝟙 _) a = Sec.map (0 : (res R F).X s ⟶ _) a := by rw [h]
  have hb : Sec.map (𝟙 _) b = Sec.map (0 : (res R F).X s ⟶ _) b := by rw [h]
  simp [Sec.map] at ha hb
  rw [ha, hb]

theorem lineUnit_face_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 2 U) (i : Fin 3) :
    lineUnit L ((x.res g).face i) = umap g (lineUnit L (x.face i)) := by
  rw [← face_res, ClsSpec.lineUnit_res]

theorem rep_unique (q : ℕ) [NeZero q] {E : Spc} (hE : Inv q E) (L : E ⟶ ofCat (glCat 1))
    (γ γ' : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ 0 2 (by simp) U x = 0)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w))
    (h0' : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ' 0 2 (by simp) U x = 0)
    (h1' : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ' 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2' : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ' 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    γ = γ' := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s hs U x => ?_
  match p with
  | 0 =>
    obtain rfl : s = 2 := by omega
    rw [h0, h0']
  | 1 =>
    obtain rfl : s = 1 := by omega
    refine ClsSpec.sep (ClsSpec.loc_mono (root_loc (hE U ⟨x.face 0⟩) (lineUnit L x)) fun V g ⟨v, hv⟩ => ?_)
    have hv' : v ^ q = lineUnit L (x.res g) := by rw [ClsSpec.lineUnit_res]; exact hv
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 1 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 1 1 _ V U g x,
      h1 V _ v hv', h1' V _ v hv']
  | 2 =>
    obtain rfl : s = 0 := by omega
    have hU := hE U ⟨(x.face 0).face 0⟩
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2))) (root_loc hU (lineUnit L (x.face 0))))
      fun V g ⟨⟨v, hv⟩, w, hw⟩ => ?_)
    rw [← lineUnit_face_res] at hv hw
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 2 0 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 2 0 _ V U g x,
      h2 V _ v w hv hw, h2' V _ v w hv hw]
  | p + 3 => exact sec_neg _ _ (by omega) _ _

theorem rep_comp (q : ℕ) {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1))
    (γ : Cochain ((chains (ZMod q)).obj E') (res _ (tw q 1)) 2)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E' 0 U), ev γ 0 2 (by simp) U x = 0)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E' 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E' 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit (f ≫ L) x →
      ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 1 1 (by simp) U x =
        Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit (f ≫ L) (x.face 2) →
      w ^ q = lineUnit (f ≫ L) (x.face 0) →
      ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 2 0 (by simp) U x =
        kumT q U v + kumT q U w - kumT q U (v * w)) := by
  refine ⟨fun U x => ?_, fun U x v hv => ?_, fun U x v w hv hw => ?_⟩
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]; exact h0 U _
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]; exact h1 U _ v hv
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]
    refine h2 U _ v w ?_ ?_
    · rw [← map_face]; exact hv
    · rw [← map_face]; exact hw

theorem face_forms (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2)
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w) :=
  fun U x v w hv hw => h2 U x v w (by rw [sub_zero_one]; exact hv) (by rw [sub_one_one]; exact hw)

theorem firstChernClassTateTwist_pullback (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)) (hE' : Inv q E') :
    pull _ f _ _ (c1 q L) = c1 q (f ≫ L) := by
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨x.map f⟩
  obtain ⟨γ, hγ, h0, h1, h2⟩ := firstChernClassTateTwist_cocycle_representative q hE' L
  obtain ⟨γ', hγ', h0', h1', h2'⟩ := firstChernClassTateTwist_cocycle_representative q hE (f ≫ L)
  obtain ⟨k0, k1, k2⟩ := rep_comp q f L γ.1 h0 h1 (face_forms q L γ.1 h2)
  have key := rep_unique q hE (f ≫ L) _ γ'.1 k0 k1 k2 h0' h1' (face_forms q (f ≫ L) γ'.1 h2')
  rw [← hγ, ← hγ']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map f)) γ (zero_add 2)) = _
  congr 1
  exact Cocycle.ext key

end GlobalTheory.EtC.ChernSpec

namespace GlobalTheory.EtC.ChernSpec
open GlobalTheory.EtC.ClsSpec
set_option backward.isDefEq.respectTransparency false

theorem isOneCochain_add (q : ℕ) [NeZero q] {E : Spc} (L M N : E ⟶ ofCat (glCat 1)) (hE : Inv q E)
    (hN : ∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) :
    c1 q N = c1 q L + c1 q M := by
  obtain ⟨γL, hL, l0, l1, l2⟩ := firstChernClassTateTwist_cocycle_representative q hE L
  obtain ⟨γM, hM, m0, m1, m2⟩ := firstChernClassTateTwist_cocycle_representative q hE M
  obtain ⟨γN, hN', n0, n1, n2⟩ := firstChernClassTateTwist_cocycle_representative q hE N
  have l2' := face_forms q L γL.1 l2
  have m2' := face_forms q M γM.1 m2
  have n2' := face_forms q N γN.1 n2
  have hq₁ : ∀ (U : Scheme.{0}) (_ : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hE U ⟨x.face 0⟩
  obtain ⟨b, hb, hbv⟩ : ∃ b : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 0) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (b U x) = b V (x.res g)) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → w ^ q = lineUnit M x →
        b U x = kumT q U v + kumT q U w - kumT q U (v * w) := by
    rcases kumT_cases q with ht | ht
    · exact exists_two_family ht hq₁ (fun U x => lineUnit L x) (fun U x => lineUnit M x)
        (fun V U g x => ClsSpec.lineUnit_res L g x) (fun V U g x => ClsSpec.lineUnit_res M g x)
    · refine ⟨fun _ _ => 0, fun V U g x => map_zero _, fun U x v w _ _ => ?_⟩
      rw [ht]
      simp
  obtain ⟨β, hβ1, hβ0⟩ := exists_single (R := ZMod q) (E := E) (I := res _ (tw q 1)) (n := 1) 1 0 (by simp) b hb
  rw [← hL, ← hM, ← hN', eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_add, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨β, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, Cocycle.coe_add, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1,
    ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).1]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).1 x, hβ0 _ _ _ _ _ (by decide), smap_zero, l0, m0, n0]
    simp
  | 1 =>
    obtain rfl : t = 1 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).2 0 0 1 (by simp) ht x]
    rw [Finset.sum_eq_zero fun i _ => by rw [hβ0 _ _ _ _ _ (by decide), smul_zero], smul_zero, add_zero, hβ1]
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc (hq₁ U x) (lineUnit L x))
      (root_loc (hq₁ U x) (lineUnit M x))) fun V g ⟨⟨v, hv⟩, w, hw⟩ => ?_)
    rw [← ClsSpec.lineUnit_res] at hv hw
    rw [res_map, hb, hbv V _ v w hv hw, res_sub, res_add,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γL.1 1 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γM.1 1 1 _ V U g x,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γN.1 1 1 _ V U g x, l1 V _ v hv, m1 V _ w hw,
      n1 V _ (v * w) (by rw [mul_pow, hv, hw, hN]), smap_sub, smap_add]
  | 2 =>
    obtain rfl : t = 0 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).2 1 (-1) 0 (by simp) ht x]
    rw [hβ0 _ _ _ _ _ (by decide), smap_zero, zero_add, Fin.sum_univ_three, hβ1, hβ1, hβ1]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, ← sub_eq_add_neg]
    have hU := hE U ⟨(x.face 0).face 0⟩
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and
      (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2))) (root_loc hU (lineUnit L (x.face 0))))
      (ClsSpec.loc_and (root_loc hU (lineUnit M (x.face 2))) (root_loc hU (lineUnit M (x.face 0)))))
      fun V g ⟨⟨⟨a, ha⟩, c, hc⟩, ⟨a', ha'⟩, c', hc'⟩ => ?_)
    rw [← lineUnit_face_res] at ha hc ha' hc'
    have hN2 : ∀ i, lineUnit N ((x.res g).face i) = lineUnit L ((x.res g).face i) * lineUnit M ((x.res g).face i) :=
      fun i => hN V _
    simp only [res_add, res_sub, neg_one_sq, one_smul]
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γL.1 2 0 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γM.1 2 0 _ V U g x,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γN.1 2 0 _ V U g x, l2' V _ a c ha hc, m2' V _ a' c' ha' hc',
      n2' V _ (a * a') (c * c') (by rw [mul_pow, ha, ha', hN2]) (by rw [mul_pow, hc, hc', hN2])]
    rw [hb, hb, hb, face_res, face_res, face_res,
      hbv V _ c c' (by rw [hc]) (by rw [hc']),
      hbv V _ (a * c) (a' * c') (by rw [lineUnit_face, mul_pow, ha, hc]) (by rw [lineUnit_face, mul_pow, ha', hc']),
      hbv V _ a a' ha ha']
    have e : a * c * (a' * c') = a * a' * (c * c') := by rw [mul_mul_mul_comm]
    rw [e]
    abel
  | p + 3 => exact sec_neg _ _ (by omega) _ _

end GlobalTheory.EtC.ChernSpec

theorem _root_.GlobalTheory.EtC.firstChernClassTateTwist_cocycle_naturality_additivity : ∀ (q : ℕ) [NeZero q], (∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk γ = c1 q L ∧ (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧ (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) → w ^ q = lineUnit L (x.sub 1 1 (by omega)) → ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' → pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧ ∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E → (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M := by
  intro q _
  exact ⟨fun L hE => firstChernClassTateTwist_cocycle_representative q hE L, fun f L hE' => GlobalTheory.EtC.ChernSpec.firstChernClassTateTwist_pullback q f L hE',
    fun L M N hE hN => GlobalTheory.EtC.ChernSpec.isOneCochain_add q L M N hE hN⟩

end
