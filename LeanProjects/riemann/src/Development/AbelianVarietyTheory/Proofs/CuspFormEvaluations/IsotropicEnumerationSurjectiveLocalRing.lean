import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsIdempotentElemRangeSpMapSubset
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentatives

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace IsotropicEnum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem comp_list_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T' ⟶ T) (L : List (T ⟶ G)) :
    h ≫ L.prod = (L.map fun x => h ≫ x).prod := by
  induction L with
  | nil => simp [MonObj.comp_one]
  | cons x L ih => simp [MonObj.comp_mul, ih]

theorem inZh_comp (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ) {T T' : Over Xo.X} (h : T' ⟶ T)
    {a : Fin n → (T ⟶ Xo.univ.t.G)} (ha : InZh Xo Λ N a) : InZh Xo Λ N (fun b => h ≫ a b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [← MonObj.comp_pow, ha.1 b, MonObj.comp_one]
  · have h1 := ha.2 mu hmu cm hcm i
    have hl : (List.ofFn fun j => (h ≫ a j) ≫ Xo.univ.t.act.act (cm i j)) =
        (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j)).map fun y => h ≫ y := by
      simp [List.map_ofFn, Function.comp_def, Category.assoc]
    rw [hl, ← comp_list_prod, h1, MonObj.comp_one]

theorem ev_sum {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso Dw k Q act e) {m : ℕ} (hm : 0 < m) {n : ℕ} (v : Fin n → Dw.La) :
    I.ev m (∑ j, v j) = (List.ofFn fun j => I.ev m (v j)).prod := by

  have h0 : I.ev m 0 = 1 := by
    have h := I.add m 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Fin.sum_univ_succ, I.add, ih (fun j => v j.succ), List.ofFn_succ, List.prod_cons]

theorem exists_eq_of_isAlgClosed (Xo : Moduli Dw l) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X)
    {n : ℕ} (Λ : GenLat E n) {N : ℕ} (hΛ : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La)
    (w : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hw : ∀ i, InZh Xo Λ N (w i))
    (hinj : Function.Injective w) (a : Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a) : ∃ i, w i = a := by
  classical
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x (Spec.preimage (x ≫ Xo.s)).hom
    (by simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage])
  have hM : 0 < N ^ 2 := pow_pos hN 2

  have evEq : ∀ u u' : Dw.La, Dw.ModN (N ^ 2) (u - u') → I.ev (N ^ 2) u = I.ev (N ^ 2) u' := by
    intro u u' h
    have h1 : I.ev (N ^ 2) (u - u') = 1 := (I.ker _ hM _).2 h
    have h2 := I.add (N ^ 2) (u - u') u'
    rw [sub_add_cancel, h1, _root_.one_mul] at h2
    exact h2

  have key : ∀ c : Fin n → (ptO Xo x ⟶ Xo.univ.t.G), InZh Xo Λ N c →
      ∃ y : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) →
        ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) →
          ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • y j)) ∧ ∀ b, I.ev (N ^ 2) (y b) = c b := by
    intro c hc
    have hy : ∀ b, ∃ y, I.ev (N ^ 2) y = c b := fun b => (I.onto _ hM (c b)).1 (hc.1 b)
    choose y hy using hy
    refine ⟨y, fun mu hmu cm hcm i => ?_, hy⟩
    have h1 := hc.2 mu hmu cm hcm i
    refine (I.ker _ hM _).1 ?_
    have hfun : (fun j => I.ev (N ^ 2) (cm i j • y j)) = fun j => c j ≫ Xo.univ.t.act.act (cm i j) := by
      funext j
      simp only [I.lin, hy]
    rw [ev_sum I hM, hfun]
    exact h1
  obtain ⟨zz, -, -, hcover⟩ := ZCount.exists_class_representatives E H Dw n Λ N hΛ hN hle
  have hf : ∀ i, ∃ j, w i = fun b => I.ev (N ^ 2) (zz j b) := by
    intro i
    obtain ⟨y, hy, hyw⟩ := key (w i) (hw i)
    obtain ⟨j, hj⟩ := hcover y hy
    refine ⟨j, funext fun b => ?_⟩
    rw [← hyw b]
    exact evEq _ _ (hj b)
  choose f hf using hf

  have finj : Function.Injective f := by
    intro i i' h
    apply hinj
    rw [hf i, hf i', h]
  have fsurj : Function.Surjective f := Finite.surjective_of_injective finj
  obtain ⟨y, hy, hya⟩ := key a ha
  obtain ⟨j, hj⟩ := hcover y hy
  obtain ⟨i, rfl⟩ := fsurj j
  refine ⟨i, ?_⟩
  rw [hf i]
  funext b
  rw [← hya b]
  exact (evEq _ _ (hj b)).symm

end IsotropicEnum

open IsotropicEnum in

theorem isotropic_enumeration_onto_of_isLocalRing :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x0 z → (∀ a, InZh Xo Λ N a → ∃ i, z i = a) ∧ ∀ z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z' i)) → GeoInj Xo x0 z' → ∃ σ : Equiv.Perm (Fin (Λ.zCard N (Dw.p + Dw.q))), ∀ i, z' i = z (σ i) := by
  intro hL E _ _ _ H Dw l Xo T _ _ x0 n Λ N hΛ hN hle z hz hzi
  classical

  let ψ : T →+* AlgebraicClosure (IsLocalRing.ResidueField T) :=
    (algebraMap (IsLocalRing.ResidueField T) (AlgebraicClosure (IsLocalRing.ResidueField T))).comp
      (IsLocalRing.residue T)
  let g : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl
  have hA : ∀ (zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)),
      (∀ i, InZh Xo Λ N (zz i)) → GeoInj Xo x0 zz → ∀ a, InZh Xo Λ N a → ∃ i, zz i = a := by
    intro zz hzz hgi a ha
    obtain ⟨i, hi⟩ := exists_eq_of_isAlgClosed Xo (spMap ψ ≫ x0) Λ hΛ hN hle
      (fun i b => g ≫ zz i b) (fun i => inZh_comp Xo Λ N g (hzz i)) (hgi _ ψ g rfl)
      (fun b => g ≫ a b) (inZh_comp Xo Λ N g ha)
    refine ⟨i, funext fun b => ?_⟩
    have hib : g ≫ zz i b = g ≫ a b := congrFun hi b

    obtain ⟨e, he, hiff⟩ := exists_isIdempotentElem_torsion_eq hL E H Dw l Xo T x0 (N ^ 2) (pow_pos hN 2)
      (zz i b) (a b) ((hzz i).1 b) (ha.1 b)
    have hψ : ψ e = 1 := (hiff _ ψ).2 (congrArg (fun f => f.left) hib)
    have hmul : e * (1 - e) = 0 := by rw [mul_sub, _root_.mul_one, he.eq, sub_self]
    have he1 : e = 1 := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
      · exact (sub_eq_zero.1 ((hu.mul_right_eq_zero).1 hmul)).symm
      · rw [(hu.mul_left_eq_zero).1 hmul, map_zero] at hψ
        exact absurd hψ zero_ne_one
    have hid := (hiff T (RingHom.id T)).1 (by rw [he1, map_one])
    have hsp : spMap (RingHom.id T) = 𝟙 _ := by simp [spMap]
    rw [hsp, Category.id_comp, Category.id_comp] at hid
    exact Over.OverMorphism.ext hid
  refine ⟨hA z hz hzi, fun z' hz' hzi' => ?_⟩
  have hsel : ∀ i, ∃ j, z j = z' i := fun i => hA z hz hzi (z' i) (hz' i)
  choose σ' hσ' using hsel
  have hinj' : Function.Injective z' := by
    intro i i' h
    apply hzi' _ ψ g rfl
    show (fun b => g ≫ z' i b) = fun b => g ≫ z' i' b
    rw [h]
  have σinj : Function.Injective σ' := by
    intro i i' h
    apply hinj'
    rw [← hσ' i, ← hσ' i', h]
  exact ⟨Equiv.ofBijective σ' ⟨σinj, Finite.surjective_of_injective σinj⟩, fun i => (hσ' i).symm⟩

end GlobalTheory
