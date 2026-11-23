import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelOfTheta

open GlobalTheory.CechPic

section Algebra

variable {G U : Type} [CommGroup G] [CommGroup U]

theorem rel_prod (R : G → U → Prop) (h₁ : R 1 1) (hm : ∀ x x' c c', R x c → R x' c' → R (x * x') (c * c'))
    {k : ℕ} (hk : 1 ≤ k) {z : U} (hz : z ^ k = 1) {I : Type} [Fintype I] (p : I → G) (hp : ∀ i, p i ^ k = 1)
    (m : I → ℤ) (h : ∀ i, R (p i) (z ^ m i)) (a : I → ℤ) : R (∏ i, p i ^ a i) (z ^ ∑ i, a i * m i) := by
  let M : Submonoid (G × U) :=
    { carrier := {q | R q.1 q.2}, one_mem' := h₁, mul_mem' := fun {q q'} H H' => hm _ _ _ _ H H' }
  have key : ∀ i, ((p i, z ^ m i) : G × U) ^ a i ∈ M := fun i => by
    have f : IsOfFinOrder ((p i, z ^ m i) : G × U) := isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Prod.ext (hp i) (by
      show (z ^ m i) ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow])⟩
    exact (Submonoid.powers_le.2 (show ((p i, z ^ m i) : G × U) ∈ M from h i))
      (f.mem_powers_iff_mem_zpowers.2 (Subgroup.zpow_mem_zpowers _ _))
  have := M.prod_mem (t := Finset.univ) fun i _ => key i
  have e : ∏ i, ((p i, z ^ m i) : G × U) ^ a i = (∏ i, p i ^ a i, z ^ ∑ i, a i * m i) := by
    refine Prod.ext (by simp [Prod.fst_prod]) ?_
    have s := map_prod (zpowersHom U z) (fun i => Multiplicative.ofAdd (a i * m i)) Finset.univ
    rw [← ofAdd_sum] at s
    refine Eq.trans ?_ s.symm
    simp [Prod.snd_prod, ← zpow_mul, mul_comm]
  rw [e] at this
  exact this

theorem rel_bilin (R : G → G → U → Prop) (h₁ : R 1 1 1) (h₀ : ∀ x y c, R x y c → R 1 y 1)
    (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) (hs : ∀ x y c, R x y c → R y x c⁻¹)
    {k : ℕ} (hk : 1 ≤ k) {z : U} (hz : z ^ k = 1) {I : Type} [Fintype I] (p : I → G) (hp : ∀ i, p i ^ k = 1)
    (ω : I → I → ℤ) (h : ∀ i j, R (p i) (p j) (z ^ ω i j)) (a b : I → ℤ) :
    R (∏ i, p i ^ a i) (∏ j, p j ^ b j) (z ^ ∑ i, ∑ j, a i * b j * ω i j) := by
  have e₁ : ∀ j, R (∏ i, p i ^ a i) (p j) (z ^ ∑ i, a i * ω i j) := fun j =>
    rel_prod (fun x c => R x (p j) c) (h₀ _ _ _ (h j j)) (fun _ _ _ _ => hm _ _ _ _ _) hk hz p hp _ (fun i => h i j) a
  have e₀ : R (∏ i, p i ^ a i) 1 (z ^ ∑ i, a i * 0) :=
    rel_prod (fun x c => R x 1 c) h₁ (fun _ _ _ _ => hm _ _ _ _ _) hk hz p hp _
      (fun i => by simpa using hs _ _ _ (h₀ _ _ _ (h i i))) a
  have e₂ := rel_prod (fun y c => R y (∏ i, p i ^ a i) c) (by simpa using hs _ _ _ e₀)
    (fun _ _ _ _ => hm _ _ _ _ _) hk hz p hp (fun j => -∑ i, a i * ω i j)
    (fun j => by simpa using hs _ _ _ (e₁ j)) b
  have e₃ := hs _ _ _ e₂
  rw [← zpow_neg] at e₃
  convert e₃ using 2
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_neg, neg_neg, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_coord {La : Type} [AddCommGroup La] (EF : La → La → ℤ) {n : ℕ} (bas : (Fin n → ℤ) ≃ₗ[ℤ] La)
    (hl : ∀ x x' y, EF (x + x') y = EF x y + EF x' y) (hr : ∀ x y y', EF x (y + y') = EF x y + EF x y')
    (u v : Fin n → ℤ) :
    EF (bas u) (bas v) = ∑ i, ∑ j, u i * v j * EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) := by
  let B : La →+ La →+ ℤ := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (EF x) (hr x))
    (fun x x' => AddMonoidHom.ext fun y => hl x x' y)
  have d : ∀ w : Fin n → ℤ, bas w = ∑ i, w i • bas (Pi.single i 1) := fun w => by
    conv_lhs => rw [pi_eq_sum_univ' w]
    simp only [map_sum, map_smul]
  show B (bas u) (bas v) = ∑ i, ∑ j, u i * v j * B (bas (Pi.single i 1)) (bas (Pi.single j 1))
  rw [d u, d v]
  simp only [map_sum, map_zsmul, AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem prod_val {k : ℕ} [NeZero k] {n : ℕ} (p : Fin n → G) (hp : ∀ i, p i ^ k = 1) (a : Fin n → ℤ) :
    (List.ofFn fun i => p i ^ ((a i : ZMod k)).val).prod = ∏ i, p i ^ a i := by
  rw [List.prod_ofFn]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' _ (hp i)]

end Algebra

section Classes

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}

theorem pull_one (hL : L.IsLB) (hr : Out.Rigidified A L) (T : Over S) :
    pull (1 : T ⟶ A).left (cls L hL) = 0 := by
  have e : pull (eSec A) (cls L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 hr
  have e' : (1 : T ⟶ A).left = (toUnit T).left ≫ eSec A := rfl
  rw [e', pull_comp, e, map_zero]

omit [GrpObj A] in
theorem pull_pull {T T' : Over S} (f : T' ⟶ T) (a : T ⟶ A) (c : Pic A.left) :
    pull f.left (pull a.left c) = pull (f ≫ a).left c := (pull_comp _ _ _).symm

variable [IsCommMonObj A]

theorem isLB_lam (hL : L.IsLB) : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _

theorem cls_lam (hL : L.IsLB) :
    cls _ (isLB_lam hL) = pull (fst A A * snd A A).left (cls L hL) - pull (fst A A).left (cls L hL) -
      pull (snd A A).left (cls L hL) + pull (1 : A ⊗ A ⟶ A).left (cls L hL) := by
  refine (cls_linComb hL _ _ (isLB_lam hL)).trans ?_
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum A (x2 A) I).left (cls L hL)) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have p₀ : psum A (x2 A) ∅ = 1 := rfl
  have p₁ : psum A (x2 A) {0} = fst A A := _root_.mul_one (fst A A)
  have p₂ : psum A (x2 A) {1} = snd A A := _root_.mul_one (snd A A)
  have p₃ : psum A (x2 A) {0, 1} = fst A A * snd A A := congrArg (fst A A * ·) (_root_.mul_one (snd A A))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem pull_lam (hL : L.IsLB) (hr : Out.Rigidified A L) {T : Over S} (a b : T ⟶ A) :
    pull (lift a b).left (cls _ (isLB_lam hL)) =
      pull (a * b).left (cls L hL) - pull a.left (cls L hL) - pull b.left (cls L hL) := by
  rw [cls_lam hL, pull_one hL hr, add_zero, map_sub, map_sub, pull_pull, pull_pull, pull_pull, MonObj.comp_mul,
    lift_fst, lift_snd]

end Classes

section Pairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L M : LB A.left}

theorem exists_theta_iff (hL : L.IsLB) (k : ℤ) {T : Over S} (x : T ⟶ A) :
    (∃ θ : Out.ThetaGrp A L k T, θ.pt = x) ↔
      k • pull (snd T A).left (cls L hL) - k • pull (Out.translPt A x).left (cls L hL) = 0 := by
  have e := cls_linComb hL (K := Fin 2) ![(snd T A).left, (Out.translPt A x).left] ![k, -k] (LB.isLB_linComb hL _ _)
  rw [Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, ← sub_eq_add_neg] at e
  rw [← e, cls_eq_zero_iff]
  exact ⟨fun ⟨θ, h⟩ => h ▸ ⟨θ.φ, θ.isGen⟩, fun ⟨t, ht⟩ => ⟨⟨x, t, ht⟩, rfl⟩⟩

theorem exists_theta_one (hL : L.IsLB) (k : ℤ) (T : Over S) : ∃ θ : Out.ThetaGrp A L k T, θ.pt = 1 := by
  have e : Out.translPt A (1 : T ⟶ A) = snd T A := by
    show (fst T A ≫ 1) * snd T A = _
    rw [MonObj.comp_one, _root_.one_mul]
  rw [exists_theta_iff hL, e, sub_self]

theorem weilIs_of_pow (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) (hM : M.IsLB) (d : ℕ)
    (e : cls M hM = d • cls L hL) {k : ℤ} {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A L k x y c) : Out.WeilIs A M k x y (c ^ d) := by
  have up : ∀ (T' : Over S) (u : T' ⟶ A), (∃ θ : Out.ThetaGrp A L k T', θ.pt = u) →
      ∃ θ : Out.ThetaGrp A M k T', θ.pt = u := fun T' u H => by
    rw [exists_theta_iff hL] at H
    rw [exists_theta_iff hM, e, map_nsmul, map_nsmul, smul_comm k d, smul_comm k d, ← smul_sub, H, smul_zero]
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := k) (x := x) (y := y) hG hA hM
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, H, -⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨-, θ, -, H⟩, -⟩ := h p
      exact ⟨V, hV, up _ _ ⟨θ, H⟩⟩)
  have iso : LBIso (lbPow L d) (M.pull (𝟙 A : A ⟶ A).left) :=
    (cls_eq_iff (isLB_lbPow hL d) (pull_isLB hM _)).1 (by
      rw [cls_lbPow hL, cls_pull hM, Over.id_left, pull_id, e])
  have := (weilIs_along_hom hG S A A (𝟙 A) L M d k T x y c c' hA hA hL hM inferInstance iso
    (by simpa using hc')).2 h
  exact this ▸ hc'

theorem weilIs_one (hG : Out.GlobalFnsSt) (P : Out.PolAV S) (k : ℕ) {T : Over S} {y : T ⟶ P.A}
    (hy : ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp P.A P.L k (Out.overRes V), θ.pt = Out.overResι V ≫ y) :
    Out.WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs (k := k) (x := 1) (y := y) hG P.isAb P.isLB
    (fun p => ⟨⊤, trivial, by rw [MonObj.comp_one]; exact exists_theta_one P.isLB _ _⟩) hy
  have h₂ := weilIs_mul_left hG S P k T 1 1 y c c hc hc
  rw [_root_.mul_one] at h₂
  have := CommutatorPairing.weilIs_unique hG P.isAb P.isLB h₂ hc
  rwa [mul_eq_left.1 this] at hc

theorem weilIs_bilin (hG : Out.GlobalFnsSt) (P : Out.PolAV S) [IsCommMonObj P.A] {k : ℕ} (hk : 1 ≤ k) {T : Over S}
    {z : Γ(T.left, ⊤)ˣ} (hz : z ^ k = 1) {I : Type} [Fintype I] (p : I → (T ⟶ P.A)) (hp : ∀ i, p i ^ k = 1)
    (ω : I → I → ℤ) (h : ∀ i j, Out.WeilIs P.A P.L k (p i) (p j) (z ^ ω i j)) (a b : I → ℤ) :
    Out.WeilIs P.A P.L k (∏ i, p i ^ a i) (∏ j, p j ^ b j) (z ^ ∑ i, ∑ j, a i * b j * ω i j) :=
  rel_bilin (fun (x y : T ⟶ P.A) c => Out.WeilIs P.A P.L k x y c)
    (weilIs_one hG P k fun p => ⟨⊤, trivial, by rw [MonObj.comp_one]; exact exists_theta_one P.isLB _ _⟩)
    (fun x y c H => weilIs_one hG P k fun q => by
      obtain ⟨V, hV, ⟨-, θ, -, H'⟩, -⟩ := H q
      exact ⟨V, hV, θ, H'⟩)
    (fun x x' y c c' => weilIs_mul_left hG S P k T x x' y c c')
    (fun _ _ _ H => CommPairing.weilIs_symm P.isLB H) hk hz p hp ω h a b

end Pairing

section Principal

variable {S : Scheme.{0}}

theorem cls_diag (hG : Out.GlobalFnsSt)
    (hc : ∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen)
    (P : Out.PolAV S) [IsCommMonObj P.A] :
    cls _ (pull_isLB (isLB_lam P.isLB) (lift (𝟙 P.A) (𝟙 P.A)).left) = 2 • cls P.L P.isLB := by
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2
    ((MulPull.mulPull_of_cube_of_symm hc (exists_gen_negLB hG)).1 S P 2)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id] at h
  have e : Out.mulA P.A 2 = 𝟙 P.A * 𝟙 P.A := pow_two _
  rw [e] at h
  rw [cls_pull (isLB_lam P.isLB), pull_lam P.isLB P.rigid, Over.id_left, pull_id]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h]
  push_cast
  module

theorem relAmple_of_pow {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) (h : Out.RelAmple A L) : Out.RelAmple A M := by
  have := hA.proper
  rw [relAmple_iff_isAmpleLB A hL] at h
  refine relAmple_of_isAmpleLB A hM fun U hU => ?_
  refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _) ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).1
    ((isAmpleLB_pow_iff (pull_isLB hL _) hd).2 (h U hU))
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

theorem translDiff_local {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (hr : Out.Rigidified A L) {T : Over S} (x : T ⟶ A)
    (h : pull (lift (fst T A ≫ x) (snd T A)).left (cls _ (isLB_lam hL)) = 0) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen := by
  obtain ⟨i, hi⟩ := exists_chart hL (x.left p)
  refine ⟨x.left ⁻¹ᵁ L.U i, hi, ?_⟩
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  rw [← cls_eq_zero_iff (pull_isLB hD _), cls_pull hD]
  rw [pull_lam hL hr] at h
  have e₂ : cls _ hD = pull (fst T A ≫ x).left (cls L hL) := by
    refine (cls_linComb hL _ _ hD).trans ?_
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul]
    rw [← sub_eq_zero, ← h, ← Hom.mul_def]
    abel
  rw [e₂, ← pull_comp, ← cls_pull hL _ (pull_isLB hL _), cls_eq_zero_iff]
  exact ChartRig.exists_gen_pull _ _ i hL fun q _ => q.2

theorem eq_one_of_lam (P : Out.PolAV S) [IsCommMonObj P.A] (T : Over S) (x : T ⟶ P.A)
    (h : ∃ t : ((abelian₂ P.A P.L).pull (lift (snd P.A T ≫ x) (fst P.A T)).left).Gen, t.IsGen) : x = 1 := by
  have h₀ := (cls_eq_zero_iff (pull_isLB (isLB_lam P.isLB) _)).2 h
  rw [cls_pull (isLB_lam P.isLB)] at h₀
  have loc : ∀ (T' : Over S) (u : T' ⟶ T),
      pull (lift (fst T' P.A ≫ u ≫ x) (snd T' P.A)).left (cls _ (isLB_lam P.isLB)) = 0 := fun T' u => by
    have e₁ := congrArg (pull (lift (snd T' P.A) (fst T' P.A ≫ u)).left) h₀
    rwa [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.assoc] at e₁
  have aff : ∀ (R : CommRingCat.{0}) (f : Spec R ⟶ T.left), f ≫ x.left = f ≫ (1 : T ⟶ P.A).left := fun R f => by
    let u : Over.mk (f ≫ T.hom) ⟶ T := Over.homMk f rfl
    have key := P.ktriv R (f ≫ T.hom) (u ≫ x) (translDiff_local P.isLB P.rigid (u ≫ x) (loc _ u))
    have key' : u ≫ x = u ≫ 1 := key.trans (MonObj.comp_one u).symm
    exact congrArg CommaMorphism.left key'
  exact Over.OverMorphism.ext (T.left.affineOpenCover.openCover.hom_ext _ _ fun i => aff _ _)

end Principal

section Level

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem unitOn_map {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    unitOn (Units.map i.toMonoidHom c) = Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) := by
  apply Units.ext
  exact congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))

theorem map_unitS {K : Type} [CommRing K] (x : Sp K ⟶ S) (β : o →+* K) (h : x ≫ s = spMap β) (u : oˣ) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn (Units.map β.toMonoidHom u) := by
  rw [unitOn_map, ← h]
  rfl

theorem comb_geom (hG : Out.GlobalFnsSt) (t : TObj g k J b s) [IsCommMonObj t.A] (hk : 1 ≤ k) {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ S) (β : o →+* K) (h : x ≫ s = spMap β) (q : Fin (2 * g) → (Over.mk x ⟶ t.A))
    (hq : ∀ i, q i = (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i) :
    (∀ a : Fin (2 * g) → ℤ, ∏ i, q i ^ a i = 1 ↔ ∃ c, a = k • c) ∧
    (∀ y : Over.mk x ⟶ t.A, y ^ k = 1 → ∃ a : Fin (2 * g) → ℤ, ∏ i, q i ^ a i = y) ∧
    ∀ a c : Fin (2 * g) → ℤ, Out.WeilIs t.A t.L k (∏ i, q i ^ a i) (∏ i, q i ^ c i)
      (unitOn (Units.map β.toMonoidHom b.ζ) ^ ∑ i, ∑ j, a i * c j * Out.stdSymp g i j) := by
  have : NeZero k := ⟨by omega⟩
  have tor : ∀ i, q i ^ k = 1 := fun i => by rw [hq, ← MonObj.comp_pow, t.torsion, MonObj.comp_one]
  have bij : ∀ y : Over.mk x ⟶ t.A, y ^ k = 1 → ∃! c : Ix g k, (List.ofFn fun i => q i ^ (c i).val).prod = y := by
    obtain rfl := funext hq
    exact t.bij K x
  refine ⟨fun a => ⟨fun ha => ?_, ?_⟩, fun y hy => ?_, fun a c => ?_⟩
  · have e := (bij 1 (one_pow k)).unique (y₁ := fun i => (a i : ZMod k)) (y₂ := 0)
      ((prod_val q tor a).trans ha) (by simp)
    choose c hc using fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd (a i) k).1 (congrFun e i)
    exact ⟨c, funext fun i => by simpa using hc i⟩
  · rintro ⟨c, rfl⟩
    refine Finset.prod_eq_one fun i _ => ?_
    rw [Pi.smul_apply, nsmul_eq_mul, zpow_mul, zpow_natCast, tor, one_zpow]
  · obtain ⟨c, hc, -⟩ := bij y hy
    refine ⟨fun i => (c i).val, ?_⟩
    rw [← hc, List.prod_ofFn]
    simp only [zpow_natCast]
  · have hz : unitOn (Units.map β.toMonoidHom b.ζ) ^ k = 1 := by
      have : Units.map β.toMonoidHom b.ζ ^ k = 1 := Units.ext (b.prim K β).pow_eq_one
      unfold unitOn
      rw [← map_pow, this, map_one]
    refine @weilIs_bilin _ hG t.pol ‹_› k hk (Over.mk x) _ hz _ _ q tor _ (fun i j => ?_) a c
    have H := CommPairing.weilIs_pull hG t.ab t.isLB (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S)
      (t.pairing i j)
    rw [← hq, ← hq, map_zpow] at H
    rw [← map_unitS x β h]
    exact H

end Level

theorem exists_siegPre : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (EF : La → La → ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La), (∀ x x' y, EF (x + x') y = EF x y + EF x' y) → (∀ x y y', EF x (y + y') = EF x y + EF x y') → (∀ i j, EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j) → (∀ x y, EF (bas' x) (bas' y) = omegaStd x y) → ∀ (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp o) (s' : S ⟶ Sp B) (t : TObj g k J b s), 1 ≤ k → (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (β : o →+* K) (β' : B →+* K), x ≫ s = spMap β → x ≫ s' = spMap β' → β (b.ζ : o) = β' ζ) → ∃ c : SiegPre g k ζ s', c.Principal ∧ TSieg bas bas' t c := by
  intro hL _ hc g k J La _ EF bas bas' hl hr hb hb' o B _ _ b ζ S s s' t hk hζ
  have hG := hL.globalFns
  haveI := t.ab.comm
  have hΛ : (abelian₂ t.A t.L).IsLB := isLB_lam t.isLB
  have diag : cls _ (pull_isLB hΛ (lift (𝟙 t.A) (𝟙 t.A)).left) = 2 • cls t.L t.isLB :=
    @cls_diag _ hG hc t.pol ‹_›
  let e : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fin (2 * g) → ℤ) := bas'.trans bas.symm
  let p : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.A) := t.pt
  have tor : ∀ i, p i ^ k = 1 := t.torsion
  have form : ∀ u v, ∑ i, ∑ j, e u i * e v j * Out.stdSymp g i j = omegaStd u v := fun u v => by
    rw [← hb', ← bas.apply_symm_apply (bas' u), ← bas.apply_symm_apply (bas' v), form_coord EF bas hl hr]
    simp only [hb]
    rfl
  refine ⟨{
    A := t.A
    ab := t.ab
    P := abelian₂ t.A t.L
    isLB := hΛ
    rig₁ := ?_
    rig₂ := ?_
    symm := ?_
    lev := fun a => ∏ i, p i ^ e a i
    lev_add := fun a a' => by simp only [map_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
    lev_tors := fun a => ?_
    geom := fun K _ _ x β' z hx hz => ?_ }, ⟨?_, ?_⟩, Iso.refl _, (inferInstance : IsMonHom (𝟙 t.A)), ?_, fun i => ?_⟩
  · rw [← cls_eq_zero_iff (pull_isLB hΛ _), cls_pull hΛ, pull_lam t.isLB t.rigid, pull_one t.isLB t.rigid,
      _root_.one_mul, sub_zero, sub_self]
  · rw [← cls_eq_zero_iff (pull_isLB hΛ _), cls_pull hΛ, pull_lam t.isLB t.rigid, pull_one t.isLB t.rigid,
      _root_.mul_one, sub_zero, sub_self]
  · rw [← cls_eq_iff hΛ (pull_isLB hΛ _), cls_pull hΛ, pull_lam t.isLB t.rigid, cls_lam t.isLB,
      pull_one t.isLB t.rigid, add_zero, mul_comm (snd t.A t.A), sub_right_comm]
  · rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, tor, one_zpow]
  · obtain ⟨β, hβ⟩ : ∃ β : o →+* K, x ≫ s = spMap β := ⟨(Spec.preimage (x ≫ s)).hom, (Spec.map_preimage _).symm⟩
    have hz' : Units.map β.toMonoidHom b.ζ = z := Units.ext ((hζ K x β β' hβ hx).trans hz.symm)
    have cmp : ∀ a : Fin (2 * g) → ℤ, toUnit (Over.mk x) ≫ ∏ i, p i ^ a i = ∏ i, (toUnit (Over.mk x) ≫ p i) ^ a i :=
      fun a => by
        let F : (𝟙_ (Over S) ⟶ t.A) →* (Over.mk x ⟶ t.A) :=
          MonoidHom.mk' (fun y => toUnit (Over.mk x) ≫ y) (MonObj.comp_mul _)
        exact (map_prod F _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow F _ _)
    obtain ⟨h₁, h₂, h₃⟩ := comb_geom hG t hk x β hβ (fun i => toUnit (Over.mk x) ≫ p i)
      (fun i => congrArg (· ≫ p i) (toUnit_unique _ _))
    simp only [cmp]
    refine ⟨fun a => (h₁ _).trans ⟨fun ⟨c, hc⟩ => ⟨e.symm c, ?_⟩, fun ⟨c, hc⟩ => ⟨e c, ?_⟩⟩, fun y hy => ?_,
      fun a a' => ?_⟩
    · rw [← map_nsmul, ← hc, e.symm_apply_apply]
    · rw [hc, map_nsmul]
    · obtain ⟨a, ha⟩ := h₂ y hy
      exact ⟨e.symm a, by rwa [e.apply_symm_apply]⟩
    · have H := weilIs_of_pow hG t.ab t.isLB (pull_isLB hΛ _) 2 diag (h₃ (e a) (e a'))
      rw [form, hz'] at H
      have e' : unitOn (z ^ (2 * omegaStd a a')) = (unitOn z ^ omegaStd a a') ^ 2 := by
        unfold unitOn
        rw [map_zpow, mul_comm, zpow_mul, zpow_ofNat]
      rw [e']
      exact H
  · exact relAmple_of_pow t.ab t.isLB (pull_isLB hΛ _) one_le_two diag t.ample
  · exact @eq_one_of_lam _ t.pol ‹_›
  · refine (cls_eq_iff hΛ (pull_isLB hΛ _)).1 ?_
    rw [cls_pull hΛ]
    simp [pull_id]
  · have : e (bas'.symm (bas (Pi.single i 1))) = Pi.single i 1 := by simp [e]
    show ((∏ j, p j ^ e (bas'.symm (bas (Pi.single i 1))) j) ≫ 𝟙 t.A).left = (p i).left
    rw [this, Category.comp_id, Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp

end GlobalTheory.SiegelOfTheta
