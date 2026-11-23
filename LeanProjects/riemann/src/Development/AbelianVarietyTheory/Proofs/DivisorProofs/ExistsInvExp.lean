import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfFpqc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EpiPowOfIsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ESDual

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}

def scaleTate {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {w : ℕ → Q → Q → kˣ → Prop}
    (I : TateIsoO D k Q act w) (e : ℕ) : TateIsoO D k Q act w where
  ζ n := I.ζ n ^ ((p ^ e) ^ 2)
  ζ_prim n hn hp := (I.ζ_prim n hn hp).pow_of_coprime _ ((hp.symm.pow_left e).pow_left 2)
  ζ_pow n m hn hm h := by rw [pow_right_comm, I.ζ_pow n m hn hm h]
  ev n x := I.ev n (p ^ e • x)
  add n x y := by rw [smul_add, I.add]
  lin n c x := by rw [smul_comm, I.lin]
  ker n hn hp x := by
    rw [I.ker n hn hp]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hp.symm.pow_left e)
      refine ⟨u • y + v • x, ?_⟩
      rw [smul_add, smul_comm n u, ← hy, smul_comm n v, ← natCast_zsmul x, ← natCast_zsmul x, smul_smul, smul_smul,
        ← add_smul, huv, one_smul]
    · rintro ⟨y, rfl⟩
      exact ⟨p ^ e • y, smul_comm _ _ _⟩
  onto n hn hp q := by
    rw [I.onto n hn hp]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hp.symm.pow_left e)
      refine ⟨u • x, ?_⟩
      have e1 : x = p ^ e • u • x + n • v • x := by
        rw [smul_comm _ u, smul_comm n v, ← natCast_zsmul x, ← natCast_zsmul x, smul_smul, smul_smul,
          ← add_smul, huv, one_smul]
      have e2 := (I.ker n hn hp (n • v • x)).2 ⟨_, rfl⟩
      conv_rhs => rw [e1, I.add, e2, _root_.mul_one]
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  tower n m hn hm h x := I.tower n m hn hm h _
  isom n hn hp x y := by
    have h := I.isom n hn hp (p ^ e • x) (p ^ e • y)
    have e1 : (2 * D.EF (p ^ e • x) (p ^ e • y) : ℤ) = (((p ^ e) ^ 2 : ℕ) : ℤ) * (2 * D.EF x y) := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      push_cast
      ring
    rw [e1, zpow_mul, zpow_natCast] at h
    exact h

def scale {s : S ⟶ Sp R} (o : Obj b N s) (e : ℕ) {s' : S ⟶ Sp R} (h : s = s') : Obj b N s' where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie := h ▸ o.lie
  lieRank := h ▸ o.lieRank
  eta x := o.eta (p ^ e • x)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_comm, o.eta_ker]
  geom k _ _ x β hx := by
    obtain ⟨I, hI⟩ := o.geom k x β (h ▸ hx)
    exact ⟨scaleTate I e, fun y => hI _⟩

theorem eta_nsmul {s : S ⟶ Sp R} (o : Obj b N s) (n : ℕ) (x : D.La) : o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem eta_congr {s : S ⟶ Sp R} (o : Obj b N s) {n : ℕ} (hn : n ≡ 1 [MOD N]) (hn0 : 0 < n) (x : D.La) :
    o.eta (n • x) = o.eta x := by
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hn0).1 hn.symm
  have : n = 1 + N * k := by omega
  rw [this, add_smul, one_smul, mul_smul, o.eta_add, o.eta_ker, _root_.mul_one]

theorem exists_inv_exp (hN : 0 < N) (hp : N.Coprime p) (e : ℕ) : ∃ f : ℕ, p ^ (e + f) ≡ 1 [MOD N] := by
  refine ⟨e * (N.totient - 1), ?_⟩
  have h1 : 1 ≤ N.totient := Nat.totient_pos.2 hN
  have : e + e * (N.totient - 1) = N.totient * e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h1
    rw [hm]; simp; ring
  rw [this, pow_mul]
  simpa using (Nat.ModEq.pow_totient hp.symm).pow e

def idMap {s : S ⟶ Sp R} (o : Obj b N s) : ObjMap o o (𝟙 S) where
  φ := 𝟙 _
  φ₂ := 𝟙 _
  cart := GlobalTheory.SiegLower.isGrpPullback_id o.A
  sq := ⟨by simp, by simp⟩
  act c := by simp
  pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB
  eta y := by simp

def compMap {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ObjMap o₁ o₃ (f ≫ g) where
  φ := h₁.φ ≫ h₂.φ
  φ₂ := h₁.φ₂ ≫ h₂.φ₂
  cart := h₁.cart.comp h₂.cart
  sq := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  act c := by rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  pol := by
    have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
    have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
    exact LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  eta y := by rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]

theorem pow_left_comm {S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (c : ℕ) :
    ((𝟙 A') ^ c).left ≫ φ = φ ≫ ((𝟙 A) ^ c).left := by
  let u : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have key : ∀ n : ℕ, (u ^ n).left = ((𝟙 A') ^ n).left ≫ φ := by
    intro n
    induction n with
    | zero =>
      let v : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk ((1 : A' ⟶ A').left ≫ φ) (by
        rw [Category.assoc, h.1.w, Over.w_assoc]; rfl)
      have h1 := h.2 A' 1 1 v v rfl rfl
      rw [_root_.mul_one] at h1
      have h2 : v = 1 := mul_eq_left.1 (Over.OverMorphism.ext h1 : v * v = v)
      rw [pow_zero, pow_zero, ← h2]; rfl
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact h.2 A' _ _ _ _ ih (Category.id_comp _).symm
  rw [← key]
  have : u ^ c = u ≫ (𝟙 A) ^ c := by rw [MonObj.comp_pow, Category.comp_id]
  rw [this]; rfl

theorem square_dual {S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj A'] [GrpObj B'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (hB : IsAbelianScheme B') (φ' : B'.left ⟶ B.left) {c : ℕ}
    (hc : 0 < c) {ψ : A ⟶ B} {χ : B ⟶ A} {ψ' : A' ⟶ B'} {χ' : B' ⟶ A'} (h₁ : ψ ≫ χ = (𝟙 A) ^ c)
    (h₂ : ψ' ≫ χ' = (𝟙 A') ^ c) (h₃ : χ' ≫ ψ' = (𝟙 B') ^ c) (sq : φ ≫ ψ.left = ψ'.left ≫ φ') :
    φ' ≫ χ.left = χ'.left ≫ φ := by
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S' B' hB c hc
  haveI : Epi ((𝟙 B') ^ c).left := Flat.epi_of_flat_of_surjective _
  haveI : Epi (χ'.left ≫ ψ'.left) := by rw [← Over.comp_left, h₃]; infer_instance
  haveI : Epi ψ'.left := epi_of_epi χ'.left ψ'.left
  rw [← cancel_epi ψ'.left, ← Category.assoc, ← sq, Category.assoc, ← Over.comp_left, h₁, ← pow_left_comm h,
    ← h₂, Over.comp_left, Category.assoc]

open GlobalTheory.BirigidPow GlobalTheory.CechPic in

theorem val_adj {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsPIsog c o o' ψ)
    {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) {T : Over S} (x : T ⟶ o'.A) (y : T ⟶ o.A) :
    BirigidPow.val o'.isLB x (y ≫ ψ) = BirigidPow.val o.isLB (x ≫ ψ') y := by
  have hc := hψ.pos
  obtain ⟨-, hm, -, -, ⟨hP⟩, -⟩ := hψ
  have nat : ∀ {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (G2 A).left} (hP : P.IsLB) {U V : Over S} (r : U ⟶ V)
      (x y : V ⟶ A), pull r.left (BirigidPow.val hP x y) = BirigidPow.val hP (r ≫ x) (r ≫ y) := by
    intro A _ _ P hP U V r x y
    rw [BirigidPow.val, BirigidPow.val, ← pull_comp, ← Over.comp_left, comp_lift]
  have hsq : ∀ {U : Over S} (x y : U ⟶ o.A), BirigidPow.val o'.isLB (x ≫ ψ) (y ≫ ψ) = c • BirigidPow.val o.isLB x y := by
    intro U x y
    have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    have e := (cls_eq_iff hL (pull_isLB o'.isLB _)).2 hP
    rw [BirigidPow.cls_lbPow o.isLB, cls_pull o'.isLB _ (pull_isLB o'.isLB _)] at e
    have e' := congrArg (pull (lift x y).left) e
    rw [map_nsmul] at e'
    refine Eq.trans ?_ e'.symm
    have := nat o'.isLB (lift x y) (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)
    rw [lift_fst_assoc, lift_snd_assoc] at this
    exact this.symm
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S o'.A o'.ab c hc
  have H : BirigidPow.val o'.isLB (snd o.A o'.A) (fst o.A o'.A ≫ ψ) - BirigidPow.val o.isLB (snd o.A o'.A ≫ ψ') (fst o.A o'.A) = 0 := by
    refine GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc o.A o'.A o'.A o.ab ((𝟙 o'.A) ^ c) hfl hsu hqc _ ?_ ?_
    · rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, MonObj.one_comp, val_one_right _ o'.rig₂,
        val_one_right _ o.rig₂, sub_zero]
    · rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, sub_eq_zero]
      conv_lhs => rw [← h₂, ← Category.assoc, hsq]
      rw [← val_pow_left o.isLB o.ab o.ample o.rig₁ o.rig₂, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp]
  have := congrArg (pull (lift y x).left) H
  rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, map_zero, sub_eq_zero] at this
  exact this

open GlobalTheory.BirigidPow GlobalTheory.CechPic in

theorem dual_clauses {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsPIsog c o o' ψ)
    {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₁ : ψ ≫ ψ' = (𝟙 o.A) ^ c) (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) :
    (∀ a : D.O, o'.act.act a ≫ ψ' = ψ' ≫ o.act.act a) ∧ (∀ x, o.eta (c • x) = o'.eta x ≫ ψ') ∧
      Nonempty (LBIso (Hecke.lbPow o'.P c) (o.P.pull (sq2 ψ'))) := by
  have hc := hψ.pos
  refine ⟨fun a => ?_, fun x => ?_, ⟨?_⟩⟩
  · haveI := GlobalTheory.UPel.HT.MulEpi.epi_pow_of_isAbelianScheme S o'.A o'.ab c hc
    haveI : Epi (ψ' ≫ ψ) := by rw [h₂]; infer_instance
    haveI : Epi ψ := epi_of_epi ψ' ψ
    haveI := o.act.hom a
    rw [← cancel_epi ψ, ← Category.assoc, ← hψ.2.2.1, Category.assoc, h₁, ← Category.assoc, h₁, MonObj.comp_pow,
      MonObj.pow_comp, Category.comp_id, Category.id_comp]
  · rw [hψ.2.2.2.1, Category.assoc, h₁, MonObj.comp_pow, Category.comp_id, eta_nsmul]
  · have hL : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb o'.isLB _ _
    refine (cls_eq_iff hL (pull_isLB o.isLB _)).1 ?_
    rw [BirigidPow.cls_lbPow o'.isLB, cls_pull o.isLB _ (pull_isLB o.isLB _)]
    change _ = BirigidPow.val o.isLB (fst o'.A o'.A ≫ ψ') (snd o'.A o'.A ≫ ψ')
    rw [← val_adj hψ h₂, Category.assoc, h₂, MonObj.comp_pow, Category.comp_id,
      val_pow_right o'.isLB o'.ab o'.ample o'.rig₁ o'.rig₂, BirigidPow.val, lift_fst_snd, Over.id_left, pull_id]

end GlobalTheory.UPel.HT.ESDual
