import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZetaStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.TateTransl

section Ev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {κ : Type} [Field κ] {Q : Type} [Group Q] {act : D.O → Q → Q}
  {e : ℕ → Q → Q → κˣ → Prop} (I : TateIsoO D κ Q act e)

theorem ev_zero (n : ℕ) : I.ev n 0 = 1 := by
  have h := I.add n 0 0
  rw [add_zero] at h
  simpa using h

theorem ev_nsmul (n j : ℕ) (w : D.La) : I.ev n (j • w) = I.ev n w ^ j := by
  induction j with
  | zero => rw [zero_smul, ev_zero, pow_zero]
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem ev_neg (n : ℕ) (w : D.La) : I.ev n (-w) = (I.ev n w)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← I.add, neg_add_cancel, ev_zero])

theorem ev_eq_iff (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (w w' : D.La) :
    I.ev n w = I.ev n w' ↔ ∃ y, w - w' = n • y := by
  rw [← I.ker n hn hnp, sub_eq_add_neg, I.add, ev_neg, mul_inv_eq_one]

theorem ev_mul_nsmul (n j : ℕ) (hn : 0 < n) (hj : 0 < j) (hc : (j * n).Coprime p) (w : D.La) :
    I.ev (n * j) (n • w) = I.ev j w := by
  rw [ev_nsmul, mul_comm n j, I.tower j n hj hn hc]

end Ev

theorem one_comp_transl_pt {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (h : 𝟙_ (Over S) ⟶ A) :
    (1 : T ⟶ A) ≫ transl h = toUnit T ≫ h := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique ((1 : T ⟶ A) ≫ toUnit A) (toUnit T),
    _root_.one_mul]

theorem exists_tateIsoO_transl : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta (g y) ≫ ψ) = I.ev N y := by
  intro p _ D R _ b g c k N hcp hkp hN hNp hEF hg hck S s o A' _ _ act' ψ hA' hψ hGal hact P' hP' r₁ r₂ hiso κ _ _ x β hx
  obtain ⟨I, hI⟩ := o.geom κ x β hx
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have kpos : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hkp; omega
  have cpos : 0 < c := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hcp; omega
  have Npos : 0 < N := by omega
  haveI := D.freeLa
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have ginj : Function.Injective g := by
    intro u v huv
    have h0 : D.EF (u - v) = 0 := by
      ext w
      have e := hEF (u - v) w
      rw [map_sub, huv, sub_self, map_zero, LinearMap.zero_apply] at e
      rw [LinearMap.zero_apply]
      exact (mul_eq_zero.1 e.symm).resolve_left (by exact_mod_cast cpos.ne')
    have := D.nondeg (h0.trans (map_zero D.EF).symm)
    exact sub_eq_zero.1 this
  have hlev : ∀ n, 0 < n → n.Coprime p → ∀ w, I.ev (n * k) (n • w) = I.ev k w := fun n hn hnp w =>
    ev_mul_nsmul I n k hn kpos (Nat.Coprime.mul hkp hnp) w
  have hker : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 ↔ ∃ z, t = I.ev (N * k) (N • g z) := by
    intro t
    constructor
    · intro ht
      have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
        rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
      obtain ⟨h, hh, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
      obtain ⟨z, hz⟩ := h.2
      refine ⟨z, ?_⟩
      have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 := Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
      rw [e2, one_comp_transl_pt, hz, hI]
    · rintro ⟨z, rfl⟩
      rw [← hI, Category.assoc, comp_eq_one_of_transl ψ (o.eta (N • g z)) (hGal.inv ⟨_, mem_heckeSub o g N z⟩),
        MonObj.comp_one]
  have ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev (n * k) (g y) ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn hnp y
    rw [hker]
    constructor
    · rintro ⟨z, hz⟩
      rw [hlev N Npos hNp, ← hlev n hn hnp] at hz
      obtain ⟨w, hw⟩ := (ev_eq_iff I (n * k) (Nat.mul_pos hn kpos) (Nat.Coprime.mul hnp hkp) _ _).1 hz
      obtain ⟨w', hw'⟩ := hg w
      refine ⟨z + w', ginj ?_⟩
      rw [map_nsmul, map_add, hw', smul_add, smul_smul, ← sub_eq_iff_eq_add', hw]
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [map_nsmul, hlev n hn hnp, hlev N Npos hNp]⟩

  have htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev (n * k) (g y) ≫ ψ) ^ n = 1 := by
    intro n hn hnp y
    rw [← hΨ, ← map_pow, hΨ, ← ev_nsmul, ← map_nsmul]
    exact (ker' n hn hnp (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A', q ^ n = 1 ↔ ∃ y, I.ev (n * k) (g y) ≫ ψ = q := by
    intro n hn hnp q
    constructor
    · intro hq
      haveI := hGal.fin
      haveI := hGal.onto
      obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
      let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
        show a₀ ≫ o.A.hom = x
        rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
      have ha : a ≫ ψ = q := Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)
      have han : (a ^ n) ≫ ψ = 1 := by rw [← hΨ, map_pow, hΨ, ha, hq]
      obtain ⟨z, hz⟩ := (hker _).1 han
      rw [hlev N Npos hNp, ← hlev n hn hnp] at hz
      have hnk : 0 < n * k := Nat.mul_pos hn kpos
      have hnkp : (n * k).Coprime p := Nat.Coprime.mul hnp hkp
      have hak : a ^ (n * k) = 1 := by
        rw [pow_mul, hz, ← ev_nsmul, I.ker _ hnk hnkp]
        exact ⟨g z, by rw [smul_smul, mul_comm]⟩
      obtain ⟨w, hw⟩ := (I.onto _ hnk hnkp a).1 hak
      rw [← hw, ← ev_nsmul, ev_eq_iff I _ hnk hnkp] at hz
      obtain ⟨v, hv⟩ := hz
      have e1 : n • (w - g z - k • v) = 0 := by rw [smul_sub, smul_sub, smul_smul, ← hv, sub_self]
      have e2 : w - g z - k • v = 0 := by
        have e3 : ((n : ℤ)) • (w - g z - k • v) = 0 := by rw [natCast_zsmul]; exact e1
        exact (smul_eq_zero.1 e3).resolve_left (by exact_mod_cast hn.ne')
      have e4 : w = g z + k • v := by rw [sub_sub, sub_eq_zero] at e2; exact e2
      obtain ⟨v', hv'⟩ := hg v
      refine ⟨z + v', ?_⟩
      rw [map_add, hv', ← e4, hw, ha]
    · rintro ⟨y, rfl⟩
      exact htor n hn hnp y

  have hnκ : ∀ n : ℕ, n.Coprime p → (n : κ) ≠ 0 := fun n hnp => by
    have h := (b.unit n hnp).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (k ^ 2 / c))
      ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB o.isLB _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb o.isLB, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc, Category.comp_id]
  refine ⟨⟨I.ζ, I.ζ_prim, I.ζ_pow, fun n y => I.ev (n * k) (g y) ≫ ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_⟩
  · intro n y y'
    rw [map_add, I.add, MonObj.mul_comp]
  · intro n b' y
    rw [map_smul, I.lin, Category.assoc, hact, ← Category.assoc]
  · exact fun n hn hnp y => ker' n hn hnp y
  · exact fun n hn hnp q => onto' n hn hnp q
  · intro n m hn hm hnm y
    rw [← hΨ, ← map_pow, hΨ, Nat.mul_right_comm n m k, I.tower (n * k) m (Nat.mul_pos hn kpos) hm
      (by rw [Nat.mul_right_comm]; exact Nat.Coprime.mul hnm hkp)]
  · intro n hn hnp u v
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA' (pull_isLB hP' _) κ x n hn (hnκ n hnp) _ _
      (htor n hn hnp u) (htor n hn hnp v)
    have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) (pull_isLB hP' _) ψ hiso2 he
    have h3 := GlobalTheory.T.commutatorPairing_heckeTranslate_eq_zeta p D R b g c k (N * k) hcp hkp hEF hg hck S s o κ x β hx I n hn hnp u v e
      (by rw [Nat.cast_mul]; exact h2)
    rw [h3] at he
    exact he
  · show toUnit _ ≫ (o.eta (g y) ≫ ψ) = I.ev (N * k) (g y) ≫ ψ
    rw [← Category.assoc, hI]

end GlobalTheory.UPel.HT.Hecke.TateTransl
