import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPointStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

private theorem lbIso_pull_diag_of_lbIso_sq2 {Y : Scheme} {A B : Over Y} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (ψ : A ⟶ B) (P : LB (G2 A).left) (P' : LB (G2 B).left) (hP : P.IsLB) (hP' : P'.IsLB) (c : ℕ)
    (h : LBIso (Hecke.lbPow P c) (P'.pull (Hecke.sq2 ψ))) :
    LBIso (Geo.Tor.lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) c) ((P'.pull (lift (𝟙 B) (𝟙 B)).left).pull ψ.left) := by
  have hL := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have hM := pull_isLB hP' (lift (𝟙 B) (𝟙 B)).left
  rw [← GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hM _)]
  unfold Hecke.lbPow at h
  rw [← GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP' _)] at h
  rw [GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_pull hM, GlobalTheory.CechPic.cls_pull hP', GlobalTheory.CechPic.cls_pull hP,
    ← GlobalTheory.CechPic.pull_comp]
  rw [GlobalTheory.CechPic.cls_linComb hP, GlobalTheory.CechPic.cls_pull hP'] at h
  simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← map_nsmul, h, ← GlobalTheory.CechPic.pull_comp]
  have hd : Over.Hom.left (lift (𝟙 A) (𝟙 A)) ≫ Hecke.sq2 ψ = Over.Hom.left ψ ≫ Over.Hom.left (lift (𝟙 B) (𝟙 B)) := by
    rw [Hecke.sq2, ← Over.comp_left, ← Over.comp_left]
    congr 1
    ext <;> simp
  rw [hd]

set_option maxHeartbeats 1000000 in
theorem UpperTheory.Cb.pow_polarization_iso_pullback_of_descent :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ B) (fun a g => g ≫ act'.act a) (fun n g g' z => Out.WeilIs B (P'.pull (lift (𝟙 B) (𝟙 B)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq P' hP' h1 h2 act' hact κ _ _ x β hx
  obtain ⟨I, hI⟩ := o.geom κ x β hx
  obtain ⟨e, rfl⟩ := hc
  obtain ⟨hψ, hψ', hψψ', hψ'ψ⟩ := hq
  have hLA := pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left
  have hMB := pull_isLB hP'.1 (lift (𝟙 B) (𝟙 B)).left
  have hiso := lbIso_pull_diag_of_lbIso_sq2 ψ o.P P' o.isLB hP'.1 (p ^ e) h2
  have hcop : ∀ n : ℕ, n.Coprime p → (p ^ e).Coprime n := fun n hn => Nat.Coprime.pow_left e hn.symm
  have hev : ∀ (n d : ℕ) (z : D.La), I.ev n (d • z) = I.ev n z ^ d := by
    intro n d z
    induction d with
    | zero =>
      have h0 := I.add n 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_eq_left.mp h0.symm
    | succ d ih => rw [succ_nsmul, I.add, ih, pow_succ]
  have hpt : ∀ q : Over.mk x ⟶ B, q ≫ ψ' ≫ ψ = q ^ (p ^ e) := by
    intro q
    rw [hψ'ψ, MonObj.comp_pow, Category.comp_id]
  have hpA : ∀ q : Over.mk x ⟶ o.A, q ≫ ψ ≫ ψ' = q ^ (p ^ e) := by
    intro q
    rw [hψψ', MonObj.comp_pow, Category.comp_id]
  have htor : ∀ (n : ℕ), 0 < n → n.Coprime p → ∀ w, (I.ev n w ≫ ψ) ^ n = 1 := by
    intro n hn hnp w
    rw [← MonObj.pow_comp, (I.onto n hn hnp _).2 ⟨w, rfl⟩, MonObj.one_comp]
  refine ⟨{ ζ := fun n => I.ζ n ^ (p ^ e)
            ζ_prim := fun n hn hnp => (I.ζ_prim n hn hnp).pow_of_coprime _ (hcop n hnp)
            ζ_pow := fun n m hn hm hnm => by
              show (I.ζ (n * m) ^ (p ^ e)) ^ m = I.ζ n ^ (p ^ e)
              rw [pow_right_comm, I.ζ_pow n m hn hm hnm]
            ev := fun n z => I.ev n z ≫ ψ
            add := fun n z z' => by
              show I.ev n (z + z') ≫ ψ = (I.ev n z ≫ ψ) * (I.ev n z' ≫ ψ)
              rw [I.add, MonObj.mul_comp]
            lin := fun n a z => by
              show I.ev n (a • z) ≫ ψ = (I.ev n z ≫ ψ) ≫ act'.act a
              rw [I.lin, Category.assoc, hact, Category.assoc]
            ker := ?_
            onto := ?_
            tower := fun n m hn hm hnm z => by
              show (I.ev (n * m) z ≫ ψ) ^ m = I.ev n z ≫ ψ
              rw [← MonObj.pow_comp, I.tower n m hn hm hnm]
            isom := ?_ }, fun z => ?_⟩
  · intro n hn hnp z
    show I.ev n z ≫ ψ = 1 ↔ _
    rw [← I.ker n hn hnp z]
    constructor
    · intro h
      have h1' : I.ev n z ^ (p ^ e) = 1 := by
        rw [← hpA, ← Category.assoc, h, MonObj.one_comp]
      have h2' : I.ev n z ^ n = 1 := (I.onto n hn hnp _).2 ⟨z, rfl⟩
      have h3 := pow_gcd_eq_one.2 ⟨h1', h2'⟩
      rwa [Nat.Coprime.gcd_eq_one (hcop n hnp), pow_one] at h3
    · intro h
      rw [h, MonObj.one_comp]
  · intro n hn hnp q
    show q ^ n = 1 ↔ ∃ z, I.ev n z ≫ ψ = q
    constructor
    · intro hq
      have hq' : (q ≫ ψ') ^ n = 1 := by
        rw [← MonObj.pow_comp, hq, MonObj.one_comp]
      obtain ⟨z, hz⟩ := (I.onto n hn hnp _).1 hq'
      obtain ⟨d, hd⟩ : ∃ d : ℕ, q ^ (p ^ e * d) = q := by
        rcases Nat.lt_or_ge 1 n with h1n | h1n
        · obtain ⟨d, -, hd⟩ := Nat.exists_mul_mod_eq_one_of_coprime (hcop n hnp) h1n
          refine ⟨d, ?_⟩
          rw [← Nat.div_add_mod (p ^ e * d) n, pow_add, pow_mul, hq, one_pow, _root_.one_mul, hd, pow_one]
        · have hn1 : n = 1 := by omega
          subst hn1
          rw [pow_one] at hq
          exact ⟨0, by rw [mul_zero, pow_zero, hq]⟩
      refine ⟨d • z, ?_⟩
      rw [hev, MonObj.pow_comp, hz, Category.assoc, hpt, ← pow_mul, hd]
    · rintro ⟨z, rfl⟩
      exact htor n hn hnp z
  · intro n hn hnp z z'
    show Out.WeilIs B _ _ (I.ev n z ≫ ψ) (I.ev n z' ≫ ψ) (unitOn ((I.ζ n ^ (p ^ e)) ^ (2 * D.EF z z')))
    have hA := I.isom n hn hnp z z'
    have hnκ : ((n : ℕ) : κ) ≠ 0 := by
      have h3 := (b.unit n hnp).map β
      rw [map_natCast] at h3
      exact h3.ne_zero
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_weilCommutatorPairing_torsion_geometricPoint Y B _ hB hMB κ x n hn hnκ _ _ (htor n hn hnp z) (htor n hn hnp z')
    have h3 := (GlobalTheory.weilIs_along_hom GlobalTheory.globalFns_holds Y o.A B ψ _ _ (p ^ e) (n : ℤ) (Over.mk x)
      (I.ev n z) (I.ev n z') _ u o.ab hB hLA hMB hψ hiso hu).2 hA
    rw [h3] at hu
    convert hu using 1
    unfold unitOn
    rw [← map_pow]
    congr 1
    rw [← zpow_natCast (I.ζ n) (p ^ e), ← zpow_mul, ← zpow_natCast (I.ζ n ^ (2 * D.EF z z')) (p ^ e), ← zpow_mul,
      mul_comm]
  · show toUnit (Over.mk x) ≫ o.eta z ≫ ψ = I.ev N z ≫ ψ
    rw [← Category.assoc, hI]
