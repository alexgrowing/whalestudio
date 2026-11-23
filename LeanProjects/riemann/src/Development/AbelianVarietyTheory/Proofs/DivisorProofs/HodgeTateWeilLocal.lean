import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateLatticeSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.UPel.HT.HeckeAd

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd.TateTranslAt

open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Hecke.TateTransl GlobalTheory.UPel.HT.HeckeAd.TateTranslSys

theorem exists_tateIsoO_of_given {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R)
    (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ) (hcp : c.Coprime p) (hkp : k.Coprime p) (hN : 3 ≤ N)
    (hNp : N.Coprime p) (hck : c ∣ k ^ 2)
    (hlin : ∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧
      (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hsurj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z)
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A']
    (act' : OActN D.O A') (ψ : o.A ⟶ A') (hA' : IsAbelianScheme A') (hψ : IsMonHom ψ)
    (hGal : GlobalTheory.ZM.IsGaloisCover (heckeSubA o (h (N * k)) N) (fun g => (transl g.1).left) ψ.left)
    (hact : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') (P' : LB (G2 A').left) (hP' : P'.IsLB)
    (hiso : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)))
    (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ)
    (I : TateIsoO D κ (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)))
    (hI : ∀ y, toUnit _ ≫ o.eta y = I.ev (N * k) y) :
    ∃ I' : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c)
        (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)),
      (∀ y, toUnit _ ≫ (o.eta (h (N * k) y) ≫ ψ) = I'.ev N y) ∧
      ∀ n, 0 < n → n.Coprime p → ∀ y, I'.ev n y = I.ev (n * k) (h (n * k) y) ≫ ψ := by
  haveI := D.freeLa
  have kpos : 0 < k := levelPos_of_coprime hkp
  have cpos : 0 < c := levelPos_of_coprime hcp
  have Npos : 0 < N := by omega
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have hlev : ∀ n, 0 < n → n.Coprime p → ∀ w, I.ev (n * k) (n • w) = I.ev k w := fun n hn hnp w =>
    ev_mul_nsmul I n k hn kpos (Nat.Coprime.mul hkp hnp) w

  have hk_eq : ∀ n, 0 < n → n.Coprime p → ∀ z, I.ev k (h (n * k) z) = I.ev k (h k z) := by
    intro n hn hnp z
    obtain ⟨z', hz'⟩ := (hcomp k n kpos hn (Nat.Coprime.mul hkp hnp)).1 z
    rw [mul_comm n k, hz', I.add, (I.ker k kpos hkp (k • z')).2 ⟨z', rfl⟩, _root_.mul_one]
  have hker : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 ↔ ∃ z, t = I.ev (N * k) (N • h (N * k) z) := by
    intro t
    constructor
    · intro ht
      have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
        rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
      obtain ⟨g, hg, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
      obtain ⟨z, hz⟩ := g.2
      refine ⟨z, ?_⟩
      have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl g.1 :=
        Over.OverMorphism.ext (by rw [Over.comp_left]; exact hg.symm)
      rw [e2, one_comp_transl_pt, hz, hI]
    · rintro ⟨z, rfl⟩
      rw [← hI, Category.assoc, comp_eq_one_of_transl ψ (o.eta (N • h (N * k) z))
        (hGal.inv ⟨_, mem_heckeSubA o (h (N * k)) N z⟩), MonObj.comp_one]
  have hkerN : ∀ n, 0 < n → n.Coprime p → ∀ t : Over.mk x ⟶ o.A,
      t ≫ ψ = 1 ↔ ∃ z, t = I.ev (n * k) (n • h (n * k) z) := by
    intro n hn hnp t
    rw [hker]
    have e : ∀ z, I.ev (N * k) (N • h (N * k) z) = I.ev (n * k) (n • h (n * k) z) := fun z => by
      rw [hlev N Npos hNp, hk_eq N Npos hNp, hlev n hn hnp, hk_eq n hn hnp]
    simp only [e]
  have ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev (n * k) (h (n * k) y) ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn hnp y
    have hnk : 0 < n * k := Nat.mul_pos hn kpos
    have hnkp : (n * k).Coprime p := Nat.Coprime.mul hnp hkp
    rw [hkerN n hn hnp]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨v, hv⟩ := (ev_eq_iff I (n * k) hnk hnkp _ _).1 hz
      obtain ⟨z', hz'⟩ := exists_nsmul_of_map_eq D h u c k hcp hkp hcomp hsim hsurj n hn hnp (y - n • z) v
        (by rw [map_sub, map_nsmul, hv])
      exact ⟨z + z', by rw [smul_add, ← hz', add_sub_cancel]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [map_nsmul]⟩
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev (n * k) (h (n * k) y) ≫ ψ) ^ n = 1 := by
    intro n hn hnp y
    rw [← hΨ, ← map_pow, hΨ, ← TateTransl.ev_nsmul, ← map_nsmul]
    exact (ker' n hn hnp (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A',
      q ^ n = 1 ↔ ∃ y, I.ev (n * k) (h (n * k) y) ≫ ψ = q := by
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
      obtain ⟨z, hz⟩ := (hkerN n hn hnp _).1 han
      have hnk : 0 < n * k := Nat.mul_pos hn kpos
      have hnkp : (n * k).Coprime p := Nat.Coprime.mul hnp hkp
      have hak : a ^ (n * k) = 1 := by
        rw [pow_mul, hz, ← TateTransl.ev_nsmul, I.ker _ hnk hnkp]
        exact ⟨h (n * k) z, by rw [smul_smul, mul_comm]⟩
      obtain ⟨w, hw⟩ := (I.onto _ hnk hnkp a).1 hak
      rw [← hw, ← TateTransl.ev_nsmul, ev_eq_iff I _ hnk hnkp] at hz
      obtain ⟨v, hv⟩ := hz
      have e1 : n • (w - h (n * k) z - k • v) = 0 := by rw [smul_sub, smul_sub, smul_smul, ← hv, sub_self]
      have e2 : w - h (n * k) z - k • v = 0 := by
        have e3 : ((n : ℤ)) • (w - h (n * k) z - k • v) = 0 := by rw [natCast_zsmul]; exact e1
        exact (smul_eq_zero.1 e3).resolve_left (by exact_mod_cast hn.ne')
      have e4 : w = h (n * k) z + k • v := by rw [sub_sub, sub_eq_zero] at e2; exact e2
      obtain ⟨y'', z'', hy''⟩ := hsurj (n * k) hnk hnkp v
      have e5 : h (n * k) (z + y'') = w + (n * k) • z'' := by rw [map_add, hy'', e4, add_assoc]
      refine ⟨z + y'', ?_⟩
      rw [e5, I.add, (I.ker _ hnk hnkp ((n * k) • z'')).2 ⟨z'', rfl⟩, _root_.mul_one, hw, ha]
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

  have hmc : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have hm0 : 0 < k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd (by positivity) hck) cpos
  have hmp : (k ^ 2 / c).Coprime p :=
    Nat.Coprime.coprime_dvd_left (Dvd.intro c hmc) (Nat.Coprime.pow_left 2 hkp)
  let ev' : ℕ → D.La → (Over.mk x ⟶ A') := fun n y =>
    if 0 < n ∧ n.Coprime p then I.ev (n * k) (h (n * k) y) ≫ ψ else 1
  have hev' : ∀ n, 0 < n → n.Coprime p → ∀ y, ev' n y = I.ev (n * k) (h (n * k) y) ≫ ψ :=
    fun n hn hnp y => if_pos ⟨hn, hnp⟩
  refine ⟨⟨fun n => I.ζ n ^ u n, ?_, ?_, ev', ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_, hev'⟩
  · intro n hn hnp
    exact (I.ζ_prim n hn hnp).zpow_of_gcd_eq_one (u n) (Int.isCoprime_iff_gcd_eq_one.1 (hsim n hn hnp).1)
  · intro n m hn hm hnm
    show (I.ζ (n * m) ^ u (n * m)) ^ m = I.ζ n ^ u n
    rw [← I.ζ_pow n m hn hm hnm]
    simp only [← zpow_natCast, ← zpow_mul]
    apply zpow_eq_zpow_of_dvd (I.ζ_prim (n * m) (Nat.mul_pos hn hm) hnm).pow_eq_one
    obtain ⟨t, ht⟩ := (hcomp n m hn hm hnm).2
    exact ⟨t, by push_cast; linear_combination (m : ℤ) * ht⟩
  · intro n y y'
    simp only [ev']
    split_ifs with hn
    · rw [map_add, I.add, MonObj.mul_comp]
    · rw [_root_.mul_one]
  · intro n b' y
    simp only [ev']
    split_ifs with hn
    · have hnk : 0 < n * k := Nat.mul_pos hn.1 kpos
      have hnkp : (n * k).Coprime p := Nat.Coprime.mul hn.2 hkp
      obtain ⟨z, hz⟩ := hlin (n * k) hnk hnkp b' y
      rw [hz, I.add, (I.ker _ hnk hnkp _).2 ⟨z, rfl⟩, _root_.mul_one, I.lin, Category.assoc, hact,
        ← Category.assoc]
    · haveI := act'.hom b'
      rw [MonObj.one_comp]
  · intro n hn hnp y
    rw [hev' n hn hnp]
    exact ker' n hn hnp y
  · intro n hn hnp q
    simp only [hev' n hn hnp]
    exact onto' n hn hnp q
  · intro n m hn hm hnm y
    have hn' : n.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hnm
    have hnk : 0 < n * k := Nat.mul_pos hn kpos
    have hnkm : (n * k * m).Coprime p := by rw [Nat.mul_right_comm]; exact Nat.Coprime.mul hnm hkp
    rw [hev' (n * m) (Nat.mul_pos hn hm) hnm, hev' n hn hn', ← hΨ, ← map_pow, hΨ, Nat.mul_right_comm n m k,
      I.tower (n * k) m hnk hm hnkm]
    obtain ⟨z, hz⟩ := (hcomp (n * k) m hnk hm hnkm).1 y
    rw [hz, I.add, (I.ker _ hnk (Nat.Coprime.mul hn' hkp) _).2 ⟨z, rfl⟩, _root_.mul_one]
  · intro n hn hnp y y'
    have hnk : 0 < n * k := Nat.mul_pos hn kpos
    have hnkp : (n * k).Coprime p := Nat.Coprime.mul hnp hkp
    have hnkc : (n * k * c).Coprime p := Nat.Coprime.mul hnkp hcp
    have hrep : ∀ y, I.ev (n * k) (h (n * k) y) = I.ev (n * k) (h (n * k * c) y) := fun y => by
      obtain ⟨z, hz⟩ := (hcomp (n * k) c hnk cpos hnkc).1 y
      rw [hz, I.add, (I.ker _ hnk hnkp _).2 ⟨z, rfl⟩, _root_.mul_one]
    rw [hev' n hn hnp, hev' n hn hnp]
    obtain ⟨e, he⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA'
      (pull_isLB hP' _) κ x n hn (hnκ n hnp) _ _ (htor n hn hnp y) (htor n hn hnp y')
    have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) (pull_isLB hP' _) ψ
      hiso2 he
    rw [hrep y, hrep y'] at h2
    have hNp' : (n * (k ^ 2 / c * k ^ 2)).Coprime p :=
      Nat.Coprime.mul hnp (Nat.Coprime.mul hmp (Nat.Coprime.pow_left 2 hkp))
    have h3 := weilIs_ev_value o I k (k ^ 2 / c) n kpos hm0 hn hNp' _ _ e (by rw [Nat.cast_mul]; exact h2)
    have h4 : I.ζ (n * (k ^ 2 / c * k ^ 2)) ^ (2 * D.EF ((k ^ 2 / c) • h (n * k * c) y) ((k ^ 2 / c) • h (n * k * c) y'))
        = (I.ζ n ^ u n) ^ (2 * D.EF y y') := by
      rw [← I.ζ_pow n (k ^ 2 / c * k ^ 2) hn (by positivity) hNp']
      simp only [← zpow_natCast, ← zpow_mul]
      apply zpow_eq_zpow_of_dvd (I.ζ_prim _ (by positivity) hNp').pow_eq_one
      obtain ⟨t, ht⟩ := (hsim (n * k * c) (by positivity) hnkc).2 y y'
      obtain ⟨s', hs'⟩ := (hcomp n (k * c) hn (by positivity) (by rw [← _root_.mul_assoc]; exact hnkc)).2
      rw [← _root_.mul_assoc] at hs'
      have hmcZ : ((k ^ 2 / c : ℕ) : ℤ) * (c : ℤ) = (k : ℤ) ^ 2 := by exact_mod_cast hmc
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      refine ⟨2 * s' * D.EF y y' + 2 * k * t, ?_⟩
      simp only [Nat.cast_mul, Nat.cast_pow] at ht hs' ⊢
      linear_combination (2 * ((k ^ 2 / c : ℕ) : ℤ) * ((k ^ 2 / c : ℕ) : ℤ)) * ht
        + (2 * ((k ^ 2 / c : ℕ) : ℤ) * (k : ℤ) ^ 2 * D.EF y y') * hs'
        + (2 * ((k ^ 2 / c : ℕ) : ℤ) * u (n * k * c) * D.EF y y'
          + 2 * ((k ^ 2 / c : ℕ) : ℤ) * (n : ℤ) * (k : ℤ) * t) * hmcZ
    rw [h3, h4] at he
    exact he
  · show toUnit _ ≫ (o.eta (h (N * k) y) ≫ ψ) = ev' N y
    rw [hev' N Npos hNp, ← Category.assoc, hI]

end GlobalTheory.UPel.HT.HeckeAd.TateTranslAt

namespace GlobalTheory.UPel.HT.HeckeAd

end GlobalTheory.UPel.HT.HeckeAd
