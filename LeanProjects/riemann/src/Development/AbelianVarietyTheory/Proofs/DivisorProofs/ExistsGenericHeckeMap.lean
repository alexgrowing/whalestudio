import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.UPel.HT.Gen.HeckeRestrict

section Ev

variable {G : GDatum} {κ : Type} [Field κ] {Q : Type} [Group Q] {act : G.O → Q → Q}
  {e : ℕ → Q → Q → κˣ → Prop} (I : GTateIso G κ Q act e)

theorem ev_zero (n : ℕ) : I.ev n 0 = 1 := by
  have h := I.add n 0 0
  rw [add_zero] at h
  simpa using h

theorem ev_nsmul (n j : ℕ) (w : G.La) : I.ev n (j • w) = I.ev n w ^ j := by
  induction j with
  | zero => rw [zero_smul, ev_zero, pow_zero]
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem ev_neg (n : ℕ) (w : G.La) : I.ev n (-w) = (I.ev n w)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← I.add, neg_add_cancel, ev_zero])

theorem ev_eq_iff (n : ℕ) (hn : 0 < n) (w w' : G.La) :
    I.ev n w = I.ev n w' ↔ ∃ y, w - w' = n • y := by
  rw [← I.ker n hn, sub_eq_add_neg, I.add, ev_neg, mul_inv_eq_one]

theorem ev_mul_nsmul (n j : ℕ) (hn : 0 < n) (hj : 0 < j) (w : G.La) :
    I.ev (n * j) (n • w) = I.ev j w := by
  rw [ev_nsmul, mul_comm n j, I.tower j n hj hn]

def transport {Q' : Type} [Group Q'] {act' : G.O → Q' → Q'} {e' : ℕ → Q' → Q' → κˣ → Prop}
    (Φ : Q ≃* Q') (hact : ∀ c x, Φ (act c x) = act' c (Φ x)) (he : ∀ n x y z, e n x y z → e' n (Φ x) (Φ y) z) :
    GTateIso G κ Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n x := Φ (I.ev n x)
  add n x y := by rw [I.add, map_mul]
  lin n b x := by rw [I.lin, hact]
  ker n hn x := by rw [map_eq_one_iff Φ Φ.injective]; exact I.ker n hn x
  onto n hn q := by
    obtain ⟨q, rfl⟩ := Φ.surjective q
    rw [← map_pow, map_eq_one_iff Φ Φ.injective, I.onto n hn]
    exact exists_congr fun x => Φ.injective.eq_iff.symm
  tower n m hn hm x := by rw [← map_pow, I.tower n m hn hm]
  isom n hn x y := he _ _ _ _ (I.isom n hn x y)

end Ev

abbrev TateAt (G : GDatum) {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN G.O A)
    (P : LB (G2 A).left) {κ : Type} [Field κ] (x : Sp κ ⟶ S) : Type :=
  GTateIso G κ (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
    (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z))

theorem tate_pullback (G : GDatum) {S S' : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S')
    [GrpObj A'] [IsCommMonObj A'] (act : OActN G.O A) (act' : OActN G.O A') (P : LB (G2 A).left)
    (P' : LB (G2 A').left) (hP : P.IsLB) (hP' : P'.IsLB) (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (φ₂ : (G2 A').left ⟶ (G2 A).left) (hp : IsGrpPullback A' A f φ) (hsq : IsSquare φ φ₂)
    (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (hpol : LBIso P' (P.pull φ₂))
    (k : Type) [Field k] (x : Sp k ⟶ S') :
    (∀ I' : TateAt G A' act' P' x, ∃ I : TateAt G A act P (x ≫ f), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) ∧
    (∀ I : TateAt G A act P (x ≫ f), ∃ I' : TateAt G A' act' P' x, ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) := by
  have e : φ ≫ (lift (𝟙 A) (𝟙 A)).left = (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ := by
    apply pullback.hom_ext
    · change (φ ≫ (lift (𝟙 A) (𝟙 A)).left) ≫ (fst A A).left =
        ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂) ≫ (fst A A).left
      rw [Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id, Category.assoc, hsq.1,
        ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp]
    · change (φ ≫ (lift (𝟙 A) (𝟙 A)).left) ≫ (snd A A).left =
        ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂) ≫ (snd A A).left
      rw [Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id, Category.assoc, hsq.2,
        ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp]
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hL' : (P'.pull (lift (𝟙 A') (𝟙 A')).left).IsLB := pull_isLB hP' _
  have H1 : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull (φ ≫ (lift (𝟙 A) (𝟙 A)).left)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P' _ _ rfl) (chartPullSame P _ (fun _ => φ₂) _ _ fun _ => e) hpol
  have hw : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) :=
    LBIso.chartPull (chartPullId _) (chartPullOut P (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => 1) φ
      (fun _ => φ ≫ (lift (𝟙 A) (𝟙 A)).left) fun _ => rfl) H1
  let Φ := GlobalTheory.ObjPull.pushEquiv hp (Over.mk x)
  have hW : ∀ (n : ℕ) (g g' : Over.mk x ⟶ A') (z : kˣ),
      Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z) ↔
        Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n (Φ g) (Φ g') (unitOn z) :=
    fun n g g' z => GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ f φ _ _ hL hL' hp hw (Over.mk x) n g g' (Φ g) (Φ g')
      _ rfl rfl
  have hA : ∀ c (g : Over.mk x ⟶ A'), Φ (g ≫ act'.act c) = Φ g ≫ act.act c := fun c g =>
    Over.OverMorphism.ext (by
      show (g ≫ act'.act c).left ≫ φ = (Φ g ≫ act.act c).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact c, GlobalTheory.ObjPull.pushEquiv_left, Category.assoc])
  refine ⟨fun I' => ⟨transport I' Φ hA fun n g g' z h => (hW n g g' z).1 h, fun n y => rfl⟩,
    fun I => ⟨transport I Φ.symm (fun c g => Φ.injective ?_) (fun n g g' z h => (hW n _ _ z).2 ?_), fun n y => ?_⟩⟩
  · rw [MulEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]
  · rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h
  · exact (GlobalTheory.ObjPull.pushEquiv_symm_left hp (Over.mk x) (I.ev n y)).symm

theorem weil_value (G : GDatum) (g : G.La →ₗ[G.O] G.La) (c k : ℕ) (hc0 : 0 < c) (hk0 : 0 < k)
    (hEF : ∀ x y, G.EF (g x) (g y) = c * G.EF x y) (hck : c ∣ k ^ 2) {S : Scheme.{0}} (A : Over S) [GrpObj A]
    [IsCommMonObj A] (act : OActN G.O A) (P : LB (G2 A).left) (hA : IsAbelianScheme A) (hP : P.IsLB)
    (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (κ : Type) [Field κ] (x : Sp κ ⟶ S) (I : TateAt G A act P x) (n : ℕ) (hn : 0 < n) (u v : G.La)
    (e : (Γ((Over.mk x).left, ⊤))ˣ)
    (he : Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) ((n * (k ^ 2 / c) : ℕ) : ℤ) (I.ev (n * k) (g u))
      (I.ev (n * k) (g v)) e) : e = unitOn (I.ζ n ^ (2 * G.EF u v)) := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hmc : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have hm0 : 0 < k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd (by positivity) hck) hc0
  set m := k ^ 2 / c with hm
  have hN : 0 < n * (m * k ^ 2) := by positivity
  have eN : n * (m * k ^ 2) = n * k * (m * k) := by ring
  have hev : ∀ w : G.La, I.ev (n * k) (g w) = I.ev (n * (m * k ^ 2)) (m • g w) ≫ Out.mulA A k := fun w => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, ← ev_nsmul, smul_smul, mul_comm k m,
      ev_nsmul, eN, I.tower (n * k) (m * k) (by positivity) (by positivity)]
  haveI := isMonHom_mulA (A := A) k
  have hw := GlobalTheory.HeckeWeilValue.lbIso_mulA_diag hA hP hamp h₁ h₂ k
  rw [hev u, hev v] at he
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hL (Out.mulA A k) hw he
  have h2 := I.isom (n * (m * k ^ 2)) hN (m • g u) (m • g v)
  have eZ : ((n * m : ℕ) : ℤ) * ((k ^ 2 : ℕ) : ℤ) = ((n * (m * k ^ 2) : ℕ) : ℤ) := by push_cast; ring
  rw [eZ] at h1
  rw [GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h1 h2]
  congr 1
  have eF : G.EF (m • g u) (m • g v) = ((m * k ^ 2 : ℕ) : ℤ) * G.EF u v := by
    simp only [map_nsmul, LinearMap.smul_apply, hEF, nsmul_eq_mul]
    rw [← hmc]
    push_cast
    ring
  rw [eF, show (2 : ℤ) * (((m * k ^ 2 : ℕ) : ℤ) * G.EF u v) = ((m * k ^ 2 : ℕ) : ℤ) * (2 * G.EF u v) by ring,
    zpow_mul, zpow_natCast, I.ζ_pow n (m * k ^ 2) hn (by positivity)]

theorem tate_transl (G : GDatum) (g : G.La →ₗ[G.O] G.La) (c k N : ℕ) (cpos : 0 < c) (kpos : 0 < k) (Npos : 0 < N)
    (hEF : ∀ x y, G.EF (g x) (g y) = c * G.EF x y) (hg : ∀ x, ∃ y, g y = k • x) (hck : c ∣ k ^ 2)
    {S : Scheme.{0}} (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (act : OActN G.O A) (act' : OActN G.O A') (P : LB (G2 A).left) (P' : LB (G2 A').left)
    (hA : IsAbelianScheme A) (hA' : IsAbelianScheme A') (hP : P.IsLB) (hP' : P'.IsLB)
    (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (ψ : A ⟶ A') [IsMonHom ψ] (hact : ∀ c' : G.O, act.act c' ≫ ψ = ψ ≫ act'.act c')
    (hiso : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)))
    (κ : Type) [Field κ] [IsAlgClosed κ] (hnκ : ∀ n : ℕ, 0 < n → (n : κ) ≠ 0) (x : Sp κ ⟶ S)
    (I : TateAt G A act P x) (hsurj : ∀ q : Over.mk x ⟶ A', ∃ a : Over.mk x ⟶ A, a ≫ ψ = q)
    (hker : ∀ t : Over.mk x ⟶ A, t ≫ ψ = 1 ↔ ∃ z, t = I.ev (N * k) (N • g z)) :
    ∃ I' : TateAt G A' act' P' x, ∀ n y, I'.ev n y = I.ev (n * k) (g y) ≫ ψ := by
  haveI := G.freeLa
  let Ψ : (Over.mk x ⟶ A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have ginj : Function.Injective g := by
    intro u v huv
    have h0 : G.EF (u - v) = 0 := by
      ext w
      have e := hEF (u - v) w
      rw [map_sub, huv, sub_self, map_zero, LinearMap.zero_apply] at e
      rw [LinearMap.zero_apply]
      exact (mul_eq_zero.1 e.symm).resolve_left (by exact_mod_cast cpos.ne')
    have := G.nondeg (h0.trans (map_zero G.EF).symm)
    exact sub_eq_zero.1 this
  have hlev : ∀ n, 0 < n → ∀ w, I.ev (n * k) (n • w) = I.ev k w := fun n hn w => ev_mul_nsmul I n k hn kpos w
  have ker' : ∀ n, 0 < n → ∀ y, I.ev (n * k) (g y) ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn y
    rw [hker]
    constructor
    · rintro ⟨z, hz⟩
      rw [hlev N Npos, ← hlev n hn] at hz
      obtain ⟨w, hw⟩ := (ev_eq_iff I (n * k) (Nat.mul_pos hn kpos) _ _).1 hz
      obtain ⟨w', hw'⟩ := hg w
      refine ⟨z + w', ginj ?_⟩
      rw [map_nsmul, map_add, hw', smul_add, smul_smul, ← sub_eq_iff_eq_add', hw]
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [map_nsmul, hlev n hn, hlev N Npos]⟩
  have htor : ∀ n, 0 < n → ∀ y, (I.ev (n * k) (g y) ≫ ψ) ^ n = 1 := by
    intro n hn y
    rw [← hΨ, ← map_pow, hΨ, ← ev_nsmul, ← map_nsmul]
    exact (ker' n hn (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → ∀ q : Over.mk x ⟶ A', q ^ n = 1 ↔ ∃ y, I.ev (n * k) (g y) ≫ ψ = q := by
    intro n hn q
    constructor
    · intro hq
      obtain ⟨a, ha⟩ := hsurj q
      have han : (a ^ n) ≫ ψ = 1 := by rw [← hΨ, map_pow, hΨ, ha, hq]
      obtain ⟨z, hz⟩ := (hker _).1 han
      rw [hlev N Npos, ← hlev n hn] at hz
      have hnk : 0 < n * k := Nat.mul_pos hn kpos
      have hak : a ^ (n * k) = 1 := by
        rw [pow_mul, hz, ← ev_nsmul, I.ker _ hnk]
        exact ⟨g z, by rw [smul_smul, mul_comm]⟩
      obtain ⟨w, hw⟩ := (I.onto _ hnk a).1 hak
      rw [← hw, ← ev_nsmul, ev_eq_iff I _ hnk] at hz
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
      exact htor n hn y
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) (k ^ 2 / c))
      ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB hP _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb hP, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 A) (𝟙 A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc,
      Category.comp_id]
  refine ⟨⟨I.ζ, I.ζ_prim, I.ζ_pow, fun n y => I.ev (n * k) (g y) ≫ ψ, ?_, ?_, ker', onto', ?_, ?_⟩, fun n y => rfl⟩
  · intro n y y'
    rw [map_add, I.add, MonObj.mul_comp]
  · intro n b' y
    rw [map_smul, I.lin, Category.assoc, hact, ← Category.assoc]
  · intro n m hn hm y
    rw [← hΨ, ← map_pow, hΨ, Nat.mul_right_comm n m k, I.tower (n * k) m (Nat.mul_pos hn kpos) hm]
  · intro n hn u v
    obtain ⟨e, he⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA'
      (pull_isLB hP' _) κ x n hn (hnκ n hn) _ _ (htor n hn u) (htor n hn v)
    have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds hA (pull_isLB hP _) (pull_isLB hP' _) ψ hiso2 he
    have h3 := weil_value G g c k cpos kpos hEF hck A act P hA hP hamp h₁ h₂ κ x I n hn u v e
      (by rw [Nat.cast_mul]; exact h2)
    rw [h3] at he
    exact he

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']

theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

def toGObj {b : Base D R} (φ : R →+* R') (gb : GBase D.toG R') (hρ : gb.ρ = φ b.ρ)
    (ht : ∀ i, gb.t i = φ.comp (b.t i)) {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (s' : S ⟶ Sp R')
    (hs : s' ≫ spMap φ = s) (o : Obj b N s)
    (hgeom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R' →+* k), x ≫ s' = spMap β →
      ∃ I : TateAt D.toG o.A o.act o.P x, ∀ y, toUnit _ ≫ o.eta y = I.ev N y) : GObj gb N s' where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie R'' _ β x hx v hv := by
    have hx' : x ≫ s = spMap (β.comp φ) := by rw [← hs, ← Category.assoc, hx, spMap_comp_ring]
    rw [hρ] at hv
    obtain ⟨w, hw, e⟩ := o.lie R'' (β.comp φ) x hx' v hv
    exact ⟨w, fun i c => by rw [ht]; exact hw i c, e⟩
  lieRank k _ _ x β hx i := by
    have hx' : x ≫ s = spMap (β.comp φ) := by rw [← hs, ← Category.assoc, hx, spMap_comp_ring]
    rw [ht]
    exact o.lieRank k x (β.comp φ) hx' i
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := hgeom

theorem isGPull_comp {b : Base D R} {gb : GBase D.toG R'} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R'}
    {s₂ : S₂ ⟶ Sp R'} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj gb N s₁} {o₂ : GObj gb N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂}
    {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : IsGPull o₂ o₃ g) : IsGPull o₁ o₃ (f ≫ g) := by
  obtain ⟨ψ, ψ₂, hc, hsq, hact, ⟨hpol⟩, heta⟩ := h₂
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull ψ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull ψ₂) h₁.φ₂ h₁.φ₂ rfl) hpol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ ψ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => ψ₂) (fun _ => 1) h₁.φ₂) H
  refine ⟨h₁.φ ≫ ψ, h₁.φ₂ ≫ ψ₂, h₁.cart.comp hc, ⟨?_, ?_⟩, fun c => ?_,
    ⟨LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'⟩, fun y => ?_⟩
  · rw [Category.assoc, hsq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
  · rw [Category.assoc, hsq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) (h₁.act c)).trans
      ((Category.assoc _ _ _).trans ((congrArg (h₁.φ ≫ ·) (hact c)).trans (Category.assoc _ _ _).symm)))
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) (h₁.eta y)).trans
      ((Category.assoc _ _ _).trans ((congrArg (f ≫ ·) (heta y)).trans (Category.assoc _ _ _).symm)))

open GlobalTheory.UPel.HT.Hecke in

theorem tate_hecke {b : Base D R} (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) (cpos : 0 < c) (kpos : 0 < k) (Npos : 0 < N)
    (hEF : ∀ x y, D.EF (g x) (g y) = c * D.EF x y) (hg : ∀ x, ∃ y, g y = k • x) {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (h : IsHecke g c k N o o' ψ)
    (κ : Type) [Field κ] [IsAlgClosed κ] (hnκ : ∀ n : ℕ, 0 < n → (n : κ) ≠ 0) (x : Sp κ ⟶ S)
    (I : TateAt D.toG o.A o.act o.P x) (hI : ∀ y, toUnit _ ≫ o.eta y = I.ev (N * k) y) :
    ∃ I' : TateAt D.toG o'.A o'.act o'.P x, ∀ y, toUnit _ ≫ o'.eta y = I'.ev N y := by
  obtain ⟨hψ, hact, heta, hGal, ⟨hiso⟩, hck⟩ := h
  have hsurj : ∀ q : Over.mk x ⟶ o'.A, ∃ a : Over.mk x ⟶ o.A, a ≫ ψ = q := fun q => by
    haveI := hGal.fin
    haveI := hGal.onto
    obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
    let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
      show a₀ ≫ o.A.hom = x
      rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
    exact ⟨a, Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)⟩
  have hker : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 ↔ ∃ z, t = I.ev (N * k) (N • g z) := by
    intro t
    constructor
    · intro ht
      have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
        rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
      obtain ⟨h, hh, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
      obtain ⟨z, hz⟩ := h.2
      refine ⟨z, ?_⟩
      have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 :=
        Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
      rw [e2, TateTransl.one_comp_transl_pt, hz, hI]
    · rintro ⟨z, rfl⟩
      rw [← hI, Category.assoc, comp_eq_one_of_transl ψ (o.eta (N • g z)) (hGal.inv ⟨_, mem_heckeSub o g N z⟩),
        MonObj.comp_one]
  obtain ⟨I', hI'⟩ := tate_transl D.toG g c k N cpos kpos Npos hEF hg hck o.A o'.A o.act o'.act o.P o'.P o.ab o'.ab
    o.isLB o'.isLB o.ample o.rig₁ o.rig₂ ψ hact hiso κ hnκ x I hsurj hker
  refine ⟨I', fun y => ?_⟩
  have e := hI' N y
  rw [heta, ← Category.assoc, hI]
  exact e.symm

end GlobalTheory.UPel.HT.Gen.HeckeRestrict
