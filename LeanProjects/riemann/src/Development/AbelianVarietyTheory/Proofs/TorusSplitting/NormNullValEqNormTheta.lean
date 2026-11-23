import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormGenEqConstMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NullNorm

abbrev cpt : Sp ℂ := IsLocalRing.closedPoint ℂ

def ev : (Sp ℂ).presheaf.stalk cpt →+* ℂ := (stalkClosedPointIso (CommRingCat.of ℂ)).hom.hom

theorem mem_iff {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) : f cpt ∈ U ↔ ⊤ ≤ f ⁻¹ᵁ U := by
  rw [top_le_preimage_iff_mem, Subsingleton.elim (α := PrimeSpectrum ℂ) default (IsLocalRing.closedPoint ℂ)]

theorem ev_gs {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)) :
    ev (gs f cpt U a) = valAt' f U a := by
  have h' := (mem_iff f U).1 h
  rw [gs_eq f cpt U h, valAt'_eq_valAt f h', valAt, ← germ_stalkClosedPointIso_hom (CommRingCat.of ℂ)]
  exact congrArg ev (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h') cpt trivial _).symm

theorem ev_gm {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)ˣ) :
    ev (gm f cpt U a).val = valAt' f U a.val :=
  (congrArg ev (gs_unit f cpt U h a).symm).trans (ev_gs f U h _)

def nv : ((Sp ℂ).presheaf.stalk cpt)ˣ →* ℝ where
  toFun u := ‖ev u.val‖
  map_one' := by simp
  map_mul' u v := by simp

theorem nv_apply (u : ((Sp ℂ).presheaf.stalk cpt)ˣ) : nv u = ‖ev u.val‖ := rfl

theorem nv_zpow (u : ((Sp ℂ).presheaf.stalk cpt)ˣ) (k : ℤ) : nv (u ^ k) = nv u ^ k := by
  have := congrArg Units.val (map_zpow nv.toHomUnits u k)
  rw [Units.val_zpow_eq_zpow_val] at this
  exact this

theorem value_val {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {a : ℤ} {T : Over S}
    {s : LB.Sec (Out.LPow A L a T)} {y : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => y.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (h : Out.IsValueAt A L a s y τ v) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (r ≫ (Out.ptSecT A y).left) z J =
      gs r z ⊤ v * (val τ r z J).val := by
  let j : Fin 1 → L.ι := fun _ => J (r ≫ y.left)
  have hz : r z ∈ LB.wchart L (fun _ : Fin 1 => y.left) j := hJ.mem _ r
  have e := congrArg (gs r z (LB.wchart L (fun _ : Fin 1 => y.left) j)) (h j)
  have a₂ := (gs_res r z (Out.val_le A L y j) hz (((Out.ptSecT A y).left.app _).hom (s.f j))).trans
    (gs_pull r (Out.ptSecT A y).left z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (Out.val_le A L y j hz) _)
  have a₃ := sval_of (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s
    (r ≫ (Out.ptSecT A y).left) z J j
    (fun _ => congrArg J (by rw [Category.assoc, ← Over.comp_left, Out.ptSecT, lift_snd]))
  exact a₃.trans (a₂.symm.trans (e.trans ((gs_mul r z _ hz _ _).trans
    (congrArg₂ (· * ·) (gs_res r z le_top hz _) (gs_unit r z _ hz _)))))

theorem val_rigT {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (rig : LB.Gen (L.pull (eSec A)))
    (T : Over S) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    val (Out.rigT A L rig T k) r z J = val rig (r ≫ T.hom) z J ^ k := by
  have hz := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res r z _ hz _).trans (gm_pull r T.hom z _ ?_ _)))
  exact Out.rigT_le A L _ hz

theorem val_norm {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {rig : LB.Gen (L.pull (eSec A))} {N : ℕ}
    {α} (h : Out.IsNormMul A L rig N α) {Z : Scheme.{0}} (r : Z ⟶ S) (z : Z) {J} (hJ : Good L z J) :
    val α (r ≫ eSec A) z J = val rig r z J ^ ((N : ℤ) ^ 2) * (val rig r z J)⁻¹ := by
  have e := val_corr hJ h r
  rw [val_pull hJ, val_mul hJ, val_inv] at e
  exact e.trans (congrArg₂ (· * ·) (map_zpow _ _ _) rfl)

theorem tele (f : ℕ → ℝ) (hf : ∀ j, 0 < f j) (k : ℤ) (n : ℕ) :
    ∏ j ∈ Finset.range n, (f j ^ k * f (j + 1) ^ (-k)) = f 0 ^ k * f n ^ (-k) := by
  induction n with
  | zero => rw [Finset.prod_range_zero, zpow_neg, mul_inv_cancel₀ (zpow_pos (hf 0) k).ne']
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, zpow_neg, _root_.mul_assoc, inv_mul_cancel_left₀ (zpow_pos (hf n) k).ne']

theorem core {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x : Sp ℂ ⟶ S)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ex : V → (Over.mk x ⟶ A))
    (hadd : ∀ z w, ex (z + w) = ex z * ex w) (ν : L.L.ι → V → ℝ)
    (hpos : ∀ j z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.L.U j → 0 < ν j z)
    (h0 : ∀ j, ⊤ ≤ (ex 0).left ⁻¹ᵁ L.L.U j →
      ν j 0 = ‖valAt' x ((L.L.pull (eSec A)).U (fun _ => j)) (L.rig.s (fun _ => j)).val‖)
    (hper : ∀ j a, ex a = 1 → ⊤ ≤ (ex 0).left ⁻¹ᵁ L.L.U j → ν j a = ν j 0)
    (hiso : ∀ (m : Fin 2 → ((Over.mk x ⊗ A).left ⟶ A.left)) (ε n : Fin 2 → ℤ) (a : Fin 2 → V)
      (α : LB.Gen (LB.LinComb L.L m ε)), α.IsGen → ∑ k, ε k * n k ^ 2 = 0 →
      (∀ k z, (Out.ptSecT A (ex z)).left ≫ m k = (ex ((n k : ℂ) • z + a k)).left) →
      ∃ C : ℝ, 0 < C ∧ ∀ (z : V) (j : Fin 2 → L.L.ι), (∀ k, ⊤ ≤ (ex ((n k : ℂ) • z + a k)).left ⁻¹ᵁ L.L.U (j k)) →
        ‖valAt' (Out.ptSecT A (ex z)).left ((LB.LinComb L.L m ε).U j) (α.s j).val‖ =
          C * ∏ k, ν (j k) ((n k : ℂ) • z + a k) ^ ε k)
    {N : ℕ} (hN : N ≠ 0) (s : LB.Sec (Out.LPow A L.L 1 (Over.mk x))) (t : V → ℝ)
    (hs : ∀ j z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.L.U j →
      ‖valAt' (Out.ptSecT A (ex z)).left ((Out.LPow A L.L 1 (Over.mk x)).U (fun _ => j)) (s.f (fun _ => j))‖ =
        t z * ν j z)
    (z : V) (hz : ex z ^ (N ^ 2) = 1) (w : ℂ) (F : LB.Sec (Out.LPow A L.L ((N : ℤ) ^ 2) (Over.mk x)))
    (hF : IsVtOver A L N (fun q => q = ex z) s (ex z ^ N) F)
    (hw : Out.IsValueAt A L.L ((N : ℤ) ^ 2) F 1 (Out.rigT A L.L L.rig (Over.mk x) ((N : ℤ) ^ 2)) (toΓ ℂ w)) :
    ‖w‖ = t ((N : ℂ) • z) := by
  obtain ⟨_, α₀, α, s₁, U, -, rfl, g₀, n₀, cα, tw, sl, ac⟩ := hF
  have hU := sl.pt_eq
  choose J hJ using fun χ : Sp ℂ ⟶ A.left => exists_chart L.isLB (χ cpt)
  replace hJ : Good L.L cpt J := hJ
  have e0 : ex 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have en : ∀ (n : ℕ) (v : V), ex ((n : ℂ) • v) = ex v ^ n := fun n v => by
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, e0]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have ch : ∀ v, ⊤ ≤ (ex v).left ⁻¹ᵁ L.L.U (J (ex v).left) := fun v => (mem_iff _ _).1 (hJ _)
  obtain ⟨n, hn⟩ : ∃ n : V → ℝ, ∀ v, n v = ν (J (ex v).left) v := ⟨_, fun _ => rfl⟩
  have np : ∀ v, 0 < n v := fun v => by rw [hn]; exact hpos _ _ (ch v)
  have iso : ∀ (m : Fin 2 → ((Over.mk x ⊗ A).left ⟶ A.left)) (ε : Fin 2 → ℤ) (b : ℕ) (a : V)
      (α : LB.Gen (LB.LinComb L.L m ε)), α.IsGen → ε 0 + ε 1 * (b : ℤ) ^ 2 = 0 →
      (∀ v, (lift (𝟙 _) (ex v)).left ≫ m 0 = (ex v).left) →
      (∀ v, (lift (𝟙 _) (ex v)).left ≫ m 1 = (ex ((b : ℂ) • v + a)).left) →
      ∃ C : ℝ, 0 < C ∧ ∀ v : V, nv (val α (lift (𝟙 _) (ex v)).left cpt J) =
        C * (n v ^ ε 0 * n ((b : ℂ) • v + a) ^ ε 1) := fun m ε b a α hα hε h₀ h₁ => by
    have hm : ∀ k v, (Out.ptSecT A (ex v)).left ≫ m k =
        (ex ((((![1, (b : ℤ)] : Fin 2 → ℤ) k : ℤ) : ℂ) • v + (![0, a] : Fin 2 → V) k)).left := fun k v => by
      fin_cases k
      · exact (h₀ v).trans (by simp)
      · exact (h₁ v).trans (by simp)
    obtain ⟨C, hC, H⟩ := hiso m ε ![1, b] ![0, a] α hα (by simpa [Fin.sum_univ_two] using hε) hm
    refine ⟨C, hC, fun v => ?_⟩
    have := H v (fun k => J ((Out.ptSecT A (ex v)).left ≫ m k)) (fun k => by rw [hm]; exact ch _)
    refine (congrArg norm (ev_gm _ _ (hJ.mem m _) _)).trans (this.trans ?_)
    simp only [hm, ← hn]
    simp [Fin.prod_univ_two]
  have sn : ∀ y : Over.mk x ⟶ A, (lift (𝟙 _) y).left ≫ (snd (Over.mk x) A).left = y.left := fun y => by
    rw [← Over.comp_left, lift_snd]
  have o1 : (1 : Over.mk x ⟶ A).left = x ≫ eSec A := rfl
  have n0 : nv (val L.rig x cpt J) = n 0 := by
    rw [hn, h0 _ (ch 0), e0, o1]
    exact congrArg norm (ev_gm _ _ (hJ.mem (fun _ : PUnit => eSec A) x) _)
  obtain ⟨C₁, -, H₁⟩ := iso _ _ N 0 (LB.pullGen L.L _ _ α₀ (snd (Over.mk x) A).left)
    (DVR.pullGen_isGen _ _ _ _ g₀ _) (by simp) (fun v => by
      rw [← Category.assoc, sn]; exact Category.comp_id _) (fun v => by
      rw [add_zero, en, ← Category.assoc, sn]
      show (ex v ≫ 𝟙 A ^ N).left = _
      rw [MonObj.comp_pow, Category.comp_id])
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at H₁
  have c₁ : C₁ = 1 := by
    have := H₁ 0
    rw [val_pull hJ, sn, e0, o1, val_norm n₀ x cpt hJ, map_mul, nv_zpow, ← zpow_neg_one, nv_zpow, n0, smul_zero] at this
    exact (mul_eq_right₀ (mul_pos (zpow_pos (np 0) _) (zpow_pos (np 0) _)).ne').1 this.symm
  obtain ⟨C₂, hC₂, H₂⟩ := iso ![(snd (Over.mk x) A).left, (Out.translPt A U.pt).left] _ 1 z U.φ U.isGen (by simp)
    (fun v => sn _) (fun v => by
      show (lift (𝟙 _) (ex v) ≫ Out.translPt A U.pt).left = _
      rw [translPt_eq, MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.id_comp, hU, Nat.cast_one, one_smul, hadd,
        mul_comm])
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_one, one_smul] at H₂
  have c₂ : C₂ = 1 := by
    obtain ⟨_, -, sv⟩ := sym_val sl
    have p := congrArg nv (sv (𝟙 (Over.mk x)) (z := cpt) hJ).1
    rw [map_prod, map_one] at p
    have q : ∀ j : ℕ, (𝟙 (Over.mk x) ≫ U.pt) ^ j = ex ((j : ℂ) • z) := fun j => by rw [Category.id_comp, hU, en]
    have q' : ∀ j : ℕ, (j : ℂ) • z + z = ((j + 1 : ℕ) : ℂ) • z := fun j => by rw [Nat.cast_succ, add_smul, one_smul]
    simp only [q, H₂, q'] at p
    have hk : ex (((N ^ 2 : ℕ) : ℂ) • z) = 1 := by rw [en, hz]
    have nk : n (((N ^ 2 : ℕ) : ℂ) • z) = n 0 := by
      rw [hn, hn, hper _ _ hk (by rw [hk, ← e0]; exact ch 0), hk, e0]
    rw [Finset.prod_mul_distrib, tele (fun j => n ((j : ℂ) • z)) (fun _ => np _), nk, Nat.cast_zero, zero_smul,
      zpow_neg, mul_inv_cancel₀ (zpow_pos (np 0) _).ne', _root_.mul_one, Finset.prod_const, Finset.card_range] at p
    exact (pow_eq_one_iff_of_nonneg hC₂.le (pow_ne_zero 2 hN)).1 p
  have mt : (lift (𝟙 _) (ex z)).left ≫ (Out.mulT A (Over.mk x) N).left = (lift (𝟙 _) (ex ((N : ℂ) • z))).left := by
    rw [← Over.comp_left, Out.mulT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd, en]
  have tr : (lift (𝟙 _) (ex 0)).left ≫ (Out.translT A U.pt).left = (lift (𝟙 (Over.mk x)) (ex z)).left := by
    rw [← Over.comp_left, lift_transl, Category.id_comp, hU, e0, _root_.mul_one]
  have w₁ := twist_val ac (lift (𝟙 _) (ex 0)).left cpt hJ
  have w₂ := twist_val tw (lift (𝟙 _) (ex z)).left cpt hJ
  rw [mt, val_corr hJ cα] at w₂
  rw [tr, w₂] at w₁
  have w₃ := (value_val hw (𝟙 _) cpt hJ).symm.trans ((by rw [Category.id_comp, e0]; rfl : _ = _).trans w₁)
  have r₀ := val_rigT L.rig (Over.mk x) ((N : ℤ) ^ 2) (𝟙 _) cpt hJ
  have w₄ := congrArg (fun q => ‖ev q‖) ((congrArg₂ (· * ·) rfl (congrArg Units.val r₀.symm)).trans w₃)
  simp only [map_mul, norm_mul, ← nv_apply] at w₄
  have a₁ : ev (gs (𝟙 (Sp ℂ)) cpt ⊤ (toΓ ℂ w)) = w := (ev_gs (𝟙 (Sp ℂ)) ⊤ trivial _).trans (valAt'_id_top w)
  have a₂ : ‖ev (sval (L := L.L) (φ := fun _ : Fin 1 => (snd (Over.mk x) A).left) (ε := fun _ => 1) s
      (lift (𝟙 _) (ex ((N : ℂ) • z))).left cpt J)‖ = t ((N : ℂ) • z) * n ((N : ℂ) • z) := by
    rw [hn, ← hs _ _ (ch _)]
    refine congrArg norm ((congrArg ev (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd (Over.mk x) A).left)
      (ε := fun _ => 1) s _ cpt J (fun _ => J (ex ((N : ℂ) • z)).left) (fun _ => congrArg J (sn _)))).trans
      (ev_gs _ _ ?_ _))
    have := hJ.mem (fun _ : Fin 1 => (snd (Over.mk x) A).left) (lift (𝟙 _) (ex ((N : ℂ) • z))).left
    simpa only [sn] using this
  have a₃ : nv (val L.rig (𝟙 (Sp ℂ) ≫ x) cpt J ^ (N : ℤ) ^ 2) = n 0 ^ (N : ℤ) ^ 2 := by
    rw [nv_zpow, Category.id_comp, n0]
  have w₅ : ‖w‖ * n 0 ^ (N : ℤ) ^ 2 = C₂ * (n 0 ^ (N : ℤ) ^ 2 * n (0 + z) ^ (-(N : ℤ) ^ 2)) *
      (C₁ * (n z ^ (N : ℤ) ^ 2 * n ((N : ℂ) • z) ^ (-1 : ℤ)) * (t ((N : ℂ) • z) * n ((N : ℂ) • z))) := by
    rw [← H₁, ← H₂, ← a₂, ← a₃, ← a₁]
    exact w₄
  rw [c₁, c₂, zero_add, zpow_neg, zpow_neg_one] at w₅
  have b₁ := (zpow_pos (np 0) ((N : ℤ) ^ 2)).ne'
  have b₂ := (zpow_pos (np z) ((N : ℤ) ^ 2)).ne'
  have b₃ := (np ((N : ℂ) • z)).ne'
  apply mul_right_cancel₀ b₁
  rw [w₅]
  field_simp

end GlobalTheory.NullNorm

namespace GlobalTheory

open NullNorm in

theorem norm_nullVal_eq_norm_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ) (y : FrPt Xo c (CAt σ)), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → y.x = Fu.u i Pm → IsFnOf Fu i Pm fr y.x y.s θ → ∀ (N : ℕ), Odd N → ∀ (p : ptO Xo y.x ⟶ Xo.univ.t.G) (z : Fin g → ℂ) (w : CAt σ), p ^ (N ^ 2) = 1 → p.left = (Fu.ex i Pm z).left → IsNullVal Xo c N y p w → ‖toC w‖ = ‖θ ((N : ℂ) • z)‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm ((N : ℂ) • z) ((N : ℂ) • z)).re) := by
  intro E _ _ _ H Dw l Xo c σ g ty Fu i Pm Hm χl fr θ y hP hA hy hθ N hN p z w hp hpz hw
  obtain ⟨x, y₁, y₂, y₃, y₄, y₅, s, y₆⟩ := y
  dsimp only at hy
  subst hy
  obtain rfl : p = Fu.ex i Pm z := Over.OverMorphism.ext hpz
  obtain ⟨F, hF, hw⟩ := hw
  have hI := GlobalTheory.ConstNorm.norm_gen_eq_const_mul E H Dw l Xo _ g ty Fu i Pm Hm χl fr hP hA (Fin 2)
  obtain ⟨-, -, -, -, hne, -, h0, hper⟩ := hA
  have z₀ : ∀ v, hermForm Hm 0 v = 0 := fun v => by simp [hermForm]
  refine core Xo.univ.t.PP (Fu.u i Pm) (Fu.ex i Pm) (Fu.ex_add i Pm hP)
    (fun j v => ‖fr j v‖ * Real.exp (Real.pi / 2 * (hermForm Hm v v).re))
    (fun j v h => mul_pos (norm_pos_iff.2 (hne j v h)) (Real.exp_pos _)) (fun j h => ?_) (fun j a ha h => ?_) hI
    hN.pos.ne' s (fun v => ‖θ v‖ * Real.exp (-(Real.pi / 2) * (hermForm Hm v v).re)) (fun j v h => ?_) z hp w F hF hw
  · rw [z₀, h0 j h]; simp
  · obtain ⟨b, rfl⟩ := (Fu.ex_ker i Pm hP a).1 ha
    obtain ⟨u, e⟩ := hper b j 0
    rw [e h, z₀, z₀, norm_mul, norm_mul, u, Complex.norm_exp, zero_add]
    have : ((Real.pi : ℂ) * 0 + (Real.pi : ℂ) / 2 * hermForm Hm (Pm b) (Pm b)).re =
        Real.pi / 2 * (hermForm Hm (Pm b) (Pm b)).re := by
      rw [mul_zero, zero_add, ← Complex.re_ofReal_mul]; push_cast; rfl
    rw [this]; simp [mul_comm]
  · have e := hθ j v (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm v)).left
      (congrArg (·.left) (lift_snd (𝟙 _) (Fu.ex i Pm v))) (congrArg (·.left) (lift_fst (𝟙 _) (Fu.ex i Pm v))) h
    refine (congrArg norm e).trans ?_
    rw [norm_mul, _root_.mul_mul_mul_comm, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, _root_.mul_one]

end GlobalTheory
