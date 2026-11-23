import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlEmbed

section Alg

variable {A k : Type} [CommRing A] [Field k] {m : Type} [Fintype m] [DecidableEq m]

theorem cT_add' (c : A →+* A) (X Y : Matrix m m A) : Formalism.UG.cT c (X + Y) = Formalism.UG.cT c X + Formalism.UG.cT c Y := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_smul' (c : A →+* A) (a : A) (X : Matrix m m A) : Formalism.UG.cT c (a • X) = c a • Formalism.UG.cT c X := by
  ext i j; simp [Formalism.UG.cT]

theorem smul_mul_smul' (a b : A) (P Q : Matrix m m A) : (a • P) * (b • Q) = (a * b) • (P * Q) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem blk_mul (e f u : A) (hef : e * f = 0) (hue : u * e = 0) (huf : u * f = 0) (huu : u * u = u)
    {X1 Y1 X2 Y2 M : Matrix m m A} (h1 : e • X1 = X1) (h2 : f • Y1 = Y1) (h3 : e • X2 = X2) (h4 : f • Y2 = Y2) :
    (X1 + Y1 + u • M) * (X2 + Y2 + u • 1) = X1 * X2 + Y1 * Y2 + u • M := by
  have hfe : f * e = 0 := by rw [mul_comm, hef]
  have a1 : X1 * Y2 = 0 := by rw [← h1, ← h4, smul_mul_smul', hef, zero_smul]
  have a2 : X1 * (u • 1) = 0 := by rw [← h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, hue, zero_smul]
  have a3 : Y1 * X2 = 0 := by rw [← h2, ← h3, smul_mul_smul', hfe, zero_smul]
  have a4 : Y1 * (u • 1) = 0 := by rw [← h2, Matrix.mul_smul, Matrix.mul_one, smul_smul, huf, zero_smul]
  have a5 : (u • M) * X2 = 0 := by rw [← h3, smul_mul_smul', hue, zero_smul]
  have a6 : (u • M) * Y2 = 0 := by rw [← h4, smul_mul_smul', huf, zero_smul]
  have a7 : (u • M) * (u • 1) = u • M := by rw [smul_mul_smul', huu, Matrix.mul_one]
  simp only [add_mul, mul_add, a1, a2, a3, a4, a5, a6, a7, add_zero, zero_add]

variable (c : A →+* A) (e : A) (pr : A →+* k) (sec : k →+ A)

theorem sec_eq (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (a : k) : e * sec a = sec a := by
  rw [← sec_pr, pr_sec]

theorem sec_mul (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (a b : k) :
    sec (a * b) = sec a * sec b := by
  calc sec (a * b) = sec (pr (sec a * sec b)) := by rw [map_mul pr, pr_sec, pr_sec]
    _ = e * (sec a * sec b) := sec_pr _
    _ = sec a * sec b := by rw [← mul_assoc, sec_eq e pr sec pr_sec sec_pr]

theorem secM_mul (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (Z W : Matrix m m k) :
    (Z * W).map sec = Z.map sec * W.map sec := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, sec_mul e pr sec pr_sec sec_pr]

theorem secM_one (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) :
    (1 : Matrix m m k).map sec = e • (1 : Matrix m m A) := by
  have h1 : sec 1 = e := by rw [← map_one pr, sec_pr, mul_one]
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply, h1]
  · simp [Matrix.one_apply, h]

theorem secM_supp (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x) (Z : Matrix m m k) :
    e • Z.map sec = Z.map sec := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, sec_eq e pr sec pr_sec sec_pr]

end Alg

end GlobalTheory.GlEmbed

namespace GlobalTheory.GlEmbed

section Phi

variable {A k : Type} [CommRing A] [Field k] {m : Type} [Fintype m] [DecidableEq m]
variable (c : A →+* A) (e : A) (pr : A →+* k) (sec : k →+ A) (J Ji : Matrix m m A)

def phi (G Gi : Matrix m m k) : Matrix m m A :=
  G.map sec + Formalism.UG.cT c (J * Gi.map sec * Ji) + (1 - e - c e) • (1 : Matrix m m A)

theorem cT_cT' (hcc : ∀ x, c (c x) = x) (X : Matrix m m A) : Formalism.UG.cT c (Formalism.UG.cT c X) = X := by
  ext i j; simp [Formalism.UG.cT, hcc]

theorem cT_three (hh : Formalism.UG.cT c J = J) (P Q : Matrix m m A) :
    Formalism.UG.cT c P * J * Formalism.UG.cT c Q = Formalism.UG.cT c (Q * J * P) := by
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hh, Matrix.mul_assoc]

variable (he : e * e = e) (hef : e * c e = 0) (pr_sec : ∀ a, pr (sec a) = a) (sec_pr : ∀ x, sec (pr x) = e * x)
include he hef pr_sec sec_pr

theorem hQ (G : Matrix m m k) : e • (J * G.map sec * Ji) = J * G.map sec * Ji := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, secM_supp e pr sec pr_sec sec_pr]

theorem hY (G : Matrix m m k) : c e • Formalism.UG.cT c (J * G.map sec * Ji) = Formalism.UG.cT c (J * G.map sec * Ji) := by
  rw [← cT_smul', hQ c e pr sec J Ji he hef pr_sec sec_pr]

theorem scal : c e * c e = c e ∧ (1 - e - c e) * e = 0 ∧ (1 - e - c e) * c e = 0 ∧
    (1 - e - c e) * (1 - e - c e) = 1 - e - c e := by
  have hff : c e * c e = c e := by rw [← map_mul, he]
  have hue : (1 - e - c e) * e = 0 := by rw [sub_mul, sub_mul, one_mul, he, mul_comm (c e) e, hef]; ring
  have huf : (1 - e - c e) * c e = 0 := by rw [sub_mul, sub_mul, one_mul, hef, hff]; ring
  refine ⟨hff, hue, huf, ?_⟩
  calc (1 - e - c e) * (1 - e - c e) = (1 - e - c e) - (1 - e - c e) * e - (1 - e - c e) * c e := by ring
    _ = 1 - e - c e := by rw [hue, huf]; ring

theorem phi_mul (hJ : Ji * J = 1) (G Gi G' Gi' : Matrix m m k) :
    phi c e sec J Ji G Gi * phi c e sec J Ji G' Gi' = phi c e sec J Ji (G * G') (Gi' * Gi) := by
  obtain ⟨-, hue, huf, huu⟩ := scal c e pr sec he hef pr_sec sec_pr
  unfold phi
  rw [blk_mul e (c e) _ hef hue huf huu (secM_supp e pr sec pr_sec sec_pr G) (hY c e pr sec J Ji he hef pr_sec sec_pr Gi)
    (secM_supp e pr sec pr_sec sec_pr G') (hY c e pr sec J Ji he hef pr_sec sec_pr Gi'),
    secM_mul e pr sec pr_sec sec_pr G G', secM_mul e pr sec pr_sec sec_pr Gi' Gi, ← Formalism.UG.cT_mul]
  congr 3
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Ji J, hJ, Matrix.one_mul]

theorem phi_one (hJ : Ji * J = 1) : phi c e sec J Ji 1 1 = 1 := by
  have hJ' : J * Ji = 1 := mul_eq_one_comm.1 hJ
  unfold phi
  rw [secM_one e pr sec pr_sec sec_pr, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hJ', cT_smul', Formalism.UG.cT_one,
    ← add_smul, ← add_smul]
  have : e + c e + (1 - e - c e) = 1 := by ring
  rw [this, one_smul]

theorem phi_unitary (hcc : ∀ x, c (c x) = x) (hJ : Ji * J = 1) (hh : Formalism.UG.cT c J = J) (G Gi : Matrix m m k)
    (hG : Gi * G = 1) :
    Formalism.UG.cT c (phi c e sec J Ji G Gi) * J * phi c e sec J Ji G Gi = J := by
  obtain ⟨-, hue, huf, huu⟩ := scal c e pr sec he hef pr_sec sec_pr
  have hcu : c (1 - e - c e) = 1 - e - c e := by rw [map_sub, map_sub, map_one, hcc]; ring
  set S := G.map sec with hSdef
  set Q := J * Gi.map sec * Ji with hQdef
  have hS : e • S = S := secM_supp e pr sec pr_sec sec_pr G
  have hQ' : e • Q = Q := hQ c e pr sec J Ji he hef pr_sec sec_pr Gi
  have hL : c e • Formalism.UG.cT c S = Formalism.UG.cT c S := by rw [← cT_smul', hS]
  have h1 : Formalism.UG.cT c (phi c e sec J Ji G Gi) * J = Q * J + Formalism.UG.cT c S * J + (1 - e - c e) • J := by
    unfold phi
    rw [← hSdef, ← hQdef, cT_add', cT_add', cT_smul', Formalism.UG.cT_one, cT_cT' c hcc, hcu]
    simp only [add_mul, Matrix.smul_mul, Matrix.one_mul]
    abel
  have hQJ : e • (Q * J) = Q * J := by rw [← Matrix.smul_mul, hQ']
  have hLJ : c e • (Formalism.UG.cT c S * J) = Formalism.UG.cT c S * J := by rw [← Matrix.smul_mul, hL]
  rw [h1]
  unfold phi
  rw [← hSdef, ← hQdef, blk_mul e (c e) _ hef hue huf huu hQJ hLJ hS (hY c e pr sec J Ji he hef pr_sec sec_pr Gi)]
  have h2 : Q * J * S = e • J := by
    rw [hQdef, hSdef]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ji J, hJ, Matrix.one_mul, ← secM_mul e pr sec pr_sec sec_pr, hG,
      secM_one e pr sec pr_sec sec_pr, Matrix.mul_smul, Matrix.mul_one]
  have h3 : Formalism.UG.cT c S * J * Formalism.UG.cT c Q = c e • J := by
    rw [cT_three c J hh, h2, cT_smul', hh]
  rw [h2, h3, ← add_smul, ← add_smul]
  have : e + c e + (1 - e - c e) = 1 := by ring
  rw [this, one_smul]

theorem phi_map (G Gi : Matrix m m k) : (phi c e sec J Ji G Gi).map pr = G := by
  obtain ⟨-, hue, huf, huu⟩ := scal c e pr sec he hef pr_sec sec_pr
  have hpe : pr e = 1 := by
    have h1 : sec 1 = e := by rw [← map_one pr, sec_pr, mul_one]
    rw [← h1, pr_sec]
  have hpf : pr (c e) = 0 := by
    have := congrArg pr hef
    rwa [map_mul, map_zero, hpe, one_mul] at this
  have hpu : pr (1 - e - c e) = 0 := by rw [map_sub, map_sub, map_one, hpe, hpf]; ring
  have hYe := hY c e pr sec J Ji he hef pr_sec sec_pr Gi
  ext i j
  have hij : Formalism.UG.cT c (J * Gi.map sec * Ji) i j = c e * Formalism.UG.cT c (J * Gi.map sec * Ji) i j := by
    conv_lhs => rw [← hYe]
    rfl
  unfold phi
  rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, map_add, map_add, hij, Matrix.smul_apply, smul_eq_mul,
    map_mul, map_mul, hpf, hpu, Matrix.map_apply, pr_sec]
  ring

theorem phi_supp (G Gi : Matrix m m k) :
    (e + c e) • (phi c e sec J Ji G Gi - 1) = phi c e sec J Ji G Gi - 1 := by
  obtain ⟨hff, -, -, -⟩ := scal c e pr sec he hef pr_sec sec_pr
  have hS := secM_supp e pr sec pr_sec sec_pr G
  have hYe := hY c e pr sec J Ji he hef pr_sec sec_pr Gi
  ext i j
  have hs : e * G.map sec i j = G.map sec i j := by
    conv_rhs => rw [← hS]
    rfl
  have hy : c e * Formalism.UG.cT c (J * Gi.map sec * Ji) i j = Formalism.UG.cT c (J * Gi.map sec * Ji) i j := by
    conv_rhs => rw [← hYe]
    rfl
  unfold phi
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
  linear_combination (1 - c e) * hs + (1 - e) * hy +
    (G.map sec i j + Formalism.UG.cT c (J * Gi.map sec * Ji) i j - 2 * (1 : Matrix m m A) i j) * hef -
    (1 : Matrix m m A) i j * he - (1 : Matrix m m A) i j * hff

end Phi

end GlobalTheory.GlEmbed

namespace GlobalTheory.GlEmbed

variable {D : D7}

theorem cT_JR (S : HSp D) : Formalism.UG.cT (cA D) (S.gram.map (incA D)) = S.gram.map (incA D) := by
  ext i j
  have hh : D.sp.cm.sig (S.gram j i) = S.gram i j := S.herm.eq (S.frame j) (S.frame i)
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [← hh]
  simp [cA, sigR, inclR, incA]

theorem JR_inv_mul (S : HSp D) (h : IsUnit S.gram.det) :
    (S.gram⁻¹).map (incA D) * S.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_gl (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k)
    (b' : Matrix n (Fin S.rank) k) : b * b' = 1 → b' * b = 1 →
    ∃ gl : GL n k →* GA D S, (∀ g, SuppAt p.e S (gl g)) ∧ ∀ g, (mt S (gl g)).map p.pr = b * g.val * b' := by
  intro bb' b'b
  obtain ⟨he, hef, -⟩ := p.split
  set J := S.gram.map (incA D) with hJdef
  set Ji := (S.gram⁻¹).map (incA D) with hJidef
  have hJ : Ji * J = 1 := JR_inv_mul S (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S)
  have hh : Formalism.UG.cT (cA D) J = J := cT_JR S
  have hcc : ∀ x, cA D (cA D x) = x := Formalism.L2.Theta.cA_cA
  have Gmul : ∀ g h : Matrix n n k, b * g * b' * (b * h * b') = b * (g * h) * b' := fun g h => by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b' b, b'b, Matrix.one_mul]
  let Φ : GL n k →* Matrix (Fin S.rank) (Fin S.rank) (AE D) :=
    { toFun := fun g => phi (cA D) p.e p.sec J Ji (b * g.val * b') (b * (g⁻¹).val * b')
      map_one' := by
        simp only [inv_one, Units.val_one, Matrix.mul_one, bb']
        exact phi_one (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr hJ
      map_mul' := fun g h => by
        rw [phi_mul (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr hJ, Gmul, Gmul, mul_inv_rev, Units.val_mul,
          Units.val_mul] }
  have hmem : ∀ g, Φ.toHomUnits g ∈ HR (AF D.host.F) D.sp.cm.sig S.gram := fun g => by
    show Formalism.UG.cT (cA D) (Φ g) * J * Φ g = J
    refine phi_unitary (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr hcc hJ hh _ _ ?_
    rw [Gmul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one, bb']
  refine ⟨Φ.toHomUnits.codRestrict _ hmem, fun g => ?_, fun g => ?_⟩
  · intro i j
    have h := phi_supp (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr (b * g.val * b') (b * (g⁻¹).val * b')
    exact congrFun (congrFun h i) j
  · exact phi_map (cA D) p.e p.pr p.sec J Ji he hef p.pr_sec p.sec_pr _ _

end GlobalTheory.GlEmbed
