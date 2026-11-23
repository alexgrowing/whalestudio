import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushHomBijective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.CechPic

namespace GlobalTheory.PrincipalIntegral

section Calc

variable {S : Scheme.{0}} {A : Over S} {n : ℕ}

def pair (π : Pic (A ⊗ A).left) {T : Over S} (x y : T ⟶ A) : Pic T.left := pull (lift x y).left π

def quad (π : Pic (A ⊗ A).left) (W : Matrix (Fin n) (Fin n) ℤ) {T : Over S} (x : Fin n → (T ⟶ A)) : Pic T.left :=
  ∑ uv : Fin n × Fin n, W uv.1 uv.2 • pair π (x uv.1) (x uv.2)

theorem pull_pair (π : Pic (A ⊗ A).left) {T T' : Over S} (g : T' ⟶ T) (x y : T ⟶ A) :
    pull g.left (pair π x y) = pair π (g ≫ x) (g ≫ y) := by
  rw [pair, pair, ← pull_comp, ← Over.comp_left, comp_lift]

theorem pull_quad (π : Pic (A ⊗ A).left) (W : Matrix (Fin n) (Fin n) ℤ) {T T' : Over S} (g : T' ⟶ T)
    (x : Fin n → (T ⟶ A)) : pull g.left (quad π W x) = quad π W (fun u => g ≫ x u) := by
  simp only [quad, map_sum, map_zsmul, pull_pair]

variable [GrpObj A] [IsCommMonObj A] {π : Pic (A ⊗ A).left}
  (hadd : ∀ (T : Over S) (x x' y : T ⟶ A), pair π (x * x') y = pair π x y + pair π x' y)
  (hsym : ∀ (T : Over S) (x y : T ⟶ A), pair π x y = pair π y x)

include hadd in
theorem pair_one {T : Over S} (y : T ⟶ A) : pair π 1 y = 0 := by
  have h := hadd T 1 1 y
  rw [_root_.mul_one] at h
  exact left_eq_add.1 h

include hadd in
theorem pair_zpow {T : Over S} (x y : T ⟶ A) (m : ℤ) : pair π (x ^ m) y = m • pair π x y := by
  simpa using BilinCalc.map_prod_zpow (fun z => pair π z y) (fun a b => hadd T a b y) (fun _ : Fin 1 => x) fun _ => m

include hadd hsym in
theorem quad_mul (W : Matrix (Fin n) (Fin n) ℤ) {T : Over S} (a b : Fin n → (T ⟶ A)) :
    quad π W (fun u => a u * b u) = quad π W a + quad π W b +
      ∑ u, ∑ v, (W + W.transpose) u v • pair π (a u) (b v) := by
  have e : ∀ u v, pair π (a u * b u) (a v * b v) =
      pair π (a u) (a v) + pair π (b u) (b v) + (pair π (a u) (b v) + pair π (a v) (b u)) := fun u v => by
    rw [hadd, hsym T (a u), hsym T (b u), hadd, hadd, hsym T (a v) (a u), hsym T (b v) (a u), hsym T (b v) (b u)]
    abel
  simp only [quad, e, smul_add, Finset.sum_add_distrib, Matrix.add_apply, add_smul, Matrix.transpose_apply,
    Fintype.sum_prod_type]
  congr 2
  exact Finset.sum_comm

include hadd hsym in
theorem quad_inv (W : Matrix (Fin n) (Fin n) ℤ) {T : Over S} (a : Fin n → (T ⟶ A)) :
    quad π W (fun u => (a u)⁻¹) = quad π W a := by
  have e : ∀ x y : T ⟶ A, pair π x⁻¹ y = -pair π x y := fun x y => by
    simpa using pair_zpow hadd x y (-1)
  simp only [quad]
  refine Finset.sum_congr rfl fun uv _ => ?_
  rw [e, hsym, e, neg_neg, hsym]

variable {G : Over S} [GrpObj G] {pr : Fin n → (G ⟶ A)} (hmon : ∀ u, IsMonHom (pr u))
  (huniv : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u)
  {W : Matrix (Fin n) (Fin n) ℤ} {L : LB G.left} (hL : L.IsLB) (hLW : cls L hL = quad π W pr)

include hadd hsym hmon hLW in
theorem pull_translDiff {T T' : Over S} (x : T ⟶ G) (j : T' ⟶ T) (b : T' ⟶ G) (h : (Out.translDiff G L x).IsLB) :
    pull (lift j b).left (cls _ h) = quad π W (fun u => j ≫ x ≫ pr u) +
      ∑ u, ∑ v, (W + W.transpose) u v • pair π (j ≫ x ≫ pr u) (b ≫ pr v) := by
  unfold Out.translDiff at h ⊢
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, hLW, pull_quad, map_add, map_neg]
  have e : ∀ u, lift j b ≫ (lift (fst T G ≫ x) (snd T G) ≫ μ[G]) ≫ pr u = (j ≫ x ≫ pr u) * (b ≫ pr u) := fun u => by
    have := hmon u
    rw [← Hom.mul_def, MonObj.mul_comp, MonObj.comp_mul, Category.assoc, lift_fst_assoc, lift_snd_assoc]
  simp only [e, lift_snd_assoc, quad_mul hadd hsym]
  abel

include hadd hLW hmon in
theorem rigidified : Out.Rigidified G L := by
  refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
  rw [cls_pull hL, hLW]
  refine (pull_quad π W η[G] pr).trans (Finset.sum_eq_zero fun uv _ => ?_)
  have := hmon uv.1
  have e : η[G] ≫ pr uv.1 = 1 := by simp [Hom.one_def]
  beta_reduce
  rw [e, pair_one hadd, smul_zero]

include hadd hsym hLW hmon in
theorem sym : Out.Sym G L := fun _ => ⟨⊤, trivial, by
  refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, hLW, pull_comp, pull_quad]
  have e : ∀ u, (GrpObj.inv : G ⟶ G) ≫ pr u = (pr u)⁻¹ := fun u => by
    have := hmon u
    have h := GrpObj.inv_comp (𝟙 G) (pr u)
    simpa [Hom.inv_def] using h
  simp only [e, quad_inv hadd hsym, add_neg_cancel]⟩

include hadd hsym hLW hmon huniv in

theorem kTriv_of_kernel (hdet : (W + W.transpose).det = 1)
    (hker : ∀ (T : Over S) (x : T ⟶ A), pair π (snd A T ≫ x) (fst A T) = 0 → x = 1) : Out.KTriv G L := by
  intro R _ t x hx
  have hd : (Out.translDiff G L x).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨z, -, hz⟩ := huniv (Over.mk t) fun _ => 1
  refine (hz x fun u₀ => ?_).trans (hz (1 : Over.mk t ⟶ G) fun u => ?_).symm
  swap
  · have := hmon u
    exact MonObj.one_comp _
  choose V hV c hc using hx
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext
    ((Spec (CommRingCat.of R)).openCoverOfIsOpenCover V
      (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hV p⟩)) _ _ fun p => ?_)
  let T' : Over S := Over.mk ((V p).ι ≫ t)
  let j : T' ⟶ Over.mk t := Over.homMk (V p).ι rfl
  have key : ∀ w : Fin n → ℤ, quad π W (fun u => (snd A T' ≫ j) ≫ x ≫ pr u) +
      ∑ u, ((W + W.transpose).mulVec w) u • pair π ((snd A T' ≫ j) ≫ x ≫ pr u) (fst A T') = 0 := fun w => by
    obtain ⟨b, hb, -⟩ := huniv (A ⊗ T') fun v => fst A T' ^ w v
    have h := pull_translDiff hadd hsym hmon hL hLW x (snd A T' ≫ j) b hd
    have k : (lift (snd A T' ≫ j) b).left ≫ (fst (Over.mk t) G).left = (snd A T').left ≫ (V p).ι :=
      congrArg (fun q => q.left) (lift_fst (snd A T' ≫ j) b)
    obtain ⟨m, hm⟩ : ∃ m : (A ⊗ T').left ⟶ ((fst (Over.mk t) G).left ⁻¹ᵁ V p).toScheme,
        m ≫ ((fst (Over.mk t) G).left ⁻¹ᵁ V p).ι = (lift (snd A T' ≫ j) b).left :=
      ⟨IsOpenImmersion.lift _ (lift (snd A T' ≫ j) b).left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ V p) k).mpr ((snd A T').left y).2), IsOpenImmersion.lift_fac _ _ _⟩
    have h0 := (cls_eq_zero_iff (pull_isLB hd _)).2 ⟨c p, hc p⟩
    rw [cls_pull hd] at h0
    rw [← hm, pull_comp, h0, map_zero] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hb, hsym _ _ (fst A T' ^ w v), pair_zpow hadd, hsym _ (fst A T'), mul_smul]
  have k₀ := key 0
  have k₁ := key ((W + W.transpose).adjugate.mulVec (Pi.single u₀ 1))
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec] at k₁
  simp only [Matrix.mulVec_zero, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at k₀
  rw [k₀, zero_add, Finset.sum_eq_single u₀ (fun v _ hv => by rw [Pi.single_eq_of_ne hv, zero_smul]) (by simp),
    Pi.single_eq_same, one_smul, Category.assoc] at k₁
  have e : j ≫ x ≫ pr u₀ = j ≫ 1 := (hker T' _ k₁).trans (MonObj.comp_one j).symm
  exact congrArg (fun q => q.left) e

include hadd hsym hLW hmon huniv in

theorem kernel_of_kTriv (u₀ : Fin n) (hK : Out.KTriv G L) (T : Over S) (x : T ⟶ A)
    (hx : pair π (snd A T ≫ x) (fst A T) = 0) : x = 1 := by
  refine Over.OverMorphism.ext (Scheme.Cover.hom_ext T.left.affineOpenCover.openCover _ _ fun i => ?_)
  let R : CommRingCat := T.left.affineOpenCover.X i
  let f : Spec (CommRingCat.of R) ⟶ T.left := T.left.affineOpenCover.f i
  let T' : Over S := Over.mk (f ≫ T.hom)
  let j : T' ⟶ T := Over.homMk f rfl
  obtain ⟨y, hy, -⟩ := huniv T' fun u => if u = u₀ then j ≫ x else 1
  have hz : ∀ (Z : Over S) (a : Z ⟶ T') (z : Z ⟶ A) u, pair π (a ≫ y ≫ pr u) z = 0 := fun Z a z u => by
    rw [hy]
    split_ifs
    · have h := congrArg (pull (lift z (a ≫ j)).left) hx
      rwa [pull_pair, map_zero, lift_snd_assoc, lift_fst, Category.assoc] at h
    · rw [MonObj.comp_one, pair_one hadd]
  have hd : (Out.translDiff G L y).IsLB := LB.isLB_linComb hL _ _
  have h1 : y = 1 := hK R (f ≫ T.hom) y fun p => ⟨⊤, trivial, by
    refine (cls_eq_zero_iff (pull_isLB hd _)).1 ?_
    have h := pull_translDiff hadd hsym hmon hL hLW y (fst T' G) (snd T' G) hd
    simp only [quad, hz, smul_zero, Finset.sum_const_zero, add_zero, lift_fst_snd, Over.id_left] at h
    rw [pull_id] at h
    rw [cls_pull hd]
    exact (congrArg _ h).trans (map_zero _)⟩
  have := hmon u₀
  have e : j ≫ x = j ≫ 1 := by
    have h := hy u₀
    rw [if_pos rfl, h1, MonObj.one_comp] at h
    rw [← h, MonObj.comp_one]
  exact congrArg (fun q => q.left) e

end Calc

section Siegel

variable {h k : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B} (c : SiegPre h k ζ s)

theorem pair_mul (hG : Out.GlobalFnsSt) (hA : Out.RelAmple c.A c.diag) (T : Over S) (x x' y : T ⟶ c.A) :
    pair (cls c.P c.isLB) (x * x') y = pair (cls c.P c.isLB) x y + pair (cls c.P c.isLB) x' y := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb c.isLB _ _)).2 (Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab
    (pull_isLB c.isLB _) hA c.P c.isLB c.rig₁ c.rig₂ T x x' y).1
  rw [cls_linComb c.isLB, Fin.sum_univ_three] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
  rw [← sub_eq_zero, ← e]
  unfold pair
  abel

theorem pair_comm (T : Over S) (x y : T ⟶ c.A) : pair (cls c.P c.isLB) x y = pair (cls c.P c.isLB) y x := by
  have e : cls c.P c.isLB = pull (lift (snd c.A c.A) (fst c.A c.A)).left (cls c.P c.isLB) :=
    (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
  have k : (lift y x).left ≫ (lift (snd c.A c.A) (fst c.A c.A)).left = (lift x y).left := by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
  unfold pair
  rw [← k, pull_comp, ← e]

end Siegel

theorem principal_of_generic_of_ample_special : Out.Laws → Out.Laws2 → ∀ (h k : ℕ), Odd k → 3 ≤ k → ∀ (B : Type) [CommRing B] (ζ : B) (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsLocalRing O] [Algebra O C], IsUnitBall O C → ∀ p : ℕ, p.Prime → ‖(p : C)‖ < 1 → ∀ (β : B →+* O) (c : SiegPre h k ζ (spMap β)), (∃ c' : SiegPre h k ζ (spMap (algebraMap O C) ≫ spMap β), SiegPB c' c (spMap (algebraMap O C)) ∧ c'.Principal) → Out.RelAmple (Over.mk (pullback.snd c.A.hom (spMap (IsLocalRing.residue O)))) (c.diag.pull (pullback.fst c.A.hom (spMap (IsLocalRing.residue O)))) → c.Principal := by
  intro hl _ h k _ _ B _ ζ C O _ _ _ _ _ _ _ _ hO p hp hpn β c ⟨c', ⟨φ, φ₂, hφ, hsq, hw, _⟩, hA', hK'⟩ hsp
  obtain ⟨_, hv, hdim, hfr⟩ := UnitBallVal.main C O hO
  let f := spMap (algebraMap O C)
  have hP : cls c'.P c'.isLB = pull φ₂ (cls c.P c.isLB) := (cls_eq_iff _ (pull_isLB c.isLB _)).2 hw
  have hpair : ∀ {T : Over (Sp O)} {T' : Over (Sp C)} (u : T'.left ⟶ T.left) (a b : T ⟶ c.A) (a' b' : T' ⟶ c'.A),
      a'.left ≫ φ = u ≫ a.left → b'.left ≫ φ = u ≫ b.left →
      pair (cls c'.P c'.isLB) a' b' = pull u (pair (cls c.P c.isLB) a b) := fun u a b a' b' ha hb => by
    rw [pair, pair, hP, ← pull_comp, ← pull_comp, SiegelDescent.lift_comp_square hsq u a b a' b' ha hb]
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hD' : c'.diag.IsLB := pull_isLB c'.isLB _
  have hA : Out.RelAmple c.A c.diag := by
    refine FibreAmple.relAmple_of_fibres hl O C c.A c.ab c.diag hD ?_ hsp
    let e := hφ.1.isoPullback.inv
    have he : IsPullback e (pullback.snd c.A.hom f) c'.A.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact hφ.1.isoPullback_inv_snd⟩
    have hd : cls c'.diag hD' = pull φ (cls c.diag hD) :=
      hpair φ (𝟙 c.A) (𝟙 c.A) (𝟙 c'.A) (𝟙 c'.A) (by simp) (by simp)
    obtain ⟨w, hw⟩ : LBIso (c.diag.pull (pullback.fst c.A.hom f)) (c'.diag.pull e) := by
      refine (cls_eq_iff (pull_isLB hD _) (pull_isLB hD' _)).1 ?_
      rw [cls_pull hD, cls_pull hD', hd, ← pull_comp, hφ.1.isoPullback_inv_fst]
    exact relAmple_pull (A' := Over.mk (pullback.snd c.A.hom f)) he hD' (pull_isLB hD _) ((isGen_iff w).1 hw) ⊤
      (isAffineOpen_top _) (fun _ => trivial) hA'
  refine ⟨hA, fun T x hx => ?_⟩
  obtain ⟨hpos, hdet⟩ := isE8_W8
  let G := Out.powObj c.A 8
  let pr : Fin 8 → (G ⟶ c.A) := Out.powPr c.A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over (Sp O)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hG : IsAbelianScheme G := AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 7
  let G' := (Over.pullback f).obj G
  let ψ : G'.left ⟶ G.left := Pdiv.PullbackComparison.pφ f G
  have hψ : IsGrpPullback G' G f ψ := Pdiv.PullbackComparison.isGrpPullback f G
  choose pr' hpr using fun u => SharpPull.exists_lift hψ hφ (pr u)
  have hmon' : ∀ u, IsMonHom (pr' u) := fun u => SharpPull.isMonHom_lift hψ hφ (hpr u)
  have huniv' : ∀ (T : Over (Sp C)) (y : Fin 8 → (T ⟶ c'.A)), ∃! x : T ⟶ G', ∀ u, x ≫ pr' u = y u := fun T y => by
    obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hφ T (y u))
    obtain ⟨x, rfl⟩ := SharpPull.push_surj hψ x₀
    refine ⟨x, fun u => SharpPull.push_inj hφ ?_, fun x' hx' => SharpPull.push_inj hψ (hu _ fun u => ?_)⟩
    · rw [SharpPull.push_comp hψ hφ (hpr u), hx₀ u]
    · rw [← SharpPull.push_comp hψ hφ (hpr u), hx' u]
  let L := LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) fun uv => W8 uv.1 uv.2
  let L' := LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr' uv.1) (pr' uv.2)).left) fun uv => W8 uv.1 uv.2
  have hL : L.IsLB := LB.isLB_linComb c.isLB _ _
  have hL' : L'.IsLB := LB.isLB_linComb c'.isLB _ _
  have hLW : cls L hL = quad (cls c.P c.isLB) W8 pr := cls_linComb c.isLB _ _ _
  have hLW' : cls L' hL' = quad (cls c'.P c'.isLB) W8 pr' := cls_linComb c'.isLB _ _ _
  have hiso : LBIso L' (L.pull ψ) := by
    refine (cls_eq_iff hL' (pull_isLB hL _)).1 ?_
    rw [cls_pull hL, hLW, hLW', quad, quad, map_sum]
    exact Finset.sum_congr rfl fun uv _ => by rw [map_zsmul, hpair ψ _ _ _ _ (hpr uv.1) (hpr uv.2)]
  have := hG.smooth
  have := hG.geomConnected
  have := LocalFibre.connectedSpace_sp O
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom (eSec G (IsLocalRing.closedPoint O))
  have hadd := pair_mul c hl.globalFns hA
  have hadd' := pair_mul c' hl.globalFns hA'
  let Q : Out.PolAV (Sp C) :=
    { A := G', g := g, L := L', isLB := hL'
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hψ.1 hg
      isAb := ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) hψ.1 hG.smooth,
        MorphismProperty.of_isPullback (P := @IsProper) hψ.1 hG.proper,
        MorphismProperty.of_isPullback (P := @GeometricallyConnected) hψ.1 hG.geomConnected⟩
      rigid := rigidified hadd' hmon' hL' hLW'
      sym := sym hadd' (pair_comm c') hmon' hL' hLW'
      ample := PosDefAmple.relAmple_linComb_of_posDef hl.globalFns h k 8 B ζ _ _ c' G' pr' W8 hmon' huniv' hA' hpos
      ktriv := kTriv_of_kernel hadd' (pair_comm c') hmon' huniv' hL' hLW' hdet fun T x hx =>
        hK' T x ((cls_eq_zero_iff (pull_isLB c'.isLB _)).1 hx) }
  have hq : ∀ q : Ideal O, q.IsPrime → q ≠ ⊥ → ∃ p : ℕ, p.Prime ∧ (p : O) ∈ q := fun q hq h0 => by
    refine ⟨p, hp, ?_⟩
    rw [IsLocalRing.eq_maximalIdeal (hq.isMaximal h0), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have h1 : (p : C) * algebraMap O C v = 1 := by simpa using congrArg (algebraMap O C) hv
    have h2 : ‖algebraMap O C v‖ ≤ 1 := (hO.2 _).1 ⟨v, rfl⟩
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hpn h2).ne h3
  have hK : Out.KTriv G L := GenericKTriv.kTriv_of_generic hl O C hO.1 hq G hG g hg L hL (rigidified hadd hmon hL hLW)
    (PosDefAmple.relAmple_linComb_of_posDef hl.globalFns h k 8 B ζ _ _ c G pr W8 hmon huniv hA hpos) Q ψ hψ hiso
  have hx' : pair (cls c.P c.isLB) (snd c.A T ≫ x) (fst c.A T) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 hx
  exact kernel_of_kTriv (n := 8) (G := G) hadd (pair_comm c) hmon huniv hL hLW (0 : Fin 8) hK T x hx'

end GlobalTheory.PrincipalIntegral
