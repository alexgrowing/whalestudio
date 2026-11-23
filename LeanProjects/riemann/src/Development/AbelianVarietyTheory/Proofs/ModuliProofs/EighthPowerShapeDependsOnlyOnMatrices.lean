import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDefStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpShape
open GlobalTheory.CechPic GlobalTheory.ClassMin

theorem posDef_of_int {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hs : B.transpose = B)
    (hp : ∀ u : Fin n → ℤ, u ≠ 0 → 0 < dotProduct u (B.mulVec u)) : (B.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hβ : ∀ x y, Matrix.toBilin' B x y = Matrix.toBilin' B y x := fun x y => by
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs,
      dotProduct_comm]
  have h := realExtension_ofIntBilin_posDef hβ fun x hx => by
    rw [Matrix.toBilin'_apply']; exact hp x hx
  rw [realExtension_posDef_iff _ (Pi.basisFun ℤ (Fin n))] at h
  convert h using 1
  ext i j
  rw [gram_apply, polar_ofIntBilin hβ]
  simp

theorem exists_affine_of_nonpos {X Y Z : Scheme.{0}} (hF : IsField Γ(Y, ⊤)) (y : Y) (f : Y ⟶ X) (e : Y ⟶ Z)
    {M : LB X} {D : LB Z} (hM : IsAmpleLB M) (hD : IsAmpleLB D) (m : ℕ)
    (h : pull f (cls M hM.isLB) + m • pull e (cls D hD.isLB) = 0) :
    ∃ V : X.Opens, IsAffineOpen V ∧ f ⁻¹ᵁ V = ⊤ := by
  obtain ⟨n, hn, hg⟩ := hD.exists_isGenerated_pow
  obtain ⟨N, hN, s, hs, ha⟩ := hM.exists_affine (f y)
  refine ⟨_, ha, ?_⟩
  have hG := (hg.pull e).pow (N * m)
  obtain ⟨τ, hτ⟩ := hG.exists_mem y
  have hA : (lbPow (M.pull f) (N * n)).IsLB := isLB_lbPow (pull_isLB hM.isLB f) _
  have hs' : Out.nonzeroLocus (secPowPull (secPow s n) f) = f ⁻¹ᵁ Out.nonzeroLocus s := by
    rw [nonzeroLocus_secPowPull, nonzeroLocus_secPow _ hn]
  have hdiv := LB.isLB_div (LB.isLB_triv Y) hA
  have iso : LBIso (LB.div (LB.triv Y) (lbPow (M.pull f) (N * n))) (lbPow ((lbPow D n).pull e) (N * m)) := by
    rw [← cls_eq_iff hdiv hG.isLB, cls_div (LB.isLB_triv Y) hA, cls_lbPow (pull_isLB hM.isLB f),
      cls_lbPow (hg.pull e).isLB, cls_pull hM.isLB, cls_pull hg.isLB, cls_lbPow hD.isLB, map_nsmul,
      eq_neg_of_add_eq_zero_left h]
    show (0 : Pic Y) - _ = _
    rw [zero_sub, smul_neg, neg_neg, smul_smul, smul_smul]
    congr 1
    ring
  obtain ⟨τ', hτ'⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hdiv hG.isLB iso τ
  obtain ⟨u, hu⟩ := exists_sec_nonzeroLocus_eq_inf_div hA (LB.isLB_triv Y) τ' (secPowPull (secPow s n) f)
  rw [hτ', hs'] at hu
  have e₁ : Out.nonzeroLocus u = Y.basicOpen (U := ⊤) (u.f PUnit.unit) :=
    (inf_top_eq _).symm.trans (nonzeroLocus_inf_chart u PUnit.unit)
  have hy : y ∈ Y.basicOpen (U := ⊤) (u.f PUnit.unit) := e₁.le (hu.ge ⟨hτ, hs⟩)
  have h0 : (u.f PUnit.unit : Γ(Y, ⊤)) ≠ 0 := fun h0 => by
    rw [h0] at hy
    exact (Y.basicOpen_zero ⊤).le hy
  obtain ⟨d, hd⟩ := hF.mul_inv_cancel h0
  have ht : Y.basicOpen (U := ⊤) (u.f PUnit.unit) = ⊤ := Y.basicOpen_of_isUnit (IsUnit.of_mul_eq_one d hd)
  exact top_le_iff.1 ((e₁.trans ht).ge.trans (hu.le.trans inf_le_right))

theorem eq_comp_of_affine {X Y B : Scheme.{0}} (π : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ π = 𝟙 B)
    (hπ : Function.Bijective π.appTop.hom) (f : Y ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) (h : f ⁻¹ᵁ V = ⊤) :
    f = π ≫ e ≫ f := by
  obtain ⟨f', rfl⟩ : ∃ f' : Y ⟶ V.toScheme, f' ≫ V.ι = f :=
    ⟨IsOpenImmersion.lift V.ι f (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact h.ge (Set.mem_univ y)), IsOpenImmersion.lift_fac _ _ _⟩
  have : IsAffine V := hV
  have : IsIso π.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hπ
  have h₁ : π.appTop ≫ e.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have h₂ : e.appTop ≫ π.appTop = 𝟙 _ := by
    rw [← cancel_epi π.appTop, ← Category.assoc, h₁, Category.id_comp, Category.comp_id]
  have h₃ : f' = π ≫ e ≫ f' := ext_of_isAffine (by
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc, h₂, Category.comp_id])
  conv_lhs => rw [h₃]
  simp only [Category.assoc]

section Points
variable {S : Scheme.{0}}

def postHom {G A : Over S} [GrpObj G] [GrpObj A] (p : G ⟶ A) [IsMonHom p] (T : Over S) : (T ⟶ G) →* (T ⟶ A) :=
  MonoidHom.mk' (· ≫ p) fun x y => MonObj.mul_comp x y p

theorem exists_lift_over {T X : Over S} (f : T ⟶ X) (U : S.Opens) (h : ∀ y, T.hom y ∈ U) :
    ∃ f' : T.left ⟶ (X.hom ⁻¹ᵁ U).toScheme, f' ≫ (X.hom ⁻¹ᵁ U).ι = f.left :=
  ⟨IsOpenImmersion.lift (X.hom ⁻¹ᵁ U).ι f.left (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (congrArg (fun q => q y ∈ U) (Over.w f)).mpr (h y)), IsOpenImmersion.lift_fac _ _ _⟩

theorem not_killed (hL : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : 1 ≤ P.g)
    {m : ℤ} (hm : m ≠ 0) (h : (𝟙 P.A) ^ m = 1) : False := by
  obtain ⟨l, hl, hp⟩ := Nat.exists_infinite_primes (m.natAbs + ringChar K + 1)
  have hK : (l : K) ≠ 0 := fun h0 => by
    rcases (Nat.dvd_prime hp).1 ((ringChar.spec K l).1 h0) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  have hc := (hL.mulN (Sp K) P l hp.one_le).2.2.2.2 K (𝟙 _) hK
  have hco : IsCoprime (l : ℤ) m := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime l m.natAbs := (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      absurd (Nat.le_of_dvd (Int.natAbs_pos.2 hm) hd) (by omega)
    simpa [Int.gcd] using this
  have h1 : Nat.card {x : Over.mk (𝟙 (Sp K)) ⟶ P.A // x ^ l = 1} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_pow _⟩⟩⟩
    have key : ∀ z : Over.mk (𝟙 (Sp K)) ⟶ P.A, z ^ l = 1 → z = 1 := fun z hz => by
      have e₁ : z ^ m = 1 := by
        have := map_zpow (preHom (G := P.A) z) (𝟙 P.A) m
        rw [h, map_one] at this
        exact (congrArg (· ^ m) (Category.comp_id z).symm).trans this.symm
      obtain ⟨a, b, hab⟩ := hco
      rw [← zpow_one z, ← hab, zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, e₁, zpow_natCast, hz, one_zpow,
        one_zpow, _root_.mul_one]
    exact (key _ x.2).trans (key _ y.2).symm
  have h2 : 1 < l ^ (2 * P.g) := Nat.one_lt_pow (by omega) hp.one_lt
  exact h2.ne (h1.symm.trans hc)
end Points

section Sieg
variable {h k : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}

theorem bilin (hF : Out.GlobalFnsSt) (c : SiegPre h k ζ s) (hc : Out.RelAmple c.A c.diag) (T : Over S) {n m : ℕ}
    (x : Fin n → (T ⟶ c.A)) (W : Matrix (Fin m) (Fin m) ℤ) (W' : Matrix (Fin n) (Fin n) ℤ) (a : Matrix (Fin m) (Fin n) ℤ)
    (e : W' + W'.transpose = a.transpose * (W + W.transpose) * a) :
    ∑ uv : Fin n × Fin n, W' uv.1 uv.2 • pull (lift (x uv.1) (x uv.2)).left (cls c.P c.isLB) =
      ∑ uv : Fin m × Fin m, W uv.1 uv.2 •
        pull (lift (∏ i, x i ^ a uv.1 i) (∏ i, x i ^ a uv.2 i)).left (cls c.P c.isLB) := by
  have h₁ := GlobalTheory.T.lineBundleIso_linComb_symm_biadditive_substitution S c.A c.P c.isLB
    (GlobalTheory.T.biadditive_of_trivial_on_axes hF S c.A c.diag c.ab (pull_isLB c.isLB _) hc c.P c.isLB c.rig₁ c.rig₂) c.symm T n m x W W' a e
  rw [← cls_eq_iff (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb c.isLB _ _), cls_linComb c.isLB,
    cls_linComb c.isLB] at h₁
  exact h₁

theorem pos_of_relAmple (hL : Out.Laws) (c : SiegPre h k ζ s) (hc : Out.RelAmple c.A c.diag) (P : Out.PolAV S)
    (hg : 1 ≤ P.g) (p : S) {n : ℕ} (pr : Fin n → (P.A ⟶ c.A)) (hpr : ∀ u, IsMonHom (pr u))
    (hprod : ∀ (T : Over S) (y : Fin n → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u)
    (W : Matrix (Fin n) (Fin n) ℤ) (M : LB P.A.left) (hM : M.IsLB) (hA : Out.RelAmple P.A M)
    (e : cls M hM = ∑ uv : Fin n × Fin n, W uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB))
    (u : Fin n → ℤ) (hu : u ≠ 0) : 0 < dotProduct u (W.mulVec u) := by
  by_contra hneg
  obtain ⟨m, hm⟩ : ∃ m : ℕ, dotProduct u (W.mulVec u) = -(m : ℤ) := ⟨(dotProduct u (W.mulVec u)).natAbs, by omega⟩
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hu
  obtain ⟨K, _, _, x, -⟩ := FinEt.exists_algClosed_point S p
  obtain ⟨P', φ, hφ, hg', hmul, -⟩ := hL.polBaseChange S (Sp K) x P
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := x (default : PrimeSpectrum K)) trivial
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hxU : ∀ y, x y ∈ U := fun y => by rwa [Subsingleton.elim y (default : PrimeSpectrum K)]
  let ρ : ∀ T : Over (Sp K), (T ⟶ P'.A) →* (Over.mk (T.hom ≫ x) ⟶ P.A) := fun T =>
    MonoidHom.mk' (Out.toBase hφ.w) (hmul T)
  have inj : ∀ {T : Over (Sp K)} {a b : T ⟶ P'.A}, ρ T a = ρ T b → a = b := fun {T a b} e =>
    Over.OverMorphism.ext (hφ.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))
  let T : Over S := Over.mk (P'.A.hom ≫ x)
  let gp : T ⟶ P.A := ρ P'.A (𝟙 _)
  let z : Over.mk (𝟙 (Sp K)) ⟶ P'.A := 1
  have hz : z.left ≫ P'.A.hom = 𝟙 _ := Over.w z
  let T₀ : Over S := Over.mk (𝟙 (Sp K) ≫ x)
  let z₀ : T₀ ⟶ T := Over.homMk z.left (by
    show z.left ≫ P'.A.hom ≫ x = 𝟙 _ ≫ x
    rw [← Category.assoc, hz]
    rfl)
  let π₀ : T ⟶ T₀ := Over.homMk P'.A.hom (by
    show P'.A.hom ≫ 𝟙 _ ≫ x = P'.A.hom ≫ x
    rw [Category.id_comp])
  have hz₀ : z₀ ≫ gp = 1 := by
    refine Eq.trans (Over.OverMorphism.ext ?_) (map_one (ρ (Over.mk (𝟙 (Sp K)))))
    show z.left ≫ 𝟙 _ ≫ φ = z.left ≫ φ
    rw [Category.id_comp]
  have hbij := hL.globalFns (Sp K) P'.A P'.isAb
  have hF : IsField Γ(P'.A.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective _ hbij)).symm.toMulEquiv.isField (Field.toIsField K)
  have hTU : ∀ y, T.hom y ∈ U := fun y => hxU (P'.A.hom y)
  have key : ∀ v, (gp ≫ pr v) ^ u w = 1 := fun v => by
    obtain ⟨f, hf, -⟩ := hprod T fun i => (gp ≫ pr v) ^ u i
    obtain ⟨f', hf'⟩ := exists_lift_over f U hTU
    obtain ⟨a', ha'⟩ := exists_lift_over (gp ≫ pr v) U hTU
    have hD : c.diag.IsLB := pull_isLB c.isLB _
    have b := bilin hL.globalFns c hc T (fun _ : Fin 1 => gp ≫ pr v) W (Matrix.of fun _ _ => -(m : ℤ))
      (Matrix.of fun i _ => u i) (by
      ext i j
      simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_apply, Matrix.of_apply, ← hm, dotProduct, Matrix.mulVec,
        Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    simp only [Matrix.of_apply, Fin.prod_univ_one, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Nat.mul_one, one_smul] at b
    obtain ⟨V, hV, hfV⟩ := exists_affine_of_nonpos hF (z.left (default : PrimeSpectrum K)) f' a'
      (isAmpleLB_of_relAmple P.A hM hA U hU) (isAmpleLB_of_relAmple c.A hD hc U hU) m (by
        rw [cls_pull hM, cls_pull hD, ← pull_comp, ← pull_comp, hf', ha', e, map_sum]
        have e₁ : ∀ uv : Fin n × Fin n, pull f.left (W uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB)) =
            W uv.1 uv.2 • pull (lift ((gp ≫ pr v) ^ u uv.1) ((gp ≫ pr v) ^ u uv.2)).left
              (cls c.P c.isLB) := fun uv => by
          rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hf, hf]
        have e₂ : pull (gp ≫ pr v).left (cls c.diag hD) = pull (lift (gp ≫ pr v) (gp ≫ pr v)).left (cls c.P c.isLB) := by
          refine (pull_comp _ _ (cls c.P c.isLB)).symm.trans ?_
          rw [← Over.comp_left, comp_lift, Category.comp_id]
        rw [Finset.sum_congr rfl fun uv _ => e₁ uv, ← b, e₂, neg_smul, natCast_zsmul,
          neg_add_cancel])
    have e₃ := eq_comp_of_affine P'.A.hom z.left hz hbij f' V hV hfV
    have e₄ : f = π₀ ≫ z₀ ≫ f := Over.OverMorphism.ext (by
      show f.left = P'.A.hom ≫ z.left ≫ f.left
      rw [← hf']
      conv_lhs => rw [e₃]
      simp only [Category.assoc])
    have := hpr v
    have e₅ : z₀ ≫ (gp ≫ pr v) ^ u w = 1 := by
      refine (map_zpow (preHom (G := c.A) z₀) _ _).trans ?_
      have : preHom z₀ (gp ≫ pr v) = 1 := by
        show z₀ ≫ gp ≫ pr v = 1
        rw [← Category.assoc, hz₀]
        exact map_one (postHom (pr v) T₀)
      rw [this, one_zpow]
    rw [← hf w, e₄, Category.assoc, Category.assoc, hf w, e₅]
    exact map_one (preHom π₀)
  refine not_killed hL P' (hg'.symm ▸ hg) hw (inj ?_)
  rw [map_zpow, map_one]
  refine (hprod T fun _ => 1).unique (fun v => ?_) fun v => ?_
  · have := hpr v
    exact (map_zpow (postHom (pr v) T) gp _).trans (key v)
  · have := hpr v
    exact map_one (postHom (pr v) T)
end Sieg

section Sharp
variable {h g k : ℕ} {o : Type} [CommRing o] {b : TBase o k} {J : Type} {S : Scheme.{0}} {s : S ⟶ Sp o}

def levHom (c : SiegPre h k (b.ζ : o) s) (T : Over S) : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (T ⟶ c.A) :=
  (preHom (toUnit T)).comp (MonoidHom.mk' (fun a => c.lev a.toAdd) fun a a' => c.lev_add _ _)

theorem label_iff (c : SiegPre h k (b.ζ : o) s) (t : TObj g k J b s) (pr : Fin 8 → (t.A ⟶ c.A))
    (hpr : ∀ u, IsMonHom (pr u))
    (hprod : ∀ (T : Over S) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u)
    (a : Matrix (Fin 8) (Fin 8) ℤ) (F : t.A ⟶ t.A) (hF : ∀ u, F ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod)
    (e : Fin (2 * g) → Fin 8 → (Fin h ⊕ Fin h → ℤ)) (he : ∀ i u, (t.pt i ≫ pr u).left = (c.lev (e i u)).left)
    (i : Fin (2 * g)) (m : Ix g k) :
    t.pt i ≫ F = t.lab m ↔ ∀ u, levHom c (Out.baseOver S) (Multiplicative.ofAdd
      (∑ v, a u v • e i v - ∑ i', ((m i').val : ℤ) • e i' u)) = 1 := by
  have h0 : ∀ i u, t.pt i ≫ pr u = levHom c (Out.baseOver S) (Multiplicative.ofAdd (e i u)) := fun i u =>
    Over.OverMorphism.ext ((he i u).trans (by
      have : (toUnit (Out.baseOver S)).left = 𝟙 S :=
        (Category.comp_id _).symm.trans (Over.w (toUnit (Out.baseOver S)))
      show _ = (toUnit (Out.baseOver S)).left ≫ (c.lev (e i u)).left
      rw [this]
      exact (Category.id_comp _).symm))
  have h1 : ∀ u, (t.pt i ≫ F) ≫ pr u = levHom c (Out.baseOver S) (Multiplicative.ofAdd (∑ v, a u v • e i v)) := fun u => by
    rw [Category.assoc, hF, List.prod_ofFn, ofAdd_sum, map_prod]
    refine (map_prod (preHom (G := c.A) (t.pt i)) _ _).trans (Finset.prod_congr rfl fun v _ => ?_)
    rw [map_zpow, ofAdd_zsmul, map_zpow, ← h0]
    rfl
  have h2 : ∀ u, t.lab m ≫ pr u =
      levHom c (Out.baseOver S) (Multiplicative.ofAdd (∑ i', ((m i').val : ℤ) • e i' u)) := fun u => by
    have := hpr u
    refine (map_list_prod (postHom (pr u) (Out.baseOver S)) _).trans ?_
    rw [List.map_ofFn, List.prod_ofFn, ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [ofAdd_zsmul, map_zpow, ← h0, zpow_natCast]
    exact map_pow (postHom (pr u) (Out.baseOver S)) _ _
  simp only [ofAdd_sub, map_div, div_eq_one, ← h1, ← h2]
  exact ⟨fun h u => by rw [h], fun h => (hprod _ fun u => t.lab m ≫ pr u).unique h fun _ => rfl⟩

theorem dvd_of_levHom (c : SiegPre h k (b.ζ : o) s) (p : S) (a : Fin h ⊕ Fin h → ℤ)
    (ha : levHom c (Out.baseOver S) (Multiplicative.ofAdd a) = 1) : ∃ d, a = k • d := by
  obtain ⟨K, _, _, x, -⟩ := FinEt.exists_algClosed_point S p
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ s)
  refine ((c.geom K x β.hom (Units.map β.hom.toMonoidHom b.ζ) hβ.symm rfl).1 a).1 ?_
  let q : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
  have e : toUnit (Over.mk x) = q ≫ toUnit (Out.baseOver S) := toUnit_unique _ _
  rw [e, Category.assoc]
  exact (congrArg (q ≫ ·) ha).trans (map_one (preHom q))

theorem levHom_nsmul (c : SiegPre h k (b.ζ : o) s) (T : Over S) (d : Fin h ⊕ Fin h → ℤ) :
    levHom c T (Multiplicative.ofAdd (k • d)) = 1 := by
  rw [ofAdd_nsmul, map_pow]
  refine (map_pow (preHom (toUnit T)) (c.lev d) k).symm.trans ?_
  rw [c.lev_tors, map_one]

theorem cls_shape (hF : Out.GlobalFnsSt) (c : SiegPre h k (b.ζ : o) s) (hc : Out.RelAmple c.A c.diag)
    (t : TObj g k J b s) (pr : Fin 8 → (t.A ⟶ c.A)) (W a : Matrix (Fin 8) (Fin 8) ℤ)
    (hL : LBIso t.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left)
      (fun uv => W uv.1 uv.2)))
    (F : t.A ⟶ t.A) (hFa : ∀ u, F ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) (κ : ℕ) :
    cls _ (LB.isLB_linComb t.isLB (K := Fin 2) ![𝟙 t.A.left, F.left] ![(κ : ℤ), -1]) =
      ∑ uv : Fin 8 × Fin 8, ((κ : ℤ) • W - a.transpose * W * a) uv.1 uv.2 •
        pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by
  rw [← cls_eq_iff t.isLB (LB.isLB_linComb c.isLB _ _), cls_linComb c.isLB] at hL
  have e := bilin hF c hc t.A pr W (a.transpose * W * a) a (by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc])
  have e₁ : pull F.left (cls t.L t.isLB) = ∑ uv : Fin 8 × Fin 8, (a.transpose * W * a) uv.1 uv.2 •
      pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by
    rw [e, hL, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hFa, hFa, List.prod_ofFn, List.prod_ofFn]
  rw [cls_linComb t.isLB, Fin.sum_univ_two]
  show (κ : ℤ) • pull (𝟙 _) _ + (-1 : ℤ) • pull F.left _ = _
  rw [pull_id, e₁, hL, Finset.smul_sum, neg_one_zsmul, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun uv _ => ?_
  rw [Matrix.sub_apply, Matrix.smul_apply, sub_smul, smul_eq_mul, mul_smul]
end Sharp

theorem shape_of_isSharp : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (c : SiegPre h k (b.ζ : o) s) (c' : SiegPre h k (b.ζ : o) s') (t : TObj g k J b s) (t' : TObj g k J b s'), 1 ≤ h → Nonempty S → c.Principal → c'.Principal → IsSharp W a bas t c → IsSharp W a bas t' c' → t.Shape Mat κ → t'.Shape Mat κ := by
  intro hL _ h g W J a bas _ _ k o _ b Mat κ S S' s s' c c' t t' hh ⟨p⟩ hc hc'
    ⟨pr, hpr, hprod, hiso, hact, hpt⟩ ⟨pr', hpr', hprod', hiso', hact', hpt'⟩ H j
  have hg : 1 ≤ g := by
    have := bas.finrank_eq
    simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_sum, Fintype.card_fin, smul_eq_mul] at this
    omega
  refine ⟨fun i => ?_, ?_⟩
  · refine (label_iff c' t' pr' hpr' hprod' (a j) _ (hact' j) (fun i => bas (Pi.single i 1)) hpt' i _).2 fun u => ?_
    obtain ⟨d, hd⟩ := dvd_of_levHom c p _
      ((label_iff c t pr hpr hprod (a j) _ (hact j) (fun i => bas (Pi.single i 1)) hpt i _).1 ((H j).1 i) u)
    rw [hd]
    exact levHom_nsmul c' _ d
  · set W' := (κ : ℤ) • W - (a j).transpose * W * a j with hW'
    have pos := pos_of_relAmple hL c hc.1 t.pol hg p pr hpr hprod W' _ _ (H j).2
      (cls_shape hL.globalFns c hc.1 t pr W (a j) hiso _ (hact j) κ)
    have pd := posDef_of_int (W' + W'.transpose) (by rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm])
      fun u hu => by
        rw [Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose, dotProduct_comm u (Matrix.vecMul _ _),
          ← Matrix.dotProduct_mulVec]
        exact add_pos (pos u hu) (pos u hu)
    have amp := GlobalTheory.T.relAmple_formBundle_power_of_posDef hL.globalFns h k 8 o _ S' s' c' t'.A pr' W' hpr' hprod' hc'.1 pd
    have e := cls_shape hL.globalFns c' hc'.1 t' pr' W (a j) hiso' _ (hact' j) κ
    have hB := LB.isLB_linComb c'.isLB (K := Fin 8 × Fin 8) (fun uv => (lift (pr' uv.1) (pr' uv.2)).left)
      (fun uv => W' uv.1 uv.2)
    rw [← cls_linComb c'.isLB _ _ hB] at e
    have := t'.ab.proper
    have hM := LB.isLB_linComb t'.isLB (K := Fin 2) ![𝟙 t'.A.left, (t'.act j).left] ![(κ : ℤ), -1]
    refine relAmple_of_isAmpleLB t'.A hM fun U hU =>
      (isAmpleLB_of_relAmple t'.A hB amp U hU).of_lbIso (pull_isLB hM _) ?_
    rw [← cls_eq_iff (pull_isLB hM _) (pull_isLB hB _), cls_pull hM, cls_pull hB, e]

end GlobalTheory.SharpShape
end
