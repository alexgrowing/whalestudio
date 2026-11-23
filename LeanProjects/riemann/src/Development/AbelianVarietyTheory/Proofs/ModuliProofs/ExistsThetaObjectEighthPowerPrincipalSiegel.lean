import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoLinCombSymmBiadditiveSubstitution
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDefStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.SiegelPower

open GlobalTheory.CechPic GlobalTheory.CommutatorPairing

section Pairing

variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A]

theorem exists_gen_dual {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : ∃ u : LB.Gen (LB.LinComb (dual L) φ ε), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val (L := dual L) u r z J = (val t r z J)⁻¹ := by
  have hg : ∀ i j : K → L.ι, (LB.LinComb (dual L) φ ε).g i j = ((LB.LinComb L φ ε).g i j)⁻¹ := fun i j => by
    show ∏ k, res (le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)) :
        LB.wchart L φ i ⊓ LB.wchart L φ j ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
        (pullU (φ k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k))⁻¹) ^ ε k =
      (∏ k, res (le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)) :
        LB.wchart L φ i ⊓ LB.wchart L φ j ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
        (pullU (φ k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k))) ^ ε k)⁻¹
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have e : ∀ {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)ˣ) (n : ℤ), res h a⁻¹ ^ n = (res h a ^ n)⁻¹ := fun h a n => by
      rw [map_inv, inv_zpow]
    rw [map_inv (pullU _ _)]
    exact e _ _ _
  refine ⟨⟨fun j => (t.s j)⁻¹⟩, fun i j => ?_, fun Z r z J => map_inv _ _⟩
  have h := congrArg (·⁻¹) (ht i j)
  simp only [mul_inv, ← map_inv] at h
  exact h.trans (congrArg (· * _) (hg i j).symm)

theorem exists_theta_dual {L : LB G.left} {k : ℤ} {T : Over S} (θ : Out.ThetaGrp G L k T) :
    ∃ θ' : Out.ThetaGrp G (dual L) k T, θ'.pt = θ.pt ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ G) (z : Z.left) (J),
      thetaVal θ' t a z J = (thetaVal θ t a z J)⁻¹ := by
  obtain ⟨u, hu, hv⟩ := exists_gen_dual (L := L) (K := Fin 2) ![(snd T G).left, (Out.translPt G θ.pt).left] ![k, -k]
    θ.φ θ.isGen
  exact ⟨⟨θ.pt, u, hu⟩, rfl, fun Z t a z J => hv _ _ z J⟩

theorem weilIs_dual (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G) {L : LB G.left} (hL : L.IsLB) {n : ℤ} {T : Over S}
    {x y : T ⟶ G} {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs G L n x y c) : Out.WeilIs G (dual L) n x y c⁻¹ := by
  refine WeilIsogeny.weilIs_of_local hG hA (isLB_dual hL) fun p => ?_
  obtain ⟨V, hV, ⟨θx, θy, ex, ey⟩, H⟩ := h p
  obtain ⟨θx', fx, vx⟩ := exists_theta_dual θx
  obtain ⟨θy', fy, vy⟩ := exists_theta_dual θy
  refine ⟨V, hV, θx', θy', fx.trans ex, fy.trans ey, (commIsOf_iff (isLB_dual hL) _ _ _).2 fun Z t a z J hJ => ?_⟩
  have e := (commIsOf_iff hL _ _ _).1 (H θx θy ex ey) Z t a z J hJ
  have e' : Out.unitRes V c⁻¹ = (Out.unitRes V c)⁻¹ := map_inv _ _
  rw [e', map_inv, ← e]
  unfold commVal
  rw [vx, vx, vy, vy, fx, fy]
  simp only [mul_inv]

theorem weilIs_of_cls (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G) {L : LB G.left} (hL : L.IsLB) {M : LB A.left}
    (hM : M.IsLB) (ψ : G ⟶ A) [IsMonHom ψ] (e : cls L hL = pull ψ.left (cls M hM)) {n : ℤ} {T : Over S}
    {x y : T ⟶ G} {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A M n (x ≫ ψ) (y ≫ ψ) c) : Out.WeilIs G L n x y c := by
  have h₁ : (lbPow L 1).IsLB := LB.isLB_linComb hL _ _
  have := WeilIsogeny.weilIs_pull_hom hG hA hL hM ψ (d := 1)
    ((cls_eq_iff h₁ (pull_isLB hM _)).1 (by rw [cls_lbPow hL, one_smul, e]; rfl)) h
  simpa using this

def pairGroup (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G) (n : ℤ) {T : Over S} (x y : T ⟶ G)
    {L₀ : LB G.left} (hL₀ : L₀.IsLB) {c₀ : Γ(T.left, ⊤)ˣ} (h₀ : Out.WeilIs G L₀ n x y c₀) :
    AddSubgroup (CechPic.Pic G.left × Additive Γ(T.left, ⊤)ˣ) :=
  have tr : ∀ {L L' : LB G.left} (hL : L.IsLB) (hL' : L'.IsLB) {c}, cls L hL = cls L' hL' →
      Out.WeilIs G L' n x y c → Out.WeilIs G L n x y c := fun hL hL' c e h =>
    weilIs_of_cls hG hA hL hL' (𝟙 G) (e.trans (pull_id _).symm) (by simpa using h)
  have add : ∀ {p q : CechPic.Pic G.left × Additive Γ(T.left, ⊤)ˣ},
      (∃ L hL, cls L hL = p.1 ∧ Out.WeilIs G L n x y p.2.toMul) →
      (∃ L hL, cls L hL = q.1 ∧ Out.WeilIs G L n x y q.2.toMul) →
      ∃ L hL, cls L hL = (p + q).1 ∧ Out.WeilIs G L n x y (p + q).2.toMul := by
    rintro p q ⟨L, hL, e, h⟩ ⟨M, hM, e', h'⟩
    have hN := isLB_tens hL hM
    refine ⟨_, hN, by rw [cls_tens hL hM, e, e']; rfl, DescendedPrincipal.weilIs_mul_div hG hA hN hL h
      (tr (LB.isLB_div hN hL) hM ?_ h')⟩
    rw [cls_div hN hL, cls_tens hL hM, add_sub_cancel_left]
  have neg : ∀ {p : CechPic.Pic G.left × Additive Γ(T.left, ⊤)ˣ},
      (∃ L hL, cls L hL = p.1 ∧ Out.WeilIs G L n x y p.2.toMul) →
      ∃ L hL, cls L hL = (-p).1 ∧ Out.WeilIs G L n x y (-p).2.toMul := by
    rintro p ⟨L, hL, e, h⟩
    exact ⟨_, isLB_dual hL, by rw [cls_dual hL, e]; rfl, weilIs_dual hG hA hL h⟩
  { carrier := {p | ∃ L hL, cls L hL = p.1 ∧ Out.WeilIs G L n x y p.2.toMul}
    add_mem' := add
    neg_mem' := neg
    zero_mem' := by
      have h : ∃ L hL, cls L hL = (cls L₀ hL₀, Additive.ofMul c₀).1 ∧
        Out.WeilIs G L n x y (cls L₀ hL₀, Additive.ofMul c₀).2.toMul := ⟨L₀, hL₀, rfl, h₀⟩
      have := add h (neg h)
      rwa [add_neg_cancel] at this }

theorem mem_pairGroup (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G) (n : ℤ) {T : Over S} (x y : T ⟶ G)
    {L₀ : LB G.left} (hL₀ : L₀.IsLB) {c₀ : Γ(T.left, ⊤)ˣ} (h₀ : Out.WeilIs G L₀ n x y c₀)
    (κ : CechPic.Pic G.left) (c : Additive Γ(T.left, ⊤)ˣ) :
    (κ, c) ∈ pairGroup hG hA n x y hL₀ h₀ ↔ ∃ L hL, cls L hL = κ ∧ Out.WeilIs G L n x y c.toMul := Iff.rfl

theorem pow_eq_prod (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme G) {L : LB G.left} (hL : L.IsLB) {D : LB A.left}
    (hD : D.IsLB) {K : Type} [Fintype K] (f : K → (G ⟶ A)) (hf : ∀ i, IsMonHom (f i)) (ε : K → ℤ) (m : ℤ)
    (e : m • cls L hL = ∑ i, ε i • pull (f i).left (cls D hD)) {n : ℤ} {T : Over S} {x y : T ⟶ G}
    {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs G L n x y c) {d : K → Γ(T.left, ⊤)ˣ}
    (hd : ∀ i, Out.WeilIs A D n (x ≫ f i) (y ≫ f i) (d i)) : c ^ m = ∏ i, d i ^ ε i := by
  have h₁ := (pairGroup hG hA n x y hL h).zsmul_mem
    ((mem_pairGroup hG hA n x y hL h _ (Additive.ofMul c)).2 ⟨L, hL, rfl, h⟩) m
  have h₂ := (pairGroup hG hA n x y hL h).sum_mem (t := Finset.univ) fun i _ => (pairGroup hG hA n x y hL h).zsmul_mem
    ((mem_pairGroup hG hA n x y hL h (pull (f i).left (cls D hD)) (Additive.ofMul (d i))).2
      ⟨D.pull (f i).left, pull_isLB hD _, cls_pull hD _ _,
        weilIs_of_cls hG hA (pull_isLB hD _) hD (f i) (cls_pull hD _ _) (hd i)⟩) (ε i)
  have e₀ : ∑ i, ε i • (pull (f i).left (cls D hD), Additive.ofMul (d i)) =
      (m • cls L hL, Additive.ofMul (∏ i, d i ^ ε i)) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      exact e.symm
    · rw [Prod.snd_sum, ofMul_prod]
      rfl
  rw [e₀, mem_pairGroup] at h₂
  rw [Prod.smul_mk, mem_pairGroup] at h₁
  obtain ⟨M, hM, e₁, w₁⟩ := h₁
  obtain ⟨M', hM', e₂, w₂⟩ := h₂
  have w₃ := weilIs_of_cls hG hA hM hM' (𝟙 G) ((e₁.trans e₂.symm).trans (pull_id _).symm) (x := x) (y := y)
    (by rw [Category.comp_id, Category.comp_id]; exact w₂)
  exact weilIs_unique hG hA hM w₁ w₃

end Pairing

theorem pow_eq_one_of_weilIs (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S}
    {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ} (hx : x ^ k = 1) (h : Out.WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have H : ∀ n : ℕ, Out.WeilIs P.A P.L k (x ^ (n + 1)) y (c ^ (n + 1)) := fun n => by
    induction n with
    | zero => simpa using h
    | succ n ih => simpa only [← pow_succ] using weilIs_mul_left hG S P k T _ x y _ c ih h
  have h₁ := H k
  rw [pow_succ, hx, _root_.one_mul] at h₁
  have := weilIs_unique hG P.isAb P.isLB h₁ h
  rwa [pow_succ, mul_eq_right] at this

theorem eq_one_of_geometric {S : Scheme.{0}} {k : ℕ} (hk : Odd k) (u : Γ(S, ⊤)) (hu : u ^ k = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (k : K) ≠ 0 ∧ x.appTop.hom u ^ 2 = 1) : u = 1 := by
  have hs : IsUnit (∑ i ∈ Finset.range k, u ^ i) := by
    refine (RingedSpace.isUnit_of_isUnit_germ S.toRingedSpace ⊤ _ fun p _ => ?_)
    let κ := S.residueField p
    let K := AlgebraicClosure κ
    let x : Sp K ⟶ S := spMap (algebraMap κ K) ≫ S.fromSpecResidueField p
    obtain ⟨h₁, h₂⟩ := h K x
    have h₃ : x.appTop.hom u = 1 := by
      obtain ⟨m, rfl⟩ := hk
      have := congrArg x.appTop.hom hu
      rwa [map_pow, map_one, pow_succ, pow_mul, h₂, one_pow, _root_.one_mul] at this
    have h₄ : IsUnit (x.appTop.hom (∑ i ∈ Finset.range k, u ^ i)) := by
      simp only [map_sum, map_pow, h₃, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one]
      have := (Ne.isUnit h₁).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rwa [map_natCast] at this
    have h₅ : x (default : PrimeSpectrum K) = p :=
      (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply p _)
    have h₆ : x (default : PrimeSpectrum K) ∈ S.basicOpen (∑ i ∈ Finset.range k, u ^ i) := by
      show (default : PrimeSpectrum K) ∈ x ⁻¹ᵁ S.basicOpen _
      rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ h₄]
      trivial
    rw [h₅] at h₆
    exact (S.mem_basicOpen_top _ _).1 h₆
  have := geom_sum_mul u k
  rw [hu, sub_self] at this
  exact sub_eq_zero.1 (hs.mul_right_eq_zero.1 this)

theorem smoothOfRelativeDimension_of_card (hM : Out.MulNSt) {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (hG : IsAbelianScheme G) {L : LB G.left} (hL : L.IsLB) (rigid : Out.Rigidified G L) (sym : Out.Sym G L)
    (ample : Out.RelAmple G L) (ktriv : Out.KTriv G L) {n g : ℕ} (hn : 2 ≤ n)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
      (n : K) ≠ 0 ∧ Nat.card {y : Over.mk x ⟶ G // y ^ n = 1} = n ^ (2 * g)) :
    SmoothOfRelativeDimension g G.hom := by
  have := hG.smooth
  have := hG.geomConnected
  choose m W hW hd using H1.exists_dim G.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := S.residueField (G.hom y)
  let k := AlgebraicClosure κ
  let x : Sp k ⟶ S := spMap (algebraMap κ k) ≫ S.fromSpecResidueField (G.hom y)
  have hq := isGrpPullback_pullback G x
  have hp := hq.1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum k)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have hab := Out.TLinPf.isAb_pullback x G hG
  have := hab.smooth
  have : ConnectedSpace ((Over.pullback x).obj G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := G.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj G).hom y'
  have hL' := pull_isLB hL (pullback.fst G.hom x)
  obtain ⟨h₁, h₂⟩ := amplePt S k x G _ _ hq L _ hL hL' (PolBaseChange.lbIso_refl hL') ample ktriv
  let P : Out.PolAV (Sp k) :=
    { A := (Over.pullback x).obj G, isAb := hab, g := d, smoothDim := hd', L := L.pull (pullback.fst G.hom x)
      isLB := hL', rigid := PolBaseChange.rigidified_pull hq rigid, sym := PolBaseChange.sym_pull hq sym
      ample := h₁, ktriv := h₂ }
  obtain ⟨h₃, h₄⟩ := h k (𝟙 _ ≫ x)
  have h₅ := (hM _ P n (by omega)).2.2.2.2 k (𝟙 _) h₃
  have hb : Function.Bijective (pushHom hq (Over.mk (𝟙 _))) := by
    refine ⟨fun a b e => Over.OverMorphism.ext (hp.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])),
      fun a => ⟨Over.homMk (hp.lift a.left (𝟙 _) (Over.w a)) (hp.lift_snd _ _ _),
        Over.OverMorphism.ext (hp.lift_fst _ _ _)⟩⟩
  let e := MulEquiv.ofBijective _ hb
  have h₆ : n ^ (2 * d) = n ^ (2 * g) := by
    refine h₅.symm.trans (Eq.trans (Nat.card_congr (e.toEquiv.subtypeEquiv fun a => ?_)) h₄)
    exact ((map_eq_one_iff e e.injective).symm.trans (by rw [map_pow]; rfl))
  have h₇ : d = g := by
    have := Nat.pow_right_injective hn h₆
    omega
  rw [← h₇, ← H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)]
  exact hd y

end GlobalTheory.SiegelPower

namespace GlobalTheory.SiegelPower

open GlobalTheory.CechPic

section Algebra

variable {Γ M : Type*} [CommGroup Γ] [AddCommGroup M] {B : Γ → Γ → M}
  (hB : ∀ x x' y, B (x * x') y = B x y + B x' y) (hs : ∀ x y, B x y = B y x)

def quad (B : Γ → Γ → M) {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → Γ) : M :=
  ∑ uv : Fin n × Fin n, W uv.1 uv.2 • B (x uv.1) (x uv.2)

include hB in
theorem biadd_one (y : Γ) : B 1 y = 0 := by
  have := hB 1 1 y
  rwa [_root_.mul_one, left_eq_add] at this

include hB in
theorem biadd_inv (x y : Γ) : B x⁻¹ y = -B x y := by
  rw [eq_neg_iff_add_eq_zero, ← hB, inv_mul_cancel, biadd_one hB]

include hB in
theorem biadd_pow (x y : Γ) (k : ℕ) : B (x ^ k) y = k • B x y := by
  induction k with
  | zero => rw [pow_zero, biadd_one hB, zero_smul]
  | succ k ih => rw [pow_succ, hB, ih, succ_nsmul]

variable {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ)

include hB in
theorem quad_one : quad B W (fun _ => 1) = 0 := by simp [quad, biadd_one hB]

include hB hs in
theorem quad_inv (x : Fin n → Γ) : quad B W (fun u => (x u)⁻¹) = quad B W x := by
  refine Finset.sum_congr rfl fun uv _ => ?_
  rw [biadd_inv hB, hs, biadd_inv hB, neg_neg, hs]

include hB hs in
theorem quad_mul (x a : Fin n → Γ) : quad B W (fun u => x u * a u) =
    quad B W x + quad B W a + ∑ v, B (∏ u, x u ^ (W + W.transpose) u v) (a v) := by
  have e : ∑ v, B (∏ u, x u ^ (W + W.transpose) u v) (a v) =
      ∑ uv : Fin n × Fin n, W uv.1 uv.2 • B (x uv.1) (a uv.2) +
        ∑ uv : Fin n × Fin n, W uv.1 uv.2 • B (x uv.2) (a uv.1) := by
    rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [BilinCalc.map_prod_zpow (fun z => B z (a v)) (fun p q => hB p q _), ← Finset.sum_add_distrib]
    simp only [Matrix.add_apply, Matrix.transpose_apply, add_smul]
  rw [e, quad, quad, quad, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun uv _ => ?_
  rw [hB, hs (x uv.1), hB, hs (a uv.1), hB, hs (x uv.2) (x uv.1), hs (a uv.2) (x uv.1), hs (a uv.2) (a uv.1)]
  simp only [smul_add]
  abel

include hB hs in
theorem smul_quad_mul {k : ℕ} (x a : Fin n → Γ) (hx : ∀ u, x u ^ k = 1) :
    (k : ℤ) • quad B W a + (-(k : ℤ)) • quad B W (fun u => x u * a u) = 0 := by
  have e₁ : k • quad B W x = 0 := by
    rw [quad, Finset.smul_sum]
    refine Finset.sum_eq_zero fun uv _ => ?_
    rw [smul_comm, ← biadd_pow hB, hx, biadd_one hB, smul_zero]
  have e₂ : k • ∑ v, B (∏ u, x u ^ (W + W.transpose) u v) (a v) = 0 := by
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [← biadd_pow hB, ← Finset.prod_pow]
    simp only [← zpow_natCast, ← zpow_mul, mul_comm _ (k : ℤ)]
    simp only [zpow_mul, zpow_natCast, hx, one_zpow, Finset.prod_const_one, biadd_one hB]
  rw [quad_mul hB hs, neg_smul]
  simp only [natCast_zsmul, smul_add, e₁, e₂, zero_add, add_zero, add_neg_cancel]

include hB hs in
theorem two_smul_quad (x : Fin n → Γ) : (2 : ℤ) • quad B W x =
    ∑ i : (Fin n × Fin n) × Fin 3, (W i.1.1 i.1.2 * ![1, -1, -1] i.2) •
      B (![x i.1.1 * x i.1.2, x i.1.1, x i.1.2] i.2) (![x i.1.1 * x i.1.2, x i.1.1, x i.1.2] i.2) := by
  rw [quad, Finset.smul_sum, Fintype.sum_prod_type (f := fun i : (Fin n × Fin n) × Fin 3 => _)]
  refine Finset.sum_congr rfl fun uv _ => ?_
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_smul, one_smul,
    neg_smul, smul_neg]
  rw [hB, hs (x uv.1) (x uv.1 * x uv.2), hB, hs (x uv.2) (x uv.1 * x uv.2), hB, hs (x uv.2) (x uv.1)]
  module

theorem prod_zpow_eq {I : Type*} [Fintype I] (x : Γ) (f : I → ℤ) : ∏ i, x ^ f i = x ^ ∑ i, f i :=
  (map_sum (zmultiplesHom (Additive Γ) (Additive.ofMul x)) _ _).symm

theorem eq_one_of_det (E : Matrix (Fin n) (Fin n) ℤ) (hE : E.det = 1) (x : Fin n → Γ)
    (h : ∀ v, ∏ u, x u ^ E u v = 1) (w : Fin n) : x w = 1 := by
  have e : ∏ v, (∏ u, x u ^ E u v) ^ E.adjugate v w = x w := by
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    have : ∀ u, ∏ v, x u ^ (E u v * E.adjugate v w) = x u ^ (1 : Matrix (Fin n) (Fin n) ℤ) u w := fun u => by
      rw [← one_smul ℤ (1 : Matrix (Fin n) (Fin n) ℤ), ← hE, ← Matrix.mul_adjugate, Matrix.mul_apply]
      exact prod_zpow_eq _ _
    simp only [this]
    rw [Finset.prod_eq_single w (fun u _ hu => by rw [Matrix.one_apply_ne hu, zpow_zero]) (by simp)]
    simp
  rw [← e]
  simp [h]

theorem existsUnique_coord {Λ I : Type} [AddCommGroup Λ] {m k : ℕ} (hk : k ≠ 0) (l : Λ → Γ)
    (add : ∀ a b, l (a + b) = l a * l b) (ker : ∀ a, l a = 1 ↔ ∃ b, a = k • b)
    (onto : ∀ y : Γ, y ^ k = 1 → ∃ a, l a = y) (bas : (Fin m → ℤ) ≃ₗ[ℤ] (I → Λ)) (y : I → Γ) (hy : ∀ u, y u ^ k = 1) :
    ∃! c : Fin m → ZMod k, ∀ u, ∏ i, l (bas (Pi.single i 1) u) ^ (c i).val = y u := by
  haveI : NeZero k := ⟨hk⟩
  let F : Λ →+ Additive Γ := AddMonoidHom.mk' (fun a => Additive.ofMul (l a)) fun a b => by rw [add, ofMul_mul]
  have hF : ∀ a b, l a = l b ↔ ∃ e, a - b = k • e := fun a b => by
    rw [← ker]
    show F a = F b ↔ F (a - b) = 0
    rw [map_sub, sub_eq_zero]
  have e : ∀ (c : Fin m → ℕ) u, ∏ i, l (bas (Pi.single i 1) u) ^ c i = l (bas (fun i => (c i : ℤ)) u) := fun c u => by
    have h₁ : (fun i => (c i : ℤ)) = ∑ i, c i • (Pi.single i 1 : Fin m → ℤ) := by
      ext j
      simp [Pi.single_apply]
    apply Additive.ofMul.injective
    show _ = F _
    rw [h₁, map_sum, Finset.sum_apply, map_sum, ofMul_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, Pi.smul_apply, map_nsmul, ofMul_pow]
    rfl
  choose a ha using fun u => onto (y u) (hy u)
  refine ⟨fun i => (bas.symm a i : ZMod k), fun u => ?_, fun c hc => ?_⟩
  · have : ∀ i, ∃ d : ℤ, ((bas.symm a i : ZMod k).val : ℤ) - bas.symm a i = k * d := fun i =>
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ k).1 (by simp)
    choose d hd using this
    rw [e, ← ha, hF]
    refine ⟨bas d u, ?_⟩
    have h₂ : (fun i => ((bas.symm a i : ZMod k).val : ℤ)) - bas.symm a = k • d := by
      ext i
      simpa using hd i
    have h₃ := congrFun (congrArg bas h₂) u
    rwa [map_sub, map_nsmul, LinearEquiv.apply_symm_apply] at h₃
  · choose d hd using fun u => (hF _ _).1 (((e _ u).symm.trans (hc u)).trans (ha u).symm)
    have h₂ : (fun i => ((c i).val : ℤ)) - bas.symm a = k • bas.symm d := by
      apply bas.injective
      rw [map_sub, map_nsmul, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      exact funext hd
    ext i
    have h₃ := congrArg (Int.cast : ℤ → ZMod k) (congrFun h₂ i)
    simpa [sub_eq_zero] using h₃

theorem sum_omega {h : ℕ} (a b : Fin n → (Fin h ⊕ Fin h → ℤ)) :
    ∑ i : (Fin n × Fin n) × Fin 3, 2 * omegaStd (![a i.1.1 + a i.1.2, a i.1.1, a i.1.2] i.2)
      (![b i.1.1 + b i.1.2, b i.1.1, b i.1.2] i.2) * (W i.1.1 i.1.2 * ![1, -1, -1] i.2) =
      (∑ u, ∑ v, (W + W.transpose) u v * omegaStd (a u) (b v)) * 2 := by
  have e : ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (a u) (b v) =
      ∑ uv : Fin n × Fin n, W uv.1 uv.2 * (omegaStd (a uv.1) (b uv.2) + omegaStd (a uv.2) (b uv.1)) := by
    simp only [Matrix.add_apply, Matrix.transpose_apply, add_mul, mul_add, Finset.sum_add_distrib]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type_right]
  have o : ∀ p q r t : Fin h ⊕ Fin h → ℤ, omegaStd (p + q) (r + t) =
      omegaStd p r + omegaStd p t + omegaStd q r + omegaStd q t := fun p q r t => by
    simp only [omegaStd, ← Finset.sum_add_distrib, Pi.add_apply]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e, Finset.sum_mul, Fintype.sum_prod_type (f := fun i : (Fin n × Fin n) × Fin 3 => _)]
  refine Finset.sum_congr rfl fun uv _ => ?_
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, o]
  ring

end Algebra

end GlobalTheory.SiegelPower

namespace GlobalTheory.SiegelPower

open GlobalTheory.CechPic

section Geometry

variable {S : Scheme.{0}} {A G : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj G] {Pb : LB (G2 A).left} (hP : Pb.IsLB)

def bi {T : Over S} (a b : T ⟶ A) : CechPic.Pic T.left := pull (lift a b).left (cls Pb hP)

abbrev sharp (Pb : LB (G2 A).left) {n : ℕ} (pr : Fin n → (G ⟶ A)) (W : Matrix (Fin n) (Fin n) ℤ) : LB G.left :=
  LB.LinComb Pb (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)

omit [GrpObj A] [IsCommMonObj A] in
theorem pull_bi {T T' : Over S} (h : T' ⟶ T) (a b : T ⟶ A) : pull h.left (bi hP a b) = bi hP (h ≫ a) (h ≫ b) := by
  rw [bi, ← pull_comp, ← Over.comp_left, comp_lift, bi]

variable {n : ℕ} (pr : Fin n → (G ⟶ A)) (W : Matrix (Fin n) (Fin n) ℤ)

omit [GrpObj A] [IsCommMonObj A] [GrpObj G] in
theorem pull_sharp {T : Over S} (a : T ⟶ G) (h : (sharp Pb pr W).IsLB) :
    pull a.left (cls _ h) = quad (bi hP) W (fun u => a ≫ pr u) := by
  rw [cls_linComb hP, map_sum]
  refine Finset.sum_congr rfl fun uv _ => ?_
  rw [map_zsmul]
  exact congrArg _ (pull_bi hP a _ _)

variable (hpr : ∀ u, IsMonHom (pr u))
  (hB : ∀ (T : Over S) (x x' y : T ⟶ A), bi hP (x * x') y = bi hP x y + bi hP x' y)
  (hs : ∀ (T : Over S) (x y : T ⟶ A), bi hP x y = bi hP y x)

include hpr hB in
theorem rigidified_sharp : Out.Rigidified G (sharp Pb pr W) := by
  have h : (sharp Pb pr W).IsLB := LB.isLB_linComb hP _ _
  refine (cls_eq_zero_iff (pull_isLB h _)).1 ((pull_sharp hP pr W η[G] h).trans ?_)
  have e : (fun u => η[G] ≫ pr u) = fun _ => 1 := funext fun u => by simp [Hom.one_def]
  rw [e]
  exact quad_one (hB _) W

include hpr hB hs in
theorem sym_sharp : Out.Sym G (sharp Pb pr W) := by
  have h : (sharp Pb pr W).IsLB := LB.isLB_linComb hP _ _
  intro s
  refine ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb h _ _)).1 ?_⟩
  have e : pull (GrpObj.inv : G ⟶ G).left (cls _ h) = cls _ h := by
    refine (pull_sharp hP pr W _ h).trans (Eq.trans ?_ ((pull_sharp hP pr W (𝟙 G) h).symm.trans (pull_id _)))
    rw [← quad_inv (hB _) (hs _) W fun u => 𝟙 G ≫ pr u]
    congr 1
    funext u
    rw [Category.id_comp, Hom.inv_def]
    exact (GrpObj.inv_hom (pr u))
  rw [cls_linComb h, Fin.sum_univ_two]
  show (1 : ℤ) • pull (_ ≫ _) _ + (-1 : ℤ) • pull (G.hom ⁻¹ᵁ ⊤).ι _ = 0
  rw [pull_comp, e, one_smul, neg_smul, one_smul, add_neg_cancel]

include hpr hB hs in
theorem exists_theta_sharp {k : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ k = 1) :
    ∃ θ : Out.ThetaGrp G (sharp Pb pr W) k T, θ.pt = x := by
  have h : (sharp Pb pr W).IsLB := LB.isLB_linComb hP _ _
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB G (sharp Pb pr W) k x), t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb h _ _)).1 ?_
    rw [cls_linComb h, Fin.sum_univ_two]
    show (k : ℤ) • pull (snd T G).left _ + (-(k : ℤ)) • pull ((fst T G ≫ x) * snd T G).left _ = 0
    rw [pull_sharp hP, pull_sharp hP]
    simp only [MonObj.mul_comp]
    refine smul_quad_mul (hB _) (hs _) W _ _ fun u => ?_
    rw [← MonObj.pow_comp, ← MonObj.comp_pow, hx, MonObj.comp_one, MonObj.one_comp]
  exact ⟨⟨x, t, ht⟩, rfl⟩

include hpr hB hs in
theorem kTriv_sharp (hu : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u)
    (hW : (W + W.transpose).det = 1)
    (hK : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (Pb.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1) :
    Out.KTriv G (sharp Pb pr W) := by
  have h : (sharp Pb pr W).IsLB := LB.isLB_linComb hP _ _
  intro R _ t x hx
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun p => ?_)
  obtain ⟨V, hV, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let T : Over S := Over.mk t
  let j : Out.overRes (T := T) V ⟶ T := Out.overResι (T := T) V
  have hD : (Out.translDiff G (sharp Pb pr W) x).IsLB := LB.isLB_linComb h _ _
  have h₀ : pull ((fst T G).left ⁻¹ᵁ V).ι (cls _ hD) = 0 := (cls_eq_zero_iff (pull_isLB hD _)).2 hc
  have h₁ : ∀ (Z : Over S) (r : Z ⟶ Out.overRes (T := T) V) (a : Z ⟶ G),
      quad (bi hP) W (fun u => (r ≫ j ≫ x) ≫ pr u) +
        ∑ v, bi hP (∏ u, ((r ≫ j ≫ x) ≫ pr u) ^ (W + W.transpose) u v) (a ≫ pr v) = 0 := fun Z r a => by
    have e := IsOpenImmersion.lift_fac ((fst T G).left ⁻¹ᵁ V).ι (lift (r ≫ j) a).left (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q.left z ∈ V) (lift_fst (r ≫ j) a)).mpr (r.left z).2)
    have e₁ : pull (lift (r ≫ j) a).left (cls _ hD) = 0 := by rw [← e, pull_comp, h₀, map_zero]
    have e₂ : cls _ hD = (1 : ℤ) • pull ((fst T G ≫ x) * snd T G).left (cls _ h) +
        (-1 : ℤ) • pull (snd T G).left (cls _ h) := (cls_linComb h _ _ hD).trans (Fin.sum_univ_two _)
    rw [e₂, one_smul, neg_smul, one_smul, map_add, map_neg, ← pull_comp, ← pull_comp, ← Over.comp_left,
      ← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, pull_sharp hP, pull_sharp hP, Category.assoc] at e₁
    simp only [MonObj.mul_comp] at e₁
    rw [quad_mul (hB _) (hs _)] at e₁
    rw [← e₁]
    abel
  have h₂ : ∀ v, ∏ u, ((j ≫ x) ≫ pr u) ^ (W + W.transpose) u v = 1 := fun v => by
    refine hK _ _ ((cls_eq_zero_iff (pull_isLB hP _)).1 ?_)
    obtain ⟨a, ha, -⟩ := hu _ (Pi.mulSingle v (fst A (Out.overRes (T := T) V)))
    have one : ∀ y : A ⊗ Out.overRes (T := T) V ⟶ A, bi hP y 1 = 0 := fun y => by rw [hs, biadd_one (hB _)]
    have e₁ := h₁ _ (snd A _) 1
    have e₂ := h₁ _ (snd A _) a
    simp only [MonObj.one_comp, one, Finset.sum_const_zero, add_zero] at e₁
    rw [e₁, zero_add, Finset.sum_eq_single v (fun w _ hw => by rw [ha, Pi.mulSingle_eq_of_ne hw, one]) (by simp),
      ha, Pi.mulSingle_eq_same] at e₂
    refine Eq.trans (congrArg (fun q => bi hP q (fst A _)) ?_) e₂
    refine (map_prod (preHom (G := A) (snd A (Out.overRes (T := T) V))) _ _).trans (Finset.prod_congr rfl fun u _ => ?_)
    rw [map_zpow, Category.assoc (snd A _)]
    rfl
  have h₃ : j ≫ x = j ≫ 1 := by
    refine (hu _ fun _ => 1).unique (eq_one_of_det _ hW _ h₂) fun u => ?_
    rw [MonObj.comp_one, MonObj.one_comp]
  exact congrArg (fun q => q.left) h₃

include hB hs in
theorem two_smul_sharp (h : (sharp Pb pr W).IsLB) : (2 : ℤ) • cls _ h =
    ∑ i : (Fin n × Fin n) × Fin 3, (W i.1.1 i.1.2 * ![1, -1, -1] i.2) •
      pull (![pr i.1.1 * pr i.1.2, pr i.1.1, pr i.1.2] i.2).left
        (cls _ (pull_isLB hP (lift (𝟙 A) (𝟙 A)).left)) := by
  rw [← pull_id (cls _ h)]
  refine (congrArg _ (pull_sharp hP pr W (𝟙 G) h)).trans ?_
  simp only [Category.id_comp]
  refine (two_smul_quad (hB _) (hs _) W pr).trans (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
  refine Eq.trans ?_ (pull_bi hP _ (𝟙 A) (𝟙 A)).symm
  rw [Category.comp_id]

end Geometry

theorem unitS_pull {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (x : Sp K ⟶ S) (s : S ⟶ Sp o)
    (β : o →+* K) (hβ : x ≫ s = spMap β) (u : oˣ) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn (Units.map β.toMonoidHom u) := by
  have e : unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) :=
    Units.ext (congrArg (fun k => k.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  rw [← e, ← hβ]
  rfl

end GlobalTheory.SiegelPower

namespace GlobalTheory.SiegelPower

open GlobalTheory.CechPic

theorem exists_tObj_isSharp : Out.Laws → Out.Laws2 → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k (b.ζ : o) s), Odd k → 3 ≤ k → b.ζ ^ k = 1 → c.Principal → ∃ t : TObj g k J b s, IsSharp W a bas t c := by
  intro hL _ h g W J a bas hW hbas k o _ b S s c hk h3 hζ hc
  have hG := hL.globalFns
  have hk0 : k ≠ 0 := by omega
  haveI : NeZero k := ⟨hk0⟩
  obtain ⟨G, _, pr, hab, hpr, hu⟩ : ∃ (G : Over S) (_ : GrpObj G) (pr : Fin 8 → (G ⟶ c.A)), IsAbelianScheme G ∧
      (∀ u, IsMonHom (pr u)) ∧ ∀ (T : Over S) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u :=
    ⟨Out.powObj c.A 8, inferInstance, Out.powPr c.A, AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 7, fun u => inferInstance,
      fun T y => ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
        fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩⟩
  have := hab.comm
  have hP := c.isLB
  have hD : c.diag.IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ c.A), bi hP (x * x') y = bi hP x y + bi hP x' y := fun T x x' y => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2
      (GlobalTheory.T.biadditive_of_trivial_on_axes hG S c.A c.diag c.ab hD hc.1 c.P hP c.rig₁ c.rig₂ T x x' y).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [bi]
    abel
  have hs : ∀ (T : Over S) (x y : T ⟶ c.A), bi hP x y = bi hP y x := fun T x y => by
    have e : cls c.P hP = bi hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
    rw [bi, e, pull_bi, lift_fst, lift_snd]
  have hLB : (sharp c.P pr W).IsLB := LB.isLB_linComb hP _ _
  have rigid := rigidified_sharp hP pr W hpr hB
  have sym := sym_sharp hP pr W hpr hB hs
  have ample : Out.RelAmple G (sharp c.P pr W) := GlobalTheory.T.relAmple_formBundle_power_of_posDef hG h k 8 o b.ζ S s c G pr W hpr hu hc.1 hW.1
  have ktriv := kTriv_sharp hP pr W hpr hB hs hu hW.2 hc.2
  have ext : ∀ {T : Over S} {x y : T ⟶ G}, (∀ u, x ≫ pr u = y ≫ pr u) → x = y := fun {T x y} e =>
    (hu T fun u => y ≫ pr u).unique e fun _ => rfl
  choose act hact using fun j => (hu G fun u => (List.ofFn fun v => pr v ^ a j u v).prod).exists
  choose pt hpt using fun i => (hu (Out.baseOver S) fun u => toUnit _ ≫ c.lev (bas (Pi.single i 1) u)).exists
  have hact' : ∀ j, IsMonHom (act j) := fun j => hL.rigidity S G G hab hab _ (ext fun u => by
    have e : ∀ v, η[G] ≫ pr v = 1 := fun v => by simp [Hom.one_def]
    rw [Category.assoc, hact, e, List.prod_ofFn]
    refine (map_prod (preHom (G := c.A) η[G]) _ _).trans (Finset.prod_eq_one fun v _ => ?_)
    rw [map_zpow]
    exact (congrArg (· ^ a j u v) (e v)).trans (one_zpow _))
  have tor : ∀ i, pt i ^ k = 1 := fun i => ext fun u => by
    rw [MonObj.pow_comp, hpt, ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one, MonObj.one_comp]
  have hpt' : ∀ {T : Over S} (r : T ⟶ Out.baseOver S) i u,
      (r ≫ pt i) ≫ pr u = toUnit T ≫ c.lev (bas (Pi.single i 1) u) := fun r i u => by
    rw [Category.assoc, hpt, comp_toUnit_assoc]
  have lin : ∀ {T : Over S} (p : Fin (2 * g) → (T ⟶ G)) (m : Fin (2 * g) → ℕ) u,
      Out.linComb p m ≫ pr u = ∏ i, (p i ≫ pr u) ^ m i := fun {T} p m u => by
    let F : (T ⟶ G) →* (T ⟶ c.A) := MonoidHom.mk' (· ≫ pr u) fun x y => MonObj.mul_comp x y _
    rw [Out.linComb, List.prod_ofFn]
    exact (map_prod F _ _).trans (Finset.prod_congr rfl fun i _ => map_pow F _ _)
  have geo : ∀ (K : Type) [Field K] (x : Sp K ⟶ S), ∃ β : o →+* K, x ≫ s = spMap β ∧ (k : K) ≠ 0 := fun K _ x =>
    ⟨(Spec.preimage (x ≫ s)).hom, (Spec.map_preimage _).symm, by
      simpa using (b.unit.map (Spec.preimage (x ≫ s)).hom).ne_zero⟩
  have bij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ G), y ^ k = 1 →
      ∃! cc : Ix g k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i)
        (fun i => (cc i).val) = y := fun K _ _ x y hy => by
    obtain ⟨β, hβ, -⟩ := geo K x
    obtain ⟨g₁, g₂, -⟩ := c.geom K x β (Units.map β.toMonoidHom b.ζ) hβ rfl
    refine (existsUnique_congr fun cc => ?_).1 (existsUnique_coord hk0 (fun e => toUnit (Over.mk x) ≫ c.lev e)
      (fun e e' => by rw [c.lev_add, MonObj.comp_mul]) g₁ g₂ bas (fun u => y ≫ pr u)
      fun u => by rw [← MonObj.pow_comp, hy, MonObj.one_comp])
    refine ⟨fun H => ext fun u => ?_, fun H u => ?_⟩
    · rw [lin, ← H u]
      simp only [hpt']
    · rw [← H, lin]
      simp only [hpt']
  have dim : SmoothOfRelativeDimension g G.hom := by
    refine smoothOfRelativeDimension_of_card hL.mulN G hab hLB rigid sym ample ktriv (n := k) (by omega)
      fun K _ _ x => ⟨(geo K x).choose_spec.2, ?_⟩
    let F : Ix g k → {y : Over.mk x ⟶ G // y ^ k = 1} := fun cc =>
      ⟨Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i) (fun i => (cc i).val), by
        rw [Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [← pow_mul, mul_comm, pow_mul, ← MonObj.comp_pow, tor, MonObj.comp_one, one_pow]⟩
    have hF : Function.Bijective F := (Function.bijective_iff_existsUnique F).2 fun y =>
      (existsUnique_congr fun cc => Subtype.ext_iff.symm).1 (bij K x y.1 y.2)
    rw [← Nat.card_eq_of_bijective F hF, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  let P : Out.PolAV S :=
    { A := G, isAb := hab, g := g, smoothDim := dim, L := sharp c.P pr W, isLB := hLB, rigid := rigid, sym := sym
      ample := ample, ktriv := ktriv }
  have pairing : ∀ i j, Out.WeilIs G (sharp c.P pr W) k (pt i) (pt j) (unitS s b.ζ ^ Out.stdSymp g i j) := by
    intro i j
    have th : ∀ i (p : (Out.baseOver S).left), ∃ V : (Out.baseOver S).left.Opens, p ∈ V ∧
        ∃ θ : Out.ThetaGrp G (sharp c.P pr W) k (Out.overRes V), θ.pt = Out.overResι V ≫ pt i := fun i p =>
      ⟨⊤, trivial, exists_theta_sharp hP pr W hpr hB hs _ (by rw [← MonObj.comp_pow, tor, MonObj.comp_one])⟩
    obtain ⟨d, hd⟩ := CommutatorPairing.exists_weilIs hG hab hLB (th i) (th j)
    have h₁ : d ^ k = 1 := pow_eq_one_of_weilIs hG P k (tor i) hd
    have h₂ : unitS s b.ζ ^ k = 1 := by
      unfold unitS unitOn
      rw [← map_pow, ← map_pow, hζ, map_one, map_one]
    let e : Γ(S, ⊤)ˣ := unitS s b.ζ ^ Out.stdSymp g i j
    let d' : Γ(S, ⊤)ˣ := d
    have h₁' : d' ^ k = 1 := h₁
    have h₃ : (d' * e⁻¹) ^ k = 1 := by
      rw [mul_pow, h₁', inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm _ (k : ℤ), zpow_mul, zpow_natCast, h₂, one_zpow,
        inv_one, _root_.mul_one]
    have h₄ : (d' * e⁻¹).val = 1 := by
      refine eq_one_of_geometric hk _ (by rw [← Units.val_pow_eq_pow_val, h₃, Units.val_one]) fun K _ _ x => ?_
      obtain ⟨β, hβ, hK⟩ := geo K x
      refine ⟨hK, ?_⟩
      let z : Kˣ := Units.map β.toMonoidHom b.ζ
      obtain ⟨-, -, g₃⟩ := c.geom K x β z hβ rfl
      let r : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
      let φ : Γ(S, ⊤)ˣ →* Γ(Sp K, ⊤)ˣ := Units.map x.appTop.hom.toMonoidHom
      have w : Out.WeilIs G (sharp c.P pr W) k (r ≫ pt i) (r ≫ pt j) (φ d') :=
        CommPairing.weilIs_pull hG hab hLB r hd
      have lv : ∀ i (q : (Fin 8 × Fin 8) × Fin 3), (r ≫ pt i) ≫ ![pr q.1.1 * pr q.1.2, pr q.1.1, pr q.1.2] q.2 =
          toUnit _ ≫ c.lev (![bas (Pi.single i 1) q.1.1 + bas (Pi.single i 1) q.1.2, bas (Pi.single i 1) q.1.1,
            bas (Pi.single i 1) q.1.2] q.2) := by
        rintro i ⟨uv, l⟩
        fin_cases l
        · show (r ≫ pt i) ≫ (_ * _) = toUnit _ ≫ c.lev (_ + _)
          rw [MonObj.comp_mul, hpt', hpt', c.lev_add, MonObj.comp_mul]
        · exact hpt' r i _
        · exact hpt' r i _
      have w₂ := pow_eq_prod hG hab hLB hD
        (fun q : (Fin 8 × Fin 8) × Fin 3 => ![pr q.1.1 * pr q.1.2, pr q.1.1, pr q.1.2] q.2)
        (by
          rintro ⟨uv, l⟩
          fin_cases l
          · exact inferInstanceAs (IsMonHom (lift (pr uv.1) (pr uv.2) ≫ μ[c.A]))
          · exact hpr _
          · exact hpr _) _ 2 (two_smul_sharp hP pr W hB hs hLB) w
        (fun q => by rw [lv, lv]; exact g₃ _ _)
      have hz : φ (unitS s b.ζ) = unitOn z := unitS_pull x s β hβ b.ζ
      have on : ∀ m : ℤ, unitOn (z ^ m) = unitOn z ^ m := fun m => map_zpow _ _ _
      have w₃ : φ d' ^ (2 : ℤ) = φ e ^ (2 : ℤ) := by
        refine w₂.trans ?_
        rw [map_zpow, hz, ← zpow_mul, ← hbas i j, ← sum_omega]
        refine Eq.trans (Finset.prod_congr rfl fun q _ => ?_) (prod_zpow_eq (unitOn z) _)
        exact (congrArg (· ^ _) (on _)).trans (zpow_mul _ _ _).symm
      have w₄ : φ (d' * e⁻¹) ^ 2 = 1 := by
        rw [map_mul, map_inv, ← zpow_natCast, mul_zpow, inv_zpow]
        exact mul_inv_eq_one.2 w₃
      exact congrArg Units.val w₄
    have h₅ : d' = e := mul_inv_eq_one.1 (Units.ext h₄)
    exact (congrArg (Out.WeilIs G (sharp c.P pr W) k (pt i) (pt j)) h₅).mp hd
  exact ⟨{ A := G, ab := hab, dim := dim, L := sharp c.P pr W, isLB := hLB, rigid := rigid, sym := sym, ample := ample
           ktriv := ktriv, pt := pt, torsion := tor, bij := bij, pairing := pairing, act := act, hom := hact' },
    pr, hpr, hu, PolBaseChange.lbIso_refl hLB, hact, fun i u => by
      refine (congrArg (fun q => q.left) (hpt i u)).trans ?_
      exact Category.id_comp _⟩

end GlobalTheory.SiegelPower

end
