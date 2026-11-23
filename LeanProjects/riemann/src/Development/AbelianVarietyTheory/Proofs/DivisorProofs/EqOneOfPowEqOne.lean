import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.TowerWeil

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem eq_one_of_pow_eq_one {R : Type} [CommRing R] {J : Ideal R} (hJ : J ≤ Ideal.jacobson ⊥) {n : ℕ}
    (hn : IsUnit (n : R)) {w : R} (hw : w ^ n = 1) (h : w - 1 ∈ J) : w = 1 := by
  have hs : (∑ i ∈ Finset.range n, w ^ i) - n ∈ J := by
    have e : (∑ i ∈ Finset.range n, w ^ i) - n = ∑ i ∈ Finset.range n, (w ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow w 1 i
    rw [one_pow] at hq
    rw [hq]
    exact J.mul_mem_right _ h
  obtain ⟨v, hv⟩ := hn
  have hu : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    have e : (∑ i ∈ Finset.range n, w ^ i) = (v : R) * (((∑ i ∈ Finset.range n, w ^ i) - n) * (↑v⁻¹ : R) + 1) := by
      rw [mul_add, mul_comm ((∑ i ∈ Finset.range n, w ^ i) - n), ← _root_.mul_assoc, Units.mul_inv, _root_.one_mul, _root_.mul_one, hv]
      ring
    rw [e]
    exact v.isUnit.mul ((Ideal.mem_jacobson_bot.1 (hJ hs)) _)
  have h0 : (∑ i ∈ Finset.range n, w ^ i) * (w - 1) = 0 := by rw [geom_sum_mul, hw, sub_self]
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)

theorem map_unitOn {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') (c : Rˣ) :
    Units.map (spMap j).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom (c : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem unitOn_bijective {R : Type} [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem exists_weilIs_root {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (P : LB (G2 A).left) (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) (N : ℕ) (hN : 0 < N) {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) :
    ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N x y c₀ := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP r₁ r₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP r₁ r₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ z : T ⟶ A, z ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag hP hB hB' (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts x hx) (lifts y hy)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts 1 (one_pow N)) (lifts y hy)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG hA hD h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (x ^ (m + 1)) y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ x (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hD ih hc₀
  have hp := pw (N - 1)
  rw [Nat.sub_add_cancel hN, hx] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG hA hD hp (e₁' ▸ hc₁), hc₀⟩

theorem unitOn_pow' {R : Type} [CommRing R] (u : Rˣ) (m : ℕ) : unitOn (u ^ m) = unitOn u ^ m := by
  unfold unitOn; exact map_pow _ u m

theorem unitOn_zpow' {R : Type} [CommRing R] (u : Rˣ) (m : ℤ) : unitOn (u ^ m) = unitOn u ^ m := by
  unfold unitOn; exact map_zpow _ u m

theorem unitOn_one' {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := by
  unfold unitOn; exact map_one _

theorem exists_spMap {R K : Type} [CommRing R] [CommRing K] (x : Sp K ⟶ Sp R) : ∃ f : R →+* K, spMap f = x :=
  ⟨(Spec.preimage x).hom, by simp [spMap]⟩

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap f' ≫ spMap f = spMap (f'.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem weil_geom : ∀ g n : ℕ, 3 ≤ n → Odd n → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (β : cycAway n →+* R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp R)) ⟶ A)), (∀ a a', lev (a + a') = lev a * lev a') → (∀ a, lev a ^ n = 1) → ∀ (c₀ : SiegPre g n (zetaAway n) (spMap ((Ideal.Quotient.mk (I ^ (0 + 1))).comp β))), c₀.Principal → ∀ (φ : c₀.A.left ⟶ A.left) (φ₂ : (G2 c₀.A).left ⟶ (G2 A).left), IsGrpPullback c₀.A A (spMap (Ideal.Quotient.mk (I ^ (0 + 1)))) φ → IsSquare φ φ₂ → LBIso c₀.P (P.pull φ₂) → (∀ a, (c₀.lev a).left ≫ φ = spMap (Ideal.Quotient.mk (I ^ (0 + 1))) ≫ (lev a).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R) (ψ : cycAway n →+* k) (z : kˣ), x ≫ spMap β = spMap ψ → (z : k) = ψ (zetaAway n) → ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b) (unitOn (z ^ (2 * omegaStd a b))) := by
  intro g n hn3 hodd R _ _ I hI β A _ _ hA P hP r₁ r₂ hsym hamp lev ladd ltors c₀ hc₀ φ φ₂ hpb hsq hiso hlev k _ _ x ψ z hx hz a b
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hn0 : n ≠ 0 := by omega
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨u, hun, hu⟩ := exists_weilIs_root hA P hP r₁ r₂ hamp n (by omega) (ltors a) (ltors b)
  obtain ⟨uR, rfl⟩ : ∃ uR : Rˣ, unitOn uR = u := unitOn_bijective.2 u
  have hz1 : zetaAway n ^ n = 1 := Subtype.ext (Complex.isPrimitiveRoot_exp n hn0).pow_eq_one
  let ζR : Rˣ := Units.map β.toMonoidHom (cycBase hn0).ζ
  have hζR : (ζR : R) = β (zetaAway n) := rfl
  have hζn : ζR ^ n = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζR, ← map_pow, hz1, map_one, Units.val_one])
  have huR : uR ^ n = 1 := unitOn_bijective.1 (by rw [unitOn_pow', hun, unitOn_one'])
  have hnR : IsUnit (n : R) := by simpa using (isUnit_natCast hn0).map β
  set e : ℤ := 2 * omegaStd a b with he

  have key : uR = ζR ^ e := by
    let w : Rˣ := uR * (ζR ^ e)⁻¹
    have hw : w ^ n = 1 := by
      have h1 : (ζR ^ e) ^ n = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζn, one_zpow]
      rw [mul_pow, inv_pow, h1, huR, inv_one, _root_.mul_one]
    let mk := Ideal.Quotient.mk (I ^ (0 + 1))
    have hmk : Units.map mk.toMonoidHom w = 1 := by
      refine unitOn_bijective.1 ?_
      rw [unitOn_one']
      refine GlobalTheory.ObjTheta.root_ext (n := n) ?_ (by rw [← unitOn_pow', ← map_pow, hw, map_one, unitOn_one']) (one_pow n) ?_
      · have := (hnR.map mk).map (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (0 + 1)))).inv.hom
        rwa [map_natCast, map_natCast] at this
      · intro K _ _ x₀
        obtain ⟨φ₀, rfl⟩ := exists_spMap x₀
        rw [map_unitOn, map_one, ← unitOn_one']
        congr 1
        let z₀ : Kˣ := Units.map (φ₀.comp mk).toMonoidHom ζR
        obtain ⟨-, -, g₃⟩ := c₀.geom K (spMap φ₀) (φ₀.comp (mk.comp β)) z₀ (spMap_comp' _ _) rfl
        have W₀ := g₃ a b
        have W₁ := (GlobalTheory.weilIs_grpPullback_of_comm (Sp R) (Sp (R ⧸ I ^ (0 + 1))) A c₀.A (spMap mk) φ
          (P.pull (lift (𝟙 A) (𝟙 A)).left) (c₀.P.pull (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) hD (pull_isLB c₀.isLB _) hpb
          (SiegelPull.diag_iso hsq hiso) (Over.mk (spMap φ₀)) n _ _
          (toUnit (Over.mk (spMap φ₀ ≫ spMap mk)) ≫ lev a) (toUnit (Over.mk (spMap φ₀ ≫ spMap mk)) ≫ lev b) _
          (by simp [hlev]) (by simp [hlev])).1 W₀
        have W₂ := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk (spMap φ₀ ≫ spMap mk))) hu
        have E := CommutatorPairing.weilIs_unique hG hA hD W₂ W₁
        have h₁ : (toUnit (Over.mk (spMap φ₀ ≫ spMap mk))).left = spMap (φ₀.comp mk) := by simp [spMap_comp']
        rw [h₁, map_unitOn] at E
        have E' := unitOn_bijective.1 E
        have h₂ : Units.map φ₀.toMonoidHom (Units.map mk.toMonoidHom w) = Units.map (φ₀.comp mk).toMonoidHom w := by
          ext; rfl
        rw [h₂, map_mul, map_inv, map_zpow, show Units.map (φ₀.comp mk).toMonoidHom uR = z₀ ^ e from E']
        exact mul_inv_cancel _
    have hmem : (w : R) - 1 ∈ I := by
      have e₁ := congrArg (fun q : (R ⧸ I ^ (0 + 1))ˣ => (q : R ⧸ I ^ (0 + 1))) hmk
      simp only [Units.coe_map, Units.val_one, MonoidHom.coe_coe] at e₁
      have e₂ : mk (w : R) = mk 1 := by rw [map_one]; exact e₁
      have := Ideal.Quotient.eq.1 e₂
      simpa using this
    have hw1 : (w : R) = 1 := eq_one_of_pow_eq_one (IsAdicComplete.le_jacobson_bot I) hnR
      (by rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]) hmem
    exact mul_inv_eq_one.1 (Units.ext hw1)
  have hpull := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk x)) hu
  obtain ⟨φx, rfl⟩ := exists_spMap x
  have hφ : φx.comp β = ψ := by
    rw [spMap_comp'] at hx
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 hx)
  have hval : Units.map (toUnit (Over.mk (spMap φx))).left.appTop.hom.toMonoidHom (unitOn uR) = unitOn (z ^ e) := by
    have h₁ : (toUnit (Over.mk (spMap φx))).left = spMap φx := by simp
    rw [h₁, map_unitOn, key, map_zpow]
    congr 2
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hz, ← hφ, hζR, RingHom.comp_apply]
  rw [← hval]
  exact hpull

end GlobalTheory.TowerWeil
