import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RatioTranslate
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivOmegaStd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianSche
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStdSympZmod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionGeometricPointOfField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLift

section Algebra

open Matrix

theorem omegaStd_eq_dot {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    omegaStd a b = -(a ⬝ᵥ (Matrix.J (Fin g) ℤ *ᵥ b)) := by
  simp [omegaStd, Matrix.J, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.one_apply,
    Finset.sum_sub_distrib, Matrix.neg_apply]
  ring

theorem omegaStd_mulVec {g : ℕ} (T : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (a b : Fin g ⊕ Fin g → ℤ) :
    omegaStd (T *ᵥ a) (T *ᵥ b) = -(a ⬝ᵥ ((Tᵀ * Matrix.J (Fin g) ℤ * T) *ᵥ b)) := by
  rw [omegaStd_eq_dot, neg_inj, Matrix.mulVec_mulVec,
      ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc]

theorem exists_symplectic_hom {M g : ℕ} {G : Type} [CommGroup G] {R : Type} [CommRing R] [IsDomain R] {ζ : Rˣ}
    (hM : 0 < M) (hζ : IsPrimitiveRoot ζ M) (tors : ∀ x : G, x ^ M = 1)
    (card : ∀ d : ℕ, d ∣ M → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) (e : G →* G →* Rˣ) (alt : ∀ x, e x x = 1)
    (nd : ∀ x, (∀ y, e x y = 1) → x = 1) :
    ∃ l : (Fin g ⊕ Fin g → ℤ) → G, (∀ a b, l (a + b) = l a * l b) ∧ ∀ a b, e (l a) (l b) = ζ ^ omegaStd a b := by
  obtain ⟨x, hx⟩ := GlobalTheory.exists_stdSymp_of_alternating_pairing M g G R ζ hM hζ tors card e alt nd
  obtain ⟨bas, hb⟩ := exists_equiv_omegaStd (Matrix.toBilin' (Matrix.of (Out.stdSymp g))) (LinearEquiv.refl ℤ _)
    (fun i j => by simp [Matrix.toBilin'_single])
  refine ⟨fun a => ∏ i, x i ^ bas a i,
    fun a b => by simp only [map_add, Pi.add_apply, _root_.zpow_add, Finset.prod_mul_distrib], fun a b => ?_⟩
  rw [← hb, Matrix.toBilin'_apply]
  have s := map_prod (zpowersHom Rˣ ζ) (fun p : Fin (2 * g) × Fin (2 * g) =>
    Multiplicative.ofAdd (bas a p.1 * Out.stdSymp g p.1 p.2 * bas b p.2)) Finset.univ
  rw [← ofAdd_sum, Fintype.sum_prod_type, Fintype.prod_prod_type] at s
  refine Eq.trans ?_ s.symm
  rw [map_prod e, MonoidHom.finset_prod_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_zpow, map_zpow, MonoidHom.zpow_apply, hx, ← _root_.zpow_mul, ← _root_.zpow_mul]
  simp only [zpowersHom_apply, toAdd_ofAdd]
  congr 1
  ring

theorem exists_symplectic_change {G U : Type} [CommGroup G] [CommGroup U] {h n : ℕ} {z : U}
    (hz : IsPrimitiveRoot z n) (R : G → G → U → Prop) (hR : ∀ x y c c', R x y c → R x y c' → c = c')
    (l₀ l : (Fin h ⊕ Fin h → ℤ) → G) (add₀ : ∀ a b, l₀ (a + b) = l₀ a * l₀ b) (add : ∀ a b, l (a + b) = l a * l b)
    (tors : ∀ a, l₀ a ^ n = 1) (onto : ∀ a, ∃ b, l₀ b = l a) (w₀ : ∀ a b, R (l₀ a) (l₀ b) (z ^ omegaStd a b))
    (w : ∀ a b, R (l a) (l b) (z ^ omegaStd a b)) :
    ∃ Q : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ, (∀ a b, omegaStd (Q *ᵥ a) (Q *ᵥ b) = omegaStd a b) ∧
      ∀ a, l₀ (Q *ᵥ a) = l a := by
  let F₀ : (Fin h ⊕ Fin h → ℤ) →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (l₀ a))
    fun a b => by rw [add₀, ofMul_mul]
  let F : (Fin h ⊕ Fin h → ℤ) →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (l a))
    fun a b => by rw [add, ofMul_mul]
  choose t ht using fun i => onto (Pi.single i 1)
  let T : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ := Matrix.of fun i j => t j i
  have hT : ∀ a, l₀ (T *ᵥ a) = l a := fun a => by
    have e : F₀.toIntLinearMap ∘ₗ T.mulVecLin = F.toIntLinearMap := by
      refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
      show Additive.ofMul (l₀ (T *ᵥ Pi.single i 1)) = Additive.ofMul (l (Pi.single i 1))
      rw [← ht, Matrix.mulVec_single_one]
      rfl
    exact Additive.ofMul.injective (LinearMap.congr_fun e a)
  have hs : T.map (Int.castRingHom (ZMod n)) ∈ symplecticGroup (Fin h) (ZMod n) := by
    rw [SymplecticGroup.mem_iff', ← Matrix.map_J (Fin h) (Int.castRingHom (ZMod n)), ← Matrix.transpose_map,
      ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    have e := w₀ (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1)
    rw [hT, hT] at e
    have e' := hR _ _ _ _ e (w _ _)
    rw [← mul_inv_eq_one, ← _root_.zpow_sub, hz.zpow_eq_one_iff_dvd, omegaStd_mulVec, omegaStd_eq_dot,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero, Int.cast_neg, Int.cast_neg, neg_inj] at e'
    simpa only [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply, Matrix.map_apply, eq_intCast] using e'
  obtain ⟨Q, hQ⟩ := symplecticGroupMap_zmod_surjective (Fin h) n ⟨_, hs⟩
  have hQ' : Q.1.map (Int.castRingHom (ZMod n)) = T.map (Int.castRingHom (ZMod n)) := congrArg Subtype.val hQ
  refine ⟨Q.1, fun a b => by rw [omegaStd_mulVec, SymplecticGroup.mem_iff'.1 Q.2, omegaStd_eq_dot], fun a => ?_⟩
  have d : ∀ i j, (n : ℤ) ∣ Q.1 i j - T i j := fun i j => by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
    exact congrFun (congrFun hQ' i) j
  choose D hD using d
  have e : Q.1 = T + n • Matrix.of D := by
    ext i j
    simp [← hD]
  have e' : l₀ (n • (Matrix.of D *ᵥ a)) = 1 :=
    Additive.ofMul.injective ((map_nsmul F₀ n _).trans (congrArg Additive.ofMul (tors _)))
  rw [e, Matrix.add_mulVec, Matrix.smul_mulVec, add₀, e', _root_.mul_one, hT]

end Algebra

section Geometry

open GlobalTheory.CechPic

theorem cubWeil_level {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {L : RigLB A}
    {c : CubicalStr A L} {k l : ℕ} {T : Over S} {x z : T ⟶ A} {ζ : Γ(T.left, ⊤)ˣ}
    (h : UU.CubWeil c (k * l) x z ζ) (hx : x ^ k = 1) : UU.CubWeil c k x (z ^ l) ζ := by
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨ζ', h', -⟩ := UU.existsUnique_cubWeil c (N := k) (x := x) (y := z ^ l) hx
    (by rw [← pow_mul, mul_comm, h.2.1])
  have a := (UU.cubWeil_iff_weilIs hG hA h.2.1 h.1 _).1 h.symm
  have b := (UU.cubWeil_iff_weilIs hG hA h'.2.1 h'.1 _).1 h'.symm
  rw [Nat.cast_mul] at a
  rwa [inv_injective (PairingLevels.weilIs_value_eq hG hA L.isLB c.isGen a b)]

variable {K o : Type} [Field K] [CommRing o] {s : Sp K ⟶ Sp o} {h n : ℕ} {ζ : o}

theorem pull_mul_left (c : SiegPre h n ζ s) (hc : c.Principal) {T : Over (Sp K)} (x x' y : T ⟶ c.A) :
    pull (lift (x * x') y).left (cls c.P c.isLB) =
      pull (lift x y).left (cls c.P c.isLB) + pull (lift x' y).left (cls c.P c.isLB) := by
  have hL := c.isLB
  have hΘ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow K c.A c.diag c.P c.ab
    (pull_isLB hL _) hc.1 hL).1
  have ax₁ : ∀ u : T ⟶ c.A, pull (lift (1 : T ⟶ c.A) u).left (cls c.P hL) = 0 := fun u => by
    have e := (cls_eq_zero_iff (pull_isLB hL _)).2 c.rig₁
    rw [cls_pull hL] at e
    have e' := congrArg (pull u.left) e
    rwa [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at e'
  have ax₂ : ∀ u : T ⟶ c.A, pull (lift u (1 : T ⟶ c.A)).left (cls c.P hL) = 0 := fun u => by
    have e := (cls_eq_zero_iff (pull_isLB hL _)).2 c.rig₂
    rw [cls_pull hL] at e
    have e' := congrArg (pull u.left) e
    rwa [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at e'
  have lm : ∀ a b a' b' : T ⟶ c.A, lift a b * lift a' b' = lift (a * a') (b * b') := fun a b a' b' => by
    ext1 <;> simp [MonObj.mul_comp]
  have l1 : (1 : T ⟶ c.A ⊗ c.A) = lift 1 1 := by ext1 <;> simp [MonObj.one_comp]
  have lamv : ∀ a b : T ⟶ c.A, lam (cls _ hL) (lift a 1) (lift 1 b) = pull (lift a b).left (cls c.P hL) := fun a b => by
    rw [lam, lm, l1, ax₁, ax₁, ax₂, _root_.mul_one, _root_.one_mul, sub_zero, sub_zero, add_zero]
  have key := lam_mul_left hL hΘ (lift x 1) (lift x' 1) (lift 1 y)
  rwa [lm, _root_.mul_one, lamv, lamv, lamv] at key

theorem sq_eq_one_of_translDiff (c : SiegPre h n ζ s) (hc : c.Principal) {F : Type} [Field F] (t : Sp F ⟶ Sp K)
    (x : Over.mk t ⟶ c.A) (hx : AbLaw.Triv (Out.translDiff c.A c.diag x)) : x ^ 2 = 1 := by
  have hL := c.isLB
  have hD : c.diag.IsLB := pull_isLB hL _
  have sy : ∀ {T : Over (Sp K)} (a b : T ⟶ c.A),
      pull (lift a b).left (cls c.P hL) = pull (lift b a).left (cls c.P hL) := fun a b => by
    have e := (cls_eq_iff hL (pull_isLB hL _)).2 c.symm
    rw [cls_pull hL] at e
    conv_lhs => rw [e]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd]
  have dg : ∀ {T : Over (Sp K)} (a : T ⟶ c.A), pull a.left (cls _ hD) = pull (lift a a).left (cls c.P hL) := fun a => by
    refine (congrArg (pull a.left) (cls_pull hL _ hD)).trans ?_
    rw [← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have x0 : pull (lift x x).left (cls c.P hL) = 0 :=
    (cls_pull hL _ (pull_isLB hL _)).symm.trans ((cls_eq_zero_iff (pull_isLB hL _)).2
      (DVR.exists_gen_of_isLB_local (V := F) _ (pull_isLB hL _)))
  have e := (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).2 hx
  rw [cls_linComb hD, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
  rw [← Hom.mul_def] at e
  have e' := congrArg (pull (lift (snd c.A (Over.mk t)) (fst c.A (Over.mk t))).left) e
  rw [map_zero, map_add, map_neg, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul,
    lift_fst_assoc, lift_snd, dg, dg, pull_mul_left c hc, sy _ (_ * _), sy _ (_ * _), pull_mul_left c hc,
    pull_mul_left c hc, ← comp_lift, Over.comp_left, pull_comp, x0, map_zero] at e'
  refine hc.2 _ _ ((cls_eq_zero_iff (pull_isLB hL _)).1 ?_)
  rw [cls_pull hL, pow_two, MonObj.comp_mul, pull_mul_left c hc, ← e', sy (fst c.A (Over.mk t)) (_ ≫ x)]
  abel

end Geometry

theorem exists_lift {h n d : ℕ} {k : Type} [Field k] [IsAlgClosed k] (b : TBase k (n * d)) {ζ' : k}
    (hζ' : ζ' = (b.ζ : k) ^ d) (c : SiegPre h n ζ' (𝟙 (Sp k))) (hn : 3 ≤ n) (ho : Odd (n * d)) (hc : c.Principal) :
    ∃ C : SiegPre h (n * d) (b.ζ : k) (𝟙 (Sp k)), SRel C c d 1 (𝟙 _) := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have hG := hL.globalFns
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hN : ((n * d : ℕ) : k) ≠ 0 := b.unit.ne_zero
  have hN₀ : n * d ≠ 0 := fun e => hN (by rw [e, Nat.cast_zero])
  have hn₀ : n ≠ 0 := by omega
  have hd₀ : d ≠ 0 := right_ne_zero_of_mul hN₀
  have hz : IsPrimitiveRoot b.ζ (n * d) := IsPrimitiveRoot.coe_units_iff.1 (b.prim k (RingHom.id k))
  have hz₂ : IsPrimitiveRoot (b.ζ ^ 2) (n * d) := hz.pow_of_coprime 2 (Nat.coprime_two_left.2 ho)
  have hz₃ : IsPrimitiveRoot ((b.ζ ^ 2) ^ d) n := hz₂.pow (Nat.pos_of_ne_zero hN₀) (mul_comm n d)
  have hu : ∀ y : 𝟙_ (Over (Sp k)) ⟶ c.A, toUnit (Over.mk (𝟙 (Sp k))) ≫ y = y := fun y =>
    (congrArg (· ≫ y) (toUnit_unique _ (𝟙 (𝟙_ (Over (Sp k)))))).trans (Category.id_comp _)
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k (𝟙 _) (RingHom.id k) (b.ζ ^ d)
    ((Category.id_comp _).trans (Spec.map_id _).symm) (by rw [hζ']; rfl)
  simp only [hu] at g₁ g₂ g₃

  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k c.A c.ab
  have card := GlobalTheory.card_torsion_geometricPoint_of_field GlobalTheory.card_torsion_abelianVariety _ c.A c.ab g hg
  obtain rfl : h = g := by
    have hnk : (n : k) ≠ 0 := left_ne_zero_of_mul (by rwa [Nat.cast_mul] at hN)
    have : NeZero n := ⟨hn₀⟩
    let F : (Fin h ⊕ Fin h → ZMod n) → {y : Over.mk (𝟙 (Sp k)) ⟶ c.A // y ^ n = 1} :=
      fun a => ⟨c.lev fun i => (a i).val, c.lev_tors _⟩
    have hF : Function.Bijective F := by
      refine ⟨fun a a' e => ?_, fun y => ?_⟩
      · have e₁ : c.lev (fun i => (a i).val) = c.lev fun i => (a' i).val := congrArg Subtype.val e
        have e₂ := c.lev_add ((fun i => ((a i).val : ℤ)) - fun i => ((a' i).val : ℤ)) fun i => (a' i).val
        rw [sub_add_cancel, e₁] at e₂
        obtain ⟨v, hv⟩ := (g₁ _).1 (mul_eq_right.1 e₂.symm)
        funext i
        have := congrArg (fun z : ℤ => (z : ZMod n)) (congrFun hv i)
        simpa [sub_eq_zero] using this
      · obtain ⟨a, ha⟩ := g₂ y.1 y.2
        refine ⟨fun i => a i, Subtype.ext (Eq.trans ?_ ha)⟩
        have e₂ := c.lev_add (fun i => (((a i : ZMod n)).val : ℤ)) (n • fun i => a i / n)
        have e₃ : c.lev (n • fun i => a i / n) = 1 := (g₁ _).2 ⟨_, rfl⟩
        rw [e₃, _root_.mul_one] at e₂
        refine e₂.symm.trans (congrArg c.lev (funext fun i => ?_))
        simp only [ZMod.val_intCast, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
        exact Int.emod_add_mul_ediv _ _
    have e := (Nat.card_congr (Equiv.ofBijective F hF)).trans (card k (𝟙 _) n hnk)
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_fin] at e
    have := Nat.pow_right_injective (by omega : 2 ≤ n) e
    omega

  obtain ⟨L, hLM, ⟨cu⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta hL _ c.A c.ab c.diag hD
    (DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hD _))
    (GlobalTheory.exists_gen_theta_of_isAbelianScheme k c.A c.ab _ hD)
  have toW : ∀ {m : ℕ} {T : Over (Sp k)} {x y : T ⟶ c.A} {u}, UU.CubWeil cu m x y u →
      Out.WeilIs c.A c.diag m x y u := fun H => hLM ▸ (UU.cubWeil_iff_weilIs hG c.ab H.1 H.2.1 _).1 H
  obtain ⟨f₁, f₂, f₃⟩ := (GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow k c.A c.diag c.P c.ab
    hD hc.1 c.isLB).2 (n * d) (Nat.pos_of_ne_zero hN₀)
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ c.A) := (powMonoidHom (n * d)).ker
  have hH : ∀ x : H, x.1 ^ (n * d) = 1 := fun x => x.2
  have ex : ∀ x y : H, ∃ u : kˣ, UU.CubWeil cu (n * d) x.1 y.1 (unitOn u) := fun x y => by
    obtain ⟨u, hu, -⟩ := UU.existsUnique_cubWeil cu (hH x) (hH y)
    obtain ⟨w, rfl⟩ : ∃ w : kˣ, unitOn w = u :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.toMonoidHom u,
        Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of k)) u.val)⟩
    exact ⟨w, hu⟩
  choose w hw using ex
  have uq : ∀ x y u, UU.CubWeil cu (n * d) x.1 y.1 (unitOn u) → w x y = u := fun x y u H =>
    SiegelOfPolarised.unitOn_inj ((hw x y).unique H)
  have l : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y => uq _ _ _ (by
    have := (hw x y).mul_left (hw x' y)
    unfold unitOn at this ⊢
    rwa [map_mul])
  have sk : ∀ x y, w y x = (w x y)⁻¹ := fun x y => uq _ _ _ (by
    have := (hw x y).symm
    unfold unitOn at this ⊢
    rwa [map_inv])
  have u1 : unitOn (1 : kˣ) = 1 := map_one _
  let e : H →* H →* kˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) fun y y' => by
    rw [sk (y * y'), l, mul_inv, ← sk, ← sk]) fun x x' => MonoidHom.ext fun y => l x x' y
  obtain ⟨l₁, add₁, w₁⟩ := exists_symplectic_hom (g := h) (Nat.pos_of_ne_zero hN₀) hz₂
    (fun x => Subtype.ext (hH x)) (fun m hm => by
      obtain ⟨r, hr⟩ := hm
      have hm : (m : k) ≠ 0 := left_ne_zero_of_mul (by rwa [hr, Nat.cast_mul] at hN)
      refine Eq.trans (Nat.card_congr ?_) (card k (𝟙 _) m hm)
      exact ⟨fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩, fun x => ⟨⟨x.1, show x.1 ^ (n * d) = 1 by
        rw [hr, pow_mul, x.2, one_pow]⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩)
    e (fun x => uq _ _ _ (u1 ▸ UU.cubWeil_self cu (hH x))) (fun x hx => Subtype.ext (by
      have t := GlobalTheory.CubNondeg.main hL _ c.A c.ab L cu k (𝟙 _) (n * d) hN f₁ f₂ f₃ x.1 (hH x) fun y hy => by
        have := hw x ⟨y, hy⟩
        rwa [show w x ⟨y, hy⟩ = 1 from hx ⟨y, hy⟩, u1] at this
      rw [hLM] at t
      have s₂ : x.1 ^ 2 = 1 := sq_eq_one_of_translDiff c hc (𝟙 _) x.1 t
      exact (pow_eq_one_iff_of_coprime (Nat.coprime_two_left.2 ho)).1 ⟨s₂, hH x⟩))
  let l₂ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp k)) ⟶ c.A) := fun a => (l₁ a).1
  have add₂ : ∀ a a', l₂ (a + a') = l₂ a * l₂ a' := fun a a' => congrArg Subtype.val (add₁ a a')
  have tors₂ : ∀ a, l₂ a ^ (n * d) = 1 := fun a => hH _
  have w₂ : ∀ a a', UU.CubWeil cu (n * d) (l₂ a) (l₂ a') (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) := fun a a' =>
    (show w (l₁ a) (l₁ a') = _ from w₁ a a') ▸ hw (l₁ a) (l₁ a')

  have mk : ∀ lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp k)) ⟶ c.A), (∀ a a', lev (a + a') = lev a * lev a') →
      (∀ a a', UU.CubWeil cu (n * d) (lev a) (lev a') (unitOn ((b.ζ ^ 2) ^ omegaStd a a'))) →
      ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ Sp k) (β : k →+* k') (z : k'ˣ),
        x ≫ 𝟙 _ = spMap β → (z : k') = β b.ζ →
        (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ v, a = (n * d) • v)) ∧
        (∀ y : Over.mk x ⟶ c.A, y ^ (n * d) = 1 → ∃ a, toUnit _ ≫ lev a = y) ∧
        ∀ a a', Out.WeilIs c.A c.diag (n * d : ℕ) (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev a')
          (unitOn (z ^ (2 * omegaStd a a'))) := by
    intro lev add weil k' _ _ x β z hx hzz
    obtain rfl : x = spMap β := (Category.comp_id _).symm.trans hx
    obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hzz
    have tors : ∀ a, lev a ^ (n * d) = 1 := fun a => (weil a a).1
    have hz' : IsPrimitiveRoot (Units.map β.toMonoidHom (b.ζ ^ 2)) (n * d) :=
      hz₂.map_of_injective (Units.map_injective β.injective)
    have hk' : ((n * d : ℕ) : k') ≠ 0 := by rw [← map_natCast β]; exact (map_ne_zero β).2 hN
    have W : ∀ a a', UU.CubWeil cu (n * d) (toUnit (Over.mk (spMap β)) ≫ lev a) (toUnit _ ≫ lev a')
        (unitOn (Units.map β.toMonoidHom (b.ζ ^ 2) ^ omegaStd a a')) := fun a a' => by
      have H := (weil a a').comp (toUnit (Over.mk (spMap β)))
      have e : Units.map (toUnit (Over.mk (spMap β))).left.appTop.hom.toMonoidHom
          (unitOn ((b.ζ ^ 2) ^ omegaStd a a')) = unitOn (Units.map β.toMonoidHom ((b.ζ ^ 2) ^ omegaStd a a')) :=
        Units.ext (congrArg (fun q => q.hom ((b.ζ ^ 2) ^ omegaStd a a').val)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
      rw [e, map_zpow] at H
      exact H
    have ker : ∀ a, toUnit (Over.mk (spMap β)) ≫ lev a = 1 → ∃ v, a = (n * d) • v := fun a ha =>
      SiegelOfPolarised.exists_smul_of_dvd fun a' => by
        have w₁ := W a a'
        rw [ha] at w₁
        have e := SiegelOfPolarised.unitOn_inj
          ((w₁.unique (UU.cubWeil_one_left cu w₁.2.1)).trans (map_one _).symm)
        exact (hz'.zpow_eq_one_iff_dvd _).1 e
    refine ⟨fun a => ⟨ker a, ?_⟩, SiegelOfPolarised.onto_torsion hN₀ _ (fun a b => by rw [add, MonObj.comp_mul])
      (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one]) ker ?_, fun a a' => ?_⟩
    · rintro ⟨v, rfl⟩
      have pw : ∀ m : ℕ, lev (m • v) = lev v ^ m := fun m => by
        induction m with
        | zero => rw [zero_smul, pow_zero]; exact mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
        | succ m ih => rw [succ_nsmul, add, ih, pow_succ]
      rw [pw, tors, MonObj.comp_one]
    · rw [card k' _ _ hk']
      simp [two_mul]
    · have H := toW (W a a')
      rwa [map_pow, ← zpow_ofNat, ← zpow_mul] at H
  obtain ⟨k₁, k₂, -⟩ := mk l₂ add₂ w₂ k (𝟙 _) (RingHom.id k) b.ζ
    ((Category.id_comp _).trans (Spec.map_id _).symm) rfl
  simp only [hu] at k₁ k₂
  have pw : ∀ (m : ℕ) v, l₂ (m • v) = l₂ v ^ m := fun m v => by
    induction m with
    | zero => rw [zero_smul, pow_zero]; exact mul_eq_left.1 ((add₂ 0 0).symm.trans (by rw [add_zero]))
    | succ m ih => rw [succ_nsmul, add₂, ih, pow_succ]
  have tors₃ : ∀ a, (l₂ a ^ d) ^ n = 1 := fun a => by rw [← pow_mul, mul_comm, tors₂]
  obtain ⟨Q, hQ, hQl⟩ := exists_symplectic_change hz₃ (fun x y u => Out.WeilIs c.A c.diag n x y (unitOn u))
    (fun x y u u' H H' => SiegelOfPolarised.unitOn_inj (CommutatorPairing.weilIs_unique hG c.ab hD H H'))
    (fun a => l₂ a ^ d) c.lev (fun a a' => by rw [add₂, mul_pow]) c.lev_add tors₃
    (fun a => by
      obtain ⟨v, hv⟩ := k₂ (c.lev a) (show c.lev a ^ (n * d) = 1 by rw [pow_mul, c.lev_tors, one_pow])
      have hv' : l₂ v = c.lev a := hv
      obtain ⟨v', hv''⟩ := (k₁ (n • v)).1 (show l₂ (n • v) = 1 by rw [pw, hv', c.lev_tors])
      rw [mul_smul] at hv''
      refine ⟨v', ?_⟩
      rw [← pw, ← smul_right_injective _ hn₀ hv'', hv'])
    (fun a a' => by
      have H := toW (cubWeil_level c.ab ((w₂ a a').pow_left d) (tors₃ a))
      unfold unitOn at H ⊢
      rwa [← map_pow, ← zpow_natCast (_ ^ omegaStd a a'), ← zpow_mul, mul_comm (omegaStd a a'), zpow_mul,
        zpow_natCast] at H)
    (fun a a' => by
      have H := g₃ a a'
      rwa [zpow_mul, zpow_ofNat, pow_right_comm] at H)
  have add₄ : ∀ a a', l₂ (Q.mulVec (a + a')) = l₂ (Q.mulVec a) * l₂ (Q.mulVec a') := fun a a' => by
    rw [Matrix.mulVec_add, add₂]
  refine ⟨{ A := c.A
            ab := c.ab
            P := c.P
            isLB := c.isLB
            rig₁ := c.rig₁
            rig₂ := c.rig₂
            symm := c.symm
            lev := fun a => l₂ (Q.mulVec a)
            lev_add := add₄
            lev_tors := fun a => tors₂ _
            geom := mk _ add₄ fun a a' => hQ a a' ▸ w₂ _ _ },
    𝟙 _, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl c.A) (inferInstanceAs (IsMonHom (𝟙 c.A))),
    ⟨𝟙 _, ⟨by simp, by simp⟩, ?_⟩, fun a => ?_⟩
  · exact (CechPic.cls_eq_iff c.isLB (pull_isLB c.isLB _)).1
      ((CechPic.pull_id _).symm.trans (CechPic.cls_pull c.isLB _ _).symm)
  · show (l₂ (Q.mulVec a) ^ d).left ≫ 𝟙 _ = 𝟙 _ ≫ (c.lev a ^ 1).left
    rw [hQl, pow_one, Category.comp_id, Category.id_comp]

theorem exists_level_lift : ∀ (h n N : ℕ) (k : Type) [Field k] [IsAlgClosed k] (b : TBase k N) (c : SiegPre h n ((b.ζ : k) ^ (N / n)) (𝟙 (Sp k))), 3 ≤ n → Odd N → n ∣ N → c.Principal → ∃ C : SiegPre h N (b.ζ : k) (𝟙 (Sp k)), SRel C c (N / n) 1 (𝟙 _) := by
  rintro h n N k _ _ b c hn ho ⟨d, rfl⟩ hc
  have e : n * d / n = d := Nat.mul_div_cancel_left d (by omega)
  obtain ⟨C, hC⟩ := exists_lift b (congrArg ((b.ζ : k) ^ ·) e) c hn ho hc
  refine ⟨C, ?_⟩
  convert hC using 1

end GlobalTheory.SiegLift
