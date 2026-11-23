import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelOfPolarised

open PrimNorm

section Bundle

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem prod_lam {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum A (x2 A) I.down).left) ^
      ((-1 : ℤ) ^ (2 - I.down.card)) = diff₂ (fun q : T ⟶ A => h q.left) x y :=
  (prod_square (lift x y) (fst A A) (snd A A) h).trans (by rw [lift_fst, lift_snd])

theorem hasGen_lam_pull (hL : L.IsLB) {T : Over S} (x y : T ⟶ A) (h : diff₂ (ptCls L T) x y = 1) :
    ∃ t : ((abelian₂ A L).pull (lift x y).left).Gen, t.IsGen :=
  hasGen_nested hL _ _ _ _ (by
    rw [Fintype.prod_unique, zpow_one]
    exact (prod_lam x y (cls L)).trans h)

theorem lbIso_lam_pull (hL : L.IsLB) (x y : A ⊗ A ⟶ A)
    (h : diff₂ (ptCls L _) x y = diff₂ (ptCls L _) (fst A A) (snd A A)) :
    LBIso (abelian₂ A L) ((abelian₂ A L).pull (lift x y).left) :=
  LBIso.symm (lbIso_nested hL _ _ _ _ _ _ (by
    rw [Fintype.prod_unique, zpow_one]
    exact (prod_lam x y (cls L)).trans (h.trans (prod_square_id _ _ (cls L)).symm)))

theorem eq_one_of_lam (hL : L.IsLB) (hK : Out.KTriv A L) {T : Over S} (x : T ⟶ A)
    (h : ∃ t : ((abelian₂ A L).pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  have H := ((KerPow.pull_iff _ _ _).1 h).pull (β_ T A).hom.left
    (φ' := fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T A ≫ x) (snd T A)).left ≫ (psum A (x2 A) I.down).left)
    (fun I => by
      rw [← Category.assoc, ← Over.comp_left, comp_lift, braiding_hom_snd_assoc, braiding_hom_fst])
  have H₁ : KerPow.LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (lift (fst T A ≫ x) (snd T A)).left ≫ (psum A (x2 A) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun p => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have H₂ := BoxKernel.locGen_base hL (fst T A).left (K := Fin 2) ![(1 : T ⟶ A).left, x.left] ![1, -1]
  refine KerPow.eq_one_of_locGen hK x (H₁.comb hL H₂ fun U _ g => ?_)
  rw [prod_lam, Fin.prod_univ_two, Fin.prod_univ_two]
  show _ * (g (fst T A ≫ (1 : T ⟶ A)).left ^ (1 : ℤ) * g (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    g ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * g (snd T A).left ^ (-1 : ℤ)
  rw [MonObj.comp_one, diff₂]
  apply Additive.ofMul.injective
  simp only [zpow_neg, zpow_one, ofMul_mul, ofMul_inv]
  abel

end Bundle

theorem lbIso_diag (hL : Out.Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) :
    LBIso (lbPow P.L 2) ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left) := by
  refine LBIso.symm (lbIso_nested P.isLB _ _ _ _ _ _ ?_)
  rw [Fintype.prod_unique, zpow_one]
  refine (prod_lam _ _ (cls P.L)).trans ?_
  rw [Fintype.prod_unique]
  have a := (hasGen_iff P.isLB _ _).1 (hL.mulPull S P 2)
  have b := (hasGen_iff P.isLB _ _).1 (MulPull.HasGen.pull (K := PUnit) P.rigid (toUnit P.A).left)
  rw [Fin.prod_univ_two] at a
  rw [Fintype.prod_unique, zpow_one] at b
  have a' : cls P.L (𝟙 P.A.left) ^ (4 : ℤ) * cls P.L (𝟙 P.A ^ 2).left ^ (-1 : ℤ) = 1 := a
  have b' : cls P.L (1 : P.A ⟶ P.A).left = 1 := b
  rw [pow_two, zpow_neg, zpow_one, mul_inv_eq_one] at a'
  show cls P.L (𝟙 P.A * 𝟙 P.A).left * (cls P.L (𝟙 P.A.left))⁻¹ * (cls P.L (𝟙 P.A.left))⁻¹ *
    cls P.L (1 : P.A ⟶ P.A).left = cls P.L (𝟙 P.A.left) ^ (2 : ℤ)
  rw [← a', b']
  group

theorem weilIs_of_lbIso_pow (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L N : LB A.left} (hL : L.IsLB) (hN : N.IsLB) {d : ℕ} (hw : LBIso (lbPow L d) N) {n : ℤ} {T : Over S}
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs A L n x y c) : Out.WeilIs A N n x y (c ^ d) := by
  have e : CechPic.cls N hN = d • CechPic.cls L hL :=
    ((CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) hN).2 hw).symm.trans (CechPic.cls_lbPow hL d _)
  have up : ∀ {Z : Over S} (θ : Out.ThetaGrp A L n Z), ∃ θ' : Out.ThetaGrp A N n Z, θ'.pt = θ.pt := fun {Z} θ => by
    have z := (CechPic.cls_eq_zero_iff (N := Out.thetaLB A L n θ.pt) (LB.isLB_linComb hL _ _)).2 ⟨θ.φ, θ.isGen⟩
    have z' := (CechPic.cls_linComb hL _ _ _).symm.trans z
    obtain ⟨t, ht⟩ := (CechPic.cls_eq_zero_iff (N := Out.thetaLB A N n θ.pt) (LB.isLB_linComb hN _ _)).1
      ((CechPic.cls_linComb hN _ _ _).trans (by
        simp only [e, map_nsmul, smul_comm _ d]
        rw [← Finset.smul_sum, z', smul_zero]))
    exact ⟨⟨θ.pt, t, ht⟩, rfl⟩
  obtain ⟨c', hc'⟩ := CommutatorPairing.exists_weilIs (k := n) (x := x) (y := y) hG hA hN
    (fun p => by
      obtain ⟨V, hV, ⟨θ, -, eθ, -⟩, -⟩ := h p
      obtain ⟨θ', e'⟩ := up θ
      exact ⟨V, hV, θ', e'.trans eθ⟩)
    (fun p => by
      obtain ⟨V, hV, ⟨θ₀, θ, -, eθ⟩, -⟩ := h p
      obtain ⟨θ', e'⟩ := up θ
      exact ⟨V, hV, θ', e'.trans eθ⟩)
  have hw' : LBIso (lbPow L d) (N.pull (𝟙 A : A ⟶ A).left) :=
    (CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hN _ _)).1
      (((CechPic.cls_eq_iff _ hN).2 hw).trans (CechPic.pull_id _).symm)
  have := (weilIs_along_hom hG S A A (𝟙 A) L N d n T x y c c' hA hA hL hN inferInstance hw'
    (by rwa [Category.comp_id, Category.comp_id])).2 h
  rwa [← this]

theorem unitOn_inj {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := fun _ _ h =>
  Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).1 (congrArg Units.val h))

theorem exists_smul_of_dvd {h k : ℕ} {a : Fin h ⊕ Fin h → ℤ} (H : ∀ b, (k : ℤ) ∣ omegaStd a b) : ∃ b, a = k • b := by
  have d : ∀ i, (k : ℤ) ∣ a i := by
    rintro (i | i)
    · simpa [omegaStd, Pi.single_apply] using H (Pi.single (.inr i) 1)
    · simpa [omegaStd, Pi.single_apply] using H (Pi.single (.inl i) 1)
  choose b hb using d
  exact ⟨b, funext fun i => by simpa using hb i⟩

theorem onto_torsion {I G : Type} [Fintype I] [Group G] {k : ℕ} (hk : k ≠ 0) (f : (I → ℤ) → G)
    (add : ∀ a b, f (a + b) = f a * f b) (tors : ∀ a, f a ^ k = 1) (ker : ∀ a, f a = 1 → ∃ b, a = k • b)
    (card : Nat.card {g : G // g ^ k = 1} = k ^ Fintype.card I) (g : G) (hg : g ^ k = 1) : ∃ a, f a = g := by
  haveI : NeZero k := ⟨hk⟩
  let F : (I → ZMod k) → {g : G // g ^ k = 1} := fun c => ⟨f fun i => (c i).val, tors _⟩
  have hF : Function.Injective F := fun c c' e => by
    have e₁ : f (fun i => (c i).val) = f fun i => (c' i).val := congrArg Subtype.val e
    have e₂ := add ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => (c' i).val
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := ker _ (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun z : ℤ => (z : ZMod k)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have : Finite {g : G // g ^ k = 1} := Nat.finite_of_card_ne_zero (by rw [card]; exact pow_ne_zero _ hk)
  obtain ⟨c, hc⟩ := (hF.bijective_of_nat_card_le (by rw [card, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card])).2 ⟨g, hg⟩
  exact ⟨_, congrArg Subtype.val hc⟩

end GlobalTheory.SiegelOfPolarised

namespace GlobalTheory

open SiegelOfPolarised PrimNorm in

theorem exists_siegPre_of_polAV : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (K : Type) [Field K] (em : o →+* K) (h k : ℕ) (ζ : o) (ze : Kˣ) (P : Out.PolAV (Sp K)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K)) ⟶ P.A)), P.g = h → (k : K) ≠ 0 → (ze : K) = em ζ → IsPrimitiveRoot ze k → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ x y, Out.WeilIs P.A P.L k (lev x) (lev y) (unitOn (ze ^ omegaStd x y))) → ∃ (c : SiegPre h k ζ (spMap em)) (φ : c.A ≅ P.A), IsMonHom φ.hom ∧ c.Principal ∧ LBIso c.P ((abelian₂ P.A P.L).pull (lift (fst c.A c.A ≫ φ.hom) (snd c.A c.A ≫ φ.hom)).left) ∧ ∀ x, c.lev x ≫ φ.hom = lev x := by
  intro hL _ o _ K _ em h k ζ ze P lev hg hk hze hprim add tors weil
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have dg : ((abelian₂ P.A P.L).pull (lift (𝟙 P.A) (𝟙 P.A)).left).IsLB := LB.isLB_linComb lam _ _
  have lev0 : lev 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  let c : SiegPre h k ζ (spMap em) :=
    { A := P.A
      ab := P.isAb
      P := abelian₂ P.A P.L
      isLB := lam
      rig₁ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
      rig₂ := hasGen_lam_pull P.isLB _ _ (by simp [diff₂])
      symm := lbIso_lam_pull P.isLB _ _ (diff₂_comm _ _)
      lev := lev
      lev_add := add
      lev_tors := tors
      geom := by
        intro k' _ _ x β z hx hz
        obtain ⟨φ₀, rfl⟩ := Spec.map_surjective x
        let φ : K →+* k' := φ₀.hom
        have hβ : φ.comp em = β := by
          have : CommRingCat.ofHom em ≫ φ₀ = CommRingCat.ofHom β := by
            rw [← Spec.map_inj, Spec.map_comp]; exact hx
          exact congrArg (fun q => q.hom) this
        obtain rfl : z = Units.map φ.toMonoidHom ze := Units.ext (by rw [hz, ← hβ]; simp [hze])
        have hz' : IsPrimitiveRoot (Units.map φ.toMonoidHom ze) k :=
          hprim.map_of_injective (Units.map_injective φ.injective)
        have hk' : (k : k') ≠ 0 := by rw [← map_natCast φ]; exact (map_ne_zero φ).2 hk
        have hk₀ : k ≠ 0 := fun e => hk (by simp [e])
        have W : ∀ a b, Out.WeilIs P.A P.L k (toUnit (Over.mk (Spec.map φ₀)) ≫ lev a) (toUnit _ ≫ lev b)
            (unitOn (Units.map φ.toMonoidHom ze ^ omegaStd a b)) := fun a b => by
          have H := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB (toUnit (Over.mk (Spec.map φ₀))) (weil a b)
          have e : Units.map (toUnit (Over.mk (Spec.map φ₀))).left.appTop.hom.toMonoidHom
              (unitOn (ze ^ omegaStd a b)) = unitOn (Units.map φ.toMonoidHom (ze ^ omegaStd a b)) :=
            Units.ext (congrArg (fun q => q.hom (ze ^ omegaStd a b).val) (Scheme.ΓSpecIso_inv_naturality φ₀)).symm
          rw [e, map_zpow] at H
          exact H
        have ker : ∀ a, toUnit (Over.mk (Spec.map φ₀)) ≫ lev a = 1 → ∃ b, a = k • b := fun a ha =>
          exists_smul_of_dvd fun b => by
            have w₁ := W a b
            have w₀ := W 0 b
            rw [ha] at w₁
            rw [lev0, MonObj.comp_one] at w₀
            have e := unitOn_inj (CommutatorPairing.weilIs_unique hL.globalFns P.isAb P.isLB w₁ w₀)
            rw [show omegaStd 0 b = 0 by simp [omegaStd], zpow_zero] at e
            exact (hz'.zpow_eq_one_iff_dvd _).1 e
        refine ⟨fun a => ⟨ker a, ?_⟩, onto_torsion hk₀ _ (fun a b => by rw [add, MonObj.comp_mul])
          (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one]) ker ?_, fun a b => ?_⟩
        · rintro ⟨b, rfl⟩
          have pw : ∀ n : ℕ, lev (n • b) = lev b ^ n := fun n => by
            induction n with
            | zero => rw [zero_smul, pow_zero, lev0]
            | succ n ih => rw [succ_nsmul, add, ih, pow_succ]
          rw [pw, tors, MonObj.comp_one]
        · rw [(hL.mulN _ P k (Nat.pos_of_ne_zero hk₀)).2.2.2.2 k' _ hk', hg]
          simp [two_mul]
        · have H := weilIs_of_lbIso_pow hL.globalFns P.isAb P.isLB dg (lbIso_diag hL P) (W a b)
          have e : unitOn (Units.map φ.toMonoidHom ze ^ (2 * omegaStd a b)) =
              unitOn (Units.map φ.toMonoidHom ze ^ omegaStd a b) ^ 2 := by
            rw [mul_comm, zpow_mul, zpow_ofNat]
            exact map_pow _ _ _
          rw [e]
          exact H }
  refine ⟨c, Iso.refl _, inferInstanceAs (IsMonHom (𝟙 P.A)), ⟨?_, fun T x hx => eq_one_of_lam P.isLB P.ktriv x hx⟩,
    lbIso_lam_pull P.isLB _ _ (congrArg₂ _ (Category.comp_id _) (Category.comp_id _)), fun x => Category.comp_id _⟩
  have R := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb P.isLB (inferInstanceAs (IsFinite (𝟙 P.A.left)))
  have R' := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos P.isAb P.isAb
    (LB.isLB_linComb P.isLB _ _) (inferInstanceAs (IsFinite (𝟙 P.A.left)))
  exact R'.2.2.2 _ dg (lbIso_diag hL P) (R.2.1.2 P.ample)

end GlobalTheory
