import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (endT)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PullMove

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem translT_mul {T : Over S} (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) := by
  rw [translT, lift_transl, translPt_eq, translT, translPt_eq, MonObj.comp_mul, _root_.mul_assoc]

theorem translT_one {T : Over S} : translT A (1 : T ⟶ A) = 𝟙 _ := by
  rw [translT, translPt_eq, MonObj.comp_one, _root_.one_mul, lift_fst_snd]

theorem translT_endT (φ : A ⟶ A) [IsMonHom φ] {T : Over S} (x : T ⟶ A) :
    translT A x ≫ endT A T φ = endT A T φ ≫ translT A (x ≫ φ) := by
  rw [lift_transl, translT, comp_lift, lift_fst, lift_snd_assoc, translPt_eq, MonObj.mul_comp, Category.assoc]

theorem negT_endT (φ : A ⟶ A) [IsMonHom φ] (T : Over S) : negT A T ≫ endT A T φ = endT A T φ ≫ negT A T := by
  rw [negT, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc, lift_snd_assoc]
  exact congrArg _ (GrpObj.inv_comp (snd T A) φ)

theorem negT_translT [IsCommMonObj A] {T : Over S} (x : T ⟶ A) :
    negT A T ≫ translT A x = translT A x⁻¹ ≫ negT A T := by
  rw [negT, lift_transl, translT, comp_lift, lift_fst, lift_snd_assoc, translPt_eq, GrpObj.comp_inv]
  refine congrArg _ ?_
  show fst T A ≫ x * (snd T A)⁻¹ = ((fst T A ≫ x)⁻¹ * snd T A)⁻¹
  rw [mul_inv, inv_inv]

omit [GrpObj A] in

theorem exists_conj {L : LB A.left} (hL : L.IsLB) (φ : A ⟶ A) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα : α.IsGen) {T : Over S}
    (m' m : T ⊗ A ⟶ A) (e : m' ≫ φ = endT A T φ ≫ m)
    (u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![b, -b])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m'.left] ![a, -a]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val u' r z J = val α (r ≫ (snd T A).left) z J * val u (r ≫ (endT A T φ).left) z J *
          (val α (r ≫ m'.left) z J)⁻¹ := by
  have e₁ : (endT A T φ).left ≫ (snd T A).left = (snd T A).left ≫ φ.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (endT A T φ).left ≫ m.left = m'.left ≫ φ.left := by
    rw [← Over.comp_left, ← e, Over.comp_left]
  obtain ⟨u', hu', hv⟩ := exists_gen hL (φ' := ![(snd T A).left, m'.left]) (ε' := ![a, -a])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ α (snd T A).left)
      (LB.pullGen L _ _ u (endT A T φ).left)) (LB.invGen L _ _ (LB.pullGen L _ _ α m'.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)
      (DVR.pullGen_isGen _ _ _ _ hu _)) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  refine ⟨u', hu', fun Z r z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]

theorem prod_conj {U : Type} [CommGroup U] (f g : ℕ → U) (n N : ℕ)
    (hg : ∀ i, ∏ j ∈ Finset.range n, g (n * i + j) = 1) (hf : f (n * N) = f 0) :
    ∏ j ∈ Finset.range (n * N), (f j * g j * (f (j + 1))⁻¹) = 1 := by
  have t : ∀ k, ∏ j ∈ Finset.range k, (f j * g j * (f (j + 1))⁻¹) =
      f 0 * (∏ j ∈ Finset.range k, g j) * (f k)⁻¹ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
      group
  have p : ∀ M, ∏ j ∈ Finset.range (n * M), g j = 1 := fun M => by
    induction M with
    | zero => simp
    | succ M ih => rw [Nat.mul_succ, Finset.prod_range_add, ih, hg, _root_.mul_one]
  rw [t, p, hf, _root_.mul_one, mul_inv_cancel]

theorem exists_symLift_conj [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hα : α.IsGen) {T : Over S}
    (n N : ℕ) (x : T ⟶ A) (hx : x ^ (n * N) = 1) (U : ThetaGrp A L b T) (H : SymLift A L b n (x ≫ φ) U) :
    ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![a, -a]), ∃ hu : u.IsGen,
      SymLift A L a (n * N) x ⟨x, u, hu⟩ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val u r z J = val α (r ≫ (snd T A).left) z J *
          val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![b, -b]) U.φ
            (r ≫ (endT A T φ).left) z J * (val α (r ≫ (translPt A x).left) z J)⁻¹ := by
  have hp := H.pt_eq
  have ts : ∀ y : T ⟶ A, translT A y ≫ snd T A = translPt A y := fun y => lift_snd _ _
  have ns : negT A T ≫ snd T A = snd T A ≫ (GrpObj.inv : A ⟶ A) := lift_snd _ _
  obtain ⟨u, hu, vu⟩ := exists_conj hL φ a b α hα (translPt A x) (translPt A U.pt) (by
    rw [hp, ← ts (x ≫ φ), ← Category.assoc, ← translT_endT, Category.assoc, lift_snd, ← Category.assoc, ts])
    U.φ U.isGen
  obtain ⟨ν, hν, hs⟩ := H.sym
  obtain ⟨ν', hν', vν⟩ := exists_conj hL φ a b α hα (snd T A ≫ (GrpObj.inv : A ⟶ A))
    (snd T A ≫ (GrpObj.inv : A ⟶ A)) (by
      rw [lift_snd_assoc]
      exact GrpObj.inv_comp (snd T A) φ) ν hν
  refine ⟨u, hu, ⟨rfl, corr_of_val hL fun y J hJ => ?_, ν', hν', corr_of_val hL fun y J hJ => ?_⟩, vu⟩
  · refine (ThetaPullback.val_powGen ⟨x, u, hu⟩ (n * N) _ hJ).trans (Eq.trans ?_ (val_one _).symm)
    refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) ((Fin.prod_univ_eq_prod_range _ _).trans (prod_conj
      (fun j => val α (translPt A (x ^ j)).left y J)
      (fun j => val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left]) (ε := ![b, -b]) U.φ
        (endT A T φ ≫ translT A (U.pt ^ j)).left y J) n N (fun i => ?_) (by rw [hx, pow_zero])))
    · refine (vu _ _ y J hJ).trans ?_
      simp only [Category.id_comp, ← Over.comp_left]
      rw [ts, translT_endT, MonObj.pow_comp, ← hp, ← ts x, ← Category.assoc, translT_mul, ts, pow_succ']
    · have e := (ThetaPullback.val_powGen U n (endT A T φ ≫ translT A (U.pt ^ (n * i))).left hJ).symm.trans
        ((val_corr hJ H.pow_eq _).trans (val_one _))
      refine Eq.trans ?_ e
      rw [← Fin.prod_univ_eq_prod_range (fun j => val (L := L) (φ := ![(snd T A).left, (translPt A U.pt).left])
        (ε := ![b, -b]) U.φ (endT A T φ ≫ translT A (U.pt ^ (n * i + j))).left y J)]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← Over.comp_left, Category.assoc, translT_mul, ← pow_add, add_comm]
  · have e := (ThetaPullback.val_symGen U ν (endT A T φ).left hJ).symm.trans ((val_corr hJ hs _).trans (val_one _))
    refine (ThetaPullback.val_symGen ⟨x, u, hu⟩ ν' _ hJ).trans (Eq.trans ?_ (e.trans (val_one _).symm))
    refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) (vu _ _ y J hJ) (vν _ _ y J hJ))
      (congrArg₂ (· * ·) (vu _ _ y J hJ) (congrArg (·⁻¹) (vν _ _ y J hJ)))).trans ?_
    simp only [Category.id_comp, ← Over.comp_left]
    have e₁ : translT A x⁻¹ ≫ translPt A x = snd T A := by
      rw [← ts x, ← Category.assoc, translT_mul, mul_inv_cancel, translT_one, Category.id_comp]
    have e₂ : negT A T ≫ translPt A x = translT A x⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) := by
      rw [← ts x, ← Category.assoc, negT_translT, Category.assoc, ns]
    rw [e₁, e₂, ns, negT_endT, translT_endT, GrpObj.inv_comp, ← hp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem isSymAct_of_isNormPull [IsCommMonObj A] (hA : IsAbelianScheme A) (L : RigLB A) (φ : A ⟶ A) [IsMonHom φ]
    (k N : ℕ) {T : Over S} (x : T ⟶ A) (hx : x ^ (k * N) = 1) {F G : LB.Sec (LPow A L.L (k : ℤ) T)}
    {F' G' : LB.Sec (LPow A L.L ((k * N : ℕ) : ℤ) T)} (h : IsSymAct A L k (x ≫ φ) F G)
    (hF : IsNormPull A L φ ((k * N : ℕ) : ℤ) (k : ℤ) F F') (hG : IsNormPull A L φ ((k * N : ℕ) : ℤ) (k : ℤ) G G') :
    IsSymAct A L (k * N) x F' G' := by
  have hL := L.isLB
  obtain ⟨-, U, H, ac⟩ := h
  obtain ⟨α₀, α, g₀, n₀, c, tw⟩ := hF
  obtain ⟨α₀', α', g₀', n₀', c', tw'⟩ := hG
  obtain ⟨u, hu, H', vu⟩ := exists_symLift_conj hL φ _ _ α₀ g₀ k N x hx U H
  refine ⟨hx, ⟨x, u, hu⟩, H', VVRank.isTwistPull_of_sv A hL hu fun y J hJ => ?_⟩
  have bb := fun r : (T ⊗ A).left ⟶ A.left =>
    gen_unique hL A.hom (eSec A) (Over.w η[A]) (SemiRigid.globalFns _ _ hA).2 g₀' g₀ (fun w I hI => by
      have a := val_corr hI n₀' (𝟙 _)
      have b := val_corr hI n₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm) _ r y J hJ
  rw [VVRank.sv_of_isTwistPull A tw' _ y hJ, VVRank.sv_of_isTwistPull A tw _ y hJ,
    VVRank.sv_of_isTwistPull A ac _ y hJ, vu _ _ y J hJ, val_corr hJ c, val_corr hJ c', val_pull hJ, val_pull hJ, bb]
  simp only [Category.id_comp, ← Over.comp_left]
  rw [translT_endT, ← H.pt_eq, show translT A x ≫ snd T A = translPt A x from lift_snd _ _,
    ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
    ← Units.val_mul, inv_mul_cancel_right]

end GlobalTheory.PullMove

namespace GlobalTheory.PlaceInt

theorem moves_of_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (β : 𝓞 E) (N k k' : ℕ), β * H.bar β = (N : 𝓞 E) → k' = k * N → Odd k' → ∀ (b b' : (ptO Xo x ⟶ Xo.univ.t.G)), b' ≫ Xo.univ.t.act.act β = b → b' ^ k' = 1 → ∀ (F G : SecN Xo x k) (F' G' : SecN Xo x k'), Moves Xo b F G → Pulls Xo β F F' → Pulls Xo β G G' → Moves Xo b' F' G' := by
  intro E _ _ _ H Dw l Xo S _ x β N k k' _ hk _ b b' hb hb' F G F' G' h hF hG
  subst hk hb
  have := Xo.univ.t.act.hom β
  exact PullMove.isSymAct_of_isNormPull
    ⟨inferInstance, Xo.univ.t.semi.smooth, Xo.univ.proper, Xo.univ.t.semi.geomConnected⟩ _ _ k N b' hb' h hF hG

end GlobalTheory.PlaceInt
