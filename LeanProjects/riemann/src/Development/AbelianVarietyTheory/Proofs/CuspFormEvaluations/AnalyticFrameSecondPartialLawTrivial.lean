import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CubicalReadingOneAnalyticFrame
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetRdMulInvPow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CorrOfJetsOfAnalyticFrameProducts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppLESpMapJetPt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJets
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValSecondLaw

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff

theorem tay_coord {N : ℕ} (k : Fin N) :
    tay (fun v : Fin N → ℂ => v k) 0 = MvPowerSeries.X ((0 : Fin 1), k) := by
  classical
  have hθ : ContDiffAt ℂ ω (fun v : Fin N → ℂ => v k) 0 := (contDiff_apply ℂ ℂ k).contDiffAt
  refine TCPf.eq_of_cc _ _ fun l => ?_
  induction l using List.reverseRecOn with
  | nil =>
    simp only [List.foldr_nil]
    rw [constantCoeff_tay, TM.mD_zero]
    simp
  | append_singleton l q _ =>
    obtain ⟨a, j⟩ := q
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    rw [List.foldr_append, List.foldr_append]
    simp only [List.foldr_cons, List.foldr_nil]
    rw [TM.pderiv_tay hθ]
    have hd : (fun y : Fin N → ℂ => fderiv ℂ (fun v : Fin N → ℂ => v k) y (Pi.single j 1)) =
        fun _ => (Pi.single j 1 : Fin N → ℂ) k := by
      funext y
      have := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).fderiv (x := y)
      exact congrArg (fun L : (Fin N → ℂ) →L[ℂ] ℂ => L (Pi.single j 1)) this
    rw [hd, TM.tay_const, MvPowerSeries.pderiv_X]
    congr 2
    by_cases h : k = j
    · subst h; simp
    · simp [Pi.single_apply, h, Prod.ext_iff]

theorem psJet_X' {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (p : κ) :
    psJet m (MvPowerSeries.X p : MvPowerSeries κ ℂ) = Ideal.Quotient.mk _ (MvPolynomial.X p) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem jetN_coord {n g : ℕ} (m : ℕ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j) = Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  have h : jetOf m (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, j))) := by
    rw [jetOf, tay_coord, psJet_X']
  show renN n g m (jetOf m (fun v : Fin (n * g) → ℂ => v (finProdFinEquiv (i, j)))) = _
  rw [h]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  simp only [MvPolynomial.aeval_X, Equiv.symm_apply_apply]

theorem jetN_coord_add {n g : ℕ} (m : ℕ) (i i' : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => w i j + w i' j) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j) + MvPolynomial.X (i', j)) := by
  rw [map_add, ← jetN_coord, ← jetN_coord, jetN, jetN, jetN, ← map_add]
  exact congrArg _ (jetOf_add m (contDiff_apply ℂ ℂ (finProdFinEquiv (i, j))).contDiffAt
      (contDiff_apply ℂ ℂ (finProdFinEquiv (i', j))).contDiffAt)

theorem subst_X {κ κ' : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (sb : κ → MvPolynomial κ' ℂ) (p : κ) :
    (jetSubstP m sb : Jet ℂ κ m →ₐ[ℂ] Jet ℂ κ' m) (psJet m (MvPowerSeries.X p)) =
      Ideal.Quotient.mk _ (sb p - MvPolynomial.C (MvPolynomial.constantCoeff (sb p))) := by
  rw [psJet_X']
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ _) = _
  simp

theorem psIn_add {g n' : ℕ} (m : ℕ) (r : Fin 2 → Fin n') (j : Fin g) :
    (Ideal.Quotient.mk _ (psIn g m r (addF ℂ g j) - MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m r (addF ℂ g j)))) :
      Jet ℂ (Fin n' × Fin g) m) =
      Ideal.Quotient.mk _ (MvPolynomial.X (r 0, j) + MvPolynomial.X (r 1, j)) := by
  have hc : MvPolynomial.constantCoeff (psTrunc m (addF ℂ g j)) = 0 := by
    rw [FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_truncTotal _ (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [addF]
  have ha : (addF ℂ g j : MvPowerSeries (Fin 2 × Fin g) ℂ) =
      ((MvPolynomial.X ((0 : Fin 2), j) + MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin g) ℂ) :
        MvPowerSeries (Fin 2 × Fin g) ℂ) := by simp [addF]
  rw [psIn, MvPolynomial.constantCoeff_rename, hc, map_zero, sub_zero]
  have key : ∀ P : MvPolynomial (Fin 2 × Fin g) ℂ,
      (Ideal.Quotient.mk _ (MvPolynomial.rename (fun p : Fin 2 × Fin g => (r p.1, p.2)) P) : Jet ℂ (Fin n' × Fin g) m) =
      jetMap (m := m) (fun p : Fin 2 × Fin g => MvPolynomial.X (r p.1, p.2)) (fun _ => X_mem_orig _)
        (Ideal.Quotient.mk _ P) := by
    intro P
    show _ = Ideal.Quotient.mk _ (MvPolynomial.aeval _ _)
    rw [MvPolynomial.rename_eq_aeval]
    rfl
  rw [key, ha, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe, ← key]
  simp

theorem sameSum_of_jetMap {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n m : ℕ} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)} {ε : K → ℤ}
    {Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    {φ' : K' → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)} {ε' : K' → ℤ}
    {Λ' : K' → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (h : ∀ k, Φ.JetMap m (φ k) (Λ k)) (h' : ∀ k, Φ.JetMap m (φ' k) (Λ' k))
    (hs : ∀ f : ((Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) → ℤ, ∑ k, ε k * f (Λ k) = ∑ k, ε' k * f (Λ' k)) :
    LB.SameSum φ ε φ' ε' := by
  classical
  intro ψ
  have key : ∀ (χ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) M, Φ.JetMap m χ M → (χ = ψ ↔ Φ.JetMap m ψ M) := by
    rintro χ M ⟨h1, h2⟩
    exact ⟨fun e => ⟨h1, e ▸ h2⟩, fun ⟨_, h4⟩ => h2.trans h4.symm⟩
  have := hs fun M => if Φ.JetMap m ψ M then 1 else 0
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (this.trans (Finset.sum_congr rfl fun k _ => ?_))
  · rw [key _ _ (h k)]
    split_ifs <;> simp
  · rw [key _ _ (h' k)]
    split_ifs <;> simp

theorem sum_two {M : Type} [AddCommMonoid M] (F : ULift.{0} (Finset (Fin 2)) → M) :
    ∑ I, F I = F ⟨∅⟩ + F ⟨{0}⟩ + F ⟨{1}⟩ + F ⟨{0, 1}⟩ := by
  rw [← Equiv.ulift.symm.sum_comp, show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]
  rfl

theorem sum_three {M : Type} [AddCommMonoid M] (F : thK.{0} → M) :
    ∑ I, F I = F ⟨∅⟩ + F ⟨{0}⟩ + F ⟨{1}⟩ + F ⟨{2}⟩ + F ⟨{0, 1}⟩ + F ⟨{0, 2}⟩ + F ⟨{1, 2}⟩ + F ⟨{0, 1, 2}⟩ := by
  have h := Equiv.sum_comp (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) F
  refine h.symm.trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [add_assoc]
  rfl

theorem psumL_pi {n n' g : ℕ} (I : ULift.{0} (Finset (Fin n))) (B : Fin n → (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    psumL n g I ∘ₗ LinearMap.pi B = ∑ i ∈ I.down, B i := by
  refine LinearMap.ext fun w => ?_
  simp [psumL, LinearMap.sum_apply]

theorem count {g : ℕ} (P Q R : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (f : ((Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) → ℤ) :
    ∑ I : thK.{0}, thε I * f (psumL 3 g I ∘ₗ LinearMap.pi ![Q, R, P]) =
      ∑ k : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)),
        Sum.elim (cε 2) (Sum.elim (fun k => - cε 2 k) (fun k => - cε 2 k)) k *
        f (Sum.elim (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![P, Q + R])
          (Sum.elim (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![P, Q]) (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![P, R])) k) := by
  rw [sum_three, Fintype.sum_sum_type, Fintype.sum_sum_type, sum_two, sum_two, sum_two]
  simp only [Sum.elim_inl, Sum.elim_inr, psumL_pi]
  simp [thε, cε, Finset.sum_insert, add_comm P, add_assoc]
  ring

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)

theorem jetRd_scale_one {n m : ℕ} {K : Type} [Fintype K]
    {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ Xo.univ.t.G.left)} {ε : K → ℤ}
    (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) :
    scaleGen φ ε (unitΓ (1 : (Jet ℂ (Fin n × Fin g) m)ˣ)) τ = τ := by
  simp only [scaleGen, unitΓ, map_one, _root_.one_mul]

theorem jetRd_pe (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) {n' : ℕ}
    (φ : Fin 2 → Fin g → MvPolynomial (Fin n' × Fin g) ℂ)
    (B : Fin 2 → (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ i j, (Ideal.Quotient.mk _ (φ i j - MvPolynomial.C (MvPolynomial.constantCoeff (φ i j))) :
      Jet ℂ (Fin n' × Fin g) m) = jetN m (fun w => B i w j)) :
    Φ.toAnFr.JetRd m _ _ (pe y g Φ.jx e m φ) (fun k => psumL 2 g k ∘ₗ LinearMap.pi B) :=
  GlobalTheory.JetLinSub.jetRd_linSubst _ _ _ _ g Φ.toAnFr 2 n' m (LinearMap.pi B) (fun p => φ p.1 p.2)
    (fun p => (subst_X m _ p).trans (h p.1 p.2)) _ _ _ _ _ (he m).2

theorem jetRd_pe_two (e : ∀ m, FrTy y g Φ.jx m) (he : Φ.IsAnE e) (m : ℕ) {n' : ℕ}
    (φ φ' : Fin g → MvPolynomial (Fin n' × Fin g) ℂ)
    (B B' : (Fin n' → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ j, (Ideal.Quotient.mk _ (φ j - MvPolynomial.C (MvPolynomial.constantCoeff (φ j))) :
      Jet ℂ (Fin n' × Fin g) m) = jetN m (fun w => B w j))
    (h' : ∀ j, (Ideal.Quotient.mk _ (φ' j - MvPolynomial.C (MvPolynomial.constantCoeff (φ' j))) :
      Jet ℂ (Fin n' × Fin g) m) = jetN m (fun w => B' w j)) :
    Φ.toAnFr.JetRd m _ _ (pe y g Φ.jx e m ![φ, φ']) (fun k => psumL 2 g k ∘ₗ LinearMap.pi ![B, B']) :=
  jetRd_pe Φ e he m ![φ, φ'] ![B, B'] (Fin.forall_fin_two.2 ⟨h, h'⟩)

set_option backward.isDefEq.respectTransparency false in
theorem jetRd_cube {n : ℕ} (m : ℕ) (a b d : jO y g m n ⟶ Xo.univ.t.G)
    (P Q R : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.toAnFr.JetMap m a.left P)
    (hb : Φ.toAnFr.JetMap m b.left Q) (hd : Φ.toAnFr.JetMap m d.left R) :
    Φ.toAnFr.JetRd m _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
      (lift a (lift b d)).left) (fun I => psumL 3 g I ∘ₗ LinearMap.pi ![P, Q, R]) := by
  obtain ⟨-, hq2, e2⟩ := (GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ n m).2.2.1 b d Q R hb hd
  obtain ⟨hq1, e1⟩ := ha
  have hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (P (colsOf n g v)))
      (lift (Φ.e (Q (colsOf n g v))) (Φ.e (R (colsOf n g v))))).left) :=
    isHolFam_pullback_lift _ _ _ Xo.univ.t.G.hom (Xo.univ.t.G ⊗ Xo.univ.t.G).hom _ _ _ y.x
      (fun v => Over.w (Φ.e (P (colsOf n g v))))
      (fun v => Over.w (lift (Φ.e (Q (colsOf n g v))) (Φ.e (R (colsOf n g v))))) hq1 hq2
  have e3 : (lift a (lift b d)).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
      jetPt _ hq m := by
    apply pullback.hom_ext
    · rw [Category.assoc, jetPt_comp _ hq (pullback.fst _ _) _ hq1 (fun v => congrArg Over.Hom.left (lift_fst _ _)), ← e1]
      exact congrArg Over.Hom.left (lift_fst a (lift b d))
    · rw [Category.assoc, jetPt_comp _ hq (pullback.snd _ _) _ hq2 (fun v => congrArg Over.Hom.left (lift_snd _ _)), ← e2]
      exact congrArg Over.Hom.left (lift_snd a (lift b d))
  rw [e3]
  refine GlobalTheory.AnValJetGlob.jetRd_pullGen _ _ _ _ g Φ.toAnFr n m _ _ _ _ _ _ _ hq fun v => ?_
  have := GlobalTheory.cubical_reading_one E H Dw l Xo c y g ty el Φ (P (colsOf n g v)) (Q (colsOf n g v)) (R (colsOf n g v))
  have hv : LinearMap.pi ![P, Q, R] (colsOf n g v) = ![P (colsOf n g v), Q (colsOf n g v), R (colsOf n g v)] := by
    funext i
    fin_cases i <;> rfl
  simpa only [LinearMap.comp_apply, hv] using this

end Main

theorem second_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ m, ∃ u : (Jet ℂ (Fin 3 × Fin g) m)ˣ, (u : Jet ℂ (Fin 3 × Fin g) m) = psJet m (anFB ty).ph2 ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift (jpt y g Φ.jx m (1 : Fin 3)) (lift (jpt y g Φ.jx m (2 : Fin 3)) (jpt y g Φ.jx m (0 : Fin 3)))).left) (scaleGen _ _ (unitΓ u) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn g m ![1, 2] ((anFB ty).G.F j)]) (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)])) (LB.invGen Xo.univ.t.PP.L _ _ (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)]))))) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ himm e he m
  refine ⟨1, by rw [show (anFB ty).ph2 = 1 from rfl, FBIdJet.psJet_one, Units.val_one], ?_⟩
  rw [jetRd_scale_one]
  have hp := (GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ 3 m).1
  have hL := jetRd_cube Φ m _ _ _ _ _ _ (hp 1) (hp 2) (hp 0)
  have hX : ∀ (i : Fin 3) (j : Fin g), (Ideal.Quotient.mk _ (MvPolynomial.X (i, j) -
      MvPolynomial.C (MvPolynomial.constantCoeff (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin g) ℂ))) :
      Jet ℂ (Fin 3 × Fin g) m) = jetN m (fun w => (LinearMap.proj i : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) w j) := by
    intro i j
    simp only [LinearMap.proj_apply]
    rw [jetN_coord]
    simp
  have hF : ∀ j, (Ideal.Quotient.mk _ (psIn g m ![(1 : Fin 3), 2] ((anFB ty).G.F j) -
      MvPolynomial.C (MvPolynomial.constantCoeff (psIn g m ![(1 : Fin 3), 2] ((anFB ty).G.F j)))) :
      Jet ℂ (Fin 3 × Fin g) m) =
      jetN m (fun w => ((LinearMap.proj 1 : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) +
        (LinearMap.proj 2 : (Fin 3 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) w j) := by
    intro j
    simp only [LinearMap.proj_apply, LinearMap.add_apply, Pi.add_apply]
    rw [show (anFB ty).G.F j = addF ℂ g j from rfl, psIn_add, jetN_coord_add]
    rfl
  have h1 := jetRd_pe_two Φ e he m (fun j => MvPolynomial.X ((0 : Fin 3), j))
    (fun j => psIn g m ![1, 2] ((anFB ty).G.F j)) (LinearMap.proj 0) (LinearMap.proj 1 + LinearMap.proj 2) (hX 0) hF
  have h2 := jetRd_pe_two Φ e he m (fun j => MvPolynomial.X ((0 : Fin 3), j))
    (fun j => MvPolynomial.X ((1 : Fin 3), j)) (LinearMap.proj 0) (LinearMap.proj 1) (hX 0) (hX 1)
  have h3 := jetRd_pe_two Φ e he m (fun j => MvPolynomial.X ((0 : Fin 3), j))
    (fun j => MvPolynomial.X ((2 : Fin 3), j)) (LinearMap.proj 0) (LinearMap.proj 2) (hX 0) (hX 2)
  have h2' := (jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ _ _ _ h2 h2).2.1
  have h3' := (jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ _ _ _ h3 h3).2.1
  have h23 := (jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ _ _ _ h2' h3').1
  have hR := (jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 3 m _ _ _ _ _ _ _ _ _ _ h1 h23).1
  have hS := sameSum_of_jetMap Φ.toAnFr hL.1 hR.1 (count (LinearMap.proj 0) (LinearMap.proj 1) (LinearMap.proj 2))
  have hC := GlobalTheory.AnVal.JetCorr.corr_of_jetRd _ _ _ _ g Φ.toAnFr himm 3 m _ _ _ _ _ _ _ _ _ _ hL hR hS
  exact hC

end GlobalTheory.AnValSecondLaw
