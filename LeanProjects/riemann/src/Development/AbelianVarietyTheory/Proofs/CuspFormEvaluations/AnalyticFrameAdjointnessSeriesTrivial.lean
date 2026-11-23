import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdjReadingOne
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetRdMulInvPow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CorrOfJetsOfAnalyticFrameProducts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppLESpMapJetPt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.JetReadingLinearSubstitutionPoints
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CmFrameJetPointsAreExponentialJets

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnValAd

theorem tay_coord {g : ℕ} (c : ℂ) (k : Fin g) :
    tay (fun v : Fin g → ℂ => c * v k) 0 = MvPowerSeries.C c * MvPowerSeries.X ((0 : Fin 1), k) := by
  ext n
  rw [MvPowerSeries.coeff_C_mul, ← GlobalTheory.JetLinSub.tay_coord k, coeff_tay, coeff_tay]
  unfold mD lD
  have hf : (fun v : Fin g → ℂ => c * v k) = c • (fun v : Fin g → ℂ => v k) := by
    funext v
    simp [smul_eq_mul]
  rw [hf, iteratedFDeriv_const_smul_apply (by fun_prop)]
  simp [smul_eq_mul, mul_div_assoc]

theorem psJet_CX {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (c : ℂ) (s : κ) :
    psJet m (MvPowerSeries.C c * MvPowerSeries.X s : MvPowerSeries κ ℂ) =
      Ideal.Quotient.mk _ (MvPolynomial.C c * MvPolynomial.X s) := by
  have h := GlobalTheory.JetLinSub.psJet_X (κ := κ) m s
  unfold psJet psTrunc at h ⊢
  simp only [MvPowerSeries.coeff_C_mul, ← MvPolynomial.C_mul_monomial, ← Finset.mul_sum, map_mul, h]

theorem jetN_coord {n g : ℕ} (m : ℕ) (c : ℂ) (i : Fin n) (j : Fin g) :
    jetN m (fun w : Fin n → Fin g → ℂ => c * w i j) =
      Ideal.Quotient.mk _ (MvPolynomial.C c * MvPolynomial.X (i, j)) := by
  unfold jetN
  have hf : (fun v : Fin (n * g) → ℂ => (fun w : Fin n → Fin g → ℂ => c * w i j) (colsOf n g v)) =
      fun v => c * v (finProdFinEquiv (i, j)) := rfl
  rw [hf]
  unfold jetOf
  rw [tay_coord, psJet_CX]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval
      (fun p : Fin 1 × Fin (n * g) => (MvPolynomial.X (finProdFinEquiv.symm p.2) : MvPolynomial (Fin n × Fin g) ℂ))
      (MvPolynomial.C c * MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, j)))) = _
  rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Equiv.symm_apply_apply]

theorem subst_X_eq {n n' g : ℕ} (m : ℕ) (sb : Fin n × Fin g → MvPolynomial (Fin n' × Fin g) ℂ) (p : Fin n × Fin g)
    (hc : MvPolynomial.constantCoeff (sb p) = 0) :
    (jetSubstP m sb : Jet ℂ (Fin n × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m) (psJet m (MvPowerSeries.X p)) =
      Ideal.Quotient.mk _ (sb p) := by
  rw [GlobalTheory.JetLinSub.psJet_X]
  show Ideal.Quotient.mk _ (MvPolynomial.aeval
      (fun i => sb i - MvPolynomial.C (MvPolynomial.constantCoeff (sb i))) (MvPolynomial.X p)) = _
  rw [MvPolynomial.aeval_X, hc, map_zero, sub_zero]

theorem mk_psIn_lin {n' g : ℕ} (m : ℕ) (i : Fin n') (c : ℂ) (j : Fin g) :
    Ideal.Quotient.mk (orig ℂ (Fin n' × Fin g) ^ (m + 1))
      (psIn g m ![i] (MvPowerSeries.C c * MvPowerSeries.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.C c * MvPolynomial.X (i, j)) := by
  have h := psJet_CX m c ((0 : Fin 1), j)
  unfold psJet at h
  have h' := congrArg (⇑(jetMap (fun p : Fin 1 × Fin g =>
      (MvPolynomial.X (![i] p.1, p.2) : MvPolynomial (Fin n' × Fin g) ℂ)) (fun _ => X_mem_orig _) :
      Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)) h
  have e1 : ∀ P : MvPolynomial (Fin 1 × Fin g) ℂ,
      (jetMap (fun p : Fin 1 × Fin g => (MvPolynomial.X (![i] p.1, p.2) : MvPolynomial (Fin n' × Fin g) ℂ))
        (fun _ => X_mem_orig _) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n' × Fin g) m)
        (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig ℂ (Fin n' × Fin g) ^ (m + 1)) (MvPolynomial.aeval
        (fun p : Fin 1 × Fin g => (MvPolynomial.X (![i] p.1, p.2) : MvPolynomial (Fin n' × Fin g) ℂ)) P) :=
    fun _ => rfl
  rw [e1, e1, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq] at h'
  unfold psIn
  rw [← MvPolynomial.aeval_X_left_apply (MvPolynomial.rename _ _), MvPolynomial.aeval_rename]
  exact h'

theorem jetMap_unique {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n m : ℕ} {ψ ψ' : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left}
    {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : Φ.JetMap m ψ Λ) (h' : Φ.JetMap m ψ' Λ) : ψ = ψ' := by
  obtain ⟨h1, rfl⟩ := h
  obtain ⟨h2, rfl⟩ := h'
  rfl

theorem sameSum_cancel {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K ⊕ K → (Y ⟶ X)) (ψ ψ' : K → (Y ⟶ X))
    (ε : K → ℤ) (h1 : ∀ k, φ (Sum.inl k) = ψ' k) (h2 : ∀ k, φ (Sum.inr k) = ψ k) :
    LB.SameSum (Sum.elim φ ψ) (Sum.elim (Sum.elim ε fun k => -ε k) ε) ψ' ε := by
  have hφ : φ = Sum.elim ψ' ψ := by
    funext k
    cases k with
    | inl k => exact h1 k
    | inr k => exact h2 k
  subst hφ
  intro x
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc, ← Finset.sum_add_distrib]
  refine (congrArg (HAdd.hAdd _) (Finset.sum_eq_zero fun k _ => ?_)).trans (add_zero _)
  dsimp only [Sum.elim_inl, Sum.elim_inr]
  have key : ∀ (P : Prop) (i1 i2 : Decidable P) (b : ℤ), @ite ℤ P i1 (-b) 0 + @ite ℤ P i2 b 0 = 0 := by
    intro P i1 i2 b
    by_cases hP : P
    · rw [@if_pos P i1 hP, @if_pos P i2 hP]
      omega
    · rw [@if_neg P i1 hP, @if_neg P i2 hP]
      omega
  exact key _ _ _ _

theorem scaleGen_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {A : Type} [CommRing A] {K : Type} [Fintype K] (φ : K → (Sp A ⟶ Xo.univ.t.G.left))
    (ε : K → ℤ) (t : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) : scaleGen φ ε (unitΓ 1) t = t := by
  unfold scaleGen unitΓ
  simp only [map_one]
  cases t
  congr 1
  funext j
  exact one_mul _

def pairL {g : ℕ} (A B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : (Fin 2 → Fin g → ℂ) →ₗ[ℂ] (Fin 2 → Fin g → ℂ) :=
  LinearMap.pi ![A ∘ₗ LinearMap.proj 0, B ∘ₗ LinearMap.proj 1]

theorem pairL_apply {g : ℕ} (A B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (w : Fin 2 → Fin g → ℂ) :
    pairL A B w = ![A (w 0), B (w 1)] := by
  funext i
  fin_cases i <;> rfl

theorem adjoint_series_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → (∀ a : 𝓞 E, star a = H.bar a) → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)]) (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m ((anFB ty).ad a) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y g Φ.jx m (0 : Fin 2)) (jpt y g Φ.jx m (1 : Fin 2))).left) (pe y g Φ.jx e m ![fun j => psIn g m ![0] ((anFB ty).A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])) (scaleGen _ _ (unitΓ u) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn g m ![1] ((anFB ty).A.act (H.bar a) j)])) := by
  intro E _ _ _ H Dw l Xo c _ _ y g ty el Φ hImm hstar e he a
  have h3 : ∀ (b : 𝓞 E) (j : Fin g), (anFB ty).A.act b j =
      MvPowerSeries.C (ty j (b : E)) * MvPowerSeries.X ((0 : Fin 1), j) := by
    intro b j
    rfl
  have h5 : ∀ m : ℕ, psJet m (1 : MvPowerSeries (Fin 2 × Fin g) ℂ) = 1 := by
    intro m
    unfold psJet psTrunc
    rw [Finset.sum_eq_single 0]
    · rw [MvPowerSeries.coeff_zero_one, ← MvPolynomial.C_apply, map_one, map_one]
    · intro b _ hb
      rw [MvPowerSeries.coeff_one, if_neg hb, map_zero]
    · intro h0
      exfalso
      apply h0
      simp [degLE]
      exact ⟨fun _ => 0, by ext i; simp⟩
  obtain ⟨wL, hwL, hread⟩ := GlobalTheory.AdjRead.exists_adj_reading_one E H Dw l Xo c y g ty el Φ a
  refine ⟨wL, hwL, fun m => ⟨1, ?_, ?_⟩⟩
  · rw [show (anFB ty).ad a = 1 from rfl, h5, Units.val_one]
  rw [scaleGen_one]
  obtain ⟨hJ, -, hMul, -, -⟩ := GlobalTheory.AnVal.jetPts_jetMap E H Dw l Xo c y g ty el Φ 2 m
  obtain ⟨-, hq, hlift⟩ := hMul (jpt y g Φ.jx m 0) (jpt y g Φ.jx m 1) (LinearMap.proj 0) (LinearMap.proj 1)
    (hJ 0) (hJ 1)
  have R1 := GlobalTheory.AnValJetGlob.jetRd_pullGen _ _ _ _ g Φ.toAnFr 2 m _ _ _ _ wL
    (Sum.elim (fun I => psumL 2 g I ∘ₗ pairL LinearMap.id (tyAct ty (H.bar a)))
      (fun I => psumL 2 g I ∘ₗ pairL (tyAct ty a) LinearMap.id)) _ hq (fun v => by
        have h := hread (colsOf 2 g v 0) (colsOf 2 g v 1)
        have hp : (fun k => (Sum.elim (fun I => psumL 2 g I ∘ₗ pairL LinearMap.id (tyAct ty (H.bar a)))
            (fun I => psumL 2 g I ∘ₗ pairL (tyAct ty a) LinearMap.id) :
              ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → (Fin 2 → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) k
              (colsOf 2 g v)) =
            Sum.elim (fun I => psumL 2 g I ![colsOf 2 g v 0, tyAct ty (H.bar a) (colsOf 2 g v 1)])
              (fun I => psumL 2 g I ![tyAct ty a (colsOf 2 g v 0), colsOf 2 g v 1]) := by
          funext k
          rcases k with I | I <;> simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply, pairL_apply,
            LinearMap.id_apply]
        rw [hp]
        exact h)
  rw [← hlift] at R1
  have hσA : ∀ p : Fin 2 × Fin g, (jetSubstP m (fun p => ![fun j => psIn g m ![0] ((anFB ty).A.act a j),
      fun j => MvPolynomial.X ((1 : Fin 2), j)] p.1 p.2) : Jet ℂ (Fin 2 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m)
      (psJet m (MvPowerSeries.X p)) = jetN m (fun w => pairL (tyAct ty a) LinearMap.id w p.1 p.2) := by
    rintro ⟨i, j⟩
    fin_cases i
    · show (jetSubstP m _ : Jet ℂ (Fin 2 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m)
        (psJet m (MvPowerSeries.X ((0 : Fin 2), j))) = jetN m (fun w => pairL (tyAct ty a) LinearMap.id w 0 j)
      rw [subst_X_eq]
      · show Ideal.Quotient.mk _ (psIn g m ![0] ((anFB ty).A.act a j)) = _
        have hw : (fun w : Fin 2 → Fin g → ℂ => pairL (tyAct ty a) LinearMap.id w 0 j) =
            fun w => ty j (a : E) * w 0 j := by
          funext w
          simp [pairL_apply, tyAct]
        rw [hw, jetN_coord, h3, mk_psIn_lin]
      · show MvPolynomial.constantCoeff (psIn g m ![0] ((anFB ty).A.act a j)) = 0
        rw [h3]
        unfold psIn psTrunc
        simp
        apply Finset.sum_eq_zero
        intro e _
        rw [MvPolynomial.constantCoeff_monomial]
        split_ifs with he
        · subst he
          simp
        · rfl
    · show (jetSubstP m _ : Jet ℂ (Fin 2 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m)
        (psJet m (MvPowerSeries.X ((1 : Fin 2), j))) = jetN m (fun w => pairL (tyAct ty a) LinearMap.id w 1 j)
      rw [subst_X_eq]
      · show Ideal.Quotient.mk _ (MvPolynomial.X ((1 : Fin 2), j)) = _
        have hw : (fun w : Fin 2 → Fin g → ℂ => pairL (tyAct ty a) LinearMap.id w 1 j) =
            fun w => 1 * w 1 j := by
          funext w
          simp [pairL_apply]
        rw [hw, jetN_coord, map_one, _root_.one_mul]
      · show MvPolynomial.constantCoeff (MvPolynomial.X ((1 : Fin 2), j) : MvPolynomial (Fin 2 × Fin g) ℂ) = 0
        simp
  have hσB : ∀ p : Fin 2 × Fin g, (jetSubstP m (fun p => ![fun j => MvPolynomial.X ((0 : Fin 2), j),
      fun j => psIn g m ![1] ((anFB ty).A.act (H.bar a) j)] p.1 p.2) :
        Jet ℂ (Fin 2 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m)
      (psJet m (MvPowerSeries.X p)) = jetN m (fun w => pairL LinearMap.id (tyAct ty (H.bar a)) w p.1 p.2) := by
    rintro ⟨i, j⟩
    fin_cases i
    · show (jetSubstP m _ : Jet ℂ (Fin 2 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m)
        (psJet m (MvPowerSeries.X ((0 : Fin 2), j))) =
          jetN m (fun w => pairL LinearMap.id (tyAct ty (H.bar a)) w 0 j)
      rw [subst_X_eq]
      · show Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 2), j)) = _
        have hw : (fun w : Fin 2 → Fin g → ℂ => pairL LinearMap.id (tyAct ty (H.bar a)) w 0 j) =
            fun w => 1 * w 0 j := by
          funext w
          simp [pairL_apply]
        rw [hw, jetN_coord, map_one, _root_.one_mul]
      · show MvPolynomial.constantCoeff (MvPolynomial.X ((0 : Fin 2), j) : MvPolynomial (Fin 2 × Fin g) ℂ) = 0
        simp
    · show (jetSubstP m _ : Jet ℂ (Fin 2 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m)
        (psJet m (MvPowerSeries.X ((1 : Fin 2), j))) =
          jetN m (fun w => pairL LinearMap.id (tyAct ty (H.bar a)) w 1 j)
      rw [subst_X_eq]
      · show Ideal.Quotient.mk _ (psIn g m ![1] ((anFB ty).A.act (H.bar a) j)) = _
        have hw : (fun w : Fin 2 → Fin g → ℂ => pairL LinearMap.id (tyAct ty (H.bar a)) w 1 j) =
            fun w => ty j ((H.bar a : 𝓞 E) : E) * w 1 j := by
          funext w
          simp [pairL_apply, tyAct]
        rw [hw, jetN_coord, h3, mk_psIn_lin]
      · show MvPolynomial.constantCoeff (psIn g m ![1] ((anFB ty).A.act (H.bar a) j)) = 0
        rw [h3]
        unfold psIn psTrunc
        simp
        apply Finset.sum_eq_zero
        intro e _
        rw [MvPolynomial.constantCoeff_monomial]
        split_ifs with he
        · subst he
          simp
        · rfl
  have R2 := GlobalTheory.JetLinSub.jetRd_linSubst _ _ _ _ g Φ.toAnFr 2 2 m _ _ hσA _ _ _ _ _ (he m).2
  have R3 := GlobalTheory.JetLinSub.jetRd_linSubst _ _ _ _ g Φ.toAnFr 2 2 m _ _ hσB _ _ _ _ _ (he m).2
  have AdjoinForm := (GlobalTheory.AnVal.jetRd_mul_inv_pow _ _ _ _ g Φ.toAnFr 2 m _ _ _ _ _ _ _ _ _ _ R1 R2).1
  refine GlobalTheory.AnVal.JetCorr.corr_of_jetRd _ _ _ _ g Φ.toAnFr hImm 2 m _ _ _ _ _ _ _ _ _ _ AdjoinForm R3 ?_
  exact sameSum_cancel _ _ _ _ (fun k => jetMap_unique Φ.toAnFr (R1.1 (Sum.inl k)) (R3.1 k))
    (fun k => jetMap_unique Φ.toAnFr (R1.1 (Sum.inr k)) (R2.1 k))

end GlobalTheory.AnValAd
