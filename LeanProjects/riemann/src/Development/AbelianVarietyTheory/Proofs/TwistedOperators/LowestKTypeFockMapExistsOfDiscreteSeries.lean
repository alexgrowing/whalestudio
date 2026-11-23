import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilMaximalCompactFockSubstitutionCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction (parDef parHol IsAdapted)
open GlobalTheory.DefLift (AllPlus IsTensAct unfr)
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ArchRec.IoMap

theorem enum_eq {n : ℕ} {S : SPar} {c : Fin n → ℚ} (hc : StrictAnti c) (hm : ∀ a, ∃ s, (c a, s) ∈ S)
    {u : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum S u ε) (a : Fin n) : u a = c a := by
  obtain ⟨hu, q, hq, hS⟩ := he
  have hq' : StrictAnti q := fun a b hab => by
    have := hu hab
    rw [hq, hq] at this
    exact_mod_cast this
  have hsub : Finset.univ.image c ⊆ Finset.univ.image q := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨s, hs⟩ := hm a
    rw [hS] at hs
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hs
    exact Finset.mem_image.2 ⟨b, Finset.mem_univ _, congrArg Prod.fst hb⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injective _ hq'.injective, Finset.card_image_of_injective _ hc.injective])
  have hr : Set.range c = Set.range q := by
    simpa using congrArg (fun s : Finset ℚ => (s : Set ℚ)) heq
  rw [hq, (hc.range_inj hq').1 hr]

variable {D : D7}

theorem lamAt_mem (i : Fin D.R.m) (τ : D.what₂.Tau) {a : ℕ} (ha : a < D.R.r) :
    (Formalism.L2.NTheta.lamAt (D.hc τ) a - 1 / 2, true) ∈ parDef D i τ := by
  refine Finset.mem_image.2 ⟨_, Finset.mem_union_left _ ?_, rfl⟩
  have hk := D.R.m_add_three_le_k
  unfold Ranks.r at ha
  unfold Formalism.L2.NTheta.lamAt
  split_ifs with h1 h2
  · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩)
  · omega

open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes in

theorem lam_parDef (i : Fin D.R.m) (M : DSModel (Vc D i) (parDef D i)) (τ : D.what₂.Tau) :
    M.lam τ = fun a => (((Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w a : ℝ) +
      ((rhoVec (Vc D i).rank a : ℚ) : ℝ)) := by
  funext a
  have A := GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ
  obtain ⟨hpq, hV⟩ := A.rank
  have hVq : ((Vc D i).rank : ℚ) = pS D i τ + qS D i τ + D.R.t := by
    rw [hV, ← hpq]; push_cast; rfl
  rw [enum_eq (c := fun a => ((Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w a : ℚ) +
    rhoVec (Vc D i).rank a) (fun a b hab => ?_) (fun a => ⟨true, ?_⟩) (M.enum τ) a]
  · push_cast; rfl
  · have h1 : ((Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w b : ℚ) ≤
        (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w a := by
      exact_mod_cast (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).2 hab.le
    have h2 : ((a : ℕ) : ℚ) < (b : ℕ) := by exact_mod_cast hab
    simp only [rhoVec]
    linarith
  · have ha := a.2
    rw [A.coef_eq a, rhoVec, hVq]
    unfold thetaWt dShift
    split_ifs with c1 c2
    · convert lamAt_mem i τ (a := a) (by omega) using 2
      rw [Int.cast_natCast, A.aP_eq_rat a c1, aPlusQ, centred]
      ring
    · refine Finset.mem_image.2 ⟨-(D.hc τ).e i + ((D.R.t : ℚ) - 1) / 2 - ((a - pS D i τ : ℕ) : ℚ),
        Finset.mem_union_right _ (Finset.mem_image.2 ⟨a - pS D i τ, Finset.mem_range.2 (by omega), rfl⟩), ?_⟩
      rw [Nat.cast_sub (by omega)]
      congr 1
      simp only [eS]
      push_cast
      ring
    · obtain ⟨c, hc⟩ : ∃ c, (a : ℕ) = pS D i τ + D.R.t + c := ⟨a - (pS D i τ + D.R.t), by omega⟩
      convert lamAt_mem i τ (a := pS D i τ + c) (by omega) using 2
      rw [hc, Nat.add_sub_cancel_left, Int.cast_neg, Int.cast_natCast, A.aM_eq c (by omega), dRowQ, centred]
      push_cast
      ring

theorem allPlus_parDef (i : Fin D.R.m) (M : DSModel (Vc D i) (parDef D i)) : AllPlus M := fun τ a => by
  obtain ⟨-, q, -, hS⟩ := M.enum τ
  have h : (q a, M.ε τ a) ∈ parDef D i τ := hS ▸ Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 h
  exact (congrArg Prod.snd hx).symm

theorem order_parHol (i : Fin D.R.m) (M : DSModel (Wc D i) (parHol D i)) (τ : D.what₂.Tau) (a : Fin (Wc D i).rank) :
    M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1) := by
  obtain ⟨hn, hx⟩ := GlobalTheory.HolDS.enum_holPar
    (Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).rank.1) (M.enum τ)
  obtain ⟨x, rfl⟩ : ∃ x, a = Fin.cast hn (finSumFinEquiv x) :=
    ⟨finSumFinEquiv.symm (Fin.cast hn.symm a), by simp⟩
  rw [(hx x).2]
  rcases x with c | c <;> simp

theorem onb_of_adapted {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} (h : IsAdapted G 1 B) : Bᴴ * G * B = 1 := by
  obtain ⟨ε, h1, h2⟩ := h
  have h3 : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  calc Bᴴ * G * B = Bᴴ * G * (B * Formalism.REAL.Jm ε) := by rw [← h2, Matrix.one_mul]
    _ = 1 := by rw [← Matrix.mul_assoc, h1, h3]

section Dual

open GlobalTheory.CoefSpace

variable {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D}

theorem exists_dualPair (hθ : IsInfFam θ) (M : DSModel V S) (hp : AllPlus M) (lam : D.what₂.Tau → DomWeight V.rank)
    (hl : ∀ τ, M.lam τ = fun a => (((lam τ).w a : ℝ) + ((rhoVec V.rank a : ℚ) : ℝ))) (c : CoefA V)
    (e : VV ℂ lam ≃ₗ[ℂ] c.W)
    (he : ∀ u ∈ GinfC V, ∀ v, c.ρ u (e v) = e (rhoK lam (invTrK (GlobalTheory.CoefModel.realGL θ V u)) v)) :
    ∃ pr, IsDualPair θ M c pr := by
  have hA : ∀ τ, ∃ A : M.H τ →ₗ[ℂ] MvPolynomial (Fin V.rank × Fin V.rank) ℂ, Function.Injective A ∧
      (∀ x, A x ∈ nablaSq ℂ _ (lam τ)) ∧
      ∀ k : GL (Fin V.rank) ℂ, (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Matrix.unitaryGroup _ ℂ →
        ∀ x, A (M.σ τ (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) x) = sqAct ℂ _ (lam τ) k (A x) := fun τ => by
    have hε : M.ε τ = fun _ => true := funext (hp τ)
    have hds : IsHCTypeU _ (M.lam τ) (M.σ τ) := (GlobalTheory.RealPar.isDS_const_iff true _ _).1 (hε ▸ M.ds τ)
    obtain ⟨H', _, _, π', e', h1, h2, h3, h4⟩ := GlobalTheory.NablaType.exists_isHCTypeU_nablaSq _ (lam τ)
    rw [← hl] at h1
    obtain ⟨A, hA⟩ := GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU _ _ _ H' _ _ hds h1
    refine ⟨e' ∘ₗ A.toLinearMap, h2.comp A.injective, fun x => h3 _, fun k hk x => ?_⟩
    show e' (A (M.σ τ k x)) = sqAct ℂ _ (lam τ) k (e' (A x))
    rw [hA _ hk, h4 _ hk]
  choose A h1 h2 h3 using hA
  let B : D.what₂.Tau → GL (Fin V.rank) ℂ := fun τ => (M.fr_unit τ).unit
  have hB : ∀ τ, (B τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = M.fr τ := fun _ => rfl
  let T : SmT M →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau _).compLinearMap fun τ =>
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ).toLinearMap ∘ₗ A τ ∘ₗ (M.sm τ).subtype)
  have hT : ∀ v : M.Vec, T (PiTensorProduct.tprod ℂ v) = ten fun τ => A τ (v τ) := fun v => by
    simp [T, ten]
  let pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ :=
    (pairB lam).compl₁₂ (actP lam (invTrK B) ∘ₗ (VV ℂ lam).subtype ∘ₗ e.symm.toLinearMap) T
  have hpr : ∀ w t, pr (e w) t = pairB lam (actP lam (invTrK B) w.1) (T t) := fun w t => by
    simp [pr]
  refine ⟨pr, fun h0 => ?_, fun τ g hg w v u hu => ?_⟩
  · have hv : ∀ τ, ∃ v : M.sm τ, (v : M.H τ) ≠ 0 := fun τ => by
      have := (M.ds τ).1
      have := (M.ds τ).2.1
      obtain ⟨v, hv, hs⟩ := GlobalTheory.GardingVec.exists_smoothVec (M.ds τ).2.2.1 (M.fr_unit τ) (M.fr_gram τ)
      exact ⟨⟨v, Submodule.subset_span hs⟩, hv⟩
    choose v hv using hv
    refine GlobalTheory.Proof.TensorMapDescent.ten_ne_zero (fun τ => A τ (v τ)) (fun τ h => hv τ (h1 τ (h.trans (map_zero _).symm))) ?_
    refine congrArg Subtype.val ((pairingBNondegenerate_holds ℂ _ _ lam).2
      ⟨_, GlobalTheory.Proof.TensorMapDescent.ten_mem lam _ fun τ => h2 τ (v τ)⟩ fun y => ?_)
    have h4 : pr (e (rhoK lam (invTrK B)⁻¹ y)) (PiTensorProduct.tprod ℂ v) = 0 := by
      rw [h0]
      rfl
    have h5 : rhoK lam (invTrK B) (rhoK lam (invTrK B)⁻¹ y) = y := by
      rw [rhoK_mul, mul_inv_cancel, rhoK_one]
    rw [hpr, hT, ← rhoK_coe, h5] at h4
    rw [pairBK_apply]
    exact h4
  · obtain ⟨w, rfl⟩ := e.surjective w
    have ha := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
    set G := infGL θ V (atTau θ V τ g) with hGd
    let k := B * G * B⁻¹
    have hk : ∀ ρ, (k ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Matrix.unitaryGroup _ ℂ := fun ρ =>
      conj_unitary (by
        have := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (atTau θ V τ g) ρ
        rwa [hp.gram] at this)
    have hup : ∀ ρ, (Function.update v τ u ρ : M.H ρ) = M.σ ρ (k ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v ρ) := by
      intro ρ
      by_cases hρ : ρ = τ
      · subst hρ
        have e : (k ρ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = M.fr ρ * g * (M.fr ρ)⁻¹ := by
          show ((B ρ * G ρ * (B ρ)⁻¹ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = _
          rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hB, infGL_coe, ha.2.1]
        rw [Function.update_self, hu, e]
        rfl
      · have e : k ρ = 1 := by
          have : G ρ = 1 := Units.ext (ha.2.2 ρ hρ)
          show B ρ * G ρ * (B ρ)⁻¹ = 1
          rw [this, mul_one, mul_inv_cancel]
        rw [Function.update_of_ne hρ, e, Units.val_one, (M.ds ρ).2.2.1.1.1]
        rfl
    have e1 : T (PiTensorProduct.tprod ℂ (Function.update v τ u)) = actP lam k (T (PiTensorProduct.tprod ℂ v)) := by
      rw [hT, hT, actTen]
      congr 1
      funext ρ
      rw [hup, h3 ρ _ (hk ρ)]
    have e2 : rhoK lam (invTrK B) (rhoK lam (invTrK G) w) = rhoK lam (invTrK k) (rhoK lam (invTrK B) w) := by
      rw [rhoK_mul, rhoK_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
    rw [he _ ha.1, show GlobalTheory.CoefModel.realGL θ V (atTau θ V τ g) = G from rfl, hpr, hpr, ← rhoK_coe, e2, e1]
    exact pairingBInvariantK_holds ℂ _ _ lam k _ _

theorem exists_equiv_of_dualPair (hθ : IsInfFam θ) {M : DSModel V S} (hp : AllPlus M) {c c' : CoefA V} (hc : c.Is)
    (hc' : c'.Is) {pr pr'} (h : IsDualPair θ M c pr) (h' : IsDualPair θ M c' pr') :
    ∃ φ : c.W ≃ₗ[ℂ] c'.W, ∀ u ∈ GinfC V, ∀ w, φ (c.ρ u w) = c'.ρ u (φ w) := by
  have b := GlobalTheory.DefiniteMult.pair_bijective hθ hp hc h
  have b' := GlobalTheory.DefiniteMult.pair_bijective hθ hp hc' h'
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  obtain ⟨-, inj, π, hπ, -⟩ := GlobalTheory.DefLift.tensor_irreducible D V S M m hp
  have key := GlobalTheory.DefiniteMult.pair_tens hp (fun τ => (m τ).2.1) inj hπ h
  have key' := GlobalTheory.DefiniteMult.pair_tens hp (fun τ => (m τ).2.1) inj hπ h'
  let φ : c.W ≃ₗ[ℂ] c'.W := (LinearEquiv.ofBijective pr b).trans (LinearEquiv.ofBijective pr' b').symm
  have hφ : ∀ w, pr' (φ w) = pr w := fun w => (LinearEquiv.ofBijective pr' b').apply_symm_apply (pr w)
  let U : Submonoid (GA D V) :=
    { carrier := {u | ∀ w, φ (c.ρ u⁻¹ w) = c'.ρ u⁻¹ (φ w)}
      one_mem' := fun w => by rw [inv_one, map_one, map_one]; rfl
      mul_mem' := fun {a b} ha hb w => by
        rw [_root_.mul_inv_rev, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb, ha] }
  refine ⟨φ, fun u hu w => ?_⟩
  have := GlobalTheory.DefiniteMult.real_le hθ U (fun τ g hg w => by
    obtain ⟨k, rfl⟩ := hp.exists_unfr τ hg
    refine b'.1 (LinearMap.ext fun x => ?_)
    rw [hφ, ← key, ← key', hφ]) (inv_mem hu) w
  rwa [inv_inv] at this

end Dual

theorem weights_parHol (i : Fin D.R.m) {P : D.what₂.Tau → SPar} (hP : P = parAt (Wc D i) D.what₂.embLL)
    (M : DSModel (Wc D i) P) (h : ∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) :
    ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧
      (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧
      (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧
      (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1
        (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ)
        (x₁ τ) (x₂ τ) a : ℝ)) ∧
      ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2
        (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ)
        (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  subst hP
  exact GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i _ rfl M h

theorem ioEx (D : D7) : IoEx D := by
  rintro i M M' ψ θ χS χT ω hθ hω hχ c hc ⟨pr, hpr⟩ BV f hf
  have hp := allPlus_parDef i M
  have hord := order_parHol i M'
  obtain ⟨c', c0, hc', ht, -⟩ := GlobalTheory.CoefModel.exists_coef_round (Vc D i) hp.posDef
    (fun τ => Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ)
  obtain ⟨e, -, he⟩ := GlobalTheory.CoefReal.exists_real_model _ θ c' _ c0 hθ hc' ht
  obtain ⟨pr', hpr'⟩ := exists_dualPair hθ M hp _ (lam_parDef i M) c' e he
  obtain ⟨φ, hφ⟩ := exists_equiv_of_dualPair hθ hp hc hc' hpr hpr'
  have hBS : ∀ τ, (BV τ)ᴴ * gramAt D (Vc D i) τ * BV τ = 1 := fun τ => onb_of_adapted (hf τ).onS
  have hBu : ∀ τ, IsUnit (BV τ) := fun τ => (IsUnit.of_mul_eq_one_right _ (hBS τ))
  obtain ⟨x₁, x₂, x₃, hx⟩ := weights_parHol i (funext fun τ => (GlobalTheory.ThetaFiresProbe.parAt_fixed _ τ).symm) M' hord
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank := fun τ =>
    (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).rank.1.trans hrk.symm
  obtain ⟨io, h1, h2, v0, w0, hv0, hw0, h3⟩ := exists_io_poly D (Vc D i) (Wc D i) θ _ M' c' _ c0 hθ
    hc' ht BV hBu _ _ _ _ x₁ x₂ x₃ (hrk.le.trans (r_le_V i)) hpq hord
    (fun τ => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).aPlus_antitone) (fun τ => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).aM_anti) (fun τ => (hx τ).2.2.2.1)
    (fun τ => (hx τ).2.2.2.2)
  have hth : IsThetaFunO ψ (Vc D i) (Wc D i) f := by
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, by simp [Formalism.FrobeniusOrbits.Psi]⟩⟩
    exact (hf τ).theta
  have hact := GlobalTheory.T.weil_maximalCompact_fock_substitution_character D ψ θ (Vc D i) (Wc D i) _ _ ω _ M' BV hω hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq hord _ _ (fun τ => (hχ τ).1)
    (fun τ => (hχ τ).2) x₁ x₂ x₃ (fun τ => (hx τ).1) (fun τ => (hx τ).2.1)
    (fun τ => (hx τ).2.2.1) f hth (fun τ => (hf τ).vac)
  have hfr : ∀ τ, M'.fr τ * (M'.fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ))
  have hw1 : ‖φ.symm w0‖ ≠ 0 := norm_ne_zero_iff.2 fun h => by
    rw [φ.symm.map_eq_zero_iff.1 h, norm_zero] at hw0
    exact zero_ne_one hw0
  obtain ⟨io', hio⟩ : ∃ io' : LowT M' →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
      ∀ x w, io' x w = io x ((‖φ.symm w0‖ : ℂ) • φ w) :=
    ⟨LinearMap.compl₂ io ((‖φ.symm w0‖ : ℂ) • φ.toLinearMap), fun _ _ => rfl⟩
  refine ⟨io', fun u hu x w => ?_, fun τ k hk v u hu w => ?_, v0, (‖φ.symm w0‖ : ℂ)⁻¹ • φ.symm w0, hv0, ?_, ?_⟩
  · have e : (fun τ => M'.fr τ * compAt θ τ (Formalism.L2.Theta.mt (Wc D i) 1) * (M'.fr τ)⁻¹) = 1 := by
      funext τ; rw [compAt_mt_one', Matrix.mul_one, hfr]; rfl
    obtain ⟨a, b⟩ := hact u hu 1 (one_mem _) fun τ => by rw [congrFun e τ]; exact one_mem_K
    rw [hio, hio, hφ u hu, ← map_smul (c'.ρ u), ← h1 u hu a x]
    have := b (io x ((‖φ.symm w0‖ : ℂ) • φ w))
    rw [e] at this
    exact this
  · have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (conj_mem_UH M' τ hk)
    have e : (fun ρ => M'.fr ρ * compAt θ ρ (Formalism.L2.Theta.mt (Wc D i)
        (atTau θ (Wc D i) τ ((M'.fr τ)⁻¹ * k * M'.fr τ))) * (M'.fr ρ)⁻¹) = Pi.mulSingle τ k := by
      funext ρ
      rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
      by_cases h : ρ = τ
      · subst h
        rw [hs.2.1, Pi.mulSingle_eq_same]
        calc _ = (M'.fr ρ * (M'.fr ρ)⁻¹) * k * (M'.fr ρ * (M'.fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
          _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
      · rw [hs.2.2 ρ h, Pi.mulSingle_eq_of_ne h, Matrix.mul_one, hfr]
    have e' : (fun ρ => (BV ρ)⁻¹ * compAt θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * BV ρ) = 1 := by
      funext ρ
      rw [compAt_mt_one', Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ))]; rfl
    obtain ⟨-, b⟩ := hact 1 (one_mem _) _ hs.1 fun ρ => by
      rw [congrFun e ρ]
      by_cases h : ρ = τ
      · subst h; rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_K
    rw [hio, hio, ← h2 τ k hk v u hu]
    have := b (io (PiTensorProduct.tprod ℂ v) ((‖φ.symm w0‖ : ℂ) • φ w))
    rw [e, e'] at this
    exact this
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hw1]
  · rw [hio, map_smul φ, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hw1), one_smul, φ.apply_symm_apply]
    exact h3

theorem ioEx_of_discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, IoEx D :=
  fun _ _ => ioEx

end GlobalTheory.ArchRec.IoMap

end
