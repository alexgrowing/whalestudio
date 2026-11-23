import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicAdmissibleSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjectiveStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.FrameChange

open Topology Filter in

theorem cont_apply_Om {l : ℕ} [Fact l.Prime] (d : Om l) : Continuous fun g : GQ l => g d := by
  refine continuous_iff_continuousAt.2 fun g₀ => tendsto_nhds_of_eventually_eq ?_
  let S := MulAction.stabilizer (GQ l) d
  have hS : (S : Set (GQ l)) ∈ 𝓝 (g₀⁻¹ * g₀) := by
    rw [inv_mul_cancel]
    exact (stabilizer_isOpen_of_isIntegral d).mem_nhds S.one_mem
  filter_upwards [(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hS] with g hg
  have h : (g₀⁻¹ * g) • d = d := hg
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h

open Topology Filter in

theorem cont_σC {l : ℕ} [Fact l.Prime] (y : ℂ_[l]) : Continuous fun g : GQ l => Formalism.Per.σC g y := by
  refine continuous_iff_continuousAt.2 fun g₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨d, hd⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt y
    (show (0 : ℝ) < ε / 3 by positivity)
  have h1 := Metric.tendsto_nhds.1 ((cont_apply_Om d).tendsto g₀) (ε / 3) (by positivity)
  filter_upwards [h1] with g hg
  have e : ∀ g' : GQ l, dist (Formalism.Per.σC g' y) (Formalism.Per.σC g' (d : ℂ_[l])) = dist y (d : ℂ_[l]) := fun g' => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, GlobalTheory.RingBasics.norm_σC]
  have e2 : dist (Formalism.Per.σC g (d : ℂ_[l])) (Formalism.Per.σC g₀ (d : ℂ_[l])) = dist (g d) (g₀ d) := by
    rw [GlobalTheory.RingBasics.σC_coe, GlobalTheory.RingBasics.σC_coe, UniformSpace.Completion.dist_eq]
  calc dist (Formalism.Per.σC g y) (Formalism.Per.σC g₀ y)
      ≤ dist (Formalism.Per.σC g y) (Formalism.Per.σC g (d : ℂ_[l])) + dist (Formalism.Per.σC g (d : ℂ_[l])) (Formalism.Per.σC g₀ (d : ℂ_[l])) +
        dist (Formalism.Per.σC g₀ (d : ℂ_[l])) (Formalism.Per.σC g₀ y) := dist_triangle4 _ _ _ _
    _ < ε := by rw [e, e2, dist_comm (Formalism.Per.σC g₀ _), e]; linarith

theorem cont_of_frame : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (N : ↥(GK K) → Matrix n n ↥(MaximalUnramifiedExtension l)) (W : GL n P.R.BdR) (k : n → ℤ), UnitM P W → (∀ g : ↥(GK K), (N g).map (kd P) = ((W⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ k j : ℚ_[l]ˣ) : ℚ_[l])) * (W : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l))) → ∀ i j, Continuous fun g : ↥(GK K) => ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  intro l _ P AI T n _ _ K N W k hW hN i j
  obtain ⟨S, θ, hS, -, -, hθom, hθg⟩ := GlobalTheory.T.exists_theta_deRhamFilZero_surjective l P AI T
  have hemb : Topology.IsEmbedding (fun x : Om l => (x : ℂ_[l])) :=
    (UniformSpace.Completion.isUniformEmbedding_coe (Om l)).isEmbedding
  let a : n → ℂ_[l] := fun k' => θ ⟨((W⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i k', (hS _).2 (hW.2 i k')⟩
  let b : n → ℂ_[l] := fun k' => θ ⟨(W : Matrix n n P.R.BdR) k' j, (hS _).2 (hW.1 k' j)⟩
  have key : ∀ g : ↥(GK K), (((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l) : ℂ_[l]) =
      ∑ k', a k' * (((algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l])) : Om l) : ℂ_[l]) *
        Formalism.Per.σC (g : GQ l) (b k') := by
    intro g
    have e := congrFun (congrFun (hN g) i) j
    rw [Matrix.map_apply, Matrix.mul_apply] at e
    obtain ⟨h0, hθ0⟩ := hθom ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l)
    rw [← hθ0]
    let xa : n → ↥S := fun k' => ⟨((W⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i k', (hS _).2 (hW.2 i k')⟩
    let xq : n → ↥S := fun k' => ⟨algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l])),
      (hS _).2 (om_mem_Fil P _)⟩
    let xb : n → ↥S := fun k' => ⟨P.actQdR (g : GQ l) ((W : Matrix n n P.R.BdR) k' j), (hS _).2 (Fil_act _ (hW.1 k' j))⟩
    have hsum : (⟨algebraMap (Om l) P.R.BdR ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l), h0⟩ : ↥S) = ∑ k', xa k' * xq k' * xb k' := by
      apply Subtype.ext
      push_cast
      rw [show algebraMap (Om l) P.R.BdR ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l) = kd P (N g i j) from rfl, e]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [Matrix.mul_diagonal, Matrix.map_apply]
      change _ = ((W⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) i k' *
        algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l])) *
        P.actQdR (g : GQ l) ((W : Matrix n n P.R.BdR) k' j)
      rw [← IsScalarTower.algebraMap_apply]
    rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [map_mul, map_mul]
    obtain ⟨h1, h2⟩ := hθom (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l]))
    obtain ⟨h3, h4⟩ := hθg (g : GQ l) ⟨(W : Matrix n n P.R.BdR) k' j, (hS _).2 (hW.1 k' j)⟩
    have e1 : θ (xq k') = (((algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l])) : Om l) : ℂ_[l]) := h2
    have e2 : θ (xb k') = Formalism.Per.σC (g : GQ l) (b k') := h4
    rw [e1, e2]
  refine hemb.continuous_iff.2 ((continuous_congr fun g => (key g).symm).1 ?_)
  refine continuous_finsetSum _ fun k' _ => ?_
  have hχ : Continuous fun g : GQ l => (P.χQ g : ℚ_[l]) := GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc
  have hχk : Continuous fun g : ↥(GK K) => ((P.χQ (g : GQ l) ^ k k' : ℚ_[l]ˣ) : ℚ_[l]) := by
    simp only [Units.val_zpow_eq_zpow_val]
    exact (hχ.comp continuous_subtype_val).zpow₀ _ fun g => Or.inl (Units.ne_zero _)
  refine (continuous_const.mul ?_).mul ?_
  · exact (UniformSpace.Completion.continuous_coe _).comp ((continuous_algebraMap ℚ_[l] (Om l)).comp hχk)
  · exact (cont_σC (b k')).comp continuous_subtype_val

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem act_tz (g : GQ l) (a : ℤ) :
    P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  rw [tz, ← iota_act, Inhab.act_zpow, map_mul, AlgHom.commutes]

theorem phi_iter_act (m : ℕ) (g : GQ l) (b : P.R.B) : P.φB^[m] (P.actQ g b) = P.actQ g (P.φB^[m] b) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]

end GlobalTheory.PMon.FrameChange

namespace GlobalTheory.PMon

open FrameChange in

theorem exists_rep_of_fixed_frame_change : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w e : Fin r → n → ℤ) (U : Fin r → GL n P.R.BdR) (A : GL n P.R.B), IsRat r ρ → (∀ (m : Fin r) (g : ↥(GK K)), matD P ρ m g * (U m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])) → (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) → (∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (e m j)) * (W : Matrix n n P.R.BdR)) → ∃ ρ' : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l), IsRat r ρ' ∧ Framed P ρ' (fun m j => w m j + e m j) ∧ (AdmSt P ρ' → AdmSt P ρ) := by
  intro l _ P AI T n _ _ K r ρ w e U A hρ hU hA hfr
  choose W hWu hAW using hfr
  haveI := nontrivial_B P
  have alg_inj : Function.Injective (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective
  let φr : P.R.B →+* P.R.B := ((P.φB ^ r : P.R.B →ₐ[ℚ_[l]] P.R.B) : P.R.B →+* P.R.B)
  have hφr : ∀ b, φr b = P.φB^[r] b := fun b => by simp [φr, AlgHom.coe_pow]
  let X : ↥(GK K) → Matrix n n P.R.B := fun g =>
    ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B) * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) *
      (A : Matrix n n P.R.B).map (P.actQ (g : GQ l))
  have hXA : ∀ g, (A : Matrix n n P.R.B) * X g =
      (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) * (A : Matrix n n P.R.B).map (P.actQ (g : GQ l)) := by
    intro g
    simp only [X, ← mul_assoc, Units.mul_inv, one_mul]

  have h1 : (A : Matrix n n P.R.B).map φr = A := by
    ext i j; rw [Matrix.map_apply, hφr, hA]
  have h2 : ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B).map φr = ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B) := by
    have h3 : ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B).map φr * (A : Matrix n n P.R.B) = 1 := by
      conv_lhs => rw [← h1]
      rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    calc _ = ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B).map φr *
          ((A : Matrix n n P.R.B) * ((A⁻¹ : GL n P.R.B) : Matrix n n P.R.B)) := by rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, h3, one_mul]
  have hXfix : ∀ g i j, P.φB^[r] (X g i j) = X g i j := by
    intro g i j
    have eR : ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map φr =
        (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
      ext a b; rw [Matrix.map_apply, Matrix.map_apply, hφr, phi_iter_kur, hρ.rat]
    have eA : ((A : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map φr = (A : Matrix n n P.R.B).map (P.actQ (g : GQ l)) := by
      ext a b; rw [Matrix.map_apply, Matrix.map_apply, hφr, phi_iter_act, hA]
    have e : (X g).map φr = X g := by
      simp only [X, Matrix.map_mul, h2, eR, eA]
    rw [← hφr]; exact congrFun (congrFun e i) j

  have hev : ∀ (m : Fin r) g, (X g).map (ev P m) = (((W m)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) *
      Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (w m j + e m j) : ℚ_[l]ˣ) : ℚ_[l])) *
      (W m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) := by
    intro m g
    have hE : ∀ M : Matrix n n P.R.B, M.map (ev P m) = M.map (evHom P m) := fun M => by
      ext; simp [evHom_apply]
    have key := congrArg (fun M => M.map (evHom P m)) (hXA g)
    simp only [Matrix.map_mul] at key
    have k2 : ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map (evHom P m) = matD P ρ m g := by
      ext i j; simp [matD, evHom_apply, ev_kur]
    have k3 : ((A : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map (evHom P m) =
        ((A : Matrix n n P.R.B).map (evHom P m)).map (P.actQdR (g : GQ l)) := by
      ext i j; simp [evHom_apply, ev_act]
    rw [k2, k3, ← hE, hAW m, ← hE] at key
    set D := Matrix.diagonal (fun j => tz P (e m j))
    set Q' := Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (w m j + e m j) : ℚ_[l]ˣ) : ℚ_[l]))
    have hD : Matrix.diagonal (fun j => tz P (-e m j)) * D = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext j; rw [← tz_add, neg_add_cancel, tz_zero]
    have hDg : D.map (P.actQdR (g : GQ l)) = Matrix.diagonal (fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (e m j) : ℚ_[l]ˣ) : ℚ_[l])) * D := by
      rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
      congr 1; funext j; exact FrameChange.act_tz P _ _
    have hcomm : Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w m j : ℚ_[l]ˣ) : ℚ_[l])) *
        (Matrix.diagonal (fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (e m j) : ℚ_[l]ˣ) : ℚ_[l])) * D) =
        D * Q' := by
      simp only [D, Q', Matrix.diagonal_mul_diagonal]
      congr 1; funext j
      rw [zpow_add, Units.val_mul, map_mul]; ring
    rw [Matrix.map_mul, Matrix.map_mul, ← mul_assoc, ← mul_assoc, hU m g, hDg, mul_assoc _ _ (Matrix.diagonal _ * D),
      hcomm] at key

    have key2 : (W m : Matrix n n P.R.BdR) * (X g).map (ev P m) = Q' * (W m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) := by
      have k4 : (U m : Matrix n n P.R.BdR) * (D * ((W m : Matrix n n P.R.BdR) * (X g).map (ev P m))) =
          (U m : Matrix n n P.R.BdR) * (D * (Q' * (W m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)))) := by
        simpa only [mul_assoc] using key
      have k5 := (Units.mul_right_inj (U m)).mp k4
      have k6 := congrArg (fun M => Matrix.diagonal (fun j => tz P (-e m j)) * M) k5
      simpa only [← mul_assoc, hD, one_mul] using k6
    calc _ = (((W m)⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) * ((W m : Matrix n n P.R.BdR) * (X g).map (ev P m)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [key2, mul_assoc]
  have hFil : ∀ (m : Fin r) g i j, ev P m (X g i j) ∈ Fil P 0 := by
    intro m g i j
    have := congrFun (congrFun (hev m g) i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.mul_apply]
    refine Fil_sum fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.map_apply]
    exact Fil_mul_left (Fil_mul_left ((hWu m).2 i k) (q_mem_Fil P _)) (Fil_act _ ((hWu m).1 k j))
  have hpz := fun g i j => GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero l P AI T r hρ.pos (X g i j) (hXfix g i j)
    (fun k hk => hFil ⟨k, hk⟩ g i j)
  choose N hNfr hNeq using hpz
  have hNmap : ∀ g, (Matrix.of (N g)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) = X g := fun g => by
    ext i j; rw [Matrix.map_apply, Matrix.of_apply, ← hNeq]
  have hNK : ∀ g i j, ((N g i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := fun g i j => hρ.le _ (hNfr g i j)
  have hρK : ∀ g i j, (((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := fun g i j => hρ.le _ (hρ.rat g i j)
  have hXact : ∀ g h : ↥(GK K), (X h).map (P.actQ (g : GQ l)) = X h := by
    intro g h; ext i j; rw [Matrix.map_apply, hNeq, act_kur P g (hNK h i j)]
  have hRact : ∀ g h : ↥(GK K), ((ρ h : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map (P.actQ (g : GQ l)) =
      (ρ h : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
    intro g h; ext i j; rw [Matrix.map_apply, Matrix.map_apply, act_kur P g (hρK h i j)]
  have hX1 : X 1 = 1 := by
    have hm1 : (A : Matrix n n P.R.B).map (P.actQ ((1 : ↥(GK K)) : GQ l)) = A := by
      ext i j; simp
    simp only [X, hm1, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), mul_one, Units.inv_mul]
  have hXmul : ∀ g h, X (g * h) = X g * X h := by
    intro g h
    apply (Units.mul_right_inj A).mp
    have hAgh : (A : Matrix n n P.R.B).map (P.actQ ((g * h : ↥(GK K)) : GQ l)) =
        ((A : Matrix n n P.R.B).map (P.actQ (h : GQ l))).map (P.actQ (g : GQ l)) := by
      ext i j; simp [AlgEquiv.mul_apply]
    rw [hXA, ← mul_assoc, hXA, mul_assoc, ← hXact g h, ← Matrix.map_mul, hXA, Matrix.map_mul, hRact, ← mul_assoc,
      map_mul ρ, Units.val_mul, Matrix.map_mul, hAgh]
  let ρ'' : ↥(GK K) →* Matrix n n ↥(MaximalUnramifiedExtension l) :=
    { toFun := fun g => Matrix.of (N g)
      map_one' := by
        have h : (Matrix.of (N 1)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) = (1 : Matrix n n ↥(MaximalUnramifiedExtension l)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
          rw [hNmap, hX1, Matrix.map_one _ (map_zero _) (map_one _)]
        exact Matrix.map_injective alg_inj h
      map_mul' := fun g h => by
        have h' : (Matrix.of (N (g * h))).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) =
            (Matrix.of (N g) * Matrix.of (N h)).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) := by
          rw [Matrix.map_mul, hNmap, hNmap, hNmap, hXmul]
        exact Matrix.map_injective alg_inj h' }
  have hρ' : ∀ g, ((ρ''.toHomUnits g : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = Matrix.of (N g) := fun g => rfl
  have hmatD : ∀ (m : Fin r) g, matD P ρ''.toHomUnits m g = (X g).map (ev P m) := by
    intro m g; ext i j
    rw [matD, hρ', Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, hNeq, ev_kur]
  refine ⟨ρ''.toHomUnits, ?_, ?_, ?_⟩
  · refine { pos := hρ.pos, le := hρ.le, rat := fun g i j => hNfr g i j, cont := fun i j => ?_ }
    let m0 : Fin r := ⟨0, hρ.pos⟩
    refine FrameChange.cont_of_frame l P AI T n K (fun g => Matrix.of (N g)) (W m0) (fun j => w m0 j + e m0 j) (hWu m0)
      (fun g => ?_) i j
    rw [← hev m0 g]
    ext a b
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, hNeq, ev_kur]
    rfl
  · intro m
    refine ⟨(W m)⁻¹, ⟨fun i j => (hWu m).2 i j, fun i j => ?_⟩, fun g => ?_⟩
    · rw [inv_inv]; exact (hWu m).1 i j
    · rw [hmatD, hev, mul_assoc _ _ (Matrix.map _ _), ← Matrix.map_mul, Units.mul_inv,
        Matrix.map_one _ (map_zero _) (map_one _), mul_one]
  · rintro ⟨K', hK, Q', hQ'⟩
    refine ⟨K', hK, Matrix.GeneralLinearGroup.map (Polynomial.C : P.R.B →+* Bst P) A * Q', fun g => ?_⟩
    have hQg := hQ' g
    have e1 : ((Matrix.GeneralLinearGroup.map (Polynomial.C : P.R.B →+* Bst P) A : GL n (Bst P)) : Matrix n n (Bst P)) =
        (A : Matrix n n P.R.B).map (Polynomial.C : P.R.B →+* Bst P) := rfl
    have e2 : ((A : Matrix n n P.R.B).map (Polynomial.C : P.R.B →+* Bst P)).map (actSt P (g : GQ l)) =
        ((A : Matrix n n P.R.B).map (P.actQ (g : GQ l))).map (Polynomial.C : P.R.B →+* Bst P) := by
      ext i j; simp [actSt_C]
    have e3 : ∀ M : Matrix n n ↥(MaximalUnramifiedExtension l), M.map (ks P) = (M.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)).map
        (Polynomial.C : P.R.B →+* Bst P) := fun M => by ext; rfl
    rw [Units.val_mul, Matrix.map_mul, e1, e2, e3, ← mul_assoc, ← Matrix.map_mul, ← hXA, Matrix.map_mul, mul_assoc,
      ← hNmap, ← e3]
    exact congrArg _ hQg

end GlobalTheory.PMon
