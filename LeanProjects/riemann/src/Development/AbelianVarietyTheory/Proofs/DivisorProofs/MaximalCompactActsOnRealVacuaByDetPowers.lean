import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormaliseMeanSquareOfCocompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPQContinuousCharacterEqDetPowProdStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumChar

variable {D : D7}

def InK (θ : InfFam D) (V : HSp D) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D V) : Prop :=
  g ∈ GinfC V ∧ ∀ τ, s τ * compAt θ τ (mt V g) = compAt θ τ (mt V g) * s τ

theorem inK_one (θ : InfFam D) (V : HSp D) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : InK θ V s 1 :=
  ⟨one_mem _, fun τ => by
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, Matrix.mul_one, Matrix.one_mul]⟩

theorem compAt_mt_mul (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (g g' : GA D V) :
    compAt θ τ (mt V (g * g')) = compAt θ τ (mt V g) * compAt θ τ (mt V g') := by
  rw [GlobalTheory.WeilVacMove.mt_mul, GlobalTheory.WeilVacMove.compAt_mul]

theorem InK.mul {θ : InfFam D} {V : HSp D} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {g g' : GA D V}
    (h : InK θ V s g) (h' : InK θ V s g') : InK θ V s (g * g') :=
  ⟨mul_mem h.1 h'.1, fun τ => by
    rw [compAt_mt_mul, ← Matrix.mul_assoc, h.2, Matrix.mul_assoc, h'.2, Matrix.mul_assoc]⟩

theorem real_char {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (c : GA D V → ℂ)
    (hm : ∀ g g', InK θ V s g → InK θ V s g' → c (g * g') = c g * c g') (hn : ∀ g, InK θ V s g → ‖c g‖ = 1)
    (hc : ContinuousOn c {g | InK θ V s g}) :
    ∃ x y : D.what₂.Tau → ℤ, ∀ g, InK θ V s g → c g = ∏ τ,
      ((1 / 2 : ℂ) • (1 + s τ) * compAt θ τ (mt V g) + (1 / 2 : ℂ) • (1 - s τ)).det ^ x τ *
        ((1 / 2 : ℂ) • (1 - s τ) * compAt θ τ (mt V g) + (1 / 2 : ℂ) • (1 + s τ)).det ^ y τ := by
  classical
  have hat : ∀ τ k, kᴴ * gramAt D V τ * k = gramAt D V τ → atTau θ V τ k ∈ GinfC V ∧
      compAt θ τ (mt V (atTau θ V τ k)) = k ∧ ∀ τ', τ' ≠ τ → compAt θ τ' (mt V (atTau θ V τ k)) = 1 :=
    fun τ k hk => GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hk
  have hK : ∀ τ k, kᴴ * gramAt D V τ * k = gramAt D V τ → s τ * k = k * s τ → InK θ V s (atTau θ V τ k) := by
    intro τ k h1 h2
    refine ⟨(hat τ k h1).1, fun τ' => ?_⟩
    by_cases e : τ' = τ
    · rw [e, (hat τ k h1).2.1, h2]
    · rw [(hat τ k h1).2.2 τ' e, Matrix.mul_one, Matrix.one_mul]
  have key : ∀ τ, ∃ x y : ℤ, ∀ k : Matrix (Fin V.rank) (Fin V.rank) ℂ, kᴴ * gramAt D V τ * k = gramAt D V τ →
      s τ * k = k * s τ → c (atTau θ V τ k) = ((1 / 2 : ℂ) • (1 + s τ) * k + (1 / 2 : ℂ) • (1 - s τ)).det ^ x *
        ((1 / 2 : ℂ) • (1 - s τ) * k + (1 / 2 : ℂ) • (1 + s τ)).det ^ y := by
    intro τ
    obtain ⟨p, q, B, B', b1, b2, b3, b4⟩ := GlobalTheory.T.exists_basis_adapted_to_cartan_involution' _ _ _ (hs τ).1 (hs τ).2.1 (hs τ).2.2
    refine GlobalTheory.T.unitaryPQ_continuous_character_eq_det_pow_prod _ p q _ _ B B' b1 b2 b3 b4 (fun k => c (atTau θ V τ k)) (fun k k' h1 h2 h3 h4 => ?_)
      (fun k h1 h2 => hn _ (hK τ k h1 h2)) ?_
    · rw [← hm _ _ (hK τ k h1 h2) (hK τ k' h3 h4)]
      exact congrArg c (GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ h1 h3)
    · exact hc.comp ((GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).mono fun k hk => hk.1)
        fun k hk => hK τ k hk.1 hk.2
  choose x y hxy using key
  refine ⟨x, y, fun g hg => ?_⟩
  have c1 : c 1 = 1 := by
    have e := hm 1 1 (inK_one θ V s) (inK_one θ V s)
    rw [mul_one] at e
    have e0 : c 1 ≠ 0 := by rw [← norm_ne_zero_iff, hn 1 (inK_one θ V s)]; exact one_ne_zero
    exact (mul_eq_left₀ e0).1 e.symm
  have ind : ∀ A : Finset D.what₂.Tau, ∀ g, InK θ V s g → (∀ τ, τ ∉ A → compAt θ τ (mt V g) = 1) →
      c g = ∏ τ ∈ A, c (atTau θ V τ (compAt θ τ (mt V g))) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro g hg h1
      have : g = 1 := GlobalTheory.PointAtPlace.eq_one_of_mem V g
        ((GlobalTheory.SmoothForms.RealPts.glue θ hθ V).1 g fun τ => h1 τ (Finset.notMem_empty τ)) hg.1
      rw [this, c1, Finset.prod_empty]
    | insert τ A hτ ih =>
      intro g hg h1
      have hu : (compAt θ τ (mt V g))ᴴ * gramAt D V τ * compAt θ τ (mt V g) = gramAt D V τ :=
        GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ
      obtain ⟨a1, a2, a3⟩ := hat τ _ hu
      have aK := hK τ _ hu (hg.2 τ)
      rw [Finset.prod_insert hτ]
      generalize atTau θ V τ (compAt θ τ (mt V g)) = a at a1 a2 a3 aK ⊢
      have e1 : compAt θ τ (mt V (a⁻¹ * g)) = 1 := by
        rw [compAt_mt_mul, ← a2, GlobalTheory.WeilVacMove.compAt_mt_inv_mul]
      have e2 : ∀ τ', τ' ≠ τ → compAt θ τ' (mt V (a⁻¹ * g)) = compAt θ τ' (mt V g) := fun τ' h => by
        rw [← Matrix.one_mul (compAt θ τ' (mt V (a⁻¹ * g))), ← a3 τ' h, ← compAt_mt_mul, mul_inv_cancel_left]
      have gK : InK θ V s (a⁻¹ * g) := ⟨mul_mem (inv_mem a1) hg.1, fun τ' => by
        by_cases e : τ' = τ
        · rw [e, e1, Matrix.mul_one, Matrix.one_mul]
        · rw [e2 τ' e, hg.2]⟩
      have e3 := ih _ gK fun τ' h => by
        by_cases e : τ' = τ
        · rw [e, e1]
        · rw [e2 τ' e]
          exact h1 τ' fun h' => (Finset.mem_insert.1 h').elim e h
      rw [← mul_inv_cancel_left a g, hm _ _ aK gK, e3, mul_inv_cancel_left]
      congr 1
      exact Finset.prod_congr rfl fun τ' h => by rw [e2 τ' fun e => hτ (e ▸ h)]
  rw [ind Finset.univ g hg fun τ h => (h (Finset.mem_univ τ)).elim]
  exact Finset.prod_congr rfl fun τ _ => hxy τ _ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ) (hg.2 τ)

variable {S T : HSp D}

theorem actO_fin {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) {x : WO S T}
    (hx : x.map (infPart D) = 0) : actO S T g h x = x := by
  have e1 : (mt S g⁻¹).map (finPart D) = 1 := congrArg Units.val (show finHom S g⁻¹ = 1 from inv_mem hg)
  have e2 : (mt T h).map (finPart D) = 1 := congrArg Units.val (show finHom T h = 1 from hh)
  have e3 : (actO S T g h x).map (infPart D) = x.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]
  have e4 : (actO S T g h x).map (finPart D) = x.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.mul_one, Matrix.one_mul]
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun e3 i) j) (congrFun (congrFun e4 i) j)

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem dRho_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hf' : IsThetaFunO ψ S T f') :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (f + f') =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f + Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f' := by
  obtain ⟨l1, l2, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  funext w
  have h := ((GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ l1 l2 hf).1 w).fun_add
    ((GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ l1 l2 hf').1 w)
  refine Eq.trans ?_ h.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  exact congrFun ((GlobalTheory.SplitScalar.heisL ψ S T _).map_add f f') w

theorem fock_heis (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (h : IsFockVacAt (heisO ψ S T) θ τ J f) (c : ℂ) {a : WO S T}
    (ha : a.map (infPart D) = 0) : IsFockVacAt (heisO ψ S T) θ τ J (c • heisO ψ S T a f) := by
  have := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ f hf τ J h Unit {()} (fun _ => a) (fun _ => c)
    fun _ _ => ha
  rwa [Finset.sum_singleton] at this

theorem theta_heis (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {a : WO S T}
    (ha : a.map (infPart D) = 0) : IsThetaFunO ψ S T (heisO ψ S T a f) := by
  have := GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 f hf Unit {()} (fun _ => a) (fun _ => 1)
    fun _ _ => ha
  rwa [Finset.sum_singleton, one_smul] at this

def finPts (S T : HSp D) : AddSubgroup (WO S T) := ((infPart D).toAddMonoidHom.mapMatrix).ker

theorem mem_finPts {x : WO S T} : x ∈ finPts S T ↔ x.map (infPart D) = 0 := Iff.rfl

def realVac (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (J : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (J τ) f}
  zero_mem' := ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun τ z => by
    funext w
    simp [annih, Formalism.IndefR.Datum.dRho, heisO]⟩
  add_mem' := fun {f f'} h h' => ⟨GlobalTheory.WeilVacMove.isTheta_add h.1 h'.1, fun τ z => by
    have e := h.2 τ z
    have e' := h'.2 τ z
    unfold annih at e e' ⊢
    rw [dRho_add hψ hθ τ _ h.1 h'.1, dRho_add hψ hθ τ _ h.1 h'.1, smul_add, add_add_add_comm, e, e', add_zero]⟩
  smul_mem' := fun c f h => ⟨GlobalTheory.WeilVacMove.isTheta_smul c h.1, fun τ => by
    have := fock_heis hψ hθ h.1 (h.2 τ) c (finPts S T).zero_mem
    rwa [GlobalTheory.WeilVacMove.heisO_zero] at this⟩

variable {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem vac_ne_zero {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT LS LT f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 (0 : WO S T → ℂ) = 1 := hn p hp
  simp [nrm2] at n1

theorem vac_line (kS : S.SigOK) (kT : T.SigOK) (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) {f₀ f : WO S T → ℂ}
    (h₀ : IsVacO ψ θ S T sS sT ΛS ΛT f₀) (hf : f ∈ realVac h₀.1 h₀.2.inf fun τ => cplxO (sS τ) (sT τ))
    (hl : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f) : ∃ c : ℂ, f = c • f₀ := by
  by_cases f0 : f = 0
  · exact ⟨0, by rw [f0, zero_smul]⟩
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨-, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hcov f hf.1.cont f0
    (GlobalTheory.WeilVacMove.norm_periodic h₀.1 hf.1)
  have hcf := Submodule.smul_mem _ c hf
  have h1 : IsVacO ψ θ S T sS sT ΛS ΛT (c • f) := ⟨h₀.1, h₀.2.inf, hcf.1,
    ⟨fun u hu => by rw [GlobalTheory.SplitScalar.heisO_smul, hl.1 u hu],
      fun e he u hu h => by rw [GlobalTheory.SplitScalar.heisO_smul, hl.2 e he u hu h]⟩, hcf.2, h₀.2.norm.1,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩
  obtain ⟨u, -, hu⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ h₀.1 h₀.2.inf S T sS sT kS kT hS hT ΛS ΛT dS dT f₀ _ h₀ h1
  have c0 : c ≠ 0 := fun e => vac_ne_zero h1 (by rw [e, zero_smul])
  exact ⟨c⁻¹ * u, by rw [mul_smul, ← hu, inv_smul_smul₀ c0]⟩

set_option maxHeartbeats 1000000 in

theorem mem_span (kS : S.SigOK) (kT : T.SigOK) (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ))
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) {f₀ f : WO S T → ℂ}
    (h₀ : IsVacO ψ θ S T sS sT ΛS ΛT f₀) (hf : f ∈ realVac h₀.1 h₀.2.inf fun τ => cplxO (sS τ) (sT τ)) :
    f ∈ Submodule.span ℂ (Set.range fun x : finPts S T => heisO ψ S T x f₀) := by
  have hψ := h₀.1
  have hθ := h₀.2.inf
  obtain ⟨h1, -, h3⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ dS dT
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT dS.1.fg dT.1.fg fun _ => True
  have hlev := (GlobalTheory.T.completedHomLattice_multiple_mem_open_level D S T ΛS ΛT dS dT (GlobalTheory.T.completedHomLattice_finitelyGenerated D S T ΛS ΛT dS dT)).1
  have hinf := fun u => GlobalTheory.SplitScalar.latO_fin (u := u) (S := S) (T := T) (LS := (ΛS : Set (Fin S.rank → D.host.E)))
    (LT := (ΛT : Set (Fin T.rank → D.host.E)))
  let M := realVac hψ hθ fun τ => cplxO (sS τ) (sT τ)
  have hline := fun f (hf : f ∈ M) => vac_line kS kT hS hT dS dT (f := f) h₀ hf
  have hf : f ∈ M := hf
  have hM : f₀ ∈ M := ⟨h₀.2.theta, h₀.2.fock⟩
  have hne := vac_ne_zero h₀
  have hlat := h₀.2.lat
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h3 hfin hlev hinf hline hlat
  let ρ : finPts S T → M →ₗ[ℂ] M := fun x => (GlobalTheory.SplitScalar.heisL ψ S T x).restrict fun f hf =>
    ⟨theta_heis hψ hf.1 x.2, fun τ => by
      have := fock_heis hψ hθ hf.1 (hf.2 τ) 1 x.2
      rwa [one_smul] at this⟩
  have hρ : ∀ x v, ((ρ x v : M) : WO S T → ℂ) = heisO ψ S T x v := fun _ _ => rfl
  let e : M := ⟨f₀, hM⟩
  have hsq : ∀ x a : WO S T, ψ (symplOH S T x a) ^ 2 = ψ (symplO S T x a) := fun x a => by
    rw [sq, ← AddChar.map_add_eq_mul, GlobalTheory.SplitScalar.symplOH_add_self]
  have key := GlobalTheory.T.mem_span_heisenberg_translates_of_vacuum (finPts S T) M (fun x y => ψ (symplOH S T x y)) ρ (Λ.addSubgroupOf (finPts S T)) e
    (fun x y z => by
      rw [← AddChar.map_add_eq_mul, ← GlobalTheory.SplitScalar.symplOH_add_left]; rfl)
    (fun x y z => by
      rw [← AddChar.map_add_eq_mul, ← GlobalTheory.SplitScalar.symplOH_add_right]; rfl)
    (fun x => by
      have : symplO S T x x = 0 := (GlobalTheory.T.symplecticAdelicForm_biadditive_alternating_rational D S T).2.2.2.1 x
      simp only [symplOH, this, mul_zero, AddChar.map_zero_eq_one])
    (fun v => Subtype.ext (GlobalTheory.SplitScalar.heisO_zero ψ S T v))
    (fun x y v => Subtype.ext (GlobalTheory.SplitScalar.heisO_heisO ψ S T x y v))
    (fun x => by
      rw [AddSubgroup.mem_addSubgroupOf, h1 x x.2]
      exact ⟨fun h a ha => (hsq _ _).trans (h a ha), fun h a ha => (hsq _ _).symm.trans (h ⟨a, hinf a ha⟩ ha)⟩)
    (fun N hN x => by
      refine ⟨⟨incA D (N : D.host.E)⁻¹ • (x : WO S T), ?_⟩, Subtype.ext ?_⟩
      · funext i j
        have : infPart D (x.1 i j) = 0 := congrFun (congrFun (mem_finPts.1 x.2) i) j
        show infPart D (_ * x.1 i j) = 0
        rw [RingHom.map_mul, this, mul_zero]
      · show N • (incA D (N : D.host.E)⁻¹ • (x : WO S T)) = x
        rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hN])
    (fun N hN => by
      obtain ⟨R, hR, h⟩ := hfin N hN
      refine ⟨Subtype.val ⁻¹' R, hR.preimage Subtype.val_injective.injOn, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, e⟩ := h t ht
      refine ⟨t - N • ⟨u, hinf u hu⟩, ?_, ⟨u, hinf u hu⟩, hu, (sub_add_cancel _ _).symm⟩
      show (t : WO S T) - N • u ∈ R
      rwa [e, add_sub_cancel_right])
    (fun h => hne (congrArg Subtype.val h))
    (fun u hu => by
      obtain ⟨ε, -, h⟩ := h3 f₀ hlat u hu
      exact ⟨ε, Subtype.ext (h f₀ hlat)⟩)
    (fun u hu => Subtype.ext (hlat.1 u hu))
    (fun v hv => by
      have hv1 : ∀ u ∈ Λ, heisO ψ S T u f₀ = f₀ → heisO ψ S T u v = v := fun u hu h => by
        have := congrArg Subtype.val (hv ⟨u, hinf u hu⟩ hu 1 (Subtype.ext (h.trans (one_smul ℂ f₀).symm)))
        rwa [one_smul] at this
      obtain ⟨c, hc⟩ := hline v v.2 ⟨fun u hu => hv1 _ (Λ.nsmul_mem hu 2) (hlat.1 u hu),
        fun e he u hu h => hv1 u hu (hlat.2 e he u hu h)⟩
      exact ⟨c, Subtype.ext hc⟩)
    ⟨f, hf⟩ (by
      obtain ⟨U, hU, h⟩ := hf.1.level
      obtain ⟨N, hN, h'⟩ := hlev U hU
      exact ⟨N, hN, fun u hu => Subtype.ext (h _ (h' u hu) (N • u).2)⟩)
  have := Submodule.apply_mem_span_image_of_mem_span M.subtype key
  rwa [← Set.range_comp] at this

theorem vacuum_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∃ x₁ x₂ y₁ y₂ : D.what₂.Tau → ℤ, (∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * ((1 / 2 : ℂ) • (1 + sS τ) * compAt θ τ (mt S g) + (1 / 2 : ℂ) • (1 - sS τ)).det ^ y₁ τ * ((1 / 2 : ℂ) • (1 - sS τ) * compAt θ τ (mt S g) + (1 / 2 : ℂ) • (1 + sS τ)).det ^ y₂ τ) • f) := by
  intro D ψ θ S T χS χT om hW hθ kS kT sS sT hS hT
  have dS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have dT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨f₀, h₀⟩ := GlobalTheory.VacuumO.vacExists D ψ θ hW.std hθ S T sS sT kS kT hS hT _ _ dS dT
  obtain ⟨w, hw⟩ : ∃ w, f₀ w ≠ 0 := Function.ne_iff.1 (vac_ne_zero h₀)
  let c : GA D S × GA D T → ℂ := fun p => om p f₀ w / f₀ w
  have cc : Continuous c := (hW.om_cont f₀ h₀.2.theta w).div_const _
  have hc : ∀ g h, InK θ S sS g → InK θ T sT h → ‖c (g, h)‖ = 1 ∧ om (g, h) f₀ = c (g, h) • f₀ := by
    intro g h hg hh
    have h1 := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ g h hg.2 hh.2
      (fun u => ⟨fun hu => ⟨u, hu, (actO_fin hg.1 hh.1 (GlobalTheory.SplitScalar.latO_fin hu)).symm⟩,
        fun ⟨u₀, hu, e⟩ => by rwa [e, actO_fin hg.1 hh.1 (GlobalTheory.SplitScalar.latO_fin hu)]⟩) f₀ h₀
    obtain ⟨u, hu, e⟩ := GlobalTheory.VacUnique.vacUniqueO D ψ θ hW.std hθ S T sS sT kS kT hS hT _ _ dS dT f₀ _ h₀ h1
    have : c (g, h) = u := by
      show om (g, h) f₀ w / f₀ w = u
      rw [e, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hw]
    rw [this]
    exact ⟨hu, e⟩
  have hm : ∀ g h g' h', InK θ S sS g → InK θ T sT h → InK θ S sS g' → InK θ T sT h' →
      c (g * g', h * h') = c (g, h) * c (g', h') := by
    intro g h g' h' a b a' b'
    have e : om (g * g', h * h') f₀ = (c (g, h) * c (g', h')) • f₀ := by
      rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, (hc _ _ a' b').2, map_smul, (hc _ _ a b).2, smul_smul,
        mul_comm]
    show om (g * g', h * h') f₀ w / f₀ w = _
    rw [e, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hw]
  have oS := inK_one θ S sS
  have oT := inK_one θ T sT
  obtain ⟨x₁, x₂, hx⟩ := real_char hθ T sT hT (fun h => c (1, h))
    (fun h h' a a' => by rw [← hm 1 h 1 h' oS a oS a', mul_one]) (fun h a => (hc 1 h oS a).1)
    (cc.comp (Continuous.prodMk_right 1)).continuousOn
  obtain ⟨y₁, y₂, hy⟩ := real_char hθ S sS hS (fun g => c (g, 1))
    (fun g g' a a' => by rw [← hm g 1 g' 1 a oT a' oT, mul_one]) (fun g a => (hc g 1 a oT).1)
    (cc.comp (Continuous.prodMk_left 1)).continuousOn
  refine ⟨x₁, x₂, y₁, y₂, fun f hf hv g hg h hh cS cT => ?_⟩
  have e1 : om (g, h) f = c (g, h) • f := by
    have hs := mem_span kS kT hS hT dS dT h₀ (f := f) ⟨hf, hv⟩
    clear hf hv
    induction hs using Submodule.span_induction with
    | mem _ hx =>
      obtain ⟨x, rfl⟩ := hx
      show om (g, h) (heisO ψ S T x f₀) = c (g, h) • heisO ψ S T x f₀
      rw [hW.om_heis g h _ _ h₀.2.theta, actO_fin hg hh x.2, (hc g h ⟨hg, cS⟩ ⟨hh, cT⟩).2,
        GlobalTheory.SplitScalar.heisO_smul]
    | zero => rw [map_zero, smul_zero]
    | add a b _ _ ha hb => rw [map_add, ha, hb, smul_add]
    | smul r a _ ha => rw [map_smul, ha, smul_comm]
  have e2 := hm 1 h g 1 oS ⟨hh, cT⟩ ⟨hg, cS⟩ oT
  rw [one_mul, mul_one] at e2
  rw [e1, e2, hx h ⟨hh, cT⟩, hy g ⟨hg, cS⟩, ← Finset.prod_mul_distrib]
  simp only [mul_assoc]

end GlobalTheory.VacuumChar

end
