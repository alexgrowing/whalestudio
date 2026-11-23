import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinTranslate

open GlobalTheory.DualPairCheck

variable {D : D7}

def eInf (D : D7) : AF D.host.F := pairA D.host.F 1 0

theorem smul_eq_zero_of_inf {a : AE D} (h : infPart D a = 0) : eInf D • a = 0 := by
  let s : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
    TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id
  have key : ∀ a : AE D, eInf D • a = s (infPart D a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add a b ha hb => rw [smul_add, ha, hb, RingHom.map_add, map_add]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      have : eInf D • a = LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F) (fstA D.host.F a) :=
        Prod.ext (one_mul _) (zero_mul _)
      rw [this]
      rfl
  rw [key, h, map_zero]

theorem smul_eq_self_of_fin {a : AE D} (h : finPart D a = 0) : eInf D • a = a := by
  let s : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
    TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id
  have key : ∀ a : AE D, (1 - eInf D) • a = s (finPart D a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add a b ha hb => rw [smul_add, ha, hb, RingHom.map_add, map_add]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      have : (1 - eInf D) • a = LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) (sndA D.host.F a) :=
        Prod.ext (show (1 - 1) * a.1 = 0 by rw [sub_self, zero_mul]) (show (1 - 0) * a.2 = a.2 by rw [sub_zero, one_mul])
      rw [this]
      rfl
  have := key a
  rw [h, map_zero, sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem cA_smul (c : AF D.host.F) (a : AE D) : cA D (c • a) = c • cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add a b ha hb => rw [smul_add, RingHom.map_add, RingHom.map_add, ha, hb, smul_add]
  | tmul a x => rfl

variable (S T : HSp D)

theorem symplOH_add_left (x x' y : WO S T) : symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  unfold symplOH symplO hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem symplOH_add_right (x y y' : WO S T) : symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  unfold symplOH symplO hO
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

theorem symplOH_smul_left (c : AF D.host.F) (x y : WO S T) : symplOH S T (c • x) y = c * symplOH S T x y := by
  have h : hO S T (c • x) y = c • hO S T x y := by
    unfold hO
    simp only [Matrix.smul_apply, Finset.smul_sum, mul_smul_comm]
  unfold symplOH symplO
  rw [h, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm]

theorem symplOH_smul_right (c : AF D.host.F) (x y : WO S T) : symplOH S T x (c • y) = c * symplOH S T x y := by
  have h : hO S T x (c • y) = c • hO S T x y := by
    unfold hO
    simp only [Matrix.smul_apply, Finset.smul_sum, cA_smul, mul_smul_comm, smul_mul_assoc]
  unfold symplOH symplO
  rw [h, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm]

theorem symplOH_zero_left (y : WO S T) : symplOH S T 0 y = 0 := by
  have := symplOH_smul_left S T 0 0 y
  rwa [zero_smul, zero_mul] at this

theorem symplOH_zero_right (y : WO S T) : symplOH S T y 0 = 0 := by
  have := symplOH_smul_right S T 0 y 0
  rwa [zero_smul, zero_mul] at this

theorem symplOH_neg_right (x y : WO S T) : symplOH S T x (-y) = -symplOH S T x y := by
  have := symplOH_smul_right S T (-1) x y
  rwa [neg_smul, one_smul, neg_mul, one_mul] at this

theorem hO_herm (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  have hG : S.gramᴴ = S.gram := by
    exact Matrix.ext fun i j => gram_star S j i
  have hI : ∀ a b, star (S.gram⁻¹ a b) = S.gram⁻¹ b a := by
    intro a b
    have := Matrix.conjTranspose_nonsing_inv S.gram
    rw [hG] at this
    exact congrFun (congrFun this b) a
  unfold hO
  simp only [map_sum, map_mul, GlobalTheory.DualPairCheck.cA_cA, cA_incA, hI, gram_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem symplOH_skew (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH symplO
  rw [← trace_cA, map_mul, cA_incA, star_purely_imaginary_eq_neg, hO_herm, map_neg, neg_mul, map_neg, mul_neg]

theorem symplOH_self (x : WO S T) : symplOH S T x x = 0 := by
  have h := symplOH_skew S T x x
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  linear_combination (algebraMap D.host.F (AF D.host.F) (1 / 2)) * h - (symplOH S T x x) * h2

variable {S T}

theorem smul_fin {u : WO S T} (hu : u.map (infPart D) = 0) : eInf D • u = 0 := by
  ext i j; exact smul_eq_zero_of_inf (congrFun (congrFun hu i) j)

theorem smul_real {v : WO S T} (hv : v.map (finPart D) = 0) : eInf D • v = v := by
  ext i j; exact smul_eq_self_of_fin (congrFun (congrFun hv i) j)

theorem symplOH_fin_real {u v : WO S T} (hu : u.map (infPart D) = 0) (hv : v.map (finPart D) = 0) :
    symplOH S T u v = 0 := by
  rw [← smul_real hv, symplOH_smul_right, ← symplOH_smul_left, smul_fin hu, symplOH_zero_left]

theorem symplOH_real_fin {u v : WO S T} (hu : u.map (infPart D) = 0) (hv : v.map (finPart D) = 0) :
    symplOH S T v u = 0 := by
  rw [symplOH_skew, symplOH_fin_real hu hv, neg_zero]

variable (S T)

theorem continuous_symplOH (u : WO S T) : Continuous fun w : WO S T => symplOH S T w u := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  unfold symplOH symplO hO
  refine continuous_const.mul (ht.comp (continuous_const.mul ?_))
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
    continuous_finset_sum _ fun d _ => continuous_const.mul ?_
  exact (continuous_apply a).comp (continuous_apply d)

theorem ker_mem_nhds {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hc : Continuous ψ)
    (hn : ∀ x, ‖ψ x‖ = 1) : {a : Af F | ψ (pairA F 0 a) = 1} ∈ 𝓝 (0 : Af F) := by
  let χ : Af F → Circle := fun a => ⟨ψ (pairA F 0 a), by simpa [Submonoid.unitSphere] using hn _⟩
  have hχ : Continuous χ := (hc.comp (continuous_const.prodMk continuous_id)).subtype_mk _
  have h0 : χ 0 = 1 := Subtype.ext ψ.map_zero_eq_one
  have hV : χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : Af F) := by
    refine ((Circle.isOpen_centeredArc _).preimage hχ).mem_nhds ?_
    rw [Set.mem_preimage, h0, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  have : χ (N • a) = 1 := by
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    have h1 := hNV (n • a) fun v => nsmul_mem (ha v) n
    have h2 : χ (N • n • a) = χ (N • a) ^ n := by
      apply Subtype.ext
      show ψ (pairA F 0 (N • n • a)) = ((χ (N • a) ^ n : Circle) : ℂ)
      rw [Circle.coe_pow, smul_comm]
      show _ = ψ (pairA F 0 (N • a)) ^ n
      rw [← AddChar.map_nsmul_eq_pow]
      congr 1
      exact Prod.ext (smul_zero n).symm rfl
    rwa [Set.mem_preimage, h2] at h1
  exact congrArg Subtype.val this

variable (ψ : AddChar (AF D.host.F) ℂ)

theorem heisO_heisO (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext u
  simp only [heisO, Pi.smul_apply, smul_eq_mul, symplOH_add_left, symplOH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

def heisL (u : WO S T) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T u
  map_add' f g := by funext w; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

variable {S T ψ}

theorem isThetaFunO_heisO (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {u : WO S T} (hu : u.map (infPart D) = 0) : IsThetaFunO ψ S T (heisO ψ S T u f) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL hLf w => ?_⟩
  · simp only [heisO]
    rw [add_assoc, hf.quasi, symplOH_add_left, symplOH_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul]
    congr 2
    ring
  · obtain ⟨U, hU, hUf⟩ := hf.level
    let K : AddSubgroup (WO S T) :=
      { carrier := {w | ψ (symplOH S T w u) = 1}
        zero_mem' := by
          show ψ _ = 1
          rw [symplOH_zero_left, ψ.map_zero_eq_one]
        add_mem' := fun {a b} ha hb => by
          have ha' : ψ _ = 1 := ha
          have hb' : ψ _ = 1 := hb
          show ψ _ = 1
          rw [symplOH_add_left, AddChar.map_add_eq_mul, ha', hb', one_mul]
        neg_mem' := fun {a} ha => by
          have ha' : ψ _ = 1 := ha
          show ψ _ = 1
          have := AddChar.map_add_eq_mul ψ (symplOH S T a u) (symplOH S T (-a) u)
          rw [← symplOH_add_left, add_neg_cancel, symplOH_zero_left, ψ.map_zero_eq_one, ha', one_mul] at this
          exact this.symm }
    have hK : IsOpen (K : Set (WO S T)) := by
      refine K.isOpen_of_mem_nhds (g := 0) ?_
      have h1 : Continuous fun w : WO S T => (symplOH S T w u).2 := continuous_snd.comp (continuous_symplOH S T u)
      have h2 := h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA D.host.F 0 a) = 1})
        (by rw [symplOH_zero_left]; exact ker_mem_nhds hc hn)
      refine Filter.mem_of_superset h2 fun w hw => ?_
      have h3 : eInf D * symplOH S T w u = 0 := by rw [← symplOH_smul_right, smul_fin hu, symplOH_zero_right]
      have h4 : symplOH S T w u = pairA D.host.F 0 (symplOH S T w u).2 :=
        Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl
      show ψ _ = 1
      rw [h4]; exact hw
    refine ⟨U ⊓ K, hU.inter hK, fun w hw hw' => ?_⟩
    have h1 : ψ (symplOH S T w u) = 1 := hw.2
    have h2 : ψ (symplOH S T u w) = 1 := by
      have : ψ (symplOH S T (-w) u) = 1 := K.neg_mem hw.2
      rwa [symplOH_skew, symplOH_neg_right, neg_neg] at this
    conv_rhs => rw [← hUf w hw.1 hw']
    rw [heisO_heisO, heisO_heisO, h1, h2, add_comm]
  · exact (hc.comp (continuous_symplOH S T u)).mul (hf.cont.comp (continuous_id.add continuous_const))
  · have : (fun t => heisO ψ S T u f (w + L t)) = fun t => ψ (symplOH S T w u) * f (w + u + L t) := by
      funext t
      rw [heisO, symplOH_add_left, symplOH_real_fin hu (hLf t), add_zero, add_right_comm]
    rw [this]
    exact contDiff_const.mul (hf.smooth k L hL hLf (w + u))

theorem dRho_heisO {θ : InfFam D} (hθ : IsInfFam θ) {u : WO S T} (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (heisO ψ S T u g) =
      heisO ψ S T u (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) := Classical.epsilon_spec ((GlobalTheory.RealLineAt.lineAt_exists_unique D).1 θ hθ _ _ τ z)
  funext x
  have key : ∀ t, heisO ψ S T (lineAt θ τ z t) (heisO ψ S T u g) = heisO ψ S T u (heisO ψ S T (lineAt θ τ z t) g) := by
    intro t
    rw [heisO_heisO, heisO_heisO, symplOH_fin_real hu (hL.2.1 t), symplOH_real_fin hu (hL.2.1 t), add_comm]
  unfold Formalism.IndefR.Datum.dRho
  rw [heisO, ← deriv_const_mul_field]
  congr 1
  funext t
  rw [key]
  rfl

theorem pureTensorL_comm {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (H : (X → ℂ) →ₗ[ℂ] (X → ℂ))
    (h : ∀ i g, A i (H g) = H (A i g)) (f : X → ℂ) (P : MvPolynomial ι ℂ) :
    pureTensorL A (H f) P = H (pureTensorL A f P) := by
  have : pureTensorL A (H f) = H ∘ₗ pureTensorL A f := by
    refine (MvPolynomial.basisMonomials ι ℂ).ext fun k => ?_
    rw [LinearMap.comp_apply, pureTensorL, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis]
    unfold opPow
    induction (Multiset.toList (Finsupp.toMultiset k)) with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, List.foldr_cons, ih, h]
  rw [this, LinearMap.comp_apply]

theorem finite_translate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ S T f → (∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (u v : WO S T), u.map (infPart D) = 0 → v.map (finPart D) = 0 → ratW T S γ = u + v → heisO ψ S T u f 0 = heisO ψ S T (-v) f 0) ∧ ∀ (u : WO S T), u.map (infPart D) = 0 → IsThetaFunO ψ S T (heisO ψ S T u f) ∧ ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u f) P = heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f P) := by
  intro D ψ θ S T hψ hθ f hf
  refine ⟨fun γ u v hu hv h => ?_, fun u hu => ⟨isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hu, fun sS BS sT BT P => ?_⟩⟩
  · have h1 := hf.quasi γ (-v)
    rw [h, add_neg_cancel_right, symplOH_neg_right, symplOH_add_left, symplOH_fin_real hu hv, symplOH_self, add_zero,
      neg_neg, ψ.map_zero_eq_one, one_mul] at h1
    simp only [heisO, symplOH_zero_left, zero_add, h1]
  · refine pureTensorL_comm _ (heisL S T ψ u) (fun i g => ?_) f P
    unfold aPlusAll aPlus crea
    rw [map_smul, map_sub, map_smul]
    show _ • (Formalism.IndefR.Datum.dRho _ _ _ _ (heisO ψ S T u g) - _ • Formalism.IndefR.Datum.dRho _ _ _ _ (heisO ψ S T u g)) = _
    rw [dRho_heisO hθ hu, dRho_heisO hθ hu]
    rfl

end GlobalTheory.FinTranslate

end
