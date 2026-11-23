import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology

noncomputable section
open scoped Matrix TensorProduct

namespace GlobalTheory.WeilSmallAct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def inlA : Ainf F →ₗ[F] AF F := LinearMap.inl F (Ainf F) (Af F)

variable (F) in

def infOne : AF F := ((1 : Ainf F), (0 : Af F))

theorem infOne_mul (a : AF F) : infOne F * a = inlA F (fstA F a) := by
  change (((1 : Ainf F) * a.1, (0 : Af F) * a.2) : Ainf F × Af F) = ((a.1, 0) : Ainf F × Af F)
  rw [one_mul, zero_mul]

variable (F) in

def finA (y : Af F) : AF F := ((0 : Ainf F), y)

theorem eq_fin_add_infOne_mul (a : AF F) : a = finA F a.2 + infOne F * a := by
  rw [infOne_mul]
  change ((a.1, a.2) : Ainf F × Af F) = ((0 + a.1, a.2 + 0) : Ainf F × Af F)
  rw [zero_add, add_zero]

theorem fst_eq_zero_of_infOne_mul (a : AF F) (h : infOne F * a = 0) : a.1 = 0 := by
  have h' := congrArg (fun b : AF F => b.1) h
  rw [infOne_mul] at h'
  exact h'

theorem infOne_smul_tensor (m : AE F E) :
    infOne F • m = TensorProduct.map (inlA F) LinearMap.id
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul, smul_eq_mul, infOne_mul]
    rfl
  | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]

theorem infOne_smul_sub_one {d : ℕ} (A : Matrix (Fin d) (Fin d) (AE F E))
    (h : A.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1) : infOne F • (A - 1) = 0 := by
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, infOne_smul_tensor, Matrix.sub_apply, map_sub]
  have hij := congrFun (congrFun h i) j
  rw [Matrix.map_apply] at hij
  rw [hij, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem act_sub {σ : E →ₐ[F] E} {n d : ℕ} {V : Type} [AddCommGroup V] [Module (AF F) V]
    {JX : Matrix (Fin n) (Fin n) E} {JW : Matrix (Fin d) (Fin d) E}
    (e : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] V) (k : UA σ JW) (w : V) :
    e (actAB (cA σ) ((1 : UA σ JX), k) (e.symm w)) - w = e (e.symm w * (mat k - 1)ᵀ) := by
  symm
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, map_sub,
    LinearEquiv.apply_symm_apply]
  congr 2
  simp only [actAB, OneMemClass.coe_one, Units.val_one, Matrix.one_mul]
  rfl

end GlobalTheory.WeilSmallAct

namespace GlobalTheory.WeilSmallAct

theorem smallAct : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (M : Model σ X W)
    (Mo : AddSubgroup (Fin n × Fin d → Af F)) (K : Set (Fin n × Fin d → Af F)),
    IsOpen (Mo : Set (Fin n × Fin d → Af F)) → IsCompact K →
    ∀ᶠ k in 𝓝 (1 : UA σ W.J), (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
      ∀ w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), (fun i => (w.1 i).2) ∈ K → (fun i => (w.2 i).2) ∈ K →
        (∀ i, ((M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm w)) - w).1 i).1 = 0 ∧
          ((M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm w)) - w).2 i).1 = 0) ∧
        (fun i => ((M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm w)) - w).1 i).2) ∈ Mo ∧
        (fun i => ((M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm w)) - w).2 i).2) ∈ Mo := by
  intro F E _ _ _ _ _ σ n d X W M Mo K hMo hK
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  set e := M.co.e with he
  let g : (Fin n × Fin d → Af F) × (Fin n × Fin d → Af F) → (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    fun y => (fun i => finA F (y.1 i), fun i => finA F (y.2 i))
  have hfin : Continuous (finA F) := continuous_const.prodMk continuous_id
  have hg : Continuous g :=
    (continuous_pi fun i => hfin.comp ((continuous_apply i).comp continuous_fst)).prodMk
      (continuous_pi fun i => hfin.comp ((continuous_apply i).comp continuous_snd))
  let Φ : UA σ W.J × ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) → (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    fun p => e (e.symm p.2 * (mat p.1 - 1)ᵀ)
  have hmat : Continuous (fun k : UA σ W.J => mat k) := Units.continuous_val.comp continuous_subtype_val
  have he1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hΦ : Continuous Φ :=
    he1.comp ((he2.comp continuous_snd).matrix_mul ((hmat.comp continuous_fst).sub continuous_const).matrix_transpose)
  have hsnd : Continuous (fun a : AF F => a.2) := continuous_snd
  let f : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) → (Fin n × Fin d → Af F) × (Fin n × Fin d → Af F) :=
    fun l => (fun i => (l.1 i).2, fun i => (l.2 i).2)
  have hf : Continuous f :=
    (continuous_pi fun i => hsnd.comp ((continuous_apply i).comp continuous_fst)).prodMk
      (continuous_pi fun i => hsnd.comp ((continuous_apply i).comp continuous_snd))
  let U := f ⁻¹' ((Mo : Set (Fin n × Fin d → Af F)) ×ˢ (Mo : Set (Fin n × Fin d → Af F)))
  have hU : IsOpen U := (hMo.prod hMo).preimage hf
  have hC : IsCompact (g '' (K ×ˢ K)) := (hK.prod hK).image hg
  have hev : ∀ᶠ k in 𝓝 (1 : UA σ W.J), ∀ v ∈ g '' (K ×ˢ K), Φ (k, v) ∈ U := by
    apply hC.eventually_forall_of_forall_eventually
    intro v _
    have h0 : Φ (1, v) ∈ U := by
      have : Φ (1, v) = 0 := by
        show e (e.symm v * (mat (1 : UA σ W.J) - 1)ᵀ) = 0
        rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, Matrix.transpose_zero, Matrix.mul_zero, map_zero]
      rw [this]
      exact ⟨Mo.zero_mem, Mo.zero_mem⟩
    exact hΦ.continuousAt (hU.mem_nhds h0)
  filter_upwards [hev] with k hk hmap w hw1 hw2
  have hinf := infOne_smul_sub_one (mat k) hmap
  rw [act_sub e k w]
  have hkill : ∀ x : Matrix (Fin n) (Fin d) (AE F E), infOne F • (x * (mat k - 1)ᵀ) = 0 := fun x => by
    rw [← Matrix.mul_smul, ← Matrix.transpose_smul, hinf, Matrix.transpose_zero, Matrix.mul_zero]
  have hA : infOne F • e (e.symm w * (mat k - 1)ᵀ) = 0 := by
    rw [← LinearEquiv.map_smul, hkill, map_zero]
  have hw : w = g (fun i => (w.1 i).2, fun i => (w.2 i).2) + infOne F • w :=
    Prod.ext (funext fun i => eq_fin_add_infOne_mul (w.1 i)) (funext fun i => eq_fin_add_infOne_mul (w.2 i))
  have hB : e (e.symm w * (mat k - 1)ᵀ) = Φ (k, g (fun i => (w.1 i).2, fun i => (w.2 i).2)) := by
    show _ = e (e.symm (g (fun i => (w.1 i).2, fun i => (w.2 i).2)) * (mat k - 1)ᵀ)
    conv_lhs => rw [hw]
    rw [map_add, LinearEquiv.map_smul, Matrix.add_mul, Matrix.smul_mul, hkill, add_zero]
  have hmem := hk _ ⟨_, Set.mk_mem_prod hw1 hw2, rfl⟩
  rw [← hB] at hmem
  refine ⟨fun i => ⟨?_, ?_⟩, hmem.1, hmem.2⟩
  · exact fst_eq_zero_of_infOne_mul _ (congrArg (fun l => l.1 i) hA)
  · exact fst_eq_zero_of_infOne_mul _ (congrArg (fun l => l.2 i) hA)

end GlobalTheory.WeilSmallAct
