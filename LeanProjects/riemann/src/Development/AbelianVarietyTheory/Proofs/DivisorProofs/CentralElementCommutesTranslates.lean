import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuantumDetCentralCoeffsConj
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.RightTr

section Alg

variable {A : Type} [Ring A]

theorem prod_ofFn_mul_comm (R : A) : ∀ (m : ℕ) (f g : Fin m → A), (∀ i, f i * R = R * g i) →
    (List.ofFn f).prod * R = R * (List.ofFn g).prod
  | 0, _, _, _ => by simp
  | m + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_assoc,
      prod_ofFn_mul_comm R m _ _ fun i => h i.succ, ← mul_assoc, h 0, mul_assoc]

theorem gelfA_mul_comm [Algebra ℂ A] {n : ℕ} (X Y : Fin n → Fin n → A) (R : A)
    (h : ∀ a b, X a b * R = R * Y a b) (k : ℕ) :
    GlobalTheory.SmoothForms.gelfA X k * R = R * GlobalTheory.SmoothForms.gelfA Y k := by
  rw [GlobalTheory.SmoothForms.gelfA, GlobalTheory.SmoothForms.gelfA, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun idx _ => prod_ofFn_mul_comm R _ _ _ fun i => h _ _

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def rtr (h : IsCMExt F E σ) (a : GAd σ J) : Module.End ℂ (SmG σ J) where
  toFun f := ⟨fun x => f.1 (x * a), mem_SmG.2 (GlobalTheory.EisCont.CentreFinite.isSm_mul_right h (mem_SmG.1 f.2) a)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isLineOf_conj {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ}
    {γ : ℝ → GAd σ J} (hγ : IsLineOf σ J τ Z γ) (a : GAd σ J) :
    IsLineOf σ J τ (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a))
      (fun t => a⁻¹ * γ t * a) := by
  intro t
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨y, e1, e2⟩ := hγ t
  refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
  · show a⁻¹ * γ t * a = _
    rw [e1]
    refine GAd_ext σ J (fun u => ?_) fun v => by simp
    by_cases e : u = w
    · subst e; simp
    · simp [projArch_embArch_ne σ J e]
  · rw [map_mul, map_mul, e2]
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
    rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

theorem der_mul_rtr (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} {τ : EmbOver E w}
    {D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)} (hD : IsDer σ J τ D) (a : GAd σ J)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    D Z * rtr h a = rtr h a *
      D (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)) := by
  have hl : ∀ Z γ, IsLineOf σ J τ Z γ → D Z * rtr h a = rtr h a *
      D (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)) := by
    intro Z γ hγ
    refine LinearMap.ext fun f => Subtype.ext ?_
    show (D Z (rtr h a f)).1 = fun x => (D _ f).1 (x * a)
    rw [hD.2 Z γ hγ, hD.2 _ _ (isLineOf_conj hγ a)]
    funext x
    simp only [lineDer, rtr, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc, mul_inv_cancel_left]
  obtain ⟨γ₁, γ₂, e1, e2, e3⟩ := exists_lines h hJ τ Z
  generalize (1 / 2 : ℂ) • (Z - adj (J.map τ.1) Z) = Z₁ at e1 e3
  generalize (-Complex.I / 2 : ℂ) • (Z + adj (J.map τ.1) Z) = Z₂ at e2 e3
  subst e3
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul, map_add, map_smul,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hl _ _ e1, hl _ _ e2]

end GlobalTheory.LeviHC.RightTr

namespace GlobalTheory.LeviHC.RightTr

theorem comm_rtr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ u ∈ Algebra.adjoin ℂ (Set.range D), (∀ X, D X * u = u * D X) → ∀ (a : GAd σ J) (f f' : SmG σ J),
      (f'.1 = fun x => f.1 (x * a)) → (u f').1 = fun x => (u f).1 (x * a) := by
  intro F E _ _ _ _ _ σ hcm n J hJ w τ D hD u hu hcomm a f f' hf'
  let X : Fin n → Fin n → Module.End ℂ (SmG σ J) := fun i j => D (Matrix.single i j 1)
  have hsum : ∀ M : Matrix (Fin n) (Fin n) ℂ, D M = ∑ i, ∑ j, M i j • X i j := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum, X]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hgl : Formalism.REAL.GlRel X := by
    intro p q r s
    simp only [X]
    rw [← hD.1, GlobalTheory.CapFrame.single_mul_single_one, GlobalTheory.CapFrame.single_mul_single_one]
    split_ifs <;> simp [eq_comm]
  have hu' : u ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X p.1 p.2) := by
    refine Algebra.adjoin_le ?_ hu
    rintro _ ⟨M, rfl⟩
    rw [hsum]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.smul_mem _ (Algebra.subset_adjoin (R := ℂ) (s := Set.range fun p : Fin n × Fin n => X p.1 p.2) ⟨(i, j), rfl⟩) _
  obtain ⟨d, hd⟩ := GlobalTheory.SmoothForms.exists_filt hu'
  have hz := GlobalTheory.SmoothForms.central_of_filt hgl d u hd fun i j => hcomm _
  have hM : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hg : ∀ k, GlobalTheory.SmoothForms.gelfA X k * rtr hcm a = rtr hcm a * GlobalTheory.SmoothForms.gelfA X k := by
    intro k
    conv_rhs => rw [← GlobalTheory.RegSch.GelfCyc.gelfA_conj X (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹)ᵀ
      (GlobalTheory.Orb.archMat σ J τ (projArch σ J w a))ᵀ (by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]) k]
    refine gelfA_mul_comm _ _ _ (fun i j => ?_) k
    show D (Matrix.single i j 1) * _ = _
    rw [der_mul_rtr hcm hJ hD a, hsum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
    congr 1
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hcen : u ∈ Subalgebra.centralizer ℂ {rtr hcm a} := by
    refine Algebra.adjoin_le ?_ hz
    rintro _ ⟨k, rfl⟩ g hg'
    rw [Set.mem_singleton_iff.1 hg']
    exact (hg k).symm
  have e : rtr hcm a * u = u * rtr hcm a := hcen _ rfl
  have hf : f' = rtr hcm a f := Subtype.ext hf'
  rw [hf]
  show ((u * rtr hcm a) f).1 = _
  rw [← e]
  rfl

end GlobalTheory.LeviHC.RightTr
