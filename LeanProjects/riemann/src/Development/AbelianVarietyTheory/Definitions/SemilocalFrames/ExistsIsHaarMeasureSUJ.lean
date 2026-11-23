import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLocGrowthA

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.DSSU

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def SUset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | g ∈ UJset ε ∧ g.det = 1}

def KS (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | g ∈ Kset ε ∧ g.det = 1}

def SUJ (ε : Fin n → Bool) : Subgroup (UJ ε) where
  carrier := {g | (umat g).det = 1}
  one_mem' := by simp [umat]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, umat, Subgroup.coe_mul, Units.val_mul, Matrix.det_mul] at *
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, umat] at *
    have h : ((a⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val * (a : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1 := by
      rw [← Units.val_mul]; simp
    have h2 := congrArg Matrix.det h
    rwa [Matrix.det_mul, ha, mul_one, Matrix.det_one] at h2

def rhoCh (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => lam b < lam a ∧ ε b = ε a).card : ℝ) -
    ((univ.filter fun b => lam a < lam b ∧ ε b = ε a).card : ℝ)) / 2

def rhoNh (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := fun a =>
  (((univ.filter fun b => lam b < lam a ∧ ε b ≠ ε a).card : ℝ) -
    ((univ.filter fun b => lam a < lam b ∧ ε b ≠ ε a).card : ℝ)) / 2

def lowCh (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam + rhoNh ε lam - rhoCh ε lam

def Above (P : Fin n → Fin n → Prop) (μ Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → P a b) ∧ Λ = μ + ∑ a, ∑ b, (c a b : ℝ) • root a b

def IsParS (lam : Fin n → ℝ) : Prop :=
  ∑ a, lam a = 0 ∧ Function.Injective lam ∧ ∀ a b, ∃ m : ℤ, lam a - lam b = (m : ℝ)

def IsParU (lam : Fin n → ℝ) : Prop :=
  Function.Injective lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)

def E0 (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single a b 1 - (if a = b then (n : ℂ)⁻¹ else 0) • (1 : Matrix (Fin n) (Fin n) ℂ)

def EwordS (ε : Fin n → Bool) (w : List (Fin n × Fin n)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  w.foldr (fun p G => Ec ε (E0 p.1 p.2) G) f

def gelfS (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (m + 1) → Fin n, EwordS ε (cycWord a) f g

def SmoothS (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g₀ ∈ SUset ε, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ SUset ε → f g = F g

section Rep

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

def IsSqIntS (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ μ : Measure (SUJ ε), μ.IsHaarMeasure → ∀ v w : H, MemLp (fun g : SUJ ε => ⟪w, σ (umat g.1) v⟫_ℂ) 2 μ

def IsSqIntIrrS (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  CompleteSpace H ∧ Nontrivial H ∧ IsURepOn (SUset ε) σ ∧ IsIrredOn (SUset ε) σ ∧ IsSqIntS ε σ

def Stable (K : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  ∀ g ∈ K, ∀ v ∈ S, σ g v ∈ S

def IsKFinS (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ Stable (KS ε) σ S

def HasInfCharS (ε : Fin n → Bool) (χ : Fin n → ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ v w : H, IsKFinS ε σ v → IsKFinS ε σ w →
    SmoothS ε (fun g => ⟪w, σ g v⟫_ℂ) ∧
      ∀ m : ℕ, ∀ g ∈ SUset ε, gelfS ε m (fun g => ⟪w, σ g v⟫_ℂ) g = gelfVal χ (m + 1) * ⟪w, σ g v⟫_ℂ

def IsWtS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (μ : Fin n → ℝ) (v : H) : Prop :=
  ∀ θ : Fin n → ℝ, ∑ a, θ a = 0 →
    σ (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) v =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v

def IsKTypeS (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ)
    (S : Submodule ℂ H) : Prop :=
  ∑ a, Λ a = 0 ∧ FiniteDimensional ℂ S ∧ Stable (KS ε) σ S ∧
    (∀ S' : Submodule ℂ H, S' ≤ S → Stable (KS ε) σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtS σ Λ v) ∧
    ∀ (μ : Fin n → ℝ) (v : H), ∑ a, μ a = 0 → v ∈ S → v ≠ 0 → IsWtS σ μ v →
      Above (fun a b => lam b < lam a ∧ ε a = ε b) μ Λ

def IsKTypeU (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ)
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ Stable (Kset ε) σ S ∧
    (∀ S' : Submodule ℂ H, S' ≤ S → Stable (Kset ε) σ S' → S' = ⊥ ∨ S' = S) ∧
    (∃ v ∈ S, v ≠ 0 ∧ IsWtOn (Kset ε) σ Λ v) ∧
    ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → IsWtOn (Kset ε) σ μ v →
      Above (fun a b => lam b < lam a ∧ ε a = ε b) μ Λ

def IsHCS (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsSqIntIrrS ε σ ∧ HasInfCharS ε (fun a => (lam a : ℂ)) σ ∧
    (∃! S : Submodule ℂ H, IsKTypeS ε lam σ (lowCh ε lam) S) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeS ε lam σ μ S → Above (fun a b => lam b < lam a) (lowCh ε lam) μ

def IsHCU (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsSqIntIrr ε σ ∧ HasInfChar ε (fun a => (lam a : ℂ)) σ ∧
    (∃! S : Submodule ℂ H, IsKTypeU ε lam σ (lowCh ε lam) S) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeU ε lam σ μ S → Above (fun a b => lam b < lam a) (lowCh ε lam) μ

def EquivOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) : Prop :=
  ∃ T : H ≃ₗᵢ[ℂ] H', ∀ g ∈ G, ∀ v, T (σ g v) = σ' g (T v)

def Ext (ε : Fin n → Bool) (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, π (z • g) = z ^ m • π' g

end Rep

structure Fam (n : ℕ) : Type 1 where
  H : (Fin n → ℝ) → Type
  nacg : ∀ lam, NormedAddCommGroup (H lam)
  ips : ∀ lam, InnerProductSpace ℂ (H lam)
  π : ∀ lam, Matrix (Fin n) (Fin n) ℂ → (H lam →L[ℂ] H lam)

attribute [instance] Fam.nacg Fam.ips

def ConjK (ε : Fin n → Bool) (lam lam' : Fin n → ℝ) : Prop :=
  ∃ w : Equiv.Perm (Fin n), (∀ a, ε (w a) = ε a) ∧ lam' = lam ∘ w

def ParamS (ε : Fin n → Bool) (F : Fam n) : Prop :=
  (∀ lam, IsParS lam → IsHCS ε lam (F.π lam)) ∧
    ∀ lam lam', IsParS lam → IsParS lam' → (EquivOn (SUset ε) (F.π lam) (F.π lam') ↔ ConjK ε lam lam')

def ExhaustS (ε : Fin n → Bool) (F : Fam n) : Prop :=
  ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsSqIntIrrS ε σ → ∃ lam, IsParS lam ∧ EquivOn (SUset ε) σ (F.π lam)

def ClassS (ε : Fin n → Bool) : Prop := ∃ F : Fam n, ParamS ε F ∧ ExhaustS ε F

def ClassF (ε : Fin n → Bool) : Prop :=
  ∃ F : Fam n, (∀ lam, IsParU lam → IsHCU ε lam (F.π lam)) ∧
    (∀ lam lam', IsParU lam → ConjK ε lam lam' → EquivOn (UJset ε) (F.π lam) (F.π lam')) ∧
    ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      IsSqIntIrr ε σ → ∃ lam, IsParU lam ∧ EquivOn (UJset ε) σ (F.π lam)

def ClassU (n : ℕ) : Prop :=
  ∃ (H : (Fin n → Bool) → (Fin n → ℝ) → Type) (_ : ∀ ε lam, NormedAddCommGroup (H ε lam))
    (_ : ∀ ε lam, InnerProductSpace ℂ (H ε lam)) (π : ∀ ε lam, Matrix (Fin n) (Fin n) ℂ → (H ε lam →L[ℂ] H ε lam)),
    (∀ ε lam, IsHCParam lam → IsHCDS ε lam (π ε lam)) ∧
    ∀ (ε : Fin n → Bool) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsSqIntIrr ε σ' →
      ∃ (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ), IsHCParam mu ∧ (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) ∧
        UEquiv (ε ∘ s) (fun g => σ' (g.submatrix s.symm s.symm)) (π (ε ∘ s) mu)

theorem dsClass_iff : DSClass ↔ ∀ n, ClassU n := Iff.rfl

theorem isParS_two : IsParS (![1 / 2, -1 / 2] : Fin 2 → ℝ) := by
  refine ⟨by simp [Fin.sum_univ_two]; norm_num, ?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all <;> norm_num at h
  · intro a b
    fin_cases a <;> fin_cases b
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp; norm_num⟩
    · exact ⟨-1, by simp; norm_num⟩
    · exact ⟨0, by simp⟩

theorem SUJ_eq (ε : Fin n → Bool) : SUJ ε = Formalism.MainNotions.BridgeLocGrowth.SUJ ε := rfl

theorem isClosed_SUJ_in_UJ (ε : Fin n → Bool) : IsClosed (SUJ ε : Set (UJ ε)) :=
  Formalism.MainNotions.BridgeLocGrowth.isClosed_SUJ ε

theorem borelSpace_SUJ (ε : Fin n → Bool) : BorelSpace (SUJ ε) :=
  inferInstanceAs (BorelSpace (SUJ ε : Set (UJ ε)))

theorem measurableSpace_SUJ_eq (ε : Fin n → Bool) :
    (inferInstance : MeasurableSpace (SUJ ε)) = Formalism.MainNotions.BridgeLocGrowth.instMeasurableSpaceSUJ ε :=
  (borelSpace_SUJ ε).measurable_eq

theorem exists_isHaarMeasure_SUJ (ε : Fin n → Bool) : ∃ μ : Measure (SUJ ε), μ.IsHaarMeasure := by
  haveI := borelSpace_SUJ ε
  haveI : LocallyCompactSpace (SUJ ε) := (isClosed_SUJ_in_UJ ε).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨Measure.haar, inferInstance⟩

theorem mem_UJset_allPos_iff (g : Matrix (Fin n) (Fin n) ℂ) : g ∈ UJset (allPos n) ↔ g ∈ Kset (allPos n) := by
  simp [UJset, inUJ, Kset, Jm, allPos, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]

theorem compactSpace_SUJ_allPos : CompactSpace (SUJ (allPos n)) := by
  have hemb := isClosedEmbeddingMatrix n (allPos n)
  haveI : CompactSpace (UJ (allPos n)) := by
    rw [← isCompact_univ_iff, hemb.1.isEmbedding.isCompact_iff, Set.image_univ, hemb.2]
    convert (maximal_compact_facts n (allPos n)).2.1 using 1
    exact Set.ext mem_UJset_allPos_iff
  exact isCompact_iff_compactSpace.1 (isClosed_SUJ_in_UJ (allPos n)).isCompact

def stdFam (n : ℕ) : Fam n where
  H := fun _ => EuclideanSpace ℂ (Fin n)
  nacg := fun _ => inferInstance
  ips := fun _ => inferInstance
  π := fun _ => stdRep

theorem stdRep_irred_KS (S : Submodule ℂ (EuclideanSpace ℂ (Fin (n + 1))))
    (hS : Stable (KS (allPos (n + 1))) stdRep S) : S = ⊥ ∨ S = ⊤ := by
  refine stdRep_irred S fun g hg v hv => ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq g.det (n := n + 1) (by omega)
  have hd : star g.det * g.det = 1 := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary hg.1)
  have hz1 : ‖z‖ = 1 := by
    have h := congrArg norm hd
    rw [norm_mul, norm_star, ← hz, norm_pow, norm_one, ← pow_add] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega)).1 h
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
  have hzz : star z * z = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hz1]; simp
  have hmem : z⁻¹ • g ∈ KS (allPos (n + 1)) := by
    refine ⟨mem_Kset_allPos ?_, ?_⟩
    · rw [Matrix.mem_unitaryGroup_iff', star_smul, Matrix.smul_mul, Matrix.mul_smul,
        Unitary.star_mul_self_of_mem hg.1, smul_smul, star_inv₀, ← mul_inv, hzz]
      simp
    · rw [Matrix.det_smul, ← hz, Fintype.card_fin, ← mul_pow, inv_mul_cancel₀ hz0, one_pow]
  have h := S.smul_mem z (hS _ hmem v hv)
  have e : stdRep (z⁻¹ • g) v = z⁻¹ • stdRep g v := by simp [stdRep]
  rwa [e, smul_smul, mul_inv_cancel₀ hz0, one_smul] at h

theorem isSqIntIrrS_stdFam (lam : Fin (n + 1) → ℝ) : IsSqIntIrrS (allPos (n + 1)) ((stdFam (n + 1)).π lam) := by
  obtain ⟨h1, h2, ⟨⟨h3, h4⟩, h5, h6⟩, -, -⟩ := isSqIntIrr_std n
  refine ⟨h1, h2, ⟨⟨h3, fun a ha b hb => h4 a ha.1 b hb.1⟩, fun g hg => h5 g hg.1,
    fun v => (h6 v).mono fun g hg => hg.1⟩,
    fun S _ hS => stdRep_irred_KS S fun g hg => hS g ⟨(mem_UJset_allPos_iff g).2 hg.1, hg.2⟩, ?_⟩
  intro μ _ v w
  haveI := compactSpace_SUJ_allPos (n := n + 1)
  haveI := borelSpace_SUJ (allPos (n + 1))
  have hc : Continuous (fun g : SUJ (allPos (n + 1)) => umat g.1) :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val
  have hf : Continuous fun g : SUJ (allPos (n + 1)) => ⟪w, stdRep (umat g.1) v⟫_ℂ :=
    continuous_const.inner ((h6 v).comp_continuous hc fun g => g.1.2)
  exact hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem lowCh_two_split (x y : ℝ) :
    (y < x → lowCh ![true, false] ![x, y] = ![x + 1 / 2, y - 1 / 2]) ∧
      (x < y → lowCh ![true, false] ![x, y] = ![x - 1 / 2, y + 1 / 2]) := by
  constructor <;> intro h <;> have h' := h.not_gt <;> funext a <;>
    simp only [lowCh, rhoNh, rhoCh, Pi.add_apply, Pi.sub_apply, Finset.card_filter, Fin.sum_univ_two] <;>
    fin_cases a <;> simp [h, h'] <;> ring

theorem lowCh_two_compact (x y : ℝ) :
    (y < x → lowCh (allPos 2) ![x, y] = ![x - 1 / 2, y + 1 / 2]) ∧
      (x < y → lowCh (allPos 2) ![x, y] = ![x + 1 / 2, y - 1 / 2]) := by
  constructor <;> intro h <;> have h' := h.not_gt <;> funext a <;>
    simp only [lowCh, rhoNh, rhoCh, Pi.add_apply, Pi.sub_apply, Finset.card_filter, Fin.sum_univ_two] <;>
    fin_cases a <;> simp [h, h', allPos] <;> ring

theorem EwordS_const (ε : Fin n → Bool) (c : ℂ) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    EwordS ε (p :: w) (fun _ => c) = fun _ => 0 := by
  induction w generalizing p with
  | nil => funext g; simp [EwordS, Formalism.REAL.Ec, Formalism.REAL.Rd]
  | cons q w ih =>
    funext g
    have h := ih q
    unfold EwordS at h ⊢
    rw [List.foldr_cons, h]
    simp [Formalism.REAL.Ec, Formalism.REAL.Rd]

theorem isWtS_trivial_two {μ : Fin 2 → ℝ} {v : ℂ} (hs : ∑ a, μ a = 0) (hv : v ≠ 0)
    (h : IsWtS (fun _ : Matrix (Fin 2) (Fin 2) ℂ => (1 : ℂ →L[ℂ] ℂ)) μ v) : μ = 0 := by
  rw [Fin.sum_univ_two] at hs
  have h0 : μ 0 = 0 := by
    by_contra h0
    have := h ![Real.pi / (2 * μ 0), -(Real.pi / (2 * μ 0))] (by simp [Fin.sum_univ_two])
    have e : (∑ a, μ a * (![Real.pi / (2 * μ 0), -(Real.pi / (2 * μ 0))] : Fin 2 → ℝ) a) = Real.pi := by
      have : μ 1 = -μ 0 := by linarith
      simp [Fin.sum_univ_two, this]; field_simp; ring
    rw [e, Complex.exp_pi_mul_I] at this
    apply hv
    have h2 : v = -v := by simpa using this
    linear_combination h2 / 2
  funext a
  fin_cases a
  · exact h0
  · show μ 1 = 0; linarith

theorem isHCS_trivial_two :
    IsHCS (allPos 2) ![1 / 2, -1 / 2] (fun _ : Matrix (Fin 2) (Fin 2) ℂ => (1 : ℂ →L[ℂ] ℂ)) := by
  have e : lowCh (allPos 2) ![1 / 2, -1 / 2] = 0 := by
    rw [(lowCh_two_compact _ _).1 (by norm_num)]
    funext a; fin_cases a <;> simp <;> norm_num
  have er : (![1 / 2, -1 / 2] : Fin 2 → ℝ) = Formalism.QuantumDeterminants.rhoStd 2 := by
    funext a; fin_cases a <;> simp [Formalism.QuantumDeterminants.rhoStd] <;> norm_num
  refine ⟨⟨inferInstance, inferInstance, ⟨⟨rfl, fun a _ b _ => rfl⟩, fun g _ v => rfl,
    fun v => continuousOn_const⟩, fun S _ _ => eq_bot_or_eq_top S, ?_⟩, ?_, ?_, ?_⟩
  · intro μ hμ v w
    haveI := compactSpace_SUJ_allPos (n := 2)
    exact memLp_const (μ := μ) ⟪w, v⟫_ℂ
  · intro v w _ _
    refine ⟨fun g _ => ⟨Set.univ, fun _ => ⟪w, v⟫_ℂ, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩
    intro m g _
    rw [er, gelfVal_rho, zero_mul]
    change gelfS (allPos 2) m (fun _ => ⟪w, v⟫_ℂ) g = 0
    simp only [gelfS, cycWord, List.ofFn_succ, EwordS_const, Finset.sum_const_zero]
  · rw [e]
    refine ⟨⊤, ⟨by simp, inferInstance, fun _ _ _ _ => trivial, fun S _ _ => eq_bot_or_eq_top S,
      ⟨1, trivial, one_ne_zero, fun θ _ => by simp⟩, ?_⟩, ?_⟩
    · intro μ v hs _ hv h
      rw [isWtS_trivial_two hs hv h]; exact ⟨0, by simp, by simp⟩
    · rintro S ⟨-, -, -, -, ⟨v, hv, hv0, -⟩, -⟩
      exact (eq_bot_or_eq_top S).resolve_left fun h => hv0 (by simpa [h] using hv)
  · rintro μ S ⟨hs, -, -, -, ⟨v, -, hv0, h⟩, -⟩
    rw [isWtS_trivial_two hs hv0 h, e]; exact ⟨0, by simp, by simp⟩

theorem not_isHCS_trivial_split :
    ¬ IsHCS ![true, false] ![1 / 2, -1 / 2] (fun _ : Matrix (Fin 2) (Fin 2) ℂ => (1 : ℂ →L[ℂ] ℂ)) := by
  rintro ⟨-, -, ⟨S, ⟨hs, -, -, -, ⟨v, -, hv0, h⟩, -⟩, -⟩, -⟩
  have := congrFun (isWtS_trivial_two hs hv0 h) 0
  rw [(lowCh_two_split _ _).1 (by norm_num)] at this
  simp at this

end GlobalTheory.DSSU

end
