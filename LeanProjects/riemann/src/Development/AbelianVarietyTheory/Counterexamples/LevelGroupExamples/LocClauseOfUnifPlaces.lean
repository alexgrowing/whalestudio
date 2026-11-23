import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.EquivariantFiniteGroup
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul

noncomputable section

open scoped TensorProduct Topology
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DictLocTest

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def LocClause (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r) : Prop :=
  ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : Comp) (x : GA D V → Frame (X k).Ψ r), ContinuousOn x N ∧
    ∀ g ∈ N, x g ∈ (X k).dom ∧ ∃ γ ∈ (X k).Γ, dict g = ⟨k, lact γ (x g)⟩

theorem mem_dom_iff (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (y : Frame X.Ψ r) :
    lact γ y ∈ X.dom ↔ y ∈ X.dom := by
  have hg : ∀ τ : X.Ψ, ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det ≠ 0 := by
    intro τ
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine (map_ne_zero τ.1).2 ?_
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hd : ∀ τ : X.Ψ, (mat (lact γ y) τ).det =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det * (mat y τ).det := by
    intro τ
    show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ).det = _
    exact Matrix.det_mul _ _
  simp only [Data.dom, GG, Set.mem_setOf_eq, hd, mul_ne_zero_iff, GlobalTheory.NormFactor.dmin_lact X hγ y]
  constructor
  · intro h τ
    exact ⟨(h τ).1.2, (h τ).2⟩
  · intro h τ
    exact ⟨⟨hg τ, (h τ).1⟩, (h τ).2⟩

theorem lact_rmul_lact {Ψ : Finset (E →+* ℂ)} (γ' γ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact γ' (rmul (lact γ y) b) = lact (γ' * γ) (rmul y b) := by
  funext τ
  show (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ * mat b τ) =
    ((γ' * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * (mat y τ * mat b τ)
  simp only [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem lact_one {Ψ : Finset (E →+* ℂ)} (y : Frame Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = y τ
  rw [Units.val_one, ← RingHom.mapMatrix_apply, map_one, Matrix.one_mul]
  rfl

theorem locClause_of_unif {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (hK : Kf ≤ GfC V)
    (hN : ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀)
    (hth : ∀ c τ, Continuous (archM V (th c τ))) : LocClause V dict := by
  unfold DictIsUnif at hd
  obtain ⟨-, hKd, ⟨x0, -, hx0⟩, hdom, -⟩ := hd
  unfold archMat at hx0
  intro g₀
  rcases hg : dict g₀ with ⟨c, y0⟩
  refine ⟨_, hN g₀, c, fun g => rmul y0 fun τ => (mat (x0 c) τ)⁻¹ *
    Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) (g₀⁻¹ * g)) * mat (x0 c) τ, ?_, ?_⟩
  · refine Continuous.continuousOn (continuous_pi fun τ => ?_)
    have hmul : ∀ θ (a b : GA D V), archM V θ (a * b) = archM V θ a * archM V θ b := by
      intro θ a b
      unfold archM
      rw [map_mul, Units.val_mul, Matrix.map_mul]
    have hA : Continuous fun g : GA D V => archM V (th c τ) (g₀⁻¹ * g) := by
      simp only [hmul]
      exact continuous_const.matrix_mul (hth c τ)
    show Continuous fun g : GA D V => (mat y0 τ * ((mat (x0 c) τ)⁻¹ *
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) (g₀⁻¹ * g)) * mat (x0 c) τ) :
        Matrix (Fin r) (Fin r) ℂ)
    exact continuous_const.matrix_mul
      ((continuous_const.matrix_mul (hA.matrix_reindex _ _)).matrix_mul continuous_const)
  · rintro g ⟨k, hk, h, hh, rfl⟩
    have har : ∀ θ, archM V θ (g₀⁻¹ * (g₀ * k * h)) = archM V θ h := by
      intro θ
      have hk1 : infHom V k = 1 := MonoidHom.mem_ker.1 (hK hk)
      rw [show g₀⁻¹ * (g₀ * k * h) = k * h by group]
      unfold archM
      rw [map_mul, hk1, one_mul]
    simp only [har]
    obtain ⟨γ1, hγ1, e1⟩ := hKd k hk g₀
    rw [hg] at e1 hγ1
    dsimp only at e1 hγ1
    obtain ⟨γ2, hγ2, e2⟩ := hx0 (g₀ * k) h hh
    rw [e1] at e2 hγ2
    dsimp only at e2 hγ2
    have he : dict (g₀ * k * h) = ⟨c, lact (γ2 * γ1) (rmul y0 fun τ => (mat (x0 c) τ)⁻¹ *
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) h) * mat (x0 c) τ)⟩ := by
      rw [e2]
      exact congrArg (Sigma.mk c) (lact_rmul_lact γ2 γ1 y0 _)
    refine ⟨?_, γ2 * γ1, mul_mem hγ2 hγ1, he⟩
    have hm := hdom (g₀ * k * h)
    rw [he] at hm
    exact (mem_dom_iff (X c) (mul_mem hγ2 hγ1) _).1 hm

theorem continuous_place {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    {τ : L →+* ℂ} {θ : Ainf F ⊗[F] L →+* ℂ} (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) :
    Continuous fun z : AF F ⊗[F] L => θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F L) z) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] L) := ⟨rfl⟩
  haveI : FiniteDimensional F L := Module.Finite.of_restrictScalars_finite ℚ F L
  let b := Module.finBasis F L
  let B := Algebra.TensorProduct.basis (AF F) b
  have hz : ∀ z : AF F ⊗[F] L, θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F L) z) =
      ∑ i, θ (fstA F (B.repr z i) ⊗ₜ[F] (1 : L)) * τ (b i) := by
    intro z
    conv_lhs => rw [← B.sum_repr z]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← hθ.1, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [show (fun z : AF F ⊗[F] L => θ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F L) z)) =
    fun z => ∑ i, θ (fstA F (B.repr z i) ⊗ₜ[F] (1 : L)) * τ (b i) from funext hz]
  refine continuous_finset_sum _ fun i _ => Continuous.mul ?_ continuous_const
  have hf : Continuous (fstA F) := continuous_fst
  exact hθ.2.comp (hf.comp (IsModuleTopology.continuous_of_linearMap (B.coord i)))

theorem continuous_archM (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) : Continuous (archM V θ) := by
  unfold archM
  have h1 : Continuous fun h : GA D V => ((matHom V h : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
      Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :=
    Units.continuous_val.comp continuous_subtype_val
  exact h1.matrix_map (continuous_place hθ)

theorem locClause_of_unif_places {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (hK : Kf ≤ GfC V)
    (hN : ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀)
    (hth : ∀ c τ, ∃ τ', Formalism.MainNotions.StandardLattice.IsInfEmb τ' (th c τ)) : LocClause V dict :=
  locClause_of_unif hd hK hN fun c τ => (hth c τ).elim fun _ h => continuous_archM V h

end GlobalTheory.DictLocTest
