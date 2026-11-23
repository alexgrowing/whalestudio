import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.CharSingle
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.JNoEig

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Car}

def NegOneNorm (D : Car) : Prop :=
  ∀ m : ℕ, 0 < m → ∃ lam s : 𝓞 D.host.E, star (s : D.host.E) = (s : D.host.E) ∧
    star (lam : D.host.E) * (lam : D.host.E) = -1 + (m : D.host.E) * (s : D.host.E)

def mulO (N N' : ℕ) (r : D.host.E) : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => TaylorLogMetric.embT D τ r * z τ i j
  map_add' x y := by funext τ i j; exact mul_add _ _ _
  map_smul' c x := by funext τ i j; exact mul_left_comm _ _ _

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Cd.Base D cc δ)

theorem mul_integer_mem_base_lattice {N N' : ℕ} (r : 𝓞 D.host.E) {x : TaylorLogMetric.VC D N N'} (hx : x ∈ La0 B N N') :
    mulO N N' (r : D.host.E) x ∈ La0 B N N' := by
  have hle : La0 B N N' ≤ (La0 B N N').comap (mulO N N' (r : D.host.E)).toAddMonoidHom := by
    show TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') ≤
      (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')).comap (mulO N N' (r : D.host.E)).toAddMonoidHom
    rw [TaylorLogMetric.La, AddSubgroup.closure_le]
    rintro _ ⟨w, hw, A, hA, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    apply AddSubgroup.subset_closure
    refine ⟨w, hw, r • A, Submodule.smul_mem _ r hA, ?_⟩
    funext τ i j
    simp [mulO, TaylorLogMetric.embV, TaylorLogMetric.tor0, Algebra.smul_def, map_mul]
    ring
  exact hle hx

theorem star_int (r : 𝓞 D.host.E) : ∃ r' : 𝓞 D.host.E, (r' : D.host.E) = star (r : D.host.E) :=
  ⟨⟨star (r : D.host.E), by
    have h := (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd D.host.E).toIntAlgHom
    first
      | exact (mem_integralClosure_iff ℤ D.host.E).mpr h
      | exact h⟩, rfl⟩

theorem mulO_phi {N N' : ℕ} (r : D.host.E) (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (x : TaylorLogMetric.VC D N N') :
    mulO N N' r (phiU γ γ' x) = phiU γ γ' (mulO N N' r x) := by
  funext τ i j
  show TaylorLogMetric.embT D τ r * (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (x τ) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j =
    (gM (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * Matrix.of (fun i j => TaylorLogMetric.embT D τ r * x τ i j) *
      (gM (γ : Matrix (Fin N) (Fin N) D.host.E) τ)ᴴ) i j
  have h1 : Matrix.of (fun i j => TaylorLogMetric.embT D τ r * x τ i j) = TaylorLogMetric.embT D τ r • Matrix.of (x τ) := by
    ext a b
    simp
  rw [h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

theorem mulO_adj (A : ℝ) {N N' : ℕ} (r : D.host.E) (x y : TaylorLogMetric.VC D N N') :
    Ker.formV A D.what₂.Tau N N' (mulO N N' r x) y = Ker.formV A D.what₂.Tau N N' x (mulO N N' (star r) y) := by
  simp only [Formalism.L2.Ker.formV, LinearMap.mk₂'ₛₗ_apply, mulO, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, embT_star', Complex.star_def, Complex.conj_conj]
  ring

theorem gaussRow_of (hS : B.StdOK) (hL : B.LatAll) (hNeg : NegOneNorm D) : GaussRow B := by
  intro N γ Ae₁ hN hA₁ S hS₁
  have hfix₁ : ∀ y : TaylorLogMetric.VC D N 1, (phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1).symm y = y → y = 0 := by
    intro y hy
    apply Ae₁.injective
    rw [hA₁, hy, sub_self, map_zero]
  have hfix : ∀ x : TaylorLogMetric.VC D N 2, (phiU γ 1 : TaylorLogMetric.VC D N 2 ≃ₗ[ℂ] TaylorLogMetric.VC D N 2).symm x = x → x = 0 := by
    intro x hx
    apply (rowE D N 2).injective
    funext i
    rw [map_zero]
    refine hfix₁ _ ?_
    rw [← symm_coord (rowE D N 2) _ _ (map_row γ), hx]
  obtain ⟨Ae, hA⟩ := exists_cay (phiU γ 1 : TaylorLogMetric.VC D N 2 ≃ₗ[ℂ] TaylorLogMetric.VC D N 2) hfix
  have c : Copies (rowE D N 2) (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 2)
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (La0 B N 2) (La0 B N 1) (phiU γ 1) Ae (phiU γ 1) Ae₁ :=
    { form := form_row _ N 2
      char := al_row B hS N 2
      lat := lat_row B N 2
      map := map_row γ
      cay := fun x i => by
        rw [hA, hA₁, map_sub, Pi.sub_apply, symm_coord (rowE D N 2) _ _ (map_row γ)] }
  have hal0 : TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ) (0 : TaylorLogMetric.VC D N 1) = 1 := by
    unfold TaylorLogMetric.al TaylorLogMetric.Hf
    simp
  have hU₁ := c.unitaryData₁ 0 (unitaryData hL hN (by decide) γ 1 Ae hA) (formV_herm' _ _ _ _)
    (formV_pos (area_pos' B) _ _ _) (phiL_isom _ _ _ _ _ _ _) hA₁ hal0 (al_phi _ _ _ _ _ _)
  have hcard : 0 < S.card := by
    obtain ⟨x, hx, -⟩ := hS₁.2.2 0 (AddSubgroup.zero_mem _)
    exact Finset.card_pos.mpr ⟨x, hx⟩
  obtain ⟨lam, s, hs, hrel⟩ := hNeg (4 * S.card) (by omega)
  obtain ⟨lam', hlam'⟩ := star_int lam
  have hM : Multipliers (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (La0 B N 1) (phiU γ 1)
      (mulO N 1 (lam : D.host.E)) (mulO N 1 (star (lam : D.host.E))) (mulO N 1 (s : D.host.E)) S.card :=
    { lΛ := fun x hx => mul_integer_mem_base_lattice B lam hx
      l'Λ := fun x hx => by rw [← hlam']; exact mul_integer_mem_base_lattice B lam' hx
      sΛ := fun x hx => mul_integer_mem_base_lattice B s hx
      lδ := mulO_phi _ γ 1
      l'δ := mulO_phi _ γ 1
      sδ := mulO_phi _ γ 1
      adj := mulO_adj _ _
      sadj := fun x y => by rw [mulO_adj, hs]
      rel := fun x => by
        funext τ i j
        show TaylorLogMetric.embT D τ (star (lam : D.host.E)) * (TaylorLogMetric.embT D τ (lam : D.host.E) * x τ i j) =
          -x τ i j + (4 * S.card) • (TaylorLogMetric.embT D τ (s : D.host.E) * x τ i j)
        rw [← mul_assoc, ← map_mul, hrel, map_add, map_neg, map_one, map_mul, map_natCast, nsmul_eq_mul]
        ring }
  exact gauss_sq hU₁ hM (fun x hx => card_smul_mem hS₁ hx)
    (fun x hx => alpha_mult hM (Real.sqrt D.host.d / 2) _ (fun _ => rfl) (B.qInt0 hS N 1) hx) hS₁

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
