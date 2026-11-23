import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.DualPairInh
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem nv_lin {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ} (f : PS R n d)
    (hf : MvPowerSeries.constantCoeff f = 0) (a : Fin n → Fin d → S)
    (h : ∀ i j i' j', a i j * a i' j' = 0) :
    nv s f a = ∑ i, ∑ j, s (MvPowerSeries.coeff (Finsupp.single (i, j) 1) f) * a i j := by
  have ha : ∀ i j, IsNilpotent (a i j) := fun i j => ⟨2, by rw [pow_two, h]⟩
  rw [(nv_calculus R S s n d a ha).2.2.2.2.2 h f, hf, map_zero, zero_add, Fintype.sum_prod_type]

private theorem chart_add {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ} {F : FGLaw (O : Type) g}
    {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R} (hY : BXChart B O F.F Y)
    (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0) (v w : Fin g → (R : Type)) :
    Y R s (fun k => v k * e) + Y R s (fun k => w k * e) = Y R s (fun k => (v k + w k) * e) := by
  have hn : ∀ x : (R : Type), IsNilpotent (x * e) := fun x =>
    ⟨2, by rw [mul_pow, pow_two e, he, mul_zero]⟩
  have hl : ∀ v w : Fin g → (R : Type), Y R s (fun k => v k * e) + Y R s (fun k => w k * e) =
      Y R s (fun k => (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single (0, j) 1) (F.F k)) * v j +
        ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single (1, j) 1) (F.F k)) * w j) * e) := by
    intro v w
    rw [hY.law R s _ _ (fun _ => hn _) (fun _ => hn _)]
    congr 1
    funext k
    rw [nv_lin _ _ (F.const k)]
    · simp [Fin.sum_univ_two, add_mul, Finset.sum_mul, _root_.mul_assoc]
    · have hx : ∀ x y : (R : Type), x * e * (y * e) = 0 := fun x y => by
        rw [_root_.mul_mul_mul_comm, he, mul_zero]
      intro i j i' j'
      fin_cases i <;> fin_cases i' <;> exact hx _ _
  have h0 : Y R s (fun k => (0 : Fin g → (R : Type)) k * e) = 0 := by
    simp only [Pi.zero_apply, zero_mul]
    exact hY.zero R s
  have h1 := hl v 0
  have h2 := hl 0 w
  rw [h0, add_zero] at h1
  rw [h0, zero_add] at h2
  have h1' := hY.inj R s _ _ (fun _ => hn _) (fun _ => hn _) h1
  have h2' := hY.inj R s _ _ (fun _ => hn _) (fun _ => hn _) h2
  rw [hl]
  congr 1
  funext k
  have e1 := congrFun h1' k
  have e2 := congrFun h2' k
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at e1 e2
  rw [add_mul, add_mul, e1, e2]

private theorem chart_sum {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ} {F : FGLaw (O : Type) g}
    {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R} (hY : BXChart B O F.F Y)
    (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0) {κ : Type} (t : Finset κ)
    (v : κ → Fin g → (R : Type)) :
    ∑ i ∈ t, Y R s (fun k => v i k * e) = Y R s (fun k => (∑ i ∈ t, v i k) * e) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, zero_mul]
    exact (hY.zero R s).symm
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, ih, chart_add hY R s e he]
    simp only [Finset.sum_insert ha]

theorem lin_mul_tanMat : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (O : Type)), TanMat B O Y gb S → ∀ (A : OEnd B O) (α : Fin g → PS (O : Type) 1 g) (ρ : Matrix (Fin g) (Fin g) (O : Type)), (∀ j, MvPowerSeries.constantCoeff (α j) = 0) → (∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a])) → (∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (ρ k l) * i) → A.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) → lin α * S = S * ρ := by
  intro R₀ _ B O g F Y hY gb S hS A α ρ hα hA hρ
  let Dp : DualPair O := DualNum.dualPair O
  have hπ : Dp.π.SqZero := Dp.π.sqZero_of_span Dp.η (fun r => ⟨Dp.σ.1 r, Dp.sect r⟩) Dp.ker_eq Dp.η_sq
  have hn : ∀ x : (Dp.D : Type), IsNilpotent (x * Dp.η) := fun x =>
    ⟨2, by rw [mul_pow, pow_two Dp.η, Dp.η_sq, mul_zero]⟩
  have hη : Dp.η ∈ Dp.π.ker := by simpa using Dp.ση_mem 1
  ext j l
  have h := hρ Dp.σ Dp.π hπ l ⟨Dp.η, hη⟩ (fun k => ⟨Dp.σ.1 (ρ k l) * Dp.η, Dp.ση_mem _⟩) (fun _ => rfl)
  rw [map_sum, hS _ _ Dp.σ, hA _ _ _ (fun _ => hn _)] at h
  simp only [hS _ _ Dp.σ, ← _root_.mul_assoc] at h
  rw [chart_sum hY _ _ _ Dp.η_sq] at h
  have hv : (fun j => nv Dp.σ.1.toRingHom (α j) ![fun k => Dp.σ.1 (S k l) * Dp.η]) =
      fun j => Dp.σ.1 ((lin α * S) j l) * Dp.η := by
    funext j
    rw [nv_lin _ _ (hα j)]
    · simp [Matrix.mul_apply, lin, Finset.sum_mul, _root_.mul_assoc]
    · intro i j i' j'
      fin_cases i; fin_cases i'
      show Dp.σ.1 _ * Dp.η * (Dp.σ.1 _ * Dp.η) = 0
      rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  rw [hv] at h
  have h2 := congrFun (hY.inj _ _ _ _ (fun _ => hn _) (fun _ => hn _) h) j
  rw [← sub_eq_zero]
  apply Dp.free
  rw [map_sub, sub_mul, h2, Matrix.mul_apply, map_sum]
  simp only [map_mul, sub_self]

end GlobalTheory.ChF
