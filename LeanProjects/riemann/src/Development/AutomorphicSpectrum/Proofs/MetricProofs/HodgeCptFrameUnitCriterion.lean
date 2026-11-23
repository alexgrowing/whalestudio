import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatios
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormula

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Fields

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]

omit [∀ k, Fintype (ι k)] in

theorem prod_div_mem (y : (Σ k, ι k) → G) (u v : ∀ k, ι k) :
    (∏ k, y ⟨k, u k⟩) / (∏ k, y ⟨k, v k⟩) ∈ blockFnField y := by
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, u k⟩, ⟨k, v k⟩, rfl, rfl⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem blockFnField_eq_top [Algebra ℤ G] (y : (Σ k, ι k) → G) {κ : Type} (f : κ → G) (c₀ : κ)
    (hsub : ∀ j, f j / f c₀ ∈ blockFnField y)
    (hgen : ∀ a : G, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), h ≠ 0 ∧ a = g / h) :
    blockFnField y = ⊤ := by
  have hle : ∀ g ∈ Algebra.adjoin ℤ (Set.range fun j => f j / f c₀), g ∈ blockFnField y := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hsub j
    | algebraMap r => rw [eq_intCast]; exact intCast_mem (blockFnField y) r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  rw [eq_top_iff]
  intro a _
  obtain ⟨g, hg, h, hh, -, rfl⟩ := hgen a
  exact div_mem (hle g hg) (hle h hh)

theorem trdeg_top : Algebra.trdeg ℤ (⊤ : IntermediateField ℚ G) = Algebra.trdeg ℤ G := by
  have e : (⊤ : IntermediateField ℚ G) ≃ₐ[ℤ] G := (IntermediateField.topEquiv (F := ℚ) (E := G)).restrictScalars ℤ
  exact e.trdeg_eq

end Fields

section Gen

variable (Ω : Type) [Field Ω] [CharZero Ω] {S : Type} (r : S → ℕ)

theorem trdeg_genField [inst : Algebra ℤ (GenField Ω r)] :
    Algebra.trdeg ℤ (GenField Ω r) = Algebra.trdeg ℤ Ω + Cardinal.mk (GenIx r) := by
  obtain rfl : inst = OreLocalization.instAlgebra := Subsingleton.elim _ _
  haveI : Algebra.IsAlgebraic (MvPolynomial (GenIx r) Ω) (GenField Ω r) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (GenIx r) Ω))
  haveI : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr
    (by simpa using (Int.cast_injective (α := Ω)))
  have h1 := trdeg_add_eq ℤ Ω (A := GenField Ω r)
  have h2 := trdeg_add_eq Ω (MvPolynomial (GenIx r) Ω) (A := GenField Ω r)
  rw [trdeg_eq_zero (R := MvPolynomial (GenIx r) Ω) (A := GenField Ω r), add_zero, MvPolynomial.trdeg_of_isDomain] at h2
  rw [← h1, ← h2, Cardinal.lift_id]

end Gen

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {G : Type} [Field G] [CharZero G]

theorem isArithVar_of_trdeg [Nonempty K] (y : (Σ k, ι k) → G) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : ℕ)
    (htr : Algebra.trdeg ℤ (blockFnField y) = e) : IsArithVar (mCoordIdeal y) (e + 1) := by
  refine ⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord y c hc, htr, map_add, Cardinal.toENat_nat, Cardinal.toENat_nat]
  have h4 : (e : ℕ∞) + (Fintype.card K : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by
    push_cast
    ring
  rw [h4]
  rfl

theorem trdeg_of_isArithVar (x : (Σ k, ι k) → G) (d : ℕ) (hx : IsArithVar (mCoordIdeal x) (d + 1)) :
    ∃ c : ∀ k, ι k, (∀ k, x ⟨k, c k⟩ ≠ 0) ∧ Algebra.trdeg ℤ (blockFnField x) = d := by
  obtain ⟨-, ⟨-, -, hrel⟩, -, hdim⟩ := hx
  have hne : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X, h0, map_zero, zero_mul]
  choose c hc using hne
  refine ⟨c, hc, ?_⟩
  rw [GlobalTheory.CompanionTheory.Ar.Cmp.ringKrullDim_coord x c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField x) + (Fintype.card K : Cardinal)).toENat + 1 =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := WithBot.coe_injective hdim
  rw [map_add, Cardinal.toENat_nat] at h1
  have h3 : (Algebra.trdeg ℤ (blockFnField x)).toENat + ((Fintype.card K + 1 : ℕ) : ℕ∞) =
      (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
    push_cast at h1 ⊢
    rw [← add_assoc, h1]
    ring
  have h2 : (Algebra.trdeg ℤ (blockFnField x)).toENat = (d : ℕ∞) :=
    WithTop.add_right_cancel (ENat.coe_ne_top _) h3
  exact Cardinal.toENat_eq_nat.mp h2

end Dim

section Main

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ}

theorem mk_genIx : Cardinal.mk (GenIx (rk Ψ p q)) = ((Fintype.card Ψ * (p.choose 2 + q.choose 2) : ℕ) : Cardinal) := by
  show Cardinal.mk (Σ s : Ψ ⊕ Ψ, {lk : Fin (rk Ψ p q s) × Fin (rk Ψ p q s) // lk.2 < lk.1}) = _
  rw [Cardinal.mk_fintype, Fintype.card_sigma]
  simp only [FlagTrdeg.card_below_diagonal]
  rw [Fintype.sum_sum_type]
  simp [rk, Nat.choose_two_right]
  ring

variable {Ω : Type} [Field Ω] [CharZero Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {n : Ψ ⊕ Ψ → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (rk Ψ p q s) → E)
  {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)

abbrev vals (s : Ψ ⊕ Ψ) : Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω := Matrix.of fun j l => φ s j (c s l)

def chartOf (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) : ∀ k, idx (p := p) (q := q) J₀ n k
  | .inl k => j.1 k
  | .inr t => j.2 t

theorem flagCoord_eq_prod (j : FlagIx ((k : K₀) → J₀ k) n (rk Ψ p q)) :
    flagCoord _ (seg x₀) φ c j = ∏ k, yv (vals φ c) x₀ ⟨k, chartOf j k⟩ := by
  rw [Fintype.prod_sum_type]
  simp only [flagCoord, yv, chartOf, seg, map_prod]
  rfl

theorem isArithVar_yv (hB : ∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * vals φ c s = 1)
    (hgen : ∀ c₀, seg x₀ c₀ ≠ 0 → ∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => seg x₀ j / seg x₀ c₀), h ≠ 0 ∧ a = g / h)
    (d : ℕ) (hx : IsArithVar (mCoordIdeal x₀) (d + 1)) :
    IsArithVar (mCoordIdeal (yv (vals φ c) x₀)) (d + Fintype.card Ψ * (p.choose 2 + q.choose 2) + 1) := by
  classical
  obtain ⟨c₀, hc₀, htr⟩ := trdeg_of_isArithVar x₀ d hx
  have hs : seg x₀ c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc₀ k
  obtain ⟨J, hJ, hfrac⟩ := CoordGen.flagCoord_generate Ω E (Ψ ⊕ Ψ) (rk Ψ p q) n _ (seg x₀) φ c c₀ hs (hgen c₀ hs) hB
  haveI : CharZero (GenField Ω (rk Ψ p q)) :=
    charZero_of_injective_algebraMap (algebraMap Ω (GenField Ω (rk Ψ p q))).injective
  have hy : ∀ k, yv (vals φ c) x₀ ⟨k, chartOf J k⟩ ≠ 0 := by
    rw [flagCoord_eq_prod] at hJ
    exact fun k => Finset.prod_ne_zero_iff.1 hJ k (Finset.mem_univ k)
  have htop := blockFnField_eq_top (yv (vals φ c) x₀) (flagCoord _ (seg x₀) φ c) J
    (fun j => by rw [flagCoord_eq_prod, flagCoord_eq_prod]; exact prod_div_mem _ _ _) hfrac
  have htop0 := blockFnField_eq_top x₀ (seg x₀) c₀ (fun j => prod_div_mem x₀ _ _) (hgen c₀ hs)
  haveI : Nonempty (K₀ ⊕ StepIx Ψ p q) := ⟨.inl hx.1.some⟩
  refine isArithVar_of_trdeg _ (chartOf J) hy _ ?_
  rw [htop, trdeg_top, trdeg_genField, ← trdeg_top (G := Ω), ← htop0, htr, mk_genIx]
  push_cast
  rfl

end Main

theorem isArithVar_flagModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (d : ℕ), FormsOK 𝔐 bW bO m φ → IsArithVar (mCoordIdeal x₀) (d + 1) → IsArithVar (mCoordIdeal (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (d + Fintype.card (CMType H) * (D.p.choose 2 + D.q.choose 2) + 1) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ d hF hx
  exact isArithVar_yv φ (cc 𝔐 bW bO) x₀ hF.2.2.2
    (fun c₀ hc₀ => FracChart.exists_eq_div_adjoin 𝔐.X Ω 𝔐.ξ _ (seg x₀) c₀ 𝔐.tie hc₀) d hx

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY
