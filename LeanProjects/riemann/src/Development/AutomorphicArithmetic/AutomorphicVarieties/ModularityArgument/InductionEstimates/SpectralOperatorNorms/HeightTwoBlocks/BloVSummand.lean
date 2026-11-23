import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.Blo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.BloAt
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (BW.Pl E)}

noncomputable def bloV {r : ℕ} (b : Blo S r) : Submodule ℂ (LL (mu1 E r)) := b.summand.choose

theorem bloV_summand {r : ℕ} (b : Blo S r) : IsSummand (mu1 E r) (bloV b) := b.summand.choose_spec.1

theorem bloV_mem {r : ℕ} (b : Blo S r) :
    ((cuspToL2 (mu1 E r) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E r)) : LL (mu1 E r)) ∈ bloV b := b.summand.choose_spec.2

private theorem blo_sum : ∀ {n : ℕ} (d : Dat S n), ∑ j, (d.blo j).1 = n
  | _, .nil => rfl
  | _, .cons b d => by
    have := blo_sum d
    exact (Fin.sum_univ_succ (n := d.len) _).trans (congrArg (_ + ·) this)

theorem blo_sat : ∀ {n : ℕ} (d : Dat S n) (j : Fin d.len), d.sat j = (d.blo j).2.sat
  | _, .nil, j => j.elim0
  | _, .cons b d, j => by
    refine Fin.cases (motive := fun j : Fin (d.len + 1) => (Dat.cons b d).sat j = (Dat.blo (.cons b d) j).2.sat) rfl
      (fun i => blo_sat d i) j

private theorem map_addCases {r s : ℕ} (f : Fin (r + s) → ℂ) :
    Finset.univ.val.map f = (Finset.univ.val.map fun i => f (Fin.castAdd s i)) + Finset.univ.val.map fun i => f (Fin.natAdd r i) := by
  simp only [Fin.univ_val_map, List.ofFn_add, Multiset.coe_add]
  rfl

theorem blo_ms (τ : E →+* ℂ) : ∀ {n : ℕ} (d : Dat S n) (z : Fin d.len → ℂ),
    msOf (d.ptL z) τ = ∑ j, (Finset.univ.val.map ((d.blo j).2.Λ τ)).map (· + z j)
  | _, .nil, _ => rfl
  | _, .cons b d, z => by
    have ih := blo_ms τ d fun j => z (j.succ : Fin (d.len + 1))
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := d.len) _).symm
    unfold msOf at ih ⊢
    rw [map_addCases]
    congr 1
    · rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.castAdd _ i) = (0 : Fin (d.len + 1)) :=
        Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.castAdd _ i) = b.Λ τ i :=
        Fin.addCases_left (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)
    · refine Eq.trans ?_ ih
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.natAdd _ i) = ((d.idx i).succ : Fin (d.len + 1)) :=
        Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.natAdd _ i) = d.lam τ i :=
        Fin.addCases_right (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)

noncomputable def datB {n : ℕ} (d : Dat S n) (h2 : 2 ≤ d.len) : Datum E n where
  r := d.len
  two := h2
  d := fun j => (d.blo j).1
  pos := fun j => (d.blo j).2.pos
  sum := blo_sum d
  μ := fun j => mu1 E (d.blo j).1
  haar := fun _ => inferInstance
  V := fun j => bloV (d.blo j).2
  summand := fun j => bloV_summand (d.blo j).2

theorem datB_at {n : ℕ} (d : Dat S n) (h2 : 2 ≤ d.len) (j : Fin d.len) :
    At (mu1 E (d.blo j).1) S (bloV (d.blo j).2) (fun τ => Finset.univ.val.map ((d.blo j).2.Λ τ))
      fun w => ((d.blo j).2.sat w).map fun x : ℂˣ => (x : ℂ) :=
  bloAt E S _ _ _ (bloV_summand _) (bloV_mem _)

theorem bloV_unique {r : ℕ} (b : Blo S r) {m : (E →+* ℂ) → Multiset ℂ} {B : BW.Pl E → Multiset ℂ}
    (h : At (mu1 E r) S (bloV b) m B) :
    (∀ τ, m τ = Finset.univ.val.map (b.Λ τ)) ∧ ∀ w ∉ S, B w = (b.sat w).map fun x : ℂˣ => (x : ℂ) := by
  have hb := bloAt E S r b (bloV b) (bloV_summand b) (bloV_mem b)
  have hp := Dp.parEx E r b.pos (mu1 E r) (bloV b) (bloV_summand b)
  exact ⟨fun τ => (hp.1 τ).unique (h.1 τ) (hb.1 τ), fun w hw => (hp.2.1 w (h.2 w hw).2.1).unique (h.2 w hw) (hb.2 w hw)⟩

private theorem on_of {n : ℕ} (d : Dat S n) {Λ : (E →+* ℂ) → Multiset ℂ} {t : BW.Pl E → Multiset ℂ} (lam : Fin d.len → ℂ)
    (m : Fin d.len → (E →+* ℂ) → Multiset ℂ) (B : Fin d.len → BW.Pl E → Multiset ℂ)
    (hA : ∀ j, At (mu1 E (d.blo j).1) S (bloV (d.blo j).2) (m j) (B j))
    (hΛ : ∀ τ, Λ τ = ∑ j, (m j τ).map (· + lam j))
    (ht : ∀ w ∉ S, t w = ∑ j, (B j w).map (· * (Ideal.absNorm w.asIdeal : ℂ) ^ (-lam j))) : d.On Λ t := by
  have hu := fun j => bloV_unique (d.blo j).2 (hA j)
  refine ⟨lam, funext fun τ => ?_, fun w hw => ?_⟩
  · rw [hΛ τ, blo_ms]
    exact Finset.sum_congr rfl fun j _ => by rw [(hu j).1 τ]
  · rw [ht w hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hu j).2 w hw, blo_sat, Multiset.map_map]
    rfl

theorem datB_pt {n : ℕ} (d : Dat S n) (h2 : 2 ≤ d.len) (Λ : (E →+* ℂ) → Multiset ℂ) (t : BW.Pl E → Multiset ℂ) :
    (datB d h2).Pt S Λ t ↔ d.On Λ t := by
  constructor
  · rintro ⟨lam, m, B, hA, hΛ, ht⟩
    exact on_of d lam m B hA hΛ ht
  · rintro ⟨z, rfl, ht⟩
    refine ⟨z, _, _, fun j => datB_at d h2 j, fun τ => blo_ms τ d z, fun w hw => ?_⟩
    rw [ht w hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [blo_sat, Multiset.map_map]
    rfl

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.datOn :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (S : Set (BW.Pl E)) (n : ℕ) (d : Dat S n), 2 ≤ d.len →
      ∃ b : Datum E n, ∀ Λ t, b.Pt S Λ t ↔ d.On Λ t := by
  intro E _ _ _ S n d h2
  exact ⟨UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.datB d h2, UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.datB_pt d h2⟩
