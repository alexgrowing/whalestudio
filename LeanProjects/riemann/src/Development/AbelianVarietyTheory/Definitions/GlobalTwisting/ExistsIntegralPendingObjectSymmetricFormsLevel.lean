import Mathlib
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsBranchingCoordinatesIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty

noncomputable section

namespace GlobalTheory.LvT.PendExample

open Formalism.BasicNotions Classical NumberField GlobalTheory.MemberTorsor
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

section Span
variable (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)

def GSpan : AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : 𝓞 D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = D.what₂.embLL (r : D.what₂.LL) • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

variable {D lam}

theorem gspan_smul (d : 𝓞 D.what₂.LL) {p} (hp : p ∈ GSpan D lam) : D.what₂.embLL (d : D.what₂.LL) • p ∈ GSpan D lam := by
  induction hp using AddSubgroup.closure_induction with
  | mem q hq =>
    obtain ⟨r, f, hf, rfl⟩ := hq
    exact AddSubgroup.subset_closure ⟨d * r, f, hf, by rw [smul_smul, ← map_mul]; rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact neg_mem ha

variable (lam) in

def idl (G : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) : Submodule (𝓞 D.what₂.LL) (Unit → D.what₂.LL) where
  carrier := {x | D.what₂.embLL (x ()) • G ∈ GSpan D lam}
  add_mem' {a b} ha hb := by
    show D.what₂.embLL (a () + b ()) • G ∈ GSpan D lam
    rw [map_add, add_smul]; exact add_mem ha hb
  zero_mem' := by
    show D.what₂.embLL 0 • G ∈ GSpan D lam
    rw [map_zero, zero_smul]; exact zero_mem _
  smul_mem' d a ha := by
    show D.what₂.embLL ((d : D.what₂.LL) * a ()) • G ∈ GSpan D lam
    rw [map_mul, mul_smul]; exact gspan_smul d ha

variable {g : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ}

end Span

section Lat
variable (K : Type) [Field K] [NumberField K] [StarRing K] (κ : Type) [Fintype κ] [DecidableEq κ]

@[reducible] def sLat (a : ℝ) (L : Submodule (𝓞 K) (κ → K)) : HLat K where
  V := κ → K
  ι := κ
  b := Pi.basisFun K κ
  X := fun _ => ((a : ℂ)⁻¹) • 1
  L := L

variable {K κ}

theorem sLat_good {a : ℝ} (ha : a ≠ 0) {L : Submodule (𝓞 K) (κ → K)} (h1 : L.FG)
    (h2 : Submodule.span K (L : Set (κ → K)) = ⊤) : (sLat K κ a L).Good := by
  refine ⟨fun v => ?_, h1, h2⟩
  show IsUnit (Matrix.det (((a : ℂ)⁻¹) • (1 : Matrix κ κ ℂ)))
  have : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  simp [this]

theorem sLat_norm {a : ℝ} (ha : a ≠ 0) (L : Submodule (𝓞 K) (κ → K)) (σ : K →+* ℂ) (x : κ → K) :
    (Formalism.HermitianLatticesTheory.majAt (sLat K κ a L).b (sLat K κ a L).X (InfinitePlace.mk σ) x x).re =
      (∑ c, (((a ^ 2 : ℝ) : ℂ) • ipUnit) (stdEmb κ σ x c) (stdEmb κ σ x c)).re := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hi : (((a : ℂ)⁻¹) • (1 : Matrix κ κ ℂ))⁻¹ = (a : ℂ) • (1 : Matrix κ κ ℂ) :=
    Matrix.inv_eq_left_inv (by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha']; simp)
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.fcoord
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have h1 : ((sLat K κ a L).X (InfinitePlace.mk σ))⁻¹.mulVec
      (Formalism.HermitianLatticesTheory.vecAt (sLat K κ a L).b (InfinitePlace.mk σ) x) c =
      a * (InfinitePlace.mk σ).embedding (x c) := by
    show ((((a : ℂ)⁻¹) • (1 : Matrix κ κ ℂ))⁻¹.mulVec _) c = _
    rw [hi, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [h1]
  show (starRingEnd ℂ _ * _).re = (((a ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ (σ _) * σ _)).re
  rw [Complex.conj_mul', Complex.conj_mul', norm_mul, InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs]
  push_cast
  rw [mul_pow, ← Complex.ofReal_pow, sq_abs]
  push_cast
  rfl

end Lat

section Chain
variable (D : D7) (u : D.what₂.Word) (T : ℕ) [Fact T.Prime]

def mk (sg : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1)) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (L : Submodule (𝓞 D.what₂.LL) (Unit → D.what₂.LL)) (h1 : L.FG)
    (h2 : Submodule.span D.what₂.LL (L : Set (Unit → D.what₂.LL)) = ⊤) (be : D.what₂.Tau → ℝ) (hbe : ∀ τ, 0 ≤ be τ) :
    Ch D u where
  C := chain D.R D.what₂.Tau (D.hcW u) T
  A := atT D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau
  P := period D.R D.what₂.Tau (D.hcW u) T
  fm := { forms D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau D.what₂.LL D.what₂.embLL D.what₂.places with
    sg := sg
    ipV := fun _ _ => ((a ^ 2 : ℝ) : ℂ) • ipUnit
    lat := fun _ => sLat D.what₂.LL (D.what₂.Tau → (ZMod T)ˣ) a (stdLat D.what₂.LL _).L
    lat_good := fun _ => sLat_good ha (stdLat_good D.what₂.LL _).2.1 (stdLat_good D.what₂.LL _).2.2
    emb := fun _ => stdEmb _ D.what₂.embLL
    emb_basis := fun _ => stdEmb_basis _ D.what₂.embLL
    emb_norm := fun i x => by
      rw [sLat_norm ha]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      have : (chain D.R D.what₂.Tau (D.hcW u) T).wt i c = 1 := by
        show ((Nat.card PUnit : ℕ) : ℂ)⁻¹ = 1
        simp
      rw [this, one_mul]
    rhoT_lat := (forms D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau D.what₂.LL D.what₂.embLL D.what₂.places).rhoT_lat
    Bw := (forms D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau D.what₂.LL D.what₂.embLL D.what₂.places).Bw
    Bw_span := (forms D.R D.what₂.Tau (D.hcW u) T D.what₂.card_Tau D.what₂.LL D.what₂.embLL D.what₂.places).Bw_span
    ipP := ((((b ^ 2 : ℝ) : ℂ) • ipUnit).comp (LinearMap.proj (R := ℂ) (φ := fun _ : Unit => Unit → ℂ) ())).compl₂
      (LinearMap.proj (R := ℂ) (φ := fun _ : Unit => Unit → ℂ) ())
    ptLat := sLat D.what₂.LL Unit b L
    ptLat_good := sLat_good hb h1 h2
    ptEmb := stdEmb _ D.what₂.embLL
    ptEmb_basis := stdEmb_basis _ D.what₂.embLL
    ptEmb_norm := fun x => by
      rw [sLat_norm hb, Fintype.sum_unique]
      rfl
    beOn := be
    beOn_nonneg := hbe }

def base (sg : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1)) : Ch D u :=
  mk D u T sg 1 1 one_ne_zero one_ne_zero (stdLat D.what₂.LL Unit).L (stdLat_good D.what₂.LL _).2.1
    (stdLat_good D.what₂.LL _).2.2 0 fun _ => le_rfl

end Chain

theorem nfAll_pos {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ}
    (hp : p ≠ 0) : 0 < (nfAll l p p).re := by
  unfold nfAll
  simp only [fockF_self_eq (extremal ℂ n _)]
  rw [← Complex.ofReal_prod, Complex.div_ofReal_re]
  refine div_pos (fockF_self_pos hp) (Finset.prod_pos fun τ _ => ?_)
  have := fockF_self_pos (f := extremal ℂ n (l τ)) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (l τ).natW)
  rwa [fockF_self_eq, Complex.ofReal_re] at this

def frameL {n : ℕ} (l : DomWeight n) (g : GL (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  detPow ℂ n g l.detShift • (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose).toLinearMap

def tailW {N : ℕ} (l : DomWeight N) : DomWeight (N - 1) where
  w i := l.w ⟨i.1 + 1, by omega⟩
  anti _ _ h := l.anti (Nat.succ_le_succ h)

def tailSg (D : D7) (u : D.what₂.Word) : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => tailW (Examples₂.lamOf (D.hcW u τ) D.R.m)

end GlobalTheory.LvT.PendExample
