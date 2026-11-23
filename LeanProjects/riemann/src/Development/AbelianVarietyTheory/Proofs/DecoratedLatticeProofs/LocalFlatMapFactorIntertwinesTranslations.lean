import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatTrans

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_sandwich (a c : AE D) (m : k) : p.ι (p.π a * m * p.π c) = a * p.ι m * c := by
  rw [GlobalTheory.LocChar.ι_mul, GlobalTheory.LocChar.ι_mul, p.ι_π, p.ι_π]
  have h := GlobalTheory.LocChar.e_mul_ι p m
  linear_combination (a * c * p.e + a * c) * h

theorem mul_map_ι_mul {a b l m : Type} [Fintype a] [Fintype b] (A : Matrix m a (AE D)) (M : Matrix a b k)
    (C : Matrix b l (AE D)) : A * M.map p.ι * C = (A.map p.π * M * C.map p.π).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_sum, ι_sandwich]

theorem map_incA_map {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : (M.map (incA D)).map p.π = M.map p.pr := by
  ext; rfl

theorem ι_mem_idAt : ∃ v, ∀ y : k, p.ι y ∈ GlobalTheory.FinPl.idAt D (· = v) := by
  obtain ⟨-, he, v, ε, hε, hsum⟩ := p.split
  refine ⟨v, fun y => GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_⟩
  have hε' := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hε
  subst hε'
  rw [← hsum]
  have h1 := GlobalTheory.LocChar.e_mul_ι p y
  have h2 : cA D p.e * p.e = 0 := by rw [mul_comm]; exact he
  linear_combination (1 - cA D p.e) * h1 + p.ι y * h2

theorem sb_translate {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {Φ : X → ℂ}
    (hΦ : Φ ∈ SB X) (t : X) : (fun z => Φ (z + t)) ∈ SB X :=
  ⟨hΦ.1.comp_continuous (continuous_add_const t), hΦ.2.comp_homeomorph (Homeomorph.addRight t)⟩

section Local
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def bigPt (c ρ : ℕ) (x : Matrix n (n' ⊕ Unit) k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks x.toCols₁ (Matrix.of fun r i => if i.val = ρ then x r (Sum.inr ()) else 0) 0 0

theorem flCol_translate [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (c ρ : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x t : Matrix n (n' ⊕ Unit) k) :
    GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) (fun z => Φ (z + bigPt c ρ x)) t = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ (t + x) := by
  unfold GlobalTheory.LocFlat.flCol GlobalTheory.RootEx.opE
  congr 1
  funext e
  have h1 : affPt (ρ + 1) t.toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) (fun r => t r (Sum.inr ())) + bigPt c ρ x =
      affPt (ρ + 1) (t + x).toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) (fun r => (t + x) r (Sum.inr ())) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt, add_right_comm]
    · by_cases h : j.val = ρ <;> simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt, h, add_assoc]
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt]
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt]
  have h2 : ch (affPt (ρ + 1) t.toCols₁ e) = ch (affPt (ρ + 1) (t + x).toCols₁ e) := by
    simp [ch, affPt, basePt]
  simp only [h1, h2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq n] [DecidableEq n'] in

theorem mul_bigPt_mul {a b : Type} {c ρ : ℕ} (j₀ : Fin (c + 1)) (hj : j₀.val = ρ) (β : Matrix a (n ⊕ Fin c) k) (β₀ : Matrix a n k)
    (γ : Matrix (n' ⊕ Fin (c + 1)) b k) (γ₀ : Matrix (n' ⊕ Unit) b k) (hβ : ∀ r i, β r (Sum.inl i) = β₀ r i)
    (hγ : ∀ i s, γ (Sum.inl i) s = γ₀ (Sum.inl i) s) (hγ' : ∀ s, γ (Sum.inr j₀) s = γ₀ (Sum.inr ()) s)
    (x : Matrix n (n' ⊕ Unit) k) : β * bigPt c ρ x * γ = β₀ * x * γ₀ := by
  ext r s
  have hj' : ∀ j : Fin (c + 1), j.val = ρ ↔ j = j₀ := fun j => by rw [← hj, Fin.val_inj]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, bigPt, hβ, hγ, hj', hγ', Finset.sum_ite_irrel]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem rows_of_inverse {N N₀ c : ℕ} (j₀ : Fin (c + 1)) (F : Frame k N (n' ⊕ Fin (c + 1))) (F₀ : Frame k N₀ (n' ⊕ Unit))
    (q : Matrix (Fin N₀) (Fin N) k) (h1 : ∀ r i, (q * F.β) r (Sum.inl i) = F₀.β r (Sum.inl i))
    (h2 : ∀ r, (q * F.β) r (Sum.inr j₀) = F₀.β r (Sum.inr ())) (h3 : ∀ r j, j ≠ j₀ → (q * F.β) r (Sum.inr j) = 0) :
    (∀ i s, F.γ (Sum.inl i) s = (F₀.γ * q) (Sum.inl i) s) ∧ ∀ s, F.γ (Sum.inr j₀) s = (F₀.γ * q) (Sum.inr ()) s := by
  let σ : n' ⊕ Unit → n' ⊕ Fin (c + 1) := Sum.map id fun _ => j₀
  have hq : F₀.β * F.γ.submatrix σ id = q := by
    conv_rhs => rw [← Matrix.mul_one q, ← F.βγ, ← Matrix.mul_assoc]
    ext r s
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
      Finset.sum_eq_single j₀ (fun j _ hj => by rw [h3 r j hj, zero_mul]) (by simp), h2]
    simp [h1, σ]
  have hγ : F₀.γ * q = F.γ.submatrix σ id := by rw [← hq, ← Matrix.mul_assoc, F₀.γβ, Matrix.one_mul]
  rw [hγ]
  exact ⟨fun _ _ => rfl, fun _ => rfl⟩

end Local

theorem proj_laws {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    d.p0.map p.π * d.i₀.map p.pr = 1 ∧ d.p0.map p.π * d.e.map p.pr = 0 ∧ d.p0.map p.π * d.e'.map p.pr = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_j0).trans (Matrix.map_one _ (map_zero _) (map_one _))
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_jX).trans (Matrix.map_zero _ (map_zero _))
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_jY).trans (Matrix.map_zero _ (map_zero _))

def prHom : D.host.E →+* k := p.π.comp (incA D)

theorem pr_eq : p.pr = prHom p := rfl

theorem up_bigPt {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (s hh : k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (hC : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV) (hJ : p.IsJacFrame J s hh G₀ FW)
    (x : Matrix n (n' ⊕ Unit) k) :
    p.up FV FW (bigPt c ρ x) = B.d.ext0 J.W (J.d.inc0 B.V₀ (p.up F₀ G₀ x)) := by
  obtain ⟨hc, hinl, hlt, heq, hgt⟩ := hB
  obtain ⟨q1, q2, q3⟩ := proj_laws p B.d
  let j₀ : Fin (c + 1) := ⟨ρ, by omega⟩
  have col : ∀ (r : Fin B.V₀.rank) (j : n' ⊕ Fin (c + 1)) (a : k) (y : Fin B.V.rank → k), (∀ r', FV.β r' j = a * y r') →
      (B.d.p0.map p.π * FV.β) r j = a * (B.d.p0.map p.π *ᵥ y) r := fun r j a y h => by
    simp only [Matrix.mul_apply, h, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  obtain ⟨g1, g2⟩ := rows_of_inverse j₀ FV F₀ (B.d.p0.map p.π)
    (fun r i => by
      rw [hC.1, ← Matrix.one_mul (B.o.iA.map p.pr * FA.β), ← q1, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [hinl, pr_eq, Matrix.map_mul, Matrix.mul_assoc])
    (fun r => by
      rw [col r _ s (B.d.i₀.map p.pr *ᵥ fun i => p.pr (vecB B.o B.ζ i)) fun r' => by
        rw [heq j₀ rfl, pr_eq, RingHom.map_mulVec]; rfl, Matrix.mulVec_mulVec, q1, Matrix.one_mulVec, hC.2])
    (fun r j hj => by
      have hj' : j.val ≠ ρ := fun h => hj (Fin.ext h)
      rcases lt_or_gt_of_ne hj' with h | h
      · rw [col r _ _ _ (hlt ⟨j.val, h⟩ j rfl)]
        exact mul_eq_zero_of_right _ (congrFun (congrFun q2 r) ⟨j.val, h⟩)
      · have := j.2
        rw [col r _ _ _ (hgt ⟨2 * ρ - j.val, by omega⟩ j (by simp only; omega))]
        exact mul_eq_zero_of_right _ (congrFun (congrFun q3 r) ⟨2 * ρ - j.val, by omega⟩))
  rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Place.up, Place.up,
    mul_bigPt_mul j₀ rfl FW.β _ FV.γ _ hJ.2.1 g1 g2, ← map_incA_map]
  refine Eq.trans ?_ (mul_map_ι_mul p J.d.j0 _ B.d.p0).symm
  simp only [Matrix.mul_assoc]
  rfl

theorem factor_trans : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (x : Matrix n (n' ⊕ Unit) k) (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = Ψ.1 (t + x)) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ (p.up F₀ G₀ x) (L₀ Ψ) := by
  intro D _ hFLs _ k _ _ _ _ _ _ p ν hν ψ ψk hpc ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW hC hB hJ Tm hTm L₀ hL₀ x Ψ Ψ' hΨ
  have hψc : Continuous ψk := ((GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ st.weil.std).2.1 ψk hpc).1
  have hc : c = 2 * ρ := hJ.1
  obtain ⟨Φ, hΦ, hΦΨ⟩ := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k ψk ν hψc hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  have h1 : flatBF st (Tm ⟨Φ, hΦ⟩) = L₀ Ψ := hL₀ _ _ hΦΨ.symm
  have h2 : flatBF st (Tm ⟨_, sb_translate hΦ (bigPt c ρ x)⟩) = L₀ Ψ' := hL₀ _ _ (by
    funext t
    rw [hΨ, ← hΦΨ]
    exact (flCol_translate ψk ν c ρ Φ x t).symm)
  have h3 := hTm.trans (bigPt c ρ x) ⟨Φ, hΦ⟩ ⟨_, sb_translate hΦ (bigPt c ρ x)⟩ fun _ => rfl
  obtain ⟨v, hv⟩ := ι_mem_idAt p
  rw [← h2, h3, up_bigPt p B J s _ FA F₀ FV G₀ FW hC hB hJ, ← h1]
  exact ((hFLs ψ (· = v)).1 ρ B J st).Heisenberg₂.core _ (hTm.theta _) _ fun i j => hv _

end GlobalTheory.FlatTrans
