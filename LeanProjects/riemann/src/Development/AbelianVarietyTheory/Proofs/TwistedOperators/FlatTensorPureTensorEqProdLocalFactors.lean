import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorPureTensorEqProdContr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

open GlobalTheory.SplitFlip (Grid Edge)

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem flCol_datC_congr (ψ : AddChar k Circle) (ν : Measure k) {a b N N' : ℕ} (Φ : Matrix (Fin N) (Fin N') k → ℂ)
    {c₁ c₂ p₁ p₂ : ℕ} (hc : c₁ = c₂) (hp : p₁ = p₂) (h₁ : a + c₁ = N') (h₁' : b + (c₁ + 1) = N) (h₂ : a + c₂ = N')
    (h₂' : b + (c₂ + 1) = N) :
    GlobalTheory.LocFlat.flCol ψ ν p₁ (datC h₁ h₁' Φ) = GlobalTheory.LocFlat.flCol ψ ν p₂ (datC h₂ h₂' Φ) := by
  subst hc hp; rfl

theorem flRow_datC_congr (ψ : AddChar k Circle) (ν : Measure k) {a b N N' : ℕ} (Φ : Matrix (Fin N) (Fin N') k → ℂ)
    {c₁ c₂ p₁ p₂ : ℕ} (hc : c₁ = c₂) (hp : p₁ = p₂) (h₁ : a + c₁ = N') (h₁' : b + (c₁ + 1) = N) (h₂ : a + c₂ = N')
    (h₂' : b + (c₂ + 1) = N) :
    GlobalTheory.LocFlat.flRow ψ ν p₁ (datC h₁ h₁' Φ) = GlobalTheory.LocFlat.flRow ψ ν p₂ (datC h₂ h₂' Φ) := by
  subst hc hp; rfl

theorem stepDatum_eq_datC (G : Grid k) (hs : 1 ≤ G.s) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (j : Fin (G.m - 1)) :
    stepDatum hs φ j = datC (c := G.m - 2 - j) (c' := G.m - 2 - j + 1)
      (by have := topRank_add hs (j + 1); have := j.2; show _ = G.rank (G.m, j + 1); omega)
      (by have := topRank_add hs j; have := j.2; show _ = G.rank (G.m, j); omega) (φ (.theta G.m j)) := rfl

theorem theta_sub_congr (G : Grid k) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G)
    {i i' : ℕ} (h : i = i') (p₁ : G.rank (G.m, i + 1) ≤ topRank G (i + 1)) (p₂ : G.rank (G.m, i) = topRank G i)
    (p₃ : G.rank (G.m, i' + 1) ≤ topRank G (i' + 1)) (p₄ : G.rank (G.m, i') = topRank G i') :
    φ (.theta G.m i) ((x i).submatrix (Fin.castLE p₁) (Fin.cast p₂))ᵀ =
      φ (.theta G.m i') ((x i').submatrix (Fin.castLE p₃) (Fin.cast p₄))ᵀ := by
  subst h; rfl

theorem prod_fin_even (n : ℕ) (g : ℕ → ℂ) :
    (∏ j ∈ Finset.range (2 * n), if Even j then g j else 1) = ∏ i ∈ Finset.range n, g (2 * i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, if_pos (even_two_mul n), if_neg (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one n), mul_one]

theorem locA_last (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (j : ℕ) (hj : j + 2 = G.m) :
    locA G hs ψ ν φ j (x j, x (j + 1)) =
      φ (.theta G.m (G.m - 1)) (lastMap hs (by omega) x)ᵀ * GlobalTheory.StepData.hat ψ ν (-1) (fun u =>
        GlobalTheory.LocFlat.flCol ψ ν 1 (stepDatum hs φ ⟨G.m - 2, by omega⟩) (fromCols (x (G.m - 2)) (Matrix.of fun r _ => u r)))
        (x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1))) := by
  obtain rfl : j = G.m - 2 := by omega
  rw [locA, dif_pos (by omega), stepDatum_eq_datC]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact theta_sub_congr G φ x (by omega) _ _ _ _
  · congr 1
    funext u
    exact congrFun (flCol_datC_congr ψ ν _ (by simp) rfl _ _ _ _) _

theorem locA_double (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (hm : Even G.m) (j : ℕ) (he : Even j)
    (hj : j < G.m - 2) (q) :
    locA G hs ψ ν φ j q =
      GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν ((G.m - 2 - j) / 2 + 1) (stepDatum hs φ ⟨j, by omega⟩))
        (GlobalTheory.LocFlat.flRow ψ ν ((G.m - 2 - (j + 1)) / 2 + 1) (stepDatum hs φ ⟨j + 1, by omega⟩)) q := by
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hm
  rw [locA, dif_neg (by omega), dif_pos (by omega), stepDatum_eq_datC, stepDatum_eq_datC]
  exact congrArg₂ (fun A B => GlobalTheory.LocFlat.contr ψ ν A B q)
    (flCol_datC_congr ψ ν _ (by simp only; omega) (by omega) _ _ _ _)
    (flRow_datC_congr ψ ν _ (by simp only; omega) (by omega) _ _ _ _)

end

theorem flatTensor_pureTensor_eq_prod_locA : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s), 2 ≤ G.m → Even G.m → ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) → ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (G.lines₂ (GlobalTheory.SplitFlip.oppositePath G.m) φ) x y = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * ∏ n ∈ Finset.range (G.m / 2), locA G hs ψ ν φ (2 * n) (x (2 * n), x (2 * n + 1)) := by
  intro k _ _ _ _ _ _ G hs hm hme ψ ν hψ hψ1 hν φ hφ x y
  rw [GlobalTheory.FunObj.flatTensor_pureTensor_eq_prod_contr k G hs hm hme ψ ν hψ hψ1 hν φ hφ x y, mul_assoc]
  congr 1
  obtain ⟨n, hn⟩ : ∃ n, G.m = 2 * n + 2 := by obtain ⟨b, hb⟩ := hme; exact ⟨b - 1, by omega⟩
  have hr : G.m / 2 = n + 1 := by omega
  rw [hr, Finset.prod_range_succ, mul_comm, locA_last G hs ψ ν φ x (2 * n) (by omega)]
  congr 1
  have h2 : G.m - 2 = 2 * n := by omega
  rw [← prod_fin_even n (fun j => locA G hs ψ ν φ j (x j, x (j + 1)))]
  rw [← Fin.prod_univ_eq_prod_range (fun j => if Even j then locA G hs ψ ν φ j (x j, x (j + 1)) else 1) (2 * n)]
  rw [← h2]
  refine Finset.prod_congr rfl fun j _ => if_ctx_congr Iff.rfl (fun hj => ?_) fun _ => rfl
  exact (locA_double G hs ψ ν φ ⟨n + 1, by omega⟩ j hj j.2 _).symm

end GlobalTheory.FlatPlace
