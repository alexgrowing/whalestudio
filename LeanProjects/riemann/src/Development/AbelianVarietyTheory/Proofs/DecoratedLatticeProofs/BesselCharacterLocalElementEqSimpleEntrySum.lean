import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocBesChar
open GlobalTheory.LocFrame (hA hQ besselAuxiliaryVectors IsHermitianAuxiliaryVectorSystem ent colN)
open Finset (range)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem psiE_ι {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (y : k) :
    psiE ψ (p.ι y) = ψk (y / p.xi) := by
  rw [h]
  congr 1
  have : p.ι y = p.ι (p.π (incA D D.host.xi0 * p.ι (y / p.xi))) := by
    rw [RingHom.map_mul, p.π_ι]
    change _ = p.ι (p.xi * _)
    rw [mul_div_cancel₀ _ (Witness.xi_ne p)]
  rw [this, p.ι_π, mul_left_comm, Witness.e_ι]

theorem psiE_cA (ψ : AddChar (AF D.host.F) ℂ) (x : AE D) : psiE ψ (cA D x) = psiE ψ x := by
  rw [psiE, psiE, GlobalTheory.DualPairCheck.trace_cA]

theorem psiE_supp {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) {u : AE D}
    (hu : (p.e + cA D p.e) * u = u) : psiE ψ u = ψk ((p.π u + p.π (cA D u)) / p.xi) := by
  have e : u = p.ι (p.π u) + cA D (p.ι (p.π (cA D u))) := by
    rw [p.ι_π, p.ι_π, RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA, ← add_mul, hu]
  conv_lhs => rw [e]
  rw [psiE_add, psiE_cA, psiE_ι p h, psiE_ι p h, add_div, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem hA_supp {V : HSp D} {e : AE D} {g : GA D V} (hg : SuppAt e V g) {x y : Fin V.rank → D.host.E} (h : hQ V x y = 0) :
    (e + cA D e) * hA V g x y = hA V g x y := by
  have e1 : hA V g x y = (ratV (star y) ᵥ* gA V) ⬝ᵥ (mt V g - 1) *ᵥ ratV x := by
    rw [← dotProduct_mulVec, mulVec_mulVec, mul_sub, sub_mulVec, dotProduct_sub, ← mt_one V, ← hA, ← hA,
      ← GlobalTheory.LocFrame.incA_hQ, h, map_zero, sub_zero]
  rw [e1]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hg i j
  linear_combination ((ratV (star y) ᵥ* gA V) i * ratV x j) * this

theorem π_hA (V : HSp D) (g : GA D V) (x y : Fin V.rank → D.host.E) :
    p.π (hA V g x y) = (Witness.prH p ∘ (star y ᵥ* V.gram)) ⬝ᵥ (mt V g).map p.π *ᵥ (Witness.prH p ∘ x) := by
  have h1 : ratV (star y) ᵥ* gA V = ratV (star y ᵥ* V.gram) := funext fun i => (RingHom.map_vecMul (incA D) _ _ i).symm
  rw [hA, ← mulVec_mulVec, dotProduct_mulVec, h1, GlobalTheory.LocFrame.map_dot]
  rfl

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem map_mt_inv {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) {g : GA D V} {q : GL Y k}
    (h : (mt V g).map p.π = F.β * q.val * F.γ) : (mt V g⁻¹).map p.π = F.β * (q⁻¹).val * F.γ := by
  have h1 : (mt V g⁻¹).map p.π * (mt V g).map p.π = 1 := by
    rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * q.val * F.γ) * (F.β * (q⁻¹).val * F.γ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc F.β (q⁻¹).val, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc q.val, Units.mul_inv, Matrix.one_mul, F.βγ]
  rw [← Matrix.mul_one ((mt V g⁻¹).map p.π), ← h2, ← Matrix.mul_assoc, ← h, h1, Matrix.one_mul]

theorem col_ne_zero {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (j : Y) {t : k} {x : Fin N → k}
    (h : ∀ r, F.β r j = t * x r) : t ≠ 0 := fun e => by
  have h1 := congrFun (congrFun F.γβ j) j
  simp [Matrix.mul_apply, h, e] at h1

section Coef
variable {V X : HSp D} {jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E} {a : ℕ → Fin V.rank → D.host.E}
  {κ : ℕ → D.host.E} {t : ℕ → k} (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) {M : Matrix (Fin X.rank) n k} {F : Frame k V.rank (n ⊕ Fin c)}
  (hl : ∀ r b, F.β r (Sum.inl b) = (jX.map p.pr * M) r b) (hr : ∀ (i : Fin c) r, F.β r (Sum.inr i) = t i * p.pr (a i r))
include H hl hr

theorem π_coef {g : GA D V} {q : GL (n ⊕ Fin c) k} (h : (mt V g).map p.π = F.β * q.val * F.γ) (i j : Fin c) :
    t j * p.π (hA V g (a j) (a (c - 1 - i))) = p.pr (κ i) * t i * q.val (.inr i) (.inr j) := by
  set u := Witness.prH p ∘ (star (a (c - 1 - i)) ᵥ* V.gram) with hu
  have e1 : t j • (Witness.prH p ∘ a j) = F.β *ᵥ Pi.single (.inr j) 1 := by
    rw [mulVec_single_one]
    exact funext fun r => (hr j r).symm
  have e2 (b : n) : (u ᵥ* F.β) (.inl b) = 0 := by
    have : (u ᵥ* (jX.map (Witness.prH p) * M)) b = 0 := by
      rw [← vecMul_vecMul, show u ᵥ* jX.map (Witness.prH p) = 0 from funext fun s => by
        rw [hu, ← RingHom.map_vecMul, H.perp _ (by omega), Pi.zero_apply, map_zero, Pi.zero_apply], zero_vecMul, Pi.zero_apply]
    rw [← this]
    change ∑ r, u r * F.β r (.inl b) = ∑ r, u r * (jX.map p.pr * M) r b
    exact Finset.sum_congr rfl fun r _ => congrArg (u r * ·) (hl r b)
  have e3 (l : Fin c) : (u ᵥ* F.β) (.inr l) = if l = i then p.pr (κ i) * t i else 0 := by
    have h3 : (u ᵥ* F.β) (.inr l) = t l * Witness.prH p (hQ V (a l) (a (c - 1 - i))) := by
      rw [hQ, dotProduct_mulVec, RingHom.map_dotProduct, dotProduct, Finset.mul_sum]
      change ∑ r, u r * F.β r (.inr l) = _
      refine Finset.sum_congr rfl fun r _ => ?_
      change u r * F.β r (.inr l) = t l * (u r * p.pr (a l r))
      rw [hr]; ring
    rw [h3, H.pair i i.2 l l.2]
    by_cases e : l = i
    · subst e; rw [if_pos rfl, if_pos rfl, mul_comm]; rfl
    · rw [if_neg (fun e' => e (Fin.ext e')), if_neg e, map_zero, mul_zero]
  rw [π_hA, h, ← smul_eq_mul, ← dotProduct_smul, ← mulVec_smul, e1, mulVec_mulVec, Matrix.mul_assoc, F.γβ, Matrix.mul_one,
    ← mulVec_mulVec, dotProduct_mulVec, mulVec_single_one, dotProduct, Fintype.sum_sum_type]
  simp [← hu, e2, e3]

theorem π_simple {g : GA D V} {q : GL (n ⊕ Fin c) k} (h : (mt V g).map p.π = F.β * q.val * F.γ) {i : ℕ} (hi : i + 1 < c)
    {x : k} (hx : p.pr (κ i) * t i = x * t (i + 1)) : p.π (hA V g (a (i + 1)) (a (c - 1 - i))) = x * ent q i := by
  have h1 := π_coef p H hl hr h ⟨i, by omega⟩ ⟨i + 1, hi⟩
  have h2 : t (i + 1) ≠ 0 := col_ne_zero F _ (hr ⟨i + 1, hi⟩)
  rw [ent, dif_pos hi]
  refine mul_left_cancel₀ h2 (h1.trans ?_)
  simp only [hx]
  ring

end Coef

def scal {ρ : ℕ} (B : BesLev D ρ) (s : k) (i : ℕ) : k :=
  if i < ρ then s * p.xi ^ (ρ - i) else if i = ρ then s else s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - i))

theorem scal_lo {ρ : ℕ} (B : BesLev D ρ) (s : k) {i : ℕ} (hi : i < ρ) :
    p.pr (if i = ρ then hQ B.L B.ζ B.ζ else 1) * scal p B s i = p.xi * scal p B s (i + 1) := by
  rw [if_neg hi.ne, show p.pr 1 = 1 from (Witness.prH p).map_one, scal, scal, if_pos hi]
  split_ifs with h1 h2
  · rw [show ρ - i = ρ - (i + 1) + 1 by omega]; ring
  · rw [show ρ - i = 1 by omega]; ring
  · omega

theorem scal_hi {ρ : ℕ} (B : BesLev D ρ) (s : k) {i : ℕ} (hi : ρ ≤ i) (hi' : i < 2 * ρ) :
    p.pr (if i = ρ then hQ B.L B.ζ B.ζ else 1) * scal p B s i = -p.xi * scal p B s (i + 1) := by
  have hx := Witness.xi_ne p
  rw [scal, scal, if_neg (show ¬ i < ρ by omega), if_neg (show ¬ i + 1 < ρ by omega), if_neg (show ¬ i + 1 = ρ by omega)]
  split_ifs with h1
  · rw [show ρ - 1 - (2 * ρ - (i + 1)) = 0 by omega]
    change p.hz B * s = _
    field_simp
  · rw [show ρ - 1 - (2 * ρ - (i + 1)) = ρ - 1 - (2 * ρ - i) + 1 by omega, show p.pr 1 = 1 from (Witness.prH p).map_one, pow_succ]
    field_simp

theorem col_eq {ρ : ℕ} {B : BesLev D ρ} {s : k} {FA : Frame k B.A.rank n} {FV : Frame k B.V.rank (n ⊕ Fin c)}
    (h : p.IsBesFrame B s FA FV) (i : Fin c) (r) :
    FV.β r (Sum.inr i) = scal p B s i * p.pr (besselAuxiliaryVectors B.d (vecB B.o B.ζ) i r) := by
  obtain ⟨hc, -, h1, h2, h3⟩ := h
  have := i.2
  unfold scal besselAuxiliaryVectors
  split_ifs with e1 e2
  · rw [h1 ⟨i, e1⟩ i rfl r, colN, dif_pos e1]
  · exact h2 i e2 r
  · have e3 : 2 * ρ - i < ρ := by omega
    rw [h3 ⟨2 * ρ - i, e3⟩ i (by simp only; omega) r, colN, dif_pos e3]

theorem psiBes_isLoc : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → psiBes ψ B.d 1 (vecB B.o B.ζ) g = (ψk (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  intro D k _ _ _ _ p ψ ψk hψ σ B s n _ _ c FA FV hF g q hq hg
  obtain rfl := hF.1
  have H := GlobalTheory.LocFrame.isHermitianAuxiliaryVectorSystem_besselVectors B.d B.o B.line
  have hx := Witness.xi_ne p
  rw [psiBes, map_one, one_mul, GlobalTheory.LocFrame.simpleSum_eq_sum_hA, psiE_supp p hψ, GlobalTheory.LocFrame.simpleSum_eq_sum_ent]
  · congr 2
    rw [div_eq_iff hx, show 2 * σ + 1 - 1 = σ + σ by omega, Finset.sum_range_add, add_mul, map_sum, map_sum, map_sum,
      Finset.sum_mul, ← Finset.sum_range_reflect (fun i => ent q (σ + i)), Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have h1 := π_simple p H hF.2.1 (col_eq p hF) hg.2 (i := i) (by omega) (scal_lo p B s hi')
      rw [show σ + σ - i = 2 * σ + 1 - 1 - i by omega, h1, mul_comm]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have h1 := π_simple p H hF.2.1 (col_eq p hF) (map_mt_inv p FV hg.2) (i := σ + (σ - 1 - i)) (by omega)
        (scal_hi p B s (by omega) (by omega))
      rw [show 2 * σ + 1 - 1 - (σ + (σ - 1 - i)) = i + 1 by omega, show σ + (σ - 1 - i) + 1 = σ + σ - i by omega,
        GlobalTheory.LocFrame.ent_inv hq] at h1
      rw [GlobalTheory.LocFrame.cA_hA, h1]
      ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => hA_supp hg.1 ?_
    have hi' := Finset.mem_range.1 hi
    rw [H.pair i (by omega) _ (by omega), if_neg (by omega)]

end GlobalTheory.LocBesChar
end
