import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFrameHalfInverseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.LocFlatFB
open GlobalTheory.LocFlat

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

def embR (l : Fin c) (x₀ : Matrix (n ⊕ Unit) n' k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fun r q => match r, q with
  | Sum.inl a, Sum.inl s => x₀ (Sum.inl a) s
  | Sum.inr l', Sum.inl s => if l' = l then x₀ (Sum.inr ()) s else 0
  | _, Sum.inr _ => 0

def restr (l : Fin c) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : Matrix (n ⊕ Unit) n' k :=
  fun r s => match r with
  | Sum.inl a => t (Sum.inl a) (Sum.inl s)
  | Sum.inr _ => t (Sum.inr l) (Sum.inl s)

theorem affPt_add_rowAt (l : Fin c) (p : ℕ) (hl : l.val + 1 = p) (x x₀ : Matrix (n ⊕ Unit) n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p x.toRows₁ e + rowAt n c p (x (Sum.inr ())) + embR l x₀ =
      affPt p (x + x₀).toRows₁ e + rowAt n c p ((x + x₀) (Sum.inr ())) := by
  ext (a | a) (s | s)
  · simp [affPt, basePt, rowAt, embR, Free, toRows₁]
  · simp [affPt, basePt, rowAt, embR, Free]
  · by_cases h : a = l
    · subst h; simp [affPt, basePt, rowAt, embR, Free, hl]
    · have h' : ¬ a.val + 1 = p := fun h2 => h (Fin.ext (by omega))
      simp [affPt, basePt, rowAt, embR, Free, h, h']
  · simp [affPt, basePt, rowAt, embR, Free]

theorem ch_affPt_add (p : ℕ) (x x₀ : Matrix (n ⊕ Unit) n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (affPt p (x + x₀).toRows₁ e) = ch (affPt p x.toRows₁ e) := by
  simp [ch, affPt, basePt, Matrix.add_apply]

theorem flRow_translate (ψ : AddChar k Circle) (ν : Measure k) (l : Fin c) (p : ℕ) (hl : l.val + 1 = p)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ x : Matrix (n ⊕ Unit) n' k) :
    GlobalTheory.LocFlat.flRow ψ ν p (fun t => Φ (t + embR l x₀)) x = GlobalTheory.LocFlat.flRow ψ ν p Φ (x + x₀) := by
  unfold GlobalTheory.LocFlat.flRow GlobalTheory.RootEx.opE
  congr 1
  funext e
  dsimp only
  rw [affPt_add_rowAt l p hl x x₀ e, ch_affPt_add]

theorem restr_affPt (l : Fin c) (p : ℕ) (hl : l.val + 1 = p) (x : Matrix (n ⊕ Unit) n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    restr l (affPt p x.toRows₁ e + rowAt n c p (x (Sum.inr ()))) = x := by
  ext (a | a) s
  · simp [restr, affPt, basePt, rowAt, Free, toRows₁]
  · simp [restr, affPt, basePt, rowAt, Free, hl]

theorem flRow_modulate (ψ : AddChar k Circle) (ν : Measure k) (l : Fin c) (p : ℕ) (hl : l.val + 1 = p)
    (Φ Φ' : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (g : Matrix (n ⊕ Unit) n' k → ℂ)
    (h : ∀ t, Φ' t = g (restr l t) * Φ t) (x : Matrix (n ⊕ Unit) n' k) :
    GlobalTheory.LocFlat.flRow ψ ν p Φ' x = g x * GlobalTheory.LocFlat.flRow ψ ν p Φ x := by
  unfold GlobalTheory.LocFlat.flRow GlobalTheory.RootEx.opE
  rw [← integral_const_mul]
  congr 1
  funext e
  dsimp only
  rw [h, restr_affPt l p hl x e, mul_assoc]

end Local

end GlobalTheory.LocFlatFB

namespace GlobalTheory.LocFlatFB
open GlobalTheory.LocFlat

section Frames

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem map_pr_mul {l m m' : Type} [Fintype m] (M : Matrix l m D.host.E) (N : Matrix m m' D.host.E) :
    (M * N).map p.pr = M.map p.pr * N.map p.pr := Matrix.map_mul (f := prH p)

theorem pr_mulVec {l m : Type} [Fintype m] (M : Matrix l m D.host.E) (v : m → D.host.E) (r : l) :
    p.pr ((M *ᵥ v) r) = ∑ a, p.pr (M r a) * p.pr (v a) := by
  change prH p (∑ a, M r a * v a) = ∑ a, prH p (M r a) * prH p (v a)
  simp only [map_sum, map_mul]

theorem wittDecomposition_coreProj_mul_core_eq_one {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.q0 * d.i₀ = 1 :=
  rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)

theorem projection_q_zero_i_zero_eq_one {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.q0.map p.pr * d.i₀.map p.pr = 1 := by
  rw [← map_pr_mul, wittDecomposition_coreProj_mul_core_eq_one]
  exact Matrix.map_one _ (map_zero (prH p)) (map_one (prH p))

theorem projection_q_zero_e_eq_zero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.q0.map p.pr * d.e.map p.pr = 0 := by
  have h : d.q0 * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jX)
  rw [← map_pr_mul, h]
  exact Matrix.map_zero _ (map_zero (prH p))

theorem projection_q_zero_e_prime_eq_zero {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.q0.map p.pr * d.e'.map p.pr = 0 := by
  have h : d.q0 * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jY)
  rw [← map_pr_mul, h]
  exact Matrix.map_zero _ (map_zero (prH p))

theorem mul_col_eq {R m N Y Z : Type} [CommRing R] [Fintype N] (Q : Matrix m N R) (F : Matrix N Y R) (y : Y) (C : R)
    (E : Matrix N Z R) (z : Z) (h : ∀ r, F r y = C * E r z) (a : m) : (Q * F) a y = C * (Q * E) a z := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem mul_col_eq' {R m N Y Z : Type} [CommRing R] [Fintype N] (Q : Matrix m N R) (F : Matrix N Y R) (y : Y)
    (E : Matrix N Z R) (z : Z) (h : ∀ r, F r y = E r z) (a : m) : (Q * F) a y = (Q * E) a z := by
  simp only [Matrix.mul_apply, h]

def selR (R n : Type) [CommRing R] [DecidableEq n] {c : ℕ} (l : Fin c) : Matrix (n ⊕ Unit) (n ⊕ Fin c) R :=
  fromBlocks 1 0 0 (Matrix.of fun _ j => if j = l then 1 else 0)

def selC (R n' : Type) [CommRing R] [DecidableEq n'] (c : ℕ) : Matrix n' (n' ⊕ Fin c) R := fromCols 1 0

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem embR_eq (l : Fin c) (x₀ : Matrix (n ⊕ Unit) n' k) :
    embR l x₀ = (selR k n l)ᵀ * x₀ * selC k n' (c + 1) := by
  ext (a | a) (s | s) <;> simp [embR, selR, selC, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem restr_eq (l : Fin c) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    restr l t = selR k n l * t * (selC k n' (c + 1))ᵀ := by
  ext (a | a) s <;> simp [restr, selR, selC, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

variable {p}

theorem jac_inc {ρ : ℕ} {J : JacLev D ρ} {s hh : k} {G₀ : Frame k J.W₀.rank n'} {F : Frame k J.W.rank (n' ⊕ Fin c)}
    (h : p.IsJacFrame J s hh G₀ F) : F.γ * J.d.i₀.map p.pr = (selC k n' c)ᵀ * G₀.γ := by
  have h1 : F.β * (selC k n' c)ᵀ = J.d.i₀.map p.pr * G₀.β := by
    ext r a
    rw [← h.2.1 r a]
    simp [selC, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  rw [← Matrix.mul_one (J.d.i₀.map p.pr), ← G₀.βγ, ← Matrix.mul_assoc (J.d.i₀.map p.pr), ← h1, Matrix.mul_assoc,
    ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul]

theorem jac_proj {ρ : ℕ} {J : JacLev D ρ} {s hh : k} {G₀ : Frame k J.W₀.rank n'} {F : Frame k J.W.rank (n' ⊕ Fin c)}
    (h : p.IsJacFrame J s hh G₀ F) : selC k n' c * F.γ = G₀.γ * J.d.q0.map p.pr := by
  have h1 : G₀.γ * J.d.q0.map p.pr * F.β = selC k n' c := by
    ext a (b | j)
    · rw [mul_col_eq' _ _ _ _ b (fun r => h.2.1 r b), Matrix.mul_assoc, ← Matrix.mul_assoc (J.d.q0.map p.pr), projection_q_zero_i_zero_eq_one,
        Matrix.one_mul, G₀.γβ]
      simp [selC]
    · have hc := h.1
      by_cases hj : j.val < ρ
      · rw [mul_col_eq _ _ _ _ (J.d.e.map p.pr) ⟨j.val, hj⟩ (h.2.2.1 ⟨j.val, hj⟩ j rfl), Matrix.mul_assoc, projection_q_zero_e_eq_zero]
        simp [selC]
      · have := j.2
        rw [mul_col_eq _ _ _ _ (J.d.e'.map p.pr) ⟨2 * ρ - 1 - j.val, by omega⟩
          (h.2.2.2 ⟨2 * ρ - 1 - j.val, by omega⟩ j (by dsimp only; omega)), Matrix.mul_assoc, projection_q_zero_e_prime_eq_zero]
        simp [selC]
  rw [← h1, Matrix.mul_assoc, F.βγ, Matrix.mul_one]

theorem bes_inc {ρ : ℕ} {B : BesLev D ρ} {s : k} {FA : Frame k B.A.rank n} {F₀ : Frame k B.V₀.rank (n ⊕ Unit)}
    {F : Frame k B.V.rank (n ⊕ Fin c)} (h₀ : p.IsCoreFrame B s FA F₀) (h : p.IsBesFrame B s FA F) (l : Fin c)
    (hl : l.val = ρ) : F.β * (selR k n l)ᵀ = B.d.i₀.map p.pr * F₀.β := by
  ext r (b | u)
  · rw [mul_col_eq' _ F₀.β _ _ b (fun r => h₀.1 r b), ← Matrix.mul_assoc, ← map_pr_mul, ← h.2.1 r b]
    simp [selR, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · have h1 : (F.β * (selR k n l)ᵀ) r (Sum.inr u) = F.β r (Sum.inr l) := by
      simp [selR, Matrix.mul_apply, Fintype.sum_sum_type]
    rw [h1, h.2.2.2.1 l hl r, pr_mulVec, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [h₀.2 a, Matrix.map_apply]; ring

theorem bes_proj {ρ : ℕ} {B : BesLev D ρ} {s : k} {FA : Frame k B.A.rank n} {F₀ : Frame k B.V₀.rank (n ⊕ Unit)}
    {F : Frame k B.V.rank (n ⊕ Fin c)} (h₀ : p.IsCoreFrame B s FA F₀) (h : p.IsBesFrame B s FA F) (l : Fin c)
    (hl : l.val = ρ) : B.d.q0.map p.pr * F.β = F₀.β * selR k n l := by
  have h1 : B.d.q0.map p.pr * F.β * (selR k n l)ᵀ = F₀.β := by
    rw [Matrix.mul_assoc, bes_inc h₀ h l hl, ← Matrix.mul_assoc, projection_q_zero_i_zero_eq_one, Matrix.one_mul]
  have h2 : ∀ r (j : Fin c), j ≠ l → (B.d.q0.map p.pr * F.β) r (Sum.inr j) = 0 := by
    intro r j hj
    have hc := h.1
    have hj' : j.val ≠ ρ := fun e => hj (Fin.ext (e.trans hl.symm))
    by_cases hj : j.val < ρ
    · rw [mul_col_eq _ _ _ _ (B.d.e.map p.pr) ⟨j.val, hj⟩ (h.2.2.1 ⟨j.val, hj⟩ j rfl), projection_q_zero_e_eq_zero]
      simp
    · have := j.2
      rw [mul_col_eq _ _ _ _ (B.d.e'.map p.pr) ⟨2 * ρ - j.val, by omega⟩
        (h.2.2.2.2 ⟨2 * ρ - j.val, by omega⟩ j (by dsimp only; omega)), projection_q_zero_e_prime_eq_zero]
      simp
  rw [← h1]
  generalize B.d.q0.map p.pr * F.β = M at h2
  ext r (b | j)
  · simp [selR, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · by_cases hj : j = l
    · subst hj
      simp [selR, Matrix.mul_apply, Fintype.sum_sum_type]
    · rw [h2 r j hj]
      simp [selR, Matrix.mul_apply, Fintype.sum_sum_type, hj]

end Frames

end GlobalTheory.LocFlatFB

namespace GlobalTheory.LocFlatFB
open GlobalTheory.LocFlat

section Adelic

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

theorem incA_mul_ι (a : D.host.E) (x : k) : (incA D a : AE D) * p.ι x = p.ι (p.pr a * x) := by
  have h : p.pr a * x = p.π ((incA D a : AE D) * p.ι x) := by rw [map_mul, p.π_ι]; rfl
  rw [h, p.ι_π, mul_left_comm, e_mul_ι]

theorem rat_mul_ι {l m n : ℕ} (M : Matrix (Fin l) (Fin m) D.host.E) (N : Matrix (Fin m) (Fin n) k) :
    (rat M : Mx D l m) * (N.map p.ι : Mx D m n) = (M.map p.pr * N).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, rat]
  exact Finset.sum_congr rfl fun a _ => incA_mul_ι p _ _

theorem ι_mul_rat {l m n : ℕ} (N : Matrix (Fin l) (Fin m) k) (M : Matrix (Fin m) (Fin n) D.host.E) :
    (N.map p.ι : Mx D l m) * (rat M : Mx D m n) = (N * M.map p.pr).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, rat]
  exact Finset.sum_congr rfl fun a _ => by rw [mul_comm (N i a), mul_comm, incA_mul_ι]

theorem infPart_eq_zero {e : AE D} (he : IsSplitIdem D e) {z : AE D} (hz : e * z = z ∨ cA D e * z = z) :
    infPart D z = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have h4 : (e + cA D e) * cA D e = cA D e := by rw [add_mul, h2, he', zero_add]
  have h5 : (e + cA D e) * e = e := by rw [add_mul, h1, mul_comm, h2, add_zero]
  rcases hz with hz | hz
  · rw [← hz, ← h5, h3, map_mul, map_mul, h0, zero_mul, zero_mul]
  · rw [← hz, ← h4, h3, map_mul, map_mul, h0, zero_mul, zero_mul]

theorem mxAt_of_half {e : AE D} (he : IsSplitIdem D e) {m n : ℕ} {x : Mx D m n}
    (hx : IsHalf e x ∨ IsHalf (cA D e) x) : GlobalTheory.FinPl.MxAt (fun _ => True) x := fun i j =>
  Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (infPart_eq_zero he (hx.imp (fun h => h i j) fun h => h i j)),
    (Submodule.mem_iInf _).2 fun w => (w.2 trivial).elim⟩

theorem isHalf_mul {e : AE D} {l m n r : ℕ} (A : Mx D l m) {y : Mx D m n} (hy : IsHalf e y) (C : Mx D n r) :
    IsHalf e (A * y * C : Mx D l r) := by
  have h : e • y = y := by ext i j; exact hy i j
  intro i j
  have h2 : e • (A * y * C : Mx D l r) = A * y * C := by rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]
  exact congrFun (congrFun h2 i) j

theorem hO_core {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) (x : WO S T) (y : WO S₀ T₀) :
    hO S T x (dS.ext0 T (dT.inc0 S₀ y)) = hO S₀ T₀ (dT.p0 * x * dS.j0 : Mx D _ _) y := by
  rw [dS.hO_coordS, dT.hO_coordT]
  simp only [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc, HypDec.p0_jX, HypDec.p0_j0, HypDec.p0_jY,
    Matrix.mul_one, Matrix.mul_zero, pairS, adj_zero, Matrix.zero_mul, trace_zero, zero_add, add_zero]
  simp only [← Matrix.mul_assoc, HypDec.pX_j0, HypDec.pY_j0, HypDec.p0_j0, Matrix.one_mul, Matrix.zero_mul, pairT,
    adj_zero, Matrix.mul_zero, trace_zero, zero_add, add_zero]

theorem continuous_hO_up {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (y : WO S T) :
    Continuous fun t : Matrix Y Y' k => p.π (hO S T (p.up FS FT t) y) := by
  have h : Continuous fun t : Matrix Y Y' k => p.up FS FT t :=
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_map p.cont_ι
  refine p.cont_π.comp ?_
  unfold hO
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_finset_sum _ fun c _ =>
    continuous_finset_sum _ fun d _ => continuous_const.mul (h.matrix_elem d a)

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c ρ σ : ℕ}
  {J : JacLev D ρ} {B : BesLev D σ} {s hh s' : k} {G₀ : Frame k J.W₀.rank n'} {FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))}
  {FA : Frame k B.A.rank n} {F₀ : Frame k B.V₀.rank (n ⊕ Unit)} {FV : Frame k B.V.rank (n ⊕ Fin c)}

variable {p}

theorem up_embR (hJ : p.IsJacFrame J s hh G₀ FW) (h₀ : p.IsCoreFrame B s' FA F₀) (hB : p.IsBesFrame B s' FA FV)
    (l : Fin c) (hl : l.val = σ) (x₀ : Matrix (n ⊕ Unit) n' k) :
    p.up FW FV (embR l x₀) = J.d.ext0 B.V (B.d.inc0 J.W₀ (p.up G₀ F₀ x₀)) := by
  rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Place.up, Place.up, HypDec.j0, HypDec.p0, rat_mul_ι, ι_mul_rat, embR_eq]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, bes_inc h₀ hB l hl, Matrix.mul_assoc, jac_proj hJ]
  simp only [Matrix.mul_assoc]

theorem core_up (hJ : p.IsJacFrame J s hh G₀ FW) (h₀ : p.IsCoreFrame B s' FA F₀) (hB : p.IsBesFrame B s' FA FV)
    (l : Fin c) (hl : l.val = σ) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    (B.d.p0 * p.up FW FV t * J.d.j0 : Mx D _ _) = p.up G₀ F₀ (restr l t) := by
  rw [Place.up, Place.up, HypDec.j0, HypDec.p0, rat_mul_ι, ι_mul_rat, restr_eq]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, bes_proj h₀ hB l hl, Matrix.mul_assoc, jac_inc hJ]
  simp only [Matrix.mul_assoc]

end Adelic

theorem factor_isModel : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (T₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix (n ⊕ Unit) n' k)), Ψ.1 = GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ.1 → flatFB st (Tm Φ) = T₀ Ψ) → p.IsModel ψ G₀ F₀ T₀ := by
  intro D hFLs _ k _ _ _ _ _ _ p ν hν ψ ψk hχ σ J B st s _ n n' _ _ _ _ c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm T₀ hT
  have hcont := ((GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std).2.1 ψk hχ).1
  have hc : c = 2 * σ + 1 := hBF.1
  have hF := ((hFLs ψ fun _ => True).2 σ J B st).Heisenberg₂
  let l : Fin c := ⟨σ, by omega⟩
  have hon : ∀ Ψ : SB (Matrix (n ⊕ Unit) n' k), ∃ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      Ψ.1 = flRow ψk ν (σ + 1) Φ.1 := fun Ψ => by
    obtain ⟨Φ, hΦ, h⟩ := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k ψk ν hcont hν n n' c (σ + 1) (by omega)).2 (by omega)).2 Ψ.1 Ψ.2
    exact ⟨⟨Φ, hΦ⟩, h.symm⟩
  refine ⟨fun Ψ => ?_, fun x₀ Ψ Ψ' hΨ' => ?_, fun y hy Ψ Ψ' hΨ' => ?_⟩
  · obtain ⟨Φ, h⟩ := hon Ψ
    rw [← hT Φ Ψ h]
    exact hF.theta _ (hTm.theta Φ)
  · obtain ⟨Φ, h⟩ := hon Ψ
    let Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨fun t => Φ.1 (t + embR l x₀),
      Φ.2.1.comp_continuous (continuous_add_right _), Φ.2.2.comp_homeomorph (Homeomorph.addRight (embR l x₀))⟩
    have h' : Ψ'.1 = flRow ψk ν (σ + 1) Φ'.1 := funext fun x => by
      rw [hΨ', h]; exact (flRow_translate ψk ν l (σ + 1) rfl Φ.1 x₀ x).symm
    rw [← hT Φ' Ψ' h', ← hT Φ Ψ h, hTm.trans (embR l x₀) Φ Φ' fun _ => rfl, up_embR hJF hCF hBF l rfl]
    exact hF.core _ (hTm.theta Φ) _ (mxAt_of_half p.split (Or.inl fun i j => e_mul_ι p _))
  · obtain ⟨Φ, h⟩ := hon Ψ
    have hY : IsHalf (cA D p.e) (J.d.ext0 B.V (B.d.inc0 J.W₀ y)) := isHalf_mul B.d.j0 hy J.d.p0
    have hlc : IsLocallyConstant fun t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
        ψ (symplO J.W B.V (p.up FW FV t) (J.d.ext0 B.V (B.d.inc0 J.W₀ y))) := by
      simp only [fun t => (GlobalTheory.T.heisenberg_frame_half_inverse D k p _ _ J.W B.V FW FV ψ ψk hχ).2.2.2.1 t _ hY]
      exact (GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψk hcont).comp_continuous
        (continuous_hO_up p FW FV _)
    let Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
      ⟨fun t => ψ (symplO J.W B.V (p.up FW FV t) (J.d.ext0 B.V (B.d.inc0 J.W₀ y))) * Φ.1 t,
        hlc.mul Φ.2.1, Φ.2.2.mul_left⟩
    have h' : Ψ'.1 = flRow ψk ν (σ + 1) Φ'.1 := funext fun x => by
      rw [hΨ', h]
      refine (flRow_modulate ψk ν l (σ + 1) rfl Φ.1 Φ'.1 (fun x => ψ (symplO J.W₀ B.V₀ (p.up G₀ F₀ x) y))
        (fun t => ?_) x).symm
      change ψ (symplO J.W B.V _ _) * _ = _
      rw [symplO, hO_core, core_up hJF hCF hBF l rfl, symplO]
    rw [← hT Φ' Ψ' h', ← hT Φ Ψ h, hTm.modul _ hY Φ Φ' fun _ => rfl]
    exact hF.core _ (hTm.theta Φ) _ (mxAt_of_half p.split (Or.inr hy))

end GlobalTheory.LocFlatFB

end
