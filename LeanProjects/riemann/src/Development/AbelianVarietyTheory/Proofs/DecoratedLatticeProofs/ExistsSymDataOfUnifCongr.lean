import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainOneCouplingCosetOfPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain
namespace UnifChange
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

theorem apply_mul_KOne {f : Matrix ι ι' k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x) (hp : ∀ x y, MaxM y → f (x + y) = f x)
    {a : GL ι k} (ha : a ∈ KOne k ι) {b : GL ι' k} (hb : b ∈ KOne k ι') (x : Matrix ι ι' k) :
    f (a.val * x * b.val) = f x := by
  obtain ⟨a1, a2⟩ := mem_KO.1 (KOne_le_KO ha)
  obtain ⟨b1, b2⟩ := mem_KO.1 (KOne_le_KO hb)
  by_cases hx : IntM x
  · have e : a.val * x * b.val = x + ((a.val - 1) * x * b.val + x * (b.val - 1)) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
    rw [e]
    exact hp _ _ ((((mem_KOne.1 ha).mul_intM hx).mul_intM b1).add (hx.mul_maxM (mem_KOne.1 hb)))
  · have h1 : f x = 0 := by_contra fun h => hx (hs _ h)
    rw [h1]
    by_contra h
    have := (a2.mul (hs _ h)).mul b2
    apply hx
    simpa [Matrix.mul_assoc, ← Matrix.mul_assoc (a⁻¹).val] using this

theorem reGL_symm_mem_KOne (e : ι ≃ Y) {d : GL Y k} (hd : d ∈ KOne k Y) : (reGL e).symm d ∈ KOne k ι :=
  mem_KOne.2 fun i j => by simpa [reGL_symm_val, Matrix.one_apply] using mem_KOne.1 hd (e i) (e j)

def Near (F G : LatFrame k ι Y) : Prop := G.ord = F.ord ∧ F.bas⁻¹ * G.bas ∈ KOne k Y

theorem Near.conj {F G : LatFrame k ι Y} (h : Near F G) :
    ∃ d ∈ KOne k ι, ∀ g, G.conj.symm g = d⁻¹ * F.conj.symm g * d := by
  refine ⟨_, reGL_symm_mem_KOne F.ord h.2, fun g => ?_⟩
  rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply, h.1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have : reGL F.ord (F.conj.symm g) = F.bas⁻¹ * g * F.bas := by
    conv_rhs => rw [← F.conj.apply_symm_apply g, LatFrame.conj_apply]
    group
  rw [this]; group

theorem Near.J_eq {F G : LatFrame k ι Y} (h : Near F G) (P : TypeDatum k ι) :
    (P.toLevel.map G.conj).J = (P.toLevel.map F.conj).J := by
  obtain ⟨d, hd, e⟩ := h.conj
  ext g
  rw [Level.mem_map, Level.mem_map, e, P.J.mul_mem_cancel_right (P.KOne_le hd),
    P.J.mul_mem_cancel_left (inv_mem (P.KOne_le hd))]

theorem Near.stabLat_eq {F G : LatFrame k ι Y} (h : Near F G) : stabLat G.bas = stabLat F.bas := by
  ext g
  have hd := KOne_le_KO h.2
  have e : G.bas⁻¹ * g * G.bas = (F.bas⁻¹ * G.bas)⁻¹ * (F.bas⁻¹ * g * F.bas) * (F.bas⁻¹ * G.bas) := by group
  rw [mem_stabLat, mem_stabLat, e, (KO k Y).mul_mem_cancel_right hd, (KO k Y).mul_mem_cancel_left (inv_mem hd)]

theorem Near.transport_eq {F G : LatFrame k ι Y} {F' G' : LatFrame k ι' Y'} (h : Near F G) (h' : Near F' G')
    {f : Matrix ι ι' k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x) (hp : ∀ x y, MaxM y → f (x + y) = f x) :
    G.transport G' f = F.transport F' f := by
  funext x
  change f (G.coords G' x) = f (F.coords F' x)
  rw [← apply_mul_KOne hs hp (reGL_symm_mem_KOne F.ord (inv_mem h.2)) (reGL_symm_mem_KOne F'.ord h'.2) (F.coords F' x)]
  congr 1
  unfold LatFrame.coords
  rw [reGL_symm_val, reGL_symm_val, submatrix_mul_equiv, submatrix_mul_equiv, h.1, h'.1]
  congr 1
  simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.bas.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc F'.bas.val, Units.mul_inv,
    Matrix.one_mul]

theorem near_refl (F : LatFrame k ι Y) : Near F F := ⟨rfl, by simp⟩

theorem val_pow_sub_one {u : k} (hu : valuation k (u - 1) < 1) (m : ℕ) : valuation k (u ^ m - 1) < 1 := by
  have h1 : valuation k u ≤ 1 := by
    have := Valuation.map_add_le (valuation k) hu.le (le_of_eq (map_one (valuation k)))
    simpa using this
  induction m with
  | zero => simp
  | succ m ih =>
    have e : u ^ (m + 1) - 1 = u * (u ^ m - 1) + (u - 1) := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ hu
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h1 zero_le ih

variable {ϖ ϖ' : kˣ}

theorem val_div_sub_one (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k ((ϖ : k)⁻¹ * ϖ' - 1) < 1 := by
  have e : (ϖ : k)⁻¹ * ϖ' - 1 = (ϖ : k)⁻¹ * ((ϖ' : k) - ϖ) := by field_simp
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  rwa [e, map_mul, map_inv₀, inv_mul_lt_one₀ h0]

theorem near_typeFrame {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) (o : ι ≃ n ⊕ Fin c) :
    Near (typeFrame ϖ o) (typeFrame ϖ' o) := by
  refine ⟨rfl, mem_KOne.2 fun i j => ?_⟩
  rw [Units.val_mul, GlobalTheory.SymSupport.typeFrame_inv_val, GlobalTheory.SymSupport.typeFrame_val, diagonal_mul_diagonal,
    ← diagonal_one, diagonal_sub, diagonal_apply]
  split_ifs
  · rcases i with i | i
    · simp
    · have := val_pow_sub_one (val_div_sub_one h) (i.val + 1)
      rwa [mul_pow, inv_pow] at this
  · simp

theorem val_eq (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k (ϖ' : k) = valuation k (ϖ : k) := Valuation.map_eq_of_sub_lt _ h

theorem isUnif_of_near (hϖ : IsUnif ϖ) (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) : IsUnif ϖ' :=
  fun x => by rw [val_eq h]; exact hϖ x

theorem inv_sub_inv_mem (hϖ : IsUnif ϖ) (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) :
    valuation k (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) ≤ 1 := by
  have h1 := (hϖ _).1 (val_div_sub_one h)
  have e : ((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k) = -((ϖ' : k)⁻¹ * ((ϖ : k)⁻¹ * ϖ' - 1)) := by
    simp only [Units.val_inv_eq_inv_val]; field_simp; ring
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  rwa [e, Valuation.map_neg, map_mul, map_inv₀, val_eq h, inv_mul_le_one₀ h0]

theorem psi_inv_mul {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ)
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) {x : k} (hx : x ∈ 𝒪[k]) :
    ψ ((ϖ'⁻¹ : kˣ) * x) = ψ ((ϖ⁻¹ : kˣ) * x) := by
  have hi : (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) * x ∈ 𝒪[k] := mul_mem (inv_sub_inv_mem hϖ h) hx
  have e : ((ϖ'⁻¹ : kˣ) : k) * x = (ϖ⁻¹ : kˣ) * x + (((ϖ'⁻¹ : kˣ) : k) - ((ϖ⁻¹ : kˣ) : k)) * x := by ring
  rw [e, AddChar.map_add_eq_mul, hψ.eq_one (show _ ∈ cball (1 : kˣ) from hi), mul_one]

theorem isSymLevel_of_near {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ)
    (h : valuation k ((ϖ' : k) - (ϖ : k)) < valuation k (ϖ : k)) {ρ κ l : ℕ} {P : TypeDatum k (Fin κ ⊕ Fin l)}
    (hP : IsSymLevel ψ ϖ ρ P) : IsSymLevel ψ ϖ' ρ P := by
  refine ⟨hP.1, fun g => ?_⟩
  have hg := intM_of_mem_KO (P.le_KO g.2)
  rw [hP.2 g, psi_inv_mul hψ hϖ h, psi_inv_mul hψ hϖ h]
  · refine sum_mem fun r _ => sum_mem fun s _ => ?_
    split_ifs
    exacts [hg _ _, zero_mem _]
  · unfold simpleSum
    refine sum_mem fun r _ => sum_mem fun s _ => ?_
    split_ifs
    exacts [hg _ _, zero_mem _]

variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem transport_iterPhi (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    {F G : LatFrame k (Ix r t (j + 1)) Y} {F' G' : LatFrame k (Ix r t j) Y'} (h : Near F G) (h' : Near F' G') :
    G.transport G' (P.iterPhi t μ hμ j) = F.transport F' (P.iterPhi t μ hμ j) :=
  h.transport_eq h'
    (fun x hx i l => by simpa using TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc r t j).symm i) l)
    fun x y hy => TypeDatum.Phi_add _ (hμ _) (x.submatrix (ixSucc r t j) id) (y := y.submatrix (ixSucc r t j) id)
      fun _ _ => hy _ _

end General
end UnifChange

open UnifChange

theorem exists_symData_of_unif_congr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {s κ : ℕ} (S : SymData k s κ) (ϖ' : kˣ), valuation k ((ϖ' : k) - (S.ϖ : k)) < valuation k (S.ϖ : k) → ∃ S' : SymData k s κ, S'.ϖ = ϖ' ∧ S'.ψ = S.ψ ∧ S'.ρ = S.ρ ∧ S'.P = S.P ∧ S'.μ = S.μ ∧ ∀ (τ : ℕ) (ν : Measure k), (∀ j c h, (S'.T (Fin τ)).Phi j c h = (S.T (Fin τ)).Phi j c h) ∧ (∀ j c h, (S'.T (Fin τ)).entry S'.ψ ν j c h 1 1 = (S.T (Fin τ)).entry S.ψ ν j c h 1 1) ∧ (∀ x₀, (S'.T (Fin τ)).Psi 1 x₀ (S'.y0 (Fin τ)) = (S.T (Fin τ)).Psi 1 x₀ (S.y0 (Fin τ))) ∧ (S'.T (Fin τ)).xiTop (box _ (1 : kˣ)) S'.ψ ν (-1) (Submodule.Quotient.mk (S'.y0 (Fin τ))) = (S.T (Fin τ)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin τ))) := by
  intro k _ _ _ _ _ _ s κ S ϖ' h
  let S' : SymData k s κ :=
    { S with ϖ := ϖ', unif := isUnif_of_near S.unif h, sym := isSymLevel_of_near S.cond S.unif h S.sym }
  refine ⟨S', rfl, rfl, rfl, rfl, rfl, fun τ ν => ?_⟩
  have hPhi : ∀ j c H, (S'.T (Fin τ)).Phi j c H = (S.T (Fin τ)).Phi j c H := fun j c H =>
    transport_iterPhi S.P S.μ S.tame j (near_typeFrame h _) (near_typeFrame h _)
  have hTop : (S'.T (Fin τ)).PhiTop = (S.T (Fin τ)).PhiTop :=
    transport_iterPhi S.P S.μ S.tame (s + 1) (near_refl _) (near_typeFrame h _)
  have hJ : ∀ j c H, ((S'.T (Fin τ)).lev j c H).J = ((S.T (Fin τ)).lev j c H).J := fun j c H =>
    (near_typeFrame h _).J_eq _
  have hB : ∀ j c (H : j + c = s + 1), stabLat ((S'.T (Fin τ)).bas j c H) = stabLat ((S.T (Fin τ)).bas j c H) := fun j c H =>
    (near_typeFrame h (stdOrd (Fin κ) (Fin τ) j c H)).stabLat_eq
  have hy : S'.y0 (Fin τ) - S.y0 (Fin τ) ∈ box (XIx (Fin κ) (Fin τ) (s + 1)) (1 : kˣ) := by
    intro i
    unfold SymData.y0
    rw [← Pi.single_sub, Pi.single_apply]
    split_ifs
    · simpa using inv_sub_inv_mem S.unif h
    · simp
  refine ⟨hPhi, fun j c H => ?_, fun x₀ => ?_, ?_⟩
  · unfold Chain.entry xi volNat
    rw [hPhi, hJ, hB]
    rfl
  · have := (oneCoupling k s κ S (Fin τ) (pattern_iter k s κ S (Fin τ))).2.1 x₀ _ hy
    rw [← this]
    unfold Chain.Psi
    rw [hPhi]
    rfl
  · unfold Chain.xiTop
    rw [hTop, (Submodule.Quotient.eq _).2 hy]

end GlobalTheory.SymChain
