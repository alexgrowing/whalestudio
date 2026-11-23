import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Formalism.LocalToGlobal.CharacterGerms.RowTieMemCFin
import Formalism.LocalToGlobal.CharacterGerms.RowTieFlagS

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.RF.MemS

open scoped BigOperators
open Classical
open UpperTheory.G2

variable {d : ℕ} [NeZero d] {hd : ZMod d}

section P0
open Formalism.IncomingBounds Formalism.L2.Pj

private abbrev IIs {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod d → T) (o : Orb) : Type := Σ t : ZMod d, Fin (r (tau o t))

private def subG {C : Type} [Field C] {T Orb : Type} (r : T → ℕ) (tau : Orb → ZMod d → T)
    (gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n) :
    MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  MvPolynomial.aeval fun x => ∑ col : Fin 2, MvPolynomial.C (gm x.2.1 x.2.2.2.1 col x.2.2.1) *
    MvPolynomial.X (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n)

variable (hd) in

private structure SelfConjugatePlaceSetting {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    {Orb : Type} [Fintype Orb] (tau : Orb → ZMod d → T) (gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C)
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod d → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N) : Prop where

  inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2
  hd2 : hd + hd = 0
  conj : ∀ o t, cc (tau o t) = tau o (t + hd)

  gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + hd) q s * gm o t q s' = if s = s' then 0 else 1

  hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd
  std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val

  alt : ∀ o, (X o).Alt
  hj : ∀ o, (X o).j' < (X o).n
  supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s

  mon : ∀ o, ∀ q ∈ L o, ∀ g e M, q.1 = GlobalTheory.mon g e M → ∃ s : ZMod d, ∀ b k, b ≠ s → e b k = 0
  wt : ∀ o s k, ((L o).map fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + hd) k).sum = gaC o s k
  tie : WtTieS r tau gaC a
  plinj : Function.Injective pl

variable (hd) in

private def IsotropicToStdSubstHarmonic : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod d → T) (gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod d → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N),
    SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n) (isX : T → Prop),
      subG r tau gm plc (blkProd X F N L pl) ∈ harmK r n C cc isX (fun _ => 1)

variable (hd) in

private def IsotropicToStdSubstLineInvariant : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod d → T) (gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod d → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N),
    SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowInv r n C (subG r tau gm plc (blkProd X F N L pl))

variable (hd) in

private def IsotropicToStdSubstLineDegree : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ) (cc : T → T) (a : T → ℕ → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod d → T) (gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (gaC : Orb → ZMod d → ℕ → ℕ) (N : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N),
    SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl → ∀ (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n),
      RowDeg r n C a (subG r tau gm plc (blkProd X F N L pl))

variable (d) in

private def IsotropicToStdSubstIntegral : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (T : Type) (r : T → ℕ)
    (Orb : Type) [Fintype Orb] (tau : Orb → ZMod d → T) (gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C)
    (J : Orb → Fin 2 → Type) [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o))
    (N : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N) (n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n)
    (O : Subring C), (∀ o t q s, gm o t q s ∈ O) → ∀ m, (subG r tau gm plc (blkProd X F N L pl)).coeff m ∈ O

section Mem

variable {C : Type} [Field C] {V : VF C} {T : Type} (r : T → ℕ) (cc : T → T) (isX : T → Prop)
  (a : T → ℕ → ℕ) {Orb : Type} [Fintype Orb] (tau : Orb → ZMod d → T) (gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C)
  (O : Subring C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

private def selfConjTuplesInLattice : Set (∀ o, MvPolynomial (Fin N × WV fun _ => IIs r tau o) C) :=
  {Po | subG r tau gm plc (∏ o, toAll o (Po o)) ∈ HaO r n C O cc isX a}

variable {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]

private theorem block_membership_self_conj_first (h1 : IsotropicToStdSubstHarmonic hd) (h2 : IsotropicToStdSubstLineInvariant hd) (h3 : IsotropicToStdSubstLineDegree hd) (h4 : IsotropicToStdSubstIntegral d) (hd2 : hd + hd = 0)
    (X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod d → ℕ → ℕ)
    (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2) (conj : ∀ o t, cc (tau o t) = tau o (t + hd))
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + hd) q s * gm o t q s' = if s = s' then 0 else 1)
    (gm_int : ∀ o t q s, gm o t q s ∈ O)
    (hty : ∀ o g (x : IIs r tau o), ((X o).G g).ty (Sum.inl x) = if g = 0 then x.1 else x.1 + hd)
    (std : ∀ o g t (c : Fin ((X o).rkF g t)), ((F o).en g t c).2.val = c.val)
    (alt : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (X o).rkF 0 s) (tie : WtTieS r tau gaC a) :
    PlaneBlockProductsMemFamily hd X N F (selfConjTuplesInLattice r cc isX a tau gm O plc) gaC := by
  intro L mon wt pl plinj
  have H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl := ⟨inj, hd2, conj, gm_hyp, hty, std, alt, hj, supp, mon, wt, tie, plinj⟩
  exact ⟨⟨h1 C V T r cc a Orb tau gm J X F gaC N L pl H n plc isX, h2 C V T r cc a Orb tau gm J X F gaC N L pl H n plc,
    h3 C V T r cc a Orb tau gm J X F gaC N L pl H n plc⟩, h4 C V T r Orb tau gm J X F N L pl n plc O gm_int⟩

end Mem

private theorem first_chern_integral : IsotropicToStdSubstIntegral d := by
  intro C _ V T r Orb _ tau gm J _ X F N L pl n plc O hgm m
  refine coeff_mem_of_OP (aeval_mem_OP _ (fun x => ?_) (blkProd_mem_ZP X F N L pl)) m
  refine Subring.sum_mem _ fun col _ => Subring.mul_mem _ ?_ ?_
  · exact ⟨MvPolynomial.C ⟨_, hgm x.2.1 x.2.2.2.1 col x.2.2.1⟩, by simp⟩
  · exact ⟨MvPolynomial.X (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n), by simp⟩

end P0

section P1
open Formalism.IncomingBounds Formalism.L2.Pj

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] (r : T → ℕ) (tau : Orb → ZMod d → T)
  (gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

private abbrev AA (r : T → ℕ) (tau : Orb → ZMod d → T) (N : ℕ) : Type := Fin N × Σ o, IIs r tau o

private def eW (N : ℕ) : (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ≃ AA r tau N × Fin 2 where
  toFun y := ((y.1, ⟨y.2.1, y.2.2.2⟩), y.2.2.1)
  invFun z := (z.1.1, ⟨z.1.2.1, ⟨z.2, z.1.2.2⟩⟩)
  left_inv := by rintro ⟨ρ, ⟨o, ⟨g, c⟩⟩⟩; rfl
  right_inv := by rintro ⟨⟨ρ, ⟨o, c⟩⟩, g⟩; rfl

private def lam (z : AA r tau N × Fin 2) : Letter T r n := ⟨tau z.1.2.1 z.1.2.2.1, z.1.2.2.2, plc (z.1.1, z.2)⟩

variable {r tau}

private theorem lam_inj (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2) :
    Function.Injective (lam r tau plc) := by
  rintro ⟨⟨ρ, o, t, c⟩, col⟩ ⟨⟨ρ', o', t', c'⟩, col'⟩ h
  simp only [lam] at h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  have h1' : (o, t) = (o', t') := inj h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1'
  have h2' := eq_of_heq h2
  obtain ⟨rfl, h3⟩ := Prod.mk.inj h2'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (plc.injective h3)
  rfl

variable (r tau)

private def Gm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 α.2.2.1 col g

variable (hd) in
private def Mm (α : AA r tau N) (col g : Fin 2) : C := gm α.2.1 (α.2.2.1 + hd) col (1 - g)

variable {r tau gm}

private theorem gram_matrix_mul_right (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + hd) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (g g' : Fin 2) : ∑ col, Mm hd r tau gm α col g' * Gm r tau gm α col g = if g' = g then 1 else 0 := by
  simp only [Mm, Gm]
  rw [gm_hyp]
  fin_cases g <;> fin_cases g' <;> simp

private theorem gram_matrix_mul_left (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + hd) q s * gm o t q s' = if s = s' then 0 else 1)
    (α : AA r tau N) (col col' : Fin 2) : ∑ g, Gm r tau gm α col' g * Mm hd r tau gm α col g = if col' = col then 1 else 0 := by
  have hAB : (Matrix.of fun g col => Mm hd r tau gm α col g) * (Matrix.of fun col g => Gm r tau gm α col g) = 1 := by
    ext g' g
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact gram_matrix_mul_right gm_hyp α g g'
  have hBA := mul_eq_one_comm.1 hAB
  have := congrFun (congrFun hBA col') col
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

variable (r tau gm)

variable (hd) in

private def coS (ℓ : Letter T r n) (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) : C :=
  ∑ col, if ℓ = lam r tau plc ((eW r tau N y).1, col) then Mm hd r tau gm (eW r tau N y).1 col (eW r tau N y).2 else 0

variable {r tau gm}

private theorem coS_lam (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2) (α α' : AA r tau N) (col g : Fin 2) :
    coS hd r tau gm plc (lam r tau plc (α, col)) ((eW r tau N).symm (α', g)) = if α = α' then Mm hd r tau gm α col g else 0 := by
  unfold coS
  rw [Equiv.apply_symm_apply]
  simp only [(lam_inj plc inj).eq_iff, Prod.mk.injEq]
  by_cases h : α = α'
  · subst h
    simp
  · simp [h]

private theorem sum_coS (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2) {M : Type} [AddCommMonoid M]
    (α : AA r tau N) (col : Fin 2) (Φ : C → (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) → M) (h0 : ∀ y, Φ 0 y = 0) :
    ∑ y, Φ (coS hd r tau gm plc (lam r tau plc (α, col)) y) y =
      ∑ g, Φ (Mm hd r tau gm α col g) ((eW r tau N).symm (α, g)) := by
  calc ∑ y, Φ (coS hd r tau gm plc (lam r tau plc (α, col)) y) y
      = ∑ z, Φ (coS hd r tau gm plc (lam r tau plc (α, col)) ((eW r tau N).symm z)) ((eW r tau N).symm z) :=
        (Equiv.sum_comp (eW r tau N).symm _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [coS_lam plc inj]
      rw [Finset.sum_eq_single α]
      · simp
      · intro b _ hb
        simp [Ne.symm hb, h0]
      · simp

private theorem subG_X (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) :
    subG r tau gm plc (MvPolynomial.X y) = ∑ col, MvPolynomial.C (Gm r tau gm (eW r tau N y).1 col (eW r tau N y).2) *
      MvPolynomial.X (lam r tau plc ((eW r tau N y).1, col)) := by
  unfold subG
  rw [MvPolynomial.aeval_X]
  rfl

private theorem back_subG (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + hd) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS hd r tau gm plc ℓ x) * MvPolynomial.X x) (subG r tau gm plc Q) = Q := by
  have key : ∀ y, MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS hd r tau gm plc ℓ x) * MvPolynomial.X x)
      (subG r tau gm plc (MvPolynomial.X y)) = MvPolynomial.X y := by
    intro y
    obtain ⟨⟨α, g⟩, rfl⟩ := (eW r tau N).symm.surjective y
    rw [subG_X, Equiv.apply_symm_apply, map_sum]
    simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
    have hs : ∀ col, ∑ x, MvPolynomial.C (coS hd r tau gm plc (lam r tau plc (α, col)) x) * MvPolynomial.X x
        = ∑ g', MvPolynomial.C (Mm hd r tau gm α col g') * MvPolynomial.X ((eW r tau N).symm (α, g')) :=
      fun col => sum_coS (hd := hd) (gm := gm) plc inj α col
        (fun c x => MvPolynomial.C c * MvPolynomial.X x) (fun x => by rw [map_zero, zero_mul])
    simp only [hs, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    have hg : ∀ g', ∑ col, MvPolynomial.C (Gm r tau gm α col g * Mm hd r tau gm α col g') *
        MvPolynomial.X ((eW r tau N).symm (α, g')) =
        MvPolynomial.C (if g' = g then (1:C) else 0) * MvPolynomial.X ((eW r tau N).symm (α, g')) := by
      intro g'
      rw [← Finset.sum_mul, ← map_sum, ← gram_matrix_mul_right gm_hyp α g g']
      simp only [mul_comm]
    simp only [hg]
    simp
  have hc : (MvPolynomial.aeval (fun ℓ => ∑ x, MvPolynomial.C (coS hd r tau gm plc ℓ x) * MvPolynomial.X x)).comp
      (subG r tau gm plc) = AlgHom.id C _ := by
    apply MvPolynomial.algHom_ext
    intro y
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    exact key y
  have := AlgHom.congr_fun hc Q
  rw [AlgHom.comp_apply, AlgHom.id_apply] at this
  exact this

end P1

section P2
open Formalism.IncomingBounds Formalism.L2.Pj

section Gen

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod d → T}
  {gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

private theorem mem_vars_subG {Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ℓ ∈ (subG r tau gm plc Q).vars) : ∃ z, ℓ = lam r tau plc z := by
  unfold subG at h
  rw [MvPolynomial.aeval_eq_bind₁] at h
  obtain ⟨y, _, hy⟩ := MvPolynomial.mem_vars_bind₁ _ _ h
  have h1 := MvPolynomial.vars_sum_subset _ _ hy
  rw [Finset.mem_biUnion] at h1
  obtain ⟨col, _, h2⟩ := h1
  have h3 := MvPolynomial.vars_mul _ _ h2
  rw [MvPolynomial.vars_C, Finset.empty_union, MvPolynomial.vars_X, Finset.mem_singleton] at h3
  exact ⟨((eW r tau N y).1, col), h3⟩

private theorem coS_off (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2) (α : AA r tau N) (col : Fin 2)
    (y : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) (h : y.1 ≠ α.1) :
    coS hd r tau gm plc (lam r tau plc (α, col)) y = 0 := by
  unfold coS
  apply Finset.sum_eq_zero
  intro col' _
  rw [if_neg]
  intro hl
  have h1 := congrArg (fun z => z.1.1) (lam_inj plc inj hl)
  exact h h1.symm

private theorem isImgS_subG {dd : ℕ} (X : ∀ o, RawChart C d (fun _ => IIs r tau o) (Fin 2 × Fin dd))
    (uv : Letter T r n → Fin dd → C) (e : ∀ o, IIs r tau o → Fin dd → C)
    (hu : ∀ o g (c : IIs r tau o) x, (X o).u g c x = gm o c.1 x.1 g * e o c x.2)
    (huv : ∀ o (c : IIs r tau o) b, uv ⟨tau o c.1, c.2, b⟩ = e o c)
    (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + hd) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    IsImgS X plc (fun ℓ : Letter T r n => ℓ.2.2) uv (subG r tau gm plc Q) Q := by
  refine ⟨coS hd r tau gm plc, ?_, (back_subG plc inj gm_hyp Q).symm⟩
  intro ℓ hℓ
  obtain ⟨⟨⟨ρ, o, t, c⟩, col⟩, rfl⟩ := mem_vars_subG plc hℓ
  refine ⟨ρ, col, rfl, ?_, ?_⟩
  · intro ρ' w hρ
    exact coS_off plc inj _ col (ρ', w) hρ
  · have h1 : (∑ w, coS hd r tau gm plc (lam r tau plc ((ρ, ⟨o, ⟨t, c⟩⟩), col)) (ρ, w) • (X w.1).u w.2.1 w.2.2)
        = ∑ y : Fin N × (WVO fun o (_ : Fin 2) => IIs r tau o),
            coS hd r tau gm plc (lam r tau plc ((ρ, ⟨o, ⟨t, c⟩⟩), col)) y • (X y.2.1).u y.2.2.1 y.2.2.2 := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single ρ]
      · intro ρ' _ hρ'
        apply Finset.sum_eq_zero
        intro w _
        rw [coS_off plc inj (ρ, ⟨o, ⟨t, c⟩⟩) col (ρ', w) hρ', zero_smul]
      · simp
    rw [h1, sum_coS plc inj (ρ, ⟨o, ⟨t, c⟩⟩) col (fun c y => c • (X y.2.1).u y.2.2.1 y.2.2.2) (fun y => zero_smul _ _)]
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change _ = ∑ g, Mm hd r tau gm (ρ, ⟨o, ⟨t, c⟩⟩) col g * (X o).u g ⟨t, c⟩ x
    have hR : ∑ g, Mm hd r tau gm (ρ, ⟨o, ⟨t, c⟩⟩) col g * (X o).u g ⟨t, c⟩ x =
        (∑ g, Gm r tau gm (ρ, ⟨o, ⟨t, c⟩⟩) x.1 g * Mm hd r tau gm (ρ, ⟨o, ⟨t, c⟩⟩) col g) * e o ⟨t, c⟩ x.2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      rw [hu]
      simp only [Gm]
      ring
    rw [hR, gram_matrix_mul_left gm_hyp]
    have hL : uv (lam r tau plc ((ρ, ⟨o, ⟨t, c⟩⟩), col)) = e o ⟨t, c⟩ := huv o ⟨t, c⟩ _
    rw [hL]
    split_ifs <;> simp

end Gen

end P2

section P3
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Fam

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod d → T} {gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod d → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N} {n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

variable (hd) in

private def trueT (g : Fin 2) (s : ZMod d) : ZMod d := if g = 0 then s else s + hd

private theorem SelfConjugatePlaceSetting.en_fst (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod d)
    (q : Fin ((X o).rkF g s)) : ((F o).en g s q).1 = trueT hd g s := by
  have h := (F o).en_ty g s q
  rw [H.hty] at h
  unfold trueT
  split_ifs at h ⊢ with hg
  · exact h
  · calc ((F o).en g s q).1 = ((F o).en g s q).1 + hd + hd := by rw [add_assoc, H.hd2, add_zero]
      _ = s + hd := by rw [h]

variable (r tau gm) in

private def PsiS (o : Orb) {M : ℕ} (col : Fin M → Fin N) :
    MvPolynomial (Fin M × WV fun _ => IIs r tau o) C →ₐ[C] MvPolynomial (Letter T r n) C :=
  (subG r tau gm plc).comp (rename fun x : Fin M × WV fun _ => IIs r tau o =>
    ((col x.1, (⟨o, x.2⟩ : WVO fun o (_ : Fin 2) => IIs r tau o))))

private theorem SelfConjugatePlaceSetting.inv_minor (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {M : ℕ}
    (col : Fin M → Fin N) (k : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k)) := by
  have hX : ∀ x : Fin M × Fin ((X o).rkF g s),
      ((PsiS r tau gm plc o col).comp (rename ((F o).letter g s))) (MvPolynomial.X x) =
        ∑ q, MvPolynomial.C (gm o (trueT hd g s) q g) *
          MvPolynomial.X (lam r tau plc ((col x.1, ⟨o, (F o).en g s x.2⟩), q)) := by
    intro x
    rw [AlgHom.comp_apply, rename_X]
    unfold PsiS
    rw [AlgHom.comp_apply, rename_X, subG_X]
    apply Finset.sum_congr rfl
    intro q _
    have e : gm o ((F o).en g s x.2).1 = gm o (trueT hd g s) := by rw [H.en_fst]
    dsimp only [Gm, Flag.letter, eW, Equiv.coe_fn_mk]
    rw [e]
  have hk : ∀ (ρ : Fin M) (c : Fin ((X o).rkF g s)) (q : Fin 2),
      keyL (lam r tau plc ((col (ρ, c).1, ⟨o, (F o).en g s (ρ, c).2⟩), q)) =
        (tau o (trueT hd g s), (c : ℕ), plc (col ρ, q)) := by
    intro ρ c q
    simp only [keyL, lam]
    rw [H.std, H.en_fst]
  exact rowShift_minor_lin ((PsiS r tau gm plc o col).comp (rename ((F o).letter g s))) (tau o (trueT hd g s))
    (fun ρ q => gm o (trueT hd g s) q g) (fun x q => lam r tau plc ((col x.1, ⟨o, (F o).en g s x.2⟩), q))
    (fun ρ q => plc (col ρ, q)) hX hk σ i i' hi t k

private theorem SelfConjugatePlaceSetting.inv_mon (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {M : ℕ}
    (col : Fin M → Fin N) (e : ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (rename ((F o).letter g s) (monP C M ((X o).rkF g s) e))) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (monP C M ((X o).rkF g s) e)) := by
  unfold monP
  simp only [map_prod, map_pow]
  exact Finset.prod_congr rfl fun k _ => by rw [H.inv_minor plc o g s col k σ i i' hi t]

private theorem SelfConjugatePlaceSetting.inv_bi (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o : Orb) (g g' : Fin 2) (s s' : ZMod d) {M : ℕ}
    (col : Fin M → Fin N) (k e1 e2 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2)) =
      PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1 *
        rename ((F o).letter g' s') (minorK C M ((X o).rkF g' s') k) ^ e2) := by
  simp only [map_mul, map_pow]
  rw [H.inv_minor plc o g s col k σ i i' hi t, H.inv_minor plc o g' s' col k σ i i' hi t]

private theorem SelfConjugatePlaceSetting.inv_ch (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod d) {M : ℕ}
    (col : Fin M → Fin N) (k e1 : ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1)) =
      PsiS r tau gm plc o col (rename ((F o).letter g s) (minorK C M ((X o).rkF g s) k) ^ e1) := by
  simp only [map_pow]
  rw [H.inv_minor plc o g s col k σ i i' hi t]

private theorem SelfConjugatePlaceSetting.inv_monAll (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) {M : ℕ}
    (col : Fin M → Fin N) (e : ZMod d → ℕ → ℕ) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col
      (∏ s : ZMod d, rename ((F o).letter g s) (monP C M ((X o).rkF g s) (e s)))) =
      PsiS r tau gm plc o col (∏ s : ZMod d, rename ((F o).letter g s) (monP C M ((X o).rkF g s) (e s))) := by
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro s _
  exact H.inv_mon plc o g s col (e s) σ i i' hi t

private theorem SelfConjugatePlaceSetting.inv_poly (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o : Orb) (b : GlobalTheory d) (col : Fin (b.what₂ (X o).n) → Fin N)
    (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) :
    rowShift r n C σ i i' t (PsiS r tau gm plc o col (b.poly (X o) (F o))) = PsiS r tau gm plc o col (b.poly (X o) (F o)) := by
  cases b with
  | bi g s e y => exact H.inv_bi plc o g (1 - g) s (s + (e : ZMod d)) col (X o).n _ _ σ i i' hi t
  | ch g s u => exact H.inv_ch plc o g s col (X o).n u σ i i' hi t
  | mon g e M => exact H.inv_monAll plc o g col e σ i i' hi t

private theorem subG_blkProd :
    subG r tau gm plc (blkProd X F N L pl) =
      ∏ o, ∏ i, PsiS r tau gm plc o (fun ρ => plAt N pl o ⟨i, ρ⟩) ((blkAt L o i).poly (X o) (F o)) := by
  unfold blkProd prodAll toAll PsiS
  simp only [map_prod, AlgHom.comp_apply, MvPolynomial.rename_rename]
  rfl

end Fam

private theorem isotropic_to_standard_substitution_invariant : IsotropicToStdSubstLineInvariant hd := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc σ i i' hi t
  rw [subG_blkProd, map_prod]
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => H.inv_poly plc o _ _ σ i i' hi t

end P3

section P4
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

private theorem trueT_iff (hd2 : hd + hd = 0) (g : Fin 2) (t' s : ZMod d) :
    ((if g = 0 then t' else t' + hd) = s) ↔ t' = trueT hd g s := by
  unfold trueT
  split_ifs
  · rfl
  · constructor
    · rintro rfl
      rw [add_assoc, hd2, add_zero]
    · rintro rfl
      rw [add_assoc, hd2, add_zero]

private theorem trueT_one (hd2 : hd + hd = 0) (t : ZMod d) : trueT hd 1 (t + hd) = t := by
  unfold trueT
  rw [if_neg (by decide), add_assoc, hd2, add_zero]

private theorem SelfConjugatePlaceSetting.rkF_eq {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
    {Orb : Type} [Fintype Orb] {tau : Orb → ZMod d → T} {gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C}
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
    {gaC : Orb → ZMod d → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
    (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o : Orb) (g : Fin 2) (s : ZMod d) :
    (X o).rkF g s = r (tau o (trueT hd g s)) := by
  unfold RowData.rkF
  have e : (Finset.univ.filter fun c : IIs r tau o => ((X o).G g).ty (Sum.inl c) = s) =
      Finset.univ.map (Function.Embedding.sigmaMk (β := fun t => Fin (r (tau o t))) (trueT hd g s)) := by
    ext ⟨t', c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.sigmaMk_apply, H.hty]
    rw [trueT_iff H.hd2]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem subG_isWeightedHomogeneous {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod d → T}
    {gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n) (σ : T) (i : Fin (r σ))
    (P : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) (D : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous
      (fun x : Fin N × WVO (fun o (_ : Fin 2) => IIs r tau o) =>
        if (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ : Σ τ, Fin (r τ)) = ⟨σ, i⟩ then 1 else 0) P D) :
    MvPolynomial.IsWeightedHomogeneous (Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.wLet r n σ i) (subG r tau gm plc P) D := by
  unfold subG
  refine Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.isWH_aeval _ ?_ hP
  intro x
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro col _
  have h := (MvPolynomial.isWeightedHomogeneous_C (Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.wLet r n σ i)
    (gm x.2.1 x.2.2.2.1 col x.2.2.1)).mul
    (MvPolynomial.isWeightedHomogeneous_X C (Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.wLet r n σ i)
      (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2, plc (x.1, col)⟩ : Letter T r n))
  rw [zero_add, Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.wLet_mk] at h
  exact h

private theorem eq_and_eq_of_tau_eq_of_injective {T Orb : Type} {tau : Orb → ZMod d → T}
    (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2) {o o' : Orb} {t t' : ZMod d}
    (h : tau o t = tau o' t') : o = o' ∧ t = t' :=
  Prod.mk.inj (@inj (o, t) (o', t') h)

private theorem first_chern_degree_lemma_4 {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
    {Orb : Type} [Fintype Orb] {tau : Orb → ZMod d → T} {gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C}
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
    {gaC : Orb → ZMod d → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
    (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o0 : Orb) (s0 : ZMod d) (i : Fin (r (tau o0 s0))) :
    MvPolynomial.IsWeightedHomogeneous
      (fun x => Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.wRowG (X o0) (fun _ y => y.2.val) 0 s0 i x +
        Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.wRowG (X o0) (fun _ y => y.2.val) 1 (s0 + hd) i x)
      (prodAll (plAt N pl o0) fun j => (blkAt L o0 j).poly (X o0) (F o0))
      (∑ k ∈ Finset.Icc (i.val + 1) (r (tau o0 s0)), gaC o0 s0 k) := by
  have e0 : (X o0).rkF 0 s0 = r (tau o0 s0) := by rw [H.rkF_eq o0 0 s0]; simp [trueT]
  have e1 : (X o0).rkF 1 (s0 + hd) = r (tau o0 s0) := by rw [H.rkF_eq o0 1 (s0 + hd), trueT_one H.hd2]
  have hsum : (∑ k ∈ Finset.Icc (i.val + 1) (r (tau o0 s0)), gaC o0 s0 k) =
      ∑ j : Fin (L o0).length,
        ((∑ k ∈ Finset.Icc (i.val + 1) ((X o0).rkF 0 s0), (blkAt L o0 j).wt (X o0) 0 s0 k) +
          ∑ k ∈ Finset.Icc (i.val + 1) ((X o0).rkF 1 (s0 + hd)), (blkAt L o0 j).wt (X o0) 1 (s0 + hd) k) := by
    rw [e0, e1]
    calc (∑ k ∈ Finset.Icc (i.val + 1) (r (tau o0 s0)), gaC o0 s0 k)
        = ∑ k ∈ Finset.Icc (i.val + 1) (r (tau o0 s0)),
            ((L o0).map fun q => q.1.wt (X o0) 0 s0 k + q.1.wt (X o0) 1 (s0 + hd) k).sum := by
          apply Finset.sum_congr rfl
          intro k _
          rw [H.wt o0 s0 k]
      _ = ∑ k ∈ Finset.Icc (i.val + 1) (r (tau o0 s0)), ∑ j : Fin (L o0).length,
            ((blkAt L o0 j).wt (X o0) 0 s0 k + (blkAt L o0 j).wt (X o0) 1 (s0 + hd) k) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← Fin.sum_univ_fun_getElem]
          rfl
      _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_add_distrib]
  rw [hsum]
  unfold prodAll
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro j _
  apply Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_rename
  refine Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_congr (fun x => rfl) ?_
  exact Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.isWH_add
    (Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.blockPoly_isWeightedHomogeneous' (X o0) (F o0) (fun _ y => y.2.val) (fun g t c => H.std o0 g t c) _ 0 s0 i)
    (Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.blockPoly_isWeightedHomogeneous' (X o0) (F o0) (fun _ y => y.2.val) (fun g t c => H.std o0 g t c) _ 1 (s0 + hd) i)

private theorem first_chern_degree_lemma_3 {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
    {Orb : Type} [Fintype Orb] {tau : Orb → ZMod d → T} {gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C}
    {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
    {gaC : Orb → ZMod d → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}
    (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (σ : T) (i : Fin (r σ)) :
    MvPolynomial.IsWeightedHomogeneous
      (fun x : Fin N × WVO (fun o (_ : Fin 2) => IIs r tau o) =>
        if (⟨tau x.2.1 x.2.2.2.1, x.2.2.2.2⟩ : Σ τ, Fin (r τ)) = ⟨σ, i⟩ then 1 else 0)
      (blkProd X F N L pl) (a σ i) := by
  by_cases hσ : ∃ o0 s0, tau o0 s0 = σ
  · obtain ⟨o0, s0, rfl⟩ := hσ
    rw [H.tie.1 o0 s0 i i.isLt]
    unfold blkProd
    have hsum : (∑ k ∈ Finset.Icc (i.val + 1) (r (tau o0 s0)), gaC o0 s0 k) =
        ∑ o, if o = o0 then ∑ k ∈ Finset.Icc (i.val + 1) (r (tau o0 s0)), gaC o0 s0 k else 0 := by
      rw [Finset.sum_ite_eq']
      simp
    rw [hsum]
    apply MvPolynomial.IsWeightedHomogeneous.prod
    intro o _
    unfold toAll
    apply Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_rename
    split_ifs with ho
    · subst ho
      refine Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_congr ?_ (first_chern_degree_lemma_4 H o s0 i)
      rintro ⟨ρ, g, t, c⟩
      have key : ((⟨tau o t, c⟩ : Σ τ, Fin (r τ)) = ⟨tau o s0, i⟩) ↔ (t = s0 ∧ c.val = i.val) := by
        constructor
        · intro hx
          obtain ⟨-, rfl⟩ := eq_and_eq_of_tau_eq_of_injective H.inj (Sigma.mk.inj_iff.mp hx).1
          exact ⟨rfl, congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.mp hx).2)⟩
        · rintro ⟨rfl, hc⟩
          rw [Fin.ext hc]
      simp only [Function.comp, Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.wRowG, H.hty]
      fin_cases g
      · simp [key]
      · simp [key]
    · apply Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_of_zero
      intro x
      simp only [Function.comp]
      rw [if_neg]
      intro hx
      exact ho (eq_and_eq_of_tau_eq_of_injective H.inj (Sigma.mk.inj_iff.mp hx).1).1
  · have h0 : a σ i = 0 := H.tie.2 σ (fun o s h => hσ ⟨o, s, h⟩) i i.isLt
    rw [h0]
    apply Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_of_zero
    intro x
    rw [if_neg]
    intro hx
    exact hσ ⟨_, _, (Sigma.mk.inj_iff.mp hx).1⟩

open WeightHomogeneousMinors WeightHomogeneousLetters in
private theorem isotropic_to_std_subst_degree : IsotropicToStdSubstLineDegree hd := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc
  intro m hm σ i
  have hW : MvPolynomial.IsWeightedHomogeneous (Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.wLet r n σ i)
      (subG r tau gm plc (blkProd X F N L pl)) (a σ i) := subG_isWeightedHomogeneous plc σ i _ _ (first_chern_degree_lemma_3 H σ i)
  have h2 := hW (MvPolynomial.mem_support_iff.mp hm)
  rwa [Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.weight_wLet] at h2

end P4

section P5
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Chain

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod d → T}
  {gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

private theorem pderiv_subG_off {p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C} {ℓ : Letter T r n}
    (h : ∀ z, ℓ ≠ lam r tau plc z) : pderiv ℓ (subG r tau gm plc p) = 0 :=
  pderiv_eq_zero_of_notMem_vars fun hv => by
    obtain ⟨z, hz⟩ := mem_vars_subG plc hv
    exact h z hz

private theorem pderiv_subG_lam (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2) (α0 : AA r tau N) (col0 : Fin 2)
    (p : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) :
    pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc p) =
      ∑ g, MvPolynomial.C (Gm r tau gm α0 col0 g) * subG r tau gm plc (pderiv ((eW r tau N).symm (α0, g)) p) := by
  rw [chain_aeval]
  have hX : ∀ y, MvPolynomial.pderiv (lam r tau plc (α0, col0)) (subG r tau gm plc (MvPolynomial.X y)) =
      if (eW r tau N y).1 = α0 then MvPolynomial.C (Gm r tau gm α0 col0 (eW r tau N y).2) else 0 := by
    intro y
    rw [subG_X, map_sum]
    simp only [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X, Pi.single_apply, (lam_inj plc inj).eq_iff,
      Prod.mk.injEq, mul_ite, mul_one, mul_zero]
    by_cases hy : (eW r tau N y).1 = α0
    · rw [if_pos hy]
      subst hy
      simp
    · rw [if_neg hy]
      simp [hy]
  simp only [hX]
  calc ∑ y, subG r tau gm plc (MvPolynomial.pderiv y p) *
        (if (eW r tau N y).1 = α0 then MvPolynomial.C (Gm r tau gm α0 col0 (eW r tau N y).2) else 0)
      = ∑ z, subG r tau gm plc (MvPolynomial.pderiv ((eW r tau N).symm z) p) *
        (if (eW r tau N ((eW r tau N).symm z)).1 = α0 then
          MvPolynomial.C (Gm r tau gm α0 col0 (eW r tau N ((eW r tau N).symm z)).2) else 0) :=
        (Equiv.sum_comp (eW r tau N).symm _).symm
    _ = _ := by
      simp only [Equiv.apply_symm_apply]
      rw [Fintype.sum_prod_type, Finset.sum_eq_single α0]
      · simp [mul_comm]
      · intro b _ hb
        simp [hb]
      · simp

end Chain

end P5

section P6
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

section Plane

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod d → T}
  {gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

private theorem lap_plane (inj : Function.Injective fun x : Orb × ZMod d => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + hd) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) (o : Orb) (t : ZMod d)
    (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + hd))))
    (hno : ∀ ρ g1 g2, g1 ≠ g2 → (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ Q.vars →
      (eW r tau N).symm ((ρ, ⟨o, ⟨t + hd, a2⟩⟩), g2) ∈ Q.vars → False) :
    ∑ b, pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + hd), a2, b⟩ : Letter T r n)
      (subG r tau gm plc Q)) = 0 := by
  have hD : ∀ (ρ : Fin N) (g g' : Fin 2), g ≠ g' →
      MvPolynomial.pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g'))
        (MvPolynomial.pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + hd, a2⟩⟩), g)) Q) = 0 := by
    intro ρ g g' hne
    by_cases h1 : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g') ∈ Q.vars
    · have h2 : (eW r tau N).symm ((ρ, ⟨o, ⟨t + hd, a2⟩⟩), g) ∉ Q.vars :=
        fun h2 => hno ρ g' g (Ne.symm hne) h1 h2
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars h2, map_zero]
    · rw [pderiv_comm', MvPolynomial.pderiv_eq_zero_of_notMem_vars h1, map_zero]
  have hF : ∀ b : Fin n, (∀ z, b ≠ plc z) →
      MvPolynomial.pderiv (⟨tau o t, a1, b⟩ : Letter T r n)
        (MvPolynomial.pderiv (⟨tau o (t + hd), a2, b⟩ : Letter T r n) (subG r tau gm plc Q)) = 0 := by
    intro b hb
    rw [pderiv_subG_off (r := r) (tau := tau) (gm := gm) plc (p := Q) (ℓ := ⟨tau o (t + hd), a2, b⟩)
      (fun z h => hb (z.1.1, z.2) (congrArg (fun ℓ : Letter T r n => ℓ.2.2) h)), map_zero]
  have hsub : (∑ b ∈ Finset.univ.map plc, MvPolynomial.pderiv (⟨tau o t, a1, b⟩ : Letter T r n)
      (MvPolynomial.pderiv (⟨tau o (t + hd), a2, b⟩ : Letter T r n) (subG r tau gm plc Q))) =
      ∑ b, MvPolynomial.pderiv (⟨tau o t, a1, b⟩ : Letter T r n)
        (MvPolynomial.pderiv (⟨tau o (t + hd), a2, b⟩ : Letter T r n) (subG r tau gm plc Q)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b _ hb
    apply hF b
    intro z hz
    apply hb
    rw [hz]
    exact Finset.mem_map_of_mem plc (Finset.mem_univ z)
  have hcalc : ∀ (ρ : Fin N) (col : Fin 2),
      MvPolynomial.pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n)
        (MvPolynomial.pderiv (⟨tau o (t + hd), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q)) =
      ∑ g, ∑ g', MvPolynomial.C (gm o (t + hd) col g * gm o t col g') *
        subG r tau gm plc (MvPolynomial.pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g'))
          (MvPolynomial.pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + hd, a2⟩⟩), g)) Q)) := by
    intro ρ col
    have e1 : (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n) = lam r tau plc ((ρ, ⟨o, ⟨t, a1⟩⟩), col) := rfl
    have e2 : (⟨tau o (t + hd), a2, plc (ρ, col)⟩ : Letter T r n) =
        lam r tau plc ((ρ, ⟨o, ⟨t + hd, a2⟩⟩), col) := rfl
    rw [e1, e2, pderiv_subG_lam plc inj, map_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [MvPolynomial.pderiv_C_mul, pderiv_subG_lam plc inj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g' _
    simp only [Gm, map_mul]
    ring
  rw [← hsub, Finset.sum_map, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro ρ _
  rw [Finset.sum_congr rfl (fun col _ => hcalc ρ col), Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro g _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro g' _
  rw [← Finset.sum_mul, ← map_sum, gm_hyp]
  by_cases hgg : g = g'
  · simp [hgg]
  · rw [hD ρ g g' hgg, map_zero, mul_zero]

end Plane

section Fam

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod d → T} {gm : Orb → ZMod d → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod d → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}

private theorem zmod_two_add_one_add_one_eq (hd2 : hd + hd = 0) (t : ZMod d) : t + hd + hd = t := by rw [add_assoc, hd2, add_zero]

private theorem SelfConjugatePlaceSetting.rowsOK (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (o : Orb) :
    ∃ kind : Fin N → Knd d, RowsOK (X o).G (X o).Alt
      (prodAll (plAt N pl o) fun i => (blkAt L o i).poly (X o) (F o)) kind := by
  have hw : ∀ i : Fin (L o).length, ∀ (g : Fin 2) (s : ZMod d) (k : ℕ),
      (blkAt L o i).wt (X o) g s k ≠ 0 → k ≤ (X o).rkF g s := by
    intro i g s k hne
    have hq : (L o).get i ∈ L o := List.get_mem _ _
    obtain rfl | rfl : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    · have hle := le_sum_map (L o) (fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + hd) k) hq
      rw [H.wt] at hle
      have hg : gaC o s k ≠ 0 := by
        intro h0
        rw [h0] at hle
        exact hne (by simp only [blkAt]; omega)
      exact (H.supp o s k hg).2
    · have hle := le_sum_map (L o) (fun q => q.1.wt (X o) 0 (s + hd) k + q.1.wt (X o) 1 (s + hd + hd) k) hq
      rw [H.wt, zmod_two_add_one_add_one_eq H.hd2] at hle
      have hg : gaC o (s + hd) k ≠ 0 := by
        intro h0
        rw [h0] at hle
        exact hne (by simp only [blkAt]; omega)
      have h3 := (H.supp o (s + hd) k hg).2
      rw [H.rkF_eq] at h3 ⊢
      simpa [trueT] using h3
  choose kind hk using fun i => exists_rowsOK (X o) (F o) (Or.inl (H.alt o)) (H.hj o) (blkAt L o i) (hw i)
  exact ⟨_, rowsOK_prodAll (X o).G (X o).Alt (plAt_inj N H.plinj o) _ kind hk⟩

private theorem lab_eq (hd2 : hd + hd = 0) (g1 g2 : Fin 2) (h : g1 ≠ g2) (t : ZMod d) :
    (if g1 = 0 then t else t + hd) = (if g2 = 0 then t + hd else t + hd + hd) := by
  fin_cases g1 <;> fin_cases g2
  · exact absurd rfl h
  · simp [add_assoc, hd2]
  · simp
  · exact absurd rfl h

private theorem SelfConjugatePlaceSetting.no_conj (H : SelfConjugatePlaceSetting hd r cc a tau gm X F gaC N L pl) (ρ : Fin N) (o : Orb) (g1 g2 : Fin 2) (hne : g1 ≠ g2)
    (t : ZMod d) (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + hd))))
    (hx : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ (blkProd X F N L pl).vars)
    (hx' : (eW r tau N).symm ((ρ, ⟨o, ⟨t + hd, a2⟩⟩), g2) ∈ (blkProd X F N L pl).vars) : False := by
  obtain ⟨kind, hk⟩ := H.rowsOK o
  have hx2 : (ρ, (⟨o, ⟨g1, ⟨t, a1⟩⟩⟩ : WVO fun o (_ : Fin 2) => IIs r tau o)) ∈ (blkProd X F N L pl).vars := hx
  have hx2' : (ρ, (⟨o, ⟨g2, ⟨t + hd, a2⟩⟩⟩ : WVO fun o (_ : Fin 2) => IIs r tau o)) ∈ (blkProd X F N L pl).vars := hx'
  have h1 := mem_vars_blkProdG hx2
  have h2 := mem_vars_blkProdG hx2'
  refine no_conj_of_rowsOK hk h1 h2 hne ?_
  simp only [tyW, H.hty]
  exact lab_eq H.hd2 g1 g2 hne t

end Fam

private theorem isotropic_to_std_subst_harmonic : IsotropicToStdSubstHarmonic hd := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc isX
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ _ a1 a2
  rw [lap_one_apply]
  by_cases hrange : ∃ o t, tau o t = τ
  · obtain ⟨o, t, rfl⟩ := hrange
    generalize hcc : cc (tau o t) = σ' at a2 ⊢
    obtain rfl : σ' = tau o (t + hd) := hcc.symm.trans (H.conj o t)
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact lap_plane plc H.inj H.gm_hyp _ o t a1 a2
      (fun ρ g1 g2 hne h1 h2 => H.no_conj ρ o g1 g2 hne t a1 a2 h1 h2)
  · push_neg at hrange
    apply Finset.sum_eq_zero
    intro b _
    apply Finset.sum_eq_zero
    intro b' _
    rw [pderiv_comm', pderiv_subG_off (r := r) (tau := tau) (gm := gm) plc (p := blkProd X F N L pl)
      (ℓ := ⟨τ, a1, b⟩) (fun z h => hrange z.1.2.1 z.1.2.2.1 (congrArg Sigma.fst h).symm), map_zero, smul_zero]

end P6

section P7
open Formalism.IncomingBounds Formalism.L2.Pj

private theorem blkMemS_mono {C : Type} [Field C] {V : VF C} {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
    [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)] {X : ∀ o, RowData C V d (I o) (J o)} {n : ℕ} {F : ∀ o, Flag (X o)}
    {FF FF' : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {gaC : Orb → ZMod d → ℕ → ℕ}
    (h : PlaneBlockProductsMemFamily hd X n F FF gaC) (hs : FF ⊆ FF') : PlaneBlockProductsMemFamily hd X n F FF' gaC :=
  fun L h1 h2 pl hpl => hs (h L h1 h2 pl hpl)

section Chart

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb]

private theorem gm_mem {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (o : Orb) (t : ZMod d) (q s : Fin 2) :
    lab.gm o t q s ∈ V.RR := by
  obtain ⟨M, hM⟩ := ha.gm_lim o 0
  have h1 : V.Ge 0 (lab.gm o t q s - emA3 io ι (lab.tau o t) (M q s)) := by simpa using hM t q s
  have h2 := h1.add (hg.em_int o t (M q s))
  rwa [sub_add_cancel] at h2

private theorem first_family_subset_image {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ}
    (plc : Fin N × Fin 2 ↪ Fin n) :
    selfConjTuplesInLattice Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc ⊆
      imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc := by
  intro Po hPo
  refine ⟨_, hPo, ?_⟩
  exact isImgS_subG plc (fun o => Y.rawSelf (selfOfLab ha hg o)) ((chartLetterSystem C3 V ι a).uv n) (fun o => selfLieBasisVector C3 ι lab o)
    (fun o g c x => rfl) (fun o c b => rfl) ha.inj ha.gm_hyp _

private theorem block_membership_self_conj_charts
    {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d}
    (ha : LabSArith V io ι lab) (hg : LabSGeo C3 ι Y lab) (Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)
    (F : ∀ o, Flag (rdS Y (selfOfLab ha hg) Hy o)) (gaC : Orb → ZMod d → ℕ → ℕ)
    (std : ∀ o g t (q : Fin ((rdS Y (selfOfLab ha hg) Hy o).rkF g t)), ((F o).en g t q).2.val = q.val)
    (alt : ∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt) (hj : lab.j' < lab.n)
    (supp : ∀ o s k, gaC o s k ≠ 0 → 1 ≤ k ∧ k ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s)
    (tie : WtTieS Dw.mult lab.tau gaC fun τ i => a (τ, i)) :
    PlaneBlockProductsMemFamily lab.hd (fun o => rdS Y (selfOfLab ha hg) Hy o) N F (imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc) gaC :=
  blkMemS_mono (block_membership_self_conj_first Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) lab.tau lab.gm V.RR plc isotropic_to_std_subst_harmonic isotropic_to_standard_substitution_invariant isotropic_to_std_subst_degree first_chern_integral ha.hd_two
    (fun o => rdS Y (selfOfLab ha hg) Hy o) F gaC ha.inj ha.conj
    ha.gm_hyp (gm_mem ha hg)
    (fun _ _ _ => rfl)
    std alt (fun _ => hj) supp tie) (first_family_subset_image ha hg a plc)

end Chart

end P7

end Formalism.L2.FormalSeriesBounds.RF.MemS

end

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF UpperTheory.G2 NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem UpperTheory.blkMemS_selfConjugate_places_of_CMDatum :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
    (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C)
    (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Formalism.L2.FormalSeriesBounds.LabS E C Orb d) (ha : LabSArith V io ι lab),
    ∀ (hg : LabSGeo C3 ι Y lab) (Hy : ∀ o, (Y.rawSelf (selfOfLab ha hg o)).Hyps V)
    (a : (E →+* ℂ) × ℕ → ℕ) (N n : ℕ) (plc : Fin N × Fin 2 ↪ Fin n)
    (F : ∀ o, RF.Flag (rdS Y (selfOfLab ha hg) Hy o)) (ga : Orb → ZMod d → ℕ → ℕ),
    (∀ o g t (q : Fin ((rdS Y (selfOfLab ha hg) Hy o).rkF g t)), ((F o).en g t q).2.val = q.val) →
    (∀ o, (rdS Y (selfOfLab ha hg) Hy o).Alt) → lab.j' < lab.n →
    (∀ o s k', ga o s k' ≠ 0 → 1 ≤ k' ∧ k' ≤ (rdS Y (selfOfLab ha hg) Hy o).rkF 0 s) →
    WtTieS Dw.mult lab.tau ga (fun τ i => a (τ, i)) →
    PlaneBlockProductsMemFamily lab.hd (fun o => rdS Y (selfOfLab ha hg) Hy o) N F (RF.imgFamS Y (selfOfLab ha hg) (chartLetterSystem C3 V ι a) n plc) ga := by
  intro E _ _ _ H Dw lv Xo c _ _ T io y C3 C _ _ V ι _ k Y _ Orb _ d _ lab ha hg Hy a N n plc F ga std alt hj supp tie
  exact Formalism.L2.FormalSeriesBounds.RF.MemS.block_membership_self_conj_charts ha hg Hy a plc F ga std alt hj supp tie
