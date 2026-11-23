import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathArgsOfNotMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotalTensorThetaLiftEqOfSchwartzEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SandwichedFlipRouteThroughSmallEqInvConstRouteBiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClassSumSchwartzProductsGridPathStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

section Local

open GlobalTheory.SplitFlip Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem update_two_add (x z : Γ.Args) (b₁ b₂ : Edge) (u u' : Matrix (Fin (Γ.rank b₁.tgt)) (Fin (Γ.rank b₁.src)) k)
    (v v' : Matrix (Fin (Γ.rank b₂.tgt)) (Fin (Γ.rank b₂.src)) k) :
    (Function.update (Function.update (x + z) b₁ (u + u')) b₂ (v + v') : Γ.Args) =
      Function.update (Function.update x b₁ u) b₂ v + Function.update (Function.update z b₁ u') b₂ v' := by
  funext b
  by_cases hb : b = b₂
  · subst hb; simp
  · by_cases hb' : b = b₁
    · subst hb'; simp [Function.update_of_ne hb]
    · simp [Function.update_of_ne hb, Function.update_of_ne hb']

theorem mem_update_two {c : kˣ} {z : Γ.Args} (hz : ∀ b, z b ∈ matLat _ (c • stdLat k _)) {b₁ b₂ : Edge}
    {u : Matrix (Fin (Γ.rank b₁.tgt)) (Fin (Γ.rank b₁.src)) k} {v : Matrix (Fin (Γ.rank b₂.tgt)) (Fin (Γ.rank b₂.src)) k}
    (hu : u ∈ matLat _ (c • stdLat k _)) (hv : v ∈ matLat _ (c • stdLat k _)) (b : Edge) :
    (Function.update (Function.update z b₁ u) b₂ v : Γ.Args) b ∈ matLat _ (c • stdLat k _) := by
  by_cases hb : b = b₂
  · subst hb; rwa [Function.update_self]
  · by_cases hb' : b = b₁
    · subst hb'; rwa [Function.update_of_ne hb, Function.update_self]
    · rw [Function.update_of_ne hb, Function.update_of_ne hb']; exact hz b

def setA (i j : ℕ) (x : Γ.Args) (Z : Matrix (Fin (Γ.rank (i + 1, j + 1))) (Γ.Cols i j) k) : Γ.Args :=
  Function.update (Function.update x (.ex i (j + 1)) Z.toCols₁) (.theta (i + 1) j) Z.toCols₂ᵀ

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem joinA_setA (i j : ℕ) (x : Γ.Args) (Z : Matrix (Fin (Γ.rank (i + 1, j + 1))) (Γ.Cols i j) k) :
    Γ.joinA i j (setA i j x Z) = Z := by
  rw [Grid.joinA, setA, Function.update_self, Function.update_of_ne (by simp), Function.update_self, transpose_transpose,
    fromCols_toCols]

variable {ϖ : kˣ} {e : ℕ} {γ : List Edge} {S : Γ.Args → ℂ}

theorem isNatDatum_two (hS : Γ.IsTensor ϖ e γ S) {b₁ b₂ : Edge} (h1 : b₁ ∈ γ) (h2 : b₂ ∈ γ) (hne : b₁ ≠ b₂) (x : Γ.Args)
    {A B : Type} (f₁ : Matrix A B k →+ Matrix (Fin (Γ.rank b₁.tgt)) (Fin (Γ.rank b₁.src)) k)
    (f₂ : Matrix A B k →+ Matrix (Fin (Γ.rank b₂.tgt)) (Fin (Γ.rank b₂.src)) k)
    (hf : ∀ (c : kˣ) Z, Z ∈ matLat A (c • stdLat k B) ↔ f₁ Z ∈ matLat _ (c • stdLat k _) ∧ f₂ Z ∈ matLat _ (c • stdLat k _)) :
    IsNatDatum ϖ e fun Z => S (Function.update (Function.update x b₁ (f₁ Z)) b₂ (f₂ Z)) := by
  refine ⟨fun Z hZ => ?_, fun Z Z₀ hZ₀ => ?_⟩
  · have h := hf 1 Z
    simp only [one_smul] at h
    rcases not_and_or.1 (mt h.2 hZ) with h' | h'
    · exact hS.2.1 _ _ h1 (by rwa [Function.update_of_ne hne, Function.update_self])
    · exact hS.2.1 _ _ h2 (by rwa [Function.update_self])
  · beta_reduce
    rw [map_add, map_add, ← hS.2.2 (Function.update (Function.update x b₁ (f₁ Z)) b₂ (f₂ Z)) _
      (mem_update_two (z := 0) (fun _ => zero_mem _) ((hf _ _).1 hZ₀).1 ((hf _ _).1 hZ₀).2), ← update_two_add, add_zero]

theorem mem_matLat_cols {A B₁ B₂ : Type} (c : kˣ) (Z : Matrix A (B₁ ⊕ B₂) k) :
    Z ∈ matLat A (c • stdLat k _) ↔ Z.toCols₁ ∈ matLat _ (c • stdLat k _) ∧ Z.toCols₂ᵀ ∈ matLat _ (c • stdLat k _) := by
  simp only [mem_matLat, SplitFlip.stdLat, smul_diagLat, mem_diagLat, Matrix.row, Sum.forall, toCols₁, toCols₂, of_apply, transpose_apply,
    Pi.one_apply, forall_and]
  exact and_congr_right fun _ => forall_comm

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def colsL (A B₁ B₂ : Type) : Matrix A (B₁ ⊕ B₂) k →+ Matrix A B₁ k := ⟨⟨toCols₁, rfl⟩, fun _ _ => rfl⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def colsR (A B₁ B₂ : Type) : Matrix A (B₁ ⊕ B₂) k →+ Matrix B₂ A k := ⟨⟨fun Z => Z.toCols₂ᵀ, rfl⟩, fun _ _ => rfl⟩

theorem isNatDatum_small (hS : Γ.IsTensor ϖ e γ S) {i j : ℕ} (h1 : Edge.theta i j ∈ γ) (h2 : Edge.ex i j ∈ γ) (x : Γ.Args) :
    IsNatDatum ϖ e (Γ.sliceB i j S x) :=
  isNatDatum_two hS h1 h2 (by simp) x (colsL _ _ _) (colsR _ _ _) mem_matLat_cols

theorem isNatDatum_big (hS : Γ.IsTensor ϖ e γ S) {i j : ℕ} (h1 : Edge.ex i (j + 1) ∈ γ) (h2 : Edge.theta (i + 1) j ∈ γ)
    (x : Γ.Args) : IsNatDatum ϖ e fun Z => S (setA i j x Z) :=
  isNatDatum_two hS h1 h2 (by simp) x (colsL _ _ _) (colsR _ _ _) mem_matLat_cols

theorem sliceB_add (hS : Γ.IsTensor ϖ e γ S) (i j : ℕ) (x z : Γ.Args) (hz : ∀ b, z b ∈ matLat _ (ϖ ^ e • stdLat k _)) :
    Γ.sliceB i j S (x + z) = Γ.sliceB i j S x := by
  funext Z
  rw [Grid.sliceB, Grid.sliceB, ← hS.2.2 (Function.update (Function.update x _ _) _ _) _
    (mem_update_two (b₁ := .theta i j) (b₂ := .ex i j) hz (zero_mem _) (zero_mem _)), ← update_two_add, add_zero, add_zero]

theorem sliceB_setA (hS : Γ.IsTensor ϖ e γ S) {i j : ℕ} (h1 : Edge.ex i (j + 1) ∉ γ) (h2 : Edge.theta (i + 1) j ∉ γ)
    (x : Γ.Args) (Y : Matrix (Fin (Γ.rank (i + 1, j + 1))) (Γ.Cols i j) k) :
    Γ.sliceB i j S (setA i j x Y) = Γ.sliceB i j S x := by
  funext Z
  refine hS.1 fun b hb => ?_
  have a1 : b ≠ .ex i (j + 1) := fun h => h1 (h ▸ hb)
  have a2 : b ≠ .theta (i + 1) j := fun h => h2 (h ▸ hb)
  by_cases hb : b = .ex i j
  · subst hb; rw [Function.update_self, Function.update_self]
  · by_cases hb' : b = .theta i j
    · subst hb'; rw [Function.update_of_ne hb, Function.update_of_ne hb, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hb, Function.update_of_ne hb, Function.update_of_ne hb', Function.update_of_ne hb', setA,
        Function.update_of_ne a2, Function.update_of_ne a1]

theorem mem_of_update_two (hS : Γ.IsTensor ϖ e γ S) {b₁ b₂ : Edge} {x : Γ.Args} {u v}
    (h : S (Function.update (Function.update x b₁ u) b₂ v) ≠ 0) {b : Edge} (hb : b ∈ γ) (h1 : b ≠ b₁) (h2 : b ≠ b₂) :
    x b ∈ matLat _ (stdLat k _) := by
  by_contra h'
  exact h (hS.2.1 _ b hb (by rwa [Function.update_of_ne h2, Function.update_of_ne h1]))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem add_update_two {x y : Γ.Args} {b₁ b₂ : Edge} (h1 : x b₁ = 0) (h2 : x b₂ = 0) (h1' : y b₁ = 0) (h2' : y b₂ = 0) (u v) :
    x + Function.update (Function.update (0 : Γ.Args) b₁ u) b₂ v + y = Function.update (Function.update (x + y) b₁ u) b₂ v := by
  funext b
  by_cases hb : b = b₂
  · subst hb; simp [h2, h2']
  · by_cases hb' : b = b₁
    · subst hb'; simp [Function.update_of_ne hb, h1, h1']
    · simp [Function.update_of_ne hb, Function.update_of_ne hb']

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem exists_rep_sandwich {W : G.Weil} (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) {X Y Z U : Node} {A : Path T X Y} {r : Path T Y Z} {B' : Path T Z U}
    (hg : OnGrid D.R.m t ((A.comp r).comp B')) {ι : Type} (s : Finset ι) (α φA : ι → PureT G A) (β φB : ι → PureT G B')
    (σ : ι → TotT G r) (ψ : ι → PureT G r → PureT G r) (hA : ∀ κ ∈ s, VecAll ρ e A (φA κ) (α κ))
    (hB : ∀ κ ∈ s, VecAll ρ e B' (φB κ) (β κ)) (hσ : ∀ κ ∈ s, ∀ d ∈ (σ κ).support, VecAll ρ e r (ψ κ d) d)
    (H : ArgT G ((A.comp r).comp B') → ℂ)
    (hH : ∀ x y z, HalfAll e A x → HalfAll e r y → HalfAll e B' z → H ((x.append y).append z) =
      ∑ κ ∈ s, famProd A (φA κ) x * famProd B' (φB κ) z * (σ κ).sum fun d c => c * famProd r (ψ κ d) y) :
    ∃ φ : PureT G ((A.comp r).comp B') → PureT G ((A.comp r).comp B'),
      (∀ d ∈ (∑ κ ∈ s, sandwich (α κ) (σ κ) (β κ)).support, VecAll ρ e _ (φ d) d) ∧
      ∀ x, HalfAll e _ x → ((∑ κ ∈ s, sandwich (α κ) (σ κ) (β κ)).sum fun d c => c * famProd _ (φ d) x) = H x := by
  classical
  have hv : ∀ κ ∈ s, ∀ d ∈ (σ κ).support, VecAll ρ e _ (((φA κ).append (ψ κ d)).append (φB κ)) (((α κ).append d).append (β κ)) :=
    fun κ hκ d hd => (vecAll_append ρ e _ _ _ _ _ _).2 ⟨(vecAll_append ρ e _ _ _ _ _ _).2 ⟨hA κ hκ, hσ κ hκ d hd⟩, hB κ hκ⟩
  let φ : PureT G ((A.comp r).comp B') → PureT G ((A.comp r).comp B') := fun d =>
    if h : ∃ φ, VecAll ρ e _ φ d then h.choose else d
  have hφ : ∀ d φ', VecAll ρ e _ φ' d → φ d = φ' := fun d φ' h => by
    have h' : ∃ φ, VecAll ρ e _ φ d := ⟨φ', h⟩
    simp only [φ, dif_pos h']
    exact vecAll_unique ρ hL he _ hg _ _ d h'.choose_spec h
  refine ⟨φ, fun d hd => ?_, fun x hx => ?_⟩
  · obtain ⟨κ, hκ, hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hd)
    obtain ⟨d', hd', hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
    obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hd)
    rw [hφ _ _ (hv κ hκ d' hd')]
    exact hv κ hκ d' hd'
  · obtain ⟨x', z, rfl⟩ := exists_append _ _ x
    obtain ⟨x, y, rfl⟩ := exists_append _ _ x'
    rw [halfAll_append, halfAll_append] at hx
    rw [hH x y z hx.1.1 hx.1.2 hx.2]
    have e1 : ∀ τ : TotT G ((A.comp r).comp B'), (τ.sum fun d c => c * famProd _ (φ d) ((x.append y).append z)) =
      Finsupp.linearCombination ℂ (fun d => famProd _ (φ d) ((x.append y).append z)) τ := fun τ => rfl
    rw [e1, map_sum]
    refine Finset.sum_congr rfl fun κ hκ => ?_
    rw [sandwich, map_finsuppSum, Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d hd => ?_
    rw [Finsupp.linearCombination_single, hφ _ _ (hv κ hκ d hd), famProd_append, famProd_append, smul_eq_mul]
    ring

theorem edges_routes (t : T) (i j : ℕ) : edges (routeSmall t i j) = [.theta i j, .ex i j] ∧
    edges (routeBig t i j) = [.ex i (j + 1), .theta (i + 1) j] := ⟨rfl, rfl⟩

theorem edges_outer {m : ℕ} {t : T} {i j : ℕ} {A : Path T (.grid 0 m) (.grid i (j + 1))} {Bp : Path T (.grid (i + 1) j) (.grid m 0)}
    (hA : OnGrid m t A) (hB : OnGrid m t Bp) : (edges A).Nodup ∧ (edges Bp).Nodup ∧ (∀ b ∈ edges Bp, b ∉ edges A) ∧
      ∀ b, b ∈ edges A ∨ b ∈ edges Bp → b ≠ .theta i j ∧ b ≠ .ex i j ∧ b ≠ .ex i (j + 1) ∧ b ≠ .theta (i + 1) j := by
  obtain ⟨_, _, h1, -, -, a1, a2⟩ := edges_bound A hA
  obtain ⟨rfl, rfl⟩ := Node.grid.inj h1
  obtain ⟨_, _, -, -, -, b1, b2⟩ := edges_bound Bp hB
  refine ⟨a1, b1, fun b hb hb' => ?_, fun b hb => ?_⟩
  · have := a2 b hb'
    have := b2 b hb
    cases b <;> simp only at * <;> omega
  · rcases hb with hb | hb
    · have := a2 b hb
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp only at this <;> omega
    · have := b2 b hb
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp only at this <;> omega

theorem exists_classes_two {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {X Y X' Y' : Node} (p : Path T X Y) (q : Path T X' Y')
    (hp : OnGrid D.R.m t p) (hq : OnGrid D.R.m t q) (np : (edges p).Nodup) (nq : (edges q).Nodup)
    (hpq : ∀ b ∈ edges q, b ∉ edges p) {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ)
    (h1 : ∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b,
      z w b ∈ SplitFlip.matLat _ (unifAt w ^ n w • SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y)
    (h2 : ∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b, b ∈ edges p ∨ b ∈ edges q →
      x w b ∈ SplitFlip.matLat _ (SplitFlip.stdLat (Kw w) _)) :
    ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (φ' d' : ι → PureT G q) (r : ι → ArgT G p) (r' : ι → ArgT G q),
      (∀ κ ∈ s, VecAll ρ e p (φ κ) (d κ)) ∧ (∀ κ ∈ s, VecAll ρ e q (φ' κ) (d' κ)) ∧
      ∀ x x' y, HalfAll e p x → HalfAll e q x' → K (fun w => pathArgs B t w p x + pathArgs B t w q x') y =
        ∑ κ ∈ s, famProd p (φ κ) x * famProd q (φ' κ) x' * K (fun w => pathArgs B t w p (r κ) + pathArgs B t w q (r' κ)) y := by
  obtain ⟨ι, s, φ, d, r, a1, a2⟩ := GlobalTheory.T.exists_classSum_schwartzProducts_gridPath hL B ρ t he n p hp np (U := ArgT G q × U)
    (fun x y => K (x + fun w => pathArgs B t w q y.1) y.2) (fun x z y hz => by rw [add_right_comm, h1 _ z _ hz])
    fun x y h w hw b hb => by
      have := h2 _ _ h w hw b (.inl hb)
      rwa [Pi.add_apply, Pi.add_apply, pathArgs_of_notMem B t w q _ b fun h' => hpq b h' hb, add_zero] at this
  obtain ⟨ι', s', φ', d', r', b1, b2⟩ := GlobalTheory.T.exists_classSum_schwartzProducts_gridPath hL B ρ t he n q hq nq (U := ι × U)
    (fun x y => K ((fun w => pathArgs B t w p (r y.1)) + x) y.2) (fun x z y hz => by rw [← add_assoc, h1 _ z _ hz])
    fun x y h w hw b hb => by
      have := h2 _ _ h w hw b (.inr hb)
      rwa [Pi.add_apply, Pi.add_apply, pathArgs_of_notMem B t w p _ b (hpq b hb), zero_add] at this
  refine ⟨ι × ι', s ×ˢ s', fun κ => φ κ.1, fun κ => d κ.1, fun κ => φ' κ.2, fun κ => d' κ.2, fun κ => r κ.1, fun κ => r' κ.2,
    fun κ hκ => a1 _ (Finset.mem_product.1 hκ).1, fun κ hκ => b1 _ (Finset.mem_product.1 hκ).2, fun x x' y hx hx' => ?_⟩
  refine (a2 x (x', y) hx).trans ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun κ _ => ?_
  refine (congrArg _ (b2 x' (κ, y) hx')).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => (mul_assoc _ _ _).symm

theorem exists_decomp : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (Tl : ∀ w, (locGrid G t w).Args → ℂ), (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t i j)).comp Bp)) (Tl w)) → (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp)) ((locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w))) → ∀ e : AE D, IsIdemSum e (locPl G t) → ∃ (ι : Type) (s : Finset ι) (α : ι → PureT G A) (β : ι → PureT G Bp) (σs : ι → TotT G (routeSmall t i j)) (σb : ι → TotT G (routeBig t i j)), (∀ κ ∈ s, ∃ Φ : ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ, (∀ w ∈ locPl G t, GlobalTheory.SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (Φ w)) ∧ HasFlip B t ρ ⟨i, hi⟩ ⟨j, hj⟩ (depthAt G) Φ (σb κ) (σs κ)) ∧ (∀ κ ∈ s, (∃ φA, GlobalTheory.FlipRun.VecAll ρ e A φA (α κ)) ∧ ∃ φB, GlobalTheory.FlipRun.VecAll ρ e Bp φB (β κ)) ∧ (∃ φ : PureT G ((A.comp (routeSmall t i j)).comp Bp) → PureT G ((A.comp (routeSmall t i j)).comp Bp), (∀ d ∈ (∑ κ ∈ s, ((σs κ).sum fun d c => Finsupp.single (((α κ).append d).append (β κ)) c)).support, GlobalTheory.FlipRun.VecAll ρ e ((A.comp (routeSmall t i j)).comp Bp) (φ d) d) ∧ ∀ x : GlobalTheory.FlipRun.ArgT G ((A.comp (routeSmall t i j)).comp Bp), GlobalTheory.FlipRun.HalfAll e ((A.comp (routeSmall t i j)).comp Bp) x → ((∑ κ ∈ s, ((σs κ).sum fun d c => Finsupp.single (((α κ).append d).append (β κ)) c)).sum fun d c => c * GlobalTheory.FlipRun.famProd ((A.comp (routeSmall t i j)).comp Bp) (φ d) x) = ∏ w ∈ locPl G t, (Tl) w (GlobalTheory.FlipRun.pathArgs B t w ((A.comp (routeSmall t i j)).comp Bp) x)) ∧ (∃ φ : PureT G ((A.comp (routeBig t i j)).comp Bp) → PureT G ((A.comp (routeBig t i j)).comp Bp), (∀ d ∈ (∑ κ ∈ s, ((σb κ).sum fun d c => Finsupp.single (((α κ).append d).append (β κ)) c)).support, GlobalTheory.FlipRun.VecAll ρ e ((A.comp (routeBig t i j)).comp Bp) (φ d) d) ∧ ∀ x : GlobalTheory.FlipRun.ArgT G ((A.comp (routeBig t i j)).comp Bp), GlobalTheory.FlipRun.HalfAll e ((A.comp (routeBig t i j)).comp Bp) x → ((∑ κ ∈ s, ((σb κ).sum fun d c => Finsupp.single (((α κ).append d).append (β κ)) c)).sum fun d c => c * GlobalTheory.FlipRun.famProd ((A.comp (routeBig t i j)).comp Bp) (φ d) x) = ∏ w ∈ locPl G t, (fun w => (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w)) w (GlobalTheory.FlipRun.pathArgs B t w ((A.comp (routeBig t i j)).comp Bp) x)) := by
  intro D T L sc G μ₀ hL W B ρ t i j hi hj A Bp hA hB Tl hT hTb e he
  obtain ⟨nA, nB, hAB, ho⟩ := edges_outer hA hB
  rw [edges_comp, edges_comp, (edges_routes t i j).1] at hT
  rw [edges_comp, edges_comp, (edges_routes t i j).2] at hTb
  have hm : ∀ (l : List SplitFlip.Edge) b, b ∈ edges A ∨ b ∈ edges Bp → b ∈ edges A ++ l ++ edges Bp := fun l b hb => by
    rcases hb with hb | hb <;> simp [hb]
  have hflip : ∀ w ∈ locPl G t, ∀ x Z, flipAt W t i j w (depthAt G w) ((locGrid G t w).sliceB i j (Tl w) x) Z =
      (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w) (setA i j x Z) :=
    fun w hw x Z => by
      rw [flipTensor_eq, joinA_setA, sliceB_setA (hT w hw)]
      · simp only [List.mem_append, not_or]
        exact ⟨⟨fun h => (ho _ (.inl h)).2.2.1 rfl, by simp⟩, fun h => (ho _ (.inr h)).2.2.1 rfl⟩
      · simp only [List.mem_append, not_or]
        exact ⟨⟨fun h => (ho _ (.inl h)).2.2.2 rfl, by simp⟩, fun h => (ho _ (.inr h)).2.2.2 rfl⟩
  obtain ⟨ι, s, φA, α, φB, β, rA, rB, vA, vB, hK⟩ := exists_classes_two hL B ρ t he (depthAt G) A Bp hA hB nA nB hAB
    (U := (∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w)) ⊕
      ∀ w, Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w))
    (fun x => Sum.elim (fun Z => ∏ w ∈ locPl G t, (locGrid G t w).sliceB i j (Tl w) (x w) (Z w))
      fun Z => ∏ w ∈ locPl G t, flipAt W t i j w (depthAt G w) ((locGrid G t w).sliceB i j (Tl w) (x w)) (Z w))
    (fun x z y hz => by
      rcases y with Z | Z <;> refine Finset.prod_congr rfl fun w hw => ?_ <;> rw [Pi.add_apply, sliceB_add (hT w hw) _ _ _ _ (hz w hw)])
    (fun x y h w hw b hb => by
      rcases y with Z | Z
      · exact mem_of_update_two (hT w hw) (Finset.prod_ne_zero_iff.1 h w hw) (hm _ b hb) (ho b hb).1 (ho b hb).2.1
      · have := Finset.prod_ne_zero_iff.1 h w hw
        rw [hflip w hw] at this
        exact mem_of_update_two (hTb w hw) this (hm _ b hb) (ho b hb).2.2.1 (ho b hb).2.2.2)
  let Φ : ι → ∀ w, Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w) → ℂ := fun κ w =>
    (locGrid G t w).sliceB i j (Tl w) (pathArgs B t w A (rA κ) + pathArgs B t w Bp (rB κ))
  have hΦ : ∀ κ, ∀ w ∈ locPl G t, SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (Φ κ w) := fun κ w hw =>
    isNatDatum_small (hT w hw) (by simp) (by simp) _
  have hΦ' : ∀ κ, ∀ w ∈ locPl G t, SplitFlip.IsNatDatum (unifAt w) (depthAt G w) (flipAt W t i j w (depthAt G w) (Φ κ w)) :=
    fun κ w hw => by
      rw [funext (hflip w hw _)]
      exact isNatDatum_big (hTb w hw) (by simp) (by simp) _
  choose σs hs using fun κ => LocTensor.exists_hasLocal_small B ρ t ⟨i, hi⟩ ⟨j, hj⟩ hL he (hΦ κ)
  choose σb hb using fun κ => LocTensor.exists_hasLocal_big B ρ t ⟨i, hi⟩ ⟨j, hj⟩ hL he (hΦ' κ)
  refine ⟨ι, s, α, β, σs, σb, fun κ _ => ⟨Φ κ, hΦ κ, e, he, hs κ, hb κ⟩, fun κ hκ => ⟨⟨_, vA κ hκ⟩, _, vB κ hκ⟩, ?_, ?_⟩
  · choose φ₁ φ₂ c1 c2 using hs
    refine exists_rep_sandwich ρ hL he (onGrid_comp (onGrid_comp hA (onGrid_routeSmall t hi hj)) hB) s α φA β φB σs
      (fun κ d => (((), φ₁ κ d), φ₂ κ d)) vA vB (fun κ _ d hd => ⟨⟨trivial, (c1 κ d hd).1⟩, (c1 κ d hd).2⟩) _
      fun x y z hx hy hz => ?_
    refine Eq.trans (Finset.prod_congr rfl fun w hw => ?_) ((hK x z (.inl fun w => Matrix.fromCols
      (locArg B t w (.down t i j) y.1.2) (locArg B t w (.right i j) y.2).transpose) hx hz).trans
      (Finset.sum_congr rfl fun κ _ => congrArg _ ?_))
    · rw [pathArgs_append, pathArgs_append, pathArgs_snoc, pathArgs_snoc, SplitFlip.Grid.sliceB]
      · exact congrArg _ (add_update_two (pathArgs_of_notMem B t w A x _ fun h => (ho _ (.inl h)).1 rfl)
          (pathArgs_of_notMem B t w A x _ fun h => (ho _ (.inl h)).2.1 rfl)
          (pathArgs_of_notMem B t w Bp z _ fun h => (ho _ (.inr h)).1 rfl)
          (pathArgs_of_notMem B t w Bp z _ fun h => (ho _ (.inr h)).2.1 rfl) _ _)
      · intro b hb h
        rw [(edges_routes t i j).1] at hb
        have := ho b (.inl h)
        simp [this.1, this.2.1] at hb
      · intro b hb h
        have := ho b (.inr hb)
        rw [edges_comp, (edges_routes t i j).1] at h
        simp [this.1, this.2.1, hAB b hb] at h
    · refine Eq.trans ?_ ((c2 κ y.1.2 y.2 hy.1.2 hy.2).symm.trans (Finsupp.sum_congr fun d _ => ?_))
      · refine Finset.prod_congr rfl fun w _ => ?_
        exact congrArg (Φ κ w) (congrArg₂ Matrix.fromCols (dif_pos (And.intro hi.le hj))
          (congrArg Matrix.transpose (dif_pos (And.intro hi hj.le))))
      · exact congrArg _ (congrArg (· * _) (one_mul _).symm)
  · choose φ₁ φ₂ c1 c2 using hb
    refine exists_rep_sandwich ρ hL he (onGrid_comp (onGrid_comp hA (onGrid_routeBig t hi hj)) hB) s α φA β φB σb
      (fun κ d => (((), φ₁ κ d), φ₂ κ d)) vA vB (fun κ _ d hd => ⟨⟨trivial, (c1 κ d hd).1⟩, (c1 κ d hd).2⟩) _
      fun x y z hx hy hz => ?_
    refine Eq.trans (Finset.prod_congr rfl fun w hw => ?_) ((hK x z (.inr fun w => Matrix.fromCols
      (locArg B t w (.right i (j + 1)) y.1.2) (locArg B t w (.down t (i + 1) j) y.2).transpose) hx hz).trans
      (Finset.sum_congr rfl fun κ _ => congrArg _ ?_))
    · rw [hflip w hw, pathArgs_append, pathArgs_append, pathArgs_snoc, pathArgs_snoc, setA]
      · exact congrArg _ (add_update_two (pathArgs_of_notMem B t w A x _ fun h => (ho _ (.inl h)).2.2.1 rfl)
          (pathArgs_of_notMem B t w A x _ fun h => (ho _ (.inl h)).2.2.2 rfl)
          (pathArgs_of_notMem B t w Bp z _ fun h => (ho _ (.inr h)).2.2.1 rfl)
          (pathArgs_of_notMem B t w Bp z _ fun h => (ho _ (.inr h)).2.2.2 rfl) _ _)
      · intro b hb h
        rw [(edges_routes t i j).2] at hb
        have := ho b (.inl h)
        simp [this.2.2.1, this.2.2.2] at hb
      · intro b hb h
        have := ho b (.inr hb)
        rw [edges_comp, (edges_routes t i j).2] at h
        simp [this.2.2.1, this.2.2.2, hAB b hb] at h
    · refine Eq.trans ?_ ((c2 κ y.1.2 y.2 hy.1.2 hy.2).symm.trans (Finsupp.sum_congr fun d _ => ?_))
      · refine Finset.prod_congr rfl fun w _ => ?_
        exact congrArg (flipAt W t i j w (depthAt G w) (Φ κ w))
          (congrArg₂ Matrix.fromCols (dif_pos (And.intro hi hj)) (congrArg Matrix.transpose (dif_pos (And.intro hi hj))))
      · exact congrArg _ (congrArg (· * _) (one_mul _).symm)

theorem oneFlip : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j < D.R.m) (c : ℂ), c ≠ 0 → CommutesWith W B ρ t ⟨i, hi⟩ ⟨j, hj⟩ c → ∀ (A : Path T (.grid 0 D.R.m) (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) (.grid D.R.m 0)), GlobalTheory.FlipRun.OnGrid D.R.m t A → GlobalTheory.FlipRun.OnGrid D.R.m t Bp → ∀ (Q : GlobalTheory.FlipRun.PolE G →₀ ℂ) (τ : TotT G ((A.comp (routeSmall t i j)).comp Bp)) (Tl : ∀ w, (locGrid G t w).Args → ℂ), (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t i j)).comp Bp)) (Tl w)) → (∀ w ∈ locPl G t, (locGrid G t w).IsTensor (unifAt w) (depthAt G w) (GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp)) ((locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w))) → GlobalTheory.FlipRun.RepFin B ρ t _ τ Tl → ∃ τ' : TotT G ((A.comp (routeBig t i j)).comp Bp), GlobalTheory.FlipRun.RepFin B ρ t _ τ' (fun w => (locGrid G t w).flipTensor .one (psiAt W w) (unifAt w) (depthAt G w) i j (givenLevel G t w) (Tl w)) ∧ ∀ M : Vol G, M.Is t → GlobalTheory.FlipRun.CuspStep W M ρ t → ∀ F : Fn G (.grid 0 D.R.m), GlobalTheory.FlipRun.IsCuspListed W.θ _ F → TotConv W M _ (GlobalTheory.FlipRun.tensE W _ Q τ) F → TotConv W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) τ') F ∧ liftT W M _ (GlobalTheory.FlipRun.tensE W _ Q τ) F = c⁻¹ • liftT W M _ (GlobalTheory.FlipRun.tensE W _ (GlobalTheory.FlipRun.flipPolE ρ i j Q) τ') F := by
  intro D T L sc G μ₀ hL W B ρ t i j hi hj c hc hcomm A Bp hA hBp Q τ Tl hT hTb hR
  obtain ⟨e, he, φ, hφ, hfun⟩ := hR
  obtain ⟨ι, s, α, β, σs, σb, hflip, hout, hR₂, hR'⟩ := exists_decomp hL W B ρ t i j hi hj A Bp hA hBp Tl hT hTb e he
  have hPs : OnGrid D.R.m t ((A.comp (routeSmall t i j)).comp Bp) :=
    onGrid_comp (onGrid_comp hA (onGrid_routeSmall t hi hj)) hBp
  have hPb : OnGrid D.R.m t ((A.comp (routeBig t i j)).comp Bp) :=
    onGrid_comp (onGrid_comp hA (onGrid_routeBig t hi hj)) hBp
  refine ⟨∑ κ ∈ s, sandwich (α κ) (σb κ) (β κ), ⟨e, he, hR'⟩, fun M hM hC F hF _ => ?_⟩
  obtain ⟨φ', hφ', -⟩ := hR'
  obtain ⟨φ₂, hφ₂, hfun₂⟩ := hR₂
  refine ⟨totConv_tensE M ρ t he hC _ hPb _ φ' hφ' F hF _, ?_⟩
  rw [GlobalTheory.T.totalTensorThetaLift_eq_of_schwartz_eq hL M ρ t he hC _ hPs τ _ φ φ₂ hφ hφ₂ (fun x hx => (hfun x hx).trans (hfun₂ x hx).symm) F hF Q,
    tensE_sum, liftT_sum, tensE_sum, liftT_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  obtain ⟨Φ, hΦ, hF'⟩ := hflip κ hκ
  obtain ⟨⟨φA, hφA⟩, φB, hφB⟩ := hout κ hκ
  exact GlobalTheory.T.sandwichedFlip_routeThroughSmall_eq_inv_const_routeBig M B ρ t i j hi hj c hc hcomm hM hC A Bp hA hBp e he (α κ) (β κ) φA φB hφA hφB (σs κ) (σb κ) Φ hΦ hF' F hF Q

end GlobalTheory.FlipRun

end
