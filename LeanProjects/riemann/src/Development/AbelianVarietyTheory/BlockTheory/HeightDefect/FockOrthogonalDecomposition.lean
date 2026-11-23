import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure IsOrthDec (V : HSp D) (τ : D.what₂.Tau) (P N : Submodule D.host.E V.V) : Prop where
  compl : IsCompl P N
  orth : ∀ x ∈ P, ∀ y ∈ N, V.hT x y = 0
  pos : ∀ x ∈ P, x ≠ 0 → 0 < (tauE D τ (V.hT x x)).re
  neg : ∀ x ∈ N, x ≠ 0 → (tauE D τ (V.hT x x)).re < 0

def IsSignInv (V : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) : Prop :=
  ∃ P N : Submodule D.host.E V.V, IsOrthDec V τ P N ∧ (∀ x ∈ P, s x = x) ∧ ∀ x ∈ N, s x = -x

abbrev InvFam (V : HSp D) : Type := D.what₂.Tau → Module.End D.host.E V.V

def IsSignFam (V : HSp D) (s : InvFam V) : Prop := ∀ τ, IsSignInv V τ (s τ)

def thAt (V : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (LinearMap.toMatrix V.frame V.frame s).map (tauE D τ)

def KAt (V : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) : Set (Matrix (Fin V.rank) (Fin V.rank) ℂ) :=
  {g | g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ g * thAt V τ s = thAt V τ s * g}

abbrev InfFam (D : D7) : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

theorem infMat_one (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) :
    infMat D.sp.cm.sig V.gram θ (1 : GA D V) = 1 := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (1 : GA D V) = 1 := rfl
  simp only [infMat, this, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem infMat_mul (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

def Kinf (θ : InfFam D) (V : HSp D) (s : InvFam V) : Subgroup (GA D V) where
  carrier := {g | g ∈ GinfC V ∧ ∀ τ, Commute (infMat D.sp.cm.sig V.gram (θ τ) g) (thAt V τ (s τ))}
  one_mem' := ⟨one_mem _, fun τ => by rw [infMat_one]; exact Commute.one_left _⟩
  mul_mem' := fun {g h} hg hh => ⟨mul_mem hg.1 hh.1, fun τ => by
    rw [infMat_mul]; exact (hg.2 τ).mul_left (hh.2 τ)⟩
  inv_mem' := fun {g} hg => ⟨inv_mem hg.1, fun τ => by
    let u : (Matrix (Fin V.rank) (Fin V.rank) ℂ)ˣ :=
      ⟨infMat D.sp.cm.sig V.gram (θ τ) g, infMat D.sp.cm.sig V.gram (θ τ) g⁻¹,
        by rw [← infMat_mul, mul_inv_cancel, infMat_one], by rw [← infMat_mul, inv_mul_cancel, infMat_one]⟩
    exact Commute.units_inv_left (u := u) (hg.2 τ)⟩

abbrev WC (V W : HSp D) : Type := Matrix (Fin V.rank) (Fin W.rank) ℂ

def wAt (θ : InfFam D) (V W : HSp D) (τ : D.what₂.Tau) (x : WA V W) : WC V W :=
  x.map fun a => θ τ (infPart D a)

def actC (V W : HSp D) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (x : WC V W) : WC V W :=
  if V.rank ≤ W.rank then g.map (starRingEnd ℂ) * x * h.transpose
  else g * x * (h.map (starRingEnd ℂ)).transpose

def hC (V W : HSp D) (τ : D.what₂.Tau) (x y : WC V W) : ℂ :=
  if V.rank ≤ W.rank then
    ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * gramAt D V τ k i * gramAt D W τ j l * y k l
  else
    ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * gramAt D V τ i k * gramAt D W τ l j * y k l

def symplC (V W : HSp D) (τ : D.what₂.Tau) (x y : WC V W) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hC V W τ y x).re

def jAt (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V)
    (x : WC V W) : WC V W :=
  Complex.I • actC V W (thAt V τ s) (thAt W τ s') x

def SpAt (V W : HSp D) (τ : D.what₂.Tau) : Set (WC V W →L[ℝ] WC V W) :=
  {k | ∀ x y, symplC V W τ (k x) (k y) = symplC V W τ x y}

def UJAt (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V) :
    Set (WC V W →L[ℝ] WC V W) :=
  {k | k ∈ SpAt V W τ ∧ ∀ x, k (jAt V W τ s s' x) = jAt V W τ s s' (k x)}

def IsRealLine (V W : HSp D) (L : ℝ →+ WA V W) : Prop :=
  Continuous L ∧ ∀ t, (L t).map (finPart D) = 0

def dHeis (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  fun w => deriv (fun t : ℝ => Heisenberg₂ ψ V W (L t) f w) 0

def IsJPair (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) (L L' : ℝ →+ WA V W) : Prop :=
  IsRealLine V W L ∧ IsRealLine V W L' ∧
    ∀ t τ, wAt θ V W τ (L' t) = jAt V W τ (s τ) (s' τ) (wAt θ V W τ (L t))

def cre (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L L' : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  dHeis ψ V W L f - Complex.I • dHeis ψ V W L' f

def ann (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (L L' : ℝ →+ WA V W) (f : WA V W → ℂ) : WA V W → ℂ :=
  dHeis ψ V W L f + Complex.I • dHeis ψ V W L' f

def IsVacuum (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W)
    (f : WA V W → ℂ) : Prop :=
  IsThetaFun ψ V W f ∧ ∀ L L', IsJPair θ V W s s' L L' → ann ψ V W L L' f = 0

inductive IsFockMon (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) :
    (WA V W → ℂ) → Prop
  | vac (f : WA V W → ℂ) : IsVacuum ψ θ V W s s' f → IsFockMon ψ θ V W s s' f
  | cre (L L' : ℝ →+ WA V W) (f : WA V W → ℂ) : IsJPair θ V W s s' L L' → IsFockMon ψ θ V W s s' f →
      IsFockMon ψ θ V W s s' (cre ψ V W L L' f)

def polFun (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) :
    Submodule ℂ (WA V W → ℂ) :=
  Submodule.span ℂ {f | IsFockMon ψ θ V W s s' f}

variable {X : ThetaX D} {T : ThetaTied D X}

def polSch (Wl : WeilTied D X T) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) :
    Submodule ℂ (X.Sch V W) :=
  (polFun Wl.ψ θ V W s s').comap (Wl.evS V W)

def IsStdDec (A Y : HSp D) (ι : A.V →ₗ[D.host.E] Y.V) (n : ℕ) (b : Prop) (s : InvFam Y) : Prop :=
  ∃ (e f : Fin n → Y.V) (z : Y.V),
    (∀ i i', Y.hT (e i) (e i') = 0 ∧ Y.hT (f i) (f i') = 0 ∧ Y.hT (e i) (f i') = if i = i' then 1 else 0) ∧
    (∀ i x, Y.hT (ι x) (e i) = 0 ∧ Y.hT (ι x) (f i) = 0) ∧
    (∀ x, Y.hT (ι x) z = 0) ∧ (∀ i, Y.hT z (e i) = 0 ∧ Y.hT z (f i) = 0) ∧ (z ≠ 0 ↔ b) ∧
    ∀ τ, IsOrthDec Y τ
        (LinearMap.range ι ⊔ Submodule.span D.host.E (Set.range fun i => e i + f i))
        (Submodule.span D.host.E (Set.range fun i => e i - f i) ⊔ Submodule.span D.host.E {z}) ∧
      (∀ x, s τ (ι x) = ι x) ∧ (∀ i, s τ (e i + f i) = e i + f i ∧ s τ (e i - f i) = -(e i - f i)) ∧ s τ z = -z

def TowerAdapted (X : ThetaX D) (s : ∀ V : HSp D, InvFam V) : Prop :=
  ∀ t, Odd t → D.R.r + 5 ≤ t → ∀ j, j < D.R.m →
    IsStdDec (X.Xs t j) (X.Ys t j) (X.iXYs t j) ((D.R.m - 1 - j) / 2) (Even j) (s (X.Ys t j))

def KfinWeilCompatibleWith (Wl : WeilTied D X T) (s : ∀ V : HSp D, InvFam V) : Prop :=
  (∀ V, IsSignFam V (s V)) ∧
    AllSome (IsInfFam (D := D)) fun θ => ∀ V W : HSp D, V.rank ≠ W.rank →
      X.kfin V W = polSch Wl θ V W (s V) (s W)

def KfinWeilCompatibleExists (Wl : WeilTied D X T) : Prop := ∃ s, KfinWeilCompatibleWith Wl s

def KfinTied (Wl : WeilTied D X T) : Prop := ∃ s, TowerAdapted X s ∧ KfinWeilCompatibleWith Wl s

def IsMaxCompactIn {M : Type} [Monoid M] [TopologicalSpace M] (G K : Set M) : Prop :=
  (K ⊆ G ∧ 1 ∈ K ∧ (∀ a ∈ K, ∀ b ∈ K, a * b ∈ K) ∧ IsCompact K) ∧
    ∀ K' : Set M, K ⊆ K' → K' ⊆ G → (∀ a ∈ K', ∀ b ∈ K', a * b ∈ K') → IsCompact K' → K' = K

def ClaimDecExists (D : D7) : Prop := ∀ (V : HSp D) (τ : D.what₂.Tau), ∃ s, IsSignInv V τ s

def ClaimKMax (D : D7) : Prop :=
  ∀ (V : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V), IsSignInv V τ s →
    IsMaxCompactIn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (KAt V τ s) ∧
    (s = 1 ∨ s = -1 → KAt V τ s = Formalism.QuantumDeterminants.UH (gramAt D V τ))

def IsPosCx (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V) (s' : Module.End D.host.E W.V)
    (J' : WC V W → WC V W) : Prop :=
  IsLinearMap ℝ J' ∧ (∀ x, J' (J' x) = -x) ∧ (∀ x y, symplC V W τ (J' x) (J' y) = symplC V W τ x y) ∧
    (∀ x, x ≠ 0 → 0 < -symplC V W τ (J' x) x) ∧
    ∀ g ∈ KAt V τ s, ∀ h ∈ KAt W τ s', ∀ x, J' (actC V W g h x) = actC V W g h (J' x)

def ClaimJ (D : D7) : Prop :=
  ∀ (V W : HSp D) (τ : D.what₂.Tau) s s', IsSignInv V τ s → IsSignInv W τ s' →
    ∀ J', IsPosCx V W τ s s' J' ↔ J' = jAt V W τ s s'

def ClaimUJ (D : D7) : Prop :=
  ∀ (V W : HSp D) (τ : D.what₂.Tau) s s', IsSignInv V τ s → IsSignInv W τ s' →
    ∀ K : Set (WC V W →L[ℝ] WC V W),
      (IsMaxCompactIn (SpAt V W τ) K ∧
        ∀ g ∈ KAt V τ s, ∀ h ∈ KAt W τ s', ∃ k ∈ K, ∀ x, k x = actC V W g h x) ↔ K = UJAt V W τ s s'

def AnnNil (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W)
    (n : ℕ) (f : WA V W → ℂ) : Prop :=
  ∀ l : List ((ℝ →+ WA V W) × (ℝ →+ WA V W)), l.length = n → (∀ p ∈ l, IsJPair θ V W s s' p.1 p.2) →
    l.foldr (fun p g => ann ψ V W p.1 p.2 g) f = 0

def IsImpl (Wl : WeilTied D X T) (θ : InfFam D) (V W : HSp D) (k : D.what₂.Tau → (WC V W →L[ℝ] WC V W))
    (M : Module.End ℂ (X.Sch V W)) : Prop :=
  (∀ w w' : WA V W, w'.map (finPart D) = w.map (finPart D) → (∀ τ, wAt θ V W τ w' = k τ (wAt θ V W τ w)) →
    ∀ Φ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W w (Wl.evS V W Φ) →
      Wl.evS V W (M Φ') = Heisenberg₂ Wl.ψ V W w' (Wl.evS V W (M Φ))) ∧
  ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ →
    ∀ Φ, ∫ w in 𝓕, ‖Wl.evS V W (M Φ) w‖ ^ 2 ∂μ = ∫ w in 𝓕, ‖Wl.evS V W Φ w‖ ^ 2 ∂μ

def IsUJFinite (Wl : WeilTied D X T) (θ : InfFam D) (V W : HSp D) (s : InvFam V) (s' : InvFam W) (Φ : X.Sch V W) :
    Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ
    {Ψ : X.Sch V W | ∃ k M, (∀ τ, k τ ∈ UJAt V W τ (s τ) (s' τ)) ∧ IsImpl Wl θ V W k M ∧ Ψ = M Φ})

def ClaimPolChar (Wl : WeilTied D X T) : Prop :=
  ∀ θ, IsInfFam θ → ∀ V W : HSp D, V.rank ≠ W.rank → ∀ s s', IsSignFam V s → IsSignFam W s' → ∀ Φ : X.Sch V W,
    (Φ ∈ polSch Wl θ V W s s' ↔ ∃ n, AnnNil Wl.ψ θ V W s s' n (Wl.evS V W Φ)) ∧
    (Φ ∈ polSch Wl θ V W s s' ↔ IsUJFinite Wl θ V W s s' Φ)

def ClaimPolStable (Wl : WeilTied D X T) : Prop :=
  ∀ θ, IsInfFam θ → ∀ V W : HSp D, V.rank ≠ W.rank → ∀ s s', IsSignFam V s → IsSignFam W s' →
    ∀ χ χ', ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → ∀ Φ ∈ polSch Wl θ V W s s',
      (∀ g ∈ Kinf θ V s ⊔ GfC V, ∀ h ∈ Kinf θ W s' ⊔ GfC W, Wl.om V W χ χ' (g, h) Φ ∈ polSch Wl θ V W s s') ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        {Ψ : X.Sch V W | ∃ g ∈ Kinf θ V s, ∃ h ∈ Kinf θ W s', Ψ = Wl.om V W χ χ' (g, h) Φ})

def ClaimPolDense (Wl : WeilTied D X T) : Prop :=
  ∀ θ, IsInfFam θ → ∀ V W : HSp D, V.rank ≠ W.rank → ∀ s s', IsSignFam V s → IsSignFam W s' →
    ∀ (Φ : X.Sch V W) (S : List (List (ℝ →+ WA V W))), (∀ l ∈ S, ∀ L ∈ l, IsRealLine V W L) → ∀ ε : ℝ, 0 < ε →
      ∃ Φ' ∈ polSch Wl θ V W s s',
        (∀ u : WA V W, u.map (infPart D) = 0 → Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) = Wl.evS V W Φ →
          Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ') = Wl.evS V W Φ') ∧
        ∀ l ∈ S, ∀ w, ‖l.foldr (dHeis Wl.ψ V W) (Wl.evS V W (Φ - Φ')) w‖ ≤ ε

def ClaimPolSwap (Wl : WeilTied D X T) : Prop :=
  ∀ θ, IsInfFam θ → ∀ V W : HSp D, V.rank ≠ W.rank → ∀ s s', IsSignFam V s → IsSignFam W s' →
    ∀ (Φ : X.Sch V W) (Φ' : X.Sch W V), (∀ x : WA V W, Wl.evS W V Φ' x.transpose = Wl.evS V W Φ x) →
      (Φ ∈ polSch Wl θ V W s s' ↔ Φ' ∈ polSch Wl θ W V s' s)

example (V : HSp D) (τ : D.what₂.Tau) (h : ∀ x : V.V, x ≠ 0 → 0 < (tauE D τ (V.hT x x)).re) : IsSignInv V τ 1 :=
  ⟨⊤, ⊥, ⟨isCompl_top_bot, fun x _ y hy => by rw [(Submodule.mem_bot _).1 hy, map_zero], fun x _ => h x,
    fun x hx hx' => absurd ((Submodule.mem_bot _).1 hx) hx'⟩, fun _ _ => rfl,
    fun x hx => by rw [(Submodule.mem_bot _).1 hx]; simp⟩

example (V W : HSp D) (τ : D.what₂.Tau) (x : WC V W) : jAt V W τ 1 1 x = Complex.I • x := by
  have h : ∀ U : HSp D, thAt U τ 1 = 1 := fun U => by
    simp only [thAt, LinearMap.toMatrix_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  simp only [jAt, actC, h]
  split_ifs <;> simp

theorem KfinTied.some {Wl : WeilTied D X T} (h : KfinTied Wl) : KfinWeilCompatibleExists Wl :=
  let ⟨s, _, hs⟩ := h; ⟨s, hs⟩

end GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition

end
