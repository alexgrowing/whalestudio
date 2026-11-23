import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAffLine

noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

def coneI (r : ℝ) : Set (ℝ × ℝ) := {x | r < x.2 ∧ r < x.2 + x.1}

def coneC (r : ℝ) : Set (ℝ × ℝ) := {x | r < x.2 - x.1 ∧ r < x.2 + x.1}

def coneA (r : ℝ) : Set (ℝ × ℝ) := {x | r < x.2 - x.1 ∧ r < x.2}

abbrev yv (N : ℝ) : ℂ × ℂ → ℂ := aff 1 1 (1 - N)

abbrev zv (N : ℝ) : ℂ × ℂ → ℂ := aff 1 2 (1 - N)

abbrev nz (N : ℝ) : ℂ × ℂ → ℂ := aff (-1) 0 N

abbrev mc (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg 1 1 (1 - N) 0 1 1

abbrev ma (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg 1 2 (1 - N) 0 1 1

abbrev mb (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg 0 1 0 (-1) (-1) (2 * N - 1)

abbrev ml (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg (-1) 0 N 0 (-1) (N - 1)

def Om1 (N r : ℝ) : Set (ℝ × ℝ) := chgR 1 1 (1 - N) 0 1 1 ⁻¹' coneC r

def Om2 (N r : ℝ) : Set (ℝ × ℝ) := chgR 1 2 (1 - N) 0 1 1 ⁻¹' coneA r

def Om3 (N r : ℝ) : Set (ℝ × ℝ) := chgR 0 1 0 (-1) (-1) (2 * N - 1) ⁻¹' coneC r

def Om4 (N r : ℝ) : Set (ℝ × ℝ) := chgR (-1) 0 N 0 (-1) (N - 1) ⁻¹' coneI r ∩ {x | x.1 < 1 / 2}

def chamberPairOneTwo (M : ℝ) : Set (ℝ × ℝ) := {x | x.1 < -M ∧ M < x.1 + x.2}

def chamberPairTwoThree (M : ℝ) : Set (ℝ × ℝ) := {x | x.1 + x.2 < -M ∧ M < x.1 + 2 * x.2}

def chamberPairThreeFour (M : ℝ) : Set (ℝ × ℝ) := {x | x.1 + 2 * x.2 < -M ∧ M < x.2}

def chamberPairFourLast (M : ℝ) : Set (ℝ × ℝ) := {x | x.2 < -M ∧ x.1 < -M}

lemma mem_Om1 {N r : ℝ} {x : ℝ × ℝ} : x ∈ Om1 N r ↔ r < N - x.1 ∧ r < x.1 + 2 * x.2 + 2 - N := by
  simp only [Om1, Set.mem_preimage, chgR, affR, coneC, Set.mem_setOf_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma mem_Om2 {N r : ℝ} {x : ℝ × ℝ} : x ∈ Om2 N r ↔ r < N - x.1 - x.2 ∧ r < x.2 + 1 := by
  simp only [Om2, Set.mem_preimage, chgR, affR, coneA, Set.mem_setOf_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma mem_Om3 {N r : ℝ} {x : ℝ × ℝ} :
    x ∈ Om3 N r ↔ r < 2 * N - 1 - x.1 - 2 * x.2 ∧ r < 2 * N - 1 - x.1 := by
  simp only [Om3, Set.mem_preimage, chgR, affR, coneC, Set.mem_setOf_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma mem_Om4 {N r : ℝ} {x : ℝ × ℝ} :
    x ∈ Om4 N r ↔ (r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1) ∧ x.1 < 1 / 2 := by
  simp only [Om4, Set.mem_inter_iff, Set.mem_preimage, chgR, affR, coneI, Set.mem_setOf_eq]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> refine ⟨⟨?_, ?_⟩, h₃⟩ <;> linarith

lemma isOpen_hp (α β γ r : ℝ) : IsOpen {x : ℝ × ℝ | r < affR α β γ x} :=
  isOpen_lt continuous_const (continuous_affR α β γ)

lemma convex_hp (α β γ r : ℝ) : Convex ℝ {x : ℝ × ℝ | r < affR α β γ x} := by
  have hl : IsLinearMap ℝ (fun x : ℝ × ℝ => α * x.1 + β * x.2) :=
    ⟨fun a b => by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun c a => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  have h := convex_halfSpace_gt hl (r - γ)
  have e : {x : ℝ × ℝ | r < affR α β γ x} = {w : ℝ × ℝ | r - γ < α * w.1 + β * w.2} := by
    ext x
    simp only [Set.mem_setOf_eq, affR]
    constructor <;> intro h' <;> linarith
  rw [e]
  exact h

lemma open_convex2 {Ω : Set (ℝ × ℝ)} (α₁ β₁ γ₁ α₂ β₂ γ₂ r : ℝ)
    (h : ∀ x, x ∈ Ω ↔ r < affR α₁ β₁ γ₁ x ∧ r < affR α₂ β₂ γ₂ x) : IsOpen Ω ∧ Convex ℝ Ω := by
  have e : Ω = {x | r < affR α₁ β₁ γ₁ x} ∩ {x | r < affR α₂ β₂ γ₂ x} := by
    ext x; exact h x
  rw [e]
  exact ⟨(isOpen_hp _ _ _ _).inter (isOpen_hp _ _ _ _), (convex_hp _ _ _ _).inter (convex_hp _ _ _ _)⟩

lemma oc_coneI (r : ℝ) : IsOpen (coneI r) ∧ Convex ℝ (coneI r) :=
  open_convex2 0 1 0 1 1 0 r fun x => by simp [coneI, affR, add_comm]

lemma isOpen_convex_Om1 (N r : ℝ) : IsOpen (Om1 N r) ∧ Convex ℝ (Om1 N r) :=
  open_convex2 (-1) 0 N 1 2 (2 - N) r fun x => by
    rw [mem_Om1]; simp only [affR]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma isOpen_convex_Om2 (N r : ℝ) : IsOpen (Om2 N r) ∧ Convex ℝ (Om2 N r) :=
  open_convex2 (-1) (-1) N 0 1 1 r fun x => by
    rw [mem_Om2]; simp only [affR]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma isOpen_convex_Om3 (N r : ℝ) : IsOpen (Om3 N r) ∧ Convex ℝ (Om3 N r) :=
  open_convex2 (-1) (-2) (2 * N - 1) (-1) 0 (2 * N - 1) r fun x => by
    rw [mem_Om3]; simp only [affR]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma isOpen_convex_Om4 (N r : ℝ) : IsOpen (Om4 N r) ∧ Convex ℝ (Om4 N r) := by
  have h := open_convex2 (Ω := {x : ℝ × ℝ | r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1})
    0 (-1) (N - 1) (-1) (-1) (2 * N - 1) r fun x => by
      simp only [affR, Set.mem_setOf_eq]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have h' := (isOpen_hp (-1) 0 (1 / 2) 0)
  have h'' := (convex_hp (-1) 0 (1 / 2) 0)
  have e : Om4 N r = {x : ℝ × ℝ | r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1} ∩
      {x | 0 < affR (-1) 0 (1 / 2) x} := by
    ext x
    rw [mem_Om4]
    simp only [affR, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨h₁, by linarith⟩
    · rintro ⟨h₁, h₂⟩; exact ⟨h₁, by linarith⟩
  rw [e]
  exact ⟨h.1.inter h', h.2.inter h''⟩

lemma isOpen_chamberPairOneTwo (M : ℝ) : IsOpen (chamberPairOneTwo M) :=
  (open_convex2 (-1) 0 0 1 1 0 M fun x => by
    simp only [chamberPairOneTwo, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma isOpen_V12 (M : ℝ) : IsOpen (chamberPairTwoThree M) :=
  (open_convex2 (-1) (-1) 0 1 2 0 M fun x => by
    simp only [chamberPairTwoThree, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma isOpen_V23 (M : ℝ) : IsOpen (chamberPairThreeFour M) :=
  (open_convex2 (-1) (-2) 0 0 1 0 M fun x => by
    simp only [chamberPairThreeFour, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma isOpen_V34 (M : ℝ) : IsOpen (chamberPairFourLast M) :=
  (open_convex2 0 (-1) 0 (-1) 0 0 M fun x => by
    simp only [chamberPairFourLast, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma nonempty_V01 (M : ℝ) : (chamberPairOneTwo M).Nonempty :=
  ⟨(-M - 1, 2 * M + 2), by simp only [chamberPairOneTwo, Set.mem_setOf_eq]; constructor <;> linarith⟩

lemma nonempty_V12 (M : ℝ) : (chamberPairTwoThree M).Nonempty :=
  ⟨(-3 * M - 3, 2 * M + 2), by simp only [chamberPairTwoThree, Set.mem_setOf_eq]; constructor <;> linarith⟩

lemma nonempty_V23 (M : ℝ) : (chamberPairThreeFour M).Nonempty :=
  ⟨(-3 * M - 3, M + 1), by simp only [chamberPairThreeFour, Set.mem_setOf_eq]; constructor <;> linarith⟩

lemma nonempty_V34 (M : ℝ) : (chamberPairFourLast M).Nonempty :=
  ⟨(-M - 1, -M - 1), by simp only [chamberPairFourLast, Set.mem_setOf_eq]; constructor <;> linarith⟩

lemma exists_midpoint (N r : ℝ) (x : ℝ × ℝ) :
    ∃ a ∈ coneI r, ∃ b ∈ Om3 N r, x = midpoint ℝ a b := by
  obtain ⟨u, v⟩ := x
  set B : ℝ := |r| + 1 with hB
  set A : ℝ := |r| + |r + 1 - 2 * N + 2 * u| + |r + 1 - 2 * N + 2 * u + 4 * v - 2 * B| + 1 with hA
  have h₀ := le_abs_self r
  have h₁ := le_abs_self (r + 1 - 2 * N + 2 * u)
  have h₂ := le_abs_self (r + 1 - 2 * N + 2 * u + 4 * v - 2 * B)
  have h₃ := abs_nonneg r
  have h₄ := abs_nonneg (r + 1 - 2 * N + 2 * u)
  have h₅ := abs_nonneg (r + 1 - 2 * N + 2 * u + 4 * v - 2 * B)
  refine ⟨(A, B), ?_, (2 * u - A, 2 * v - B), ?_, ?_⟩
  · simp only [coneI, Set.mem_setOf_eq]
    constructor <;> linarith
  · rw [mem_Om3]
    simp only
    constructor <;> linarith
  · rw [midpoint_eq_smul_add]
    ext <;> simp <;> ring

lemma chain4 (hTC : TubeChain) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {T : Type} [TopologicalSpace T] [FirstCountableTopology T] {Ω₀ Ω₁ Ω₂ Ω₃ : Set (ℝ × ℝ)}
    {F₀ F₁ F₂ F₃ : ℂ × ℂ → T → X}
    (h₀ : IsOpen Ω₀ ∧ Convex ℝ Ω₀ ∧ TubeGood F₀ Ω₀) (h₁ : IsOpen Ω₁ ∧ Convex ℝ Ω₁ ∧ TubeGood F₁ Ω₁)
    (h₂ : IsOpen Ω₂ ∧ Convex ℝ Ω₂ ∧ TubeGood F₂ Ω₂) (h₃ : IsOpen Ω₃ ∧ Convex ℝ Ω₃ ∧ TubeGood F₃ Ω₃)
    (j₀ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₀ ∩ Ω₁ ∧ ∀ l ∈ tube V, ∀ g, F₀ l g = F₁ l g)
    (j₁ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₁ ∩ Ω₂ ∧ ∀ l ∈ tube V, ∀ g, F₁ l g = F₂ l g)
    (j₂ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₂ ∩ Ω₃ ∧ ∀ l ∈ tube V, ∀ g, F₂ l g = F₃ l g)
    (mid : ∀ x : ℝ × ℝ, ∃ a ∈ Ω₀, ∃ b ∈ Ω₃, x = midpoint ℝ a b) :
    ∃ Φ : ℂ × ℂ → T → X, TubeGood Φ Set.univ ∧
      (∀ l ∈ tube Ω₀, ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F₀ l g) ∧
      ∀ l ∈ tube Ω₃, ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F₃ l g := by
  obtain ⟨Φ, hΦ, hE⟩ := hTC X T 3 ![Ω₀, Ω₁, Ω₂, Ω₃] ![F₀, F₁, F₂, F₃]
    (by intro i; fin_cases i; exacts [h₀, h₁, h₂, h₃])
    (by intro i; fin_cases i; exacts [j₀, j₁, j₂])
    (by intro x; obtain ⟨a, ha, b, hb, e⟩ := mid x; exact ⟨0, 3, a, ha, b, hb, e⟩)
  exact ⟨Φ, hΦ, hE 0, hE 3⟩

section Fac

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma Fac_left_fst {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, x.1 < a) : Fac (fun l => f l.1) Ω := by
  have := Fac_left hf 1 0 0 (Ω := Ω) (fun x hx => by simpa [affR] using h x hx)
  simpa [aff] using this

lemma Fac_left_snd {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, x.2 < a) : Fac (fun l => f l.2) Ω := by
  have := Fac_left hf 0 1 0 (Ω := Ω) (fun x hx => by simpa [affR] using h x hx)
  simpa [aff] using this

lemma Fac_strip_snd {f : ℂ → X} (hf : StripEntire f) (Ω : Set (ℝ × ℝ)) : Fac (fun l => f l.2) Ω := by
  have := Fac_strip hf 0 1 0 Ω
  simpa [aff] using this

end Fac

lemma lineHol_exp (U : Set (ℂ × ℂ)) : LineHol (fun l : ℂ × ℂ => Complex.exp (l.1 ^ 2 + l.2 ^ 2)) U := by
  intro p v
  apply Differentiable.differentiableOn
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  fun_prop

section Core

variable {T : Type} [TopologicalSpace T] [FirstCountableTopology T]
  {ES EA EB W : Type} [NormedAddCommGroup ES] [NormedSpace ℂ ES] [NormedAddCommGroup EA]
  [NormedSpace ℂ EA] [NormedAddCommGroup EB] [NormedSpace ℂ EB] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]

theorem core (hId : IdTube) (hTC : TubeChain) (N R : ℝ) (hR : |N| + 1 ≤ R)
    {o₀ : ℂ × ℂ → T → ES →L[ℂ] W} {oc oa : ℂ × ℂ → T → EB →L[ℂ] W} {ob ol : ℂ × ℂ → T → EA →L[ℂ] W}
    (g₀ : TubeGood o₀ (coneI (10 * R))) (gc : TubeGood oc (coneC (10 * R)))
    (ga : TubeGood oa (coneA (10 * R))) (gb : TubeGood ob (coneC (10 * R)))
    (gl : TubeGood ol (coneI (10 * R)))
    {Dc Da Db d : ℂ → ℂ} (hDc : StripEntire Dc) (hDa : StripEntire Da) (hDb : StripEntire Db)
    (hd : StripEntire d)
    {Op₀ O : ℂ → ES →L[ℂ] EB} {Opc : ℂ → EB →L[ℂ] EB} {Opa : ℂ → EB →L[ℂ] EA} {Opb : ℂ → EA →L[ℂ] EA}
    (hOp₀ : LeftGood Op₀ (-R)) (hO : LeftGood O (1 / 2)) (hOpc : LeftGood Opc (-R))
    (hOpa : LeftGood Opa (-R)) (hOpb : LeftGood Opb (-R))
    (J₀ : ∀ l ∈ tube (chamberPairOneTwo (100 * R)), ∀ g, Dc (yv N l) • o₀ l g = (oc (mc N l) g).comp (Op₀ l.1))
    (J₁ : ∀ l ∈ tube (chamberPairTwoThree (100 * R)), ∀ g,
      Da (zv N l) • oc (mc N l) g = (oa (ma N l) g).comp (Opc (yv N l)))
    (J₂ : ∀ l ∈ tube (chamberPairThreeFour (100 * R)), ∀ g,
      Db l.2 • oa (ma N l) g = (ob (mb N l) g).comp (Opa (zv N l)))
    (J₃ : ∀ l ∈ tube (chamberPairFourLast (100 * R)), ∀ g,
      (-d (nz N l)) • (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1))) =
        (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1))))) :
    ∃ Φ : ℂ × ℂ → T → ES →L[ℂ] W, TubeGood Φ Set.univ ∧
      (∀ l ∈ tube (coneI (10 * R)), ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
        (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g) ∧
      ∀ l ∈ tube (Om4 N (10 * R)), ∀ g, (-d (nz N l)) • Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
        (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1)))) := by
  have hN := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hN₁ := hN.1
  have hN₂ := hN.2
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]

  set F₀ : ℂ × ℂ → T → ES →L[ℂ] W := fun l g => (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g with hF₀
  set F₁ : ℂ × ℂ → T → ES →L[ℂ] W :=
    fun l g => (Da (zv N l) * Db l.2) • (oc (mc N l) g).comp (Op₀ l.1) with hF₁
  set F₂ : ℂ × ℂ → T → ES →L[ℂ] W :=
    fun l g => Db l.2 • (oa (ma N l) g).comp ((Opc (yv N l)).comp (Op₀ l.1)) with hF₂
  set F₃ : ℂ × ℂ → T → ES →L[ℂ] W :=
    fun l g => (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1))) with hF₃
  have t₀ : TubeGood F₀ (coneI (10 * R)) :=
    TubeGood_smul (Fac_mul (Fac_mul (Fac_strip hDc _ _ _ _) (Fac_strip hDa _ _ _ _))
      (Fac_strip_snd hDb _)) g₀
  have t₁ : TubeGood F₁ (Om1 N (10 * R)) :=
    TubeGood_smul (Fac_mul (Fac_strip hDa _ _ _ _) (Fac_strip_snd hDb _))
      (TubeGood_comp (TubeGood_chg gc _ _ _ _ _ _)
        (Fac_left_fst hOp₀ fun x hx => by have := (mem_Om1.1 hx).1; linarith))
  have t₂ : TubeGood F₂ (Om2 N (10 * R)) :=
    TubeGood_smul (Fac_strip_snd hDb _)
      (TubeGood_comp (TubeGood_chg ga _ _ _ _ _ _)
        (Fac_comp
          (Fac_left hOpc _ _ _ fun x hx => by
            have := (mem_Om2.1 hx).1
            simp only [affR]; linarith)
          (Fac_left_fst hOp₀ fun x hx => by
            have := mem_Om2.1 hx
            linarith [this.1, this.2])))
  have t₃ : TubeGood F₃ (Om3 N (10 * R)) :=
    TubeGood_comp (TubeGood_chg gb _ _ _ _ _ _)
      (Fac_comp
        (Fac_left hOpa _ _ _ fun x hx => by
          have := (mem_Om3.1 hx).1
          simp only [affR]; linarith)
        (Fac_comp
          (Fac_left hOpc _ _ _ fun x hx => by
            have := mem_Om3.1 hx
            simp only [affR]; linarith [this.1, this.2])
          (Fac_left_fst hOp₀ fun x hx => by
            have := (mem_Om3.1 hx).2
            linarith)))
  have j₀ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ coneI (10 * R) ∩ Om1 N (10 * R) ∧
      ∀ l ∈ tube V, ∀ g, F₀ l g = F₁ l g := by
    refine ⟨chamberPairOneTwo (100 * R), isOpen_chamberPairOneTwo _, nonempty_V01 _, ?_, ?_⟩
    · rintro x ⟨h₁, h₂⟩
      refine ⟨?_, mem_Om1.2 ⟨?_, ?_⟩⟩
      · simp only [coneI, Set.mem_setOf_eq]
        constructor <;> linarith
      all_goals linarith
    · intro l hl g
      change (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g =
        (Da (zv N l) * Db l.2) • (oc (mc N l) g).comp (Op₀ l.1)
      rw [← J₀ l hl g, smul_smul]
      congr 1
      ring
  have j₁ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Om1 N (10 * R) ∩ Om2 N (10 * R) ∧
      ∀ l ∈ tube V, ∀ g, F₁ l g = F₂ l g := by
    refine ⟨chamberPairTwoThree (100 * R), isOpen_V12 _, nonempty_V12 _, ?_, ?_⟩
    · rintro x ⟨h₁, h₂⟩
      refine ⟨mem_Om1.2 ⟨?_, ?_⟩, mem_Om2.2 ⟨?_, ?_⟩⟩ <;> linarith
    · intro l hl g
      change (Da (zv N l) * Db l.2) • (oc (mc N l) g).comp (Op₀ l.1) =
        Db l.2 • (oa (ma N l) g).comp ((Opc (yv N l)).comp (Op₀ l.1))
      rw [← ContinuousLinearMap.comp_assoc _ (Opc (yv N l)), ← J₁ l hl g,
        ContinuousLinearMap.smul_comp, smul_smul]
      congr 1
      ring
  have j₂ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Om2 N (10 * R) ∩ Om3 N (10 * R) ∧
      ∀ l ∈ tube V, ∀ g, F₂ l g = F₃ l g := by
    refine ⟨chamberPairThreeFour (100 * R), isOpen_V23 _, nonempty_V23 _, ?_, ?_⟩
    · rintro x ⟨h₁, h₂⟩
      refine ⟨mem_Om2.2 ⟨?_, ?_⟩, mem_Om3.2 ⟨?_, ?_⟩⟩ <;> linarith
    · intro l hl g
      change Db l.2 • (oa (ma N l) g).comp ((Opc (yv N l)).comp (Op₀ l.1)) =
        (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1)))
      rw [← ContinuousLinearMap.comp_assoc _ (Opa (zv N l)), ← J₂ l hl g,
        ContinuousLinearMap.smul_comp]
  obtain ⟨Φ, hΦ, e₀, e₃⟩ := chain4 hTC (F₀ := F₀) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    ⟨(oc_coneI _).1, (oc_coneI _).2, t₀⟩ ⟨(isOpen_convex_Om1 N _).1, (isOpen_convex_Om1 N _).2, t₁⟩
    ⟨(isOpen_convex_Om2 N _).1, (isOpen_convex_Om2 N _).2, t₂⟩ ⟨(isOpen_convex_Om3 N _).1, (isOpen_convex_Om3 N _).2, t₃⟩
    j₀ j₁ j₂ (exists_midpoint N _)
  refine ⟨Φ, hΦ, e₀, fun l hl g => ?_⟩

  have hsub : chamberPairFourLast (100 * R) ⊆ Om4 N (10 * R) ∩ Om3 N (10 * R) := by
    rintro x ⟨h₁, h₂⟩
    refine ⟨mem_Om4.2 ⟨⟨?_, ?_⟩, ?_⟩, mem_Om3.2 ⟨?_, ?_⟩⟩ <;> linarith
  have hneg : StripEntire fun z => -d z :=
    ⟨hd.1.neg, fun b c => by
      obtain ⟨M, hM⟩ := hd.2 b c
      exact ⟨M, fun z h₁ h₂ => by simpa using hM z h₁ h₂⟩⟩
  have hleft : LineHol (fun l : ℂ × ℂ => (-d (nz N l)) • Φ l g) (tube (Om4 N (10 * R))) :=
    (TubeGood_smul (Fac_strip hneg (-1) 0 N _) (TubeGood_mono hΦ (Set.subset_univ _))).hol g
  have hcomp : TubeGood (fun (l : ℂ × ℂ) g => (ol (ml N l) g).comp
      ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1))))) (Om4 N (10 * R)) :=
    TubeGood_comp (TubeGood_mono (TubeGood_chg gl _ _ _ _ _ _) fun x hx => hx.1)
      (Fac_comp
        (Fac_left_snd hOpb fun x hx => by
          have := (mem_Om4.1 hx).1.1
          linarith)
        (Fac_comp
          (Fac_left hOpa _ _ _ fun x hx => by
            have := mem_Om4.1 hx
            simp only [affR]; linarith [this.1.1, this.2])
          (Fac_comp
            (Fac_left hOpc _ _ _ fun x hx => by
              have := mem_Om4.1 hx
              simp only [affR]; linarith [this.1.1, this.2])
            (Fac_left_fst hO fun x hx => (mem_Om4.1 hx).2))))
  have hright : LineHol (fun l : ℂ × ℂ => Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
      (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1)))))
      (tube (Om4 N (10 * R))) :=
    fun p v => (lineHol_exp _ p v).smul (hcomp.hol g p v)
  refine hId (ES →L[ℂ] W) (Om4 N (10 * R)) (chamberPairFourLast (100 * R)) _ _ (isOpen_convex_Om4 N _).1 (isOpen_convex_Om4 N _).2
    (isOpen_V34 _) (nonempty_V34 _) (fun x hx => (hsub hx).1) hleft hright ?_ hl
  intro l' hl'
  have e := e₃ l' (show (l'.1.re, l'.2.re) ∈ Om3 N (10 * R) from (hsub hl').2) g
  simp only [e]
  rw [smul_comm]
  exact congrArg _ (J₃ l' hl' g)

end Core

end GlobalTheory.CompanionTheory.RgEisGal
