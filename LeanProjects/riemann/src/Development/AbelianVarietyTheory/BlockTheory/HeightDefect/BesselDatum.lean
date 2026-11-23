import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.LocalRingCardinality.ConjSqrtMinusD

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.BesselData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure BesselDatum (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) where
  isom : HSpace.IsIsomEmb A B ι

  ρ : ℕ
  rank_eq : B.rank = A.rank + (2 * ρ + 1)

  e : Fin ρ → B.V

  f : Fin ρ → B.V

  z : B.V
  ee : ∀ i j, B.hD (e i) (e j) = 0
  ff : ∀ i j, B.hD (f i) (f j) = 0
  ef : ∀ i j, B.hD (e i) (f j) = if i = j then 1 else 0
  eA : ∀ i x, B.hD (e i) (ι x) = 0
  fA : ∀ i x, B.hD (f i) (ι x) = 0
  zA : ∀ x, B.hD z (ι x) = 0
  ez : ∀ i, B.hD (e i) z = 0
  fz : ∀ i, B.hD (f i) z = 0
  zz : B.hD z z ≠ 0

  θ : D.host.E
  θ_ne : θ ≠ 0

def vecA (B : HSp D) (v : B.V) : Fin B.rank → AE D := fun i => incA D (B.frame.repr v i)

def hA (B : HSp D) (x y : Fin B.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (y i) * incA D (B.gram i j) * x j

def actV (B : HSp D) (g : GA D B) (v : B.V) : Fin B.rank → AE D := (mt B g).mulVec (vecA B v)

namespace BesselDatum

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesselDatum A B ι)

def aux : Fin (d.ρ + 1) → B.V := Fin.snoc (α := fun _ => B.V) d.e d.z

def NSet : Set (GA D B) :=
  {n | (∀ i, ∃ c : Fin d.ρ → AE D, (∀ l, i ≤ l → c l = 0) ∧
        actV B n (d.e i) = vecA B (d.e i) + ∑ l, c l • vecA B (d.e l)) ∧
    ∀ x : B.V, (∀ i, B.hD x (d.e i) = 0) →
      ∃ c : Fin d.ρ → AE D, actV B n x = vecA B x + ∑ l, c l • vecA B (d.e l)}

def N : Subgroup (GA D B) := Subgroup.closure d.NSet

def NQ : Subgroup d.N := (GQ B).subgroupOf d.N

def simpleSum (n : GA D B) : AE D := ∑ i : Fin d.ρ, hA B (actV B n (d.aux i.succ)) (vecA B (d.f i))

def psiN (ψ : AddChar (AF D.host.F) ℂ) (n : GA D B) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D) (incA D d.θ * d.simpleSum n))

def IsUnitPair (ν : Measure d.N) (𝓝 : Set d.N) : Prop :=
  ν.IsHaarMeasure ∧ IsFundamentalDomain d.NQ 𝓝 ν ∧ ν 𝓝 = 1

def coeff (ψ : AddChar (AF D.host.F) ℂ) (ν : Measure d.N) (𝓝 : Set d.N) (F : GA D B → ℂ) (g : GA D B) : ℂ :=
  ∫ n in 𝓝, F ((n : GA D B) * g) * star (d.psiN ψ (n : GA D B)) ∂ν

def period (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (ν : Measure d.N) (𝓝 : Set d.N)
    (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : ℂ :=
  ∫ h in 𝓕, φ h * d.coeff ψ ν 𝓝 F (s h) ∂μ

def Converges (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (ν : Measure d.N) (𝓝 : Set d.N)
    (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : Prop :=
  ∀ g, IntegrableOn (fun h => φ h * d.coeff ψ ν 𝓝 (rTr B g F) (s h)) 𝓕 μ

def ExSet (ε : AE D) (i : Fin (d.ρ + 1)) : Set (GA D B) :=
  {g | SuppAt ε B g ∧
    (∀ x : A.V, ε • (actV B g (ι x) - vecA B (ι x)) = 0) ∧
    (∀ l, ε • (actV B g (d.f l) - vecA B (d.f l)) = 0) ∧
    (∀ l, l ≠ i → ε • (actV B g (d.aux l) - vecA B (d.aux l)) = 0) ∧
    ∃ y : Fin A.rank → AE D,
      ε • (actV B g (d.aux i) - vecA B (d.aux i)) = ε • ((frameMat B A ι).map (incA D)).mulVec y}

def Ex (ε : AE D) (i : Fin (d.ρ + 1)) : Subgroup (GA D B) := Subgroup.closure (d.ExSet ε i)

def exch (ε : AE D) (i : Fin (d.ρ + 1)) (m : Measure (d.Ex ε i)) (b : (GA D B → ℂ) → ℂ) : (GA D B → ℂ) → ℂ :=
  fun F => ∫ u, b (rTr B (u : GA D B) F) ∂m

def toPos (ε : AE D) (m : ∀ i, Measure (d.Ex ε i)) (p : ℕ) (b : (GA D B → ℂ) → ℂ) : (GA D B → ℂ) → ℂ :=
  ((List.finRange (d.ρ + 1)).filter fun i => decide (p ≤ i.1)).foldr (fun i b' => d.exch ε i (m i) b') b

end BesselDatum

structure PosDatum (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) where
  bes : BesselDatum A B ι
  n : ℕ

  ε : Fin n → AE D
  split : ∀ a, IsSplitIdem D (ε a)

  apart : ∀ a b, a ≠ b → (ε a + cA D (ε a)) * (ε b + cA D (ε b)) = 0
  p : Fin n → ℕ
  one_le : ∀ a, 1 ≤ p a
  le_sym : ∀ a, p a ≤ bes.ρ + 1
  m : ∀ a i, Measure (bes.Ex (ε a) i)
  haar : ∀ a i, (m a i).IsHaarMeasure

namespace PosDatum

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def sym (d : BesselDatum A B ι) : PosDatum A B ι where
  bes := d
  n := 0
  ε := Fin.elim0
  split := fun a => a.elim0
  apart := fun a => a.elim0
  p := Fin.elim0
  one_le := fun a => a.elim0
  le_sym := fun a => a.elim0
  m := fun a => a.elim0
  haar := fun a => a.elim0

def move (P : PosDatum A B ι) (b : (GA D B → ℂ) → ℂ) : (GA D B → ℂ) → ℂ :=
  (List.finRange P.n).foldr (fun a b' => P.bes.toPos (P.ε a) (P.m a) (P.p a) b') b

def period (P : PosDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (GA D A)) (𝓕 : Set (GA D A))
    (ν : Measure P.bes.N) (𝓝 : Set P.bes.N) (s : GA D A → GA D B) (φ : GA D A → ℂ) (F : GA D B → ℂ) : ℂ :=
  P.move (P.bes.period ψ μ 𝓕 ν 𝓝 s φ) F

theorem period_sym (d : BesselDatum A B ι) (ψ μ 𝓕 ν 𝓝 s φ F) :
    (sym d).period ψ μ 𝓕 ν 𝓝 s φ F = d.period ψ μ 𝓕 ν 𝓝 s φ F := rfl

end PosDatum

theorem toPos_sym {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesselDatum A B ι) (ε m b) :
    d.toPos ε m (d.ρ + 1) b = b := by
  unfold BesselDatum.toPos
  rw [List.filter_eq_nil_iff.2 (fun i _ => by have := i.2; simp; omega)]
  rfl

theorem embedding_xi_zero_ne_zero (D : D7) : D.host.xi0 ≠ 0 := by
  have h1 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
  have h2 : D.host.sqrtMinusD ≠ 0 := by
    intro h
    have := D.host.sqrtMinusD_sq
    rw [h] at this
    have hd : (D.host.d : D.host.E) ≠ 0 := by
      have := D.host.qd_big.2
      exact_mod_cast (by omega : D.host.d ≠ 0)
    apply hd
    linear_combination this
  unfold Host.xi0
  exact div_ne_zero (by norm_num) (mul_ne_zero h1 h2)

theorem hT_swap {S : HSp D} {x y : S.V} {c : D.host.E} (h : S.hT x y = c) : S.hT y x = star c := by
  rw [← h]; exact (S.herm.eq x y).symm

def memberDatum (D : D7) (u : D.what₂.Word) : BesselDatum (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) where
  isom := D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega)
  ρ := D.R.rS
  rank_eq := by
    rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.X_rank 0 (Nat.zero_le _)]
    have h1 := D.R.two_le_m
    obtain ⟨c, hc⟩ := D.R.m_even
    simp only [Ranks.rankY, Ranks.r, Ranks.N, Ranks.rS]
    omega
  e := D.sp.hypE
  f := D.sp.hypF
  z := D.zmOf u
  ee := fun i j => D.sp.hyp_ee j i
  ff := fun i j => D.sp.hyp_ff j i
  ef := fun i j => by
    have := hT_swap (D.sp.hyp_ef i j)
    unfold HSpace.hD
    rw [this]; split_ifs <;> simp
  eA := fun i x => (D.sp.hyp_orthX i x).1
  fA := fun i x => (D.sp.hyp_orthX i x).2
  zA := fun x => by
    unfold HSpace.hD D7.zmOf
    rw [map_smul, D.sp.zm_orth, smul_zero]
  ez := fun i => by
    unfold HSpace.hD D7.zmOf
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, (D.sp.hyp_orthz i).1, smul_zero]
  fz := fun i => by
    unfold HSpace.hD D7.zmOf
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, (D.sp.hyp_orthz i).2, smul_zero]
  zz := by
    unfold HSpace.hD D7.zmOf
    rw [map_smul, LinearMap.map_smulₛₗ (D.sp.Y 0).hT, LinearMap.smul_apply, D.sp.zm_norm]
    have hc := D.cOf_ne u
    have hT : (D.sp.T : D.host.E) ≠ 0 := by exact_mod_cast D.sp.T_prime.ne_zero
    simp [hc, hT]
  θ := D.host.xi0
  θ_ne := embedding_xi_zero_ne_zero D

theorem odd_codim {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesselDatum A B ι) : Odd (B.rank - A.rank) :=
  ⟨d.ρ, by rw [d.rank_eq]; omega⟩

def PlaceDivides (D : D7) (ε : AE D) (π : 𝓞 D.host.E) : Prop :=
  π ≠ 0 ∧ finPart D (ε * incA D (π : D.host.E)⁻¹) ∉ intAE D

def IsNormGen (D : D7) (π : 𝓞 D.host.E) (p : ℕ) : Prop :=
  (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (p : D.host.E)

structure BesselTied (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T)
    (piT : D.what₂.Word → 𝓞 D.host.E) (piGbar : Fin 2 → 𝓞 D.host.E) where
  piT_norm : ∀ u, IsNormGen D (piT u) (D.mem u).A.T
  piGbar_norm : ∀ i, IsNormGen D (piGbar i) (D.host.g i)

  dat : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → Odd (B.rank - A.rank) →
    X.Pos A B ι → PosDatum A B ι

  dat_surj : ∀ A B ι h h', Function.Surjective (dat A B ι h h')

  per : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (h : HSpace.IsIsomEmb A B ι) (h' : Odd (B.rank - A.rank))
    (p : X.Pos A B ι), A.SigOK → ∀ μ 𝓕, IsVolPair D A μ 𝓕 →
    ∀ ν 𝓝, (dat A B ι h h' p).bes.IsUnitPair ν 𝓝 →
    ∀ s : GA D A → GA D B, (∀ g, EmbRel B A ι (s g) g) →
    ∀ (σ : X.FJd A B ι) (φ : X.AF A) (F : X.cusp B),
      (dat A B ι h h' p).bes.Converges Wl.ψ μ 𝓕 ν 𝓝 s (fun g => star (T.ev A φ g)) (T.ev B (F : X.AF B)) →
      X.Bper A B ι p σ φ F = (T.petC A : ℂ) *
        (dat A B ι h h' p).period Wl.ψ μ 𝓕 ν 𝓝 s (fun g => star (T.ev A φ g)) (T.ev B (F : X.AF B))

  posSym : ∀ u, dat _ _ _ (memberDatum D u).isom (odd_codim (memberDatum D u)) (X.posSym u) =
    PosDatum.sym (memberDatum D u)

  pos_bessel_eq_memberDatum : ∀ u, (dat _ _ _ (memberDatum D u).isom (odd_codim (memberDatum D u)) (X.pos1 u)).bes = memberDatum D u

  pos_bessel_p_eq_one : ∀ u a, (dat _ _ _ (memberDatum D u).isom (odd_codim (memberDatum D u)) (X.pos1 u)).p a = 1

  pos_split_places : ∀ u ε, IsSplitIdem D ε →
    ((∃ a, (dat _ _ _ (memberDatum D u).isom (odd_codim (memberDatum D u)) (X.pos1 u)).ε a = ε) ↔
      (PlaceDivides D ε (piT u) ∨ ∃ i, PlaceDivides D ε (piGbar i)))

def NSetIsGroup (D : D7) : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι),
    (d.N : Set (GA D B)) = d.NSet ∧ ∀ ε i, IsSplitIdem D ε → (d.Ex ε i : Set (GA D B)) = d.ExSet ε i

def PsiNIsChar (D : D7) : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ),
    IsCharAF D.host.F ψ →
    (∀ n ∈ d.N, ∀ n' ∈ d.N, d.psiN ψ (n * n') = d.psiN ψ n * d.psiN ψ n') ∧
    (∀ n ∈ d.N, n ∈ GQ B → d.psiN ψ n = 1) ∧
    ∀ g h, EmbRel B A ι g h → ∀ n ∈ d.N, g * n * g⁻¹ ∈ d.N ∧ d.psiN ψ (g * n * g⁻¹) = d.psiN ψ n

def FramesExist (D : D7) : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι),
    (∃ ν 𝓝, d.IsUnitPair ν 𝓝) ∧ ∀ h, ∃! g, EmbRel B A ι g h

def ConvergesDef (D : D7) : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ),
    IsCharAF D.host.F ψ → A.SigOK → A.IsDefinite → ∀ μ 𝓕, IsVolPair D A μ 𝓕 → ∀ ν 𝓝, d.IsUnitPair ν 𝓝 →
    ∀ s : GA D A → GA D B, (∀ g, EmbRel B A ι (s g) g) →
    ∀ φ F, IsAutFun A φ → IsAutFun B F → d.Converges ψ μ 𝓕 ν 𝓝 s φ F

def ExchangeFinite (D : D7) : Prop :=
  ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (P : PosDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ),
    IsStdChar D ψ (-1) → A.SigOK → ∀ μ 𝓕, IsVolPair D A μ 𝓕 → ∀ ν 𝓝, P.bes.IsUnitPair ν 𝓝 →
    ∀ s : GA D A → GA D B, (∀ g, EmbRel B A ι (s g) g) →
    ∀ φ F, IsAutFun A φ → IsAutFun B F → P.bes.Converges ψ μ 𝓕 ν 𝓝 s φ F →
    ∀ ε, IsSplitIdem D ε → (∀ a, (ε + cA D ε) * (P.ε a + cA D (P.ε a)) = 0) →
    ∀ m : ∀ i, Measure (P.bes.Ex ε i), (∀ i, (m i).IsHaarMeasure) → ∀ i : Fin (P.bes.ρ + 1), 1 ≤ i.1 →
      IsLocallyConstant (fun u : P.bes.Ex ε i =>
        P.bes.toPos ε m (i.1 + 1) (P.period ψ μ 𝓕 ν 𝓝 s φ) (rTr B (u : GA D B) F)) ∧
      HasCompactSupport (fun u : P.bes.Ex ε i =>
        P.bes.toPos ε m (i.1 + 1) (P.period ψ μ 𝓕 ν 𝓝 s φ) (rTr B (u : GA D B) F))

end GlobalTheory.IndefiniteRowSideFullHecke.BesselData

end
