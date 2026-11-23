import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.SegRing
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.ConclusionA2

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas

open Formalism.MainNotions.G

def Conclusion2 (_D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  ∀ (p n' : ℕ) [NeZero n'] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jW : W →+* O) (w : O),
  UnramifiedQuadraticSetting p n' W Qq O Kf ι σ jW w → 13 ≤ p →
  ∀ (r K : ℕ) [NeZero r] [NeZero K], 2 ≤ r →
  ∀ (F : Frames n' r) (deg : Fin n' → ℕ) (L₁ N₁ Ns E₀ mStar : ℕ) (E' : Fin n' → ℕ) (a Y Q : ℝ),
  F.Valid L₁ N₁ →
  (∀ t ∈ F.TT, a ≤ (deg t : ℝ) ∧ (deg t : ℝ) ≤ 2 * a) →
  (∀ j : ℤ, (F.letters j).card ≤ Ns) → Ns ≤ N₁ → Ns ≤ 2 * F.TT.card → Ns + r ≤ K →
  (∀ j : ℤ, ∀ x ∈ F.letters j, (p : ℝ) ^ F.dist j x ≤ Q) →
  1 ≤ Y →
  Ck * (Ns : ℝ) ^ 2 * Real.log a ≤ ((r + K : ℕ) : ℝ) →
  128 * ((r + K : ℕ) : ℝ) ^ 2 * (Ns : ℝ) * Y ^ 2 ≤ (p : ℝ) ^ ((L₁ : ℤ) - 1) →
  (∀ t ∈ F.TT, E' t ≤ E₀) →
  32 * (p : ℝ) * Y * ((r + K : ℕ) : ℝ) ^ 2 * (Ns : ℝ) * Q ^ 2 * ((E₀ : ℝ) + mStar + 1) ≤ a →
  let k : ℝ := ((r + K : ℕ) : ℝ)
  let La : ℝ := CLa * (Ns : ℝ) ^ 2 * Real.log a
  let Bo : ℤ → ℤ → ℝ := fun j x =>
    (deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x)
  let mg : ℤ → ℤ → ℤ := fun j x => (mStar : ℤ) + (⌊Bo j x / (k ^ 2 * Y)⌋₊ : ℤ)
  let th : ℤ → ℤ → ℝ := fun j x => Bo j x / 2
  let o : ℤ → ℤ → ℝ := fun j x =>
    La * a / ((p : ℝ) * k * (p : ℝ) ^ F.dist j x) +
      (if Even x then (10 : ℝ) else 1) * a * (p : ℝ) ^ (-((L₁ : ℤ) + (F.dist j x : ℤ)))
  let d : Fin n' → ℕ := fun t => if t ∈ F.TT then deg t - E' t else 0
  let XXs : ℤ → Submodule O (SegRing O r K) := fun j => XX' O r K F j (mg j) (th j) (o j)
  let NN : Submodule O (RRing O n' (r + K)) := Submodule.span O (Gen O p K F XXs d)
  let bound : ℝ := (1 - Crk * (F.TT.card : ℝ) * (r : ℝ) ^ 2 * k / Y) *
    ∏ t ∈ F.TT, ((Nat.choose (deg t + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)
  (∃ Sg : Submodule O (RRing O n' (r + K)), Sg ≤ NN ∧ (∃ T : Submodule O (RRing O n' (r + K)), IsCompl Sg T) ∧
      (∃ (ιb : Type) (b : Module.Basis ιb O Sg), ∀ i, (b i : RRing O n' (r + K)) ∈ Gen O p K F XXs d) ∧
      ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * bound ≤ (Module.finrank O Sg : ℝ) ∧
      ∀ (FF : Type) [Field FF] [Fintype FF], Fintype.card FF = p ^ n' →
        bound / (nPl FF (r + K) r : ℝ) ≤ (Module.finrank O Sg : ℝ)) ∧
  ∀ P ∈ NN, ∀ mm ∈ P.support,
    (vsDeg mm : ℝ) ≤ Cdeg * (F.TT.card : ℝ) * (La * a / ((p : ℝ) * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + k * Q)

def PathPairCorrespondence (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n' : ℕ) [NeZero n'] (TT : Finset (Fin n')) (r L₁ L₂ u M₀ G' N₁ : ℕ),
    Even n' → 2 ≤ r → L₁ ≤ L₂ → L₂ < u → G' = (M₀ + 5) * ((6 * r + 1) * u) → 3 * G' ≤ n' →
    Formalism.G0.GoodOrbitIntervalTileCondition n' (TT.map Fin.valEmbedding) L₂ (r - 1) r u M₀ G' N₁ →
    ∃ F : Frames n' r, F.TT = TT ∧ F.Valid L₁ N₁ ∧
      (∀ j : ℤ, ∃ s < n' / ((6 * r + 1) * u), Formalism.G0.Marked (TT.map Fin.valEmbedding) r u s ∧
        ∀ i < r, (F.fr j i % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2 + 2 * i)) ∧
      (∀ s < n' / ((6 * r + 1) * u), Formalism.G0.Marked (TT.map Fin.valEmbedding) r u s →
        ∃ j : ℤ, (F.fr j 0 % (n' : ℤ)).toNat ∈ Formalism.G0.cell r u s (2 * r + 2))

def admB2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ι : Type) (n : ℕ) [NeZero n]
    (LL : Letters ι) (S : Set ι),
    (∀ F G : MvPolynomial (ι × Fin n) O,
      valS LL S (F * G) = valS LL S F + valS LL S G ∧ min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) ∧
      lam1S LL S (F * G) = lam1S LL S F + lam1S LL S G ∧
      lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G)) ∧
    (∀ l ∈ S, ∀ c : Fin n,
      (LL.vec l = true → (0 : WithTop ℤ) ≤ valS LL S (X (l, c) : MvPolynomial (ι × Fin n) O) ∧
          lam1S LL S (X (l, c) : MvPolynomial (ι × Fin n) O) ≤ (1 : WithBot ℤ)) ∧
      (LL.vec l = false → (-1 : WithTop ℤ) ≤ valS LL S (X (l, c) : MvPolynomial (ι × Fin n) O) ∧
          lam1S LL S (X (l, c) : MvPolynomial (ι × Fin n) O) ≤ (0 : WithBot ℤ))) ∧
    (∀ y : Fin n → ι, Function.Injective y → (∀ i, y i ∈ S ∧ LL.vec (y i) = true) →
      valS LL S (Matrix.det (Matrix.of fun a b : Fin n => (X (y a, b) : MvPolynomial (ι × Fin n) O))) = 1)

def stCount (n : ℕ) (mu : Fin n → ℤ) : ℕ :=
  Nat.card {I : ℤ → Finset (Fin n) // IsSt (N := 0) (fun _ => mu) I}

def admB3 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n N : ℕ) (mu : Fin (N + 1) → Fin n → ℤ), Dominant (pEnd mu) →
    ((Nat.card {I : ℤ → Finset (Fin n) // IsSt mu I} : ℕ) : ℚ) = ∏ i : Fin n, ∏ j : Fin n,
      if i < j then (((pEnd mu i : ℤ) : ℚ) - ((pEnd mu j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1

def ColumnFamilyLowerSet (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (m : ℕ) (ν : Fin (m + 1) → ℤ), Dominant ν →
    stCount (m + 1) ν =
      ∑ μ ∈ Fintype.piFinset (fun i : Fin m => Finset.Icc (ν i.succ) (ν i.castSucc)), stCount m μ

open Classical in

def GenericProjectionCriterion (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (m : ℕ) (ν : Fin (m + 1) → ℤ) (b : ℕ), Dominant ν →
    (stCount (m + 1) ν * Nat.choose (b + m) m =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin (m + 1) => Finset.Icc (ν i) (ν i + b)).filter (fun μ => HStrip ν μ b),
        stCount (m + 1) μ) ∧
    (stCount (m + 1) ν * Nat.choose (b + m) m =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin (m + 1) => Finset.Icc (ν i - b) (ν i)).filter (fun μ => HStrip μ ν b),
        stCount (m + 1) μ)

def ColumnFamilyClosure (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (FF : Type) [Field FF] [Fintype FF] (k r : ℕ), r ≤ k → Fintype.card FF ^ (r * (k - r)) ≤ nPl FF k r

def TensorColumnFamily (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.HyperplaneRank D

def BranchingColumnFamily (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D

def GlobalSectionsSchur (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D

def BracketPolynomialSpan (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.RotatedSumBound D

def GradedLatticeStable (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ConclusionB3 D

section Seg

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ)

def segN : ℕ := (F.letters j).card

def segE (i : Fin (segN F j)) : ℤ := ((F.letters j).orderIsoOfFin rfl i : ℤ)

def segLL : Letters (Fin (segN F j)) := ⟨fun i => LZ.vec (segE F j i)⟩

def segRen (R : Type*) [CommRing R] (k : ℕ) :
    MvPolynomial (Fin (segN F j) × Fin k) R →ₐ[R] MvPolynomial (ℤ × Fin k) R :=
  rename fun v => (segE F j v.1, v.2)

def segPairsAll (K : ℕ) : Set ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) :=
  {q | ∃ b' b'' : Fin (segN F j) → ℕ, (∃ P1 : PPath r (segN F j) (segLL F j) b', P1.mu = q.1) ∧
      ∃ P2 : PPath K (segN F j) (segLL F j) b'', P2.mu = q.2}

def segPairs [NeZero r] (K : ℕ) [NeZero K] (m : ℤ → ℤ) (th o : ℤ → ℝ) :
    Set ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) :=
  {q | ∃ b' b'' : Fin (segN F j) → ℕ, (∃ P1 : PPath r (segN F j) (segLL F j) b', P1.mu = q.1) ∧
      (∃ P2 : PPath K (segN F j) (segLL F j) b'', P2.mu = q.2) ∧
      ∀ i : Fin (segN F j),
        (F.IsW j (segE F j i) → b'' i = 0) ∧
        (¬ F.IsW j (segE F j i) →
          (Even (segE F j i) → q.2 i.succ 0 + m (segE F j i) ≤ q.1 i.castSucc (lastIdx r) ∧
            (b'' i : ℝ) ≤ o (segE F j i)) ∧
          (¬ Even (segE F j i) → q.2 i.castSucc 0 + m (segE F j i) ≤ q.1 i.succ (lastIdx r) ∧
            (b' i : ℝ) ≤ o (segE F j i)) ∧
          th (segE F j i) ≤ ((q.1 i.castSucc (lastIdx r) : ℤ) : ℝ))}

end Seg

def NestedTypeBound (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K]
    (F : Frames n' r) (L₁ N₁ : ℕ) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ),
  F.Valid L₁ N₁ → segN F j + r ≤ K → (∀ x, 0 ≤ m x) →
  XX' O r K F j m th o =
    Submodule.map (segRen F j O (r + K)).toLinearMap (Formalism.MainNotions.CovariantDegrees.XXZ O (segPairs F j K m th o)) ∧
  LinearIndependent O (fun x : {x : ((Fin (segN F j + 1) → Fin r → ℤ) × (Fin (segN F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} =>
      segRen F j O (r + K) (PsiPl O x.1.1.1 x.1.2.1 * PsiTan O x.1.1.2 x.1.2.2)) ∧
  Formalism.MainNotions.CovariantDegrees.Saturated (XX' O r K F j m th o) ∧
  (CharZero O → (XX' O r K F j m th o : Set (SegRing O r K)) =
    {f | MvPolynomial.map (algebraMap O (KK O)) f ∈ Submodule.map (segRen F j (KK O) (r + K)).toLinearMap
      (⨆ q ∈ segPairs F j K m th o, Formalism.MainNotions.CovariantDegrees.jointType (KK O) (segLL F j) q.1 q.2)}) ∧
  (∀ (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ),
    A ∈ supported O {v : ℤ × Fin r | v.1 ∈ F.letters j} →
    G ∈ supported O {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} →
    (∀ x ∈ F.letters j, ¬ F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x)) →
    (∀ mm ∈ (plEmb O r K A * nmEmb O r K G).support, ∀ x ∈ F.letters j, ¬ F.IsW j x → (ordDeg mm x : ℝ) ≤ o x) →
    plEmb O r K A * nmEmb O r K G ∈ XX' O r K F j m th o) ∧
  (∀ (A : MvPolynomial (ℤ × Fin r) (FF O)) (G : MvPolynomial (ℤ × Fin K) (FF O)) (M : ℤ → ℤ),
    A ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ F.letters j} →
    G ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1} →
    (∀ x ∈ F.letters j, ¬ F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x)) →
    (∀ mm ∈ (plEmb (FF O) r K A * nmEmb (FF O) r K G).support, ∀ x ∈ F.letters j, ¬ F.IsW j x →
      (ordDeg mm x : ℝ) ≤ o x) →
    ∃ P ∈ XX' O r K F j m th o,
      MvPolynomial.map (IsLocalRing.residue O) P = plEmb (FF O) r K A * nmEmb (FF O) r K G)

def TypeDecompositionsCommute (_D : Formalism.BasicNotions.D7) : Prop :=
  (∀ (R : Type) [CommRing R] (ι κ : Type) (f : ι → κ) (n : ℕ) [NeZero n] (LL : Letters κ) (S : Set κ)
      (A : MvPolynomial (ι × Fin n) R), Function.Injective f →
    valS LL S (rename (fun v : ι × Fin n => (f v.1, v.2)) A) =
        valS (⟨fun i => LL.vec (f i)⟩ : Letters ι) (f ⁻¹' S) A ∧
      lam1S LL S (rename (fun v : ι × Fin n => (f v.1, v.2)) A) =
        lam1S (⟨fun i => LL.vec (f i)⟩ : Letters ι) (f ⁻¹' S) A) ∧
  (∀ (O : Type) [CommRing O] [IsDomain O] (ι : Type) (n : ℕ) [NeZero n] (LL : Letters ι) (S : Set ι)
      (A : MvPolynomial (ι × Fin n) O),
    valS LL S (MvPolynomial.map (algebraMap O (KK O)) A) = valS LL S A ∧
      lam1S LL S (MvPolynomial.map (algebraMap O (KK O)) A) = lam1S LL S A)

theorem twistSub_rename {R : Type} [CommRing R] {ι κ : Type} (f : ι → κ) {n : ℕ} (LL : Letters κ) (S : Set κ)
    (j : Fin n) (A : MvPolynomial (ι × Fin n) R) :
    twistSub LL S j (rename (fun v : ι × Fin n => (f v.1, v.2)) A) =
      rename (fun v : ι × Fin n => (f v.1, v.2)) (twistSub (⟨fun i => LL.vec (f i)⟩ : Letters ι) (f ⁻¹' S) j A) := by
  have h : (twistSub (R := R) LL S j).comp (rename (fun v : ι × Fin n => (f v.1, v.2))).toRingHom =
      (rename (fun v : ι × Fin n => (f v.1, v.2))).toRingHom.comp
        (twistSub (R := R) (⟨fun i => LL.vec (f i)⟩ : Letters ι) (f ⁻¹' S) j) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [twistSub]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, twistSub,
        eval₂Hom_X', Set.mem_preimage]
      split_ifs <;> simp_all [map_sum, rename_X]
  exact RingHom.congr_fun h A

theorem sDegs_rename {R : Type} [CommRing R] {ι κ : Type} (f : ι → κ) (hf : Function.Injective f) {n : ℕ}
    (LL : Letters κ) (S : Set κ) (j : Fin n) (A : MvPolynomial (ι × Fin n) R) :
    sDegs LL S j (rename (fun v : ι × Fin n => (f v.1, v.2)) A) =
      sDegs (⟨fun i => LL.vec (f i)⟩ : Letters ι) (f ⁻¹' S) j A := by
  classical
  unfold sDegs
  rw [twistSub_rename f LL S j A]
  have hg : Function.Injective (fun v : ι × Fin n => (f v.1, v.2)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hf h.1) h.2
  rw [MvPolynomial.support_rename_of_injective hg, Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro m _
  rw [MvPolynomial.coeff_rename_mapDomain _ hg]

theorem valuation_lowest_degree_rename (R : Type) [CommRing R] (ι κ : Type) (f : ι → κ) (n : ℕ) [NeZero n] (LL : Letters κ) (S : Set κ)
      (A : MvPolynomial (ι × Fin n) R) (hf : Function.Injective f) :
    valS LL S (rename (fun v : ι × Fin n => (f v.1, v.2)) A) =
        valS (⟨fun i => LL.vec (f i)⟩ : Letters ι) (f ⁻¹' S) A ∧
      lam1S LL S (rename (fun v : ι × Fin n => (f v.1, v.2)) A) =
        lam1S (⟨fun i => LL.vec (f i)⟩ : Letters ι) (f ⁻¹' S) A := by
  refine ⟨?_, ?_⟩
  · unfold valS
    rw [sDegs_rename f hf]
  · unfold lam1S
    rw [sDegs_rename f hf]

theorem space_criterion_clause (O : Type) [CommRing O] (n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K]
    (F : Frames n' r) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ)
    (A : MvPolynomial (ℤ × Fin r) O) (G : MvPolynomial (ℤ × Fin K) O) (M : ℤ → ℤ)
    (hA : A ∈ supported O {v : ℤ × Fin r | v.1 ∈ F.letters j})
    (hG : G ∈ supported O {v : ℤ × Fin K | v.1 ∈ F.letters j ∧ ¬ F.IsW j v.1})
    (hc : ∀ x ∈ F.letters j, ¬ F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} A) ∧
      (¬ Even x → lam1S LZ {y | y < x} G ≤ ((M x : ℤ) : WithBot ℤ) ∧
          ((M x + m x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} A) ∧
      geR (valS LZ {y | y < x} A) (th x))
    (ho : ∀ mm ∈ (plEmb O r K A * nmEmb O r K G).support, ∀ x ∈ F.letters j, ¬ F.IsW j x → (ordDeg mm x : ℝ) ≤ o x) :
    plEmb O r K A * nmEmb O r K G ∈ XX' O r K F j m th o := by
  unfold XX'
  rw [Submodule.mem_inf]
  refine ⟨Submodule.subset_span ⟨A, G, M, hA, hG, hc, rfl⟩, ?_⟩
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm
  exact ho mm hmm

def AdmB (D : Formalism.BasicNotions.D7) : Prop :=
  PathPairCorrespondence D ∧ admB2 D ∧ admB3 D ∧ ColumnFamilyLowerSet D ∧ GenericProjectionCriterion D ∧ ColumnFamilyClosure D ∧ TensorColumnFamily D ∧ BranchingColumnFamily D ∧ GlobalSectionsSchur D ∧ BracketPolynomialSpan D ∧ GradedLatticeStable D ∧
    NestedTypeBound D ∧ TypeDecompositionsCommute D

def HodgeTateFromSandwich (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop := AdmB D → Conclusion2 D CLa Ck Crk Cdeg

def SecondPartClosed (D : Formalism.BasicNotions.D7) : Prop :=
  AdmB D → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ CLa Ck : ℝ, C₀ ≤ CLa → C₀ ≤ Ck →
    ∃ Crk Cdeg : ℝ, 0 < Crk ∧ 0 < Cdeg ∧ Conclusion2 D CLa Ck Crk Cdeg

def Conclusion2Family (CLa Ck Crk Cdeg : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) CLa Ck Crk Cdeg

def AdmBF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), AdmB (Fm.D x i)

def SecondPartFamily (CLa Ck Crk Cdeg : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  AdmBF Fm → Conclusion2Family CLa Ck Crk Cdeg Fm

def SecondPartFamilyClosed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  AdmBF Fm → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ CLa Ck : ℝ, C₀ ≤ CLa → C₀ ≤ Ck →
    ∃ Crk Cdeg : ℝ, 0 < Crk ∧ 0 < Cdeg ∧ Conclusion2Family CLa Ck Crk Cdeg Fm

def PlaneCountTheoremDesign (Fm : Formalism.MainNotions.DFamP) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ CLa Ck : ℝ, C₀ ≤ CLa → C₀ ≤ Ck → ∃ Crk Cdeg : ℝ, 0 < Crk ∧ 0 < Cdeg ∧
    ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), Conclusion2Family CLa Ck Crk Cdeg (Fm ε h0 h1)

def AdmBDF (Fm : Formalism.MainNotions.DFamP) : Prop :=
  ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), AdmBF (Fm ε h0 h1)

def PlaneCountDesignStatement (Fm : Formalism.MainNotions.DFamP) : Prop := AdmBDF Fm → PlaneCountTheoremDesign Fm

end Formalism.MainNotions.SelectionLemmas
