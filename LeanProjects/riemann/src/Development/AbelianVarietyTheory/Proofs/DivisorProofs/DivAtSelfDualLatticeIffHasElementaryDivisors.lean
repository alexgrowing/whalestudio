import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin

noncomputable section

namespace GlobalTheory.DivTransfer

open scoped Matrix
open Formalism.UG

section Local

variable {K : Type} [Field K] {n : ℕ} {O : Subring K}

theorem exists_mat {A C : Matrix (Fin n) (Fin n) K}
    (h : ∀ w : Fin n → K, (∀ i, w i ∈ O) → ∃ z : Fin n → K, (∀ i, z i ∈ O) ∧ A *ᵥ w = C *ᵥ z) :
    ∃ H : Matrix (Fin n) (Fin n) K, (∀ i j, H i j ∈ O) ∧ A = C * H := by
  have h1 : ∀ j : Fin n, ∀ i, (Pi.single j 1 : Fin n → K) i ∈ O := fun j i => by
    by_cases e : i = j
    · subst e; simp
    · simp [e]
  choose z hz ez using fun j => h _ (h1 j)
  refine ⟨Matrix.of fun i j => z j i, fun i j => hz j i, Matrix.ext fun i j => ?_⟩
  have := congrFun (ez j) i
  rw [Matrix.mulVec_single_one] at this
  exact this

theorem mulVec_mem {A : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ O) {z : Fin n → K} (hz : ∀ i, z i ∈ O) (i : Fin n) :
    (A *ᵥ z) i ∈ O :=
  Subring.sum_mem (t := Finset.univ) _ fun j _ => mul_mem (hA i j) (hz j)

theorem exists_GLint {g g' : Matrix (Fin n) (Fin n) K} (hg : ∀ i j, g i j ∈ O) (hg' : ∀ i j, g' i j ∈ O)
    (h : g * g' = 1) : ∃ a ∈ GLint (Fin n) O, (a : Matrix (Fin n) (Fin n) K) = g := by
  let G : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨g i j, hg i j⟩
  let G' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨g' i j, hg' i j⟩
  have e : G * G' = 1 := by
    apply Matrix.map_injective (f := O.subtype) O.subtype_injective
    change (G * G').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact h
  exact ⟨_, ⟨⟨G, G', e, mul_eq_one_comm.1 e⟩, rfl⟩, rfl⟩

theorem entry_mem {a : GL (Fin n) K} (ha : a ∈ GLint (Fin n) O) (i j : Fin n) :
    (a : Matrix (Fin n) (Fin n) K) i j ∈ O := by
  obtain ⟨b, rfl⟩ := ha
  exact ((b : Matrix (Fin n) (Fin n) O) i j).2

def LocBasis (O : Subring K) (x : Matrix (Fin n) (Fin n) K) (τ : Fin n → K) (g : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ z : Fin n → K, (∀ i, z i ∈ O) → ∀ i, (g *ᵥ z) i ∈ O) ∧
  (∀ w : Fin n → K, (∀ i, w i ∈ O) → ∃ z : Fin n → K, (∀ i, z i ∈ O) ∧ w = g *ᵥ z) ∧
  (∀ w : Fin n → K, (∀ i, w i ∈ O) → ∃ z : Fin n → K, (∀ i, z i ∈ O) ∧ x *ᵥ w = g *ᵥ fun i => τ i * z i) ∧
  (∀ z : Fin n → K, (∀ i, z i ∈ O) → ∃ w : Fin n → K, (∀ i, w i ∈ O) ∧ x *ᵥ w = g *ᵥ fun i => τ i * z i)

theorem mulVec_diag (g : Matrix (Fin n) (Fin n) K) (τ z : Fin n → K) :
    (g *ᵥ fun i => τ i * z i) = (g * Matrix.diagonal τ) *ᵥ z := by
  rw [← Matrix.mulVec_mulVec]
  congr 1
  exact funext fun i => (Matrix.mulVec_diagonal _ _ i).symm

theorem locBasis_iff (x : Matrix (Fin n) (Fin n) K) {τ : Fin n → K} (hτ : ∀ i, τ i ≠ 0) :
    (∃ g, LocBasis O x τ g) ↔ ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
      x = (a : Matrix (Fin n) (Fin n) K) * Matrix.diagonal τ * (b : Matrix (Fin n) (Fin n) K) := by
  constructor
  · rintro ⟨g, h1, h2, h3, h4⟩
    simp only [mulVec_diag] at h3 h4
    obtain ⟨g₀, hg, e0⟩ := exists_mat (O := O) (A := g) (C := 1) fun w hw => ⟨_, h1 w hw, by simp⟩
    rw [one_mul] at e0
    subst e0
    obtain ⟨g', hg', e1⟩ := exists_mat (O := O) (A := 1) (C := g) fun w hw => by simpa using h2 w hw
    obtain ⟨h, hh, e2⟩ := exists_mat h3
    obtain ⟨h', hh', e3⟩ := exists_mat (O := O) (A := g * Matrix.diagonal τ) (C := x) fun w hw =>
      (h4 w hw).imp fun z hz => ⟨hz.1, hz.2.symm⟩
    have hd : Matrix.diagonal (fun i => (τ i)⁻¹) * Matrix.diagonal τ = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      exact funext fun i => inv_mul_cancel₀ (hτ i)
    have e1' : g' * g = 1 := mul_eq_one_comm.1 e1.symm
    have hl : (Matrix.diagonal (fun i => (τ i)⁻¹) * g') * (g * Matrix.diagonal τ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc g', e1', one_mul, hd]
    have e4 : h * h' = 1 := by
      rw [← one_mul (h * h'), ← hl, Matrix.mul_assoc, ← Matrix.mul_assoc _ h, ← e2, ← e3]
    obtain ⟨a, ha, rfl⟩ := exists_GLint hg hg' e1.symm
    obtain ⟨b, hb, rfl⟩ := exists_GLint hh hh' e4
    exact ⟨a, ha, b, hb, e2⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, fun z hz => mulVec_mem (entry_mem ha) hz, fun w hw => ⟨_, mulVec_mem (entry_mem (inv_mem ha)) hw, ?_⟩,
      fun w hw => ⟨_, mulVec_mem (entry_mem hb) hw, ?_⟩, fun z hz => ⟨_, mulVec_mem (entry_mem (inv_mem hb)) hz, ?_⟩⟩
    · rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    · rw [mulVec_diag, Matrix.mulVec_mulVec]
    · rw [mulVec_diag, Matrix.mulVec_mulVec, Matrix.mul_assoc _ b.1, Units.mul_inv, mul_one]

end Local

theorem basis_iff_locBasis {R K : Type} [CommRing R] [Field K] {n : ℕ} (π : R →+* K) (s : K → R)
    (hs : ∀ x, π (s x) = x) {ε : R} (hε : ∀ y, ε * y = s (π y)) {I : R → Prop} {O : Subring K}
    (hI : ∀ y, I y → π y ∈ O) (hI' : ∀ x ∈ O, I (s x)) {Λ : (Fin n → R) → Prop}
    {N N' X : Matrix (Fin n) (Fin n) R} (hN : N * N' = 1) (hΛ : ∀ y, Λ y ↔ ∀ i, I ((N' *ᵥ y) i)) (t : Fin n → R) :
    (∃ B : Matrix (Fin n) (Fin n) R,
      (∀ z, (∀ i, I (z i)) → Λ fun i => ε * B.mulVec z i) ∧
      (∀ y, Λ y → ∃ z, (∀ i, I (z i)) ∧ (fun i => ε * y i) = fun i => ε * B.mulVec z i) ∧
      (∀ y, Λ y → ∃ z : Fin n → R, (∀ i, I (z i)) ∧
        (fun i => ε * (N * X * N').mulVec y i) = fun i => ε * B.mulVec (fun j => t j * z j) i) ∧
      (∀ z : Fin n → R, (∀ i, I (z i)) → ∃ y, Λ y ∧
        (fun i => ε * (N * X * N').mulVec y i) = fun i => ε * B.mulVec (fun j => t j * z j) i)) ↔
    ∃ g, LocBasis O (X.map π) (fun i => π (t i)) g := by
  have hN' : N' * N = 1 := mul_eq_one_comm.1 hN
  have hv : ∀ (A : Matrix (Fin n) (Fin n) R) z, (fun i => π (A.mulVec z i)) = (A.map π *ᵥ fun j => π (z j)) :=
    fun A z => funext fun i => RingHom.map_mulVec π A z i
  have hsm : ∀ (A : Matrix (Fin n) (Fin n) R) y i, (A *ᵥ fun i => ε * y i) i = ε * (A *ᵥ y) i := fun A y i =>
    congrFun (Matrix.mulVec_smul A ε y) i
  have heq : ∀ y y' : Fin n → R, ((fun i => ε * y i) = fun i => ε * y' i) ↔
      (fun i => π ((N' *ᵥ y) i)) = fun i => π ((N' *ᵥ y') i) := fun y y' => by
    constructor
    · intro h
      funext i
      rw [← hs (π _), ← hε, ← hsm, h, hsm, hε, hs]
    · intro h
      have h2 : (fun i => ε * (N' *ᵥ y) i) = fun i => ε * (N' *ᵥ y') i := by
        funext i
        rw [hε, hε, congrFun h i]
      funext i
      have := congrFun (congrArg (N *ᵥ ·) h2) i
      simpa only [hsm, Matrix.mulVec_mulVec, hN, Matrix.one_mulVec] using this
  have hΛε : ∀ y : Fin n → R, Λ (fun i => ε * y i) ↔ ∀ i, π ((N' *ᵥ y) i) ∈ O := fun y => by
    rw [hΛ]
    refine forall_congr' fun i => ?_
    rw [hsm, hε]
    exact ⟨fun h => hs (π _) ▸ hI _ h, hI' _⟩
  have hc : ∀ y, N' *ᵥ (N *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hN', Matrix.one_mulVec]
  have hΛs : ∀ w : Fin n → K, (∀ i, w i ∈ O) → Λ (N *ᵥ fun i => s (w i)) := fun w hw => by
    rw [hΛ, hc]
    exact fun i => hI' _ (hw i)
  have hX : ∀ y, (fun i => π ((N' *ᵥ ((N * X * N') *ᵥ y)) i)) = X.map π *ᵥ fun i => π ((N' *ᵥ y) i) := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, hv]
  have hB : ∀ (B : Matrix (Fin n) (Fin n) R) z,
      (fun i => π ((N' *ᵥ (B *ᵥ z)) i)) = (N' * B).map π *ᵥ fun i => π (z i) := fun B z => by
    rw [Matrix.mulVec_mulVec, hv]
  simp only [heq, hΛε, hX, hB, map_mul]
  constructor
  · rintro ⟨B, h1, h2, h3, h4⟩
    refine ⟨(N' * B).map π, fun z hz i => ?_, fun w hw => ?_, fun w hw => ?_, fun z hz => ?_⟩
    · have := h1 _ (fun i => hI' _ (hz i)) i
      rw [congrFun (hB B _) i] at this
      simpa only [hs] using this
    · obtain ⟨z, hz, e⟩ := h2 _ (hΛs w hw)
      refine ⟨_, fun i => hI _ (hz i), ?_⟩
      simpa only [hc, hs] using e
    · obtain ⟨z, hz, e⟩ := h3 _ (hΛs w hw)
      refine ⟨_, fun i => hI _ (hz i), ?_⟩
      simpa only [hc, hs] using e
    · obtain ⟨y, hy, e⟩ := h4 _ (fun i => hI' _ (hz i))
      refine ⟨_, fun i => hI _ ((hΛ y).1 hy i), ?_⟩
      simpa only [hs] using e
  · rintro ⟨g, h1, h2, h3, h4⟩
    have hg : (N' * (N * g.map s)).map π = g := by
      rw [← Matrix.mul_assoc, hN', one_mul]
      exact Matrix.ext fun i j => hs _
    refine ⟨N * g.map s, fun z hz i => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
    · rw [congrFun (hB _ _) i, hg]
      exact h1 _ (fun i => hI _ (hz i)) i
    · obtain ⟨z, hz, e⟩ := h2 _ fun i => hI _ ((hΛ y).1 hy i)
      refine ⟨_, fun i => hI' _ (hz i), ?_⟩
      simpa only [hg, hs] using e
    · obtain ⟨z, hz, e⟩ := h3 _ fun i => hI _ ((hΛ y).1 hy i)
      refine ⟨_, fun i => hI' _ (hz i), ?_⟩
      simpa only [hg, hs] using e
    · obtain ⟨w, hw, e⟩ := h4 _ fun i => hI _ (hz i)
      refine ⟨_, hΛs w hw, ?_⟩
      simpa only [hg, hs, hc] using e

open IsDedekindDomain NumberField in

theorem hasDiv_iff {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) {ϖ : P.adicCompletion E}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : List ℤ) (g : GL (Fin n) (P.adicCompletion E)) :
    GlobalTheory.SphPar.HasDiv (Ov E P) d g ↔ ∃ a ∈ GLint (Fin n) (Ov E P), ∃ b ∈ GLint (Fin n) (Ov E P),
      (g : Matrix (Fin n) (Fin n) (P.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (P.adicCompletion E)) *
        Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) * (b : Matrix (Fin n) (Fin n) (P.adicCompletion E)) := by
  refine ⟨?_, fun h => ⟨ϖ, hϖ, h⟩⟩
  rintro ⟨u, hu, a, ha, b, hb, e⟩
  have hu' : Valued.v u = Valued.v ϖ := hu.trans hϖ.symm
  have h0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hu0 : u ≠ 0 := fun h => by
    rw [h, map_zero] at hu'
    exact (map_ne_zero _).2 h0 hu'.symm
  have hm : ∀ k : ℤ, (u / ϖ) ^ k ∈ Ov E P := fun k => by
    change Valued.v ((u / ϖ) ^ k) ≤ 1
    rw [map_zpow₀, map_div₀, hu', div_self ((map_ne_zero _).2 h0), one_zpow]
  have hd : ∀ (c : Fin n → ℤ) (i j : Fin n), Matrix.diagonal (fun i => (u / ϖ) ^ c i) i j ∈ Ov E P := fun c i j => by
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hm _
    · exact zero_mem _
  obtain ⟨c, hc, ec⟩ := exists_GLint (hd fun i => d.getD i 0) (hd fun i => -d.getD i 0) (by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (div_ne_zero hu0 h0))])
  refine ⟨a, ha, c * b, mul_mem hc hb, ?_⟩
  rw [e, Units.val_mul, ec, ← Matrix.mul_assoc, Matrix.mul_assoc a.1 _ (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  congr 3
  funext i
  rw [← mul_zpow, mul_div_cancel₀ _ h0]

open IsDedekindDomain NumberField in
theorem valued_unif {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {ϖ : 𝓞 E}
    (h1 : ϖ ∈ w.asIdeal) (h2 : ϖ ∉ w.asIdeal ^ 2) :
    Valued.v (algebraMap E (w.adicCompletion E) (ϖ : E)) = WithZero.exp (-1 : ℤ) := by
  have a1 := (w.intValuation_le_pow_iff_mem ϖ 1).2 (by simpa using h1)
  have a2 := mt (w.intValuation_le_pow_iff_mem ϖ 2).1 h2
  have a3 : w.intValuation ϖ ≠ 0 := w.intValuation_ne_zero ϖ fun h => h2 (h ▸ zero_mem _)
  rw [Formalism.UG.P.levelaf_valued_algebraMap, show w.valuation E (ϖ : E) = w.intValuation ϖ from
    w.valuation_of_algebraMap ϖ]
  rw [← WithZero.exp_log a3, WithZero.exp_le_exp] at a1 a2
  rw [← WithZero.exp_log a3]
  congr 1
  omega

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frame_mul {R : Type} [Monoid R] {H H' A A' : R} (hH : H' * H = 1) (hA : A * A' = 1) :
    (H' * A) * (A' * H) = 1 := by
  rw [mul_assoc, ← mul_assoc A, hA, one_mul, hH]

theorem frame_conj {R : Type} [Monoid R] {H H' A A' X Y Z : R} (hZ : Z = H' * Y * H) (hY : Y = A * X * A') :
    Z = (H' * A) * X * (A' * H) := by
  simp only [hZ, hY, mul_assoc]

theorem map_mul_inv {E R : Type} [Field E] [CommRing R] {n : ℕ} (ι : E →+* R) {M M' : Matrix (Fin n) (Fin n) E}
    (h : M' * M = 1) : M.map ι * M⁻¹.map ι = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h),
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem finMat_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g h : HA (AF F) σ J) :
    finMat σ J (g * h) = finMat σ J g * finMat σ J h :=
  Matrix.map_mul (f := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))

theorem finMat_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : finMat σ J (1 : HA (AF F) σ J) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem divAt_iff_of_frame {D : D7} (V : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} {ϖ : 𝓞 D.host.E}
    (d : List ℤ) (hef : IsPrimeIdem P e f) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    {N N' X : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)} (hN : N * N' = 1)
    (hL : ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔ IntVec (N'.mulVec y)) {α : GA D V}
    (hα : finMat D.sp.cm.sig V.gram α = N * X * N') {g : GL (Fin V.rank) (P.adicCompletion D.host.E)}
    (hX : X.map (GlobalTheory.LFun.compAt D.host.F P) = g.1) :
    DivAt V e (ϖ : D.host.E) d α ↔ d.length = V.rank ∧ HasDiv (Ov D.host.E P) d g := by
  have hϖ := valued_unif h1 h2
  have h0 : algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E) ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have key := basis_iff_locBasis (GlobalTheory.LFun.compAt D.host.F P) (GlobalTheory.LFun.singleAt D.host.F P) (GlobalTheory.LFun.compAt_singleAt P)
    (ε := finPart D e) (fun y => by rw [GlobalTheory.LFun.finPart_of_isPrimeIdem hef, GlobalTheory.LFun.singleAt_mul, one_mul])
    (I := (· ∈ intAE D)) (O := Ov D.host.E P) (fun y hy => (GlobalTheory.LFun.mem_intAE_iff_compAt y).1 hy P)
    (fun x => GlobalTheory.LFun.singleAt_mem_intAE) (Λ := (· ∈ Formalism.L2.NTheta.LamHat V))
    (X := X) hN hL (fun i => finPart D (incA D ((ϖ : D.host.E) ^ (d.getD i.1 0))))
  have ht : (fun i : Fin V.rank => GlobalTheory.LFun.compAt D.host.F P (finPart D (incA D ((ϖ : D.host.E) ^ (d.getD i.1 0))))) =
      fun i : Fin V.rank => algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E) ^ d.getD i.1 0 :=
    funext fun i => by rw [GlobalTheory.LFun.compAt_incA, map_zpow₀]
  rw [← hα] at key
  replace key := key.trans (by rw [hX, ht, locBasis_iff _ fun i => zpow_ne_zero _ h0])
  unfold DivAt IntVec
  exact and_congr Iff.rfl (key.trans (hasDiv_iff P hϖ d g).symm)

theorem divAt_cj_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU D.host.E V.rank ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ) (x : UA D.host.E V.rank),
      IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → x ∈ locU V.rank P →
      (DivAt V e (ϖ : D.host.E) d (cj j h₀ x) ↔ d.length = V.rank ∧ HasDiv (Ov D.host.E P) d (cLoc P x)) := by
  intro D _ V j h₀ M hM _ _ hj hL P e f ϖ d x hef h1 h2 _
  have hMM := map_mul_inv (Algebra.TensorProduct.includeRight :
      D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E).toRingHom hM
  have hH : finMat D.sp.cm.sig V.gram h₀⁻¹ * finMat D.sp.cm.sig V.gram h₀ = 1 :=
    (finMat_mul' _ _ _ _).symm.trans ((congrArg _ (inv_mul_cancel h₀)).trans (finMat_one' _ _))
  have hα : finMat D.sp.cm.sig V.gram (cj j h₀ x) = finMat D.sp.cm.sig V.gram h₀⁻¹ *
      finMat D.sp.cm.sig V.gram (j x) * finMat D.sp.cm.sig V.gram h₀ :=
    (congrArg _ (cj_apply j h₀ x)).trans ((finMat_mul' _ _ _ _).trans (congrArg (· * _) (finMat_mul' _ _ _ _)))
  refine divAt_iff_of_frame V d hef h1 h2 (frame_mul hH hMM) (fun y => ?_) (frame_conj hα (hj x)) ?_
  · rw [← Matrix.mulVec_mulVec]
    exact hL y
  · refine Matrix.ext fun a b => ?_
    exact congrArg (fun y : FiniteAdeleRing (𝓞 D.host.E) D.host.E => y P)
      ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).apply_symm_apply
        (pFin D.host.E (((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)) a b)))

end GlobalTheory.DivTransfer

end
