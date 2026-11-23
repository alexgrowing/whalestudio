import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.BdCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.PairEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.GaloisLiftMemFirstOrderDeformations
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.UpConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.CardCnd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.SumCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem bl_le_zl_of_lc {R D M : Type} [CommRing R] [Group D] [AddCommGroup M] [Module R M]
    [TopologicalSpace D] (ρ : Representation R D M) (hρ : LC ρ) : Bl ρ ≤ Zl ρ := by
  intro z hz
  rw [mem_Bl] at hz
  obtain ⟨y, hy⟩ := hz
  rw [mem_Zl]
  have hz : z = fun g => ρ g y - y := funext hy
  subst hz
  refine ⟨(hρ y).sub (IsLocallyConstant.const _), ?_⟩
  intro g g'
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

private theorem lc_comp_of_lc_of_continuous {R D D' M : Type} [CommRing R] [Group D] [Group D'] [AddCommGroup M]
    [Module R M] [TopologicalSpace D] [TopologicalSpace D'] (ρ : Representation R D M) (hρ : LC ρ)
    (ι : D' →* D) (hι : Continuous ι) : LC (ρ.comp ι) :=
  fun y => (hρ y).comp_continuous hι

private theorem comp_mem_zl_comp_of_mem_zl_of_continuous {R D D' M : Type} [CommRing R] [Group D] [Group D'] [AddCommGroup M]
    [Module R M] [TopologicalSpace D] [TopologicalSpace D'] (ρ : Representation R D M)
    (ι : D' →* D) (hι : Continuous ι) (z : D → M) (hz : z ∈ Zl ρ) : z ∘ ι ∈ Zl (ρ.comp ι) := by
  rw [mem_Zl] at hz ⊢
  refine ⟨hz.1.comp_continuous hι, fun g g' => ?_⟩
  simp [hz.2]

private theorem card_pow_nu_le_card_skew_w1 (A X : Type) [CommRing A] [CommRing X] [Algebra A X] [Finite X]
    (n g a : ℕ) (ha : a ≤ n) :
    Nat.card X ^ nu n a g ≤ Nat.card {Y : ↥(W1 n A X g a) //
      (Y : Matrix (Fin n) (Fin n) (DD X g))ᵀ = -(Y : Matrix (Fin n) (Fin n) (DD X g))} := by
  classical
  let S1 := {p : Fin a × Fin a // p.1 < p.2}
  let S2 := {p : Fin (n - a) × Fin (n - a) // p.1 < p.2}
  let S := (S1 → X) × (S2 → X) × (Fin a × Fin (n - a) → Fin g → X)
  let V : S → (i j : Fin n) → (i : ℕ) < j → DD X g := fun s i j hij =>
    if hi : (i : ℕ) < a then
      if hj : (j : ℕ) < a then DD.C (s.1 ⟨(⟨i, hi⟩, ⟨j, hj⟩), hij⟩)
      else ⟨0, s.2.2 (⟨i, hi⟩, ⟨j - a, by have := j.isLt; omega⟩), 0, 0⟩
    else DD.C (s.2.1 ⟨(⟨i - a, by have := i.isLt; omega⟩, ⟨j - a, by have := j.isLt; omega⟩),
      Fin.mk_lt_mk.2 (by omega)⟩)
  let Mf : S → Matrix (Fin n) (Fin n) (DD X g) := fun s i j =>
    if hij : (i : ℕ) < j then V s i j hij else if hji : (j : ℕ) < i then -(V s j i hji) else 0
  have hV : ∀ s i j hij, (V s i j hij).ep' = 0 ∧ (V s i j hij).eta = 0 ∧
      (((i : ℕ) < a ↔ (j : ℕ) < a) → (V s i j hij).ep = 0) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → (V s i j hij).a = 0) := by
    intro s i j hij
    by_cases hi : (i : ℕ) < a
    · by_cases hj : (j : ℕ) < a
      · simp [V, hi, hj, DD.C_ep, DD.C_ep', DD.C_eta]
        exact ⟨funext (DD.C_ep' _), funext (DD.C_ep _)⟩
      · simp [V, hi, hj]
    · have hj : ¬ (j : ℕ) < a := by omega
      simp [V, hi, hj, DD.C_ep, DD.C_ep', DD.C_eta]
      exact ⟨funext (DD.C_ep' _), funext (DD.C_ep _)⟩
  have memW : ∀ Z : Matrix (Fin n) (Fin n) (DD X g), (∀ i j, (Z i j).ep' = 0 ∧ (Z i j).eta = 0 ∧
      (((i : ℕ) < a ↔ (j : ℕ) < a) → (Z i j).ep = 0) ∧ (¬((i : ℕ) < a ↔ (j : ℕ) < a) → (Z i j).a = 0)) →
      Z ∈ W1 n A X g a := by
    intro Z hZ i j
    obtain ⟨h1, h2, h3, h4⟩ := hZ i j
    exact ⟨fun hs => ⟨fun h => absurd h (by decide), fun _ => h3 hs, fun _ => h1, fun _ => h2⟩,
      fun hs => ⟨fun _ => h4 hs, fun h => absurd h (by decide), fun _ => h1, fun _ => h2⟩⟩
  have hM : ∀ s i j, (Mf s i j).ep' = 0 ∧ (Mf s i j).eta = 0 ∧
      (((i : ℕ) < a ↔ (j : ℕ) < a) → (Mf s i j).ep = 0) ∧
      (¬((i : ℕ) < a ↔ (j : ℕ) < a) → (Mf s i j).a = 0) := by
    intro s i j
    by_cases hij : (i : ℕ) < j
    · simp only [Mf, dif_pos hij]
      exact hV s i j hij
    · by_cases hji : (j : ℕ) < i
      · simp only [Mf, dif_neg hij, dif_pos hji]
        obtain ⟨h1, h2, h3, h4⟩ := hV s j i hji
        refine ⟨funext fun t => ?_, ?_, fun hs => funext fun t => ?_, fun hs => ?_⟩
        · simp [DD.neg_ep', h1]
        · simp [DD.neg_eta, h2]
        · simp [DD.neg_ep, h3 hs.symm]
        · simp [DD.neg_a, h4 (fun h => hs h.symm)]
      · simp only [Mf, dif_neg hij, dif_neg hji]
        exact ⟨funext fun t => DD.zero_ep' t, DD.zero_eta, fun _ => funext fun t => DD.zero_ep t,
          fun _ => DD.zero_a⟩
  have hanti : ∀ s, (Mf s)ᵀ = -(Mf s) := by
    intro s
    refine Matrix.ext fun i j => ?_
    show Mf s j i = -(Mf s i j)
    simp only [Mf]
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · simp only [dif_neg (lt_asymm h), dif_pos h]
    · have h1 : ¬ (j : ℕ) < i := by omega
      have h2 : ¬ (i : ℕ) < j := by omega
      simp only [dif_neg h1, dif_neg h2, neg_zero]
    · simp only [dif_pos h, dif_neg (lt_asymm h), neg_neg]
  have hx1 : ∀ s (i j : Fin n) (hij : (i : ℕ) < j) (hi : (i : ℕ) < a) (hj : (j : ℕ) < a),
      Mf s i j = DD.C (s.1 ⟨(⟨i, hi⟩, ⟨j, hj⟩), hij⟩) := by
    intro s i j hij hi hj
    simp only [Mf, V, dif_pos hij, dif_pos hi, dif_pos hj]
  have hx2 : ∀ s (i j : Fin n) (hij : (i : ℕ) < j) (hi : ¬ (i : ℕ) < a),
      Mf s i j = DD.C (s.2.1 ⟨(⟨i - a, by have := i.isLt; omega⟩, ⟨j - a, by have := j.isLt; omega⟩),
        Fin.mk_lt_mk.2 (by omega)⟩) := by
    intro s i j hij hi
    simp only [Mf, V, dif_pos hij, dif_neg hi]
  have hx3 : ∀ s (i j : Fin n) (hij : (i : ℕ) < j) (hi : (i : ℕ) < a) (hj : ¬ (j : ℕ) < a),
      Mf s i j = ⟨0, s.2.2 (⟨i, hi⟩, ⟨j - a, by have := j.isLt; omega⟩), 0, 0⟩ := by
    intro s i j hij hi hj
    simp only [Mf, V, dif_pos hij, dif_pos hi, dif_neg hj]
  let φ : S → {Y : ↥(W1 n A X g a) //
      (Y : Matrix (Fin n) (Fin n) (DD X g))ᵀ = -(Y : Matrix (Fin n) (Fin n) (DD X g))} :=
    fun s => ⟨⟨Mf s, memW _ (hM s)⟩, hanti s⟩
  have hφ : Function.Injective φ := by
    intro s s' hss
    have hE : ∀ i j, Mf s i j = Mf s' i j := fun i j =>
      congrFun (congrFun (congrArg (fun Y : {Y : ↥(W1 n A X g a) //
        (Y : Matrix (Fin n) (Fin n) (DD X g))ᵀ = -(Y : Matrix (Fin n) (Fin n) (DD X g))} =>
          (Y.1 : Matrix (Fin n) (Fin n) (DD X g))) hss) i) j
    refine Prod.ext (funext fun p => ?_) (Prod.ext (funext fun p => ?_) (funext fun p => funext fun t => ?_))
    · have h := congrArg DD.a (hE ⟨p.1.1, by have := p.1.1.isLt; omega⟩ ⟨p.1.2, by have := p.1.2.isLt; omega⟩)
      rw [hx1 s _ _ p.2 p.1.1.isLt p.1.2.isLt, hx1 s' _ _ p.2 p.1.1.isLt p.1.2.isLt, DD.C_a, DD.C_a] at h
      exact h
    · have hlt : (p.1.1 : ℕ) < p.1.2 := p.2
      have h := congrArg DD.a (hE ⟨p.1.1 + a, by have := p.1.1.isLt; omega⟩
        ⟨p.1.2 + a, by have := p.1.2.isLt; omega⟩)
      rw [hx2 s _ _ (by simp; omega) (by simp), hx2 s' _ _ (by simp; omega) (by simp), DD.C_a, DD.C_a] at h
      convert h using 2 <;> exact Subtype.ext (Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp)))
    · have h := congrArg (fun z : DD X g => z.ep t) (hE ⟨p.1, by have := p.1.isLt; omega⟩
        ⟨p.2 + a, by have := p.2.isLt; omega⟩)
      rw [hx3 s _ _ (by simp; omega) p.1.isLt (by simp), hx3 s' _ _ (by simp; omega) p.1.isLt (by simp)] at h
      simp only at h
      convert h using 3 <;> exact Fin.ext (by simp)
  calc Nat.card X ^ nu n a g = Nat.card S := by
        simp only [S, S1, S2, Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_subtype,
          Fintype.card_product_filter_lt, Fintype.card_fin, Fintype.card_prod, nu]
        rw [pow_add, pow_add, pow_mul]
        ring
    _ ≤ _ := Nat.card_le_card_of_injective φ hφ

private theorem rho1_mul_mem_m1_of_mem_m1 {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (k : Kap x)
    (X : Type) [CommRing X] [Algebra x.A X] (g : F.G₀) (Y : Matrix (Fin n) (Fin n) (DD X k.g))
    (hY : Y ∈ k.M1 X) : k.ρ1 X g * Y ∈ k.M1 X := by
  classical
  have pa : ∀ z : DD X k.g, z ∈ ddPart x.A X k.g true false false false ↔ z.ep = 0 ∧ z.ep' = 0 ∧ z.eta = 0 :=
    fun z => ⟨fun h => ⟨h.2.1 rfl, h.2.2.1 rfl, h.2.2.2 rfl⟩,
      fun h => ⟨fun h' => absurd h' (by decide), fun _ => h.1, fun _ => h.2.1, fun _ => h.2.2⟩⟩
  have pe : ∀ z : DD X k.g, z ∈ ddPart x.A X k.g false true false false ↔ z.a = 0 ∧ z.ep' = 0 ∧ z.eta = 0 :=
    fun z => ⟨fun h => ⟨h.1 rfl, h.2.2.1 rfl, h.2.2.2 rfl⟩,
      fun h => ⟨fun _ => h.1, fun h' => absurd h' (by decide), fun _ => h.2.1, fun _ => h.2.2⟩⟩
  have memI : ∀ Z : Matrix (Fin n) (Fin n) (DD X k.g), Z ∈ k.M1 X ↔ ∀ i j : Fin n,
      (((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → Z i j ∈ ddPart x.A X k.g true false false false) ∧
      (¬((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → Z i j ∈ ddPart x.A X k.g false true false false) := fun Z => Iff.rfl
  have hC : ∀ (c : X) (z : DD X k.g), DD.C c * z = ⟨c * z.a, fun t => c * z.ep t, fun t => c * z.ep' t, c * z.eta⟩ := by
    intro c z
    refine DD.ext_iff.2 ⟨?_, funext fun t => ?_, funext fun t => ?_, ?_⟩
    · simp [DD.mul_a, DD.C_a]
    · simp [DD.mul_ep, DD.C_a, DD.C_ep]
    · simp [DD.mul_ep', DD.C_a, DD.C_ep']
    · simp [DD.mul_eta, DD.C_a, DD.C_ep, DD.C_ep', DD.C_eta]
  have hRe : ∀ i k' : Fin n, x.ρX (DD X k.g) g i k' = DD.C (algebraMap x.A X ((mat x.ρ) g i k')) := fun i k' => rfl
  have hRz : ∀ i k' : Fin n, ¬((i : ℕ) < x.a ↔ (k' : ℕ) < x.a) → (mat x.ρ) g i k' = 0 := fun i k' h =>
    (Submodule.mem_bot _).1 ((x.blk g i k').2 h)
  have hRY : x.ρX (DD X k.g) g * Y ∈ k.M1 X := by
    rw [memI] at hY ⊢
    intro i j
    constructor
    · intro hs
      rw [Matrix.mul_apply]
      refine Submodule.sum_mem _ fun k' _ => ?_
      by_cases hk : ((i : ℕ) < x.a ↔ (k' : ℕ) < x.a)
      · have hz := (pa _).1 ((hY k' j).1 (hk.symm.trans hs))
        rw [hRe, hC, pa]
        refine ⟨funext fun t => ?_, funext fun t => ?_, ?_⟩
        · simp [congrFun hz.1 t]
        · simp [congrFun hz.2.1 t]
        · simp [hz.2.2]
      · rw [hRe, hRz i k' hk]
        simp
    · intro hs
      rw [Matrix.mul_apply]
      refine Submodule.sum_mem _ fun k' _ => ?_
      by_cases hk : ((i : ℕ) < x.a ↔ (k' : ℕ) < x.a)
      · have hz := (pe _).1 ((hY k' j).2 (fun h => hs (hk.trans h)))
        rw [hRe, hC, pe]
        refine ⟨?_, funext fun t => ?_, ?_⟩
        · simp [hz.1]
        · simp [congrFun hz.2.1 t]
        · simp [hz.2.2]
      · rw [hRe, hRz i k' hk]
        simp
  have hκ : ∀ (j : Fin k.g) (i k' : Fin n), ((i : ℕ) < x.a ↔ (k' : ℕ) < x.a) → k.κ j g i k' = 0 :=
    fun j i k' h => (Submodule.mem_bot _).1 (((k.mem j).1 g i k').1 h)
  have hEZ : ∀ Z ∈ k.M1 X, DD.epM (fun j => (k.κ j g).map (algebraMap x.A X)) * Z ∈ k.M1 X := by
    intro Z hZ
    rw [memI] at hZ ⊢
    have hep' : ∀ k' j : Fin n, (Z k' j).ep' = 0 := by
      intro k' j
      by_cases h : ((k' : ℕ) < x.a ↔ (j : ℕ) < x.a)
      · exact ((pa _).1 ((hZ k' j).1 h)).2.1
      · exact ((pe _).1 ((hZ k' j).2 h)).2.1
    have key : ∀ i j k' : Fin n,
        (DD.epM (fun j => (k.κ j g).map (algebraMap x.A X)) i k' * Z k' j).a = 0 ∧
        (DD.epM (fun j => (k.κ j g).map (algebraMap x.A X)) i k' * Z k' j).ep' = 0 ∧
        (DD.epM (fun j => (k.κ j g).map (algebraMap x.A X)) i k' * Z k' j).eta = 0 ∧
        (((i : ℕ) < x.a ↔ (j : ℕ) < x.a) →
          (DD.epM (fun j => (k.κ j g).map (algebraMap x.A X)) i k' * Z k' j).ep = 0) := by
      intro i j k'
      have hz' := hep' k' j
      refine ⟨?_, funext fun t => ?_, ?_, fun hs => funext fun t => ?_⟩
      · simp [DD.mul_a, DD.epM]
      · simp [DD.mul_ep', DD.epM, congrFun hz' t]
      · simp [DD.mul_eta, DD.epM, hz']
      · by_cases hk : ((i : ℕ) < x.a ↔ (k' : ℕ) < x.a)
        · simp [DD.mul_ep, DD.epM, hκ t i k' hk]
        · have hza := ((pe _).1 ((hZ k' j).2 (fun h => hk (hs.trans h.symm)))).1
          simp [DD.mul_ep, DD.epM, hza]
    intro i j
    constructor
    · intro hs
      rw [Matrix.mul_apply]
      refine Submodule.sum_mem _ fun k' _ => ?_
      obtain ⟨-, h2, h3, h4⟩ := key i j k'
      exact (pa _).2 ⟨h4 hs, h2, h3⟩
    · intro hs
      rw [Matrix.mul_apply]
      refine Submodule.sum_mem _ fun k' _ => ?_
      obtain ⟨h1, h2, h3, -⟩ := key i j k'
      exact (pe _).2 ⟨h1, h2, h3⟩
  show (1 + DD.epM (fun j => (k.κ j g).map (algebraMap x.A X))) * x.ρX (DD X k.g) g * Y ∈ k.M1 X
  rw [Matrix.mul_assoc, Matrix.add_mul, Matrix.one_mul]
  exact add_mem hRY (hEZ _ hRY)

theorem UpperTheory.V.Pa.oneLevel :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m q d : ℕ) (a : ArData G q d) (rep : Representation x.A G.Γ (k.M1 (x.Am m))) (rep' : Representation x.A G.Γ (k.EpsilonEtaTensorDual (x.Am m))) (e : L.Vl → ℕ) (f : Option (Fin q) → ℕ) (c₁ c₂ : ℕ), l ≠ 2 → a.Counts → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (fun _ => 1) (k.M1 (x.Am m)) rep → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (fun g => epsD k (x.Am m) (h.p g)) (k.EpsilonEtaTensorDual (x.Am m)) rep' → (∀ v, Finite (k.Zb (x.Am m) v) ∧ Nat.card (k.Zb (x.Am m) v) ≤ Nat.card x.K ^ e v) → (∀ j, Nat.card (Representation.invariants (rep'.comp (a.ι (.inr (.inr j))) : Representation x.A (a.D (.inr (.inr j))) _)) ≤ Nat.card x.K ^ f j) → Nat.card rep.invariants ≤ Nat.card x.K ^ c₁ → (Finite (Zl rep') → {y | y ∈ Zl rep' ∧ ∀ j : Fin q, y ∘ a.ι (.inr (.inr (some j))) ∈ Bl (rep'.comp (a.ι (.inr (.inr (some j)))) : Representation x.A (a.D (.inr (.inr (some j)))) _)}.ncard ≤ Nat.card (Bl rep') * Nat.card x.K ^ c₂) → (Sel1 h (x.Am m) k).Finite ∧ (Sel1 h (x.Am m) k).ncard * Nat.card x.K ^ (m * (n + nu n x.a k.g) * Fintype.card L.Vl + m * nu n x.a k.g * d) ≤ (Bd1 h (x.Am m) k).ncard * Nat.card x.K ^ (c₁ + c₂ + ∑ v, e v + ∑ j, f j) := by
  intro l _ L G G0 h n x k m q d a rep rep' e f c₁ c₂ hl ha hrep hrep' hZb hf hc1 hc2
  obtain ⟨hfA, hcA, hfD, hlA, hlD, -, -, h2, -⟩ := finAm l G0.frame n x m k.g
  haveI := hfA
  haveI := hfD
  have hLC := (lc1 l L G G0 h n x k m).2.2 (fun _ => 1) (k.M1 (x.Am m)) rep (IsLocallyConstant.const _) hrep
  have hLC' := (lc1 l L G G0 h n x k m).2.2 _ (k.EpsilonEtaTensorDual (x.Am m)) rep' (lc1 l L G G0 h n x k m).2.1 hrep'
  obtain ⟨b, hb⟩ := pairEx l L G G0 h n x k m
  have hdual := hb rep rep' hrep hrep'
  have hgw := ha.gw
  have hcont : ∀ w, Continuous (a.ι w) := by
    rintro (v | u | j)
    · exact continuous_subtype_val.comp (G.φ_cont v)
    · exact continuous_subtype_val.comp (G.φu_cont u)
    · exact continuous_subtype_val.comp (a.φq_cont j)
  have hsmul : ∀ y : ↥(k.M1 (x.Am m)), l • y = 0 := by
    intro y
    apply Subtype.ext
    refine Matrix.ext fun i j => ?_
    simpa using hlD (y.1 i j)
  let U : (u : L.St) → AddSubgroup (L.Gu u → ↥(k.M1 (x.Am m))) := fun u =>
    { carrier := {z | z ∈ Zl (rep.comp (a.ι (.inr (.inl u)))) ∧ ∀ g ∈ L.Ju u, z g = 0}
      add_mem' := fun {z z'} hz hz' => ⟨add_mem hz.1 hz'.1, fun g hg => by simp [hz.2 g hg, hz'.2 g hg]⟩
      zero_mem' := ⟨zero_mem _, fun g _ => rfl⟩
      neg_mem' := fun {z} hz => ⟨neg_mem hz.1, fun g hg => by simp [hz.2 g hg]⟩ }
  obtain ⟨𝓛, h𝓛v, h𝓛u, h𝓛j⟩ : ∃ 𝓛 : (w : ArData.W L q) → AddSubgroup (a.D w → ↥(k.M1 (x.Am m))),
      (∀ v, 𝓛 (.inl v) = (Bl (rep.comp (a.ι (.inl v)))).toAddSubgroup ⊔ k.Zb (x.Am m) v) ∧
      (∀ u, 𝓛 (.inr (.inl u)) = U u) ∧
      (∀ j, 𝓛 (.inr (.inr j)) = (Zl (rep.comp (a.ι (.inr (.inr j))))).toAddSubgroup) :=
    ⟨fun w => match w with
      | .inl v => (Bl (rep.comp (a.ι (.inl v)))).toAddSubgroup ⊔ k.Zb (x.Am m) v
      | .inr (.inl u) => U u
      | .inr (.inr j) => (Zl (rep.comp (a.ι (.inr (.inr j))))).toAddSubgroup,
      fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have hZbZl : ∀ v, k.Zb (x.Am m) v ≤ (Zl (rep.comp (a.ι (.inl v)))).toAddSubgroup := by
    intro v β hβ
    obtain ⟨hlc, hco, -, -⟩ := hβ
    refine (mem_Zl (rep.comp (a.ι (.inl v)))).2 ⟨hlc, fun g g' => Subtype.ext ?_⟩
    have e1 : h.p₀ (G.φ v g) = G0.φ v g := Subtype.ext (h.φ v g)
    have e2 := hrep.1 (G.φ v g) (β g')
    simp only [one_smul] at e2
    show _ = ((β g : ↥(k.M1 (x.Am m))) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) +
      ((rep (G.φ v g : G.Γ) (β g') : ↥(k.M1 (x.Am m))) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))
    refine (hco g g').trans ?_
    rw [e2, map_inv, e1]
  have hUnr : ∀ u, ∀ g ∈ L.Ju u, rep.comp (a.ι (.inr (.inl u))) g = 1 := by
    intro u g hg
    have e1 : h.p₀ (G.φu u g) = G0.φu u g := Subtype.ext (h.φu u g)
    have hI : G0.φu u g ∈ G0.frame.Iu u := ⟨g, hg, rfl⟩
    have r := (rho1 l G0.frame n x k (x.Am m)).2.2.2.2 u
    apply LinearMap.ext
    intro Z
    apply Subtype.ext
    have e2 := hrep.1 (G.φu u g) Z
    simp only [one_smul] at e2
    show ((rep (G.φu u g : G.Γ) Z : ↥(k.M1 (x.Am m))) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) =
      (Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))
    rw [e2, map_inv, e1, r _ hI, r _ (inv_mem hI)]
    simp
  have h𝓛 : ∀ w, (Bl (rep.comp (a.ι w))).toAddSubgroup ≤ 𝓛 w ∧ 𝓛 w ≤ (Zl (rep.comp (a.ι w))).toAddSubgroup := by
    rintro (v | u | j)
    · rw [h𝓛v]
      exact ⟨le_sup_left, sup_le (bl_le_zl_of_lc _ (lc_comp_of_lc_of_continuous _ hLC _ (hcont _))) (hZbZl v)⟩
    · rw [h𝓛u]
      refine ⟨fun z hz => ⟨bl_le_zl_of_lc _ (lc_comp_of_lc_of_continuous _ hLC _ (hcont _)) hz, fun g hg => ?_⟩, fun z hz => hz.1⟩
      obtain ⟨y, hy⟩ := (mem_Bl _).1 hz
      rw [hy g, hUnr u g hg]
      simp
    · rw [h𝓛j]
      exact ⟨bl_le_zl_of_lc _ (lc_comp_of_lc_of_continuous _ hLC _ (hcont _)), le_rfl⟩
  obtain ⟨hZfin, hZfin', hGW⟩ := hgw x.A _ _ rep rep' b hLC hdual 𝓛 h𝓛
  obtain ⟨hSelFin, hSel1, hBd⟩ := selN l L G G0 h n x k m rep hl hrep hZfin
  have hT : {y : G.Γ → ↥(k.EpsilonEtaTensorDual (x.Am m)) | y ∈ Zl rep' ∧ ∀ w, 𝓛 w = (Zl (rep.comp (a.ι w))).toAddSubgroup →
      y ∘ ⇑(a.ι w) ∈ Bl (rep'.comp (a.ι w))}.ncard ≤ Nat.card ↥(Bl rep') * Nat.card x.K ^ c₂ := by
    refine le_trans ?_ (hc2 hZfin')
    exact Set.ncard_le_ncard (fun y hy => ⟨hy.1, fun j => hy.2 _ (h𝓛j _)⟩)
      ((Set.toFinite (Zl rep' : Set (G.Γ → ↥(k.EpsilonEtaTensorDual (x.Am m))))).subset (fun y hy => hy.1))
  have hfinGW : {z : G.Γ → ↥(k.M1 (x.Am m)) | z ∈ Zl rep ∧ ∀ w, z ∘ ⇑(a.ι w) ∈ 𝓛 w}.Finite :=
    (Set.toFinite (Zl rep : Set (G.Γ → ↥(k.M1 (x.Am m))))).subset (fun y hy => hy.1)
  have hsub : ∀ z, z ∈ Zl rep → (∀ v, z ∘ ⇑(a.ι (.inl v)) ∈ 𝓛 (.inl v)) →
      (∀ u, ∀ g ∈ L.Ju u, z ↑(G.φu u g) = 0) → z ∈ {z | z ∈ Zl rep ∧ ∀ w, z ∘ ⇑(a.ι w) ∈ 𝓛 w} := by
    intro z hz hv hu
    refine ⟨hz, ?_⟩
    rintro (v | u | j)
    · exact hv v
    · rw [h𝓛u]
      exact ⟨comp_mem_zl_comp_of_mem_zl_of_continuous _ _ (hcont _) z hz, fun g hg => hu u g hg⟩
    · rw [h𝓛j]
      exact comp_mem_zl_comp_of_mem_zl_of_continuous _ _ (hcont _) z hz
  have hS := le_trans hSel1 (Nat.mul_le_mul_right _ (Set.ncard_le_ncard
    (fun z hz => hsub z hz.1 (fun v => by rw [h𝓛v]; exact hz.2.1 v) hz.2.2) hfinGW))
  have hPv : ∀ v, Nat.card ↥(𝓛 (.inl v)) * Nat.card x.K ^ (m * (n + nu n x.a k.g)) ≤
      Nat.card ↥(k.M1 (x.Am m)) * Nat.card x.K ^ e v := by
    intro v
    haveI := (hZb v).1
    have hsc := sumCount x.A (L.Gv v) ↥(k.M1 (x.Am m)) (rep.comp (a.ι (.inl v))) (k.b1 (x.Am m) v)
      (k.Zb (x.Am m) v) (hZb v).1 (fun y hy => bMem l G0.frame n x k m v y _ hy
        ((lc_comp_of_lc_of_continuous _ hLC (a.ι (.inl v)) (hcont _) y).sub (IsLocallyConstant.const y)) (fun g => by
          have e1 : h.p₀ (G.φ v g) = G0.φ v g := Subtype.ext (h.φ v g)
          have e2 := hrep.1 (G.φ v g) y
          simp only [one_smul] at e2
          show ((rep ↑(G.φ v g) y - y : ↥(k.M1 (x.Am m))) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) = _
          rw [Submodule.coe_sub, e2, map_inv, e1]))
    rw [h𝓛v, ← bCard l G0.frame n x k m v]
    exact hsc.2.trans (Nat.mul_le_mul_left _ (hZb v).2)
  have hPu : ∀ u, Nat.card ↥(𝓛 (.inr (.inl u))) = Nat.card ↥(k.M1 (x.Am m)) := by
    intro u
    rw [h𝓛u]
    have hun := ha.unr u x.A ↥(k.M1 (x.Am m)) (rep.comp (a.ι (.inr (.inl u))))
      (lc_comp_of_lc_of_continuous _ hLC _ (hcont _)) hsmul (hUnr u)
    rw [← hun.2]
    exact Nat.card_coe_set_eq _
  have hPj : ∀ j, Nat.card ↥(𝓛 (.inr (.inr j))) ≤ Nat.card ↥(k.M1 (x.Am m)) * Nat.card x.K ^ f j := by
    intro j
    rw [h𝓛j]
    have hd : IsDualPair (G.ε.comp (a.ι (.inr (.inr j)))) (rep.comp (a.ι (.inr (.inr j))))
        (rep'.comp (a.ι (.inr (.inr j)))) b :=
      ⟨hdual.left, hdual.right, fun g y z => hdual.equiv _ y z⟩
    obtain ⟨-, hc⟩ := ha.locQ j x.A _ _ (rep.comp (a.ι (.inr (.inr j)))) (rep'.comp (a.ι (.inr (.inr j)))) b
      (lc_comp_of_lc_of_continuous _ hLC _ (hcont _)) hd
    refine le_trans (le_of_eq hc) ?_
    rw [add_zero, pow_one]
    exact Nat.mul_le_mul_left _ (hf j)
  have hfix : ∀ i : Fin d, Nat.card x.K ^ (m * nu n x.a k.g) ≤
      Nat.card {y : ↥(k.M1 (x.Am m)) // (rep (a.cw i)) y = y} := by
    intro i
    have hη : a.cw i * G.c ∈ G.η.ker := by
      rw [MonoidHom.mem_ker, map_mul, a.cw_η i, G.η_c]
      simp
    let hh : G.G₀ := ⟨a.cw i * G.c, hη⟩
    obtain ⟨r1, rmul, rconj, -, -⟩ := rho1 l G0.frame n x k (x.Am m)
    have hAB : k.ρ1 (x.Am m) (h.p₀ hh) * k.ρ1 (x.Am m) (h.p₀ hh⁻¹) = 1 := by
      rw [← rmul, ← map_mul, mul_inv_cancel, map_one, r1]
    have hBA : k.ρ1 (x.Am m) (h.p₀ hh⁻¹) * k.ρ1 (x.Am m) (h.p₀ hh) = 1 := by
      rw [← rmul, ← map_mul, inv_mul_cancel, map_one, r1]
    have hci : G.c⁻¹ = G.c := inv_eq_of_mul_eq_one_right G.c_sq
    have hwi : (a.cw i)⁻¹ = a.cw i := inv_eq_of_mul_eq_one_right (a.cw_sq i)
    have hconj : G0.frame.conj (h.p₀ hh) = h.p₀ hh⁻¹ := by
      apply Subtype.ext
      show G0.c * h.p (a.cw i * G.c) * G0.c⁻¹ = h.p ((a.cw i * G.c)⁻¹)
      rw [← h.c, ← map_inv, ← map_mul, ← map_mul, _root_.mul_inv_rev, hci, hwi]
      congr 1
      rw [mul_assoc, mul_assoc, G.c_sq, mul_one]
    have hε : G0.frame.eps ℤ_[l] x.A (h.p₀ hh) = 1 := by
      have hε0 : G0.ε (h.p (a.cw i * G.c)) = 1 := by
        rw [h.ε, map_mul, a.cw_ε i, a.c_ε]
        simp
      show Units.map _ (G0.ε (h.p (a.cw i * G.c))) = 1
      rw [hε0, map_one]
    have hsym : (k.ρ1 (x.Am m) (h.p₀ hh))ᵀ = k.ρ1 (x.Am m) (h.p₀ hh) := by
      have hc := rconj (h.p₀ hh)
      rw [hconj, hε, _root_.one_zpow, Units.val_one, map_one, one_smul] at hc
      calc (k.ρ1 (x.Am m) (h.p₀ hh))ᵀ = (k.ρ1 (x.Am m) (h.p₀ hh))ᵀ *
            (k.ρ1 (x.Am m) (h.p₀ hh⁻¹) * k.ρ1 (x.Am m) (h.p₀ hh)) := by rw [hBA, Matrix.mul_one]
        _ = k.ρ1 (x.Am m) (h.p₀ hh) := by rw [← Matrix.mul_assoc, hc, Matrix.one_mul]
    have hcw : a.cw i = (hh : G.Γ) * G.c := by
      show a.cw i = a.cw i * G.c * G.c
      rw [mul_assoc, G.c_sq, mul_one]
    have hrepcw : ∀ Z : ↥(k.M1 (x.Am m)), ((rep (a.cw i) Z : ↥(k.M1 (x.Am m))) :
        Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) = k.ρ1 (x.Am m) (h.p₀ hh) *
          (-(Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))ᵀ) * k.ρ1 (x.Am m) (h.p₀ hh⁻¹) := by
      intro Z
      have e1 := hrep.1 hh (rep G.c Z)
      have e2 := hrep.2 Z
      simp only [one_smul] at e1 e2
      rw [hcw, map_mul, Module.End.mul_apply, e1]
      congr 2
    let ψ : {Y : ↥(W1 n x.A (x.Am m) k.g x.a) //
        (Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))ᵀ = -(Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))} →
        {y : ↥(k.M1 (x.Am m)) // (rep (a.cw i)) y = y} := fun Y =>
      ⟨⟨k.ρ1 (x.Am m) (h.p₀ hh) * Y.1.1, rho1_mul_mem_m1_of_mem_m1 x k (x.Am m) (h.p₀ hh) Y.1.1 Y.1.2⟩, by
        apply Subtype.ext
        rw [hrepcw]
        show k.ρ1 (x.Am m) (h.p₀ hh) * (-(k.ρ1 (x.Am m) (h.p₀ hh) * Y.1.1)ᵀ) * k.ρ1 (x.Am m) (h.p₀ hh⁻¹) =
          k.ρ1 (x.Am m) (h.p₀ hh) * Y.1.1
        rw [Matrix.transpose_mul, hsym, Y.2, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Matrix.mul_assoc, hAB,
          Matrix.mul_one]⟩
    have hψ : Function.Injective ψ := by
      intro Y1 Y2 hY
      have e : k.ρ1 (x.Am m) (h.p₀ hh) * Y1.1.1 = k.ρ1 (x.Am m) (h.p₀ hh) * Y2.1.1 :=
        congrArg (fun y : {y : ↥(k.M1 (x.Am m)) // (rep (a.cw i)) y = y} =>
          (y.1 : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) hY
      have e' := congrArg (fun M => k.ρ1 (x.Am m) (h.p₀ hh⁻¹) * M) e
      simp only [← Matrix.mul_assoc, hBA, Matrix.one_mul] at e'
      exact Subtype.ext (Subtype.ext e')
    calc Nat.card x.K ^ (m * nu n x.a k.g) = Nat.card (x.Am m) ^ nu n x.a k.g := by rw [pow_mul, hcA]
      _ ≤ _ := card_pow_nu_le_card_skew_w1 x.A (x.Am m) n k.g x.a x.a_le
      _ ≤ _ := Nat.card_le_card_of_injective ψ hψ
  have hfixP : (Nat.card x.K ^ (m * nu n x.a k.g)) ^ d ≤
      ∏ i : Fin d, Nat.card {y : ↥(k.M1 (x.Am m)) // (rep (a.cw i)) y = y} := by
    calc (Nat.card x.K ^ (m * nu n x.a k.g)) ^ d = ∏ _i : Fin d, Nat.card x.K ^ (m * nu n x.a k.g) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hfix i)
  have hP : (∏ w, Nat.card ↥(𝓛 w)) * (Nat.card x.K ^ (m * (n + nu n x.a k.g))) ^ Fintype.card L.Vl ≤
      Nat.card ↥(k.M1 (x.Am m)) ^ Fintype.card (ArData.W L q) * Nat.card x.K ^ (∑ v, e v + ∑ j, f j) := by
    have h1 : ∏ v, (Nat.card ↥(𝓛 (.inl v)) * Nat.card x.K ^ (m * (n + nu n x.a k.g))) ≤
        ∏ v, (Nat.card ↥(k.M1 (x.Am m)) * Nat.card x.K ^ e v) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun v _ => hPv v)
    have h3 : ∏ j, Nat.card ↥(𝓛 (.inr (.inr j))) ≤ ∏ j, (Nat.card ↥(k.M1 (x.Am m)) * Nat.card x.K ^ f j) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => hPj j)
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ] at h1 h3
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.card_sum, Fintype.card_sum]
    simp only [hPu, Finset.prod_const, Finset.card_univ]
    calc _ = ((∏ v, Nat.card ↥(𝓛 (.inl v))) * (Nat.card x.K ^ (m * (n + nu n x.a k.g))) ^ Fintype.card L.Vl) *
          Nat.card ↥(k.M1 (x.Am m)) ^ Fintype.card L.St * ∏ j, Nat.card ↥(𝓛 (.inr (.inr j))) := by ring
      _ ≤ (Nat.card ↥(k.M1 (x.Am m)) ^ Fintype.card L.Vl * Nat.card x.K ^ ∑ v, e v) *
          Nat.card ↥(k.M1 (x.Am m)) ^ Fintype.card L.St *
          (Nat.card ↥(k.M1 (x.Am m)) ^ Fintype.card (Option (Fin q)) * Nat.card x.K ^ ∑ j, f j) := by
        gcongr
      _ = _ := by ring
  have hNpos : 0 < Nat.card ↥(k.M1 (x.Am m)) := Nat.card_pos
  have hBpos : 0 < Nat.card ↥(Bl rep') := by
    haveI : Finite ↥(Zl rep') := hZfin'
    haveI : Finite ↥(Bl rep') := Finite.of_injective _ (Submodule.inclusion_injective (bl_le_zl_of_lc rep' hLC'))
    exact Nat.card_pos
  have key : Set.ncard {z : G.Γ → ↥(k.M1 (x.Am m)) | z ∈ Zl rep ∧ ∀ w, z ∘ ⇑(a.ι w) ∈ 𝓛 w} *
      ((Nat.card x.K ^ (m * (n + nu n x.a k.g))) ^ Fintype.card L.Vl * (Nat.card x.K ^ (m * nu n x.a k.g)) ^ d) ≤
      Nat.card ↥(k.M1 (x.Am m)) * (Nat.card x.K ^ c₂ * Nat.card x.K ^ (∑ v, e v + ∑ j, f j)) := by
    have hpos : 0 < Nat.card ↥(Bl rep') * Nat.card ↥(k.M1 (x.Am m)) ^ Fintype.card (ArData.W L q) := by
      positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    have hG := hGW
    have hE := Nat.mul_le_mul_left (Set.ncard {z : G.Γ → ↥(k.M1 (x.Am m)) | z ∈ Zl rep ∧ ∀ w, z ∘ ⇑(a.ι w) ∈ 𝓛 w} *
      Nat.card ↥(Bl rep') * Nat.card ↥(k.M1 (x.Am m)) ^ Fintype.card (ArData.W L q)) hfixP
    have hT' := Nat.mul_le_mul_left (Nat.card ↥(k.M1 (x.Am m))) hT
    have hT'' := Nat.mul_le_mul_right (∏ w, Nat.card ↥(𝓛 w)) hT'
    have hP' := Nat.mul_le_mul_left (Nat.card ↥(k.M1 (x.Am m)) * Nat.card ↥(Bl rep') * Nat.card x.K ^ c₂) hP
    have hc := Nat.mul_le_mul_right ((Nat.card x.K ^ (m * (n + nu n x.a k.g))) ^ Fintype.card L.Vl)
      ((hE.trans hG).trans hT'')
    calc _ = _ := by ring
      _ ≤ _ := hc
      _ = _ := by ring
      _ ≤ _ := hP'
      _ = _ := by ring
  refine ⟨hSelFin, ?_⟩
  refine Nat.le_of_mul_le_mul_right ?_ hNpos
  have k1 := Nat.mul_le_mul_right ((Nat.card x.K ^ (m * (n + nu n x.a k.g))) ^ Fintype.card L.Vl *
    (Nat.card x.K ^ (m * nu n x.a k.g)) ^ d) hS
  have k2 := Nat.mul_le_mul_right (Nat.card { y : ↥(k.M1 (x.Am m)) // (rep G.c) y = y }) key
  have k3 := Nat.mul_le_mul_left (Nat.card ↥(k.M1 (x.Am m)) * (Nat.card x.K ^ c₂ *
    Nat.card x.K ^ (∑ v, e v + ∑ j, f j)) * (Bd1 h (x.Am m) k).ncard) hc1
  calc _ = _ := by rw [pow_add, pow_mul, pow_mul]; ring
    _ ≤ _ := k1
    _ = _ := by ring
    _ ≤ _ := k2
    _ = _ := by rw [← hBd]; ring
    _ ≤ _ := k3
    _ = _ := by ring
