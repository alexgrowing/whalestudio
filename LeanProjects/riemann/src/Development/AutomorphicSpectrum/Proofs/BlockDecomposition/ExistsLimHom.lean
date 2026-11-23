import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulSubEqZeroOfSum
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

section Lim

variable {T : Type} [CommRing T] (ϖ : T)

def Tends (x : ℕ → T) (L : T) : Prop := ∀ k, ∃ M, ∀ m, M ≤ m → x m - L ∈ Ideal.span {ϖ ^ k}

variable {ϖ}

theorem smodEq_iff {a b : T} {k : ℕ} :
    a ≡ b [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] ↔ a - b ∈ Ideal.span {ϖ ^ k} := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem Tends.unique [IsHausdorff (Ideal.span {ϖ}) T] {x : ℕ → T} {L L' : T} (h : Tends ϖ x L)
    (h' : Tends ϖ x L') : L = L' := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) T) _ fun k => ?_
  have h0 : L - L' ∈ Ideal.span {ϖ ^ k} := by
    obtain ⟨M, hM⟩ := h k
    obtain ⟨M', hM'⟩ := h' k
    have := sub_mem (hM' (max M M') (le_max_right _ _)) (hM (max M M') (le_max_left _ _))
    simpa using this
  have : L - L' ≡ 0 [SMOD ((Ideal.span {ϖ}) ^ k • ⊤ : Submodule T T)] :=
    smodEq_iff.2 (by simpa using h0)
  exact this

theorem exists_tends [IsAdicComplete (Ideal.span {ϖ}) T] (x : ℕ → T)
    (h : ∀ k, ∃ M, ∀ m, M ≤ m → x m - x M ∈ Ideal.span {ϖ ^ k}) : ∃ L, Tends ϖ x L := by
  choose M hM using h
  let N : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup M
  have hN : ∀ k, M k ≤ N k := fun k => Finset.le_sup (Finset.self_mem_range_succ k)
  have hmono : Monotone N := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hab))
  have hc : ∀ k m, N k ≤ m → x m - x (N k) ∈ Ideal.span {ϖ ^ k} := fun k m hm => by
    have := sub_mem (hM k m ((hN k).trans hm)) (hM k (N k) (hN k))
    simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) T)
    (f := fun k => x (N k)) (fun {a b} hab => smodEq_iff.2 (by
      have := hc a (N b) (hmono hab)
      rw [← neg_sub]
      exact neg_mem this))
  refine ⟨L, fun k => ⟨N k, fun m hm => ?_⟩⟩
  have := add_mem (hc k m hm) (smodEq_iff.1 (hL k))
  simpa using this

theorem Tends.add {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m + y m) (a + b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (hM m ((le_max_left _ _).trans hm)) (hM' m ((le_max_right _ _).trans hm))
  convert this using 1; ring

theorem Tends.mul {x y : ℕ → T} {a b : T} (hx : Tends ϖ x a) (hy : Tends ϖ y b) :
    Tends ϖ (fun m => x m * y m) (a * b) := fun k => by
  obtain ⟨M, hM⟩ := hx k
  obtain ⟨M', hM'⟩ := hy k
  refine ⟨max M M', fun m hm => ?_⟩
  have := add_mem (Ideal.mul_mem_right (y m) _ (hM m ((le_max_left _ _).trans hm)))
    (Ideal.mul_mem_left _ a (hM' m ((le_max_right _ _).trans hm)))
  convert this using 1; ring

theorem tends_const (a : T) : Tends ϖ (fun _ => a) a := fun k => ⟨0, fun _ _ => by simp⟩

theorem exists_lim_hom {S : Type} [CommRing S] [IsAdicComplete (Ideal.span {ϖ}) T] (a : ℕ → S →+* T)
    (h : ∀ f k, ∃ M, ∀ m, M ≤ m → a m f - a M f ∈ Ideal.span {ϖ ^ k}) :
    ∃ ψ : S →+* T, ∀ f, Tends ϖ (fun m => a m f) (ψ f) := by
  choose L hL using fun f => exists_tends (ϖ := ϖ) (fun m => a m f) (h f)
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hL⟩
  · exact (hL 1).unique (by simpa using tends_const (ϖ := ϖ) (1 : T))
  · intro f g
    exact (hL (f * g)).unique (by simpa using (hL f).mul (hL g))
  · exact (hL 0).unique (by simpa using tends_const (ϖ := ϖ) (0 : T))
  · intro f g
    exact (hL (f + g)).unique (by simpa using (hL f).add (hL g))

end Lim

variable {l : ℕ} [Fact l.Prime]

theorem exists_period (A : PAlg l) (f : (A.cont ℤ_[l]).A) (k : ℕ) :
    ∃ M : ℕ, ∀ z z' : ℤ_[l], PadicInt.toZModPow M z = PadicInt.toZModPow M z' →
      Hom.f (A.evCont z) f - Hom.f (A.evCont z') f ∈ Ideal.span {A.pi ^ k} := by
  obtain ⟨M, hM⟩ := GlobalTheory.CompanionTheory.PadicShift.exists_period l _ (f.2 k)
  refine ⟨M, fun z z' h => Ideal.Quotient.eq.1 (hM z z' ?_)⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h, sub_self]

end GlobalTheory.CompanionTheory.ContUniv
