import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SCls
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CoeffSlD

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

noncomputable section

namespace UpperTheory.V.Z.Kato.Nb.InverseLimitApi

private def Fm (R : Type) [CommRing R] (w : ℕ) : Submodule R ((Fin 2 → R) → R) :=
  Submodule.span R {φ | ∃ i j : ℕ, i + j = w ∧ φ = fun u => u 0 ^ i * u 1 ^ j}

private theorem fm_mul {R : Type} [CommRing R] {a b : ℕ} {φ ψ : (Fin 2 → R) → R} (hφ : φ ∈ Fm R a) (hψ : ψ ∈ Fm R b) :
    φ * ψ ∈ Fm R (a + b) := by
  induction hφ using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul k x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  | mem x hx =>
    induction hψ using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul k x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
    | mem y hy =>
      obtain ⟨i, j, rfl, rfl⟩ := hx
      obtain ⟨i', j', rfl, rfl⟩ := hy
      refine Submodule.subset_span ⟨i + i', j + j', by omega, ?_⟩
      funext u
      simp only [Pi.mul_apply]
      ring

private theorem fm_pow {R : Type} [CommRing R] {φ : (Fin 2 → R) → R} (hφ : φ ∈ Fm R 1) (k : ℕ) : φ ^ k ∈ Fm R k := by
  induction k with
  | zero => exact Submodule.subset_span ⟨0, 0, rfl, by funext u; simp⟩
  | succ k ih => rw [pow_succ]; exact fm_mul ih hφ

private theorem fm_lin {R : Type} [CommRing R] (m : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) :
    (fun u => (m *ᵥ u) i) ∈ Fm R 1 := by
  have h0 : (fun u : Fin 2 → R => u 0 ^ 1 * u 1 ^ 0) ∈ Fm R 1 := Submodule.subset_span ⟨1, 0, rfl, rfl⟩
  have h1 : (fun u : Fin 2 → R => u 0 ^ 0 * u 1 ^ 1) ∈ Fm R 1 := Submodule.subset_span ⟨0, 1, rfl, rfl⟩
  have h := add_mem (Submodule.smul_mem _ (m i 0) h0) (Submodule.smul_mem _ (m i 1) h1)
  convert h using 1
  funext u
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem un_pow (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) (j : ℕ) : f ^ j ∈ X.Un m := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
  induction j with
  | zero => simpa using (h m).1
  | succ j ih => rw [pow_succ]; exact ((h m).2 _ ih _ hf).1

private def Cf (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) : Submodule ℤ_[l] (X.Khat l) where
  carrier := {x | ∃ f ∈ X.Un (l ^ n), Rep X l n f x}
  zero_mem' := by
    obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
    obtain ⟨h1, -, h3, -⟩ := sCls Ω ε X l n
    refine ⟨1, (h _).1, ?_⟩
    simpa using h3 1 _ 0 (h1 1)
  add_mem' := by
    rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
    obtain ⟨-, -, -, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
    obtain ⟨-, h2, -⟩ := sCls Ω ε X l n
    exact ⟨f * g, ((h _).2 f hf g hg).1, (h2 _ _ _ _ ha hb).1⟩
  smul_mem' := by
    rintro k a ⟨f, hf, ha⟩
    obtain ⟨-, -, -, -, -, -, h⟩ := sCls Ω ε X l n
    obtain ⟨j, hj⟩ := h f k a ha
    exact ⟨f ^ j, un_pow X _ f hf j, hj⟩

private def Pm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) : Submodule ℤ_[l] (X.Fn l) where
  carrier := {t | PolMod X l w n t}
  zero_mem' := ⟨0, fun _ => (Cf X l n).zero_mem, fun u => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    refine ⟨c + d, fun i => (Cf X l n).add_mem (hc i) (hd i), fun u => ?_⟩
    simp only [Pi.add_apply, ha u, hb u, smul_add, Finset.sum_add_distrib]
  smul_mem' := by
    rintro k a ⟨c, hc, ha⟩
    refine ⟨k • c, fun i => (Cf X l n).smul_mem k (hc i), fun u => ?_⟩
    simp only [Pi.smul_apply, ha u, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

private theorem pm_fm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (c : X.Khat l) (hc : c ∈ Cf X l n)
    (φ : (Fin 2 → ℤ_[l]) → ℤ_[l]) (hφ : φ ∈ Fm ℤ_[l] w) : (fun u => φ u • c) ∈ Pm X l w n := by
  induction hφ using Submodule.span_induction with
  | zero =>
    convert (Pm X l w n).zero_mem using 1
    funext u; simp
  | add x y _ _ hx hy =>
    convert (Pm X l w n).add_mem hx hy using 1
    funext u; simp [add_smul]
  | smul k x _ hx =>
    convert (Pm X l w n).smul_mem k hx using 1
    funext u; simp [mul_smul]
  | mem x hx =>
    obtain ⟨i, j, rfl, rfl⟩ := hx
    refine ⟨Pi.single ⟨i, by omega⟩ c, fun k => ?_, fun u => ?_⟩
    · show Pi.single (M := fun _ => X.Khat l) _ c k ∈ Cf X l n
      rw [Pi.single_apply]
      split_ifs
      · exact hc
      · exact zero_mem _
    · rw [Finset.sum_eq_single (⟨i, by omega⟩ : Fin (i + j + 1))]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, smul_zero]
      · simp

private theorem pm_act (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (t : X.Fn l)
    (ht : PolMod X l w n t) : PolMod X l w n (X.act l m t) := by
  obtain ⟨c, hc, ht⟩ := ht
  have key : ∀ i : Fin (w + 1), (fun u => (((fun u => (mZl l m *ᵥ u) 0) ^ (i : ℕ) * (fun u => (mZl l m *ᵥ u) 1) ^ (w - (i : ℕ)) :
      (Fin 2 → ℤ_[l]) → ℤ_[l]) u) • X.kmap l (X.sl (toGQ m)).toRingEquiv (c i)) ∈ Pm X l w n := by
    intro i
    apply pm_fm
    · obtain ⟨f, hf, hr⟩ := hc i
      obtain ⟨-, -, -, -, h, -⟩ := sSlD Ω ε X 1 one_pos
      obtain ⟨-, -, -, -, h', -⟩ := sCls Ω ε X l n
      exact ⟨slU X (toGQ m) f, h _ _ f hf, h' (X.sl (toGQ m)).toRingEquiv f _ hr⟩
    · have := fm_mul (fm_pow (fm_lin (mZl l m) 0) i) (fm_pow (fm_lin (mZl l m) 1) (w - i))
      rwa [show (i : ℕ) + (w - i) = w by omega] at this
  have h := (Pm X l w n).sum_mem fun i (_ : i ∈ Finset.univ) => key i
  show X.act l m t ∈ Pm X l w n
  convert h using 1
  funext u
  show X.kmap l _ (t _) = _
  rw [ht, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl

private theorem pm_down (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (w n : ℕ) (t : X.Fn l)
    (ht : PolMod X l w (n + 1) t) : PolMod X l w n t := by
  obtain ⟨c, hc, ht⟩ := ht
  refine ⟨c, fun i => ?_, ht⟩
  obtain ⟨f, hf, hr⟩ := hc i
  obtain ⟨-, -, -, -, -, h, -⟩ := sCls Ω ε X l n
  refine ⟨f, fun W hW => ?_, h _ _ hr⟩
  obtain ⟨g, hg⟩ := hf W hW
  refine ⟨g ^ l, ?_⟩
  rw [Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ']
  exact hg

private def Im (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) : Submodule ℤ_[l] (X.Fn l) where
  carrier := {a | InvM X l N w n a}
  zero_mem' := by
    obtain ⟨he, -⟩ := sApi Ω ε X l n
    refine ⟨⟨0, (Pm X l w n).zero_mem, he.refl _⟩, fun γ _ => ?_, 0, zero_mem _, fun u => by simp⟩
    rw [map_zero]; exact he.refl _
  add_mem' := by
    rintro a b ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩ ⟨⟨s, hs, hbs⟩, hb, y, hy, hyb⟩
    obtain ⟨-, h, -⟩ := sApi Ω ε X l n
    refine ⟨⟨t + s, (Pm X l w n).add_mem ht hs, (h _ _ _ _ hat hbs).1⟩, fun γ hγ => ?_, x + y, add_mem hx hy, ?_⟩
    · rw [map_add]; exact (h _ _ _ _ (ha γ hγ) (hb γ hγ)).1
    · have := (h x ((l : ℤ_[l]) ^ cL X l N w • a) y ((l : ℤ_[l]) ^ cL X l N w • b) hxa hyb).1
      rw [← smul_add] at this
      exact this
  smul_mem' := by
    rintro k a ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩
    obtain ⟨-, -, h, -⟩ := sApi Ω ε X l n
    refine ⟨⟨k • t, (Pm X l w n).smul_mem k ht, h _ _ _ hat⟩, fun γ hγ => ?_, k • x, Submodule.smul_mem _ _ hx, ?_⟩
    · rw [map_smul]; exact h _ _ _ (ha γ hγ)
    · have := h k x ((l : ℤ_[l]) ^ cL X l N w • a) hxa
      rw [smul_comm] at this
      exact this

private theorem main : SInvApi := by
  intro Ω _ _ _ ε X l _ N w n
  refine ⟨(Im X l N w n).zero_mem, fun a b ha hb => ⟨(Im X l N w n).add_mem ha hb, (Im X l N w n).sub_mem ha hb⟩,
    fun k a ha => (Im X l N w n).smul_mem k ha, ?_, fun ι S a h => (Im X l N w n).sum_mem h, ?_, ?_,
    fun m t _ ht => pm_act X l w n m t ht⟩
  · rintro a b hab ⟨⟨t, ht, hbt⟩, hb, x, hx, hxb⟩
    obtain ⟨he, -, hs, -, -, hm, -⟩ := sApi Ω ε X l n
    refine ⟨⟨t, ht, he.trans hab hbt⟩, fun γ hγ => he.trans (hm _ _ _ hab) (he.trans (hb γ hγ) (he.symm hab)), x, hx, ?_⟩
    exact he.trans (x := x) (y := (l : ℤ_[l]) ^ cL X l N w • b) hxb (hs _ _ _ (he.symm hab))
  · rintro a ⟨⟨t, ht, hat⟩, ha, x, hx, hxa⟩
    obtain ⟨-, -, -, -, -, -, -, h, -⟩ := sApi Ω ε X l n
    exact ⟨⟨t, pm_down X l w n t ht, h _ _ hat⟩, fun γ hγ => h _ _ (ha γ hγ), x, hx,
      h x ((l : ℤ_[l]) ^ cL X l N w • a) hxa⟩
  · intro a
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := sApi Ω ε X l n
    exact ⟨⟨0, (Pm X l w 0).zero_mem, h _ _⟩, fun γ _ => h _ _, 0, zero_mem _, h 0 ((l : ℤ_[l]) ^ cL X l N w • a)⟩

end UpperTheory.V.Z.Kato.Nb.InverseLimitApi

theorem UpperTheory.V.Z.Kato.Nb.sInvApi :
    UpperTheory.V.Z.Kato.Nb.SInvApi :=
  UpperTheory.V.Z.Kato.Nb.InverseLimitApi.main

end
