import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.PhiRootVal

def RootOrZero {K : Type} [Field K] (z : K) : Prop := z = 0 ∨ ∃ n : ℕ, 0 < n ∧ z ^ n = 1

variable {K : Type} [Field K]

theorem RootOrZero.zero : RootOrZero (0 : K) := Or.inl rfl

theorem RootOrZero.one : RootOrZero (1 : K) := Or.inr ⟨1, one_pos, one_pow 1⟩

theorem RootOrZero.mul {z w : K} (hz : RootOrZero z) (hw : RootOrZero w) : RootOrZero (z * w) := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · exact Or.inl (zero_mul w)
  rcases hw with rfl | ⟨m, hm, hw⟩
  · exact Or.inl (mul_zero z)
  refine Or.inr ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [mul_pow, pow_mul, hz, one_pow, one_mul, mul_comm n m, pow_mul, hw, one_pow]

theorem RootOrZero.inv {z : K} (hz : RootOrZero z) : RootOrZero z⁻¹ := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · exact Or.inl inv_zero
  exact Or.inr ⟨n, hn, by rw [inv_pow, hz, inv_one]⟩

theorem RootOrZero.prod {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, RootOrZero (f i)) :
    RootOrZero (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (RootOrZero.one : RootOrZero (1 : K))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem RootOrZero.intOff {z : K} (hz : RootOrZero z) (σ : K →+* ℂ) (S : Finset ℕ) : IntOff S (σ z) := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · rw [map_zero]; exact IntOff.zero
  exact IntOff.of_pow hn (by rw [← map_pow, hz, map_one])

theorem addChar_root {A : Type} [AddCommGroup A] [Finite A] (ψ : AddChar A K) (a : A) : RootOrZero (ψ a) := by
  refine Or.inr ⟨Nat.card A, Nat.card_pos, ?_⟩
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]

theorem hom_root {G : Type} [Group G] [Finite G] (χ : G →* Kˣ) (g : G) : RootOrZero ((χ g : Kˣ) : K) := by
  refine Or.inr ⟨Nat.card G, Nat.card_pos, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

section Loc
variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem unitV_root (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : RootOrZero (LocE.unitV χ a) := by
  unfold LocE.unitV
  split_ifs with h
  · exact hom_root χ _
  · exact RootOrZero.zero

end Loc
end GlobalTheory.PhiRootVal

namespace GlobalTheory.PhiRootVal
variable {K : Type} [Field K]
section Loc2
variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem phiQ_root (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x) :
    RootOrZero (LocE.PhiQ q ξ k₀ r c' n' c n x) := by
  unfold LocE.PhiQ
  split_ifs
  · exact unitV_root ξ _
  · exact RootOrZero.zero

theorem lamGv_root (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (r t j : ℕ) (M : ℕ → ℕ → E) :
    RootOrZero (LocE.lamGv ψ₀ χ r t j M) := by
  unfold LocE.lamGv
  exact (addChar_root ψ₀ _).mul (RootOrZero.prod _ _ fun i _ => unitV_root (χ i) _)

theorem lamGvS_root (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r t j : ℕ) (M : ℕ → ℕ → E) :
    RootOrZero (LocE.lamGvS ψ₀ χ k₀ r t j M) := by
  unfold LocE.lamGvS
  exact (addChar_root ψ₀ _).mul (RootOrZero.prod _ _ fun i _ => unitV_root (χ i) _)

theorem phiG_root (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (sharp : Bool)
    (k₀ r t j c' n' c n : ℕ) (x) : RootOrZero (LocE.PhiG q ψ₀ χ sharp k₀ r t j c' n' c n x) := by
  unfold LocE.PhiG
  dsimp only
  split_ifs
  · exact (lamGv_root ψ₀ χ _ _ _ _).mul (unitV_root _ _).inv
  · exact RootOrZero.zero

theorem phiGS_root (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x) : RootOrZero (LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x) := by
  unfold LocE.PhiGS
  dsimp only
  split_ifs
  · exact (lamGvS_root ψ₀ χ _ _ _ _ _).mul (unitV_root _ _).inv
  · exact RootOrZero.zero

end Loc2

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem phiAt_root (sharp : Bool) (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiAt (R := R) Ch mu sharp i P x) := by
  unfold PhiAt
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

theorem phiTop_root (sharp : Bool) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiTop (R := R) Ch mu sharp m2 P x) := by
  unfold PhiTop
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

end Chain

theorem phi_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ (P : HeightOneSpectrum (𝓞 t.X.E)), (∀ (i : ℕ) x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiAt (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp i P x))) ∧ ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x)) := by
  intro D L hT Gi Gl K Y cX ex t u μ P
  exact ⟨fun i x => (phiAt_root _ _ _ _ _ x).intOff _ _, fun x => (phiTop_root _ _ _ _ _ x).intOff _ _⟩

end GlobalTheory.PhiRootVal
