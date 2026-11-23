import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Mem.Col2.IdxEx

theorem jat_le_stab_lamY {X : Fields} {Pr : Primes X} {R : Ranks} (sharp : Bool) (j : ℕ)
    (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Pr.vGs) (g : AutY X R j) (hg : g ∈ Jat (Pr := Pr) sharp j P) :
    g ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P) := by
  unfold Jat at hg
  rw [if_pos hP] at hg
  unfold lamYat
  rw [if_pos hP]
  split_ifs at hg
  · exact hg.1
  · exact hg.1

theorem prCat_le_GLint : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P), prCat (Pr := Pr) sharp j P h ≤ GLint X.E (R.N j) P := by
  intro X Pr R sharp j P hP h hh g hg
  obtain ⟨r, ⟨-, hr⟩, hrg⟩ := hg
  have e : (MulAut.conj h⁻¹).toMonoidHom r = h⁻¹ * r * h := by simp
  have hr' : (MulAut.conj h⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) sharp j P := hr
  rw [e] at hr'
  have h1 := jat_le_stab_lamY sharp j P hP _ hr'
  have h2 := mul_mem (mul_mem hh h1) (inv_mem hh)
  have e2 : h * (h⁻¹ * r * h) * h⁻¹ = r := by group
  rw [e2] at h2
  unfold lamYat at h2
  rw [if_pos hP] at h2
  have key : ∀ x : Sp X.E (R.N j), Loc.inX X.E (R.N j) (cOf R j) x ∈
      LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1) ↔ x ∈ stdAt X.E (R.N j) P := fun x =>
    ⟨fun hx => by simpa only [GlobalTheory.CongLevel.resX_inX] using GlobalTheory.CongLevel.resX_mem P _ _ _ _ hx,
      GlobalTheory.CongLevel.inX_mem_lamY P _ _ _ x⟩
  intro x
  have h3 := h2 (Loc.inX X.E (R.N j) (cOf R j) x)
  rw [hrg x] at h3
  exact (key _).symm.trans (h3.trans (key _))

end GlobalTheory.Mem.Col2.IdxEx
