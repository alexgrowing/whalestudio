import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemBase
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

noncomputable section

namespace GlobalTheory.RootSum

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j)

theorem mult_tau (t : D.what₂.Tau) : S.Dw.mult (DV.tauEmb D t) = S.Dw.p := by
  simp [Datum.mult, A.cm t]

theorem conj_tau_ne (t : D.what₂.Tau) : conjEmb (DV.tauEmb D t) (A.H.rt : D.host.E) ≠ A.H.rt0 := by
  intro h
  have h1 : starRingEnd ℂ A.H.rt0 = A.H.rt0 := by
    have h0 : DV.tauEmb D t (A.H.rt : D.host.E) = A.H.rt0 := A.cm t
    rw [← h0] at h ⊢
    exact h
  have hd : (0 : ℝ) < A.H.d := by exact_mod_cast A.H.d_prime.pos
  have h2 := congrArg Complex.re A.H.sqrt_neg_disc_sq
  have h3 : A.H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  simp [pow_two, h3] at h2
  nlinarith [sq_nonneg A.H.rt0.re]

theorem mult_conj_tau (t : D.what₂.Tau) : S.Dw.mult (conjEmb (DV.tauEmb D t)) = S.Dw.q := by
  rw [Datum.mult, if_neg (conj_tau_ne t)]

theorem tau_inj' {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_conjEmb' (σ : D.host.E →+* ℂ) : conjEmb (conjEmb σ) = σ :=
  RingHom.ext fun a => by simp [conjEmb]

theorem eq_tau_or_conj (σ : D.host.E →+* ℂ) :
    (σ (A.H.rt : D.host.E) = A.H.rt0 ∧ ∃ t, σ = DV.tauEmb D t) ∨
      (σ (A.H.rt : D.host.E) ≠ A.H.rt0 ∧ ∃ t, σ = conjEmb (DV.tauEmb D t)) := by
  have hmem : ∀ ρ : D.host.E →+* ℂ, ρ ∈ cmTypeOfSqrt D ↔ ρ (A.H.rt : D.host.E) = A.H.rt0 := fun ρ => by
    rw [mem_cm_type_iff, A.rt_eq, A.cmHost_rootComplex_eq_pm_sqrt]
  by_cases h : σ (A.H.rt : D.host.E) = A.H.rt0
  · exact Or.inl ⟨h, DatOf.exists_tauEmb D ((hmem σ).2 h)⟩
  · refine Or.inr ⟨h, ?_⟩
    have hc : ComplexEmbedding.conjugate σ ∈ cmTypeOfSqrt D := by
      by_contra hc
      exact h ((hmem σ).1 ((cm_type_mem_iff_conj_not_mem D σ).2 hc))
    obtain ⟨t, ht⟩ := DatOf.exists_tauEmb D hc
    refine ⟨t, RingHom.ext fun a => ?_⟩
    have := congrArg (fun ρ : D.host.E →+* ℂ => starRingEnd ℂ (ρ a)) ht
    simp only [ComplexEmbedding.conjugate_coe_eq, Function.comp_apply, RingHomCompTriple.comp_apply,
      Complex.conj_conj] at this
    simpa [conjEmb] using this

def rootLetter (x : DV.Rt D.what₂.Tau N) : Letter S.Dw :=
  if h : (x.2 : ℕ) < S.Dw.p then ⟨DV.tauEmb D x.1, ⟨x.2, by rw [mult_tau]; exact h⟩⟩
  else ⟨conjEmb (DV.tauEmb D x.1), ⟨S.Dw.p + S.Dw.q - 1 - x.2, by
    rw [mult_conj_tau]; have := S.rank_eq; have := x.2.2; omega⟩⟩

open Classical in

theorem rootExp_eq (x : DV.Rt D.what₂.Tau N) (l : Letter S.Dw) :
    rootExp S x l = if l = rootLetter S x then (if (x.2 : ℕ) < S.Dw.p then 1 else -1) else 0 := by
  classical
  simp only [rootExp, rootEx, rootSym]
  by_cases h : (x.2 : ℕ) < S.Dw.p
  · have hm : (x.2 : ℕ) < S.Dw.mult (DV.tauEmb D x.1) := by rw [mult_tau]; exact h
    simp only [if_pos h, expo_single, letterOf, dif_pos hm, rootLetter, dif_pos h, Option.some.injEq]
    by_cases e : l = ⟨DV.tauEmb D x.1, ⟨x.2, hm⟩⟩ <;> simp [e, eq_comm]
  · have hm : S.Dw.p + S.Dw.q - 1 - (x.2 : ℕ) < S.Dw.mult (conjEmb (DV.tauEmb D x.1)) := by
      rw [mult_conj_tau]; have := S.rank_eq; have := x.2.2; omega
    simp only [if_neg h, expo_single, letterOf, dif_pos hm, rootLetter, dif_neg h, Option.some.injEq]
    by_cases e : l = ⟨conjEmb (DV.tauEmb D x.1), ⟨_, hm⟩⟩ <;> simp [e, eq_comm]

theorem rootLetter_key (x : DV.Rt D.what₂.Tau N) :
    ((rootLetter S x).1, ((rootLetter S x).2 : ℕ)) =
      if (x.2 : ℕ) < S.Dw.p then (DV.tauEmb D x.1, (x.2 : ℕ))
      else (conjEmb (DV.tauEmb D x.1), S.Dw.p + S.Dw.q - 1 - x.2) := by
  by_cases h : (x.2 : ℕ) < S.Dw.p
  · rw [rootLetter, dif_pos h, if_pos h]
  · rw [rootLetter, dif_neg h, if_neg h]

theorem letter_ext {l l' : Letter S.Dw} (h : (l.1, (l.2 : ℕ)) = (l'.1, (l'.2 : ℕ))) : l = l' := by
  obtain ⟨a, i⟩ := l
  obtain ⟨b, k⟩ := l'
  obtain ⟨rfl, h'⟩ := Prod.mk.inj h
  obtain rfl : i = k := Fin.ext h'
  rfl

theorem rootLetter_bijective : Function.Bijective (rootLetter S) := by
  have hr := S.rank_eq
  have key : ∀ x y, rootLetter S x = rootLetter S y →
      ((rootLetter S x).1, ((rootLetter S x).2 : ℕ)) = ((rootLetter S y).1, ((rootLetter S y).2 : ℕ)) :=
    fun x y h => by rw [h]
  refine ⟨fun x y hxy => ?_, fun l => ?_⟩
  · have e := key x y hxy
    rw [rootLetter_key, rootLetter_key] at e
    have hx := x.2.2
    have hy := y.2.2
    split_ifs at e with h1 h2 h2
    · obtain ⟨e1, e2⟩ := Prod.mk.inj e
      exact Prod.ext (tau_inj' e1) (Fin.ext e2)
    · exact absurd (Prod.mk.inj e).1 (fun h => conj_tau_ne y.1 (h ▸ A.cm x.1))
    · exact absurd (Prod.mk.inj e).1 (fun h => conj_tau_ne x.1 (h.symm ▸ A.cm y.1))
    · obtain ⟨e1, e2⟩ := Prod.mk.inj e
      have e1' : DV.tauEmb D x.1 = DV.tauEmb D y.1 := by
        have := congrArg conjEmb e1
        simpa [conjEmb_conjEmb'] using this
      exact Prod.ext (tau_inj' e1') (Fin.ext (by omega))
  · obtain ⟨σ, i⟩ := l
    rcases eq_tau_or_conj (A := A) σ with ⟨hσ, t, rfl⟩ | ⟨hσ, t, rfl⟩
    · have hi : (i : ℕ) < S.Dw.p := by have := i.isLt; have := mult_tau S t; omega
      refine ⟨(t, ⟨i, by omega⟩), letter_ext S ?_⟩
      rw [rootLetter_key, if_pos hi]
    · have hi : (i : ℕ) < S.Dw.q := by have := i.isLt; have := mult_conj_tau S t; omega
      have hn : ¬ (S.Dw.p + S.Dw.q - 1 - i < S.Dw.p) := by omega
      refine ⟨(t, ⟨S.Dw.p + S.Dw.q - 1 - i, by omega⟩), letter_ext S ?_⟩
      rw [rootLetter_key, if_neg hn]
      exact Prod.ext rfl (by dsimp only; omega)

theorem divOf_root {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (k : s.Comp) (x : DV.Rt D.what₂.Tau N) :
    divOf (Φ.C k) (rootExp S x) =
      (if (x.2 : ℕ) < S.Dw.p then 1 else -1 : ℤ) • (Φ.C k).gr (rootLetter S x).1 (rootLetter S x).2 := by
  classical
  rw [divOf]
  simp_rw [rootExp_eq, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp

end GlobalTheory.RootSum

namespace GlobalTheory.RootSum

theorem sum_two_roots_ge : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp), (∑ x : DV.Rt D.what₂.Tau N, (if (x.2 : ℕ) < j then 0 else 2 : ℤ) • divOf (Φ.C k) (rootExp S x)) = -(∑ x : Letter S.Dw, (Φ.C k).gr x.1 x.2) + ∑ x : DV.Rt D.what₂.Tau N, divOf (Φ.C k) (rootExp S x) := by
  intro D A N j S κ s Φ k
  rw [← Fintype.sum_bijective (rootLetter S) (rootLetter_bijective S)
    (fun x => (Φ.C k).gr (rootLetter S x).1 (rootLetter S x).2) (fun x : Letter S.Dw => (Φ.C k).gr x.1 x.2)
    (fun _ => rfl)]
  simp_rw [divOf_root, S.p_eq]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · simp
  · simp only [neg_smul, one_smul, smul_neg]
    rw [two_smul]
    abel

end GlobalTheory.RootSum
