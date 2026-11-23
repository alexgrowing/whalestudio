import Development.EtaleCohomology.EtaleSheaves.LeafRoofPf

noncomputable section
open LateralTheory.E.t_E6Cut

namespace LateralTheory.E.LeafRoofEtPf

def LeafRoofEtP : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ∃ (P : Type) (_ : CommRing P) (a : B →+* P) (b : MvPolynomial (Fin d) (B ⧸ varIdeal φ) →+* P)
    (m : P →+* B ⧸ varIdeal φ) (e : P), a.Etale ∧ b.Etale ∧ (∀ j, a (φ (MvPolynomial.X j)) = b (MvPolynomial.X j)) ∧
    m.comp a = Ideal.Quotient.mk _ ∧ m.comp b = MvPolynomial.constantCoeff ∧
    m e = 0 ∧ e * e - e ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ∧
    ∀ x, m x = 0 → x ∈ Ideal.span (Set.range fun j => b (MvPolynomial.X j)) ⊔ Ideal.span {e}

theorem LeafRoofEt_of (h : LeafRoofEtP) : LateralTheory.E.LeafRoofPf.LeafRoofEt := by
  intro d C B _ _ φ hφ
  obtain ⟨P, _, a, b, m, e, ha, hb, hab, hma, hmb, hme, he, hk⟩ := h d φ hφ
  refine ⟨P, inferInstance, a, b, m, 1 - e, ha, hb, hab, hma, hmb, by simp [hme], fun x hx => ⟨1, ?_⟩⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hk x hx)
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  have : (1 - e) ^ 1 * (y + r * e) = (1 - e) * y - r * (e * e - e) := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ he)

end LateralTheory.E.LeafRoofEtPf
