import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleNegMono

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

def vecE (n' : ℕ) : Fin n' → Bool := fun s => decide (Even s.val)

def flW {n' m : ℕ} (d : Fin n' → ℕ) : Fin n' → Fin (m + 1) → ℤ := fun s => Pi.single 0 (d s : ℤ)

theorem isFlat_flW {n' m : ℕ} (d : Fin n' → ℕ) : IsFlat (m := m) (vecE n') d (flW d) := by
  intro s
  by_cases hs : Even s.val
  · simp [lamAt, vecE, flW, hs]
  · funext i
    simp only [lamAt, vecE, flW, hs, if_false, decide_false, Bool.false_eq_true]
    by_cases hi : i = Fin.last m
    · subst hi
      simp
    · have hr : i.rev ≠ 0 := by
        intro h0
        apply hi
        rw [← Fin.rev_rev i, h0, Fin.rev_zero]
      simp [hi, hr]

theorem LLT_eq (n' : ℕ) : LLT n' = flatLetters (vecE n') := rfl

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_shift (c : Kf) (hc : c ≠ 0) (a b : ℕ) (M : Submodule O X) {x : X}
    (hx : x ∈ scale (c ^ ((a + b : ℕ) : ℤ)) M) : (c ^ (-(a : ℤ))) • x ∈ scale (c ^ (b : ℤ)) M := by
  rw [mem_scale] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, hy, ?_⟩
  rw [smul_smul, ← zpow_add₀ hc, show -(a : ℤ) + ((a + b : ℕ) : ℤ) = b by push_cast; ring]

end Scale

def IsFlatIdent {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) [Algebra (WF p n') O] {m : ℕ} (r : ℕ)
    (d : Fin n' → ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (vec : Fin n' → Bool)
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf lam0)) : Prop :=
  (∀ F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
    InA (O := O) (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ↔
    Θ F ∈ HL (O := O) ι σ lam0 (colSpan W h)) ∧
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
    ∀ e : Edge W Qq (m + 1), IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) →
      ∀ (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (i : ℕ),
        InWjRg p n' O w r (flatLetters vec) g
          (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) i ↔
        Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (Re p ι σ w r lam0 e)

theorem flatSrc (hEP : EdgePlane) (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field Kf] [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (m r : ℕ) (d : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit h.det) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)),
      IsFlatIdent ι σ w φ r d (flW d) (vecE n') h Θ →
    ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
    ∀ e : Edge W Qq (m + 1), IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) →
    ∀ (c' o : ℕ) (sig : MvPolynomial (TV n' (m + 1)) (KK O))
      (Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)),
      HasMultideg sig d → subst p n' O w n' r g (Fsig : MvPolynomial (TV n' (m + 1)) (KK O)) = sig →
      Realisable p n' w n' r g c' o sig →
      ∃ Fv : Vsp Kf (flW (m := m) d),
        Fv ∈ scale (algebraMap O Kf w ^ (-(o : ℤ))) (HL (O := O) ι σ (flW d) (colSpan W h)) ∧
        Fv - Θ Fsig ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r (flW d) e) ∧
        ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = colSpan W h → e' ≠ e →
          Fv ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r (flW d) e') := by
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro Θ hΘ g hg e he c' o sig Fsig hsig hsub hreal
  obtain ⟨F, hFA, hFdeg, hFW, hFo⟩ := hreal
  obtain ⟨F', rfl⟩ : ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
      (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) = F := ⟨⟨F, hFdeg d hsig⟩, rfl⟩
  have hc0 : algebraMap O Kf w ≠ 0 := w_ne_zero hS
  obtain ⟨hE1, -, hE3⟩ := hEP p n' W Qq O Kf ι σ j w hS φ hφ m r h hh
  refine ⟨(algebraMap O Kf w ^ (-(o : ℤ))) • Θ F', ?_, ?_, ?_⟩
  · exact mem_scale.mpr ⟨Θ F', (hΘ.1 F').mp hFA, rfl⟩
  · have key : InWjRg p n' O w r (flatLetters (vecE n')) g
        ((F' - (w ^ o) • Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
          MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + c') := by
      show InWj w (subst p n' O w n' r g _) (o + c')
      have hx : ((F' - (w ^ o) • Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
          MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) =
          (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) -
            C (algebraMap O (KK O) (w ^ o)) * (Fsig : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) := by
        rw [Submodule.coe_sub, Submodule.coe_smul_of_tower, ← algebraMap_smul (KK O), smul_eq_C_mul]
      rw [hx, map_sub, map_mul, hsub, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        MvPolynomial.algebraMap_eq]
      exact hFW
    have hmem := scale_shift (algebraMap O Kf w) hc0 o c' _ ((hΘ.2 g hg e he _ (o + c')).mp key)
    have heq : (algebraMap O Kf w ^ (-(o : ℤ))) • Θ (F' - (w ^ o) • Fsig) =
        (algebraMap O Kf w ^ (-(o : ℤ))) • Θ F' - Θ Fsig := by
      rw [map_sub, map_smul, ← algebraMap_smul Kf (w ^ o), smul_sub, smul_smul, map_pow,
        ← zpow_natCast, ← zpow_add₀ hc0, neg_add_cancel, zpow_zero, one_smul]
    rwa [heq] at hmem
  · intro e' he' hsrc hne
    obtain ⟨g', hg', hb'⟩ := hE1 e' he' hsrc
    have hrat : ratPlane p n' r g' ≠ ratPlane p n' r g := fun hr =>
      hne ((hE3 g' g e' e hg' hg hb' he).mpr hr)
    exact scale_shift (algebraMap O Kf w) hc0 o c' _
      ((hΘ.2 g' hg' e' hb' F' (o + c')).mp (hFo g' hg' hrat))

end Formalism.MainNotions.Pf14
