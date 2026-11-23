import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TowerGal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem up_diag_mul {R : Type} [CommRing R] {A B : M4 R} (hA : IsUp A) (hB : IsUp B) (i : Fin 4) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA i j h, zero_mul]
  · rw [hB j i h, mul_zero]

private theorem low_left {R : Type} [CommRing R] {N : M4 R} (h : IsLow N) : adj N * N = 1 := by
  have := h.1
  rwa [IsGSp, one_smul] at this

private theorem pair_psi_one {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] {Φ : Fr O Γ} {a : O →+* R}
    {Q : PD Φ.ι Γ R} (hQ : Φ.IsPair a Q) (v : Φ.ι) (i : Fin 4) : Q.ψ v i 1 = 1 := by
  rw [PD.ψ, map_one, mul_one, low_left (hQ.low v), Matrix.one_apply_eq]

private theorem pair_psi_mul {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] {Φ : Fr O Γ} {a : O →+* R}
    {Q : PD Φ.ι Γ R} (hQ : Φ.IsPair a Q) (v : Φ.ι) (i : Fin 4) {s t : Γ} (hs : s ∈ Φ.Gv v) (ht : t ∈ Φ.Gv v) :
    Q.ψ v i (s * t) = Q.ψ v i s * Q.ψ v i t := by
  rw [PD.ψ, PD.ψ, PD.ψ, ← up_diag_mul (hQ.flag v s hs) (hQ.flag v t ht), map_mul]
  have h1 : Q.n v * adj (Q.n v) = 1 := mul_eq_one_comm.1 (low_left (hQ.low v))
  have h2 : adj (Q.n v) * Q.r s * Q.n v * (adj (Q.n v) * Q.r t * Q.n v) =
      adj (Q.n v) * Q.r s * (Q.n v * adj (Q.n v)) * Q.r t * Q.n v := by
    simp only [mul_assoc]
  rw [h2, h1, mul_one, mul_assoc (adj (Q.n v)) (Q.r s)]

private theorem hasFlag_push {H A B : Type} [Group H] [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    {r : H →* GL (Fin n) A} {κ : Fin n → H →* Aˣ} (h : W.HasFlag r κ) :
    W.HasFlag (W.pushRep f r) fun i => W.pushCh f (κ i) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨Matrix.GeneralLinearGroup.map f g, fun s => ?_⟩
  have key : ∀ i j, (Matrix.GeneralLinearGroup.map f g * W.pushRep f r s * (Matrix.GeneralLinearGroup.map f g)⁻¹ :
      GL (Fin n) B) i j = f ((g * r s * g⁻¹ : GL (Fin n) A) i j) := by
    intro i j
    rw [MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, (hg s).1 i j hij, map_zero]
  · rw [key, (hg s).2 i]
    rfl

theorem UpperTheory.V.Ws.P1.psiEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (ρ : K.V.frame.G₀ →* GL (Fin 4) R), (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → K.IsRho ρ Q →
          ∃ ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* Rˣ, K.IsPsi ψ Q ∧ ∀ (R' : Type) [CommRing R'] (f : R →+* R') (v : K.V.frame.Vl),
            W.HasFlag (W.pushRep f (ρ.comp (K.V.frame.φ v))) fun i => W.pushCh f (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K R _ _ Q ρ hQ hρ
  have hd : ∀ (v : W.Vl l T.L) (g : Dec (F := T.L) (K.s.A v)), resLe T.F_le g ∈ (T.fr ∅).Gv (K.e v) := by
    intro v g
    have h1 : (g : G T.L Ω) ∈ Dec (F := T.L) (T.pl (K.e v)) := by
      rw [← K.hA]; exact g.2
    exact h1
  let p : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* R := fun v i =>
    { toFun := fun g => algebraMap c'.O R (K.κ g) * Q.ψ (K.e v) i (resLe T.F_le g)
      map_one' := by
        rw [OneMemClass.coe_one, map_one, map_one, Units.val_one, map_one, one_mul]
        exact pair_psi_one (Φ := T.fr ∅) hQ (K.e v) i
      map_mul' := fun g g' => by
        have h2 := pair_psi_mul (Φ := T.fr ∅) hQ (K.e v) i (hd v g) (hd v g')
        rw [Subgroup.coe_mul, map_mul, map_mul, Units.val_mul, map_mul]
        erw [h2]
        exact mul_mul_mul_comm _ _ _ _ }
  refine ⟨fun v i => (p v i).toHomUnits, fun v i g => rfl, fun R' _ f v => hasFlag_push f ?_⟩
  have h1 : adj (Q.n (K.e v)) * Q.n (K.e v) = 1 := low_left (hQ.low (K.e v))
  refine ⟨⟨adj (Q.n (K.e v)), Q.n (K.e v), h1, mul_eq_one_comm.mp h1⟩, fun s => ?_⟩
  have key : ∀ i j, ((⟨adj (Q.n (K.e v)), Q.n (K.e v), h1, mul_eq_one_comm.mp h1⟩ : GL (Fin 4) R) *
      (ρ.comp (K.V.frame.φ v)) s *
      (⟨adj (Q.n (K.e v)), Q.n (K.e v), h1, mul_eq_one_comm.mp h1⟩ : GL (Fin 4) R)⁻¹ : GL (Fin 4) R) i j =
      algebraMap c'.O R (K.κ s.1) *
        (adj (Q.n (K.e v)) * Q.r (resLe T.F_le s.1) * Q.n (K.e v)) i j := by
    intro i j
    change (adj (Q.n (K.e v)) * W.mat ρ (K.V.pr s.1) * Q.n (K.e v)) i j = _
    rw [hρ, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key]
    have := hQ.flag (K.e v) _ (hd v s) i j hij
    erw [this]
    exact mul_zero _
  · rw [key]
    rfl
