import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DualMFst
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.DualMSmulOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftConj

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem tri_mul {X : Type} [CommRing X] {n : ℕ} (M N : Matrix (Fin n) (Fin n) X)
    (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) :
    (∀ i j, j < i → (M * N) i j = 0) ∧ ∀ i, M i i = 0 → (M * N) i i = 0 := by
  constructor
  · intro i j hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [hM i k hk, zero_mul]
    · rw [hN k j (lt_of_lt_of_le hij hk), mul_zero]
  · intro i hi
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_trichotomy k i with hk | rfl | hk
    · rw [hM i k hk, zero_mul]
    · rw [hi, zero_mul]
    · rw [hN k i hk, mul_zero]

private theorem conj_id {O A : Type} [CommRing O] [Ring A] [Algebra O A] (c : O) (W Wi P Pi d Y : A)
    (h1 : Wi * W = 1) (h2 : W * Wi = 1) (h3 : P * Pi = 1) :
    Wi * (c • (d * Pi) - (P * (W * Y * Wi) * Pi - W * Y * Wi)) * W =
      (c • (Wi * d * W) - ((Wi * P * W) * Y - Y * (Wi * P * W))) * (Wi * Pi * W) := by
  have e1 : ∀ Z : A, W * (Wi * Z) = Z := fun Z => by rw [← mul_assoc, h2, one_mul]
  have e2 : ∀ Z : A, Wi * (W * Z) = Z := fun Z => by rw [← mul_assoc, h1, one_mul]
  have e3 : ∀ Z : A, P * (Pi * Z) = Z := fun Z => by rw [← mul_assoc, h3, one_mul]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, e1, e2, e3, h1, h2, h3, mul_one]

theorem UpperTheory.V.Th.Coc.locAt :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n) (v : L.Vl), ∃ c₁ : O, c₁ ≠ 0 ∧ ∀ (G : Glob l L) (h : G.Hom G0) (R : Type) [CommRing R] [Algebra O R] (x : R →ₐ[O] O) (m : ℕ) (δ : R →ₗ[O] Om O m) (τ : MonoidAlgebra R G.G₀ → R) (c : O) (d : MonoidAlgebra R G.G₀ →+ Matrix (Fin n) (Fin n) (Om O m)) (ψ : Fin n → L.Gv v →* Rˣ), IsLift x δ (repR x (mat (y.ρ.comp h.p₀))) τ c d → (∀ i g, x (ψ i g : Rˣ) = (y.ψ v i g : Oˣ)) → (∀ g, repR x (mat (y.ρ.comp h.p₀)) (G.frame.oEl v ψ g) = 0 ∧ d (G.frame.oEl v ψ g) = 0) → (∀ i, ∀ g ∈ G.frame.mu v, δ (ψ i g : Rˣ) = 0) → ∃ Y, LocAt G.frame (y.ρm h m) (fun v => red m (y.w v)) (fun v => red m ((y.w v)⁻¹ : GL (Fin n) O)) (fun g => c₁ • (d (MonoidAlgebra.single g 1) * y.ρm h m g⁻¹)) v Y := by
  intro l _ L G0 n O _ _ _ _ y v
  obtain ⟨s, hs⟩ := y.reg v
  let r : L.Gv v → Matrix (Fin n) (Fin n) O := fun g =>
    (((y.w v)⁻¹ * y.ρ (G0.frame.φ v g) * y.w v : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)
  obtain ⟨c₁, hc₁, hfl⟩ := flag r (fun i g => ((y.ψ v i g : Oˣ) : O)) s
    (fun g => (y.tri v g).1) (fun g => (y.tri v g).2) (fun i j hij => hs (Units.ext hij))
  refine ⟨c₁, hc₁, ?_⟩
  intro G h R _ _ x m δ τ c d ψ hlift hψ hker hmu
  let W : GL (Fin n) O := y.w v
  let ρg : G.G₀ →* Matrix (Fin n) (Fin n) O := mat (y.ρ.comp h.p₀)
  let ρg' : G.G₀ →* Matrix (Fin n) (Fin n) O := mat ((MulAut.conj W⁻¹).toMonoidHom.comp (y.ρ.comp h.p₀))
  have hconj : ∀ a, repR x ρg' a = ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * repR x ρg a * ((W⁻¹⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) := by
    intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, mul_add, add_mul]
    | single g a =>
      rw [repR_single, repR_single, inv_inv, mul_smul_comm, smul_mul_assoc]
      rfl
  obtain ⟨d', hl', hd'⟩ := liftConj x δ (repR x ρg') (repR x ρg) τ c W⁻¹ d hconj hlift
  have hp : ∀ g : L.Gv v, h.p₀ (G.frame.φ v g) = G0.frame.φ v g := fun g => Subtype.ext (h.φ v g)
  have hr : ∀ g, ρg' (G.frame.φ v g) = r g := by
    intro g
    simp only [ρg', r, mat, MonoidHom.comp_apply, hp, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl
  have hD : ∀ gt : Fin n → L.Gv v, (List.ofFn fun i => dualM (bar (Om O m) (r (gt i))) (d' (MonoidAlgebra.single (G.frame.φ v (gt i)) 1)) - (TrivSqZeroExt.inl (algebraMap O (Om O m) ((y.ψ v i (gt i) : Oˣ) : O)) + TrivSqZeroExt.inr (c • δ ((ψ i (gt i) : Rˣ) : R))) • 1).prod = 0 := by
    intro gt
    have e := rel x δ ρg' τ c d' (fun g : L.Gv v => G.frame.φ v g) (fun i g => ((ψ i g : Rˣ) : R)) gt hl' ?_ ?_
    · simpa only [hr, hψ] using e
    · rw [hconj]
      show _ * repR x ρg (G.frame.oEl v ψ gt) * _ = 0
      rw [(hker gt).1, mul_zero, zero_mul]
    · rw [hd']
      show _ * d (G.frame.oEl v ψ gt) * _ = 0
      rw [(hker gt).2, mul_zero, zero_mul]
  obtain ⟨Y', hY'⟩ := hfl (Om O m) (fun g => d' (MonoidAlgebra.single (G.frame.φ v g) 1)) (fun i g => c • δ ((ψ i g : Rˣ) : R)) hD
  have hredm : ∀ A B : Matrix (Fin n) (Fin n) O, red m (A * B) = red m A * red m B := fun A B => Matrix.map_mul
  have hred1 : red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hbar : ∀ Z : Matrix (Fin n) (Fin n) O, bar (Om O m) Z = red m Z := fun Z => rfl
  have h1 : red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * red m (W : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hredm, ← Units.val_mul, inv_mul_cancel, Units.val_one, hred1]
  have h2 : red m (W : Matrix (Fin n) (Fin n) O) * red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) = 1 := by
    rw [← hredm, ← Units.val_mul, mul_inv_cancel, Units.val_one, hred1]
  have hd'' : ∀ a, red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * d a * red m (W : Matrix (Fin n) (Fin n) O) = d' a := by
    intro a
    rw [hd', inv_inv]
    rfl
  have hPr : ∀ g : G.G₀, ∀ g0 : L.Gv v, h.p₀ g = G0.frame.φ v g0 →
      red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * y.ρm h m g * red m (W : Matrix (Fin n) (Fin n) O) = bar (Om O m) (r g0) := by
    intro g g0 hg
    rw [hbar]
    show red m _ * red m _ * red m _ = red m _
    rw [← hredm, ← hredm]
    congr 1
    show ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * ((y.ρ (h.p₀ g) : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (W : Matrix (Fin n) (Fin n) O) = _
    rw [hg]
    simp only [r, W, Units.val_mul]
  refine ⟨red m (W : Matrix (Fin n) (Fin n) O) * Y' * red m ((W⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O), fun g => ?_⟩
  have h3 : y.ρm h m (G.frame.φ v g) * y.ρm h m (G.frame.φ v g)⁻¹ = 1 := by
    show red m _ * red m _ = 1
    rw [← hredm, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, hred1]
  simp only [UpperTheory.V.Pa.dY]
  rw [conj_id c₁ _ _ _ _ _ Y' h1 h2 h3, hd'', hPr _ g (hp g), hPr _ g⁻¹ (by rw [map_inv, hp, map_inv])]
  have hN : ∀ i j, j < i → bar (Om O m) (r g⁻¹) i j = 0 := by
    intro i j hij
    show algebraMap O (Om O m) (r g⁻¹ i j) = 0
    rw [show r g⁻¹ i j = 0 from (y.tri v g⁻¹).1 i j hij, map_zero]
  have T := tri_mul _ _ (hY' g).1 hN
  refine ⟨T.1, fun hg i => T.2 i ?_⟩
  rw [(hY' g).2 i, hmu i g hg, smul_zero, smul_zero]
