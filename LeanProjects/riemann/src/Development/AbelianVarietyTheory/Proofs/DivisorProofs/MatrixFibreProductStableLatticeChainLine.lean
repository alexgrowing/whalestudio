import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreLine

theorem cancel_left {O : Type} [CommRing O] {a b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => hA ?_
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

theorem cancel_left₂ {O : Type} [CommRing O] {a a' b c : ℕ} {A : Matrix (Fin a) (Fin b) O}
    {A' : Matrix (Fin a') (Fin b) O} (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    {X Y : Matrix (Fin b) (Fin c) O} (h : A * X = A * Y) (h' : A' * X = A' * Y) : X = Y := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  refine sub_eq_zero.mp (hA _ ?_ ?_)
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, sub_self]
  · rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h', sub_self]

theorem solve {O : Type} [CommRing O] {a b c : ℕ} (A : Matrix (Fin a) (Fin b) O) (B : Matrix (Fin a) (Fin c) O)
    (h : ∀ v, ∃ w, A *ᵥ w = B *ᵥ v) : ∃ S : Matrix (Fin b) (Fin c) O, B = A * S := by
  choose w hw using h
  refine ⟨Matrix.of fun i j => w (Pi.single j 1) i, Matrix.ext_of_mulVec_single fun j => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← hw]
  congr 1
  rw [Matrix.mulVec_single_one]
  rfl

theorem mkRep {Γ O : Type} [Group Γ] [CommRing O] {a a' m : ℕ} (A : Matrix (Fin a) (Fin m) O)
    (A' : Matrix (Fin a') (Fin m) O) (ρ : Γ →* GL (Fin a) O) (ρ' : Γ →* GL (Fin a') O)
    (hA : ∀ v, A *ᵥ v = 0 → A' *ᵥ v = 0 → v = 0)
    (hst : ∀ g v, ∃ w, A *ᵥ w = (ρ g : Matrix (Fin a) (Fin a) O) *ᵥ (A *ᵥ v) ∧
      A' *ᵥ w = (ρ' g : Matrix (Fin a') (Fin a') O) *ᵥ (A' *ᵥ v)) :
    ∃ r' : Γ →* GL (Fin m) O, Tw r' ρ A ∧ Tw r' ρ' A' := by
  choose w hw using hst
  let M : Γ → Matrix (Fin m) (Fin m) O := fun g => Matrix.of fun i j => w g (Pi.single j 1) i
  have hM : ∀ g j, M g *ᵥ Pi.single j 1 = w g (Pi.single j 1) := fun g j => by
    rw [Matrix.mulVec_single_one]
    rfl
  have k1 : ∀ g, A * M g = (ρ g : Matrix (Fin a) (Fin a) O) * A := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).1]
  have k2 : ∀ g, A' * M g = (ρ' g : Matrix (Fin a') (Fin a') O) * A' := fun g =>
    Matrix.ext_of_mulVec_single fun j => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, (hw g _).2]
  let f : Γ →* Matrix (Fin m) (Fin m) O :=
    { toFun := M
      map_one' := cancel_left₂ hA (by rw [k1, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
        (by rw [k2, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
      map_mul' := fun g h => cancel_left₂ hA
        (by rw [k1, ← Matrix.mul_assoc, k1, Matrix.mul_assoc, k1, ← Matrix.mul_assoc, map_mul, Units.val_mul])
        (by rw [k2, ← Matrix.mul_assoc, k2, Matrix.mul_assoc, k2, ← Matrix.mul_assoc, map_mul, Units.val_mul]) }
  refine ⟨f.toHomUnits, fun g => ?_, fun g => ?_⟩
  · rw [MonoidHom.coe_toHomUnits]
    exact k1 g
  · rw [MonoidHom.coe_toHomUnits]
    exact k2 g

theorem rank_map {O F : Type} [CommRing O] [Field F] (f : O →+* F) {a b : ℕ} (A : Matrix (Fin a) (Fin b) O)
    (B : Matrix (Fin b) (Fin a) O) (h : A * B = 1) : (A.map f).rank = a ∧ (B.map f).rank = a :=
  rank_of_mul_eq_one _ _ (by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)])

theorem fibre_line : ∀ {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) (Ac As : Matrix (Fin n) (Fin n) O) (ρc ρs : Γ →* GL (Fin n) O) (x : Fin n → O), Function.Injective Ac.mulVec → Function.Injective As.mulVec → Tw ρc r Ac → Tw ρs r As → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (∀ g, ∃ u, Ac *ᵥ u = (r g : Matrix (Fin n) (Fin n) O) *ᵥ x - fun a => (χ g : O) * x a) → ∃ (r2 : Γ →* GL (Fin (n + 1)) O) (B B' : Matrix (Fin n) (Fin (n + 1)) O) (C : Matrix (Fin 1) (Fin (n + 1)) O) (E : Matrix (Fin (n + 1)) (Fin n) O), Tw r2 r B ∧ Tw r2 ρs B' ∧ Tw r2 (GlobalTheory.TripleGal.rk1 χ) C ∧ Tw ρc r2 E ∧ B * E = Ac ∧ C * E = 0 ∧ B = As * B' ∧ (E.map (residue O)).rank = n ∧ (C.map (residue O)).rank = 1 ∧ (B'.map (residue O)).rank = n ∧ ∀ v, B *ᵥ v = 0 → C *ᵥ v = 0 → v = 0 := by
  intro Γ O _ _ _ _ n r χ Ac As ρc ρs x hAc hAs htc hts h1 h2 h3 h4
  let B : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (x i) (fun j => Ac i j) j
  let Cm : Matrix (Fin 1) (Fin (n + 1)) O := Matrix.of fun _ j => Fin.lastCases (1 : O) (fun _ => 0) j
  let E : Matrix (Fin (n + 1)) (Fin n) O := Matrix.of fun i j => if i = j.castSucc then 1 else 0
  let P : Matrix (Fin n) (Fin (n + 1)) O := Matrix.of fun i j => Fin.lastCases (0 : O) (fun j => if i = j then 1 else 0) j
  let e : Matrix (Fin (n + 1)) (Fin 1) O := Matrix.of fun _ _ => 1
  have hB : ∀ v, B *ᵥ v = Ac *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • x := fun v => by
    funext i
    simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  have hC : ∀ v, Cm *ᵥ v = fun _ => v (Fin.last n) := fun v => by
    funext i
    simp [Cm, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have hBs : ∀ (u : Fin n → O) (c : O), B *ᵥ (Fin.snoc u c : Fin (n + 1) → O) = Ac *ᵥ u + c • x := fun u c => by
    rw [hB]
    simp
  have hBE : B * E = Ac := by
    ext i k
    simp [B, E, Matrix.mul_apply]
  have hCE : Cm * E = 0 := by
    ext i k
    simp [Cm, E, Matrix.mul_apply]
  have hPE : P * E = 1 := by
    ext i k
    simp [P, E, Matrix.mul_apply, Matrix.one_apply]
  have hCe : Cm * e = 1 := by
    ext i k
    rw [Subsingleton.elim i k]
    simp [Cm, e, Matrix.mul_apply, Fin.sum_univ_castSucc]
  have hinj : ∀ v, B *ᵥ v = 0 → Cm *ᵥ v = 0 → v = 0 := fun v hb hc => by
    have hl : v (Fin.last n) = 0 := by
      rw [hC] at hc
      exact congrFun hc 0
    rw [hB, hl, zero_smul, add_zero] at hb
    have h0 : (fun j : Fin n => v j.castSucc) = 0 := hAc (by rw [hb, Matrix.mulVec_zero])
    funext j
    refine Fin.lastCases hl (fun j => congrFun h0 j) j
  have hr : ∀ g, (GlobalTheory.TripleGal.rk1 χ g : Matrix (Fin 1) (Fin 1) O) = Matrix.scalar (Fin 1) (χ g : O) := fun _ => rfl
  obtain ⟨r2, hr2B, hr2C⟩ := mkRep B Cm r (GlobalTheory.TripleGal.rk1 χ) hinj (fun g v => by
    obtain ⟨u, hu⟩ := h4 g
    have hu' : (r g : Matrix (Fin n) (Fin n) O) *ᵥ x = Ac *ᵥ u + (χ g : O) • x := by
      rw [hu]
      exact (sub_add_cancel _ _).symm
    refine ⟨Fin.snoc ((ρc g : Matrix (Fin n) (Fin n) O) *ᵥ (fun j => v j.castSucc) + v (Fin.last n) • u)
      ((χ g : O) * v (Fin.last n)), ?_, ?_⟩
    · rw [hBs, hB, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, htc g,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hu', smul_add, smul_smul, mul_comm, add_assoc]
    · rw [hC, hC, hr]
      funext i
      simp [Matrix.mulVec_diagonal])
  obtain ⟨B', hB'⟩ := solve As B (fun v => by
    obtain ⟨w0, hw0⟩ := h2
    obtain ⟨w1, hw1⟩ := h3 (fun j => v j.castSucc)
    exact ⟨w1 + v (Fin.last n) • w0, by rw [hB, Matrix.mulVec_add, Matrix.mulVec_smul, hw0, hw1]⟩)
  obtain ⟨S, hS⟩ := solve B' (1 : Matrix (Fin n) (Fin n) O) (fun v => by
    obtain ⟨u, c, huc⟩ := h1 v
    refine ⟨Fin.snoc u c, hAs ?_⟩
    rw [Matrix.one_mulVec, Matrix.mulVec_mulVec, ← hB', hBs, huc]
    rfl)
  refine ⟨r2, B, B', Cm, E, hr2B, fun g => cancel_left hAs ?_, hr2C, fun g => cancel_left₂ hinj ?_ ?_, hBE, hCE, hB',
    (rank_map _ P E hPE).2, (rank_map _ Cm e hCe).1, (rank_map _ B' S hS.symm).1, hinj⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hB', hr2B g, hts g, Matrix.mul_assoc, ← hB']
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBE, hr2B g, Matrix.mul_assoc, hBE, htc g]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCE, hr2C g, Matrix.mul_assoc, hCE, Matrix.zero_mul, Matrix.mul_zero]

end GlobalTheory.FibreLine
