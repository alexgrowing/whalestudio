import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.coc_fin :
    ∀ (G R : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommRing R] [Finite R] (n : ℕ) (ρ : G → Matrix (Fin n) (Fin n) R), TopFG G → ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g * ρ h) → IsLocallyConstant ρ → {z : G → Matrix (Fin n) (Fin n) R | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹}.Finite := by
  intro G R _ _ _ _ _ n ρ hfg h1 hmul hρ
  obtain ⟨s, hs, hden⟩ := hfg
  haveI : Finite s := hs.to_subtype
  have hinv : ∀ g, ρ g⁻¹ * ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, h1]
  have hinv' : ∀ g, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, h1]
  have hz1 : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → z 1 = 0 := by
    intro z hz
    have := hz 1 1
    simpa [h1] using this
  have hzinv : ∀ z : G → Matrix (Fin n) (Fin n) R, (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) →
      ∀ g, z g⁻¹ = ρ g⁻¹ * (-z g) * ρ g := by
    intro z hz g
    have e := hz g g⁻¹
    rw [mul_inv_cancel, hz1 z hz] at e
    have e2 : ρ g * z g⁻¹ * ρ g⁻¹ = -z g := eq_neg_of_add_eq_zero_right e.symm
    calc z g⁻¹ = ρ g⁻¹ * (ρ g * z g⁻¹ * ρ g⁻¹) * ρ g := by
          simp only [Matrix.mul_assoc]
          rw [hinv, Matrix.mul_one, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
      _ = ρ g⁻¹ * (-z g) * ρ g := by rw [e2]
  apply Set.Finite.of_finite_image (f := fun z : G → Matrix (Fin n) (Fin n) R => fun x : s => z x)
    (Set.toFinite _)
  rintro z ⟨hzl, hz⟩ z' ⟨hzl', hz'⟩ he
  let H : Subgroup G :=
    { carrier := {g | z g = z' g}
      mul_mem' := fun {a b} ha hb => by
        change z (a * b) = z' (a * b)
        change z a = z' a at ha
        change z b = z' b at hb
        rw [hz, hz', ha, hb]
      one_mem' := by
        change z 1 = z' 1
        rw [hz1 z hz, hz1 z' hz']
      inv_mem' := fun {a} ha => by
        change z a = z' a at ha
        change z a⁻¹ = z' a⁻¹
        rw [hzinv z hz, hzinv z' hz', ha] }
  have hsH : Subgroup.closure s ≤ H := (Subgroup.closure_le H).2 fun x hx => congrFun he ⟨x, hx⟩
  have hcl : IsClosed (H : Set G) := by
    have hd := hzl.comp₂ hzl' (fun a b => a - b)
    have hc := hd.isClosed_fiber 0
    convert hc using 1
    ext g
    exact sub_eq_zero.symm
  have hU : (H : Set G) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hden.closure_eq]
    exact closure_minimal (fun x hx => hsH hx) hcl
  funext g
  have hg : g ∈ (H : Set G) := hU ▸ Set.mem_univ g
  exact hg
