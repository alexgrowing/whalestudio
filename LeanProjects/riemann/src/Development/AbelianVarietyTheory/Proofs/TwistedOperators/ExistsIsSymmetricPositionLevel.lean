import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.SymLevelExists

section Plain
variable {F : Type} [Field F] {κ l : ℕ}

def symGroup (F : Type) [Field F] (κ l p : ℕ) : Subgroup (GL (Fin κ ⊕ Fin l) F) where
  carrier := {x | ∃ u ∈ N F (Fin κ) l p, ∃ γ : GL (Fin κ) F, IsUpperUnip Fin.val γ.val ∧ x = u * embX l γ}
  one_mem' := ⟨1, one_mem _, 1, fun _ _ _ => rfl, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, γ, hγ, rfl⟩ ⟨u', hu', γ', hγ', rfl⟩
    refine ⟨_, mul_mem hu (Radical.conj_mem γ hu'), γ * γ',
      Radical.Uni.mul (b := Fin.val) hγ hγ', ?_⟩
    rw [map_mul]; group
  inv_mem' := by
    rintro _ ⟨u, hu, γ, hγ, rfl⟩
    refine ⟨_, Radical.conj_mem γ⁻¹ (inv_mem hu), γ⁻¹, Radical.Uni.inv (b := Fin.val) hγ, ?_⟩
    rw [map_inv]; group

theorem simpleSum_mul_embX (u : GL (Fin κ ⊕ Fin l) F) (γ : GL (Fin κ) F) :
    simpleSum (u * embX l γ) = simpleSum u := by
  have hv : ∀ i j, (u * embX l γ).val (Sum.inr i) (Sum.inr j) = u.val (Sum.inr i) (Sum.inr j) := by
    intro i j
    rw [Units.val_mul, Radical.embX_val, ← fromBlocks_toBlocks u.val]
    simp [fromBlocks_multiply]
  simp only [simpleSum, hv]

theorem toBlocks₁₁_mul_embX {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
    (u * embX l γ).val.toBlocks₁₁ = γ.val := by
  rw [Units.val_mul, Radical.embX_val]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks u.val]
  simp [fromBlocks_multiply, Radical.toBlocks₁₁_of_mem hu]

theorem superSum_mul {a : Type} [Fintype a] [DecidableEq a] {pos : a → ℕ} {M M' : Matrix a a F}
    (h : IsUpperUnip pos M) (h' : IsUpperUnip pos M') :
    superSum pos (M * M') = superSum pos M + superSum pos M' := by
  simp only [superSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · exact Radical.Uni.mul_apply_succ (b := pos) h h' hij
  · simp

def symSum (x : GL (Fin κ ⊕ Fin l) F) : F := simpleSum x + superSum Fin.val x.val.toBlocks₁₁

theorem symSum_eq {p : ℕ} {u : GL (Fin κ ⊕ Fin l) F} (hu : u ∈ N F (Fin κ) l p) (γ : GL (Fin κ) F) :
    symSum (u * embX l γ) = simpleSum u + superSum Fin.val γ.val := by
  rw [symSum, simpleSum_mul_embX, toBlocks₁₁_mul_embX hu]

theorem symSum_mul {p : ℕ} {x y : GL (Fin κ ⊕ Fin l) F} (hx : x ∈ symGroup F κ l p) (hy : y ∈ symGroup F κ l p) :
    symSum (x * y) = symSum x + symSum y := by
  obtain ⟨u, hu, γ, hγ, rfl⟩ := hx
  obtain ⟨u', hu', γ', hγ', rfl⟩ := hy
  have e : u * embX l γ * (u' * embX l γ') = u * (embX l γ * u' * (embX l γ)⁻¹) * embX l (γ * γ') := by
    rw [map_mul]; group
  rw [e, symSum_eq (mul_mem hu (Radical.conj_mem γ hu')), symSum_eq hu, symSum_eq hu',
    Radical.simpleSum_mul hu (Radical.conj_mem γ hu'), Radical.simpleSum_conj, Units.val_mul, superSum_mul hγ hγ']
  ring

end Plain

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_residue_char {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) :
    ∃ χ : 𝓀[k] → Circle, (∀ y z, χ (y + z) = χ y * χ z) ∧
      ∀ y : 𝒪[k], χ (IsLocalRing.residue 𝒪[k] y) = ψ ((ϖ⁻¹ : kˣ) * (y : k)) := by
  have hs : Function.Surjective (IsLocalRing.residue 𝒪[k]) := IsLocalRing.residue_surjective
  have key : ∀ y z : 𝒪[k], IsLocalRing.residue 𝒪[k] y = IsLocalRing.residue 𝒪[k] z →
      ψ ((ϖ⁻¹ : kˣ) * (y : k)) = ψ ((ϖ⁻¹ : kˣ) * (z : k)) := by
    intro y z h
    have h1 : valuation k ((y : k) - z) < 1 := (residue_eq_iff_lt y z).1 h
    have h2 := (hϖ _).1 h1
    have h3 : ψ ((ϖ⁻¹ : kˣ) * ((y : k) - z)) = 1 := by
      refine hψ.eq_one ?_
      have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
      simp only [cball, Set.mem_setOf_eq, Units.val_one, map_one, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      rwa [inv_mul_le_one₀ h0]
    rw [show ((ϖ⁻¹ : kˣ) : k) * (y : k) = (ϖ⁻¹ : kˣ) * ((y : k) - z) + (ϖ⁻¹ : kˣ) * (z : k) by ring,
      AddChar.map_add_eq_mul, h3, one_mul]
  have h2 : ∀ y : 𝒪[k], ψ ((ϖ⁻¹ : kˣ) * ((Function.surjInv hs (IsLocalRing.residue 𝒪[k] y) : 𝒪[k]) : k)) =
      ψ ((ϖ⁻¹ : kˣ) * (y : k)) := fun y => key _ _ (Function.surjInv_eq hs _)
  refine ⟨fun y => ψ ((ϖ⁻¹ : kˣ) * ((Function.surjInv hs y : 𝒪[k]) : k)), fun y z => ?_, h2⟩
  obtain ⟨y, rfl⟩ := hs y
  obtain ⟨z, rfl⟩ := hs z
  beta_reduce
  rw [← map_add, h2, h2, h2, ← AddChar.map_add_eq_mul, ← mul_add]
  rfl

def symSumInt {κ l : ℕ} (g : GL (Fin κ ⊕ Fin l) 𝒪[k]) : 𝒪[k] :=
  (∑ i : Fin l, ∑ j : Fin l, if j.val = i.val + 1 then g.val (Sum.inr i) (Sum.inr j) else 0) +
    ∑ i : Fin κ, ∑ j : Fin κ, if j.val = i.val + 1 then g.val (Sum.inl i) (Sum.inl j) else 0

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem map_symSumInt {F : Type} [Field F] (f : 𝒪[k] →+* F) {κ l : ℕ} (g : GL (Fin κ ⊕ Fin l) 𝒪[k]) :
    f (symSumInt g) = symSum (Matrix.GeneralLinearGroup.map f g) := by
  simp only [symSumInt, symSum, simpleSum, superSum, map_add, map_sum, apply_ite f, map_zero]
  rfl

end Local

theorem exists_isSymLevel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ ρ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsSymLevel ψ ϖ ρ P := by
  intro k _ _ _ _ ψ hψ ϖ hϖ ρ κ l
  obtain ⟨χ, hadd, hres⟩ := exists_residue_char hψ hϖ
  let χ' : symGroup 𝓀[k] κ l (ρ + 1) →* ℂˣ :=
    MonoidHom.mk' (fun x => Circle.toUnits (χ (symSum (x : GL (Fin κ ⊕ Fin l) 𝓀[k])))) fun x y => by
      rw [Subgroup.coe_mul, symSum_mul x.2 y.2, hadd, map_mul]
  refine ⟨TypeDatum.ofResidue _ χ', fun g => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨g₀, ⟨u, hu, γ, hγ, e⟩, rfl⟩
    exact ⟨u, hu, γ, hγ, g₀, rfl, e⟩
  · rintro ⟨u, hu, γ, hγ, g₀, rfl, e⟩
    exact ⟨g₀, ⟨u, hu, γ, hγ, e⟩, rfl⟩
  · rintro ⟨_, g₀, hg, rfl⟩
    rw [TypeDatum.ofResidue_lam _ χ' g₀ hg]
    change ((χ (symSum (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀)) : Circle) : ℂ) = _
    rw [← map_symSumInt, hres, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← mul_add]
    exact congrArg (fun z : k => ((ψ ((ϖ⁻¹ : kˣ) * z) : Circle) : ℂ)) (map_symSumInt (algebraMap 𝒪[k] k) g₀)

end GlobalTheory.SymLevelExists
