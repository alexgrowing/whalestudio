import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.LFun.ConjParam

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem conj_mem_hecke {h : G → ℂ} (hh : h ∈ Hecke ℂ K) : (fun g => starRingEnd ℂ (h g)) ∈ Hecke ℂ K := by
  obtain ⟨h1, S, hS⟩ := hh
  exact ⟨fun a b g => congrArg _ (h1 a b g), S, fun g hg => hS g fun h0 => hg (by simp [h0])⟩

theorem eigen_conj (hK : IsCommensurated K) (hinv : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, g⁻¹ = k₁ * g * k₂)
    {ρ : Representation ℂ G V} (hρ : GlobalTheory.LGrp.IsUnitarisable ρ) {x : V} (h0 : x ≠ 0) (hx : x ∈ fixed ρ K)
    {h : G → ℂ} (hh : h ∈ Hecke ℂ K) {a b : ℂ} (ha : heckeVec ρ K h x = a • x)
    (hb : heckeVec ρ K (fun g => starRingEnd ℂ (h g)) x = b • x) : starRingEnd ℂ b = a := by
  obtain ⟨B, hB, hpos, hinvB⟩ := hρ
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have hreal : ∀ g, starRingEnd ℂ (B (ρ g x) x) = B (ρ g x) x := fun g => by
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hinv g
    have e1 : B x (ρ g x) = B (ρ g⁻¹ x) x := by
      rw [← hinvB g (ρ g⁻¹ x) x, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e2 : B (ρ k₁ (ρ g x)) x = B (ρ g x) x := by
      rw [← hinvB k₁ (ρ g x) x, hfix k₁ hk₁]
    rw [← hB, e1, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix k₂ hk₂, e2]
  have key : ∀ f ∈ Hecke ℂ K, B (heckeVec ρ K f x) x = ∑ᶠ c : G ⧸ K, f c.out * B (ρ c.out x) x := fun f hf => by
    refine ((B.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_)
    simp
  have hxx : starRingEnd ℂ (B x x) = B x x := (hB x x).symm
  have hne : B x x ≠ 0 := fun e => by simpa [e] using hpos x h0
  have e1 := key h hh
  have e2 := congrArg (starRingEnd ℂ) (key _ (conj_mem_hecke hh))
  rw [ha] at e1
  rw [hb, show ⇑(starRingEnd ℂ) = (starAddEquiv : ℂ ≃+ ℂ) from rfl, AddEquiv.map_finsum] at e2
  apply mul_right_cancel₀ hne
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at e1 e2
  rw [e1]
  refine Eq.trans ?_ (e2.trans (finsum_congr fun c => ?_))
  · change _ = starRingEnd ℂ _
    rw [map_mul, hxx]
  · change starRingEnd ℂ _ = _
    rw [map_mul, hreal]
    exact congrArg (· * _) (Complex.conj_conj _)

end General

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem conj_satU {m : ℕ} (ϖ : L) (q : ℕ) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    starRingEnd ℂ (SatU ϖ q (fun g => starRingEnd ℂ (h g)) α) = SatU ϖ q h fun i => starRingEnd ℂ (α i) := by
  have hs : ∀ {ι : Type} (f : ι → ℂ), starRingEnd ℂ (∑ᶠ i, f i) = ∑ᶠ i, starRingEnd ℂ (f i) := fun f =>
    AddEquiv.map_finsum (starAddEquiv : ℂ ≃+ ℂ) f
  unfold SatU
  rw [hs]
  refine finsum_congr fun a => ?_
  rw [map_mul, hs, map_prod]
  congr 1
  · simp
  · refine finsum_congr fun c => ?_
    split_ifs <;> simp

theorem inv_mem {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ n) :
    ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g⁻¹ = k₁ * g * k₂ := by
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ (g := (g : GL (Fin n) L)) (by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

theorem satU_star_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.IsUnitarisable ρ → IsSatVecU ϖ q ρ x α → ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => ((star (α i) : ℂˣ) : ℂ)) = SatU ϖ q h (fun i => (α i : ℂ)) := by
  intro L _ _ _ ϖ σ q n hU V _ _ ρ x α hρ hx h hh
  exact (conj_satU ϖ q h fun i => (α i : ℂ)).symm.trans
    (eigen_conj (P.isCommensurated_integral_unitary_of_unramified hU n) (inv_mem hU) hρ hx.1 hx.2.1 hh (hx.2.2 h hh) (hx.2.2 _ (conj_mem_hecke hh)))

end GlobalTheory.LFun.ConjParam

end
