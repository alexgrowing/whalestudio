import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL

namespace GlobalTheory.DiscSpec

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N a c d : ℕ} {n : Fin c → ℕ}

def finVec {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) : Submodule ℂ V where
  carrier := {v | FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k v))}
  add_mem' := fun {v w} (hv : FiniteDimensional _ _) (hw : FiniteDimensional _ _) =>
    Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k => ρ k v) ⊔ Submodule.span ℂ (Set.range fun k => ρ k w))
      (Submodule.span_le.2 (by
        rintro _ ⟨k, rfl⟩
        simp only [map_add]
        exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)))
  zero_mem' := FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton 0).subset (by
    rintro _ ⟨k, rfl⟩
    simp))
  smul_mem' := fun z v (hv : FiniteDimensional _ _) =>
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k => ρ k v))
      (Submodule.span_le.2 (by
        rintro _ ⟨k, rfl⟩
        simp only [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)))

def tensorForms (π : ∀ i, CuspSub E (n i)) : Submodule ℂ ((∀ i, GA E (n i)) → ℂ) :=
  Submodule.span ℂ {F | ∃ φ : ∀ i, (π i).V, F = fun m => ∏ i, (φ i).1.1 (m i)}

def indForms (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) : Submodule ℂ (Sm E N) where
  carrier := {φ | (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, φ.1 (u * g) = φ.1 g) ∧
    φ ∈ GlobalTheory.PRep.smoothPart (finRep E N) ∧ φ ∈ finVec (cptRep E N) ∧
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)),
      (fun m => φ.1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorForms π}
  add_mem' := fun h1 h2 => ⟨fun u hu g => congrArg₂ (· + ·) (h1.1 u hu g) (h2.1 u hu g),
    add_mem h1.2.1 h2.2.1, add_mem h1.2.2.1 h2.2.2.1, fun k g => add_mem (h1.2.2.2 k g) (h2.2.2.2 k g)⟩
  zero_mem' := ⟨fun _ _ _ => rfl, zero_mem _, zero_mem _, fun _ _ => zero_mem _⟩
  smul_mem' z _ h1 := ⟨fun u hu g => congrArg (z • ·) (h1.1 u hu g), Submodule.smul_mem _ z h1.2.1,
    Submodule.smul_mem _ z h1.2.2.1, fun k g => Submodule.smul_mem _ z (h1.2.2.2 k g)⟩

def IsQuotOf (V I : Submodule ℂ (Sm E N)) : Prop :=
  ∃ f : Sm E N →ₗ[ℂ] Sm E N, I.map f = V ∧ ∀ o, ∀ φ ∈ I, f (act o φ) = act o (f φ)

def IsIsoGL (V V' : Submodule ℂ (Sm E N)) : Prop :=
  ∃ T : V ≃ₗ[ℂ] V', ∀ (o : Op E N) (φ ψ : V), ψ.1 = act o φ.1 → (T ψ).1 = act o (T φ).1

def spehExp (d : ℕ) (i : Fin d) : ℝ := ((d : ℝ) - 1) / 2 - (i : ℕ)

def IsSpehOf (V : Submodule ℂ (Sm E N)) (π : CuspSub E a) (d : ℕ) : Prop :=
  ∃ (h : ∑ _ : Fin d, a = N) (ν : Fin d → HChar E), (∀ i, (ν i).IsAbsPow (spehExp d i + a * spehExp d i)) ∧
    IsQuotOf V (indForms h fun i => π.twist (ν i))

def IsNormalised (π : CuspSub E a) : Prop := ∀ φ ∈ π.V, ∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

structure HasSpehComp (V : Submodule ℂ (Sm E N)) (π : CuspSub E a) (d : ℕ) : Prop where
  exLoc : ∀ w, ∃ σ σ', π.IsLocComp w σ ∧ IsLocCompGL V w σ'
  loc : ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
    GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ
  inf : ∀ τ, ∃ m, π.HasInfChar τ m ∧ HasInfCharGL V τ (GlobalTheory.SphGal.spehInf d m)

theorem IsSpehOf.mul_eq {V : Submodule ℂ (Sm E N)} {π : CuspSub E a} (h : IsSpehOf V π d) : d * a = N := by
  obtain ⟨h, -⟩ := h
  simpa using h

theorem mul_spehExp (a d : ℕ) (i : Fin d) : a * spehExp d i = (modExp (fun _ : Fin d => Fin a) i : ℝ) / 2 := by
  have h1 : Finset.univ.filter (fun b => i < b) = Finset.Ioi i := by ext; simp
  have h2 : Finset.univ.filter (fun b => b < i) = Finset.Iio i := by ext; simp
  have h3 : ((d - 1 - i : ℕ) : ℝ) = d - 1 - (i : ℕ) := by
    have := i.2
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  simp only [modExp, h1, h2, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, nsmul_eq_mul, Fintype.card_fin, spehExp]
  push_cast
  rw [h3]
  ring

theorem fin_mem_indForms {h : ∑ i, n i = N} {π : ∀ i, CuspSub E (n i)} {φ : Sm E N} (hφ : φ ∈ indForms h π)
    (x : GL (Fin N) (Af E)) : act (.fin x) φ ∈ indForms h π := by
  refine ⟨fun u hu g => ?_, GlobalTheory.PRep.smoothPart_stable _ x φ hφ.2.1, ?_, fun k g => ?_⟩
  · change φ.1 (u * g * _) = φ.1 (g * _)
    rw [mul_assoc, hφ.1 u hu]
  · have : FiniteDimensional _ _ := hφ.2.2.1
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E N k φ)).map
      (finRep E N x)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, Subtype.ext (funext fun g => ?_)⟩
    change φ.1 (g * finGL E N x * infGL E N _) = φ.1 (g * infGL E N _ * finGL E N x)
    rw [mul_assoc, mul_assoc, infGL_comm]
  · have := hφ.2.2.2 k (g * x)
    rw [map_mul] at this
    convert this using 2 with m
    change φ.1 (_ * finGL E N x) = _
    simp only [mul_assoc]

theorem indForms_one (h : ∑ _ : Fin 1, a = a) (π : CuspSub E a) : indForms h (fun _ => π) = π.V := by
  have he : ∀ b i, stdBlocks (fun _ : Fin 1 => a) h ⟨b, i⟩ = i := fun b i => Fin.ext (by
    rw [stdBlocks_val, Subsingleton.elim b 0]; simp)
  have hl : ∀ m, leviEmb (Ad E) (stdBlocks (fun _ : Fin 1 => a) h) m = m 0 := fun m => by
    ext i j
    have := leviEmb_apply_same (Ad E) (stdBlocks (fun _ : Fin 1 => a) h) m 0 i j
    rwa [he, he] at this
  refine le_antisymm (fun φ hφ => ?_) fun φ hφ => ⟨fun u hu g => ?_, (π.cusp φ hφ).1.level, (π.cusp φ hφ).1.kfin,
    fun k g => Submodule.subset_span ⟨fun _ => ⟨_, π.stable (.cpt k) _ (π.stable (.fin g) φ hφ)⟩, funext fun m => ?_⟩⟩
  · have key : ∀ F ∈ tensorForms fun _ : Fin 1 => π, ∃ ψ ∈ π.V, ∀ g, F (fun _ => g) = ψ.1 g := fun F hF => by
      induction hF using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨ψ, rfl⟩ := hF
        exact ⟨ψ 0, (ψ 0).2, fun g => by simp⟩
      | zero => exact ⟨0, zero_mem _, fun _ => rfl⟩
      | add F G _ _ hF hG =>
        obtain ⟨x, hx, e⟩ := hF
        obtain ⟨y, hy, e'⟩ := hG
        exact ⟨x + y, add_mem hx hy, fun g => congrArg₂ (· + ·) (e g) (e' g)⟩
      | smul z F _ hF =>
        obtain ⟨x, hx, e⟩ := hF
        exact ⟨z • x, Submodule.smul_mem _ _ hx, fun g => congrArg (z • ·) (e g)⟩
    obtain ⟨ψ, h1, h2⟩ := key _ (hφ.2.2.2 1 1)
    rwa [show φ = ψ from Subtype.ext (funext fun g => by simpa [hl] using h2 g)]
  · rw [show u = 1 from Units.ext (Matrix.ext fun i j => by
      have := (mem_unipRad.1 hu).2 0 i j
      rwa [he, he] at this), one_mul]
  · rw [hl, Fin.prod_univ_one, ← mul_assoc]
    rfl

theorem isSpehOf_one (π : CuspSub E a) : IsSpehOf π.V π 1 := by
  refine ⟨by simp, fun _ => 1, fun i => ?_, LinearMap.id, ?_, fun _ _ _ => rfl⟩
  · have : spehExp 1 i + a * spehExp 1 i = 0 := by simp [spehExp]
    rw [this]
    exact ⟨fun _ _ _ => rfl, fun _ => by simp [HChar.val, HChar.locK], fun _ => by simp [HChar.inf]⟩
  · simp only [Submodule.map_id, CuspSub.twist_one]
    exact indForms_one _ π

theorem isNormalised_triv (ha : a ≤ 1) : IsNormalised (CuspSub.triv E ha) := fun φ hφ _ _ => by
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  rfl

theorem isNormalised_of_isDiscrete {π : CuspSub E a} (h : IsDiscrete π.V) : IsNormalised π :=
  fun φ hφ => (h.sqInt φ hφ).1

theorem isIsoGL_iff (π π' : CuspSub E a) : IsIsoGL π.V π'.V ↔ π.Iso π' := by
  refine exists_congr fun T => ⟨fun h o φ => Subtype.ext (h o φ _ rfl), fun h o φ ψ e => ?_⟩
  rw [show ψ = π.op o φ from Subtype.ext e, h]
  rfl

end GlobalTheory.DiscSpec

namespace GlobalTheory.Published

open GlobalTheory.DiscSpec

def DiscreteSpectrumGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E N), IsDiscrete V ∧ IsSpehOf V π d) ∧
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    (∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → IsIsoGL V V' → V = V') ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → HasSpehComp V π d

theorem DiscreteSpectrumGL.iso (H : DiscreteSpectrumGL) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    {N a d : ℕ} (hN : 1 ≤ N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {π π' : CuspSub E a} (h : IsNormalised π)
    (h' : IsNormalised π') (e : IsSpehOf V π d) (e' : IsSpehOf V π' d) : π.Iso π' :=
  Quotient.exact (eq_of_heq (Sigma.mk.inj ((H E N hN).2.2.1 V hV a d a d π π' h h' e e').2).2)

end GlobalTheory.Published

end
