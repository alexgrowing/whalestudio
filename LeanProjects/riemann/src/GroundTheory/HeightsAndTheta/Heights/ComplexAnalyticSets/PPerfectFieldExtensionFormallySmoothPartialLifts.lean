import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPerfectFieldExtensionFormallySmoothFrobeniusLift
set_option maxSynthPendingDepth 1

open Polynomial IntermediateField

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]

def IsGoodPartialLift (p : ℕ) (N : Ideal B) (u : K →ₐ[F] B ⧸ N) (ψ : K →+* B)
    (σ : Σ L : IntermediateField F K, L →ₐ[F] B) : Prop :=
  (∀ z : K, ∃ h : z ^ p ∈ σ.1, σ.2 ⟨z ^ p, h⟩ = ψ z) ∧ ∀ y : σ.1, Ideal.Quotient.mk N (σ.2 y) = u y

def PartialLiftLE (σ τ : Σ L : IntermediateField F K, L →ₐ[F] B) : Prop :=
  ∃ h : σ.1 ≤ τ.1, ∀ y : σ.1, τ.2 (IntermediateField.inclusion h y) = σ.2 y

theorem PartialLiftLE.trans {a b d : Σ L : IntermediateField F K, L →ₐ[F] B} (h₁ : PartialLiftLE a b)
    (h₂ : PartialLiftLE b d) : PartialLiftLE a d := by
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  exact ⟨h₁.trans h₂, fun y => by rw [← h₁' y, ← h₂' (IntermediateField.inclusion h₁ y)]; rfl⟩

theorem exists_isGoodPartialLift_upperBound {p : ℕ} {N : Ideal B} {u : K →ₐ[F] B ⧸ N} {ψ : K →+* B}
    (c : Set {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ})
    (hc : IsChain (fun a b => PartialLiftLE a.1 b.1) c) (hne : c.Nonempty) :
    ∃ ub : {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ},
      ∀ a ∈ c, PartialLiftLE a.1 ub.1 := by
  obtain ⟨i₀, hi₀⟩ := hne
  have : Nonempty c := ⟨⟨i₀, hi₀⟩⟩
  let t : c → IntermediateField F K := fun i => i.1.1.1
  have dir : Directed (· ≤ ·) t := by
    intro i j
    by_cases hij : i = j
    · exact ⟨i, le_rfl, hij ▸ le_rfl⟩
    rcases hc i.2 j.2 (fun h => hij (Subtype.ext h)) with h | h
    · exact ⟨j, h.1, le_rfl⟩
    · exact ⟨i, le_rfl, h.1⟩
  have dir' : Directed (· ≤ ·) (fun i => (t i).toSubalgebra) := dir.mono_comp _ (fun _ _ h => h)
  let f : ∀ i, (t i).toSubalgebra →ₐ[F] B := fun i => i.1.1.2
  have hf : ∀ (i j : c) (h : (t i).toSubalgebra ≤ (t j).toSubalgebra),
      f i = (f j).comp (Subalgebra.inclusion h) := by
    intro i j h
    ext y
    by_cases hij : i = j
    · subst hij; rfl
    rcases hc i.2 j.2 (fun h => hij (Subtype.ext h)) with ⟨h', h''⟩ | ⟨h', h''⟩
    · exact (h'' y).symm
    · exact h'' (Subalgebra.inclusion h y)
  have hT : (iSup t).toSubalgebra ≤ ⨆ i, (t i).toSubalgebra :=
    (IntermediateField.toSubalgebra_iSup_of_directed dir).le
  let φ : ↥(iSup t) →ₐ[F] B := Subalgebra.iSupLift _ dir' f hf _ hT
  have hφ : ∀ (i : c) (y : K) (hy : y ∈ t i), φ ⟨y, (le_iSup t i) hy⟩ = i.1.1.2 ⟨y, hy⟩ :=
    fun i y hy => Subalgebra.iSupLift_mk _ (i := i) ⟨y, hy⟩ _
  refine ⟨⟨⟨iSup t, φ⟩, ⟨fun z => ?_, fun y => ?_⟩⟩,
    fun a ha => ⟨le_iSup t ⟨a, ha⟩, fun y => hφ ⟨a, ha⟩ y.1 y.2⟩⟩
  · obtain ⟨h, h'⟩ := (i₀.2).1 z
    exact ⟨le_iSup t ⟨i₀, hi₀⟩ h, (hφ ⟨i₀, hi₀⟩ _ h).trans h'⟩
  · have hy : (y : K) ∈ ⋃ i, (t i : Set K) := by
      rw [← IntermediateField.coe_iSup_of_directed dir]; exact y.2
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    rw [show y = ⟨y, (le_iSup t i) hi⟩ from rfl, hφ i y hi]
    exact i.1.2.2 ⟨y, hi⟩

theorem exists_isGoodPartialLift_frobenius [PerfectField F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]
    {N : Ideal B} (hpB : (p : B) = 0) (hN : N ^ 2 = ⊥) (u : K →ₐ[F] B ⧸ N) :
    ∃ σ, IsGoodPartialLift p N u ((sqZeroFrobeniusLift N hp.out hpB hN).comp u.toRingHom) σ := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap F K).injective p
  set P := sqZeroFrobeniusLift N hp.out hpB hN
  set ψ : K →+* B := P.comp u.toRingHom
  let L₀ : IntermediateField F K :=
    { (frobenius K p).fieldRange with
      algebraMap_mem' := fun a => ⟨algebraMap F K ((frobeniusEquiv F p).symm a), by
        rw [frobenius_def, ← map_pow]; congr 1; exact (frobeniusEquiv F p).apply_symm_apply a⟩ }
  let e := (frobenius K p).rangeRestrictFieldEquiv
  have he : ∀ (y : (frobenius K p).fieldRange) (z : K), (y : K) = z ^ p → e.symm y = z :=
    fun y z h => e.symm_apply_eq.mpr (Subtype.ext (h.trans (frobenius_def p z).symm))
  let φ₀ : L₀ →ₐ[F] B :=
    { ψ.comp (e.symm.toRingHom : (frobenius K p).fieldRange →+* K) with
      commutes' := fun a => by
        obtain ⟨b, rfl⟩ := (frobeniusEquiv F p).surjective a
        have hb : algebraMap F L₀ (frobeniusEquiv F p b) =
            ⟨algebraMap F K b ^ p, ⟨algebraMap F K b, by rw [frobenius_def]⟩⟩ := by
          apply Subtype.ext
          show algebraMap F K (frobeniusEquiv F p b) = _
          rw [frobeniusEquiv_def, map_pow]
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_coe]
        rw [hb]
        show ψ (e.symm _) = _
        rw [he _ (algebraMap F K b) rfl]
        simp [ψ, P, ← Ideal.Quotient.mk_algebraMap, sqZeroFrobeniusLift_mk, frobenius_def] }
  refine ⟨⟨L₀, φ₀⟩, fun z => ⟨⟨z, by rw [frobenius_def]⟩, congrArg ψ (he _ z rfl)⟩, fun y => ?_⟩
  obtain ⟨z, hz⟩ := y.2
  have hy : y = ⟨z ^ p, ⟨z, by rw [frobenius_def]⟩⟩ := Subtype.ext (hz.symm.trans (frobenius_def p z))
  subst hy
  show Ideal.Quotient.mk N (ψ (e.symm _)) = _
  rw [he _ z rfl]
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u z)
  simp [ψ, P, ← hc, sqZeroFrobeniusLift_mk]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
