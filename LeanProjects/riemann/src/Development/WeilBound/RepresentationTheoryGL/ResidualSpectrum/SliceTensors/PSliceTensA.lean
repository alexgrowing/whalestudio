import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDetermining

noncomputable section

open NumberField MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Affgl

namespace PositivityTheory.Rg.Rs.SliceTensor

theorem interp {K : Type} (A : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ A] :
    ∃ (S : Finset K) (a : S → A), ∀ c ∈ A, c = ∑ κ : S, c κ.1 • (a κ : K → ℂ) := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.CompanionTheory.CTFin.UniSol.exists_finset_separating A
  let ev : A →ₗ[ℂ] (S → ℂ) := LinearMap.pi fun κ => (LinearMap.proj κ.1 : (K → ℂ) →ₗ[ℂ] ℂ) ∘ₗ A.subtype
  have hinj : LinearMap.ker ev = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun c hc => Subtype.ext (hS c.1 c.2 fun κ hκ => ?_)
    exact congrFun hc ⟨κ, hκ⟩
  obtain ⟨P, hP⟩ := ev.exists_leftInverse_of_injective hinj
  refine ⟨S, fun κ => P (Pi.single κ 1), fun c hc => ?_⟩
  have h1 : P (ev ⟨c, hc⟩) = ⟨c, hc⟩ := LinearMap.congr_fun hP _
  have h2 : ev ⟨c, hc⟩ = ∑ κ : S, c κ.1 • (Pi.single κ 1 : S → ℂ) := by
    funext κ'
    simp [Finset.sum_apply, Pi.single_apply, ev]
  have h3 := congrArg Subtype.val h1
  rw [h2, map_sum] at h3
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul] at h3
  exact h3.symm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem slice_mem {r s : ℕ} {L : Subgroup (GL (Fin (r + s)) (Af E))} {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) {J : Set (Module.End ℂ (Sm E (r + s)))} (hJ : J ⊆ Zalg E (r + s))
    {J₁ : Set (Module.End ℂ (Sm E r))}
    (H3 : ∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
      (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0)
    (F : Sm E (r + s)) (hN : ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g)
    (hLv : ∀ k ∈ L, finRep E (r + s) k F = F)
    (hC : ∀ g : GA E (r + s), (fun k : Kinf E (r + s) => (cptRep E (r + s) k F).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ)
    (hZ : ∀ z ∈ J, z F = 0) (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)) (m₂ : GA E s) (G : Sm E r)
    (hA : IsAutForm G)
    (hGv : ∀ m₁, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ))) :
    G ∈ genSpace (Slice1.levelOne s L t) (ρ.comp (Slice1.levK E r s)) J₁ := by
  let h : GA E (r + s) := lev (Ad E) r s (1, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)
  let F' := rt E (r + s) h F
  have hcoef : ∀ g : GA E r, (fun k : Kinf E r => (cptRep E r k G).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (Slice1.levK E r s)) := by
    intro g
    have key := Slice1.coeff_comp ρ (Slice1.levK E r s) κ (hC (lev (Ad E) r s (g, m₂) * finGL E (r + s) t))
    convert key using 1
    funext k
    change G.1 (g * infGL E r (Unitary.toUnits k)) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
      infGL E (r + s) (Unitary.toUnits (Slice1.levK E r s k * κ)))
    rw [hGv, Slice1.lev_infGL_right, ← Slice1.toUnits_levK (s := s),
      ← map_mul (Unitary.toUnits : _ →* (Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))ˣ)]
  have hle : (Slice1.levelOne s L t : Set (GL (Fin r) (Af E))) ⊆ {k | finRep E r k G = G} := by
    intro k hk
    refine Subtype.ext (funext fun m => ?_)
    change G.1 (m * finGL E r k) = G.1 m
    rw [hGv, hGv]
    have hk' : F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ) *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t)) =
        F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) :=
      congrFun (congrArg Subtype.val (hLv _ (Slice1.mem_levelOne.1 hk))) _
    rw [← hk', Slice1.lev_finGL_right]
  have hkill : ∀ z ∈ J₁, z G = 0 := by
    refine H3 F' (fun x g => ?_) (fun z hz => ?_) G (fun m => ?_)
    · change F.1 (unip x * g * h) = F.1 (g * h)
      rw [mul_assoc, hN]
    · change z (rt E (r + s) h F) = 0
      rw [← Module.End.mul_apply, (Slice1.commute_rt_of_mem_Zalg (hJ hz) h).eq, Module.End.mul_apply, hZ z hz, map_zero]
    · rw [hGv]
      change _ = F.1 (lev (Ad E) r s (m, 1) * h)
      have e : (m, m₂) = ((m, 1) * (1, m₂) : GA E r × GA E s) := by simp
      rw [e, map_mul]
      simp only [h, mul_assoc]
  exact ⟨hA, fun k hk => hle hk, hcoef, hkill⟩

end PositivityTheory.Rg.Rs.SliceTensor

end
