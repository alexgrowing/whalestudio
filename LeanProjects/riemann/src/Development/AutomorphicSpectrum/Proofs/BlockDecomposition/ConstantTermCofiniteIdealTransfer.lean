import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRestrictionSmoothStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingHeightBoundStatement

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1

theorem slice_mem_genSpace : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₁ : Set (Module.End ℂ (Sm E r)), Cofin J₁ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₁ : Subgroup (GL (Fin r) (Af E))) (ρ₁ : Representation ℂ (Kinf E r) W), IsOpen (L₁ : Set (GL (Fin r) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₁ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₂ : GA E s, ∃ G ∈ genSpace L₁ ρ₁ J₁, ∀ m₁ : GA E r, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  intro E _ _ _ r s L hL W _ _ _ ρ hρ J hJ J₁ hJ₁ H3 t κ
  refine ⟨levelOne s L t, ρ.comp (levK E r s), isOpen_levelOne hL t,
    fun ℓ w => (hρ ℓ w).comp continuous_levK, ?_⟩
  intro F hF m₂
  obtain ⟨hN, hM, hLv, hC, hG, hZ⟩ := hF
  let h : GA E (r + s) := lev (Ad E) r s (1, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)
  let F' := rt E (r + s) h F
  let G : Sm E r := ⟨_, GlobalTheory.T.levi_restriction_smooth E r s F'.1 F'.2⟩
  have hGv : ∀ m₁, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
    intro m₁
    change F.1 (lev (Ad E) r s (m₁, 1) * h) = _
    have e : (m₁, m₂) = ((m₁, 1) * (1, m₂) : GA E r × GA E s) := by simp
    rw [e, map_mul]
    simp only [h, mul_assoc]

  have hcoef : ∀ g : GA E r, (fun k : Kinf E r => (cptRep E r k G).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (levK E r s)) := by
    intro g
    have key := coeff_comp ρ (levK E r s) κ (hC (lev (Ad E) r s (g, m₂) * finGL E (r + s) t))
    convert key using 1
    funext k
    change G.1 (g * infGL E r (Unitary.toUnits k)) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
      infGL E (r + s) (Unitary.toUnits (levK E r s k * κ)))
    rw [hGv, lev_infGL_right, ← toUnits_levK (s := s),
      ← map_mul (Unitary.toUnits : _ →* (Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))ˣ)]

  have hle : (levelOne s L t : Set (GL (Fin r) (Af E))) ⊆ {k | finRep E r k G = G} := by
    intro k hk
    refine Subtype.ext (funext fun m => ?_)
    change G.1 (m * finGL E r k) = G.1 m
    rw [hGv, hGv]
    have hk' : F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ) *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t)) =
        F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) :=
      congrFun (congrArg Subtype.val (hLv _ (mem_levelOne.1 hk))) _
    rw [← hk', lev_finGL_right]

  have hkill : ∀ z ∈ J₁, z G = 0 := by
    refine H3 F' (fun x g => ?_) (fun z hz => ?_) G (fun m => rfl)
    · change F.1 (unip x * g * h) = F.1 (g * h)
      rw [mul_assoc, hN]
    · change z (rt E (r + s) h F) = 0
      rw [← Module.End.mul_apply, (commute_rt_of_mem_Zalg (hJ.1 hz) h).eq, Module.End.mul_apply, hZ z hz, map_zero]
  refine ⟨G, ⟨⟨fun γ g => ?_, isOpen_stab_of_mem_nhds (finRep E r) G
      (Filter.mem_of_superset ((isOpen_levelOne hL t).mem_nhds (one_mem _)) hle),
    kfin_of_coeff _ G hcoef, zfin_of_cofin hJ₁ hkill, fun g => ?_⟩, fun k hk => hle hk, hcoef, hkill⟩, hGv⟩
  ·
    rw [hGv, hGv]
    have e : lev (Ad E) r s (ratGL E r γ * g, m₂) = lev (Ad E) r s (ratGL E r γ, ratGL E s 1) * lev (Ad E) r s (g, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, map_one, one_mul]
    simp only [e, mul_assoc]
    exact hM (γ, 1) _
  ·
    obtain ⟨C, N, hb⟩ := hG (lev (Ad E) r s (g, m₂) * finGL E (r + s) t)
    obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.levi_embedding_height_bound E r s (Unitary.toUnits κ)
    refine ⟨|C| * B ^ N, N, fun y => ?_⟩
    have e1 : G.1 (g * infGL E r y) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
        infGL E (r + s) (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)) := by
      rw [hGv, lev_infGL_right]
    rw [e1]
    have h1 := hb (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)
    have h2 := hB y
    have h0 : 0 ≤ height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) := zero_le_one.trans (one_le_height _)
    calc _ ≤ C * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N := h1
      _ ≤ |C| * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)
      _ ≤ |C| * (B * height y) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 N) (abs_nonneg C)
      _ = |C| * B ^ N * height y ^ N := by rw [mul_pow, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
