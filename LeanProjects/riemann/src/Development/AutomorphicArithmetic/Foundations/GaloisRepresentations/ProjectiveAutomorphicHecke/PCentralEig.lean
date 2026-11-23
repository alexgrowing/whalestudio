import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.MapWopWmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
open Module
universe u v

theorem UpperTheory.Gal.CertificateRingHomMap.pCentralEig_holds :
    UpperTheory.Gal.CertificateRingHomMap.CentralEig := by
  intro Γ H Z V _ _ _ _ _ ι K ξ _ ζ hc M hM hne hst
  haveI : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le hM
  haveI : Nontrivial M := Submodule.nontrivial_iff_ne_bot.2 hne
  let R : Z → Module.End ℂ M := fun z =>
    { toFun := fun Φ => ⟨fun g => (Φ : H → V) (g * ζ z), hst Φ Φ.2 z⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcomm : ∀ i j : Z, R i * R j = R j * R i := by
    intro i j
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun g => ?_)
    change (Φ : H → V) (g * ζ i * ζ j) = (Φ : H → V) (g * ζ j * ζ i)
    rw [mul_assoc, mul_assoc, hc i (ζ j)]
  obtain ⟨v, -, hv0, hv⟩ := UpperTheory.V.LinAlg.simEig R hcomm _ (⊤ : Submodule ℂ M) rfl top_ne_bot
    (fun _ _ _ => Submodule.mem_top)
  choose a ha using hv
  have hΦ : ∀ z g, (v : H → V) (g * ζ z) = a z • (v : H → V) g := fun z g =>
    congrFun (congrArg Subtype.val (ha z)) g
  have hv0' : (v : H → V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hv0'
  have hg₀' : (v : H → V) g₀ ≠ 0 := hg₀
  have cancel : ∀ b c : ℂ, b • (v : H → V) g₀ = c • (v : H → V) g₀ → b = c :=
    fun b c h => smul_left_injective ℂ hg₀' h
  have a1 : a 1 = 1 := by
    apply cancel
    rw [← hΦ, map_one, mul_one, one_smul]
  have amul : ∀ x y, a (x * y) = a x * a y := by
    intro x y
    apply cancel
    rw [← hΦ, map_mul, ← mul_assoc, hΦ, hΦ, smul_smul, mul_comm]
  let ψ : Z →* ℂˣ := ({ toFun := a, map_one' := a1, map_mul' := amul } : Z →* ℂ).toHomUnits
  have hψ : ∀ z, (ψ z : ℂ) = a z := fun z => by
    simp only [ψ, MonoidHom.coe_toHomUnits]
    rfl
  refine ⟨(v : H → V), v.2, hv0', ψ, ?_, ?_, ?_⟩
  · intro z g
    rw [hψ, hΦ]
  · intro z hz
    apply Units.ext
    rw [hψ, Units.val_one]
    apply cancel
    rw [← hΦ, one_smul]
    exact (hM v.2).2 _ hz g₀
  · intro z γ b hz hb
    rw [hψ]
    apply cancel
    rw [← hΦ, ← hb, ← hc z g₀, hz]
    exact (hM v.2).1 γ g₀
