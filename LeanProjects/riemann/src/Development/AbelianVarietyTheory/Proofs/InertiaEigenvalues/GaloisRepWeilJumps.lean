import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory
open Formalism.MainNotions.SumRepresentations.At

theorem norm_natCast_padicAlgCl_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h1 : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h1, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem mem_placesOver_of_inducesW (D : D7) (i : D.nd.Loc) (τ : D.host.E →+* Qbar (D.nd.l i)) (w : PlE D.host)
    (h : InducesW D.nd i τ w) : w ∈ placesOver D.host.E (D.nd.l i) := by
  have := (h ((D.nd.l i : ℕ) : 𝓞 D.host.E)).1
  show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  apply this
  simpa using norm_natCast_padicAlgCl_lt_one (D.nd.l i)

section Tw
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem twGL_val (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (g : Γ) :
    ((twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det • ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) := by
  simp only [twGL, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_map]
  simp [Algebra.algebraMap_eq_smul_one, Matrix.GeneralLinearGroup.val_det_apply]

theorem isInv_twGL_iff (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (W : Submodule k (Fin a → k)) :
    IsInv (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have hu : ((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _).1 (χ g).isUnit |>.ne_zero
    have := W.smul_mem (((χ g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).det)⁻¹ (h g v hv)
    rw [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ hu, one_smul] at this
    exact this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL (ρ : Γ →* GL (Fin a) k) (χ : Γ →* GL (Fin 1) k) (h : IsSSRep ρ) :
    IsSSRep (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL_iff ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL_iff ρ χ W').2 hW', hc⟩

end Tw

theorem contQ_twGL (D : D7) (i : D.nd.Loc) {a : ℕ} (ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)))
    (χ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) (hρ : ContQ D.nd i ρ) (hχ : ContQ D.nd i χ) :
    ContQ D.nd i (twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) := by
  unfold ContQ at *
  simp only [twGL_val]
  exact (hχ.matrix_det).smul hρ

theorem twist_compatible : ∀ D : D7, SumRepresentations.tie0 D → ∀ (i : D.nd.Loc) (a : ℕ) (ρ : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i))) (χ : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i))) (p q : ∀ w, D.naut.LP w) (m : (D.host.E →+* ℂ) → Multiset ℂ) (c : (D.host.E →+* ℂ) → ℂ), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, D.naut.wdOf i ρ w = p w) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = m ((D.naut.iotaQC i).toRingHom.comp τ)) → (SumRepresentations.At.ContQ D.nd i χ ∧ IsSSRep χ ∧ (∀ w, D.naut.wdOf i χ w = q w) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i χ τ).map (fun n : ℤ => (n : ℂ)) = {c ((D.naut.iotaQC i).toRingHom.comp τ)}) → ∃ ρ' : GE D.nd →* GL (Fin a) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ' ∧ IsSSRep ρ' ∧ (∀ w, D.naut.wdOf i ρ' w = D.naut.lpChar (p w) (q w)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ' w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ' τ).map (fun n : ℤ => (n : ℂ)) = (m ((D.naut.iotaQC i).toRingHom.comp τ)).map (· + c ((D.naut.iotaQC i).toRingHom.comp τ))) := by
  intro D hT i a ρ χ p q m c hρ hχ
  obtain ⟨hρc, hρs, hρw, hρl⟩ := hρ
  obtain ⟨hχc, hχs, hχw, hχl⟩ := hχ
  obtain ⟨-, -, hG⟩ := hT
  obtain ⟨-, -, -, hGi⟩ := hG
  obtain ⟨-, -, -, h4⟩ := hGi i
  obtain ⟨hdR, hwd, hj⟩ := h4 a ρ χ hρc hχc
  have hok : ∀ {b} (r : GE D.nd →* GL (Fin b) (Qbar (D.nd.l i))),
      (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i r w) → ∀ w, WDok D.nd D.naut i r w := by
    intro b r hr w
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · exact Or.inr (hr w hw)
    · exact Or.inl hw
  refine ⟨twGL ρ (Matrix.GeneralLinearGroup.det.comp χ), contQ_twGL D i ρ χ hρc hχc, isSSRep_twGL ρ χ hρs,
    fun w => ?_, fun w hw => ⟨?_, fun τ hτ => ?_⟩⟩
  · rw [hwd w (hok ρ (fun w hw => (hρl w hw).1) w) (hok χ (fun w hw => (hχl w hw).1) w), hρw w, hχw w]
  · exact (hdR w hw (hχl w hw).1).2 (hρl w hw).1
  · obtain ⟨n, hn, hnc⟩ := Multiset.map_eq_singleton.1 ((hχl w hw).2 τ hτ)
    have hall : ∀ w', InducesW D.nd i τ w' → D.naut.IsdRW i ρ w' ∧ D.naut.IsdRW i χ w' := fun w' hw' =>
      ⟨(hρl w' (mem_placesOver_of_inducesW D i τ w' hw')).1, (hχl w' (mem_placesOver_of_inducesW D i τ w' hw')).1⟩
    rw [hj τ n hall hn, Multiset.map_map, ← (hρl w hw).2 τ hτ, Multiset.map_map, ← hnc]
    congr 1
    funext x
    simp

end GlobalTheory
