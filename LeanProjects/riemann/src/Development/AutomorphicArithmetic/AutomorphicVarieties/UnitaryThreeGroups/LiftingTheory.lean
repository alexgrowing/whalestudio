import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TypeIIrrCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem left_conj {R : Type} [CommRing R] {m : ℕ} (x y : GG m R) (h1 : x.mat = 1) (h2 : x.right = -1)
    (h3 : y.right = 1) : (x * y * x⁻¹).left = theta y.left := by
  have hl : x.left = 1 := Units.ext h1
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    hl, h2, h3, inv_one, mul_one, one_mul, sgnAct_neg_one, map_one]

private theorem pairing_theta {R : Type} [CommRing R] {m : ℕ} (a : GL (Fin m) R) :
    (a : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m * (theta a : GL (Fin m) R) = Jmat R m := by
  rw [theta_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ (Jmat R m) (Jmat R m), Jmat_mul_Jmat,
    Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.one_mul]

private theorem cont_hom {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [Monoid M] [TopologicalSpace M]
    (f : Γ →* Mˣ) (h : Continuous fun g => (f g : M)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) :
    (Af.tw ρ χ⁻¹).comp χ.ker.subtype = ρ.comp χ.ker.subtype := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hs : χ s = 1 := s.2
  show (Af.tw ρ χ⁻¹ s : Matrix (Fin n) (Fin n) k) = ρ s
  rw [Af.tw_val, MonoidHom.inv_apply, hs, inv_one, Units.val_one, one_smul]

private theorem ad_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (ρ : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s : Γ)
    (X : Matrix (Fin n) (Fin n) k) :
    (Af.tw ρ χ s : Matrix (Fin n) (Fin n) k) * X * ((Af.tw ρ χ s)⁻¹ : GL (Fin n) k) =
      (ρ s : Matrix (Fin n) (Fin n) k) * X * ((ρ s)⁻¹ : GL (Fin n) k) := by
  rw [← map_inv, ← map_inv, Af.tw_val, Af.tw_val, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_smul]

theorem UpperTheory.V.U3.bloch_kato_type_one :
    CohInp → Af.AdVanishK → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ),
      TypeI D.η r → D.IsAutI ι r h.mult → Af.BlochKatoSelmerVanishes l (adRep r) := by
  intro hC hA Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM r h _ ι hI hAut
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have hK : ∀ s : G K Ω, (r (galEmb ℚ K Ω s)).right = 1 := fun s =>
    (h.mult _).trans (show galEmb ℚ K Ω s ∈ D.η.ker from D.η_ker ▸ galEmb_mem ℚ K Ω s)
  have hc : (r D.cc).right = -1 := (h.mult _).trans hM.ηc
  have hz : Continuous fun s : G K Ω => ((cycZ K Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ K Ω l)
  have hcyc : Continuous fun s : G K Ω => (cycBar K Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp
      (continuous_subtype_val.comp hz)
  refine hA K D.gd.quad 3 (by norm_num) l Ω ι _ ?_ hAut ?_ _ ⟨D.cc, Jgl _ 3, D.conj, ?_, ?_, ?_⟩
  · refine cont_hom _ ?_
    simp only [Af.tw_val, MonoidHom.inv_apply, ← map_inv]
    exact (hcyc.comp continuous_inv).smul (h.cont.comp (galEmbTop ℚ K Ω).1.continuous)
  · rw [irr_tw]
    exact typeI_irr_cyc hC D hM h hI
  · intro s s' hs
    have hs' : galEmb ℚ K Ω s' = D.cc * galEmb ℚ K Ω s * D.cc⁻¹ := hs
    have h1 : cycBar K Ω l s' = cycBar K Ω l s := by
      show cycBar ℚ Ω l (galEmb ℚ K Ω s') = cycBar ℚ Ω l (galEmb ℚ K Ω s)
      rw [hs', map_mul, map_mul, map_inv, mul_inv_cancel_comm]
    have h2 : D.rhoK r h.mult s' = theta (D.rhoK r h.mult s) := by
      rw [D.rhoK_apply, D.rhoK_apply, hs', map_mul, map_mul, map_inv]
      exact left_conj _ _ h.norm.atc hc (hK s)
    rw [Af.tw_val, Af.tw_val, h2, MonoidHom.inv_apply, MonoidHom.inv_apply, h1, Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul]
    have h3 : (cycBar K Ω l ^ (1 - ((3 : ℕ) : ℤ))) s = (cycBar K Ω l s)⁻¹ * (cycBar K Ω l s)⁻¹ := by
      rw [MonoidHom.zpow_apply, show (1 - ((3 : ℕ) : ℤ)) = -1 + -1 by norm_num, _root_.zpow_add, _root_.zpow_neg_one]
    rw [h3]
    exact congrArg _ (pairing_theta _)
  · intro s X
    rw [ad_tw]
    show (r (galEmb ℚ K Ω s)).adFun X = _
    rw [GG.adFun, if_pos (hK s)]
    rfl
  · intro X
    have hl : (r D.cc).left = 1 := Units.ext h.norm.atc
    show (r D.cc).adFun X = _
    rw [GG.adFun, hc, if_neg (by decide), h.norm.atc, hl, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    rfl
