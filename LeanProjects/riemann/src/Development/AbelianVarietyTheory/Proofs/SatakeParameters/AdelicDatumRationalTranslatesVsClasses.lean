import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem inFr_inFr_eq_toLin {E : Type} [Field E] {a b : ℕ} (f g : Sp E a ≃ₗ[E] Sp E a) (f' g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Matrix (Fin b) (Fin b) E) (hN : LinearMap.toMatrix' (f'.trans g').toLinearMap * N = 1) (z : HomE E a b) :
    inFr f f' (inFr g g' z) = Matrix.toLin' N ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' (f.trans g).toLinearMap) := by
  rw [Matrix.toLin'_toMatrix']
  have key : ∀ y, Matrix.toLin' N y = (f'.trans g').symm y := by
    intro y
    have h : (f'.trans g') (Matrix.toLin' N y) = y := by
      have h0 := congrArg (fun M => Matrix.toLin' M y) hN
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix'] at h0
      exact h0
    exact ((f'.trans g').symm_apply_eq.2 h.symm).symm
  ext w l
  simp only [inFr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, key, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]

set_option maxHeartbeats 1000000 in
theorem adelicDatum_at_translates : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) = 1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x' z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * (t.rd u μ).Xi i c c' (seamHom t.seam (Matrix.toLin' (star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap)) ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap)))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ Xi muT law i hi c c' x x' γ hγ γ' hγ' κ κ' hx hx' hM z
  have hr : ratA D.host.F γ ∈ UPts (sigD D) (gramN D i (Nat.le_of_succ_le hi)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ, hγ, rfl⟩
  have hr' : ratA D.host.F γ' ∈ UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ', hγ', rfl⟩
  let x₀ : UA D i (Nat.le_of_succ_le hi) := ⟨ratA D.host.F γ * ((St i _).y c).1, mul_mem hr ((St i _).y c).2⟩
  let x₀' : UA D (i + 1) hi := ⟨ratA D.host.F γ' * ((St (i + 1) hi).y c').1, mul_mem hr' ((St (i + 1) hi).y c').2⟩
  have h1 := law.lev i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') x₀ x₀' x x' κ κ' hx hx' z
  have h2 := law.rat i hi ((St i _).chOf c) ((St (i + 1) hi).chOf c') ((St i _).y c) ((St (i + 1) hi).y c') x₀ x₀' γ hγ γ' hγ' rfl rfl z
  have h3 := law.read i hi c c' (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
      (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)
  refine h1.trans ?_
  rw [h2, h3, inFr_inFr_eq_toLin _ _ _ _ _ hM z]

end GlobalTheory.TwV
