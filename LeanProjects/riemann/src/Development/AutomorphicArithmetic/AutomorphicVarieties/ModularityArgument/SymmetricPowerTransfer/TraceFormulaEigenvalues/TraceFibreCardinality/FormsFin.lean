import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

theorem UpperTheory.V.Z.Sym.Tf.formsFin :
    UpperTheory.V.Z.Sym.Tf.FormsFin := by
  intro Γ G V _ _ _ _ _ B hB
  obtain ⟨S, hS⟩ := hB.cls
  let L : B.Forms →ₗ[ℂ] (S → V) :=
    (LinearMap.funLeft ℂ V (fun s : S => (s : G))).comp B.Forms.subtype
  refine Module.Finite.of_injective L ?_
  intro φ ψ h
  apply Subtype.ext
  funext g
  obtain ⟨γ, s, hs, u, hu, rfl⟩ := hS g
  have hsv : φ.1 s = ψ.1 s := congrFun h ⟨s, hs⟩
  have e1 : φ.1 (B.ι γ * s * u) = (B.ω ⟨u, hu⟩ : ℂ) • φ.1 (B.ι γ * s) := φ.2.2 _ ⟨u, hu⟩
  have e2 : ψ.1 (B.ι γ * s * u) = (B.ω ⟨u, hu⟩ : ℂ) • ψ.1 (B.ι γ * s) := ψ.2.2 _ ⟨u, hu⟩
  have f1 : φ.1 (B.ι γ * s) = B.W γ (φ.1 s) := φ.2.1 γ s
  have f2 : ψ.1 (B.ι γ * s) = B.W γ (ψ.1 s) := ψ.2.1 γ s
  rw [e1, e2, f1, f2, hsv]
