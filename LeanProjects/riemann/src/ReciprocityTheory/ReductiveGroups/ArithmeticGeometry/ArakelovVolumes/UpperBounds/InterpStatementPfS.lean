import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfR

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem kronHolPsi_of (hE : ExtFStatement (E := E)) (hM : MeasInvStatement (E := E))
    (hV : VanishAtSStatement (E := E)) (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E))
    (hC : OmFConnStatement (E := E)) (hR : NfacRmulStatement (E := E))
    (hLa : NfacLactStatement (E := E)) : KronHolPsiStatement (E := E) := by
  intro r X Xa Fl _hPD ψ hψ hψs hψb hbm0 hstr0 hLnn j
  obtain ⟨bb, m, hbb4, hbm, hmar⟩ := hbm0
  obtain ⟨η, hη, hstr⟩ := hstr0
  obtain ⟨C0, hC0⟩ := hψb

  obtain ⟨x0, ho, b0, hb0, hx⟩ := hO r X (Fl.xs j) (Fl.xs_mem j)
  have hbbpos : 0 < bb := lt_of_le_of_lt (by positivity) hbb4

  obtain ⟨ε, hε, hball, hiso, hnull, F, hFd, hI⟩ :=
    coord_step (X := X) hLU hC Xa Fl ψ x0 ho (hψs x0 ho) bb m hbbpos hbm (hmar x0 ho) η hη (hstr x0 ho)
      (hLnn x0 ho) j b0 hb0 hx
  have hint := integ_step (X := X) x0 ho Xa Fl ψ (hψs x0 ho) bb ε hε hball hnull F hI

  obtain ⟨P, hBE, hPF⟩ :=
    hE r X x0 ho Xa.Fp F hFd (extF_hyp (X := X) x0 ho Xa.Fp ψ C0 hC0 bb hbbpos.le F hint)
  obtain ⟨hw, hs0, hdet⟩ := coord_data (X := X) hLU Xa Fl j x0 ho b0 hb0 hx
  have hP1 : P x0 = 1 :=
    value_base (X := X) hV x0 ho Xa Fl ψ (hψs x0 ho) bb ε hε hball F hFd hI P hPF hw hs0 hdet
  have hMW := metricW_of hR hLa hO hLU X Xa.Fp ψ hψ hψs ⟨C0, hC0⟩
  refine ⟨x0, Wpsi X Xa.Fp ψ, bb, F, P, 1, ho, hMW.1, hMW.2, ?_, hbb4, hFd,
    inAt_of (X := X) x0 Xa.Fp ψ bb F hint, hBE, hPF, X.Γ.one_mem, ?_, ?_⟩
  · intro x hx'
    simp [Wpsi, hx']
  · rw [lact_one (X := X), hx, hBE.2 x0 (orth_mem_dom (X := X) x0 ho) b0 hb0, hP1, mul_one]
    exact bchar_ne_zero (X := X) hb0 Xa.Fp
  · intro γ hγ j' hne
    exact vanish_other (X := X) hV hM hO hLU hR Xa Fl ψ C0 hC0 bb hbbpos.le x0 ho b0 hb0 j hx ε hε hball
      hiso hnull F hI P hBE hPF hγ j' hne

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
