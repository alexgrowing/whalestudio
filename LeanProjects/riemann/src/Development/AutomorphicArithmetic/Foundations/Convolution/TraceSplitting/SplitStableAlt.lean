import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.FinSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import GroundTheory.GlobalFields.KummerTheory.Splitting

open NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1

private theorem cmp_continuous {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} {v : Pl F} (u : PlacesOver E v) :
    Continuous (GM.cmp (n := n) u : GL (Fin n) (CompletionsOver E v) → GL (Fin n) (u.1.adicCompletion E)) :=
  Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map (continuous_apply u),
      Units.continuous_coe_inv.matrix_map (continuous_apply u)⟩

theorem UpperTheory.ConvolutionTheory.T.splitStable :
    UpperTheory.ConvolutionTheory.T.SplitStable := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v hs U J hJ
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm⟩
  obtain ⟨w₀⟩ := nonempty_placesOver E (v := v)
  obtain ⟨D, w, -, hw⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ m hm v w₀ hs
  have hc : ∀ (x : GL (Fin n) (CompletionsOver E v)) (i : Fin (m + 1)),
      GM.cmp (w i) x = mapGL n (completionMap v (w i).1) (D.comp n i x) := fun x i =>
    Units.ext (Matrix.ext fun a b => (hw _ i).symm)
  have hshift : ∀ (x : GL (Fin n) (CompletionsOver E v)) (i : Fin (m + 1)),
      D.comp n i (mapGL n (galFin σ v) x) = D.comp n (i + 1) x := fun x i =>
    Units.ext (Matrix.ext fun a b => D.map_shift _ i)
  refine ⟨fun x hx u => ?_, fun hCO hle => ?_⟩
  · obtain ⟨i, rfl⟩ := w.surjective u
    rw [hc]
    refine (hJ (w i) _).1 ?_
    rw [hshift, hJ (w (i + 1)), ← hc]
    exact hx _
  · have hJo : ∀ u, IsOpen (J u : Set (GL (Fin n) (u.1.adicCompletion E))) := fun u => by
      obtain ⟨e, he⟩ := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).1
      have h : (J u : Set (GL (Fin n) (u.1.adicCompletion E))) = e.symm ⁻¹' (U : Set (GL (Fin n) (v.adicCompletion F))) := by
        ext y
        have h1 := hJ u (e.symm y)
        rw [← he, e.apply_symm_apply] at h1
        exact h1.symm
      rw [h]
      exact hCO.2.preimage e.symm.continuous
    refine ⟨⨅ u, (J u).comap (GM.cmp u), fun g => by simp [Subgroup.mem_iInf], ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun u => (hJo u).preimage (cmp_continuous u)
    · intro g hg u
      have hgu : GM.cmp u g ∈ J u := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hg u)
      obtain ⟨e, he⟩ := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).1
      have h2 : e.symm (GM.cmp u g) ∈ U := by
        rw [hJ u, ← he, e.apply_symm_apply]
        exact hgu
      have h3 := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).2.1 _ |>.2 (hle h2)
      rw [← he, e.apply_symm_apply] at h3
      exact h3
