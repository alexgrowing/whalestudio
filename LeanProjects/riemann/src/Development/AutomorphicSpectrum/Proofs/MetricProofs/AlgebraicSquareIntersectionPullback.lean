import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RelabelTransport

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.algebraic_square_intersection_pullback : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2), (∀ (L : Fin (d + 2) → HermLine ι) (L' : Fin (d + 2) → HermLine Q.ιW) (N : HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 0) (Q.v 0) (L j) (L' j)) → IsSmoothHerm N → II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc L' N) = (N.a (Q.κ 1 k₀) : ℝ) * II K ι P (d + 2) L) ∧ ∀ (L : Fin (d + 3) → HermLine ι) (L' : Fin (d + 3) → HermLine Q.ιW), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm (Q.κ 1) (Q.v 1) (L j) (L' j)) → II Q.KW Q.ιW Q.PW (d + 3) L' = 0 := by
  intro hIn II hII K _ ι _ P d k₀ xi2 Q
  obtain ⟨hFam, -, -, hCM⟩ := hII
  letI := Q.finKW
  letI := Q.finιW
  refine ⟨?_, ?_⟩
  · classical
    intro L L' N hL hLL' hN
    haveI : Q.PW.IsPrime := Q.arithW.2.1.1
    let G := GroundTheory.Heights₂.Heights.Inter.genFibreOf (Q.v 0) Q.PW
    let b : FibreBlock (Q.κ 0) := ⟨Q.κ 1 k₀, Q.new⟩
    have hb : ∀ c : FibreBlock (Q.κ 0), c = b := by
      intro c
      apply Subtype.ext
      rcases Q.all c.1 with h | h
      · exact absurd h c.2
      · exact h
    let e : Unit ≃ FibreBlock (Q.κ 0) :=
      { toFun := fun _ => b, invFun := fun _ => (), left_inv := fun _ => rfl,
        right_inv := fun c => (hb c).symm }
    let hq : (u : Unit) → Q.ιW (Q.κ 1 k₀) ≃ fibreIdx Q.ιW (Q.κ 0) (e u) := fun _ => Equiv.refl _
    let I₀ : IFamily G.Φ (fun _ : Unit => Q.ιW (Q.κ 1 k₀)) := fun V _ Ls => NumbersDVR.intNum G.Φ V Ls
    have hI₀ : IsFieldIntersection I₀ := NumbersDVR.IntNumIsFieldIntersection.full G.Φ Unit _
    let J := Targets.Relabel.pullFamily e hq I₀
    have hJ : IsFieldIntersection J := Targets.Relabel.isFieldIntersection_pull e hq hI₀
    have hP := hIn.2.2.2.1.1 II hFam K ι Q.KW Q.ιW (Q.κ 0) (Q.v 0) Q.PW (d + 2) 1 G J L L' (fun _ => N)
      (Q.block 0) Q.arithW (by rw [Q.image 0]; exact Q.arithY) hJ hL hLL' (fun _ => hN)
    rw [Fin.append_right_eq_snoc, Q.image 0] at hP
    rw [hP]
    congr 1
    obtain ⟨V, hV⟩ := Targets.Relabel.exists_map_eq e hq (fibreIdeal (Q.κ 0) G)
    have hVd : IsProjVarF V 1 := by
      rw [← Targets.Relabel.isProjVarF_map_iff e hq, ← hV]
      exact hIn.2.2.2.1.2.2 K ι Q.KW Q.ιW (Q.κ 0) (Q.v 0) Q.PW (d + 2) 1 G (Q.block 0) Q.arithW
        (by rw [Q.image 0]; exact Q.arithY)
    have hVs : ∃ S : Set (MRingOver G.Φ fun _ : Unit => Q.ιW (Q.κ 1 k₀)),
        (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ V = Ideal.span S := by
      obtain ⟨T, hT, hTs⟩ := Q.fibre_line G
      refine ⟨(Targets.Relabel.ringEquiv G.Φ e hq).symm '' T, ?_, ?_⟩
      · rintro f ⟨g, hg, rfl⟩
        exact Targets.Relabel.isMultiHomog_symm e hq (hT g hg)
      · rw [← Ideal.map_span, ← hTs, hV, Ideal.map_symm, Targets.Relabel.comap_map]
    have hL1 := hIn.2.2.2.1.2.1 G.Φ _ V I₀ hVd hVs hI₀ (N.a (Q.κ 1 k₀))
    have key : (fun j : Fin 1 => fibreDeg (Q.κ 0) N.a ∘ e) = ![fun _ : Unit => N.a (Q.κ 1 k₀)] := by
      funext j u
      fin_cases j
      rfl
    show ((I₀ (Ideal.comap (Targets.Relabel.ringEquiv G.Φ e hq) (fibreIdeal (Q.κ 0) G)) 1
      fun j => fibreDeg (Q.κ 0) N.a ∘ e : ℤ) : ℝ) = _
    rw [hV, Targets.Relabel.comap_map, key, hL1]
  · intro L L' hL hLL'
    have h := hCM K ι Q.KW Q.ιW (Q.κ 1) (Q.v 1) Q.PW (d + 2) (d + 3) 0 L L' Fin.elim0 (Q.block 1)
      Q.arithW (by rw [Q.image 1]; exact Q.arithY) (by omega) hL hLL' (fun j => j.elim0)
    simpa [Fin.append_elim0] using h
