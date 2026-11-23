import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.TcPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.TcSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.Vertex
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.OddVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.EntVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.NotTight
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.LowCase

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

private theorem lat_six {Si : Set (ℤ × ℤ)} (h : CompanionTheory Si) (h1 : -wAl ∉ Si → -wTh ∉ Si) (h2 : wBe ∉ Si → wPs ∉ Si → -wAl ∉ Si) :
    wBe ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ nP := by
  rcases h with h | ⟨a, -, b⟩ | ⟨a, -, b⟩ | ⟨a, -, b⟩ | ⟨a, -, b⟩ | ⟨a, -, b⟩
  · exact h
  · exact absurd a (h2 (fun x => absurd (Finset.mem_coe.1 (b x)) (by decide)) fun x => absurd (Finset.mem_coe.1 (b x)) (by decide))
  · exact absurd a (h1 fun x => by simpa [wAl, wTh, wPs, wBe] using b x)
  · exact absurd a (h2 (fun x => absurd (Finset.mem_coe.1 (b x)) (by decide)) fun x => absurd (Finset.mem_coe.1 (b x)) (by decide))
  · exact absurd a (h1 fun x => by simpa [wAl, wTh, wPs, wBe] using b x)
  · exact absurd a (h1 fun x => by simpa [wAl, wTh, wPs, wBe] using b x)

theorem UpperTheory.V.Ws.lat :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) (pr : Bool) (g0 : G ℚ Ω), LabOk D pr →
      (∀ i j, i ≠ j → Raw.bar (chi D pr i) g0 ≠ Raw.bar (chi D pr j) g0) → ∀ P : PD Unit (G ℚ Ω) 𝔞.V, QPair D pr g0 𝔞 P → NearSplit D pr 𝔞 P → StarE P.r →
      ∃ P' : PD Unit (G ℚ Ω) 𝔞.V, QPair D pr g0 𝔞 P' ∧ IsConj4 (mapRep 𝔞.toK P.r) (mapRep 𝔞.toK P'.r) ∧ LatShape D pr g0 (𝔞.red c) (P'.map (residue 𝔞.V)) := by
  intro hP Ω _ _ _ l _ c D hD 𝔞 pr g0 _ hd P hQ hN hS
  obtain ⟨t, P', hT, h6⟩ := vertex 𝔞 P hQ.small (hQ.pair.low ())
    (fun g i j hij => by simpa [diagRep, Matrix.diagonal_apply_ne _ hij] using hN.red g i j) hN.flag hS
  obtain ⟨hp, hdg, hψ, hc⟩ := tcPair (frQ D pr g0) (𝔞.a c) 𝔞.toK Subtype.val_injective t P P' hT hQ.pair
  have hsm := tcSmall 𝔞 t P P' hT hQ.small
  have hred : ∀ x ∈ maximalIdeal c.O, 𝔞.red c x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 (map_nonunit (𝔞.a c) x hx)
  have hpre : PreRes (frQ D pr g0) (𝔞.red c) (P'.map (residue 𝔞.V)) := by
    refine ⟨hp.map _, fun g i => ?_, fun v s hs i => ?_, ?_⟩
    · refine Ideal.Quotient.eq.2 ?_
      rw [hdg]
      simpa [diagRep, frQ] using hN.red g i i
    · refine (PD.map_ψ P' _ v i s).trans (Ideal.Quotient.eq.2 ?_)
      exact (hψ v i s).symm ▸ hN.char s hs i
    · obtain ⟨A, _, _, _, f, P₁, hf, hcont, rfl⟩ := hsm
      haveI := hf.loc
      exact hcont.map ((residue 𝔞.V).comp f) fun x hx => (residue_eq_zero_iff _).2 (map_nonunit f x hx)
  have hmul : ∀ i g, (frQ D pr g0).χ i g * (frQ D pr g0).χ i.rev g = (frQ D pr g0).ν g := by
    intro i g
    cases pr <;> fin_cases i <;> simp [frQ, chi, lab, Raw.ps, Raw.th, Fin.rev, mul_comm]
  have hE := entVan _ _ _ hpre hmul (oddVan D hD hP.loc _ _ hred pr g0 hd)
  obtain ⟨n1, n2⟩ := noNeg _ _ _ hpre hE
  obtain ⟨s1, s2, s3⟩ := lat_six h6 n1 n2
  obtain ⟨u1, u2, u3, u4⟩ := shape _ _ _ hpre hE s1 s2 s3
  refine ⟨P', ⟨hsm, hp, fun s hs i => (hψ () i s).trans (hQ.inert s hs i)⟩, hc,
    ⟨hpre.pair, ⟨hpre.diag, hpre.char, .inl ⟨u1, u2⟩⟩, hpre.cont⟩, u1, u2 (), u3, u4.imp id ?_⟩
  rintro ⟨v1, ⟨v, v2, v3⟩, v4⟩
  refine ⟨v1, v2, fun s hs => ?_, fun ⟨m, hm⟩ => v4 ⟨fun _ => m, fun _ => hm⟩⟩
  have e : Raw.bar (chi D pr 0) s = Raw.bar (chi D pr 2) s := (𝔞.j c).injective (v3 s hs)
  have hu : Raw.bar D.al s ≠ 0 := ((D.al s).isUnit.map (residue c.O)).ne_zero
  have ht : Raw.bar D.th s = Raw.bar D.al s * Raw.bar D.Psi s := map_mul (residue c.O) (D.al s : c.O) (D.Psi s : c.O)
  cases pr
  · exact (mul_eq_left₀ hu).1 (ht.symm.trans e)
  · exact (mul_eq_left₀ hu).1 (ht.symm.trans e.symm)
