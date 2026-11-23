import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStatementOfSmall
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsGaloisRepOfDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStatementOfSmallStatement

section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameGal
section Poly
open Polynomial Formalism.L2.Col
variable {K : Type} [Field K]
end Poly
section Runs
open Formalism.BasicNotions Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds GlobalTheory.GalDef
end Runs
section Galois
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.ExpFrame GlobalTheory.TripleGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
variable [IsCMField E]
end Galois
section Side
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.ExpFrame GlobalTheory.TripleGal GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.GalDef
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.L2.Col Polynomial
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] [IsCMField E]
variable (Ω) in
theorem galois_side_of_compatible_systems (p1 : GlobalTheory.Published.ClozelCohomological) (p2 : GlobalTheory.Published.CohomologicalCsdTempered)
    (p3 : GlobalTheory.Published.HeckeLAdicCharacter) (p4 : GlobalTheory.Published.ChebotarevDegreeOne)
    (p6 : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (p7 : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup)
    (p8 : GlobalTheory.Published.BhattScholzeCrystallineLattices) (p9 : GlobalTheory.Published.HeckeLAdicCharacterAbove) (p10 : GlobalTheory.Published.LocalLanglandsGL)
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    (ι : Qbar l ≃+* ℂ) {T : Type} [DecidableEq T] {inc : T → (E →+* Qbar l)} (half : IsHalf inc) (s : T → ℤ)
    {P : Par} {W : Wts T} (hP : P.Hyp) (hL : P.Large) (hW : W.Ok P) (F : Frame l T P.Nr) (Bk : (F.I → Qbar l) → Prop)
    {Pl : Type} (pt : Pl → Fin P.Nr → F.I) (lab : Pl → HeightOneSpectrum (𝓞 E))
    (cofin : {v : HeightOneSpectrum (𝓞 E) | (Ideal.absNorm v.asIdeal).Prime ∧ v ∉ Set.range lab}.Finite)
    (hlab : ∀ Q, IsSplitAt (lab Q) ∧ ((l : ℕ) : 𝓞 E) ∉ (lab Q).asIdeal)
    (haut : ∀ mu θ, (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → ∃ π, SystemOf ι inc s lab P.Nr mu (sysOf P.Nr pt θ) π)
    (hblk : ∀ θ, Bk θ → ∀ Q, ∃ ν : Qbar l, ‖ι ν‖ ^ 2 = (Ideal.absNorm (lab Q).asIdeal : ℝ) ^ (P.Nr - P.t) ∧
      blockPoly ν (Ideal.absNorm (lab Q).asIdeal) P.t ∣ heckePolyOf P.Nr (Ideal.absNorm (lab Q).asIdeal) (sysOf P.Nr pt θ Q)) :
    GalSide Ω inc P W F Bk := by
  have hN := hP.Nr_eq
  have ht := hP.t_ge
  have hm := hP.m_pos
  have hk := hP.m_le
  obtain ⟨c, hc, hc'⟩ := exists_of_half half (fun τ => (h0 P : ℤ) - P.Nr + 1 + s τ) fun τ => -s τ
  obtain ⟨tw, htw, hcr⟩ := exists_crys_char Ω p3 p9 ι c ((h0 P : ℤ) - P.Nr + 1) fun i => by
    obtain ⟨τ, rfl | rfl⟩ := half.2.2 i
    · rw [hc, hc']; ring
    · rw [cj_cj, hc, hc']; ring
  let Fn : FrobNorm E Ω l Pl := ⟨lab, -1, tw, htw, cofin⟩
  have main := _root_.GlobalTheory.GalAut.exists_galoisRep_of_definiteUnitary p7 p6 p1 p2 p3 p9 p4 p8 p10 E Ω hE P.Nr (by omega)
  refine ⟨Pl, pt, Fn, cj, Or.inr rfl, fun mu θ ha hθ => ?_, fun θ hθ hB => ?_⟩
  · obtain ⟨π, hπ⟩ := haut mu θ ha hθ
    obtain ⟨lam, hl, hl1, hl2, -⟩ := hπ.weights half
    obtain ⟨⟨r, hr, hf⟩, -⟩ := main π hπ.1 lam hl l ι hπ.2.2.1
    refine ⟨GlobalTheory.TwistAbove.twGL tw r,
      fun τ a => ((Fin.rev a : ℕ) : ℤ) - (lam (ι.toRingHom.comp τ)).w (Fin.rev a) + c τ, fun τ a => ⟨?_, ?_⟩, ?_,
      SystemOf.reads Fn hlab hπ hf fun g => charpoly_smul _ (Units.ne_zero _)⟩
    · have := a.2
      simp only [hl2, hc', DomWeight.dual, Fin.rev_rev, hl1, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      rw [Fin.val_rev]
      omega
    · have := a.2
      simp only [cj_cj, hc, hl1, Formalism.CohomologicalDescent.UnitNormBounds.UN, Fin.val_rev]
      omega
    · convert crysWith_twist (r' := GlobalTheory.TwistAbove.twGL tw r) (fun _ => rfl) hr htw hcr using 2 with τ
      rw [jumpsOf, Multiset.map_map]
      conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
      rfl
  · have ha : ∀ τ, Antitone (res P.Nr (W.lam τ)) := fun τ a b h => hW.anti τ a b h b.2
    obtain ⟨π, hπ⟩ := haut W.lam θ ha hθ
    obtain ⟨lam, hl, hl1, hl2, hl3⟩ := hπ.weights half
    have r1 := fun τ => isRunAt_block hP hL hW τ _ _ (hl1 τ)
    have r2 := fun τ => isRunAt_dual (by omega) (r1 τ).1
    obtain ⟨-, v, hv, hd, -⟩ := (p4.dense (Ω := Ω) cofin).nonempty
    obtain ⟨Q, -⟩ : v ∈ Set.range lab := by
      by_contra h
      exact hv ⟨((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd, h⟩
    have hstr : HasString l π P.t := by
      obtain ⟨hu, σ, S, h1, h2, h3⟩ := hπ.2.2.2 Q
      obtain ⟨ν, hν, hdv⟩ := hblk θ hB Q
      obtain ⟨u, hu1, hu2⟩ := string_of_dvd ι (absNorm_ne_zero _) (by omega) S (card_of_hasSat h2) _ h3 ν hν hdv
      exact ⟨lab Q, (hlab Q).1, (hlab Q).2, hu, σ, S, u, h1, h2, hu1, hu2⟩
    obtain ⟨a, ρ, χ, bot, h1, h2, h3, h4, h5⟩ := (main π hπ.1 lam hl l ι hπ.2.2.1).2 P.t (by omega) (fun φ => by
      obtain ⟨τ, rfl | rfl⟩ := hl3 φ
      · exact ⟨_, (r1 τ).1⟩
      · exact ⟨_, hl2 τ ▸ (r2 τ).1⟩) hstr
    refine ⟨a, GlobalTheory.TwistAbove.twGL tw ρ, fun j => χ j * tw, fun τ => bot τ + c τ, h1,
      continuous_twist (fun _ => rfl) h2 htw, fun j => ?_, fun τ => ⟨?_, ?_⟩, SystemOf.reads Fn hlab hπ h5 fun g => ?_⟩
    · convert crysWith_twist (r' := rk1 (χ j * tw)) (fun g => ?_) (h3 j) htw hcr using 2 with τ
      · rw [Multiset.map_singleton, add_right_comm]
      · ext x y
        simp [rk1, Matrix.diagonal_apply, mul_comm]
    · have := hW.what₂ τ
      beta_reduce
      rw [h4 _ _ (hl2 τ ▸ (r2 τ).1), hl2, (r2 τ).2, (r1 τ).2, hc']
      omega
    · beta_reduce
      rw [cj_cj, h4 _ _ (r1 τ).1, (r1 τ).2, hc]
      omega
    · have e := scaleRoots_prod (Finset.univ.val.map fun j => ((χ j g : (Qbar l)ˣ) : Qbar l)) ((tw g : (Qbar l)ˣ) : Qbar l)
      rw [Multiset.map_map, Multiset.map_map] at e
      rw [mul_scaleRoots_of_noZeroDivisors, ← charpoly_smul _ (Units.ne_zero _)]
      exact congrArg₂ (· * ·) rfl e.symm
end Side
section Point
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame GlobalTheory.FrameAut
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.L2.Col
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
set_option maxHeartbeats 1600000 in
theorem galois_at_place_of_automorphic_at_place (p1 : GlobalTheory.Published.ClozelCohomological) (p2 : GlobalTheory.Published.CohomologicalCsdTempered)
    (p3 : GlobalTheory.Published.HeckeLAdicCharacter) (p4 : GlobalTheory.Published.ChebotarevDegreeOne)
    (p6 : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (p7 : _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup)
    (p8 : GlobalTheory.Published.BhattScholzeCrystallineLattices) (p9 : GlobalTheory.Published.HeckeLAdicCharacterAbove) (p10 : GlobalTheory.Published.LocalLanglandsGL)
    {j : Fin D.R.m} {P : Par} {W : Wts D.what₂.Tau} (hD : Dict L j P W) (hN : NumOk P W) {w : HeightOneSpectrum (𝓞 D.what₂.LL)}
    (h : AutAt p j P W w) : GalAt p j P W w := by
  classical
  intro _ F R inc _ T
  obtain ⟨⟨hpl, hcof, hbl⟩, haut⟩ := h
  obtain ⟨hn, ht, ν, hν⟩ := blk_numbers p hD hN.1 (p.R.mu w)
  let Pl := {Q : (blk p j (p.R.mu w)).Pl // ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal}
  have hpt : ∀ (Q : Pl) (k : Fin P.Nr), ∃ i, R.ix i = (Q.1, (k : ℕ) + 1) := fun Q k =>
    (T.ix_range (Q.1, (k : ℕ) + 1)).2 ⟨Nat.le_add_left _ _, k.2, Q.2⟩
  choose pt hpt using hpt
  refine _root_.GlobalTheory.FrameGal.galois_side_of_compatible_systems _ p1 p2 p3 p4 p6 p7 p8 p9 p10 (GlobalTheory.DefiniteBC.host_unramified D.host) T.io T.half T.sh hN.1 hN.2.1
    hN.2.2.1 F _ pt (fun Q => labOf p j (p.R.mu w) Q.1) (hcof.subset fun v hv => ⟨hv.1, fun ⟨Q, h1, h2⟩ => hv.2 ⟨⟨Q, h1⟩, h2⟩⟩)
    (fun Q => ⟨(hpl Q.1).1, fun h => Q.2 ((hpl Q.1).2.2.2.1 h)⟩) (fun mu θ ha hθ => ?_) fun θ hθ Q => ?_
  · obtain ⟨π, h1, h2, h3, h4⟩ := haut F R inc T mu θ ha hθ
    refine ⟨π, h1, h2, h3, fun Q => ?_⟩
    obtain ⟨hu, σ, S, a, b, c⟩ := h4 Q.1
    refine ⟨hu, σ, S, a, b, fun k hk => ?_⟩
    rcases k with _ | k
    · rw [sysOf_zero, map_one, GlobalTheory.LFun.satEig]
      simp [Multiset.esymm]
    · have e := c (pt Q ⟨k, hk⟩) (by rw [hpt])
      rw [hpt] at e
      exact (congrArg T.io (sysOf_succ P.Nr pt θ Q ⟨k, hk⟩)).trans e
  · refine ⟨R.e0 (ν Q.1), ?_, ?_⟩
    · rw [T.liftFrame_embedding_base, hbl ν hν, (hpl Q.1).2.2.1, hn, ht]
    · rw [(hpl Q.1).2.2.1, ← ht]
      exact block_dvd hθ hn pt Q Q.1 (hpt Q) hν
end Point
end GlobalTheory.FrameGal
open Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie in
theorem GlobalTheory.FrameGal.galois_steinberg_local : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter →
    GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal →
    _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove →
    GlobalTheory.Published.LocalLanglandsGL → SmallSt → GlobalTheory.ExpTie.GalSt := by
  intro p1 p2 p3 p4 p6 p7 p8 p9 p10 hS
  refine Closed.imp (GlobalTheory.T.small_estimate_implies_frame_automorphy hS) fun Fm _ _ H => ?_
  obtain ⟨a, ha⟩ := H
  exact ⟨a, fun x hx hle i p hp hm j P W hD hN w hw hR =>
    _root_.GlobalTheory.FrameGal.galois_at_place_of_automorphic_at_place p p1 p2 p3 p4 p6 p7 p8 p9 p10 hD hN (ha x hx hle i p hp hm j P W hD hN w hw hR)⟩
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_frame_compatibility : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → _root_.GlobalTheory.Published.BaseChangeDefiniteUnitaryGroup → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.LocalLanglandsGL → SmallSt → GlobalTheory.ExpTie.GalSt := by
  first | exact @_root_.GlobalTheory.FrameGal.galois_steinberg_local | exact _root_.GlobalTheory.FrameGal.galois_steinberg_local | (intros; apply _root_.GlobalTheory.FrameGal.galois_steinberg_local <;> assumption)
end
