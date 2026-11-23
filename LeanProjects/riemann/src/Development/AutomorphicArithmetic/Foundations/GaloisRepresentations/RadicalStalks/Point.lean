import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.ExistsStalkFactor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobNSucc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Root
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RankV
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FrobNNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.PullbackFirstFiltrationPrimitive
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.CohHomNatCastZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.PowCardChi
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

theorem UpperTheory.Gal.Ord.point :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      IsWOrd o w (𝟙 (Sp k)) ∨ NOo hk o π := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hnorm hf π
  rcases cnt p D R b N hN hNp hm k hk β o i w f hw hnorm hf π with h | ⟨v, hv1, hv2, hv3⟩
  · exact Or.inl h
  right
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (R := k) (Fact.out : p.Prime)).mpr hk
  have hL := lin p D R b N hN hNp hm k hk β o i w f hw hnorm hf π
  obtain ⟨σ, ψ, hσ, m, hψ⟩ := va p D R b N hN hNp hm k hk β o i w f hw hnorm hf π
  have hH := hasse p D R b N hN hNp hm k hk β o i w f hw hnorm hf π σ hσ ψ m hψ v hv1 hv2 hv3
  have hpow : ∀ n : ℕ, o.act.act ((n : D.O)) = 𝟙 o.A ^ n := by
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero, pow_zero]
      have h0 := o.act.add 0 0
      rw [add_zero] at h0
      simpa using h0
    | succ n ih => rw [Nat.cast_succ, o.act.add, ih, o.act.one, pow_succ]
  haveI hmon : IsMonHom (o.act.act ((p : D.O))) := o.act.hom _
  have hp0 : ∀ x : ↥(primDR o.A), primPull (dp0 k) (𝟙 (Sp k)) (o.act.act ((p : D.O))) x = 0 := by
    intro x
    have h1 : ((p : D.O)) = (algebraMap (𝓞 D.F) D.O) (p : 𝓞 D.F) := by simp
    have h2 : ∀ n : ℕ, coh o (n : 𝓞 D.F) = (n : k) • (1 : Module.End k ↥(primDR o.A)) := by
      intro n
      induction n with
      | zero =>
        have h0 := hL.add 0 0
        simp only [add_zero] at h0
        simpa using h0
      | succ n ih => rw [Nat.cast_succ, hL.add, ih, hL.one, Nat.cast_succ, add_smul, one_smul]
    have h3 := congrArg (fun φ : Module.End k ↥(primDR o.A) => φ x) (h2 p)
    simp only [hk, zero_smul] at h3
    have h4 : coh o (p : 𝓞 D.F) x = primPull (dp0 k) (𝟙 (Sp k)) (o.act.act ((p : D.O))) x := by
      simp only [coh, h1]
    rw [← h4]
    exact h3
  have mp : SMor o.A (RingHom.id k) (Over.Hom.left (o.act.act ((p : D.O)))) := by
    have := homMor (dp0 k) (𝟙 (Sp k)) (o.act.act ((p : D.O)))
    simpa [SMor, spMap_id] using this
  obtain ⟨τ, V, hτ, n, hτp, hV⟩ := root p k hk o.A o.ab (RingHom.id k) Function.bijective_id _ mp (by
    intro x _
    exact hp0 x)
  have hV' := hV
  rw [hpow] at hV'
  have hrel := rel p D R b N hN hNp hm k hk β o i w f hw hnorm hf π σ τ ψ V m n hψ hV'
  have hrk := rankV p k hk o.A o.ab τ V n (fun x => by simpa using hτp x) hV'
  have hcard : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]; exact hnorm
  intro x hx
  obtain ⟨z, hz⟩ := alg1 p k (𝓞 D.F) w f hf hcard π (β.comp (b.t i)) ↥(primDR o.A) (coh o) (PrimitiveSubmodule o.A)
    (frobDR p k hk o.A).toAddMonoidHom hL (GrpMor.pull n).toAddMonoidHom (GrpMor.pull m).toAddMonoidHom
    (fun y hy => hrk y hy) (fun y => hrel y) (fun x hx => hH x hx) x hx
  exact Submodule.subset_span ⟨z, hz.symm⟩
