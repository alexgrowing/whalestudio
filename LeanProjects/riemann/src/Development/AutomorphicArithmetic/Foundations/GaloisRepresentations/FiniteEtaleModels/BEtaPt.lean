import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem ev_nsmul {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n c : ℕ) (x : G.La) :
    I.ev n (c • x) = I.ev n x ^ c := by
  induction c with
  | zero =>
    rw [zero_nsmul, pow_zero]
    have h := I.add n 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  | succ c ih =>
    rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.FiniteEtaleModels.etaPtB_holds :
    EtaPtB := by
  unfold UpperTheory.Gal.FiniteEtaleModels.EtaPtB
  intro p _ D G L R _ _ gb h X s N' N o' o ψ hT Ω _ _ z x y hv
  unfold UpperTheory.Gal.Int.Geo.IsTrans at hT
  obtain ⟨-, -, -, -, hgeo⟩ := hT
  obtain ⟨I', I'', h1, h2, hiff⟩ := hgeo Ω z (Spec.preimage (z ≫ s)).hom (by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage])
  have hN' : 0 < (N' : ℕ) := by
    have := N'.2.1
    omega
  have hN : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have key := (hiff _ (Nat.mul_pos hN' hN) (Nat.Coprime.mul N'.2.2 N.2.2)
    ((N : ℕ) • x) ((N' : ℕ) • y)).2 hv
  have ex : I'.ev ((N' : ℕ) * N) ((N : ℕ) • x) = I'.ev N' x := by
    have t1 := I'.tower (N' : ℕ) N hN' hN x
    have t2 := ev_nsmul I' ((N' : ℕ) * N) N x
    exact t2.trans t1
  have ey : I''.ev ((N' : ℕ) * N) ((N' : ℕ) • y) = I''.ev N y := by
    have t1 := I''.tower (N : ℕ) N' hN hN' y
    have t2 := ev_nsmul I'' ((N' : ℕ) * N) N' y
    rw [mul_comm] at t1
    exact t2.trans t1
  have key2 := (ex ▸ ey ▸ key : I'.ev N' x ≫ ψ = I''.ev N y)
  have e1 := h1 x
  have e2 := h2 y
  rw [← Category.assoc]
  exact (congrArg (fun f => f ≫ ψ) e1).trans (key2.trans e2.symm)
