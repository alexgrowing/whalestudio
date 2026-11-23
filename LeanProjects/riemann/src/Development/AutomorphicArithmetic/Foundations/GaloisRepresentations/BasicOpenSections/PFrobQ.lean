import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.frobQ :
    FrobTors → FrobQ := by
  intro hT l _ X p f hp h hl k
  have key : pullHl l (sch.map (absFrob X p f hp h)) k 0 = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext (funext fun j => ?_)
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hu : IsUnit (((l ^ j : ℕ)) : Γ(X, ⊤)) := by
      rw [Nat.cast_pow]; exact hl.pow j
    exact hT (l ^ j) X p f hp h hu k (x.1 j)
  unfold pullHQ
  rw [key]
  exact LinearMap.baseChange_id
