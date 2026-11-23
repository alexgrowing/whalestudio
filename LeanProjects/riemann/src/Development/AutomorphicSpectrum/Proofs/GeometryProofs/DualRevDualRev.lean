import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} {ι : K → Type} {R : Type} [CommRing R]

def dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : LocPair ι R (Fin r) :=
  ⟨fun i => -Q.x (Fin.rev i), fun i => -Q.x' (Fin.rev i), fun i => Q.g (Fin.rev i), fun i => Q.f (Fin.rev i)⟩

def labelPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s))
  | .inl τ => T.comp fun i => (τ, Fin.castAdd D.q i)
  | .inr τ => dualRev (T.comp fun i => (τ, Fin.natAdd D.p i))

def omPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s.swap)) :=
  fun s => dualRev (labelPair D T s.swap)

def omPairM (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (Sum.elim (fun _ : CMType H => D.q) (fun _ : CMType H => D.p) s))
  | .inl τ => omPair D T (.inl τ)
  | .inr τ => omPair D T (.inr τ)

theorem dualRev_dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : dualRev (dualRev Q) = Q := by
  obtain ⟨x, x', f, g⟩ := Q
  simp [dualRev, Fin.rev_rev]

theorem map_map {R' R'' : Type} [CommRing R'] [CommRing R''] {σ : Type} (T : LocPair ι R σ) (ψ : R →+* R')
    (ψ' : R' →+* R'') : (T.map ψ).map ψ' = T.map (ψ'.comp ψ) := by
  obtain ⟨x, x', f, g⟩ := T
  simp [LocPair.map, MvPolynomial.map_map]

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
